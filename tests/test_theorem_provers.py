"""Offline failure-path checks; real preparation is validated separately."""
import contextlib
import fcntl
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from scripts.theorem_provers import check, deploy, deployment_guard, prepare as p


class PreparationTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.base = Path(temp.name)
        self.state = self.base / "state"
        self.state.mkdir()
        self.root = self.base / "scholz"
        self.root.mkdir()
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.27.0\n")
        (self.root / "lake-manifest.json").write_text('{"packages": []}')
        (self.root / "lakefile.toml").write_text('name = "test"\n')
        (self.root / "Example.lean").write_text("import Mathlib.Data.Finset.Card\n")
        self.pins = p.pins(self.root)
        (self.state / "scholz-pins.json").write_text(json.dumps(self.pins))
        self.receipt = self.state / "scholz-ready.json"
        self.addCleanup(patch.stopall)
        patch.object(p, "B", self.state).start()
        patch.object(p, "projects", {"scholz": (str(self.root), "4.27.0")}).start()
        patch.object(p.m, "require_disk").start()
        self.install = patch.object(p.m, "install_elan").start()
        self.lean = self.state / "runtime/elan/toolchains/leanprover--lean4---v4.27.0/bin/lean"
        self.lake = self.lean.with_name("lake")
        self.tools = patch.object(p.m, "prepare_tools", return_value=(self.lean, self.lake)).start()
        self.run = patch.object(p.m, "run").start()
        patch.object(p.m, "verify_dependencies").start()
        patch.object(p.subprocess, "check_output", return_value="a" * 40 + "\n").start()

    def valid_receipt(self):
        return {"pins": self.pins, "version": "4.27.0", "dependencies": "verified",
                "imports": "passed", "build": "passed"}

    def test_missing_receipt_names_project_and_does_not_install(self):
        with self.assertRaisesRegex(RuntimeError, str(self.receipt)):
            check.check_project("scholz")
        self.install.assert_not_called()
        self.run.assert_not_called()

    def test_bad_json_and_incomplete_receipts_are_rejected_before_execution(self):
        for value in ("{", "[]", "{}", json.dumps({**self.valid_receipt(), "version": "wrong"}),
                      json.dumps({**self.valid_receipt(), "imports": "failed"}),
                      json.dumps({**self.valid_receipt(), "dependencies": "failed"})):
            self.receipt.write_text(value)
            with self.assertRaisesRegex(RuntimeError, "Invalid readiness receipt: " + str(self.receipt)):
                check.check_project("scholz")
        self.run.assert_not_called()

    def test_pin_drift_prevents_installer_and_build(self):
        (self.root / "lakefile.toml").write_text("changed\n")
        with self.assertRaisesRegex(RuntimeError, "pins changed"):
            p.prepare_project("scholz")
        self.install.assert_not_called()
        self.run.assert_not_called()

    def test_cache_import_and_build_failures_leave_no_receipt(self):
        for failed_stage in ("cache", "imports", "build"):
            with self.subTest(stage=failed_stage):
                self.receipt.write_text(json.dumps(self.valid_receipt()))
                def fail(argv, *_):
                    is_stage = ((failed_stage == "cache" and argv[1:3] == ["exe", "cache"])
                                or (failed_stage == "imports" and argv[1] == "env")
                                or (failed_stage == "build" and argv[1:] == ["build"]))
                    if is_stage:
                        raise subprocess.CalledProcessError(1, argv)
                self.run.side_effect = fail
                with self.assertRaises(subprocess.CalledProcessError):
                    p.prepare_project("scholz")
                self.assertFalse(self.receipt.exists())

    def test_late_pin_change_prevents_receipt(self):
        def mutate(argv, *_):
            if argv[1:] == ["build"]:
                (self.root / "lakefile.toml").write_text("changed after build\n")
        self.run.side_effect = mutate
        with self.assertRaisesRegex(RuntimeError, "Concurrent pin change"):
            p.prepare_project("scholz")
        self.assertFalse(self.receipt.exists())

    def test_success_writes_receipt_only_after_build(self):
        def observe(*_):
            self.assertFalse(self.receipt.exists())
        self.run.side_effect = observe
        p.prepare_project("scholz")
        saved = json.loads(self.receipt.read_text())
        for key, value in self.valid_receipt().items():
            self.assertEqual(saved[key], value)
        self.assertEqual(self.run.call_args.args[0], [str(self.lake), "build"])
        self.assertTrue(saved["source_head"])
        self.assertTrue(saved["prepared_at_utc"])

    def test_unknown_project_fails_before_preparation(self):
        with patch("sys.argv", ["prepare.py", "scholzz"]), contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as result:
                p.main()
        self.assertEqual(result.exception.code, 2)
        self.install.assert_not_called()

    def test_preparation_lock_rejects_overlap(self):
        with (self.state / "prepare.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            with patch("sys.argv", ["prepare.py", "scholz"]):
                with self.assertRaises(BlockingIOError):
                    p.main()
        self.install.assert_not_called()

    def test_no_project_arguments_prepares_all_projects(self):
        with patch.object(p, "prepare_project") as prepare, patch("sys.argv", ["prepare.py"]), \
                patch.object(deployment_guard, "verify"):
            p.main()
        prepare.assert_called_once_with("scholz")

    def test_prepare_main_propagates_failure_without_later_projects(self):
        all_projects = {"thesis": ("unused", "4.35.0"), **p.projects}
        with patch.object(p, "projects", all_projects), \
                patch.object(p, "prepare_project", side_effect=RuntimeError("build failed")) as prepare, \
                patch.object(deployment_guard, "verify"), \
                patch("sys.argv", ["prepare.py", "thesis", "scholz"]):
            with self.assertRaisesRegex(RuntimeError, "build failed"):
                p.main()
        prepare.assert_called_once_with("thesis")

    def test_deployment_rejects_pin_drift_and_preserves_generated_evidence(self):
        source = self.base / "sources"
        source.mkdir()
        for name in deploy.SOURCE_FILES:
            (source / name).write_text("source " + name)
        (source.parent / "bootstrap_lean.py").write_text("tested helper")
        (source / "scholz-pins.json").write_text(json.dumps(self.pins))
        self.receipt.write_text("existing generated evidence")
        runtime = self.state / "runtime/elan"
        runtime.mkdir(parents=True)
        (runtime / "keep").write_text("existing runtime")
        with patch.object(deploy, "SOURCE", source):
            for _ in range(2):
                deploy.deploy()
            (self.state / "scholz-pins.json").write_text("{}")
            (source / "prepare.py").write_text("must not deploy")
            with self.assertRaisesRegex(RuntimeError, "saved environment"):
                deploy.deploy()
        self.assertEqual((self.state / "prepare.py").read_text(), "source prepare.py")
        self.assertEqual(self.receipt.read_text(), "existing generated evidence")
        self.assertEqual((runtime / "keep").read_text(), "existing runtime")

    def test_preparation_uses_only_direct_pinned_tools_without_nested_bootstrap(self):
        p.prepare_project("scholz")
        for invocation in self.run.call_args_list:
            self.assertEqual(invocation.args[0][0], str(self.lake))
            self.assertEqual(invocation.args[2]["ELAN_TOOLCHAIN"], "leanprover/lean4:v4.27.0")
        smoke = self.run.call_args_list[2].args[0]
        self.assertEqual(smoke[:3], [str(self.lake), "env", str(self.lean)])

    def test_gate_invokes_pinned_tools_with_mismatched_inherited_selectors(self):
        self.receipt.write_text(json.dumps(self.valid_receipt()))
        with patch.object(p.m, "installed_tools", return_value=(self.lean, self.lake)) as installed, \
                patch.dict(os.environ, {"ELAN_TOOLCHAIN": "wrong", "LEAN": "/wrong/lean",
                                        "LAKE_OVERRIDE_LEAN": "1", "HTTPS_PROXY": "http://proxy.invalid"}):
            check.check_project("scholz")
            self.assertEqual(os.environ["ELAN_TOOLCHAIN"], "wrong")
        env = installed.call_args.args[2]
        self.assertEqual(env["ELAN_TOOLCHAIN"], "leanprover/lean4:v4.27.0")
        self.assertEqual(env["HTTPS_PROXY"], "http://proxy.invalid")
        self.assertEqual(self.run.call_args.args[0][:3], [str(self.lake), "env", str(self.lean)])

    def test_atomic_deployment_interruption_fails_closed_and_retry_preserves_pins(self):
        # Use real helper sources so the interrupted entry point is executable.
        original = Path(deploy.__file__).resolve().parent
        source = self.base / "real-sources"
        source.mkdir()
        for name in deploy.SOURCE_FILES:
            (source / name).write_bytes((original / name).read_bytes())
        (source.parent / "bootstrap_lean.py").write_bytes((original.parent / "bootstrap_lean.py").read_bytes())
        (source / "scholz-pins.json").write_text(json.dumps(self.pins))
        pin_bytes = (self.state / "scholz-pins.json").read_bytes()
        real_replace = deploy.replace_file
        for stop_after in (1, 2, 3, 5, 7):
            with self.subTest(stop_after=stop_after):
                # A clean initial state for each migration point.
                for name in (*deploy.SOURCE_FILES, "bootstrap-tested.py", "deployment.json"):
                    (self.state / name).unlink(missing_ok=True)
                replacements = 0
                def interrupt(src, dst):
                    nonlocal replacements
                    real_replace(src, dst)
                    if dst.parent == self.state:
                        replacements += 1
                        if replacements == stop_after:
                            raise OSError("simulated deployment interruption")
                with patch.object(deploy, "SOURCE", source), \
                        patch.object(deploy, "replace_file", side_effect=interrupt):
                    with self.assertRaisesRegex(OSError, "interruption"):
                        deploy.deploy()
                self.assertEqual((self.state / "check.py").read_bytes(), (source / "check.py").read_bytes())
                self.assertEqual((self.state / "scholz-pins.json").read_bytes(), pin_bytes)
                with self.assertRaisesRegex(RuntimeError, "Incomplete or modified"):
                    deployment_guard.verify(self.state)
                env = {**os.environ, "THEOREM_PROVERS_STATE_DIR": str(self.state)}
                result = subprocess.run([sys.executable, str(self.state / "check.py")], env=env,
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10)
                self.assertNotEqual(result.returncode, 0)
                with patch.object(deploy, "SOURCE", source):
                    deploy.deploy()
                deployment_guard.verify(self.state)
                self.assertEqual((self.state / "scholz-pins.json").read_bytes(), pin_bytes)

    def test_deployment_preserves_and_rejects_user_changes(self):
        source = self.base / "sources"
        source.mkdir()
        for name in deploy.SOURCE_FILES:
            (source / name).write_text("source " + name)
        (source.parent / "bootstrap_lean.py").write_text("tested helper")
        (source / "scholz-pins.json").write_text(json.dumps(self.pins))
        with patch.object(deploy, "SOURCE", source):
            deploy.deploy()
            changed = self.state / "prepare.py"
            changed.write_text("user change, preserve exactly")
            with self.assertRaisesRegex(RuntimeError, "Locally modified"):
                deploy.deploy()
        self.assertEqual(changed.read_text(), "user change, preserve exactly")

    def test_deployment_preserves_equivalent_pin_json_bytes(self):
        source = self.base / "sources"
        source.mkdir()
        for name in deploy.SOURCE_FILES:
            (source / name).write_text("source " + name)
        (source.parent / "bootstrap_lean.py").write_text("tested helper")
        (source / "scholz-pins.json").write_text(json.dumps(self.pins, indent=2) + "\n")
        before = (self.state / "scholz-pins.json").read_bytes()
        with patch.object(deploy, "SOURCE", source):
            deploy.deploy()
            deploy.deploy()
        deployment_guard.verify(self.state)
        self.assertEqual(before, (self.state / "scholz-pins.json").read_bytes())

    def test_corrupt_backup_stops_before_replacing_intact_live_sources(self):
        source = self.base / "sources"
        source.mkdir()
        for name in deploy.SOURCE_FILES:
            (source / name).write_text("source " + name)
        (source.parent / "bootstrap_lean.py").write_text("tested helper")
        (source / "scholz-pins.json").write_text(json.dumps(self.pins))
        pin = self.state / "scholz-pins.json"
        before = pin.read_bytes()
        with patch.object(deploy, "SOURCE", source):
            deploy.deploy()
            backup = self.state / "deployment-backups" / deployment_guard.digest(before) / pin.name
            backup.write_bytes(b"")
            live_source = (self.state / "prepare.py").read_bytes()
            with self.assertRaisesRegex(RuntimeError, "Corrupt deployment backup"):
                deploy.deploy()
        self.assertEqual(pin.read_bytes(), before)
        self.assertEqual((self.state / "prepare.py").read_bytes(), live_source)

    def test_deployed_loader_ignores_unmanaged_parent_helper(self):
        original = Path(deploy.__file__).resolve().parent
        source = self.base / "real-sources"
        source.mkdir()
        for name in deploy.SOURCE_FILES:
            (source / name).write_bytes((original / name).read_bytes())
        parent_helper = source.parent / "bootstrap_lean.py"
        parent_helper.write_bytes((original.parent / "bootstrap_lean.py").read_bytes())
        (source / "scholz-pins.json").write_text(json.dumps(self.pins))
        with patch.object(deploy, "SOURCE", source):
            deploy.deploy()
        parent_helper.write_text("raise RuntimeError('unmanaged helper must not load')\n")
        code = ("import sys; " + f"sys.path.insert(0,{str(self.state)!r}); "
                "import prepare; print(prepare.helper)")
        result = subprocess.run([sys.executable, "-c", code], check=True, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10)
        self.assertEqual(result.stdout.strip(), str(self.state / "bootstrap-tested.py"))


class RestoreTests(unittest.TestCase):
    """Exercise the real shell hook; PreparationTests cover the real gate."""

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.base = Path(temp.name)
        self.state = self.base / "state"
        self.state.mkdir()
        source = Path(deploy.__file__).with_name("restore.sh")
        self.restore = self.base / "restore.sh"
        self.restore.write_bytes(source.read_bytes())
        self.deployer = self.base / "deploy.py"
        self.deployer.write_text("print('modeled helper deployment')\n")
        (self.state / "env.sh").write_text("export THEOREM_PROVERS_TEST_ACTIVATED=1\n")
        (self.state / "check.py").write_text(
            "import os, sys\nfrom pathlib import Path\n"
            "assert os.environ['THEOREM_PROVERS_TEST_ACTIVATED'] == '1'\n"
            "state = Path(__file__).parent\n"
            "(state / 'gate-called').touch()\n"
            "sys.exit(0 if (state / 'scholz-ready.json').is_file() else 17)\n")
        # A sentinel: running preparation here would destroy the test receipt.
        (self.state / "prepare.py").write_text(
            "from pathlib import Path\nstate = Path(__file__).parent\n"
            "(state / 'preparation-called').touch()\n"
            "(state / 'scholz-ready.json').unlink(missing_ok=True)\n"
            "raise RuntimeError('restore must never prepare')\n")
        self.receipt = self.state / "scholz-ready.json"

    def run_restore(self):
        return subprocess.run(
            ["bash", str(self.restore)], cwd=self.base,
            env={**os.environ, "THEOREM_PROVERS_STATE_DIR": str(self.state)},
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=10)

    def test_restored_evidence_is_preserved_and_full_gate_is_called(self):
        evidence = b"modeled previously verified evidence\n"
        self.receipt.write_bytes(evidence)
        result = self.run_restore()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.receipt.read_bytes(), evidence)
        self.assertTrue((self.state / "gate-called").exists())
        self.assertFalse((self.state / "preparation-called").exists())

    def test_missing_evidence_fails_without_preparation_or_replacement(self):
        result = self.run_restore()
        self.assertEqual(result.returncode, 17, result.stderr)
        self.assertFalse(self.receipt.exists())
        self.assertTrue((self.state / "gate-called").exists())
        self.assertFalse((self.state / "preparation-called").exists())

    def test_deployment_failure_stops_before_gate_and_preserves_evidence(self):
        evidence = b"modeled previously verified evidence\n"
        self.receipt.write_bytes(evidence)
        self.deployer.write_text("raise SystemExit(23)\n")
        result = self.run_restore()
        self.assertEqual(result.returncode, 23, result.stderr)
        self.assertEqual(self.receipt.read_bytes(), evidence)
        self.assertFalse((self.state / "gate-called").exists())
        self.assertFalse((self.state / "preparation-called").exists())


if __name__ == "__main__":
    unittest.main()
