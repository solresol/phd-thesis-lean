"""Offline failure-path checks; real preparation is validated separately."""
import contextlib
import fcntl
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from scripts.theorem_provers import check, deploy, prepare as p


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
                                or (failed_stage == "imports" and argv[1:3] == ["env", "lean"])
                                or (failed_stage == "build" and argv == ["lake", "build"]))
                    if is_stage:
                        raise subprocess.CalledProcessError(1, argv)
                self.run.side_effect = fail
                with self.assertRaises(subprocess.CalledProcessError):
                    p.prepare_project("scholz")
                self.assertFalse(self.receipt.exists())

    def test_late_pin_change_prevents_receipt(self):
        def mutate(argv, *_):
            if argv == ["lake", "build"]:
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
        self.assertEqual(self.run.call_args.args[0], ["lake", "build"])
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
        with patch.object(p, "prepare_project") as prepare, patch("sys.argv", ["prepare.py"]):
            p.main()
        prepare.assert_called_once_with("scholz")

    def test_prepare_main_propagates_failure_without_later_projects(self):
        all_projects = {"thesis": ("unused", "4.35.0"), **p.projects}
        with patch.object(p, "projects", all_projects), \
                patch.object(p, "prepare_project", side_effect=RuntimeError("build failed")) as prepare, \
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


if __name__ == "__main__":
    unittest.main()
