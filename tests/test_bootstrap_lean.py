"""Offline failure-path tests; real standalone setup is a separate integration check."""
from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import Mock, patch, call

from scripts import bootstrap_lean as boot


class BootstrapTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.runtime = self.root / "runtime"
        self.runtime.mkdir()

    def fake_elan(self):
        binary = self.runtime / "elan/bin/elan"
        binary.parent.mkdir(parents=True)
        binary.write_text("#!/bin/sh\nprintf 'elan 4.2.4 (test)\\n'\n")
        binary.chmod(0o700)
        return binary

    def make_project(self):
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        (self.root / "lake-manifest.json").write_text('{"packages": [], "packagesDir": ".lake/packages"}')
        (self.root / "lakefile.lean").write_text('import Lake\n')
        (self.root / "PhdThesisLean").mkdir()
        for name in ("PhdThesisLean.lean",):
            (self.root / name).write_text("module\npublic import Mathlib.Data.ZMod.Basic\n")
        (self.root / ".lake/packages/mathlib").mkdir(parents=True)
        binary_dir = self.runtime / "elan/toolchains/leanprover--lean4---v4.35.0/bin"
        binary_dir.mkdir(parents=True)
        for name, version in (("lean", "Lean (version 4.35.0, test)"),
                              ("lake", "Lake test (Lean version 4.35.0)")):
            binary = binary_dir / name
            binary.write_text("#!/bin/sh\nprintf '%s\\n' '" + version + "'\n")
            binary.chmod(0o700)

    def test_existing_runtime_does_not_download_or_reinstall(self):
        self.fake_elan()
        with patch.object(boot, "run") as run:
            for _ in range(2):
                boot.install_elan(self.runtime, self.root, os.environ.copy(), (self.root,))
        run.assert_not_called()

    def test_checksum_failure_never_executes_installer(self):
        def download(argv, *_):
            Path(argv[-1]).write_bytes(b"corrupt archive")
        with patch.object(boot, "run", side_effect=download) as run:
            with self.assertRaisesRegex(RuntimeError, "checksum mismatch"):
                boot.install_elan(self.runtime, self.root, {}, (self.root,))
        self.assertEqual(run.call_count, 1)
        self.assertFalse((self.runtime / "elan").exists())

    def test_download_failure_propagates_without_installer(self):
        error = subprocess.CalledProcessError(22, ["curl"])
        with patch.object(boot, "run", side_effect=error) as run:
            with self.assertRaises(subprocess.CalledProcessError):
                boot.install_elan(self.runtime, self.root, {}, (self.root,))
        self.assertEqual(run.call_count, 1)

    def test_disk_guard(self):
        with patch.object(boot.shutil, "disk_usage", return_value=Mock(free=boot.GIB)):
            with self.assertRaisesRegex(RuntimeError, "disk guard"):
                boot.require_disk(self.root, 2 * boot.GIB)

    def test_low_disk_prevents_any_install(self):
        self.make_project()
        with patch.object(boot, "require_disk", side_effect=RuntimeError("disk guard")), \
             patch.object(boot, "install_elan") as install:
            with self.assertRaisesRegex(RuntimeError, "disk guard"):
                boot.bootstrap(self.root, self.runtime, [])
        install.assert_not_called()

    def test_thesis_cold_setup_requires_fourteen_gib(self):
        self.make_project()
        with patch.object(boot, "require_disk", side_effect=RuntimeError("disk guard")) as guard:
            with self.assertRaisesRegex(RuntimeError, "disk guard"):
                boot.bootstrap(self.root, self.runtime, [])
        self.assertEqual(guard.call_args.args[1], 14 * boot.GIB)

    def test_direct_mathlib_import_is_not_silently_omitted(self):
        self.make_project()
        (self.root / "PhdThesisLean/Example.lean").write_text("import Mathlib\n")
        self.assertEqual(boot.mathlib_imports(self.root), ["Mathlib"])

    def test_disk_guard_terminates_running_command_group(self):
        proc = Mock(pid=123, returncode=None)
        proc.poll.return_value = None
        with patch.object(boot.subprocess, "Popen", return_value=proc), \
             patch.object(boot, "require_disk", side_effect=RuntimeError("disk guard")), \
             patch.object(boot.os, "killpg") as kill:
            with self.assertRaisesRegex(RuntimeError, "disk guard"):
                boot.run(["lake", "build"], self.root, {}, (self.root,))
        kill.assert_has_calls([call(123, boot.signal.SIGTERM), call(123, boot.signal.SIGKILL)])
        proc.wait.assert_any_call(timeout=10)

    def test_memory_guard_terminates_running_command_group(self):
        proc = Mock(pid=123, returncode=None)
        proc.poll.return_value = None
        with patch.object(boot.subprocess, "Popen", return_value=proc), \
             patch.object(boot, "require_disk"), \
             patch.object(boot, "child_rss", return_value=13 * boot.GIB), \
             patch.object(boot.os, "killpg") as kill:
            with self.assertRaisesRegex(RuntimeError, "memory guard"):
                boot.run(["lake", "build"], self.root, {}, (self.root,))
        kill.assert_has_calls([call(123, boot.signal.SIGTERM), call(123, boot.signal.SIGKILL)])

    def test_dependency_revision_mismatch_is_rejected(self):
        self.make_project()
        (self.root / "lake-manifest.json").write_text(
            '{"packagesDir": ".lake/packages", "packages": '
            '[{"type": "git", "name": "mathlib", "rev": "expected"}]}')
        with patch.object(boot.subprocess, "check_output", return_value="other\n"):
            with self.assertRaisesRegex(RuntimeError, "dependency pin mismatch"):
                boot.verify_dependencies(self.root)

    def test_bootstrap_repeat_preserves_pins_and_exports(self):
        self.make_project()
        self.fake_elan()
        before = {name: (self.root / name).read_bytes() for name in boot.PIN_FILES}
        with patch.object(boot, "require_disk"), patch.object(boot, "run") as run, \
             patch.dict(os.environ, {"ELAN_TOOLCHAIN": "wrong", "LEAN_PATH": "wrong"}):
            boot.bootstrap(self.root, self.runtime, ["lake", "build"])
            boot.bootstrap(self.root, self.runtime, ["lake", "build"])
        self.assertEqual(before, {name: (self.root / name).read_bytes() for name in boot.PIN_FILES})
        self.assertEqual(run.call_count, 6)
        env = run.call_args.args[2]
        self.assertEqual(env["ELAN_TOOLCHAIN"], "leanprover/lean4:v4.35.0")
        self.assertNotIn("LEAN_PATH", env)
        self.assertEqual(env["LEAN_NUM_THREADS"], "2")
        self.assertTrue((self.runtime / "env.sh").exists())
        self.assertIn("unset LEAN_PATH", (self.runtime / "env.sh").read_text())
        for invocation in run.call_args_list:
            self.assertEqual(Path(invocation.args[0][0]).name, "lake")
            self.assertTrue(Path(invocation.args[0][0]).is_absolute())

    def test_inherited_override_and_proxy_cannot_select_toolchain(self):
        self.make_project()
        proxies = self.runtime / "elan/bin"
        proxies.mkdir(parents=True)
        marker = self.root / "proxy-invoked"
        for name in ("lean", "lake"):
            binary = proxies / name
            binary.write_text("#!/bin/sh\ntouch '" + str(marker) + "'\nexit 97\n")
            binary.chmod(0o700)
        settings = self.runtime / "elan/settings.toml"
        settings.write_text('[overrides]\n"' + str(self.root) + '" = "unavailable-test-toolchain"\n')
        before = settings.read_bytes()
        inherited = {"PATH": str(proxies), "ELAN_TOOLCHAIN": "wrong",
                     "LEAN_SYSROOT": "/wrong", "LEAN": "/wrong/lean", "LAKE_OVERRIDE_LEAN": "1",
                     "HTTPS_PROXY": "http://proxy.invalid:8080", "HTTP_PROXY": "http://proxy.invalid:8080"}
        env = boot.toolchain_env(self.runtime, boot.toolchain_name(self.root), inherited)
        lean, lake = boot.installed_tools(self.runtime, boot.toolchain_name(self.root), env)
        self.assertEqual(env["LEAN"], str(lean))
        self.assertEqual(env["PATH"].split(os.pathsep)[0], str(lake.parent))
        self.assertEqual(env["HTTPS_PROXY"], inherited["HTTPS_PROXY"])
        self.assertEqual(env["HTTP_PROXY"], inherited["HTTP_PROXY"])
        self.assertEqual(inherited["ELAN_TOOLCHAIN"], "wrong")
        self.assertEqual(before, settings.read_bytes())
        self.assertFalse(marker.exists())

    def test_missing_or_mismatched_pinned_binary_does_not_fall_back_to_proxy(self):
        self.make_project()
        env = boot.toolchain_env(self.runtime, boot.toolchain_name(self.root), os.environ)
        lean = Path(env["LEAN"])
        lean.write_text("#!/bin/sh\nprintf 'Lean (version 4.27.0, wrong)\\n'\n")
        with self.assertRaisesRegex(RuntimeError, "toolchain mismatch"):
            boot.installed_tools(self.runtime, boot.toolchain_name(self.root), env)
        lean.unlink()
        with self.assertRaisesRegex(RuntimeError, "no download attempted"):
            boot.installed_tools(self.runtime, boot.toolchain_name(self.root), env)

    def test_missing_toolchain_install_is_explicit_and_custom_source_is_rejected(self):
        self.make_project()
        self.fake_elan()
        env = boot.toolchain_env(self.runtime, boot.toolchain_name(self.root), os.environ)
        Path(env["LEAN"]).unlink()
        with patch.object(boot, "run") as run, patch.object(boot, "installed_tools"):
            boot.prepare_tools(self.runtime, self.root, env, (self.root,))
        self.assertEqual(run.call_args.args[0],
                         [str(self.runtime / "elan/bin/elan"), "toolchain", "install",
                          "leanprover/lean4:v4.35.0"])
        env["ELAN_DIST_SERVER"] = "https://unreviewed.invalid"
        with patch.object(boot, "run") as run:
            with self.assertRaisesRegex(RuntimeError, "requires review"):
                boot.prepare_tools(self.runtime, self.root, env, (self.root,))
        run.assert_not_called()

    def test_pin_mutation_is_reported_even_after_command_failure(self):
        self.make_project()
        self.fake_elan()
        def mutate(*_):
            (self.root / "lean-toolchain").write_text("changed\n")
            raise subprocess.CalledProcessError(1, ["lake"])
        with patch.object(boot, "require_disk"), patch.object(boot, "run", side_effect=mutate):
            with self.assertRaisesRegex(RuntimeError, "pin files changed.*lean-toolchain"):
                boot.bootstrap(self.root, self.runtime, [])


class ProcessGroupTests(unittest.TestCase):
    def test_real_nested_timeout_kills_owned_tree_and_preserves_unrelated_process(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            marker = root / "child.json"
            repository = Path(boot.__file__).resolve().parents[1]
            leaf = ("import os,signal,time,json; from pathlib import Path; "
                    "signal.signal(signal.SIGTERM,signal.SIG_IGN); "
                    f"Path({str(marker)!r}).write_text(json.dumps([os.getpid(),os.getpgrp()])); "
                    "time.sleep(60)")
            parent = ("import os,sys; from pathlib import Path; "
                      f"sys.path.insert(0,{str(repository)!r}); "
                      "from scripts.bootstrap_lean import run; "
                      f"run([sys.executable,'-c',{leaf!r}],Path({str(root)!r}),os.environ.copy(),"
                      f"(Path({str(root)!r}),),timeout=30)")
            unrelated = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"],
                                         start_new_session=True)
            try:
                with self.assertRaisesRegex(RuntimeError, "timeout after"):
                    boot.run([sys.executable, "-c", parent], root, os.environ.copy(), (root,), timeout=2)
                self.assertTrue(marker.exists(), "nested process must really have started")
                child, group = json.loads(marker.read_text())
                deadline = time.monotonic() + 3
                while time.monotonic() < deadline:
                    stat = Path(f"/proc/{child}/stat")
                    if not stat.exists() or stat.read_text().rsplit(")", 1)[1].split()[0] == "Z":
                        break
                    time.sleep(0.05)
                else:
                    self.fail("nested child survived outer timeout")
                self.assertNotEqual(group, os.getpgrp())
                self.assertIsNone(unrelated.poll())
            finally:
                unrelated.terminate()
                unrelated.wait(timeout=5)

    def test_failed_group_leader_does_not_leave_its_child_running(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            marker = root / "child.json"
            leaf = ("import os,signal,time,json; from pathlib import Path; "
                    "signal.signal(signal.SIGTERM,signal.SIG_IGN); "
                    f"Path({str(marker)!r}).write_text(json.dumps(os.getpid())); time.sleep(60)")
            parent = ("import subprocess,sys,time; from pathlib import Path; "
                      f"subprocess.Popen([sys.executable,'-c',{leaf!r}]); "
                      f"marker=Path({str(marker)!r}); "
                      "exec('while not marker.exists(): time.sleep(0.01)'); sys.exit(7)")
            with self.assertRaises(subprocess.CalledProcessError):
                boot.run([sys.executable, "-c", parent], root, os.environ.copy(), (root,), timeout=10)
            child = json.loads(marker.read_text())
            stat = Path(f"/proc/{child}/stat")
            deadline = time.monotonic() + 3
            while stat.exists() and stat.read_text().rsplit(")", 1)[1].split()[0] != "Z":
                self.assertLess(time.monotonic(), deadline, "child survived failed group leader")
                time.sleep(0.05)


if __name__ == "__main__":
    unittest.main()
