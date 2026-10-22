"""Offline failure-path tests; real standalone setup is a separate integration check."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest
from unittest.mock import Mock, patch

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
        kill.assert_called_once_with(123, boot.signal.SIGTERM)
        proc.wait.assert_called_once_with(timeout=10)

    def test_memory_guard_terminates_running_command_group(self):
        proc = Mock(pid=123, returncode=None)
        proc.poll.return_value = None
        with patch.object(boot.subprocess, "Popen", return_value=proc), \
             patch.object(boot, "require_disk"), \
             patch.object(boot, "child_rss", return_value=13 * boot.GIB), \
             patch.object(boot.os, "killpg") as kill:
            with self.assertRaisesRegex(RuntimeError, "memory guard"):
                boot.run(["lake", "build"], self.root, {}, (self.root,))
        kill.assert_called_once_with(123, boot.signal.SIGTERM)

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
        self.assertNotIn("ELAN_TOOLCHAIN", env)
        self.assertNotIn("LEAN_PATH", env)
        self.assertEqual(env["LEAN_NUM_THREADS"], "2")
        self.assertTrue((self.runtime / "env.sh").exists())
        self.assertIn("unset ELAN_TOOLCHAIN LEAN_SYSROOT LEAN_PATH", (self.runtime / "env.sh").read_text())

    def test_pin_mutation_is_reported_even_after_command_failure(self):
        self.make_project()
        self.fake_elan()
        def mutate(*_):
            (self.root / "lean-toolchain").write_text("changed\n")
            raise subprocess.CalledProcessError(1, ["lake"])
        with patch.object(boot, "require_disk"), patch.object(boot, "run", side_effect=mutate):
            with self.assertRaisesRegex(RuntimeError, "pin files changed.*lean-toolchain"):
                boot.bootstrap(self.root, self.runtime, [])


if __name__ == "__main__":
    unittest.main()
