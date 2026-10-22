#!/usr/bin/env python3
"""Prepare this checkout's pinned Lean environment; optionally run a command."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import time


ELAN_VERSION = "4.2.4"
ELAN_URL = ("https://github.com/leanprover/elan/releases/download/v4.2.4/"
            "elan-x86_64-unknown-linux-gnu.tar.gz")
ELAN_SHA256 = "42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63"
GIB = 1024 ** 3
PIN_FILES = ("lean-toolchain", "lake-manifest.json", "lakefile.lean")


def require_disk(path, minimum):
    free = shutil.disk_usage(path).free
    if free < minimum:
        raise RuntimeError(f"disk guard: {path}: {free / GIB:.2f} GiB free; "
                           f"need {minimum / GIB:.2f} GiB")


def child_rss(pid):
    """Linux resident bytes for the command's process group, excluding file cache."""
    total = 0
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            if os.getpgid(int(entry.name)) == pid:
                total += int((entry / "statm").read_text().split()[1]) * os.sysconf("SC_PAGE_SIZE")
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            pass
    return total


def run(argv, root, env, disks, timeout=1800):
    """Inherit logs; stop this command group if resources or time run out."""
    print("+ " + shlex.join(map(str, argv)), flush=True)
    proc = subprocess.Popen(argv, cwd=root, env=env, start_new_session=True)
    started = time.monotonic()
    try:
        while proc.poll() is None:
            for disk in disks:
                require_disk(disk, 2 * GIB)
            if child_rss(proc.pid) > 12 * GIB:
                raise RuntimeError("memory guard: command group exceeds 12 GiB RSS")
            if time.monotonic() - started > timeout:
                raise RuntimeError(f"timeout after {timeout}s: {shlex.join(map(str, argv))}")
            time.sleep(1)
        if proc.returncode:
            raise subprocess.CalledProcessError(proc.returncode, argv)
    except BaseException:
        if proc.poll() is None:
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
        raise


def install_elan(runtime, root, env, disks):
    elan = runtime / "elan/bin/elan"
    if not elan.exists():
        with tempfile.TemporaryDirectory(prefix="installer-", dir=runtime) as temp:
            temp = Path(temp)
            archive = temp / "elan.tar.gz"
            run(["curl", "--fail", "--location", "--retry", "3", "--max-time", "120",
                 ELAN_URL, "--output", str(archive)], root, env, disks)
            digest = hashlib.sha256(archive.read_bytes()).hexdigest()
            if digest != ELAN_SHA256:
                raise RuntimeError(f"elan checksum mismatch: expected {ELAN_SHA256}, got {digest}")
            # Extract only the expected regular file, never arbitrary archive paths.
            with tarfile.open(archive, "r:gz") as tar:
                member = tar.getmember("elan-init")
                if not member.isfile():
                    raise RuntimeError("elan-init is not a regular file")
                with tar.extractfile(member) as source:
                    (temp / "elan-init").write_bytes(source.read())
            (temp / "elan-init").chmod(0o700)
            run([str(temp / "elan-init"), "-y", "--no-modify-path",
                 "--default-toolchain", "none"], root, env, disks)
    version = subprocess.check_output([str(elan), "--version"], env=env, text=True).strip()
    if not version.startswith(f"elan {ELAN_VERSION} "):
        raise RuntimeError(f"unexpected existing runtime: {version}")


def mathlib_imports(root):
    # The thesis includes direct `import Mathlib` declarations; do not omit them.
    files = [*root.glob("*.lean")]
    for directory in ("PhdThesisLean", "DiscreteMetricRegression"):
        files.extend((root / directory).rglob("*.lean"))
    imports = sorted({name for path in files for name in
                      re.findall(r"^(?:public )?import (Mathlib(?:\.\S+)?)(?:\s|$)", path.read_text(), re.M)})
    if not imports:
        raise RuntimeError("no Mathlib imports found; refusing a full cold build")
    return ["Mathlib"] if "Mathlib" in imports else imports


def verify_dependencies(root):
    manifest = json.loads((root / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        if package["type"] != "git":
            raise RuntimeError(f"unsupported dependency type: {package['name']}")
        path = root / manifest["packagesDir"] / package["name"]
        actual = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        if actual != package["rev"]:
            raise RuntimeError(f"dependency pin mismatch: {package['name']}: {actual} != {package['rev']}")


def bootstrap(root, runtime, command):
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise RuntimeError("bootstrap supports Linux x86_64 only")
    pins = {name: (root / name).read_bytes() for name in PIN_FILES}
    if not re.fullmatch(r"leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+\n?", pins["lean-toolchain"].decode()):
        raise RuntimeError("expected a pinned stable official Lean toolchain")
    runtime.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    for key in ("ELAN_TOOLCHAIN", "LEAN_SYSROOT", "LEAN_PATH"):
        env.pop(key, None)  # Never override the repository toolchain or import path.
    env.update(ELAN_HOME=str(runtime / "elan"), MATHLIB_CACHE_DIR=str(runtime / "mathlib-cache"),
               PATH=str(runtime / "elan/bin") + os.pathsep + env["PATH"], LEAN_NUM_THREADS="2")
    # Current public endpoint; the pinned client's optional GET_URL uses the legacy layout.
    env["MATHLIB_CACHE_GET_URL"] = "https://cache.mathlib.org/mathlib4"
    env["MATHLIB_CACHE_BASE_URL"] = "https://cache.mathlib.org"
    disks = (root, runtime)
    with (runtime / "bootstrap.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        toolchain = pins["lean-toolchain"].decode().strip().replace("/", "--").replace(":", "---")
        cold = (not (runtime / "elan/toolchains" / toolchain / "bin/lean").exists()
                or not (root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib").exists())
        for disk in disks:
            require_disk(disk, (14 if cold else 2) * GIB)
        try:
            install_elan(runtime, root, env, disks)
            run(["lake", "--version"], root, env, disks)
            run(["lake", "exe", "cache", "get", *mathlib_imports(root)], root, env, disks)
            verify_dependencies(root)
            exports = "unset ELAN_TOOLCHAIN LEAN_SYSROOT LEAN_PATH\n" + "\n".join(f"export {key}={shlex.quote(env[key])}" for key in
                                ("ELAN_HOME", "MATHLIB_CACHE_DIR", "PATH", "LEAN_NUM_THREADS",
                                 "MATHLIB_CACHE_GET_URL", "MATHLIB_CACHE_BASE_URL")) + "\n"
            (runtime / "env.sh").write_text(exports)
            if command:
                run(command, root, env, disks)
        finally:
            changed = [name for name, content in pins.items() if (root / name).read_bytes() != content]
            if changed:
                raise RuntimeError(f"pin files changed during bootstrap: {', '.join(changed)}")
    print(f"Ready. For interactive commands: source {shlex.quote(str(runtime / 'env.sh'))}")


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime-dir", type=Path, default=root / ".research/lean-runtime")
    parser.add_argument("--run", nargs=argparse.REMAINDER, default=[], metavar="COMMAND")
    args = parser.parse_args()
    bootstrap(root, args.runtime_dir.resolve(), args.run)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        print(f"bootstrap failed: {error}", file=sys.stderr)
        sys.exit(1)
