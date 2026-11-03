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
GUARD_OWNER = "_LEAN_BOOTSTRAP_GUARD_OWNER"


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
    child_env = env.copy()
    owner = child_env.get(GUARD_OWNER)
    nested = owner is not None
    if nested:
        # Nested guarded commands inherit the outer command's owned group.
        # Validate its leader is a direct child of the advertised live guard;
        # never borrow or signal an unrelated shell/process group.
        group = os.getpgrp()
        stat = Path(f"/proc/{group}/stat").read_text().rsplit(")", 1)[1].split()
        if not owner.isdecimal() or int(stat[1]) != int(owner):
            raise RuntimeError("invalid inherited bootstrap process-group ownership")
    else:
        child_env[GUARD_OWNER] = str(os.getpid())
    proc = subprocess.Popen(argv, cwd=root, env=child_env, start_new_session=not nested)
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
    finally:
        if nested:
            # The outer guard owns this group and cleans up all descendants
            # when a nested failure propagates, even if their parent exits.
            if proc.poll() is None:
                proc.terminate()
        else:
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                pass
            # Also kill surviving descendants after the group leader exits;
            # waiting only for that leader does not prove the group is empty.
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait()


def toolchain_name(root):
    name = (root / "lean-toolchain").read_text().strip()
    if not re.fullmatch(r"leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+", name):
        raise RuntimeError("expected a pinned stable official Lean toolchain")
    return name


def toolchain_env(runtime, name, inherited):
    """Pin nested tools too; retained elan directory overrides stay untouched."""
    env = inherited.copy()
    sysroot = runtime / "elan/toolchains" / name.replace("/", "--").replace(":", "---")
    env.pop("LEAN_PATH", None)
    env.update(ELAN_HOME=str(runtime / "elan"), ELAN_TOOLCHAIN=name,
               LEAN_SYSROOT=str(sysroot), LEAN=str(sysroot / "bin/lean"),
               LAKE_HOME=str(sysroot), LAKE_OVERRIDE_LEAN="0",
               ELAN=str(runtime / "elan/bin/elan"),
               PATH=str(sysroot / "bin") + os.pathsep + str(runtime / "elan/bin")
                    + os.pathsep + env.get("PATH", ""))
    return env


def installed_tools(runtime, name, env):
    """Read-only exact-binary validation: no elan proxy or auto-installation."""
    sysroot = runtime / "elan/toolchains" / name.replace("/", "--").replace(":", "---")
    lean, lake = sysroot / "bin/lean", sysroot / "bin/lake"
    if not all(path.is_file() and os.access(path, os.X_OK) for path in (lean, lake)):
        raise RuntimeError("Missing prepared toolchain binaries: " + str(sysroot)
                           + "; no download attempted")
    version = name.split(":v", 1)[1]
    actual = subprocess.check_output([str(lean), "--version"], env=env, text=True).strip()
    lake_actual = subprocess.check_output([str(lake), "--version"], env=env, text=True).strip()
    if "version " + version + "," not in actual or "Lean version " + version + ")" not in lake_actual:
        raise RuntimeError("Installed toolchain mismatch for " + name)
    return lean, lake


def prepare_tools(runtime, root, env, disks):
    """Only explicit preparation may install the exact reviewed official pin."""
    name = toolchain_name(root)
    install_elan(runtime, root, env, disks)
    sysroot = runtime / "elan/toolchains" / name.replace("/", "--").replace(":", "---")
    if not all((sysroot / "bin" / tool).is_file() for tool in ("lean", "lake")):
        if any(env.get(key) for key in ("ELAN_DIST_SERVER", "ELAN_UPDATE_ROOT")):
            raise RuntimeError("Custom elan download source requires review; no toolchain installed")
        run([str(runtime / "elan/bin/elan"), "toolchain", "install", name], root, env, disks)
    return installed_tools(runtime, name, env)


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
    env = toolchain_env(runtime, toolchain_name(root), os.environ)
    env.update(MATHLIB_CACHE_DIR=str(runtime / "mathlib-cache"), LEAN_NUM_THREADS="2")
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
            lean, lake = prepare_tools(runtime, root, env, disks)
            run([str(lake), "--version"], root, env, disks)
            run([str(lake), "exe", "cache", "get", *mathlib_imports(root)], root, env, disks)
            verify_dependencies(root)
            exports = "unset LEAN_PATH\n" + "\n".join(f"export {key}={shlex.quote(env[key])}" for key in
                                ("ELAN_HOME", "ELAN_TOOLCHAIN", "LEAN_SYSROOT", "LEAN", "LAKE_HOME",
                                 "LAKE_OVERRIDE_LEAN", "ELAN", "MATHLIB_CACHE_DIR", "PATH", "LEAN_NUM_THREADS",
                                 "MATHLIB_CACHE_GET_URL", "MATHLIB_CACHE_BASE_URL")) + "\n"
            (runtime / "env.sh").write_text(exports)
            if command:
                command = list(command)
                if command[0] in ("lean", "lake"):
                    command[0] = str(lean if command[0] == "lean" else lake)
                if command[1:3] == ["env", "lean"]:
                    command[2] = str(lean)
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
