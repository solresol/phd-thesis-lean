#!/usr/bin/env python3
"""Prepare the reviewed theorem-provers projects; never accept changed pins."""
import argparse
import datetime
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

if __package__:
    from . import deployment_guard
else:
    import deployment_guard


B = Path(os.environ.get("THEOREM_PROVERS_STATE_DIR", "/workspace/shared/theorem-provers"))
projects = {
    "thesis": ("/workspace/phd-thesis-lean", "4.35.0"),
    "littlewood": ("/workspace/function-field-littlewood", "4.35.0"),
    "scholz": ("/workspace/scholz-brauer/lean", "4.27.0"),
}
# Reuse the existing tested installer/resource runner rather than copying its
# implementation into another version-controlled module. deploy.py supplies
# the same source beside the deployed helpers.
helper = (Path(__file__).resolve().parent.parent / "bootstrap_lean.py" if __package__
          else Path(__file__).resolve().parent / "bootstrap-tested.py")
spec = importlib.util.spec_from_file_location("theorem_provers_bootstrap", helper)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


def pins(root):
    return {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
            for path in (root / "lean-toolchain", root / "lake-manifest.json",
                         *sorted(root.glob("lakefile.*")))}


def env_for(name):
    env = m.toolchain_env(B / "runtime", "leanprover/lean4:v" + projects[name][1], os.environ)
    env.update(
        ELAN_HOME=str(B / "runtime/elan"),
        MATHLIB_CACHE_DIR=str(B / ("runtime/mathlib-cache" if name in
                                  ("thesis", "littlewood") else "cache/scholz")),
        LEAN_NUM_THREADS="2",
        MATHLIB_CACHE_GET_URL="https://cache.mathlib.org/mathlib4",
        MATHLIB_CACHE_BASE_URL="https://cache.mathlib.org",
    )
    return env


def verify_existing_dependencies(root):
    for package in json.loads((root / "lake-manifest.json").read_text())["packages"]:
        if package["type"] != "git":
            raise RuntimeError("Unsupported dependency type: " + package["name"])
        dep = root / ".lake/packages" / package["name"]
        if dep.exists():
            actual = subprocess.check_output(
                ["git", "-C", str(dep), "rev-parse", "HEAD"], text=True).strip()
            dirty = subprocess.check_output(
                ["git", "-C", str(dep), "status", "--porcelain"], text=True)
            if actual != package["rev"] or dirty:
                raise RuntimeError("Existing dependency differs or has local changes; "
                                   "refusing to overwrite " + str(dep))


def atomic_json(path, data):
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", dir=path.parent,
                                         prefix=path.name + ".", delete=False) as stream:
            temporary = Path(stream.name)
            json.dump(data, stream, indent=2)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def prepare_project(name):
    path, version = projects[name]
    root = Path(path)
    before = pins(root)
    if (root / "lean-toolchain").read_text().strip() != "leanprover/lean4:v" + version:
        raise RuntimeError("PIN MISMATCH: " + name)
    record = B / (name + "-pins.json")
    if not record.is_file() or json.loads(record.read_text()) != before:
        raise RuntimeError("Dependency/configuration pins changed: review required for " + name)
    verify_existing_dependencies(root)
    receipt = B / (name + "-ready.json")
    receipt.unlink(missing_ok=True)
    env = env_for(name)
    disks = (root, B)
    cold = (not (root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib").exists()
            or not (B / "runtime/elan/toolchains" /
                    ("leanprover--lean4---v" + version) / "bin/lean").is_file())
    m.require_disk(B, ((14 if name == "thesis" else 8) if cold else 2) * m.GIB)
    try:
        lean, lake = m.prepare_tools(B / "runtime", root, env, disks)
        m.run([str(lake), "--version"], root, env, disks)
        imports = set()
        for source in root.rglob("*.lean"):
            if any(part in (".lake", "vendor", ".git", "adapters")
                   for part in source.relative_to(root).parts):
                continue
            imports.update(re.findall(r"^(?:public )?import (Mathlib\.\S+)",
                                      source.read_text(), re.M))
        if name == "thesis":
            imports = {"Mathlib"}
        if not imports:
            raise RuntimeError("No targeted Mathlib imports")
        # One guarded process layer: do not wrap a bootstrap that starts its own
        # detached Lake sessions. Reuse its primitives directly for all projects.
        m.run([str(lake), "exe", "cache", "get", *sorted(imports)], root, env, disks)
        m.verify_dependencies(root)
        smoke = B / (name + "-imports.lean")
        smoke.write_text("\n".join("import " + module for module in sorted(imports))
                         + "\n#check Nat\n")
        m.run([str(lake), "env", str(lean), str(smoke)], root, env, disks)
        m.run([str(lake), "build"], root, env, disks)
        m.verify_dependencies(root)
        verify_existing_dependencies(root)
    finally:
        if pins(root) != before:
            raise RuntimeError("Concurrent pin change detected; no files restored: " + name)
    # Only reached after the real build AND the final pin/dependency checks.
    atomic_json(receipt, {
        "pins": before, "version": version, "dependencies": "verified",
        "imports": "passed", "build": "passed",
        "source_head": subprocess.check_output(
            ["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip(),
        "prepared_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    })


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("projects", nargs="*", metavar="PROJECT")
    args = parser.parse_args()
    if any(name not in projects for name in args.projects):
        parser.error("expected project names from: " + ", ".join(projects))
    if os.uname().machine != "x86_64" or os.uname().sysname != "Linux":
        raise SystemExit("Linux x86_64 required")
    (B / "runtime").mkdir(parents=True, exist_ok=True)
    with (B / "prepare.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        deployment_guard.verify(B)
        with (B / "runtime/bootstrap.lock").open("a") as runtime_lock:
            fcntl.flock(runtime_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            for name in args.projects or projects:
                prepare_project(name)


if __name__ == "__main__":
    main()
