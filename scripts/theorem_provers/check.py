#!/usr/bin/env python3
"""Check prepared artifacts without installing or downloading anything."""
import fcntl
import json
from pathlib import Path
import shutil
import subprocess

if __package__:
    from . import prepare as p
else:
    import prepare as p


def check_project(name):
    root, version = p.projects[name]
    root = Path(root)
    expected = json.loads((p.B / (name + "-pins.json")).read_text())
    if p.pins(root) != expected:
        raise RuntimeError("Pins changed: " + name + "; stop for review, do not update automatically")
    receipt = p.B / (name + "-ready.json")
    if not receipt.is_file():
        raise RuntimeError(
            f"Missing readiness receipt: {receipt}. Preparation did not complete. "
            f"When repair is authorized, run python3 {p.B / 'prepare.py'} {name}, "
            "then rerun check.py. No installation attempted; do not fabricate a receipt.")
    try:
        ready = json.loads(receipt.read_text())
    except (OSError, ValueError) as error:
        raise RuntimeError("Invalid readiness receipt: " + str(receipt)) from error
    required = {"pins": expected, "version": version, "dependencies": "verified",
                "imports": "passed", "build": "passed"}
    if not isinstance(ready, dict) or any(ready.get(key) != value for key, value in required.items()):
        raise RuntimeError("Invalid readiness receipt: " + str(receipt))
    tool = p.B / "runtime/elan/toolchains" / ("leanprover--lean4---v" + version) / "bin/lean"
    if not tool.is_file():
        raise RuntimeError("Missing prepared toolchain " + version + "; no download attempted")
    actual = subprocess.check_output([str(tool), "--version"], text=True).strip()
    if "version " + version + "," not in actual:
        raise RuntimeError("Installed toolchain mismatch: " + actual)
    print(actual, flush=True)
    p.m.verify_dependencies(root)
    for package in json.loads((root / "lake-manifest.json").read_text())["packages"]:
        dep = root / ".lake/packages" / package["name"]
        if subprocess.check_output(["git", "-C", str(dep), "status", "--porcelain",
                                    "--untracked-files=no"], text=True):
            raise RuntimeError("Modified dependency: " + str(dep))
    p.m.run(["lake", "env", "lean", str(p.B / (name + "-imports.lean"))],
            root, p.env_for(name), (root, p.B))
    print(name + ": exact pins, dependency HEADs, and representative imports verified", flush=True)


def main():
    with (p.B / "prepare.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        if any(shutil.which(tool) != str(p.B / "runtime/elan/bin" / tool)
               for tool in ("elan", "lean", "lake")):
            raise RuntimeError("Source " + str(p.B / "env.sh") + " first: incorrect PATH")
        if not subprocess.check_output(["elan", "--version"], text=True).startswith("elan 4.2.4 "):
            raise RuntimeError("Unexpected elan version")
        for name in p.projects:
            check_project(name)


if __name__ == "__main__":
    main()
