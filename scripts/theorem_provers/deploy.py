#!/usr/bin/env python3
"""Deploy reviewed setup sources; never copy generated readiness evidence."""
import fcntl
import json
from pathlib import Path
import shutil

if __package__:
    from . import prepare as p
else:
    import prepare as p


SOURCE = Path(__file__).resolve().parent
SOURCE_FILES = ("prepare.py", "check.py", "install.sh", "env.sh", "START.md")


def validate():
    for name, (root, _) in p.projects.items():
        expected = json.loads((SOURCE / (name + "-pins.json")).read_text())
        if p.pins(Path(root)) != expected:
            raise RuntimeError("Reviewed pins differ from checkout: " + name)
        saved = p.B / (name + "-pins.json")
        if saved.exists() and json.loads(saved.read_text()) != expected:
            raise RuntimeError("Reviewed pins differ from saved environment: " + name)


def deploy():
    validate()  # Reject all pin drift before mutating shared state.
    p.B.mkdir(parents=True, exist_ok=True)
    with (p.B / "prepare.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        validate()
        for name in SOURCE_FILES:
            shutil.copyfile(SOURCE / name, p.B / name)
        shutil.copyfile(SOURCE.parent / "bootstrap_lean.py", p.B / "bootstrap-tested.py")
        for name in p.projects:
            shutil.copyfile(SOURCE / (name + "-pins.json"), p.B / (name + "-pins.json"))
    print("Deployed reviewed sources to " + str(p.B) + "; no receipt copied or generated.")


if __name__ == "__main__":
    deploy()
