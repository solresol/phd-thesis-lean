#!/usr/bin/env python3
"""Deploy reviewed setup sources; never copy generated readiness evidence."""
import fcntl
import json
import os
from pathlib import Path
import sys
import tempfile

if __package__:
    from . import prepare as p
    from . import deployment_guard as guard
else:
    # Import source modules as a package. Deployed direct scripts deliberately
    # load only their adjacent, manifest-covered bootstrap-tested.py.
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from scripts.theorem_provers import prepare as p, deployment_guard as guard


SOURCE = Path(__file__).resolve().parent
SOURCE_FILES = ("prepare.py", "check.py", "deployment_guard.py", "install.sh",
                "restore.sh", "env.sh", "START.md")


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
        payload = {name: (SOURCE / name).read_bytes() for name in SOURCE_FILES}
        payload["bootstrap-tested.py"] = (SOURCE.parent / "bootstrap_lean.py").read_bytes()
        for name in p.projects:
            filename = name + "-pins.json"
            # validate() checks semantic equality; preserve even harmless
            # formatting differences and hash the bytes actually retained.
            existing = p.B / filename
            payload[filename] = (existing if existing.exists() else SOURCE / filename).read_bytes()
        target_hashes = {name: guard.digest(data) for name, data in payload.items()}
        manifest = p.B / "deployment.json"
        previous = {name: guard.digest((p.B / name).read_bytes())
                    for name in payload if (p.B / name).exists()}
        if manifest.exists():
            saved = json.loads(manifest.read_text())
            # Permit a retry after any interrupted atomic replacement, while
            # refusing to overwrite subsequent user edits to managed sources.
            for name, actual in previous.items():
                known = {saved.get("sources", {}).get(name),
                         saved.get("previous_sources", {}).get(name), target_hashes[name]}
                if actual not in known:
                    raise RuntimeError("Locally modified deployment source; preserved: " + str(p.B / name))
        # Preserve exact pre-migration bytes too, including legacy helpers that
        # predate the manifest. No cache, runtime or generated receipt is copied.
        for name, digest in previous.items():
            backup = p.B / "deployment-backups" / digest / name
            if not backup.exists():
                backup.parent.mkdir(parents=True, exist_ok=True)
                with tempfile.NamedTemporaryFile(dir=backup.parent, delete=False) as stream:
                    staged_backup = Path(stream.name)
                    stream.write((p.B / name).read_bytes())
                    stream.flush()
                    os.fsync(stream.fileno())
                try:
                    replace_file(staged_backup, backup)
                finally:
                    staged_backup.unlink(missing_ok=True)
            if guard.digest(backup.read_bytes()) != digest:
                raise RuntimeError("Corrupt deployment backup; live source preserved: " + str(backup))
        with tempfile.TemporaryDirectory(prefix=".deployment-stage-", dir=p.B) as temporary:
            stage = Path(temporary)
            for name, data in payload.items():
                with (stage / name).open("wb") as stream:
                    stream.write(data)
                    stream.flush()
                    os.fsync(stream.fileno())
            # First make the gate fail closed if migration is interrupted even
            # before its manifest exists. A new gate never accepts old hashes.
            replace_file(stage / "check.py", p.B / "check.py")
            p.atomic_json(manifest, {"state": "updating", "sources": target_hashes,
                                     "previous_sources": previous})
            for name in payload:
                if name == "check.py":
                    continue
                if name.endswith("-pins.json") and (p.B / name).exists():
                    continue  # validated identical; never rewrite verified pins
                replace_file(stage / name, p.B / name)
            p.atomic_json(manifest, {"state": "complete", "sources": target_hashes})
        guard.verify(p.B)
    print("Deployed reviewed sources to " + str(p.B) + "; no receipt copied or generated.")


def replace_file(source, target):
    """One complete same-filesystem replacement; never truncate a live entry."""
    source.replace(target)
    directory = os.open(target.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


if __name__ == "__main__":
    deploy()
