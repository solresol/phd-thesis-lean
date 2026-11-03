"""Reject incomplete or locally modified shared setup deployments."""
import hashlib
import json
from pathlib import Path

REQUIRED = {"check.py", "prepare.py", "deployment_guard.py", "bootstrap-tested.py",
            "env.sh", "install.sh", "START.md"}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify(state):
    manifest = state / "deployment.json"
    try:
        saved = json.loads(manifest.read_text())
        if saved["state"] != "complete" or not isinstance(saved["sources"], dict) \
                or not REQUIRED.issubset(saved["sources"]):
            raise ValueError("deployment incomplete")
        for name, expected in saved["sources"].items():
            if Path(name).name != name or digest((state / name).read_bytes()) != expected:
                raise ValueError("source mismatch: " + name)
    except (OSError, ValueError, TypeError, KeyError) as error:
        raise RuntimeError("Incomplete or modified theorem-provers deployment: "
                           + str(manifest) + "; rerun reviewed source deployment") from error
