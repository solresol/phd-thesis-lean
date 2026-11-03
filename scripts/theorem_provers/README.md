# Saved theorem-provers setup

This directory is the version-controlled source for the shared prepared runtime.
It preserves the reviewed Lean 4.35.0 thesis/Littlewood and Lean 4.27.0 Scholz
pins. The three `*-pins.json` files are SHA-256 allowlists for the existing
toolchain, Lake manifest and Lake configuration, not declarations of readiness.
Changing them requires separate review; deployment rejects checkout or saved
allowlist drift. No dependency version is selected from a moving branch here.

## Installation and repair

The environment's supported **Install** field should run:

```bash
#!/bin/bash
set -euo pipefail
python3 /workspace/phd-thesis-lean/scripts/theorem_provers/deploy.py
bash /workspace/shared/theorem-provers/install.sh
```

The managed thesis checkout must contain this committed directory before these
commands run. Keep the configured repositories, refs, access settings, secrets
and variables unchanged. `deploy.py` validates every reviewed project first,
takes the shared preparation lock and copies only helper sources and pin
allowlists. Complete files are staged and fsynced, then atomically replaced;
the final completion manifest hashes every deployed source and saved allowlist.
An interrupted or mixed deployment fails the gate and supports safe retry.
Existing verified pin bytes are retained, existing managed source edits are
rejected, and pre-migration helper bytes are atomically backed up. It reuses the
existing `scripts/bootstrap_lean.py` installer and
resource runner as the deployed `bootstrap-tested.py`; there is no second
generic bootstrap implementation to maintain. Deployment does not copy or
generate readiness receipts, build outputs, toolchains or caches.

`install.sh` prepares all three projects sequentially and runs the full startup
gate. Any cache, dependency, import, build or final verification failure exits
nonzero. Shared preparation directly calls the common bootstrap primitives,
without nesting a bootstrap process inside another timed runner. Nested guarded
commands, if used elsewhere, inherit the outer owned process group so timeout
cleanup reaches their descendants. Cleanup also handles a group leader that
exits before its children and does not signal unrelated groups.
The runner retains two Lean threads, the 2 GiB disk reserve, 12 GiB
process-group RSS limit and 30-minute per-command timeout. Only the existing
official checksum-verified elan source, pinned manifests and official Mathlib
cache endpoint are used. No `lake update`, pin upgrades, resets, credentials or
network-policy changes are performed.

Every Lean/Lake command uses the absolute binary under the exact pinned
toolchain. Per-command variables and PATH also select that installation for
nested tools. Retained elan directory overrides and inherited selectors are
left untouched and cannot choose another release. Startup validates both
binaries directly and never invokes an elan toolchain proxy or installs a
missing release. Explicit preparation can install only the reviewed official
pin; custom elan download endpoints require review first.

For an explicitly authorized repair of one missing artifact, after source
deployment:

```bash
source /workspace/shared/theorem-provers/env.sh
python3 /workspace/shared/theorem-provers/prepare.py scholz
python3 /workspace/shared/theorem-provers/check.py
```

Preparation invalidates that project's old receipt and publishes a new one
atomically only after real cache/dependency verification, representative
imports, the complete default build and final pin/dependency rechecks pass.
The receipt records the source HEAD and preparation time for diagnostics.
It is evidence about work done in that filesystem; committing or copying a
receipt cannot reproduce that work. A later source refresh still requires the
worker's appropriate project build: pin readiness does not prove new sources.

## Ordinary tasks and publication

Ordinary tasks use the saved Start instructions in `START.md`:

```bash
source /workspace/shared/theorem-provers/env.sh
python3 /workspace/shared/theorem-provers/check.py
```

The checker verifies the installed exact runtime, pin allowlists, all receipt
success fields, dependency HEADs/cleanliness and representative imports. It
never repairs, downloads or installs. Missing readiness names the exact path
and the repair command, and stops. Startup must not silently fabricate it.

Committing these sources makes preparation reproducible; it does not update a
published environment. Use the supported environment editor to save the Install
field above and Start content, run installation, require its final gate to pass,
then publish the prepared filesystem. Finally launch an independent fresh task
from that published version and rerun the complete gate without preparation.
Do not claim fresh-task persistence until that test passes. A worker without
configuration/publication tools must hand these steps to the parent.

## Validation

```bash
python3 -m unittest discover -s tests -p 'test*bootstrap*.py' -v
python3 -m unittest discover -s tests -p test_theorem_provers.py -v
```

Offline tests cover missing/invalid receipts, failed cache/import/build paths,
pin drift, concurrent pin changes, project selection, lock contention,
inherited toolchain overrides/proxies, real nested process cleanup, and atomic
deployment interruption/retry with preserved pins and user changes.
They do not replace a real full Install run or
the independent fresh-task test.

The 3 November 2026 repair found a missing Scholz receipt after thesis and
Littlewood receipts had been regenerated. The old preparation code deliberately
removed readiness before work and restored it only on success. Retained logs
do not establish whether the original absence resulted from interrupted/failed
preparation or omission from a snapshot. A generated imports file alone is not
proof of a full build. The historical shared `REPORT.md` describes the original
October preparation; its then-unpublished status is not current publication
evidence.
