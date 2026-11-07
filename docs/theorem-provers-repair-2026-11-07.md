# Theorem-provers restore repair — 7 November 2026 UTC

The local filesystem is repaired and the complete mandatory gate passes.
Publication and independent fresh-task verification remain outstanding. This
is environment maintenance; no Smith theorem or complexity claim was advanced.

## Diagnosis and limits

The deployed helpers exactly matched repair commit
`038f365f89743f51f2814c48447e27e141e49160`; the 35 existing offline tests passed.
The November 3 retained Install log completed thesis/Littlewood/Scholz builds
of 9305/2626/1134 jobs and the full gate. It is not evidence for later source
revisions or the current restored filesystem.

Before repair, shared deployment files were dated **7 November 04:47:28 UTC**,
the thesis receipt **04:47:53**, the Littlewood receipt **04:48:05**, and the
Scholz imports file **04:48:15**. Scholz's newly added checks 09/10/11 had build
outputs dated **04:54:05 / 04:54:56 / 04:57:02**; check 12 and its downstream
domain output were absent. There was no Scholz receipt. These observations
show later preparation/build activity, rather than an untouched November 3
snapshot that simply omitted a receipt. No pin or helper drift was found.

The previous documented Install hook unconditionally invoked `install.sh`.
That script prepares all projects; `prepare.py` explicitly unlinks the existing
project receipt **before** cache/import/build work and replaces it only after
real success. Its failure/interruption therefore removes previous readiness.
The old full gate correctly rejected that incomplete state.

The exact reason the earlier build stopped is unavailable: the current worker
has no supported access to the setup Install transcript or complete saved
configuration. A setup timeout/interruption is plausible, not established.
No proof error was reproduced. Ordinary Start itself only checks; the Install
hook's replay must be confirmed against the parent-held editor/setup logs.

## Repair and unchanged verification

Explicitly authorized `prepare.py scholz` completed the real 1152-job default
build on current Scholz HEAD `e82b987ed509618e4a94ca25eaff93adc6a3f6f6`.
`Clift109SparseChecks12` took 182 seconds; the domain module took 26 seconds.
The script generated its own success receipt at **19:34:09 UTC** after final
pin/dependency checks. The complete original `check.py` then passed.

The new `scripts/theorem_provers/restore.sh` deploys reviewed helper sources,
sources `env.sh`, and runs the unchanged **full** gate. It never prepares,
downloads or removes/recreates receipts. Deployment includes this script in
its atomic completion manifest. Explicit `install.sh`/`prepare.py` retain their
existing invalidation, full-build and resource-guard semantics. The mandatory
checker, Start content, pin allowlists and bootstrap implementation are unchanged.

There are now **38 passing offline tests**: 17 bootstrap and 21 preparation/
restore tests. The three new shell-hook tests cover receipt preservation,
missing-evidence failure without preparation, and deployment-failure propagation.
The real restore hook also passed all three projects. Receipt SHA-256 hashes
before and after that run were identical:

| Receipt | SHA-256 |
| --- | --- |
| thesis | `3246e5f5f128556e4f0ee7e07c05f9cd44145e1a2173e474fd8e03b40ea69704` |
| Littlewood | `85c2d8dac92d76727d322c7caf0a523f94aa0a7cd176e5f451ecebd19040cd39` |
| Scholz | `bf1ceaa5d49e609222aa678c02b07b56e032224fe766f68b01811bc80b55f419` |

All project HEADs, toolchain/manifest/Lake-file hashes and dependency sources
were preserved. The existing uncommitted Smith blocker log is byte-identical
to the repair baseline. Shell syntax and `git diff --check` pass. Logs and
baseline/hash records are under ignored
`.research/environment-repair-2026-11-07/`. No receipt is committed or copied
into a candidate environment as a substitute for actual preparation.

## Exact publication handoff

Observed attached environment:
`ccarenv_b64_Y2NhcmVudl9hNGQyMjdjODQ4ZTQ4MTkxYTEyOGJiMGI3YWM1MDNkOA`.
Supported status identifies source configuration
`f4c4ae6d-5a2c-43a6-a161-c34781e84e76~cecfg_6ad84ddfad5c81a29ec606357426b447`
and source version
`f4c4ae6d-5a2c-43a6-a161-c34781e84e76~cecfgver_6aea433dd60c81a2acd44e4790f53979`,
with observed/spec revision 1, current observations, running/connected state
and enforced unrestricted networking. These identify the existing version;
they are **not** a newly published repair version.

This worker has only environment status/diagnostic tools, with no environment
editor, save/publish or desktop-control tool. The supported publication route
is the **parent-held environment editor**, not a repository push or local file
write. Its setup workspace may differ from this repaired worker's filesystem.

1. In that setup workspace, obtain the committed repair sources without
   overwriting work. Deploy them; explicitly repair any missing project using
   the reviewed preparation path. Require the complete gate to pass there.
2. Change **only Install** to the following restore-only command. Preserve the
   existing Start content from `scripts/theorem_provers/START.md`, repositories,
   refs, network/security settings, credentials, variables and schedules.

   ```bash
   #!/bin/bash
   set -euo pipefail
   bash /workspace/phd-thesis-lean/scripts/theorem_provers/restore.sh
   ```

3. Run the saved Install hook in the setup workspace and compare all receipt
   hashes before/after. It must pass the full gate without changing receipts.
   Complete the supported editor's save/review requirements, then publish that
   successfully prepared filesystem. Publication has not been attempted here.
4. Independently launch a fresh task from the returned published version.
   Check its exact configuration/version, receipt hashes, pins and complete
   gate without preparation. If evidence is missing, stop. Resume proof work
   only after this independent verification succeeds.
