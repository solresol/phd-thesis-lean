Use the existing checkouts in this isolated environment; do not create Git worktrees unless explicitly requested.

The reviewed setup sources and pin allowlists are version-controlled in
`/workspace/phd-thesis-lean/scripts/theorem_provers/`. See its README for the
explicitly authorized repair and publication procedure. Generated readiness
receipts remain in shared state and must not be fabricated or committed.

Before Lean work, run:
```bash
source /workspace/shared/theorem-provers/env.sh
python3 /workspace/shared/theorem-provers/check.py
```
These checks must pass. They check PATH, elan 4.2.4, installed exact toolchains, the recorded toolchain/manifest/Lake configuration hashes, exact dependency HEADs and clean tracked dependency sources, build readiness receipts, and representative Mathlib imports. The checker never installs or upgrades a toolchain and does not run cache get or lake update.

Targets: /workspace/phd-thesis-lean (4.35.0), /workspace/function-field-littlewood (4.35.0), /workspace/scholz-brauer/lean (4.27.0). Leave /workspace/phd-thesis/proofs and all other repositories unchanged. Dependency workspaces are isolated per checkout; thesis and Littlewood share only downloaded content-keyed Mathlib archives in /workspace/shared/theorem-provers/runtime/mathlib-cache after matching their exact toolchain and all common dependency URL/revision pairs; mutable .lake workspaces remain separate. Scholz archives are isolated in /workspace/shared/theorem-provers/cache/scholz. One elan runtime at /workspace/shared/theorem-provers/runtime/elan supplies both exact toolchains.

For each project command, set MATHLIB_CACHE_DIR to its archive directory above. Do not install or warm adapters/complexitylib or its separate release-candidate toolchain. Run projects sequentially with LEAN_NUM_THREADS=2. Use prepare.py's guarded runner for costly builds (2 GiB reserve, 12 GiB process-group RSS, 30 minute command timeout). Do not delete unrelated caches or increase limits to bypass failures.

After repository refreshes, changed toolchain, manifest, or Lake configuration hashes cause a hard stop before setup. Report the exact change for review. Never automatically bless new hashes, overwrite source changes, reset repositories, run lake update, or auto-upgrade. Re-preparation for reviewed pins is a separate explicit action. Missing readiness receipts or artifacts mean preparation is incomplete; report the failure instead of silently reinstalling on task startup.

The saved filesystem retains tools and dependency outputs; shell exports must be reapplied each task. Publication and successful restoration in a new task remain separate checks. No credentials or network permissions are installed by these instructions.
