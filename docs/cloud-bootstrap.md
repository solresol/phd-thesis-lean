# Reproducible thesis cloud setup

On a Linux x86_64 worker, from this repository's root:

```sh
python3 scripts/bootstrap_lean.py --run lake build
source .research/lean-runtime/env.sh
lake env lean PhdThesisLean/SmithRowOperations.lean
lake env lean PhdThesisLean/MaxObjectiveSmith.lean
```

Run commands sequentially. The bootstrap uses this checkout alone, never another
repository's packages or shared symlinks. It installs the official Linux x86_64
elan **4.2.4** archive, verifies SHA-256
`42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63`, and runs the
installer with `--no-modify-path --default-toolchain none`. Source:
`https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz`.
It honors `lean-toolchain` (currently stable Lean 4.35.0), materializes the existing
manifest, verifies every dependency HEAD, and checks the toolchain, manifest and
`lakefile.lean` remain byte-for-byte unchanged. It never invokes `lake update`.

The default isolated runtime/cache is `.research/lean-runtime`; dependencies and
compiled proofs remain in `.lake`. A custom writable runtime can be selected:

```sh
python3 scripts/bootstrap_lean.py --runtime-dir /workspace/thesis-runtime --run lake build
source /workspace/thesis-runtime/env.sh
```

The generated `env.sh` unsets `ELAN_TOOLCHAIN`, `LEAN_SYSROOT`, `LEAN_PATH` and
exports absolute `ELAN_HOME`, `MATHLIB_CACHE_DIR`, prefixed `PATH`, plus:

```sh
export LEAN_NUM_THREADS=2
export MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4
export MATHLIB_CACHE_BASE_URL=https://cache.mathlib.org
```

The cache URL variables support the pinned clients through mathlib's official
public endpoint. The thesis includes direct `import Mathlib`, so its cache closure
is larger than Littlewood's targeted closure. Cold setup requires **14 GiB free**;
warm setup requires **2 GiB**. Each subprocess is stopped if free disk falls below
2 GiB, process-group RSS exceeds 12 GiB, or it runs longer than 30 minutes. Output
is inherited, failures exit nonzero, and concurrent bootstrap using the same
runtime is rejected by a lock. Stop on failures; do not erase unrelated data.

## Prepared environment and persistence

An ordinary task's installation does not republish the prepared environment.
These files alone do not establish durable cache persistence. Through the
supported environment editor, the candidate preparation commands are:

```sh
cd /workspace/phd-thesis-lean
python3 scripts/bootstrap_lean.py --run lake build
```

This would prepare the exact pinned toolchain under
`/workspace/phd-thesis-lean/.research/lean-runtime/elan`, archives under its
`mathlib-cache`, and dependencies/build outputs under
`/workspace/phd-thesis-lean/.lake`. The parent coordinates editor configuration,
publication and the subsequent fresh-task test separately. Do not assert that
these paths survive checkout refresh until that test succeeds. Each task should
still run the bootstrap and source its exports rather than assume inherited PATH.
Do not bake an ordinary task's entire workspace or unrelated research into an
environment to preserve this small runtime requirement.

## Verification limits

```sh
python3 -m unittest discover -s tests -p test_bootstrap_lean.py -v
```

The focused offline tests mock network/installer/Lake calls for failure paths and
test runtime reuse, checksum/download failures, resource guards, broad Mathlib
imports and unchanged pins. They are not cold-install evidence. This worker has
roughly 3 GiB free; use its previously installed scratch runtime for warm checks,
or perform cold thesis setup in a fresh worker with sufficient reserves. No new
cold thesis install should be forced into this worker. The earlier manual pinned
build and audit do not by themselves verify publication of a prepared environment.
