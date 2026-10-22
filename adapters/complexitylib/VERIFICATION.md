# Verification record — 2026-10-22

Environment: Linux x86_64; Lean 4.36.0-rc1, compiler commit
`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`.

Executed from `adapters/complexitylib/`:

```sh
ELAN_HOME=/workspace/adapter-elan \
XDG_CACHE_HOME=/workspace/adapter-cache \
PATH=/workspace/adapter-elan/bin:$PATH ./check.sh
```

Result: exit 0. `lake build --wfail` succeeded (3644 Lake jobs, including
cached/dependency targets). `lake env lean Audit.lean` succeeded, followed by
the script's axiom allowlist check. This builds only the adapter's import
closure, not the entire upstream Complexitylib library.

| Declaration | Printed axiom dependencies |
| --- | --- |
| `binaryEmbedding` | `propext` |
| `binaryEmbedding_apply` | `propext` |
| `binaryEmbedding_length` | `propext` |
| `decode_binaryEmbedding` | `propext` |
| `SimulationObligation` | `propext`, `Classical.choice`, `Quot.sound` |
| `reduction_of_simulation` | `propext`, `Classical.choice`, `Quot.sound` |
| `wordEncoding` | none |

No placeholder, custom axiom or unsafe declaration occurs in the adapter
library source. No simulation proof or NP-hardness transfer is claimed.
`SimulationObligation` is a proposition with no supplied proof.

The checkout was clean before branching; origin was
`https://github.com/solresol/phd-thesis-lean.git`. Main was fetched before
creating `adapter/complexitylib-bridge` at
`f0c247aff60f7dde5b12abb3a1e7211083e57216`.
`git diff --exit-code origin/main -- . ':!adapters'` passed before commit.
Root pins and canonical source files are unchanged; the root 4.35 build was
not rerun. The independent bootstrap/Smith work is outside this change.

Initial setup's mathlib cache hook encountered a read-only home cache;
redirecting `XDG_CACHE_HOME` to `/workspace/adapter-cache` resolved it. A
virtual-address-space guard prevented thread creation; the final checked
script instead uses available-memory and disk guards, two Lean threads,
limited allocator arenas, CPU-time limits and command timeouts. No unrelated
cache was removed. Dependency artifacts and toolchain installation are local
setup state, excluded from the commit.
