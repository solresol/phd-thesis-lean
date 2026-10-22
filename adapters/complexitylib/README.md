# Complexitylib compatibility prototype

This separate Lake project checks a **binary encoding/interface bridge**, not a
second thesis proof library. It does not establish a TM2 simulation, membership
in Complexitylib's NP, or transfer of NP-hardness.

## Isolation and provenance

The canonical project at the repository root remains on Lean/mathlib 4.35.0,
with its existing lean-np-hardness pin. This subproject uses Lean 4.36.0-rc1.
Do not run `lake update` at the repository root to accommodate this adapter.
Its own `lake-manifest.json` locks the complete dependency graph.

Verified from upstream git and source on 2026-10-22:

| Component | Exact revision |
| --- | --- |
| [canonical Complexitylib](https://github.com/cslib-community/complexitylib) | `62bbf525e2d7edce00dc8b6c79a52040223c5bed` (HEAD at inspection) |
| [CSLib](https://github.com/leanprover/cslib) | `8a20ea3dd61a1ed03ec9b5936f8234b5b1dd32f6` |
| transitive mathlib | `625d8914199bc567cca9b91f90e8e5afafa5ae51` (v4.36.0-rc1) |
| canonical thesis baseline | `f0c247aff60f7dde5b12abb3a1e7211083e57216` |

The formerly inspected Complexitylib `8a2d724d...` is not the chosen pin.
SamuelSchlesinger's historical `complexitylib-v1` is a different API and is
not a dependency. Upstream dependencies remain separately owned and licensed;
no upstream or thesis proof files have been vendored. New adapter code is
Apache-2.0; that does not relicense the canonical thesis library.

## What the kernel checks

`ThesisComplexityAdapter/Bridge.lean` converts mathlib's
`Computability.Encoding α Bool` to `α ↪ List Bool`, using its left-inverse
decoder to prove injectivity. The encoding function, decoder round trip and
word length are preserved exactly. A binary-word example checks the identity
encoding, including the empty word.

The stable `LeanNPHardness.FinEncoding.toEncoding` exposes precisely the source
shape, **when the bundled alphabet is Bool**. This project does not import that
stable package: Lean 4.35 oleans cannot be consumed by Lean 4.36, and adding the
root project as a dependency would force incompatible pins into one graph.
This is a separately checked interface contract, not a checked import of the
existing thesis declarations. There is intentionally no shadow copy of
`FinEncoding`, CNF, regression instances, reductions, or the core proof library.

`SimulationObligation ea eb` states the still-missing implication from a
mathlib `TM2ComputableInPolyTime ea.encode eb.encode f` witness to the actual
`Turing.MultiTapeTM.ComputableTidilyInPolyTime f` API in Complexitylib.
It is a definition of a proposition; no inhabitant is supplied.
`reduction_of_simulation` consumes that proposition as an explicit local
hypothesis and a membership-preserving map. It constructs the actual
`Cslib.Complexity.ManyOneReducibleBy` with the tidy polynomial-time predicate.
This matches the right side of upstream
`Cslib.Complexity.polyTimeReducible_iff_manyOneReducibleBy`
(`Complexity/Computability/Complexity/Reduction.lean`). The adapter imports the
smaller generic reduction and machine interfaces; it does not import or claim
the upstream NP-hardness theorem suite.

## Next lemma: simulate bounded TM2 runs tidily

Before attempting `SimulationObligation`, define a compiler for a fixed
`Turing.FinTM2` with Boolean external alphabets and a relation between its
stack configurations and a finite-state binary CSLib multitape configuration.
The next substantive lemma should establish:

* From `TM2OutputsInTime tm input (some output) T`, construct a compiled run
  from `wordsCfg input (some compiled.q₀) (fun _ => []) []` to
  `wordsCfg input none (fun _ => []) output`.
* Bound its time **and** work space by explicit polynomials in
  `input.length + T + 1`, with constants depending only on the fixed machine.
  Prove the bounds and include initialization, output emission and cleanup.

This is an intended lemma specification, not a theorem in this prototype.
Use CSLib's `computesTidily_iff` to connect the run to
`ComputesTidilyInTimeAndSpace`. TM2's `FinTM2` has finite stacks, finite symbol
alphabets, finite labels, finite local state and finite supported code; a proof
must account for compound TM2 statements and their step cost, stack direction,
branching, halting, input/output alphabet equivalences, the empty input, and
possible input/output stack aliasing. Compile internal symbols to fixed-width
binary blocks and prove their decoding/size bounds. Recover the original
Boolean output, restore all heads and clear every work tape; semantic output
agreement alone is insufficient. Compose the explicit bounds with the TM2
witness's `Polynomial ℕ` time bound to obtain Complexitylib's `PolyBounded`
time and space predicates. None of these machine obligations follows merely
from injectivity or polynomial output length.

Thesis reductions also use non-Boolean finite alphabets (for example CNF
symbols). A later extension needs a checked fixed-width symbol codec with a
linear length theorem and polynomial-time conversion machines. The binary
bridge here does not cover these encodings automatically.

Even after machine simulation, full hardness transfer needs a proved
relationship between the two NP definitions/encodings (or an independently
proved Complexitylib-hard source and a checked reduction into the thesis
problem). The conditional witness theorem by itself proves neither.

## Reproduce and integrate

From **this directory**, with elan available:

```sh
lake exe cache get Mathlib.Computability.TuringMachine.Computable
./check.sh
```

The first command is optional; Lake can build missing dependencies. A selective
mathlib cache covering the transitive Mathlib imports of the Complexitylib
machine interface makes first setup faster. Keep elan's toolchains and cache
on a persistent volume if the execution environment is ephemeral; installation
is not itself a guarantee that that volume survives. This execution used
`ELAN_HOME=/workspace/adapter-elan` and
`XDG_CACHE_HOME=/workspace/adapter-cache` so it did not write to read-only home
caches. Those directories are not repository deliverables.

`check.sh` applies a 20-minute limit per build/audit, two Lean worker threads,
a per-process CPU-time limit, and available-memory/free-disk guards. It scans new
Lean code for placeholders and checks the printed axiom dependencies. It does
not delete caches. Standard Lean logical axioms are allowed; `sorryAx` and
custom axioms are rejected.

Integrate by reviewing/cherry-picking the adapter commit or merging its feature
branch after the independent main work is ready. All tracked additions are
under `adapters/complexitylib/`; no root imports, CI, bootstrap, Smith files,
toolchain or manifests are changed. Run the root's existing verification under
4.35 separately when integrating. Do not add this subproject to the root Lake
dependency graph. A future common-toolchain port needs its own reviewed plan;
it must preserve one canonical theorem source library.
