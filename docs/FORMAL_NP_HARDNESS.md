# Machine-checking NP-hardness reductions

Research note, 24 July 2026.

## What has to be checked

A machine-checked NP-hardness result has three separable layers:

1. **Semantic correctness:** the reduction preserves YES-instances in both
   directions.
2. **Resource correctness:** the target encoding and the reduction's running
   time are polynomial in the source encoding length, including the bit sizes
   of integers and weights.
3. **Hardness transfer:** the source language is formally known to be NP-hard
   in the same computation and reduction model.

Finite tests can expose mistakes in layer 1, and SAT/SMT search can discover
gadgets in restricted templates, but neither replaces a proof for all inputs
or the bit-complexity argument.

## Established proof-assistant work

### ACL2: correctness of the Cook-Levin translation

Gamboa and Cowles gave an ACL2 proof of the correctness of the translation
from a nondeterministic Turing-machine computation to a Boolean formula. Their
focus was the detailed semantic correctness that textbooks usually abbreviate.

- Ruben Gamboa and John Cowles, *A Mechanical Proof of the Cook-Levin
  Theorem*, TPHOLs 2004.
- [Author-hosted paper](https://www.cs.uwyo.edu/~ruben/static/pdf/tm2sat.pdf)
- [DOI](https://doi.org/10.1007/978-3-540-30142-4_8)

### Coq: a full concrete complexity model and Cook-Levin

Gäher and Kunze formalised time complexity, NP, polynomial-time reductions,
and the NP-completeness of SAT in Coq. They use a call-by-value lambda calculus
as the main programming model, prove its polynomial equivalence to Turing
machines, and use Turing machines as an intermediate representation in the
hardness reduction. The reduction functions are implemented and analysed in
the formal model.

- Lennard Gäher and Fabian Kunze, *Mechanising Complexity Theory: The
  Cook-Levin Theorem in Coq*, ITP 2021.
- [Paper and metadata](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2021.20)
- [Checked source repository](https://github.com/uds-psl/cook-levin)
- [Compiled Coq documentation](https://uds-psl.github.io/cook-levin/)

This is the strongest end-to-end precedent found: it checks all three layers
above against a concrete computation model.

### Isabelle/HOL: full Cook-Levin foundations

Balbach's Archive of Formal Proofs development defines deterministic
multi-tape Turing machines, P, NP, polynomial-time many-one reduction, CNF-SAT,
oblivious two-tape simulation, and the polynomial-time reduction of arbitrary
NP languages to SAT.

- Frank J. Balbach, *The Cook-Levin theorem*, Archive of Formal Proofs, 2023.
- [AFP entry and sources](https://isa-afp.org/entries/Cook_Levin.html)
- [Generated proof document](https://www.isa-afp.org/browser_info/current/AFP/Cook_Levin/document.pdf)

The generated document is about 875 pages, which is useful evidence of the
engineering scale of building Cook-Levin from first principles.

### Isabelle/HOL: problem-specific reduction checking

There are also narrower developments closer to the present project:

- Thiemann and Schmidinger formally encode generalized multiset ordering into
  CNF and CNF back into multiset ordering, proving quadratic and linear output
  size bounds and deriving NP-completeness/NP-hardness results.
  [AFP entry](https://isa-afp.org/entries/Multiset_Ordering_NPC.html)
- Kreuzer and Nipkow formalised the semantic reductions from Subset Sum and
  Partition to exact lattice problems. Formalisation uncovered errors in
  published proofs. Their Isabelle development checks the reduction functions
  and semantic equivalences, while the paper explicitly says that polynomial
  running time was discussed but not formalised.
  [CADE-29 paper](https://arxiv.org/abs/2306.08375) and
  [AFP sources](https://isa-afp.org/entries/CVP_Hardness.html)

The lattice work is the closest methodological match to this repository:
formalise the concrete construction and both semantic directions, make size
bounds explicit, and state clearly where the general complexity foundation is
still external.

## Automated discovery rather than kernel checking

Bergold, Scheucher, and Schröder use SAT solvers to construct reduction gadgets
automatically for families of finite completion problems. This demonstrates
that gadget discovery can be automated when the search space is a finite
template.

- [*Finding hardness reductions automatically using SAT solvers*](https://arxiv.org/abs/2402.06397)

This is complementary to Lean: a solver may propose a gadget or finite truth
table, while Lean checks the generic correctness theorem and complexity
accounting.

## Current Lean 4 position

Mathlib at this repository's pinned revision provides:

- `FinEncoding`;
- concrete two-stack Turing-machine computability;
- `TM2ComputableInTime`; and
- `TM2ComputableInPolyTime`, with a polynomial time-bound witness.

However, `TM2ComputableInPolyTime.comp` is still marked `proof_wanted` in
`Mathlib/Computability/TMComputable.lean`. Mathlib does not currently provide
P, NP, a formally NP-hard 3-SAT language, or Cook-Levin.

The external
[`LeanMillenniumPrizeProblems`](https://github.com/lean-dojo/LeanMillenniumPrizeProblems)
repository defines languages, verifier-based NP, polynomial-time many-one
reducibility, and NP-completeness on top of the same Turing-machine API. It
also records the missing composition theorem as an explicit hypothesis and
states that concrete NP-complete problems and Cook-Levin are still external.
It is a useful design reference, not yet a dependency that closes this
project's proof.

One web-indexed 2026 item claimed a reusable Lean `PolyReduction` framework
under arXiv identifier `2601.15571`. The current
[arXiv record](https://arxiv.org/abs/2601.15571) has a different title and
subject, and the associated search results did not lead to an inspectable Lean
repository. It is therefore excluded from the evidence base.

## Recommended path for this repository

1. Keep the current `ThreeCNF`, target decision problem, semantic equivalence,
   exact observation count, output cell size, and construction-cost theorems.
   They are already stronger than a correctness-only reduction sketch.
2. Introduce explicit source and target `FinEncoding`s, following the
   `LeanMillenniumPrizeProblems` interface but keeping the definitions local
   until a stable upstream library exists.
3. Prove that the concrete compiler is `TM2ComputableInPolyTime`. This requires
   an actual machine or a trusted compositional route from smaller verified
   machines; the current unit-cell operation count alone is not a bit-level
   Turing-time theorem.
4. Keep the final theorem conditional on a named, explicit
   “3-SAT is NP-hard in this model” premise unless and until a checked Lean
   Cook-Levin/3-SAT development is available.
5. Treat a self-contained Lean proof of Cook-Levin as a separate major project,
   not as a small appendix to the p-adic reduction.

This gives a clean boundary: the p-adic mathematics and construction can be
fully checked now, while the remaining missing result is recognisably a Lean
complexity-library problem rather than an ambiguity in the regression
reduction.

