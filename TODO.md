# Lean formalisation to-do

## Review weekly human literature findings before choosing research

Before choosing research on each run, review the latest findings from the
separately scheduled weekly human-authored literature check for this exact
problem and its key sublemmas. Reuse those findings; a fresh search on every run
is not required. The weekly check should prioritize new and revised arXiv papers
and relevant mathematics, theoretical computer science and computational journals,
and broaden beyond familiar authors and sources.

Keep a dated source record in the research notes: source URLs, paper versions
and access dates, changes since the previous check, whether each finding is a
proved result, computational evidence or an unverified claim, and its effect on
the next research choice. Read the actual theorem hypotheses and match them to
this project's formulation; similar titles do not establish equivalence. Other
bots' claimed results are not established progress. Reuse and cite applicable
results with license and attribution respected, and retire superseded searches
while preserving the record of retired hypotheses and existing proof standards.
If the weekly findings are missing, stale or sources are unavailable, record that
limitation rather than claiming no progress elsewhere. This requirement alone
is not evidence that a literature check occurred. Do not contact authors, change
dependencies or broaden the research target without authorization. This section
does not enable or modify any schedule.

## Active target: polynomial-bit-complexity Smith decomposition

Latest source-backed review: [24 October 2026](docs/2026-10-24-literature-review.md).
Review Ji's existing Kannan–Bachem artifact before duplicating its proof
architecture; its nonsingular-square arithmetic model does not close our
rectangular encoded-machine target. The headline status remains partial.

`cor:all-different-csp` is complete. Do not reopen that compiler queue. The next
target is the missing algorithmic ingredient of `thm:max-polytime`, on the existing
stable Lean/mathlib pins. See [the proof plan](docs/smith-complexity-plan.md) for the
exact interface, encoding obligations, daily prompt and stopping criteria.

- [x] Establish one reversible integer row-addition primitive, identify it with
  mathlib's transvection multiplication, and bound its coefficient magnitude in
  both uniform-height and power-of-two forms (`SmithRowOperations.lean`). These
  are local arithmetic invariants, not a Smith algorithm or runtime bound.
- [x] Define checked binary integer-matrix input/output encodings, including
  explicit dimension costs and zero-dimensional cases (`SmithEncoding.lean`).
  This serializes individual matrices. No serializer machine is claimed.
- [x] Specify finite decomposition output data and an executable supplied-output
  checker (`SmithDecomposition.lean`), keeping canonical Smith conditions
  separate. Prove the projection to the existing optimizer and conditional
  full-output bit bounds; this does not construct a decomposition.
- [x] Execute finite row/column addition traces with both integral inverses and
  `U*A*V=S`, materializing all five matrices in the existing dense storage
  (`SmithTrace.lean`). Diagonality is conditional; selecting a controlled-growth
  trace, swaps/sign normalization and a machine bound remain open.
- [ ] Implement a computable decomposition returning integral transformations and
  inverses satisfying that contract.
- [ ] Prove correctness and termination of the chosen controlled-growth algorithm.
- [ ] Bound all intermediate coefficients, operation count and complete encoded
  output by polynomials in actual input bit length; implement uniform machines
  for the arithmetic primitives and algorithm.
- [ ] Compose the resulting polynomial-time decomposition with
  `MaxObjectiveSmith.rhoMax_rational_smith`, denominator clearing and the binary
  cost of evaluating the max residual, removing the supplied-decomposition
  assumption without introducing unproved runtime witnesses.

The headline theorem remains partial until these obligations are discharged.

## Precision-indexed p-adic prediction growth

Source: `../phd-thesis/pac-learning-open-questions/body.tex`, Section
`sec:precision-indexed-growth` in the active thesis checkout.

This queue is complete. The finite-precision prediction-pattern interface and
all five statements are formalised in
[`PhdThesisLean/PrecisionGrowth.lean`](PhdThesisLean/PrecisionGrowth.lean),
stated first in terms of finite images and cardinalities as planned, with the
affine base-`p` logarithm identity included via `Nat.log`.

- [x] `prop:precision-growth-covering` — define reduction of a prediction
  vector modulo `p ^ k` and prove that the number of realised patterns is the
  covering number of the prediction image by radius-`p ^ (-k)` balls in the
  product sup metric.  Done: `precision_growth_covering`.
- [x] `prop:precision-growth-vc` — at `p = 2` and `k = 1`, identify the
  finite-precision pattern count with the ordinary binary growth function and
  derive the usual VC shattering criterion.  Done: `precision_growth_binary`
  and `precision_growth_vc`.
- [x] `thm:affine-precision-growth` — for affine maps on `ZMod (p ^ K)`, prove
  that the maximal reduced evaluation-image cardinality on an `m`-sample is
  `p ^ (k * min m (d + 1))`; use `0, e_1, ..., e_d` for the lower bound.
  Done: `affine_precision_growth` and `affine_precision_growth_log`.
- [x] `prop:tree-syntax-growth-bound` — formalise the finite description-count
  bound for rooted tree shapes with bounded split-rule choices and
  `ZMod (p ^ k)` leaf labels.  Done: `tree_syntax_growth_bound`.
- [x] `cor:binary-tree-precision-growth` — specialise the preceding bound to
  ordered full binary trees using the Catalan count and `L = I + 1`.
  Done: `binary_tree_precision_growth`.

The correspondence audit and completion status remain authoritative in
[`THEOREM_STATUS.md`](THEOREM_STATUS.md).
