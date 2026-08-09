# Lean formalisation to-do

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
