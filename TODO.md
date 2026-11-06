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

Latest source-backed review: [6 November 2026](docs/2026-11-06-literature-review.md).
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
  trace, sign normalization and a machine bound remain open.
- [x] Compute a terminating two-row Euclidean pivot trace from the selected
  entries (`SmithPivot.lean`): clear one column entry, preserve gcd magnitude,
  outside rows, common zero columns and all integral transformation identities.
  Division is truncated toward zero. This is a local pivot, with no complete
  diagonalization, global growth or machine bound.
- [x] Compute one total active-column sweep (`SmithColumn.lean`), selecting all
  rows below a runtime diagonal position and each quotient from the updated
  matrix. Prove clearing, integral equivalence and protected-prefix preservation;
  missing rows/columns are no-ops. This meets the weak decomposition contract
  for at most one column, without a general diagonalizer or growth/runtime bound.
- [x] Establish a divisibility-aware pair reduction (`SmithReduction.lean`):
  exact division fixes the pivot row, while a nondivisible entry strictly reduces
  a nonzero pivot's magnitude. Prove the transposed cleared-column alternative,
  integral equivalence and total runtime-indexed wrappers. A checked two-pass
  matrix cycle rules out unmodified alternating gcd sweeps as a controller.
  These are local progress invariants, without a full controller or global bound.
- [x] Lift divisibility-aware progress across complete finite sweeps
  (`SmithSweep.lean`): a nonzero pivot stays nonzero and cannot grow; an
  active-column/active-row pair either clears both active arms or strictly
  decreases its magnitude. Preserve the protected prefix, all integral inverse
  identities and rectangular/empty guards. This is a finite pass, without a
  recursive diagonalizer, global coefficient bound or encoded-machine claim.
- [x] Implement terminating isolation of one active diagonal position
  (`SmithIsolation.lean`), including zero pivots: one seeding pass either
  isolates a zero pivot or starts strict nonzero-magnitude descent. Preserve
  all integral maps/inverses and protected prefixes, and advance both zero-block
  boundaries. Missing positions and empty rectangles are no-ops. This does not
  yet recurse over all diagonal positions or bound global growth/runtime.
- [x] Implement a computable decomposition returning integral transformations and
  inverses satisfying that contract (`SmithDiagonalization.decompose_valid`).
  Recursion over diagonal positions is terminating and preserves the completed
  off-diagonal prefix, including singular, rectangular and empty inputs. This
  is the weak diagonal contract, without canonical Smith normalization or a
  global coefficient-growth or polynomial-time claim.
- [x] Bound the semantic sweep-pair count of one existing isolation by `s+1`
  in its own complete dense input bit length (`SmithIsolationCount.lean`).
  A failed nonzero pair halves the pivot magnitude; the count replays the
  exact five-matrix result and includes zero seeding and missing positions.
  This does not count arithmetic within a pair or bound later-stage widths.
- [x] Bound every prefix of one computed Euclidean pivot on all five matrices
  (`SmithPivotBounds.lean`). Its trace has at most eight additions per bit of
  the second selected entry, and all multipliers have bounded magnitude.
  For complete dense input length `s`, every intermediate magnitude is at most
  `2^(8s²+9s)`; the complete single-pivot output has quartic encoded length.
  The total single-entry reducer has the same output bound in both orientations,
  including empty/missing cases. This is local growth and a semantic addition
  count, without a global polynomial width invariant or machine runtime.
- [x] Bound every addition prefix of one complete divisibility-aware column/row
  sweep pair (`SmithSweepBounds.lean`). A selected-column invariant prevents
  compounding the local width bound at each target. The computed trace replays
  the existing controller exactly, with a degree-four semantic addition count,
  degree-seven widths and degree-nine full output size in original dense input
  bits. Both inverse maps, zero pivots and rectangular/empty guards are covered.
  Repeated isolation/global growth and uniform machine costs remain open.
- [x] Reduce the five-matrix growth obligation to bounds on the two forward
  transformations (`SmithForwardBounds.lean`). Integral inverse identities and
  the existing determinant bound control both inverse maps; `U*A*V=S` controls
  the transformed matrix. The implication covers every actual trace prefix and
  complete encoded output, including empty rectangles. Its forward-map bounds
  are hypotheses, not a proved global invariant for the diagonalizer.
- [x] Reify the complete existing diagonalizer as an addition trace and prove
  exact five-matrix replay (`SmithTraceCount.lean`). Given a positive common
  transformed-entry width `b` at every prefix, its row/column addition count
  is at most `8s²b(b+1)` in actual dense input length `s`. The prior forward-map
  hypotheses imply the corresponding count bound. The common width remains
  unproved globally; no arithmetic, trace-construction or machine cost follows.
- [ ] Prove correctness and termination of the chosen controlled-growth algorithm.
- [ ] Bound all intermediate coefficients, operation count and complete encoded
  output by polynomials in actual input bit length; implement uniform machines
  for the arithmetic primitives and algorithm.
- [ ] Compose the resulting polynomial-time decomposition with
  `MaxObjectiveSmith.rhoMax_rational_smith`, denominator clearing and the binary
  cost of evaluating the max residual, removing the supplied-decomposition
  assumption without introducing unproved runtime witnesses.

The headline theorem remains partial until these obligations are discharged.

## Ordinary summed regression witnesses and conditional counting

This separate programme follows the 28 October thesis addendum and the
`p-adic-regression-complexity-proofs` automation request. It does not change
the Smith programme or any schedule. See `THEOREM_STATUS.md` for the exact
source hash and separate semantic, size and machine milestones.

- [x] Reduce every rational design to independent original columns with the
  same prediction space; refine contacts and attain the summed optimum in a
  finite family, including rank deficiency, rank zero and repeated/conflicting
  observations (`RationalWitnesses.lean`). The affine case is included.
- [x] Express a selected optimum by a nonsingular rank-size minor and the
  exact Cramer determinant ratios (`exists_global_minimizer_cramer`).
- [x] Bound the common-denominator product in actual input bits and the
  integer determinants after clearing denominators; transfer to reduced
  rational numerator/denominator sizes and full certificate encoding length.
  `RationalWitnessBounds.lean` and `RationalWitnessEncoding.lean` prove the
  ordinary bound `12L³+9L+1` and affine bound `28(L+1)³+9(L+1)+1` in original
  binary input length, with signs, framing, dimensions and zero coefficients.
- [x] Implement fixed-divisor binary long division and the actual fixed-prime
  valuation machine. `FixedDivisorBinary.computableInPolyTime` uses `2s+3`
  TM2 steps; `PadicValuationMachine.computableInPolyTime` uses at most
  `4(s+1)²`, returning unary valuation of length at most `s`. Zero, final
  failed division, canonical quotients, state reset and cleanup are checked.
- [x] Bound the intermediate unreduced fractions in exact residual evaluation,
  norm computation, loss summation and threshold cross-products.
  `RationalVerifierBounds.check_correct` and `threshold_iff_short_check` prove
  the executable arithmetic checker correct; prefix and power bounds are
  polynomial in actual combined input/certificate bits. Raw sign/framing costs
  and substitution of the short-certificate bound are checked. This completes
  arithmetic correctness/widths, not finite-machine implementation or time.
- [x] Implement fixed-base binary powering from the valuation machine's unary
  exponent and compose their actual machines. `FixedBasePowerMachine` computes
  `p^e` within `(2*size(p)+7)(e+1)²` TM2 steps, then computes
  `p^(padicValNat p n)` from binary `n` within
  `(2*size(p)+15)(size(n)+1)²` steps, including transfer and complete cleanup.
  Zero exponent, zero magnitude and any positive fixed base are covered.
- [x] Compose the full exact rational-norm machine on the original signed,
  framed binary fraction encoding. `RationalNorm.computableInPolyTime` includes
  parsing both fields, retaining the zero flag, both valuation-power calls,
  field exchange, binary serialization and cleanup. It covers unreduced and
  zero fractions with actual polynomial TM2 runtime for every fixed prime.
- [x] Decide validity of individual signed/framed fraction strings on **all**
  Boolean inputs. `RationalFractionValidity.valid_iff` characterizes exactly
  the existing `Fraction.encode` image; `Machine.outputsInTime` supplies a
  concrete finite TM2 bound of `3L+10` steps, including rejection and cleanup.
  Canonical magnitude bits, positive denominators and positive zero sign are
  enforced; unreduced fractions remain allowed. This is one field validator,
  not runtime-dimension input/certificate parsing or the full loss verifier.
- [x] Implement signed comparison on two concatenated existing integer words.
  `SignedIntegerComparison.outputsInTime` proves at most `2L+1` actual TM2
  steps, including signs, frames, reversals, comparison and cleanup/reset.
  `RationalThresholdComparison.lossComparisonOutputsInTime` specializes this
  to the final loss/threshold products with a cubic bound in combined source
  bits. Its input consists of **already computed and serialized products**;
  multiplication and producing this input are not included.
- [x] Implement multiplication of two variable binary magnitudes with a finite
  machine. `BinaryMultiplication.computableInPolyTime` proves a complete
  six-stack TM2 run within `6(L+1)²+12(L+1)` transitions, including routing,
  shifts, finite-carry additions, factor restoration and cleanup/reset.
  Here `L=size(m)+size(n)` counts the library tagged-pair symbols; the output
  is canonical binary, including zero, and has at most `L` bits.
- [x] Compose signed integer multiplication on concatenated original Boolean
  words. `SignedIntegerMultiplication.computableInPolyTime` includes sign/frame
  extraction, magnitude multiplication, sign retention, zero-sign correction,
  serialization and every adapter transfer. `Prepare.outputsInTime` gives
  `2L+2`; `Assemble.outputsInTime` gives `3T+1`. Their composition is polynomial
  without a supplied arithmetic-cost premise; no tight degree is claimed.
  Output is exactly `SmithEncoding.encodeInt (a*b)` with length at most `L`.
  Rational field routing and multiplication composition remain open.
- [ ] Construct and bound the actual binary rational-loss verifier, then
  compose NP membership with a checked encoding bridge from existing hardness.
- [ ] Prove unique-extension threshold 3-CNF with a linear balanced
  population-count circuit; transfer an explicit fixed-width counting
  hypothesis to optimisation/counting/recovery, with time and space bounds.
- [ ] Prove the uniform-sampling approximation theorem and all three compiler
  applications, retaining multiplicities and the distinct counting notions.

Next obligation: uniform binary input/certificate parsing and finite-machine
signed addition/subtraction and rational operations (reuse the completed
`SignedIntegerMultiplication` on signed/framed words); compose residual evaluation
with the completed rational norm machine, then exact summation and the final
comparison machine. Charge construction and serialization of its cross-products.
Reuse the completed fraction-string validator; still reject invalid dimensions, counts and whole input/certificate
structures, and charge traversal and machine composition.
In particular, retain the decoded fields, check the `r*(d+1)` data count and
`d` certificate count, and reject oversized binary counts without expanding
them into exponentially long unary loops.
Reuse the polynomial prefix, power and cross-product width bounds.
No gcd is needed by this evaluator. The complete machine verifier remains
absent: the executable Lean checker is not a machine-time theorem. Then connect
the certificate bounds to NP membership and prove the binary-rational encoding
bridge from existing hardness before concluding NP-completeness.

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
