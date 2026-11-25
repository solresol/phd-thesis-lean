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

Latest source-backed review: [13 November 2026 checkpoint](docs/2026-11-06-literature-review.md#13-november-2026-checkpoint).
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
- [x] Prove exact determinantal target numerators for the existing row/column
  pair reducers (`SmithPivotMinors.lean`), and preservation of `S,S` and `S,U`
  minors at every Euclidean addition prefix. The gcd-scaled target bounds
  give at most `s+1` magnitude bits for the cleared forward row from an initial
  dense input of length `s`, including an all-zero pair. A parametric fixed-input
  shear proves that small transformed entries/minors alone cannot bound forward
  maps for arbitrary traces. This is a local invariant and an obstruction to
  one attempted global argument, not a global bound for the computed trace.
- [x] Sharpen one computed Euclidean pivot's all-five, every-addition-prefix
  width by charging each quotient against the next selected magnitude
  (`SmithPivotLinearBounds.lean`). The local exponent is `d+9c`, replacing
  `d+8c(c+1)`; from dense input length `s` it is `10s`. Complete single-entry
  output length is at most `80s³+16s²+10s+25`, in either orientation and with
  empty/missing guards. This uses the actual quotient choices and bounds the
  pivot row too; it does not control iterated sweeps/stages or machine runtime.
- [x] Reduce the computed diagonalizer's global growth obligation to transformed
  entries alone (`SmithComputedBounds.lean`). A positive prefix width `b` for
  `S` bounds actual quotients, then all five matrices by exponent
  `s+8s²b(b+1)²`, and bounds the complete encoded output. The polynomial
  transformed-prefix and forward-prefix growth obligations are proved equivalent
  for this controller. Neither polynomial witness is constructed; arbitrary
  traces do not admit this reduction, and no machine time is claimed.
- [x] Prove exact Schur-complement entries and a noncompounding transformed
  prefix bound for an exact-division sweep pair (`SmithExactDivision.lean`).
  If the incoming pivot divides both arms and earlier pivot-column entries
  vanish, transformed width is at most `2c+2` at every addition prefix, with
  at most `m+n` additions. All five matrices have exponent `2s²+4s`, and the
  complete output has at most `16s⁴+32s³+16s²+10s+25` bits. Missing/empty cases
  are included. These premises are not proved through pivot-changing phases
  or later stages; the global polynomial invariant and machine costs stay open.
- [x] Relate two consecutive exact pairs at successive positions to incoming
  3-by-3 minors (`SmithExactMinors.lean`). All transformed-entry prefixes have
  height at most `6H³`, hence width `3c+3`, instead of composing two quadratic
  estimates. In actual input bits `s`, all five prefix magnitudes are at most
  `2^(6s²+9s)` and complete output size is quartic. Zero pivots, missing positions
  and empty rectangles are included. A checked counterexample shows that exact
  arms need not persist to the next position; no global premise propagation,
  polynomial width witness or machine-time theorem follows.
- [x] Control arbitrarily many exact stages by selected incoming minors
  (`SmithExactStages.lean`). Zero exact stages are idle and their indices can
  be omitted. For `k` successive stages, every transformed-entry prefix has
  height at most `(k+1)! H^(k+1)`, hence width `(k+1)(c+k+1)+1`. For at most
  `min m n` stages, all five matrices have a quartic exponent in original input
  bits and complete output has a degree-six bit bound. Singular, rectangular,
  zero-pivot and empty cases are included. Exactness is required separately
  at every stage; pivot-changing phases, the unconditional computed-trace bound
  and uniform machine runtime remain open.
- [x] Transport variable-row/column minors through every prefix of one actual
  Euclidean or exact-division reducer (`SmithPivotMinorTransport.lean`). Fixed
  selected rows avoid the mixed pair. An incoming minor exponent `d` grows to
  at most `d+9c` for selected-entry width `c`, independently of minor order.
  Genuine row minors omitting the mixed-in row use at most `2s²+9s+1` bits
  through one reducer from dense input length `s`. A checked counterexample
  rules out unchanged-minor propagation through an outside row mixture.
  Repeated pivot/stage growth and uniform machine costs remain open.
- [x] Close the family of all fixed-order minors through every target of one
  actual column sweep (`SmithMinorFamily.lean`), and through the transposed row
  sweep. The selected-column invariant gives exponent `d+9*length(rows)*c`,
  independent of minor order, from incoming family exponent `d` and selected
  width `c`. Every minor has at most `11s²+1` magnitude bits through either
  sweep from original dense input length `s`; repeated selections, zero order,
  missing positions and empty rectangles are covered. This permits changing
  selected rows between reducers within one sweep. The width needed by the
  next alternating sweep, global stage growth and machine costs remain open.
- [x] Transport the all-minor family through both phases of one actual
  column/row pair (`SmithCrossMinorFamily.lean`). Order-one control proves the
  second phase's incoming width at the updated midpoint. Every minor at every
  addition prefix has at most `81s³+20s²+9s+1` magnitude bits in original dense
  input length `s`, including rectangular/empty cases. A checked pair shrinks
  its pivot while growing another entry. Iteration still compounds the width
  estimate; global polynomial growth and encoded-machine costs remain open.
- [x] Rule out an additive bit allowance depending only on dimensions and the
  current pivot decrease. A reachable second pair in dimension three takes
  pivot 2 to 1 with unbounded entry-height amplification.
- [x] Test the maximum absolute original minor as a pair-boundary entry bound.
  A checked two-row witness exceeds it. A weighted combination of original
  minors would still need a bound on its coefficients.
- [x] Prove the equivalence of global prefix growth and polynomial total multiplier width across the computed trace (`SmithMultiplierBudget.polynomial_budget_iff`). A polynomial bound on that sum remains open.
- [x] Charge the computed multipliers of one row sweep to the incoming selected column, retaining the final pivot width as credit (`SmithMultiplierBudget.sweepRows_budget`). The following result covers the first turn.
- [x] Bound the first turn from a dense input using each distinct incoming column field once (`SmithMultiplierBudget.initial_column_budget`, `initial_turn_width`).
- [x] Telescope the pivot-width credit through all passes of one isolation (`SmithMultiplierBudget.isolate_budget_credit`).
- [ ] Bound the cumulative exposed target charges in original input bits, then control transfer between diagonal stages.
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
  Rational field routing and multiplication are supplied by the next increment.
- [x] Compose multiplication and comparison directly on pairs of original
  signed/framed binary fractions, including unreduced and zero fractions.
  `RationalArithmetic.multiplicationComputableInPolyTime` computes both fields;
  `comparisonComputableInPolyTime` constructs and serializes both cross-products
  before comparing them. The router takes exactly `2L+10` steps; assembly takes
  at most `2T+2`; checked composition charges both multipliers and all transfers.
  Each serialized fraction product or cross-product pair has length at most `L`.
  This covers encoded fraction pairs, not malformed-string rejection or loss
  evaluation. The final loss-comparison specialization consumes an already
  evaluated and serialized loss fraction.
- [x] Prove natural subtraction of aligned canonical binary magnitudes with an
  actual finite machine. `BinarySubtraction.Machine.computableInPolyTime`
  computes `m-n` in exactly `2L+2` transitions, including borrow propagation,
  underflow disposal, high-zero normalization and cleanup/reset. Here
  `L=max(size(m),size(n))` counts the library aligned-pair symbols; output has
  at most `L` bits. This is not yet signed/framed arithmetic or its input router.
- [x] Implement signed addition and subtraction on the original concatenated
  Boolean integer words. `SignedIntegerAddition.additionComputableInPolyTime`
  and `subtractionComputableInPolyTime` each use at most `4L` actual finite TM2
  transitions. Both frames, magnitude comparison with digit retention, recovery,
  finite carry/borrow arithmetic, high-zero removal, sign selection, output
  framing and cleanup/reset are charged. Output is exactly the original signed
  encoding of the result and has length at most `L`. Equal/mixed signs, zero,
  cancellation and unequal widths are included. This is encoded-pair arithmetic,
  not arbitrary malformed-string validation or full rational-loss evaluation.
- [x] Compose fraction addition/subtraction on original Boolean fraction pairs.
  `RationalAddition.additionComputableInPolyTime` and
  `subtractionComputableInPolyTime` compute exactly the existing unreduced
  `Fraction.add`/`Fraction.sub` output. Three variable signed products, signed
  addition/subtraction, full source copying, denominator projection, retained
  components, serialization and all pair/sequential transfers are charged.
  Copying takes exactly `3L+3` steps; projection takes `u+2v+2`; output length
  is at most `2L`. No gcd, arithmetic-cost premise or runtime hypothesis is
  needed. This is encoded-pair arithmetic, without whole-input validation or
  traversal/accumulation across regression rows and columns.
- [x] Prove actual polynomial-time runtime-length fraction summation.
  `RationalSum.computableInPolyTime` and `sumComputableInPolyTime` consume a
  delimited internal list and return the exact unreduced fold/sum. Every
  addition and controller/transfer step is charged; the remaining tail is
  retained. An additive source-width budget bounds every accumulator prefix,
  giving total time `(L+1)*(P(8L+6)+24L+24)` and output length `4L+3`.
  `boundedLossOutputsInTime` charges summation of the already serialized norm
  list in original combined input/certificate bits. Norm-list production is
  supplied by the following increment; the original binary-counted parser and
  residual-list production remain open.
- [x] Runtime-length norm traversal and summed loss from serialized residuals:
  `RationalNormList.computableInPolyTime` produces the exact norm list with its
  summation prefix, charging every call, tail/prefix retention, delimiter and
  reversal. In full internal source length `L`, time is
  `(L+1)*(P(L)+(8*size(p)+2)*L+20)` and output length is at most
  `(4*size(p)+8)*L+6`. `sumComputableInPolyTime` composes exact summation;
  `boundedLossOutputsInTime` charges both phases in original combined bits.
  This component starts with serialized residuals; their production is supplied
  by the internal checker below.
- [x] Compute a runtime-length rational dot product and one complete residual.
  `RationalDotProduct.computableInPolyTime` traverses internal paired columns,
  charges each product and all transfers, and emits the exact summation format
  in `(L+1)*(P(L)+4L+6)` steps with length at most `L+6`. Its sum composition
  performs accumulation. `RationalRowResidual.computableInPolyTime` retains the
  response, erases pair tags and subtracts; `evaluate_row` identifies the exact
  original unreduced residual. `boundedRowOutputsInTime` charges the full
  arithmetic phase in original combined bits `S` via source bound `8S²+11S+3`.
  This component starts with serialized paired columns; the later pairing,
  broadcast and residual-traversal increments supply them from internal rows.
- [x] Pair separate delimited row/certificate lists with a concrete finite
  machine (`RationalColumnPairing`). Success takes at most `3L+2` transitions;
  unequal field counts clear both source tails and partial output in `3L+5`,
  producing a word disjoint from valid paired lists. Compose pairing with the
  complete response-preserving residual machine. Original combined source
  bits give bound `8S²+12S+3`; order, multiplicity, signs, unreduced fractions
  and zero columns are covered. The following increment supplies certificate
  reuse and all per-row sources; the later internal checker supplies outer
  arithmetic. Original binary parsing remains open.
- [x] Reuse one certificate across runtime-many observation sources:
  `RationalCertificateBroadcast.computableInPolyTime` copies/restores the
  certificate for every row and serializes the exact separated row inputs in
  at most `3L²+8L+5` actual TM2 steps. All cleanup and final reversal are charged;
  output length is at most `L²+L`. `source_length_le` gives `L≤2S` in original
  combined input/certificate bits, so `regressionOutputsInTime` takes at most
  `12S²+16S+5` steps. Empty shapes and order/multiplicity are covered. The source
  already contains delimited rows and one delimited certificate; binary parsing
  remains open; the next increment executes the produced row list.
- [x] Execute every row and compose the internal regression checker:
  `RationalResidualList.computableInPolyTime` runs the existing pairing/residual
  machine for each framed row, preserving the unprocessed tail and accumulated
  residuals. In complete framed input length `L`, its actual bound is
  `(L+1)*(P(L)+2Q(L)+2L+6)`, where `P` is the proved row-machine time and
  `Q(L)=L+P(L)*machinePushBound` is a proved output bound. The finite loop charges
  all transfers, delimiters, cleanup and final reversal. No cost premise is given.
  `RationalRegressionInternal.computableInPolyTime` composes certificate reuse,
  this traversal, exact norms and sum, threshold retention, cross-products and
  comparison. `outputsInTime` gives polynomial time in original combined bits
  `S`, via a proved full internal source bound `3S`. `check_correct` identifies
  the thesis decision test. The typed source has equal row/certificate lengths;
  original binary parsing, count checks and malformed-input rejection are open.
- [x] Retain and validate original binary field prefixes on every raw input:
  `RationalFractionPrefix.Machine.computableInPolyTime` takes at most `4L+10`
  actual TM2 steps to split one signed/framed stored fraction from its suffix.
  `parse_iff` and `parse_none_iff` give exact success/rejection; signs, zero,
  canonical magnitudes and denominator positivity are checked, with unreduced
  fractions retained literally. `naturalComputableInPolyTime` validates and
  retains a canonical binary count prefix (zero included) in `4L+11` steps.
  Every success emits the original bits plus one delimiter; all failure paths,
  copying, cleanup and state reset are charged. Numeric count values stay
  binary, so this is not yet their size bound or record compatibility check.
- [x] Bound binary counts before unary use, on every raw Boolean input
  (`BoundedBinaryCount`). The composed finite TM2 accepts exactly canonical
  count prefixes `n` with `n≤remainingPayload.length`, retains that payload,
  and emits `n` marks plus a delimiter. Its count phase takes at most
  `10*(M+1)²` actual steps, including overflow cleanup; the complete composition
  has proved polynomial time in original input bits and output length `2L+1`.
  Valid row/column dimensions, data counts `r*(d+1)` and certificate counts `d`
  pass; positive row count is required for the column-dimension result.
  Matching independently supplied counts and traversing the record remain open.
- [x] Traverse original binary-counted rational data/certificate lists on every
  raw word (`RationalCountedList`). Compose the bounded count parser with a
  five-stack finite TM2 validating exactly the declared number of fractions.
  Exact success/rejection, original field bits, ordering, multiplicities and
  suffix preservation are proved; the traversal takes at most `13M+6` actual
  transitions including all failure cleanup. Composition has polynomial time
  in original bits with output length at most `2L+1`. Empty lists, signs,
  unreduced fractions, malformed/truncated fields and oversized counts are
  covered. Whole-record shape and final input exhaustion remain open.
- [x] Check rectangular data shape and partition response/coefficient rows
  (`RationalRectangularFields`). A six-stack finite TM2 accepts parsed nonempty
  fields exactly when their count is `r*(d+1)`, retains the suffix and emits
  the existing internal observation words under a fixed alphabet renaming.
  Time is at most `4rd+21r+3d+4M+10`, or `32(L+1)²` in complete stage input
  length; output length is at most parsed payload length `M`. Every failure
  clears partial output and all private stacks. `originalDataOutputsInTime`
  charges this stage by `4S²+32S+14` in original combined bits; constructing
  its combined unary-dimension/parsed-data input is still to be composed.
- [x] Validate the original binary threshold/certificate suffix
  (`RationalCertificateTail`). Compose fraction-prefix parsing, delimiter
  routing and counted-list parsing with a five-stack finite machine checking
  exactly `d` coefficients and complete exhaustion. The threshold and every
  certificate bit are retained and reordered into the existing internal pair.
  The new routing and assembly bounds are `2L+2` and `5M+13`; the full suffix
  composition includes all transfers and is polynomial in unary `d` plus raw
  suffix bits. Output is at most twice the raw suffix length; original inputs
  charge the full suffix pipeline at `P(2S)`. Malformed/oversized/mismatched
  counts, invalid fields and any trailing data reject with complete cleanup.
- [x] Read both original binary dimension headers and the counted rational data
  in a single polynomial-time finite-machine pipeline (`RationalRecordPrefix`).
  A new three-stack router retains each unary terminator, distinguishing a
  valid zero dimension from failure, in at most `2L+2` transitions. Composition
  preserves both dimensions during all three parser calls and charges every
  transfer in the original binary length. `complete_iff` characterizes the
  successful stage markers; `output_original` identifies the exact dimensions
  and existing parsed-data word. Output length is at most `8L+7`. The raw
  threshold/certificate suffix is preserved; it has not been parsed here.
- [x] Execute original binary input through rectangular validation
  (`RationalRectangleAssembly`, `RationalRecordData`). The new four-stack
  machine checks both retained header delimiters, copies `d` and constructs
  the rectangular stage's physical input in at most `4L+10` transitions,
  including all failure cleanup. The complete pipeline accepts exactly valid
  payload-bounded dimensions and rational fields with count `r*(d+1)`;
  missing headers/data and mismatched rectangles reject. It preserves `d`,
  the exact internal observation rows and every raw suffix bit. Total machine
  time includes all original parsers, assembly, row validation and transfers;
  encoded output is at most `8L+7`. Original rational-record correspondence
  assumes positive row count, matching the thesis, and permits zero columns.
- [x] Compose all original binary parsing and validation while retaining the
  arithmetic inputs (`RationalRecordRouting`, `RationalRecordValidation`,
  `RationalRecordParser`). The four-stack router takes `2L+3` transitions;
  the three-stack joint failure guard takes `2M+2`. The complete machine
  includes every parser, rectangle check, row preservation during suffix
  validation, exact certificate count, exhaustion and transfer. Every raw
  input either yields the exact retained rows/certificate/threshold or the
  empty failure word; output length is at most `16L+14`. Original rational
  correspondence requires positive rows and allows zero columns.
- [ ] Construct and bound the actual binary rational-loss verifier, then
  compose NP membership with a checked encoding bridge from existing hardness.
- [ ] Prove unique-extension threshold 3-CNF with a linear balanced
  population-count circuit; transfer an explicit fixed-width counting
  hypothesis to optimisation/counting/recovery, with time and space bounds.
- [ ] Prove the uniform-sampling approximation theorem and all three compiler
  applications, retaining multiplicities and the distinct counting notions.

Next obligation: connect `RationalRecordParser` to the internal arithmetic
checker. Prove that every successful raw-word parse supplies a compatible
row/certificate source; reorder and relabel its retained rows and
certificate/threshold pair into `RationalRegressionInternal.encoding`, branch
empty parser output to false, and compose the checker with all transfers
charged. The parser already performs all original binary dimension/data reads,
rectangular checks, row preservation during suffix validation, certificate-count
agreement, complete exhaustion and joint rejection. Do not rebuild those stages.
Then join the short-witness theorem to NP membership and prove the
binary-rational encoding bridge from existing hardness before concluding
NP-completeness. The external SAT counter remains an explicit hypothesis for
later conditional results; none is used here.

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
