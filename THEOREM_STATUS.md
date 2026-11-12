# Thesis theorem formalisation status

Audited against the active thesis checkout and the copied statements at thesis
commit `2c6418bcf9643fc6e039237f0f59ace14b2557fc` on 24 July 2026.

“Complete” means that the mathematical content has a checked Lean declaration,
the project contains no `sorry` or `admit`, and the correspondence has been
reviewed. “Partial” means that the semantic reduction is checked but a
complexity or encoding claim in the LaTeX statement is not. “Pending” means
that no statement-faithful Lean theorem is currently present.

## Next algorithmic ingredient

`thm:max-polytime` remains **Partial**: the optimizer formula still receives an
integer decomposition and inverse identities as hypotheses. The active plan is
[polynomial-bit-complexity Smith decomposition](docs/smith-complexity-plan.md).
`SmithRowOperations.lean` now checks one local primitive: row addition equals
mathlib transvection multiplication, is reversible for distinct rows, and has
uniform-height and power-of-two coefficient bounds. Its four declarations audit
with only `propext`, `Classical.choice` and `Quot.sound` (some use a subset).
`SmithEncoding.lean` also supplies a finite executable dense integer-matrix
record and checked canonical Boolean encoding: unary dimensions, row-major
signed binary entries, exact entry count and complete-input checking. Its
`decode_encode` and `encode_of_decode` establish round-trip and accepted-input
canonicality. `encode_length` charges both dimension headers and every sign,
separator and magnitude bit; `accepted_dimensions_le_length` covers empty and
rectangular inputs. `encode_length_le_of_entry_bits` bounds serialization only
**given** a binary-magnitude bound, without asserting that an algorithm maintains
one. The twelve audited declarations use only `propext`, `Classical.choice` and
`Quot.sound` (some use a subset).

`SmithDecomposition.lean` now adds a finite output record with all four integral
transformations/inverses and the rectangular diagonal matrix, an executable
supplied-output checker, and separate canonical Smith conditions.
`Valid.maxHypotheses` and `rhoMax_of_valid` project the weak contract into the
existing rational max formula. The five framed matrix serializations include
all inverse entries and dimension headers; `encode_length_le_of_input_bits`
bounds their total by `2*(5s+10+2s²*(2b+2))+5`, conditional on every stored
coefficient having binary magnitude length at most `b`. This is not an
algorithmic output-growth bound. Its nine audited declarations use only
`propext`, `Classical.choice` and `Quot.sound` (or subsets). The combined output
decoder, global growth bound and uniform machine remain absent. A terminating
construction of the weak contract is now supplied by `SmithDiagonalization.lean`
below.
`SmithTrace.lean` constructs all five stored matrices by interpreting finite
row/column addition traces. `step_invariant`, `run_invariant` and
`execute_equivalence` prove both integral inverse directions and `U*A*V=S`;
`pack_matrix` checks that materializing entries preserves their matrix values.
`execute_valid_of_diagonal` supplies `Valid` only when the computed output is
diagonal. `executeDense` accepts the existing runtime-dimension dense input;
the additional trace is not computed from that input alone. The nine audited
declarations use only `propext`, `Classical.choice`, `Quot.sound` (or subsets).
This is an execution invariant, not diagonalizing trace selection, a bound on
intermediate or output coefficients, or a uniform machine implementation.
`SmithPivot.lean` now selects a terminating addition trace for a pair of rows
at a supplied column. `gcdTrace_correct` proves the second entry becomes zero,
the first has magnitude equal to the original gcd, and outside rows are fixed.
`gcdTrace_preserves_zero` also preserves common zero columns of the selected
rows. The recursion uses truncating division and strict natural remainder
descent, rather than the potentially slow signed-swap/Euclidean-division
variant. `pivotDense_correct`, `pivotDense_equivalence` and
`pivotDense_preserves_zero` connect this computation to the existing dense
storage and all five integral identities. The eleven audited declarations use
only `propext`, `Classical.choice`, `Quot.sound` or subsets. No pivot sign
normalization, full diagonalizing controller, logarithmic step bound, global
coefficient bound or uniform machine cost is claimed.
`SmithColumn.lean` computes a complete active-column sweep from the updated
matrix, selecting every row below a runtime diagonal position. `sweep_clears`
preserves previously cleared entries as well as clearing every visited nonpivot
row. `clearColumn_prefix` fixes earlier rows and columns **provided all active
rows were zero in the earlier columns**. `clearColumn_next_zero` advances the
zero lower-left block boundary. `clearColumn_of_missing` supplies the
total rectangular/empty base cases. `clearColumnDense_equivalence`,
`clearColumnDense_clears` and `clearColumnDense_prefix` connect the controller to
all five stored matrices and their integral identities.
`clearColumnDense_valid_of_cols_le_one` meets the weak `Valid` contract for
inputs with at most one column; it makes no canonical sign claim. The sixteen
audited declarations use only `propext`, `Classical.choice`, `Quot.sound` or
subsets. This is one executable controller pass, without a general alternating
row/column diagonalizer, coefficient bound, operation count or machine witness.
`SmithReduction.lean` adds a divisibility-aware pair reduction: exact division
clears the target while fixing the entire pivot row; otherwise a nonzero pivot
strictly decreases in magnitude (`reduceRows_strict`, `reduceRows_progress`).
Transposition retains all five integral identities, and
`reduceCols_clear_or_descend` proves that disturbing a cleared pivot column
requires strict pivot descent. Common zeros and outside rows/columns are
preserved. Total runtime-indexed row/column wrappers are no-ops at missing or
equal indices, including empty shapes; `reduceDense_equivalence` connects them
to the existing dense output. A kernel-checked two-pass matrix cycle exhibits
the failure of unmodified alternating gcd sweeps. The twenty audited declarations
use only `propext`, `Classical.choice`, `Quot.sound` or subsets. This is a local
progress alternative, without a full active-block controller, a polynomial
descent-count bound, global coefficient bounds or a machine implementation.
`SmithSweep.lean` lifts that alternative across complete finite sweeps.
`sweepRows_progress` proves that the entire pivot row is fixed or a nonzero
pivot strictly decreases; `sweepRows_nonzero_le` prevents subsequent pair
reductions from undoing that decrease. `cross_isolated_or_descend` proves that
an active-column pass followed by an active-row pass either clears both active
arms of the pivot or strictly decreases its original nonzero magnitude.
`cross_prefix` protects earlier rows and columns under the two zero-block
hypotheses, without a nonzero-pivot assumption. The runtime-indexed passes are
no-ops at missing positions, and `crossDense_equivalence` proves all five
integral identities for the computed stored result, including empty shapes.
`crossDense_isolated_or_descend` and `crossDense_prefix` transfer the two
controller claims to that same result. The thirty audited declarations use
only `propext`, `Classical.choice`, `Quot.sound` or subsets. A zero pivot is
processed by the total functions but is outside the nonzero descent claim.
The sweep increment supplies no recursive pivot-isolation/diagonalization
controller, polynomial descent count, global width bound or uniform machine.
`SmithIsolation.lean` now supplies the recursive **single-position** controller.
`sweepRows_eq_of_zero` proves that a sweep ending with a zero pivot was idle
on all five matrices; `cross_isolated_of_zero` therefore covers the zero outcome
of a seeding pass. `isolateNonzero` then repeats complete passes by strict
numeric-magnitude descent until both arms are clear. `isolate_isolated` has no
nonzero, rank or square hypothesis; `isolate_of_missing` handles missing/empty
positions. `isolate_invariant` preserves all integral inverse identities and
`U*A*V=S`, while `isolate_prefix` protects completed rows/columns under the two
zero-block hypotheses. `isolate_next_zero` advances both block boundaries,
even for an isolated zero with a nonzero trailing block. `isolateDense` stores
all five matrices in the existing encoding, and its equivalence, isolation and
prefix theorems refer to that computed result. The eighteen recorded axiom
audits use only `propext`, `Classical.choice`, `Quot.sound` or subsets. The
unmeasured seeding pass may increase a zero pivot, so descent is claimed only
after it; no bit-polynomial iteration or width bound follows. The recursion over
all diagonal positions is now completed by `SmithDiagonalization.lean`.

`SmithDiagonalization.decompose` computes all five dense output matrices from
the input alone. `isolate_prefix_succ` advances the invariant that every
off-diagonal entry touching a completed position is zero. `finish` recurses
through `min m n` positions; `finish_invariant` and `finish_diagonal` prove all
integral inverse identities, `U*A*V=S` and rectangular diagonality.
`decompose_valid` therefore establishes the full weak contract for every `Dense`
input, without a supplied trace, nonzero pivot, rank or square hypothesis.
`decompose_check` proves acceptance by the existing checker.
`decompose_of_empty` fixes the complete initial state in both empty orientations.
The eleven new declarations audit with only `propext`, `Classical.choice`,
`Quot.sound` or subsets. Finite evaluator regressions are separate evidence,
not the justification for the universal correctness theorem.

This completes a terminating weak integer diagonalizer. Canonical signs, zero
ordering and successive divisibility are not claimed. The unchanged output
bound still assumes a bound on every entry of all five matrices; there is no
global coefficient bound, polynomial operation count or encoded-machine runtime
theorem. Full optimizer composition remains open. The headline completion counts below
are unchanged, and the all-different CSP corollary stays complete.

`SmithIsolationCount.lean` now bounds one isolation's semantic sweep-pair count
by `s+1`, where `s` is that isolation input's complete dense encoded length.
`cross_pivot_dvd` and `cross_failure_halves` strengthen strict numeric descent
to proper-divisor halving. `nonzeroPasses_le_size` gives one pair per pivot
magnitude bit after seeding. `cross_pivot_le` bounds the seed pivot by the
incoming matrix height, even when initially zero; this yields
`isolationPasses_le_input_length` for arbitrary runtime positions and singular,
rectangular or empty inputs. `isolationPasses_replay` and
`isolate_eq_bounded_crosses` identify the exact existing result, including all
integral maps and inverses. This counts recurrence transitions, without a cost
for their tests, pairwise arithmetic, Lean evaluation or machine execution.
Later diagonal stages have transformed inputs: their encoded lengths are not
yet polynomially bounded in the original input. Global widths of all five
matrices, complete arithmetic counts, uniform machines and optimizer composition
therefore remain open; `thm:max-polytime` stays Partial.

`SmithPivotBounds.lean` bounds the actual internal Euclidean addition trace.
`gcdTrace_length_le` gives at most `8 * natAbs(b).size` additions, and
`gcdTrace_coefficient_le` bounds every multiplier by the incoming pair's common
height (at least one). `gcdTrace_prefix_pow_bound` includes the temporary signed
swap additions and all entries of `S,U,Uinv,V,Vinv`. For one pivot from a dense
input of complete encoded length `s`, `pivot_prefix_bound` bounds every prefix
magnitude by `2^(8s²+9s)`. `pivotDense_output_length_le` and
`reduceDense_output_length_le` bound all five framed output matrices by
`64s⁴+72s³+16s²+10s+25` bits. The latter includes both reduction orientations,
divisible and zero branches, missing indices and empty shapes. The twenty-one
public declarations audit with only `propext`, `Classical.choice`, `Quot.sound`
or subsets. These are local bounds and a semantic addition count, with no
arithmetic-machine or traversal/serialization runtime theorem. Repeated local
width bounds still compound; no polynomial global invariant through a whole
isolation or all diagonal stages is supplied. Headline status stays Partial.

`SmithSweepBounds.lean` extends those local bounds to one complete
divisibility-aware column/row sweep pair. `sweepRows_prefix_pow_bound` uses
the preserved selected-column height to bound all five matrices by
`2^(d+length(rows)*8c(c+1))`, including temporary signed swaps, repeated targets
and zero pivots. `crossTrace_run` replays the existing `cross` on the entire
five-matrix state. For complete dense input length `s`, put
`W=s+8s²(s+1)` and `C=W+8s(W+1)(W+2)`.
`crossTrace_input_prefix_bound` bounds every actual addition prefix by `2^C`;
`crossAdditions_le_input_length` bounds its semantic length by
`8s²+8s(W+1)`. `crossDense_output_length_le` bounds all five framed matrix
encodings by `2*(5s+10+2s²*(2(C+1)+2))+5`. These are degree-seven widths,
degree-four addition counts and degree-nine output size, retaining signs,
dimensions and both inverse matrices for arbitrary singular rectangles and
empty inputs. The 34 public declarations audit with only `propext`,
`Classical.choice`, `Quot.sound` or subsets. No quotient, arithmetic, traversal,
trace-construction or serialization machine cost is assigned. Iterating the
degree-seven width update over a bit-bounded number of pairs does not yield
a polynomial global bound. Polynomial widths through full isolation and all
diagonal stages, uniform machine runtime and final optimizer composition
therefore remain open; `thm:max-polytime` stays Partial.

`SmithForwardBounds.lean` reduces the required global size invariant to the
two forward transformations, conditionally. `inverse_entry_natAbs_eq_adjugate`
uses an integral left inverse to identify its entry magnitudes with cofactors;
`inverse_natAbs_le_pow` reuses the existing determinant bound to give
`|(Uinv)ij| <= 2^(m*(d+size(m)))` when `|Uij| <= 2^d`, and likewise for `V`.
For original complete dense input length `s`, `bounded_of_input_forward` proves
all five matrices have magnitudes at most `2^B`, where
`B=(s+2)*(d+s+1)`, from the two forward bounds and the existing integral
state invariant. `trace_prefix_bound` applies to any actual addition prefix,
including an unfinished signed swap; `output_length_le_of_forward` gives the
full framed output bound `2*(5s+10+2s²*(2(B+1)+2))+5`.
These implications preserve arbitrary singular/rectangular and empty shapes.
The hypotheses on `U,V` have not been established uniformly across repeated
sweep pairs and diagonal stages. No global polynomial, new algorithm, machine
runtime or optimizer composition is inferred; `thm:max-polytime` stays Partial.

`SmithTraceCount.lean` reifies the entire existing diagonalizer's selected row
and column additions. `decomposeTrace_result` proves exact equality with all
five computed matrices; `decomposeTrace_valid` has no width premise. For a
positive common transformed-entry width `b` at **every addition prefix**,
`decomposeTrace_length_le_of_width` bounds the semantic row/column addition
count by `8s²b(b+1)`, where `s` is the complete original dense input length.
`decomposeTrace_length_le_of_forward` gives `8s²(B+1)(B+2)`, with
`B=(s+2)*(d+s+1)`, assuming the two forward transformations have magnitude at
most `2^d` uniformly through the computed trace. These width assumptions are
still open, and no global polynomial `d=P(s)` is supplied. Rectangular,
singular, zero-pivot and empty cases are retained. All 23 new declarations
audit with only standard axioms. The count charges elementary matrix additions,
not their scalar implementation, division, traversal, trace construction,
serialization or uniform-machine execution. The headline remains Partial.

`SmithPivotMinors.lean` now proves exact determinantal numerators for the existing
pair reducer. At every addition prefix of `gcdTrace`, both selected `S,S` minors
and mixed `S,U` minors are fixed, including unfinished swaps. For row reduction
from selected entries `a=S[r,j]`, `b=S[s,j]`, let `g` be the **signed resulting
pivot**, `R=reduceRows Q r s h j`. Then
`g*R.S[s,l]=a*Q.S[s,l]-b*Q.S[r,l]` and
`g*R.U[s,c]=a*Q.U[s,c]-b*Q.U[r,c]`. The transposed theorem covers `S,V` for
column reduction. Both zero entries and the exact-division shortcut are included.
The gcd-scaled magnitude bounds yield target heights `2HK` in `S` and `2HF`
in `U` for a nonzero selected pair with selected height `H`, source-row height
`K`, and source-map height `F`. From identity maps the target's forward
coefficients have magnitude at most `2^s` and at most `s+1` binary magnitude
bits in original dense input length `s`, including the all-zero branch.
These endpoint bounds cover the cleared target, not the pivot row or the
complete five-matrix output. Existing integral inverse and empty-case contracts
are unchanged. Ten new declarations audit with only standard axioms.

The checked parametric family `A=[[1],[0]]`, trace `[row 0 1 t]`, leaves `S=A`
and all integral inverse identities intact while `U[0,1]=t`. Thus transformed
entries and their minors alone cannot control forward maps for arbitrary traces;
the actual diagonalizer needs a stronger controller-specific invariant. This is
not a lower bound or counterexample for `decomposeTrace`. The global polynomial
prefix bound, actual encoded-machine runtime, full output handling and optimizer
composition remain open; `thm:max-polytime` remains Partial.

`SmithPivotLinearBounds.lean` sharpens the existing actual Euclidean pivot,
without changing its trace. `pairStep_bound` pays only `|q|+1` for the completed
four-addition step on all five matrices, including the reversed inverse update.
`quotient_height_bound` charges that quotient to the next magnitude:
`(|a.tdiv b|+1)*|b| <= 2*max(1,|a|,|b|)`.
`gcdTrace_prefix_height_bound` then bounds every addition prefix by
`H*max(1,|a|,|b|)*2^L`, for incoming height `H` and actual trace length `L`.
The three temporary signed-swap additions are explicitly included. Combining
this with the existing `L<=8c` theorem gives the local exponent **`d+9c`**,
replacing `d+8c(c+1)`. No sign, nonzero-pair, rank or square premise is needed.
For original dense input length `s`, `pivot_prefix_bound` gives magnitude
`2^(10s)`. `pivotDense_output_length_le` and `reduceDense_output_length_le`
bound the complete five-matrix encoding by **`80s³+16s²+10s+25`**, including
the existing unary dimensions, signs and frames. The total single-entry reducer
retains exact division, both orientations, singular/rectangular inputs and
empty/missing no-op cases. These are arithmetic and encoding-size proofs.
The incoming widths of successive sweeps/stages are still uncontrolled in the
original input length. No fixed global polynomial for both forward maps,
uniform machine runtime or optimizer composition follows; the headline stays
Partial. The earlier quadratic local bound remains valid but is superseded
for this single-pivot/single-entry use.

`SmithComputedBounds.lean` now uses the actual controller's quotient selection
to reduce global growth to transformed entries alone. Given `b>0` and
`SmithTraceCount.PrefixWidth (initial A.toMatrix) (decomposeTrace A) b`, every
selected multiplier has magnitude at most `2^b`. The existing conditional count
then bounds all five matrices at every addition prefix by
`2^(s+8s²b(b+1)²)`, where `s` is the original complete dense input length.
`decompose_output_length_le` bounds the complete five-matrix encoding by
`2*(5s+10+2s²*(2*(s+8s²b(b+1)²+1)+2))+5`. Unary dimensions, inverse maps,
singular rectangles and empty inputs remain covered.
`polynomial_growth_iff` proves equivalence of existence of a polynomial
transformed-prefix width and existence of a polynomial bound for both forward
maps, specifically for the computed trace. It supplies neither polynomial
witness. This does not contradict the arbitrary-trace shear obstruction: that
trace has no controller-selected quotient guarantee. Arithmetic correctness,
conditional growth and semantic counts remain separate from machine costs.
No uniform machine, unconditional global growth bound or optimizer composition
is added; `thm:max-polytime` stays Partial. All ten new public declarations
were separately audited with only standard axioms (the width definition is
axiom-free); see the dated research record in the Smith plan.

## Headline statement catalogue

| Thesis label | Status | Lean declaration or remaining work |
|---|---|---|
| `core-theorem` | Complete | `ContactTheorem.contact_theorem`; the underlying theorem is slightly stronger. |
| `thm:fixed-prime-hardness` | Complete | `FixedPrimeMaxCut.fixed_prime_hardness` proves the complete Max-Cut reduction for every prime over `ℚ_[p]`: `local_boolean_snapping` (`lem:local-boolean-snapping`), the forcing objective `maxCutLoss` with `M_j = d_j + 1`, Booleanity of every global minimiser (`globalMin_boolean`), existence, the characterisation of global minimisers as embeddings of maximum cuts (`isGlobalMin_iff`), the Boolean value `∑ M_j + #monochromatic`, and the optimal value `∑ M_j + |E| - maxcut`. `homogeneousLoss_maxCutRows` identifies the objective with the homogeneous summed loss of an explicit `{0,1}`-valued row family of `5|E| + 2n` rows. Edges are an arbitrary finite index type (multigraphs allowed). The complexity statement is checked end to end: `PadicRegressionLanguage` states the decision problem as a `lean-np-hardness` `EncodedLanguage` (integral rows, natural bound, unary and binary CNF-style encodings); `FixedPrimeMaxCutReduction.maxCut_iff_regression` proves for every prime that the edge-streamed variant of the reduction (one forcing pair per edge endpoint, plus a pendant edge to a fresh vertex and `K + 2` constant rows absorbing the threshold) preserves membership, with snapping over `ℚ`; `FixedPrimeMaxCutMachine.fmcR_exits` and `cost_le` give an exact TM2 run within `10⁶(n+1)²` steps; and `encodedUnaryRegression_NPHard p` / `encodedRegression_NPHard p` derive NP-hardness from the library's Cook–Levin-based `encodedUnaryMaxCut_NPHard`. |
| `cor:affine-hardness` | Complete | `FixedPrimeMaxCut.intercept_pinning` proves `lem:intercept-pinning` for any integral instance (`L_aff(β,0) ≤ L_aff(β,c) - (T - r)‖c‖`, with `affineLoss_zero_lt` and `isGlobalMin_affine_iff` for `T ≥ r + 1`, and `affineRowLoss_pinnedRows` realising the pinning rows literally). `affine_hardness` then shows the affine minimisers of the pinned Max-Cut instance are exactly `(embed s, 0)` for maximum cuts `s`, with the same optimal value and `10|E| + 4n + 1` rows. The complexity statement is checked: the rows emitted by `FixedPrimeMaxCutMachine` include `r + 1` zero rows for `r` other rows, `FixedPrimeMaxCutReduction.loss_le_affineLoss` is intercept pinning over `ℚ` for these instances, `maxCut_iff_affine` proves the reduction to `PadicRegressionLanguage.AffineRegressionLang p`, and `encodedUnaryAffineRegression_NPHard p` / `encodedAffineRegression_NPHard p` conclude NP-hardness for every prime. |
| `thm:sparse-medoid-representation` | Complete | `SparseMedoid.sparse_medoid_representation`. |
| `prop:medoid-robustness` | Complete | `Medoid.medoid_robustness`. |
| `thm:threshold-coreset` | Complete | `Coreset.threshold_coreset`. |
| `prop:subset-summary-lower-bound` | Complete | `SubsetSummary.bounded_information_subset_summaries` and its weighted/unweighted component theorems. |
| `thm:max-polytime` | Partial | `MaxObjective.max_objective_attained` proves the minimum defining `ρ_max` is attained (for arbitrary `p`-adic data), and `max_objective_rational_optimum` proves that for rational data an optimal `β` may be chosen in `ℚ^n`, realising `ρ_max` (`max_objective_rational_optimum_rhoMax`); `exists_rat_solution_of_padic_solution` closes the exact-fit case by base change. The algorithm's reductions are checked: sup-norm invariance under `GL_m(ℤ)` (`norm_mulVec_generalLinearGroup`) and denominator clearing (`isGlobalMin_clear_denominators_iff`); `sum_objective_not_unimodular_invariant` witnesses the thesis's closing remark. `MaxObjectiveSmith` proves the algorithm's formula for any Smith decomposition `UAV = S` (`U`, `V` unimodular, `S` with zero off-diagonal): `smith_isGlobalMin` exhibits the optimiser `β = Vγ` with `γ_i = b'_i/s_i` (the image of a rational vector, `smith_optimizer_rational`), `rhoMax_smith` gives `ρ_max = max_{i>t}|b'_i|_p` over the zero rows of `S`, and `rhoMax_rational_smith` gives the thesis's `ρ_max(X, y) = |D|_p⁻¹ max_{i>t}|b'_i|_p`. `SmithDiagonalization.decompose_valid` now proves that a terminating rectangular integer algorithm computes a decomposition satisfying the weak contract. Global coefficient bounds, polynomial encoded-machine runtime and final optimizer composition remain open. |
| `thm:equidistributed-sum-refines-max` | Complete | `EquidistributedSumRefinesMax.equidistributed_sum_refines_max`: for `x_i ∈ ℤ_p^d` exactly equidistributed modulo `p`, an intercept in the model, and no exact affine fit, every `L_1` minimiser is an `L_∞` minimiser. The stronger `isGlobalMin_Linf_of_isGlobalMin_L1` drops the no-exact-fit hypothesis. The Lean proof is purely finite (a counting lemma `card_affZ_zero_mul_le` for nonzero affine functions on `𝔽_p^d` plus an average over `p` intercept shifts) and replaces the thesis's compactness and Haar-measure steps; the conclusion is identical. |
| `thm:nested-easy-hard-easy` | Complete | `NestedEasyHardEasy.nested_easy_hard_easy` constructs the literal multiset nesting `A_G ≤ A'_G ≤ A''_G` over `ℚ_[5]` for any self-loop-free (multi)graph and proves all three stages: `stage1_globalMin_iff` (unique optimum `0`, loss `0`); `loss_A'` and `card_A'` (the loss of `A'_G` is exactly the fixed-prime Max-Cut objective, with `5|E|+2|V|` rows); and `stage3_globalMin_iff`, `stage3_optimum`, `loss_A''_optimum` (for every `L ≥ 1` the global minimisers of `A''_G` are exactly the grid `T^n`, with `(c,…,c)` optimal at the closed-form value `m_H 5^L + 4nN5^L`). `NestedEasyHardEasyHardness.loss_A'_eq_maxCutLoss` identifies the Stage 2 loss with `FixedPrimeMaxCut.maxCutLoss`, so `stage2_globalMin_iff` and `stage2_optimal_value` give the Max-Cut characterisation of the hard stage; `nested_easy_hard_easy_with_hardness` bundles all three stages. The Stage 2 complexity clause is checked: `NestedStage2Reduction.maxCut_iff_stage2` proves that the map to the rows of `A'_{G''}` (for `G''` the graph with a pendant edge to a fresh vertex absorbing the threshold, padded to the input length `L`) preserves Max-Cut membership with bound `3|E| + 2 + L - K`; `stage2_rows_eq_A'_G` shows the produced rows are literally the multiset `A'_G` of that loopless graph; `NestedStage2Machine` computes the map with the two-pass machine (the second pass reads the reversed input and uses a flag so that the threshold's marks do not enter the bound, avoiding subtraction); and `satStage2_NPHard` with `satStage2_dataset_eq_A'_G` gives a polynomial-time reduction from CNF-SAT, through the library's chain and Max-Cut gadget reductions, all of whose datasets are `A'_G` of loopless graphs. |
| `thm:discrete-regularised` | Complete | `DiscreteRegularization.discrete_regularized_regression`. |
| `cor:discrete-algorithm` | Complete | `DiscreteRegularization.discrete_algorithm`. |
| `thm:additive-contact` | Complete | `AdditiveContact.additive_contact_theorem`. |
| `cor:additive-contact-special-cases` | Complete | `AdditiveContact.additive_contact_special_cases` and the count/\(q\)-loss component theorems. |
| `thm:q-lexicographic` | Complete | `AdditiveContact.q_lexicographic_theorem`. |
| `thm:max-contact-existence` | Complete | `MaxContact.max_contact_existence`. |
| `thm:3sat-clausewise` | Complete | `ClauseCompiler.three_sat_clausewise` and `satisfiable_iff_minimum_value` for the distinct-variable three-literal convention, and `CNFNormalisation.normalise_satisfiable_iff`, `general_satisfiable_iff_minimum_value`, `general_three_sat_clausewise` for arbitrary 3-CNF syntax (repeated literals, tautological and empty clauses), via a computable normalisation with three fresh variables and at most eight clauses per source clause (`normalise_cellSize_le`). |
| `thm:compiler-template` | Complete | `FiniteDomainCompiler.finite_domain_signed_affine_compiler`; the coefficient-norm formulation is slightly stronger. |
| `cor:qp-extension` | Complete | Included in `finite_domain_signed_affine_compiler` and the global-minimiser lemmas over all of \(\mathbb Q_p^n\). |
| `thm:all-different` | Complete | `AllDifferent.all_different_correctness`. |
| `cor:all-different-csp` | Complete | `AllDifferentCSPEncoding.all_different_csp` in `AllDifferentCSPCorollary.lean` joins the concrete Boolean-input/Boolean-output `runtimeCompilerComputableInPolyTime` witness, the complete `64(s+1)^4` output-bit bound, selected-prime validity, and exact semantics of the emitted `RuntimeObjective.loss`: a global minimum exists, its minimizers are exactly embedded minimum-conflict assignments, and for satisfiable systems exactly embedded satisfying assignments. Input domains are nonempty and scope indices are in range; repeated entries/scopes use set semantics and conflicts count deduplicated primal edges. `RuntimeCompilerInput.finEncoding` checks its unary occurrence header and has length at most `2s+1` in compact input length. All finite scans, counters, transfers, header construction and framing are included. |
| `cor:signed-nphard` | Complete | `FixedPrimeHardness.fixed_prime_signed_decision_is_three_sat_hard_in_cell_model` proves the explicit \(p=5\) reduction, correctness, output size, and a quadratic unit-cell construction bound; `CNFNormalisation.general_compileFixedPrime_correct` and `fixed_prime_signed_decision_is_general_three_sat_hard_in_cell_model` extend it to arbitrary 3-CNF syntax with a `392 · size²` cell bound. The library-native transfer is checked: `PadicRegressionLanguage.SignedRegressionLang` states the signed threshold problem (signed rows, natural bound, unary and binary encodings); `SignedThreeSatReduction.signed_iff` proves, for every prime `p > 3` and every formula of exact width three, that the streaming variant (one negative clause-reward row per clause, one forcing pair per literal occurrence, bound `2m`) preserves satisfiability; `SignedThreeSatMachine.sgR_exits`/`cost_le` give an exact two-pass TM2 run within `10⁶(n+1)²` steps; and `satReduction` composes it with the library's chain reduction, so `encodedUnarySignedRegression_NPHard`, `encodedSignedRegression_NPHard` and `signed_nphard_five` follow from the library's Cook–Levin theorem. |
| `cor:sudoku-polynomial-dyadic-hardness` | Complete | `PolynomialResidualHardness.dyadic_no_tractability_transfer` and `dyadic_compilePolynomial_correct` prove the positive polynomial-residual reduction at `p = 2` (and `polynomial_residual_hardness`, `compilePolynomial_correct` at every prime): the unit-weight objective with `α = 1 + Δ` has global minimisers on `ℤ_2^n`, all of them Boolean (`globalMinOnBall_boolean`), its minimum is `α n` iff the 3-CNF formula is satisfiable, any exact optimiser decides satisfiability, every clause residual is an `MvPolynomial` of total degree `≤ 3` and degree `≤ 1` in each variable, and the instance has `2n + m` rows. The complexity statement is checked: `PolynomialResidualLanguage.PolyRegressionLangML` states the problem over `ℤ_p` with residuals given as products of affine factors and restricted to `MultilinearDeg3` residuals (at most three factors on pairwise disjoint coordinates); `PolynomialResidualReduction.poly_iff` proves for every prime and every formula of exact width three that a per-occurrence variant (an occurrence coordinate carrying each literal's failure value, an affine linking residual, the clause product `y_k y_{k+1} y_{k+2}` on distinct coordinates, forcing pairs per occurrence, bound `9m`) preserves satisfiability, with `multilinear_polyReduce` checking the restriction; `PolynomialResidualMachine` computes it with the two-pass machine of `TwoPassMachine`; and `encodedUnaryPolyML_NPHard`, `encodedPolyML_NPHard` and `dyadic_poly_nphard` follow from the library's chain reduction and Cook–Levin theorem. |
| `cor:sudoku-special-case` | Complete | `SudokuSpecialCase.sudoku_special_case`: on the 81-cell deduplicated peer graph (`PeerEdge`, 810 edges, `degree_eq_twenty` by kernel `decide`), with clue singletons and `{1,…,9}` domains for `p > 9` and `α > 20`, the minimal objective (`sudokuLoss_eq` unfolds it to the displayed form) has a global minimiser, its global minimisers are exactly the clue-respecting digit assignments minimising the peer-conflict count, and when the puzzle is satisfiable they are exactly the valid completions (`validCompletion_iff_isProper`). `digit_difference_norm` is `cor:sudoku-differences`; `unit_complete` records that every row, column and box of a valid completion contains every digit once. |

For the completed `cor:all-different-csp` runtime path,
`AllDifferentCSPSourceSections.lean` splits the complete runtime
source into the existing checked pair of domain and scope encodings.
`SourceSectionMachine.computer` uses six stacks with separate binary row and
entry countdowns. It removes the outer count and singleton header length,
retains the domain count, copies exactly the declared domain rows, and tags
the remaining scope payload separately. The exact execution proof clears all
non-output stacks and handles empty sections, empty rows, repeated entries,
and arbitrary natural values through their encoded bit lengths.
`sourceSections_outputsInTime` and `sourceSectionsComputableInPolyTime` give
an explicit `40 * (s+1)^2` bound for the full raw input length `s`;
`RuntimeSourceSections.output_length_le_input` proves the complete paired
output is no longer than the input.
`runtimeCompilerSectionsComputableInPolyTime` starts from the actual checked
Boolean compiler input and constructs both sections internally.

The dependency is now pinned to `lean-np-hardness` commit
`21e6eb462b14c0b612895b4ff03add15eea54e70`. Its checked generic pair-left
machine supplies `pairedDomainSectionComputableInPolyTime`, which expands
domains while preserving every scope. The composed
`runtimeCompilerDomainAndScopesComputableInPolyTime` maps the actual compiler
input to exactly `(indexedDomainOccurrences C.domains, C.scopes)` under the
existing tagged pair encoding.
The generic codec, arithmetic, framing, counted-row, Boolean-fold and
unary-prime machine implementations have moved to `lean-np-hardness`;
compatibility exports retain the old thesis-facing names.
`AllDifferentCSPProcessedSections.lean` now also composes scope processing
within that pair: `LeanNPHardness.PairExchange.outputsInTime` checks each canonical
section exchange in at most `4s+6` steps for full paired wire length `s`;
`pairedScopeSectionComputableInPolyTime` specializes the dependency
`MachineAdapters.pairRightComputableInPolyTime` while preserving domain output.
`runtimeCompilerProcessedSectionsComputableInPolyTime` constructs both exact
tagged sections from the actual Boolean compiler input, with a checked
polynomial bound. `AllDifferentCSPVariableHeader.lean` now preserves the
variable count before expansion: `variableHeader_outputsInTime` and
`variableHeaderComputableInPolyTime` copy the third checked source field in
at most `3s+6` steps while retaining the complete source. The paired output is
at most `2s` cells, and `runtimeCompilerVariableHeaderComputableInPolyTime`
constructs it from the actual Boolean compiler input. This includes zero
variables and trailing empty domains. `AllDifferentCSPCountedSections.lean`
now carries that count through the source split and both section passes using
the checked generic pair-left API.
`runtimeCompilerCountedSectionsComputableInPolyTime` constructs the exact
occurrence/scope/count tuple from the actual Boolean compiler input with a
checked polynomial bound. `CountedSections.toStructuralView_ofRuntimeSystem`
proves that tuple reconstructs exactly the intended structural view;
`recordCount_le_encode_length` bounds its record count by the actual tuple
encoding length, and `raw_encode_eq_sections` gives the exact assembly and
reversal contract. `AllDifferentCSPStructuralAssembly.lean` now checks the
complete variable-header/record payload through exhaustion, reusing the
upstream counted-row decoder and existing structural tag parser.
`payloadDecode_encode` proves exact recovery; the complete merged wire has
exactly three more cells than the counted-section tuple.
`payloadEncode_length_le_encodedSize` bounds this payload by the existing framed
encoding; `payloadEncode_ofRuntimeSystem_length_le_compilerInput_quadratic`
therefore retains the `32 * (s+1)^2` bound in actual Boolean compiler input
length `s`. `rowCount_le_payloadEncode_length` bounds the required outer row
count, including its singleton header, by the payload's actual length.
`AllDifferentCSPAssemblyMachine.lean` realizes that merge in at most `2s+3`
steps using four finite stacks, clearing every non-output stack at halt.
`runtimeCompilerStructuralPayloadComputableInPolyTime` composes from the
actual Boolean compiler input to exactly `RuntimeStructuralView.ofRuntimeSystem`
under `RuntimeStructuralView.payloadFinEncoding`, with a polynomial bound.
The local `2s+3` bound is only for the final assembly pass. Empty scopes,
repetitions, zero variables, and trailing empty domains are retained.
`raw_encode_eq_count_payload` identifies the original-format bridge:
prepend the outer row count, then reverse and frame the complete stream.
`AllDifferentCSPRowCount.lean` now computes the count in unary while retaining
every payload cell. `structuralRowCount_outputsInTime` and
`structuralRowCountComputableInPolyTime` traverse the binary row lengths with
explicit predecessor loops, emitting one tally mark for each complete row.
Their exact output is `(view, view.records.length + 1)` in the standard tagged
pair encoding, in at most `20 * (s+1)^2` steps for actual payload length `s`.
The singleton variable header, empty scopes, and repetitions are counted;
all non-output stacks are empty at halt.
`runtimeCompilerStructuralCountedPayloadComputableInPolyTime` now composes this
pass from the actual Boolean compiler input, producing exactly the view and
`C.domainEntryCount + C.scopes.length + 1` with a checked polynomial bound.
`StructuralCountedPayload.encode_retain_length` gives the exact paired length;
`encode_retain_length_le` bounds it by twice the payload length, and
`encode_retain_ofRuntimeSystem_length_le_compilerInput_quadratic` bounds the
complete output by `64 * (s+1)^2` in actual Boolean input length `s`.
`AllDifferentCSPBinaryHeader.lean` now supplies the checked redundant-count
codec `StructuralCountedPayload.checkedFinEncoding` and the concrete
`StructuralBinaryHeaderMachine.computer`. `structuralBinaryHeader_outputsInTime`
and `structuralBinaryHeaderComputableInPolyTime` increment a binary counter
once per tally mark, insert the outer count, and reverse into exactly
`RuntimeStructuralView.rawFinEncoding`, preserving every payload cell.
The bound is `8 * (s+1)^2` finite-machine steps in the complete counted-payload
wire length `s`, with all non-output stacks empty at halt. The internal proof
includes zero tallies and arbitrary carry growth. The existing counter is
repackaged as `structuralRowCountCheckedComputableInPolyTime` under the checked
redundant codec. `AllDifferentCSPStructuralCompiler.lean` now composes the
complete structural path. `structuralRawComputableInPolyTime` connects row
counting to binary-header staging;
`runtimeCompilerStructuralRawComputableInPolyTime` constructs that exact raw
view from the actual Boolean compiler input.
`runtimeCompilerStructuralViewComputableInPolyTime` adds the existing framing
machine and emits exactly `RuntimeStructuralView.ofRuntimeSystem` under the
original Boolean `FinEncoding`, with every header and intermediate stream
computed internally. Its polynomial bound covers all passes and intermediate
transfers. The existing `32 * (s+1)^2` output-size bound is now the bound for
this actual Boolean output, measured against the complete Boolean compiler
input length `s`. The local header bound is not the full composition bound.
The later canonical relabelling, finite-machine edge construction,
positive-row emission and complete objective/prime assembly are checked below,
together with the ordered edge specification and
negative-row emitter.
`AllDifferentCSPSymbols.lean` specifies executable occurrence extraction and
canonical rank computation on lists. `DomainSymbols.extract_toFinset` proves
that the extracted symbols have exactly `ExplicitSystem.domainValues` as
their set, including repeated values within and between domains.
`rank_extract_eq_relabelValue` identifies the list rank (deduplicate the
smaller values, count them, and add one) with the semantic compiler's rank.
`rank_eq_iff`, `rank_lt_domainEntryPrime`, and `relabeled_domain` connect it
to equality preservation, the selected prime, and each exact relabeled domain.
These semantic contracts connect to the complete local rank machine described
below, including its composition across all retained compiler sections.
`AllDifferentCSPSymbolMachine.lean` now implements the extraction step.
`domainSymbolExtractionComputableInPolyTime` retains the exact occurrence
wire and extracts every symbol field in source order in at most `3s+3`
finite-machine steps for occurrence-wire length `s`. Its four field phases
use only finite control; zeros, repetitions, and empty occurrence lists are
covered, and every non-output stack is empty at halt.
`runtimeCompilerSymbolSectionsComputableInPolyTime` uses the pinned generic
pair-left and sequential composition APIs to start from the actual Boolean
compiler input and construct the symbol list while preserving all indexed
occurrences, scopes, and the original variable count. Its overall polynomial
bound includes preprocessing and transfer costs; `3s+3` is only the local
extraction bound. `CountedSymbolSections.toStructuralView_ofRuntimeSystem`
proves exact reconstruction, `rank_symbols_eq_relabelValue` connects the
machine-produced list to the semantic rank, and `retain_encode_length_le`
bounds the complete augmented tuple by twice the counted-section wire length.
`AllDifferentCSPSymbolMembership.lean` now supplies the serialized membership
pass. `domainSymbolMembershipComputableInPolyTime` takes a checked pair of a
canonical binary query and source-order symbol fields and returns exactly
whether the query occurs, in at most `6 * (s+1)^2` steps for complete tagged
input length `s`. It loads every candidate internally, reuses the upstream
query-preserving equality kernel, and counts loading, comparison, restoration,
and final cleanup. Empty lists, zero, repeated symbols, and unequal bit
lengths are covered; every non-output stack is empty at halt. Both loaded
words are reversed, which preserves equality and avoids a separate reversal
pass. This local membership machine is reused inside the complete rank driver
below and composes from the complete compiler input.
`AllDifferentCSPSymbolRankStep.lean` connects that machine result to the next
loop. `DomainSymbolMembership.contains_extracted` identifies membership with
the semantic union of domains; `dedup_cons` uses the returned bit to skip
repeated symbols, and `rank_cons` counts a smaller symbol only at its final
source-order occurrence. `input_cons_length` proves that taking the head as
the query removes exactly one field delimiter from the original stream.
`tailMembership_outputsInTime` therefore bounds this local query by six times
the square of that stream's length. `dedup_fields_length_le` proves that
removing duplicates cannot increase the raw binary field length. These are
checked recurrence and size contracts used by the complete rank loop below.
`AllDifferentCSPSymbolComparison.lean` now constructs the aligned binary
input needed by the rank loop's comparison. Its seven-stack loader reads the
checked tagged symbol/target pair, restores each word's original bit order,
aligns corresponding bit positions with explicit padding on the exhausted
side, and restores the complete output order. `domainSymbolAlignment_outputsInTime`
and `domainSymbolAlignmentComputableInPolyTime` give a `4s+5` bound in the
complete serialized pair length; `domainSymbolAlignment_output_length_le`
proves that alignment does not enlarge that wire. Empty words (zero), unequal
bit lengths, and cleanup of every work stack are included. This constructs
comparison input from the complete serialized pair.
`alignedSymbolLessComputableInPolyTime` reuses the upstream less-or-equal
kernel with explicit alphabet recodings that swap the aligned components and
complement the result. `domainSymbolLessComputableInPolyTime` composes that
kernel with the loader and proves an explicit `9s+10` bound, including the
complete intermediate transfer. Its encoded Boolean is exactly `symbol < target`.
`DomainSymbolComparison.rank_cons` connects that computed bit and the checked
membership bit to the existing rank recurrence. `input_head_length` charges
both comparison words and the remaining fields to the complete target/symbol
query; `input_length_le_rank_query` gives the corresponding comparison-size
bound. `AllDifferentCSPRankQueries.lean` now constructs all three queries from
the original target/nonempty-symbol-list wire: `(symbol, tail)` for membership,
`(symbol, target)` for comparison, and `(target, tail)` for the next iteration.
Its decoder checks nonemptiness without adding a header or assuming a pre-split
input. `rankQueries_outputsInTime` and `rankQueriesComputableInPolyTime` prove
a `3s+5` bound for the eight-stack preparation pass in complete input length
`s`, including every copy, ordering pass, and cleanup. Zero symbols, empty
tails, repeated values, and arbitrary binary magnitudes are included.
`RankQueries.output_length` proves the exact output equation `output + 2 = 2s`.
`AllDifferentCSPRankPredicates.lean` now calls both predicates while preserving
that next query. `rankPredicatesComputableInPolyTime` composes preparation,
query membership, and strict comparison with the checked upstream pair-left
and pair-right adapters. Its result is exactly
`(symbol ∈ tail, (symbol < target, (target, tail)))`, with Boolean predicates
and all copying, transfers, and reassembly included in the polynomial bound.
`RankPredicates.rank_step` connects those exact outputs to canonical rank:
add one only when the symbol is smaller than the target and absent from the
tail. `remaining_length` proves that the retained input loses precisely the
head's bit length plus its delimiter; `remaining_length_lt` includes zero
heads. The complete predicate output is at most `s+1` cells.
`AllDifferentCSPRankAccumulator.lean` adds the concrete three-stack conditional
accumulator machine. It consumes the two predicate bits, retains the exact
remaining query, and adds one unary tally mark exactly when the symbol is
smaller and absent from its tail. `rankAccumulator_outputsInTime` and
`rankAccumulatorComputableInPolyTime` bound this complete update by `2s`
finite-machine steps in the full predicate/query/accumulator wire length.
Every copy and order-restoration pass is charged, all work stacks are empty
at halt, and zero accumulators and empty remaining symbol lists are included.
`rankIterationComputableInPolyTime` now composes query preparation, both
predicates, and this accumulator update from the original nonempty query and
its unary tally. It reuses the pinned generic pair-left and sequential-machine
APIs, charging all intermediate copies and transfers to the complete input.
`RankIteration.rank_invariant` preserves the tally plus the remaining canonical
rank. `output_length_balance` charges the consumed head's binary length and
its delimiter against the optional tally cell; `output_length_le` proves the
complete retained state never grows. Exactly one symbol disappears even when
the complete wire length stays constant (a counted zero-valued symbol).
`RankIteration.finish` is an executable recursive specification with an
empty-list branch; `finish_one_eq_rank` and `finish_extracted_eq_relabelValue`
prove its exact canonical-rank and thesis-relabelling semantics. Its tally is
bounded by the initial tally plus the number of explicit occurrences, not by
symbol magnitudes. `AllDifferentCSPRankInitialization.lean` now constructs
the initial state from the complete target/symbol query. Its
`rankInitializationComputableInPolyTime` appends the unary tally one while
preserving every query cell in `2s+2` finite-machine steps, with exactly one
additional output cell. The empty query (zero target, empty symbol list) is
included. `RankInitialization.finish_initialize` connects this starting state
to the semantic one-based rank. `AllDifferentCSPRankControl.lean` now checks
whether symbols remain while retaining the complete query and tally.
`rankControlComputableInPolyTime` emits that bit and the unchanged state in
`2s+2` steps, with exactly one added output cell. `source_present` proves that
a zero symbol's delimiter still selects the nonempty branch, and
`RankControl.nonempty_encode` identifies that branch's retained wire exactly
with the existing iteration input. `rankEntryComputableInPolyTime` composes
initialization and testing from the original query, including transfers.
`AllDifferentCSPRankFinalization.lean` supplies
`rankFinalizationComputableInPolyTime`, returning the unary tally and clearing
the query in `s+1` steps without increasing output length.
`result_eq_finish_of_empty` identifies that tally with the recursive result
only when the checked nonempty-list bit is false.
`AllDifferentCSPRankLoopMachine.lean` now supplies the finite loop controller.
`RankLoopMachine.iteration_cycle` scans a nonempty state, loads and runs the
existing checked iteration, restores its output in order, and returns to the
next scan with all body and scratch stacks empty. Its complete cycle cost is
`P(s) + 2s + 2t + 4`, where `P` is the checked iteration polynomial and `s`,
`t` are the complete input and output wire lengths. `exit_run` checks the
empty branch in `2s+2` steps, including target disposal and tally output.
The driver fuses the existing source-field test with its loading scan and
uses the same checked zero-field criterion. `AllDifferentCSPRankLoop.lean` proves the complete repeated execution.
`RankLoop.run_bounded` uses strict source-list decrease and nonexpanding full
state to bound every cycle by the same input size; `RankLoop.outputsInTime`
proves a total bound of `(s+1) * (P(s) + 4s + 4)` for the complete state length
`s`, including all control, loading, return transfers, and the final exit.
`rankLoopComputableInPolyTime` packages this finite machine under the checked
state and unary-result encodings. `canonicalRankComputableInPolyTime` composes
it with initialization from the original serialized target/symbol query and
returns the exact one-based rank. Its full polynomial also charges that
initialization and intermediate transfer. `canonicalRank_extracted_outputsInTime`
identifies the machine output with `ExplicitSystem.relabelValue` on extracted
domain symbols. Empty lists, zero values, repetitions, arbitrary binary
magnitudes, and cleanup of all work stacks are covered. This completes the
local rank machine. The following step stages its query from the retained
compiler sections and computes the rank of their next occurrence.

`AllDifferentCSPOccurrenceQuery.lean` now constructs the next rank query from
the existing occurrence/symbol wire, whose decoder checks that an occurrence
is present. `occurrenceQueryComputableInPolyTime` removes that head record,
pairs its value with the complete symbol list, and retains its variable index,
the exact remaining occurrence stream, and a second copy of the complete
symbol list in at most `3s+6` finite-machine steps. The bound uses the full
input wire length and includes copying, order restoration, and cleanup.
`OccurrenceQuery.output_length` proves `output + 6 = input + symbols`;
`output_length_le` consequently bounds the complete result by twice its input.
Zero indices/values, empty tails, repeated symbols, and arbitrary binary
magnitudes are covered.
`AllDifferentCSPOccurrenceRank.lean` composes that preparation with the complete
rank machine. `occurrenceRankComputableInPolyTime` returns the exact unary rank
while preserving the index, remaining records, and full symbol list.
`countedOccurrenceRankComputableInPolyTime` carries the complete scopes and
original variable count through the same step using the pinned pair-left API.
`CountedOccurrenceRank.input_encode_eq_source` proves its input is exactly the
existing nonempty counted-symbol-section wire; no preassembled query is assumed.
`step_eq_relabelValue` identifies the emitted index/rank pair with the thesis
compiler's canonical relabelling when the source is compiler-produced.
`remaining_step` and `remaining_length` preserve all remaining data and remove
exactly one occurrence. `remaining_encoded_length_balance` proves that the next
source loses the head's index/value bits plus six record-format cells, so its
encoded length strictly decreases even for zeros. The complete output,
including the unary rank, is at most twice the input length.
All adapter and transfer costs are included in the composed polynomial.
`AllDifferentCSPOccurrenceEmit.lean` now converts that unary rank and emits the
exact canonical binary `[3,0,index,rank]` record while preserving the remaining
occurrences and complete symbol list. `occurrenceEmitComputableInPolyTime`
proves `12(s+1)^2` steps in the complete ranked-input wire length, including
carry propagation, order restoration, source copying, and stack cleanup.
`OccurrenceEmit.output_length` accounts for exactly six record-format cells;
`output_length_le` bounds the result by the input length plus six. Zero ranks
and indices, empty retained sources, and binary carry growth are included.
`AllDifferentCSPOccurrenceStep.lean` composes query staging, canonical ranking,
and binary emission as `occurrenceStepComputableInPolyTime`.
`countedOccurrenceStepComputableInPolyTime` carries scopes and the original
variable count through that complete step on the existing nonempty counted
section wire. The composed polynomial includes every adapter and transfer;
`12(s+1)^2` is the emitter's bound alone. `output_length_balance` proves that
the only wire-size change is replacing the old value's binary word by the
rank's binary word, and `output_length_le` bounds the complete result by `2s`.
`output_length_eq_record_add_remaining` separates the emitted record from the
remaining source with no extra cells. The remaining source strictly shrinks;
its full symbol list survives, and `record_eq_relabelValue_of_symbols` supplies
the canonical-rank invariant for later suffixes as well as the initial input.
`record_encode_eq` identifies the exact thesis record, and `record_rank_bounds`
proves each actual emitted rank is positive and below `domainEntryPrime`.
`AllDifferentCSPOccurrenceAccumulator.lean` adds the ordered-output update.
`occurrenceAccumulatorComputableInPolyTime` appends the newly emitted binary
record after all prior records while retaining the complete next source, in
`2s+4` steps for the full input wire. The five-stack finite machine charges
each routed cell and each order-restoration pass, clears every work stack,
and handles empty prior output and zero-valued fields. `output_length` proves
that this update adds no cells.
`AllDifferentCSPOccurrenceIteration.lean` composes rank, binary emission, and
ordered append as `occurrenceIterationComputableInPolyTime`, carrying all
prior output through the checked pair adapter and charging its transfers.
`step_length_balance` replaces only the old value bits by rank bits.
`step_budget_le` reserves space for every remaining rank and proves that this
full-state budget never increases. `iterate_length_le_quadratic` bounds every
executable traversal state, including accumulated records, by `2(s+1)^2` in
the original complete wire length; `finish_encoded_length_le_quadratic` gives
the same bound for all final emitted records from an empty accumulator.
`finish_eq_append_map` and `iterate_eq_finish` prove exact ordered traversal
and exhaustion after one step per source occurrence. The compiler-specific
`finish_extracted_eq_relabelValue` and `finish_rank_bounds` identify every
final index/rank with the thesis relabelling and place each rank strictly
between zero and `domainEntryPrime`. Duplicate and zero-valued occurrences
survive; empty input preserves any prior output.
`AllDifferentCSPOccurrenceLoopMachine.lean` now supplies the finite dispatcher.
`source_present` detects remaining occurrence cells, including zero fields;
`body_run` embeds the complete checked body and redirects its halt to the
return transfer. `iteration_cycle` charges `P(s)+2s+2t+4` steps for a cycle
with input/output lengths `s,t` and body polynomial `P`. `exit_run` scans the
exhausted state and returns the accumulated records in `2s+2` steps, discarding
the retained symbols and clearing every work stack.
`AllDifferentCSPOccurrenceLoop.lean` completes the repeated runtime proof.
`OccurrenceLoop.run_bounded` carries the decreasing budget through induction
on remaining occurrences, and `occurrenceLoopComputableInPolyTime` returns
exactly the prior output followed by the ordered canonical-rank records.
With initial bit length `s`, `B=2(s+1)^2` bounds every intermediate state and
the complete machine takes at most `(s+1)*(P(B)+4B+4)` steps. This includes
all body calls, dispatch scans, transfers and the final empty exit.
`AllDifferentCSPOccurrenceInitialization.lean` constructs the empty-accumulator
state in `2s+2` steps, preserving the input wire length. The composed
`occurrenceRelabellingComputableInPolyTime` starts at the existing
occurrence/symbol encoding without requiring any preconstructed loop state.
`AllDifferentCSPRelabelling.lean` then retains scopes and the original variable
count through the checked pair adapter. Its headline
`runtimeCompilerRelabelledSectionsComputableInPolyTime` starts at the actual
Boolean `RuntimeCompilerInput.finEncoding` and returns the exact existing
`CountedSections.finEncoding` with all domain values replaced by thesis ranks.
`CountedRelabelledSections.domains_ofRuntimeSystem` proves that correspondence;
scopes, occurrence order, repetitions, and variable count are preserved, and
`rank_bounds` puts every output rank strictly between zero and the selected
domain-entry prime. The complete composed runtime includes source preparation,
symbol extraction, initialization, the whole loop and both retained-section
adapters; the displayed loop polynomial alone is not the whole compiler cost.
The pair-loop composition below now constructs deduplicated primal edges.
The positive-row scan, row assembly and objective serialization are checked
below, together with computed variable/prime header attachment and the final
`all_different_csp` theorem. The full corollary is **Complete**.

`AllDifferentCSPPrimalEdges.lean` now defines an executable bounded pair scan
from the retained variable count and scope lists. `PrimalEdgeEnumeration.enumerate`
emits increasing endpoints in strict lexicographic order, so scope repetitions,
shared edges and repeated entries cannot duplicate an edge. The theorem
`enumerate_eq_sorted_primalEdges` identifies the exact ordered list with the
semantic compiler's sorted primal graph, including its treatment of out-of-range
scope entries. `enumerate_relabelledSections` connects the scan input to the
completed relabelling stage. `enumerate_length_le` bounds the list by `n^2`
for `n` explicitly listed variables. These executable semantics and size
results are realized by the complete finite pair loop below, with a checked
polynomial runtime from actual compiler input. The complete positive-row scan
and row assembly are documented below.

`AllDifferentCSPNegativeRows.lean` adds checked endpoint-pair and negative-row
section encodings by reusing the counted-row codecs. Its
`negativeRowsComputableInPolyTime` reuses the complete scope-tagging machine:
`[2,i,j]` becomes the exact raw negative residual row `[3,1,i,j]` in at most
`20(s+1)^2` steps for the supplied edge-stream wire length `s`. Decoders check
pair arity, tags and row exhaustion. `NegativeRows.rows_enumerate_eq` and
`outputEncode_enumerate_eq` give exact agreement with the semantic compiler's
ordered negative rows; `pinningWeight_eq_edgeCount` also connects edge counting
to its positive pinning weight. `outputEncode_length` charges exactly two added
cells per edge. `compiler_output_length_le_cubic` bounds the whole negative
section by `9(s+1)^3` in the actual Boolean compiler-input length. The finite
emitter starts with an already enumerated edge list. The pair loop and
projection below now construct that list and compose this emitter from actual
compiler input. Positive rows, full objective assembly and prime composition
are checked in the final stages below.
`AllDifferentCSPRowCount.lean` now reuses the existing row-counting machine
on the original domain rows. `domainVariableCountComputableInPolyTime`
retains every domain cell and constructs the exact unary variable count in
`20(s+1)^2` steps for payload length `s`, including empty domains.
`completeDomainVariableCountComputableInPolyTime` includes removal of the
checked outer count. `DomainCountedPayload.encode_retain_length_le` bounds
the complete retained payload and tally by `2s`.
`AllDifferentCSPBoundedSections.lean` carries that computed tally and every raw
scope through the complete domain-relabelling path using existing pair
adapters. Its headline
`runtimeCompilerBoundedRelabelledSectionsComputableInPolyTime` starts at the
actual Boolean compiler input and produces exact thesis-ranked occurrences,
the unary variable count, and unchanged scopes. `toCountedSections_ofRuntimeSystem`
identifies the result with the established relabelling semantics.
`variableCount_le_encode_length` holds for every value of this checked
intermediate encoding, so `candidates_length_le_square` bounds the complete
pair grid by its actual input length squared. `negativeRows_length_le_cubic`
also bounds the negative-row target in this intermediate length. These size
lemmas prepare the missing finite pair scanner; they do not assert its runtime.
Empty domains, an empty occurrence stream, and zero variables are covered.

`AllDifferentCSPScopeQueries.lean` now constructs both endpoint-membership
queries for one scope from a checked serialized endpoint-pair/scope input.
`scopeQueriesComputableInPolyTime` proves the finite routing machine takes at
most `3s+3` steps in the complete input length, including copying every scope
cell twice, restoring both query orders and clearing all scratch stacks.
`ScopeQueries.output_length` charges exactly one additional copy of the scope;
`output_length_le` bounds the entire paired output by `2s`.
`AllDifferentCSPScopeCooccurrence.lean` composes this preparation with both
existing serialized membership calls, the checked pair adapters, and a fixed
finite conjunction of their two result cells.
`scopeCooccurrenceComputableInPolyTime` supplies a genuine finite-machine
polynomial bound for the complete one-scope predicate; copying, transfers and
cleanup are included. `scopeCooccurrence_correct` identifies its answer with
the singleton-scope predicate in the exact primal-edge enumeration.
`ScopeCooccurrence.adjacent_cons` specifies the outer OR of these same-scope
answers, and `query_length_le` bounds each bounded-pair/scope query by twice the
full retained intermediate wire length. `scopeCooccurrence_steps_le` then
bounds the actual composed predicate steps by its polynomial evaluated at `2s`.
The pair scan still supplies the separate `i < j` condition. Checked examples
distinguish endpoints in different scopes from a pair occurring in one scope, including
zero, repeated entries and empty scopes.

`ScopeHead.inputFinEncoding` now checks a nonempty contiguous scope section,
without requiring an externally supplied split. `scopeHeadComputableInPolyTime`
reuses the existing source parser at its first-row entry point to separate the
first counted scope from the exact remaining section in at most `20(s+1)^2`
steps. Every work stack is clear at halt. `ScopeHead.output_length` proves
that the split changes only alphabet tags, and `tail_length_lt` proves strict
progress even when the removed scope is empty. Removing the isolated scope's
count and retaining both endpoints now compose as described below.

`AllDifferentCSPScopePayload.lean` reuses the pinned counted-row header-removal
machine with a new proof for one scope's arbitrary entry fields.
`scopePayloadComputableInPolyTime` removes only that scope's count in at most
`2s+1` steps, including empty scopes and complete cleanup.
`AllDifferentCSPScopeExtraction.lean` composes the split and header removal,
then uses the pinned pair adapters to retain both binary endpoints and every
later scope. `scopeExtractionComputableInPolyTime` starts with one contiguous
nonempty counted section and includes parsing, copying, transfers and cleanup
in its standard finite-machine polynomial bound. `output_length_balance`
charges precisely the removed count bits and delimiter; `remaining_length_lt`
proves strict progress, and `query_length_le` bounds the next membership query
by the actual incoming state length. `adjacent_step` connects the extracted
head and unchanged tail to the exact primal-edge recurrence.

`AllDifferentCSPScopeRouting.lean` now constructs both the predicate query and
its continuation, duplicating the binary endpoints while preserving the exact
head and tail order. `scopeRoutingComputableInPolyTime` proves `3s+3` steps
including restoration and scratch cleanup. `ScopeRouting.output_length`
charges exactly one extra copy of the two endpoints and bounds output by `2s`.
`AllDifferentCSPScopeTest.lean` composes extraction, routing and the existing
co-occurrence machine through the pinned pair-left adapter.
`scopeTestComputableInPolyTime` starts at the unsplit nonempty counted section
and returns the first scope's answer with both endpoints and the entire tail.
No split, copied index or membership answer is supplied externally.
`ScopeTest.output_length_balance` accounts for replacing the first counted
scope with one Boolean cell, so the complete result never grows, including
empty scopes. `result_eq_true` and `adjacent_step` give the exact same-scope
semantics and primal-edge recurrence.

`AllDifferentCSPScopeAccumulator.lean` combines the old and tested answers by
Boolean OR, copies the full retained state in order, and clears all scratch
stacks in at most `2s+3` steps. It removes exactly one Boolean cell.
`AllDifferentCSPScopeIteration.lean` composes extraction, query construction,
both membership tests and accumulation as `scopeIterationComputableInPolyTime`.
`nonempty_encode` proves that a nonempty loop state already has the exact
iteration wire format. `adjacent_invariant` preserves the accumulated answer
OR the remaining adjacency question. `output_length_balance` charges the
precise counted head removed, and `output_length_lt` proves strict progress
even for empty scopes. The executable recursion `finish` agrees with the exact
primal-edge predicate by `finish_false_eq_adjacent`, including repeated and
empty scopes. `AllDifferentCSPScopeLoopMachine.lean` now supplies the finite
dispatcher: it scans for counted scope cells, loads the complete iteration,
returns its output in order, and clears all work stacks on exit. An empty
scope has a count delimiter and cannot be mistaken for an exhausted list.
`AllDifferentCSPScopeLoop.lean` proves the complete repeated execution.
`scopeLoopComputableInPolyTime` computes the accumulated adjacency answer in
at most `(s+1) * (P(s)+4s+4)` steps, where `P` is the checked iteration's
polynomial and `s` is the original full state encoding length. The bound
includes scans, loading, all body calls, return transfers, and final cleanup.
`scopeLoop_adjacent_outputsInTime` proves exact adjacency from a false initial
accumulator. `AllDifferentCSPScopeInitialization.lean` now constructs that
false accumulator from the bare serialized endpoints and counted scope section
in `2s+2` steps, adding exactly one cell. Its composed
`scopeAdjacencyComputableInPolyTime` decides whether both endpoints occur in
one common scope, including initialization, all scope tests and cleanup.
`scopeAdjacency_query_length_le` bounds the complete query by twice the
retained intermediate length for a pair bounded by its unary variable tally;
`scopeAdjacency_steps_le` supplies a uniform polynomial bound for that call.
`AllDifferentCSPPairQueries.lean` now constructs strict-order and complete
adjacency queries from the serialized candidate-pair state. Its checked
`PairQueries.inputFinEncoding` retains binary endpoints, ranked occurrences,
the unary variable count, full scopes and previously emitted edge rows.
`pairQueriesComputableInPolyTime` copies and restores every required cell in
`4s+4` steps and clears all scratch stacks. `PairQueries.output_length` charges
two extra endpoint copies and one complete scope copy; output is at most `3s`.
`AllDifferentCSPPairTest.lean` composes those queries with the existing binary
comparison, full adjacency traversal and finite conjunction.
`pairTestComputableInPolyTime` returns precisely the increasing-endpoint,
same-scope filter while retaining the complete state, adding one answer cell.
`accept_iff_mem_enumerate` identifies it with the checked edge enumeration for
bounded candidates, and `accept_ofRuntimeSystem` connects it to the thesis
primal graph. `state_length_le_cubic` bounds a candidate state with at most
`n^2` bounded emitted edges by `12(s+1)^3` cells in the original retained-section
length `s`; `pairTest_bounded_steps_le` supplies the corresponding uniform
polynomial bound for a complete call. These are conditional bounds for the
outer loop. `AllDifferentCSPPairInitialization.lean` now constructs the exact
zero-endpoint, empty-edge state in `2s+2` steps, preserving its wire length.
`runtimeCompilerPairInitializationComputableInPolyTime` composes this from the
actual Boolean compiler input, including complete domain relabelling and unary
variable counting. `zero_edges` checks that zero variables yield no candidates,
even if malformed scopes mention indices. `AllDifferentCSPPairAdvance.lean`
now defines the executable conditional emission and row-major counter step.
`afterTest_invariant` preserves bounded counters, a bounded accumulated row
count, sound edge membership and strict output order. `advance_budget` removes
exactly one candidate from the grid budget; `run_position`, `run_exhausted` and
`run_stable` prove that `n^2` steps visit the entire grid and then stop changing.
`run_edges_eq` proves exact list equality with the existing deduplicated edge
enumerator, and `run_ofRuntimeSystem` connects this to compiler-produced input.
`iterate_length_le_cubic` bounds every state, including terminal and zero-variable
states, by `12(s+1)^3`; `iterate_test_steps_le` bounds complete predicate calls
uniformly in the original section length with no external invariant assumptions.
The executable scan's cycle count is at most `s^2`.
`AllDifferentCSPPairEmit.lean` now realizes conditional edge emission as a finite
machine. `pairEmitComputableInPolyTime` consumes the computed answer bit and
appends exactly the counted `[2,i,j]` row when true, preserving endpoints,
ranked domains, the unary bound, scopes and previous edge order. The bound
`4s+5` includes every copy, all five row framing cells and scratch cleanup;
`output_length_le` bounds the complete result by `2s+5`.
`PairEmit.afterTest_eq` identifies this result as the exact retained portion of
the abstract advancement step. `AllDifferentCSPPairFilter.lean` now composes
testing and emission: `pairFilterComputableInPolyTime` computes its own decision
from serialized endpoints and scopes, with all transfers included.
`mem_rows_iff_primalEdges` gives the exact old-or-new edge membership condition
on compiler-produced sections. `output_length_le_cubic` preserves the original
`12(s+1)^3` bound after filtering a reached active state, before counter advance;
`pairFilter_iterate_steps_le` uniformly bounds complete calls along the semantic
scan. `exhausted_eq` confirms that filtering the terminal `(n,0)` state changes
nothing, including zero variables. `AllDifferentCSPPairCounters.lean` now implements both counter actions.
`pairInnerCounterComputableInPolyTime` increments the second binary endpoint;
`pairOuterCounterComputableInPolyTime` resets it to canonical zero and increments
the first. They reuse the pinned successor and pair adapters, preserving every
retained section and edge. The reset pass takes `2s+2` steps including cleanup;
either continuation adds at most one encoded cell. `PairCounters.nextPair_eq`
identifies the two actions with the branches of the abstract row-major step.
`AllDifferentCSPPairStepBranches.lean` composes each counter action with the
complete computed filter and emitter. `pairInnerStepComputableInPolyTime` and
`pairOuterStepComputableInPolyTime` execute those complete branches, including
all transfers. `run_succ_eq` identifies the correct branch with the next
semantic scan state; its invariant, one-candidate budget decrease and cubic
wire bound follow without a new assumed invariant. `final_outer` proves the
last active outer call reaches `(n,0)` with exactly the complete ordered edge
list, for every positive `n`. Both complete branch calls have uniform polynomial
bounds in the original retained-section length.
`AllDifferentCSPPairBound.lean` now computes a binary copy of the retained unary
variable count. Its preparation pass takes `3s+3` steps, preserves the complete
scan state, and feeds the existing structural-header machine with an empty
payload. `unaryBoundComputableInPolyTime` reuses that machine's checked carry
loop in `8(n+1)^2` steps for unary length `n`; no new arithmetic machine is
assumed. `pairBoundComputableInPolyTime` composes preparation and counting,
including transfers and cleanup; its complete output has at most `2s+1` cells.
`AllDifferentCSPPairControl.lean` now implements both control predicates:
`pairActiveComputableInPolyTime` computes `i<n`, and
`pairContinuesComputableInPolyTime` computes `j+1<n`, from the complete original
state. The bound conversion, endpoint copy, successor, binary comparison,
transfers and cleanup are internal. The finite query router costs `5s+5` for
its bound-bearing input; each completed test adds exactly one answer cell and
preserves the original state. `PairControl.advance_eq` identifies the two
computed answers with the exact scan recurrence; `run_active_iff` proves
exhaustion occurs after precisely `n^2` cycles, including zero variables.
Both complete tests have uniform polynomial bounds in the original retained
section length.
`AllDifferentCSPPairGate.lean` now provides checked conditional calls on the
Boolean/pair-state wire. `PairGateMachine.skip_run` returns every cell unchanged
in `2s+2` steps without entering the body; `call_run` invokes a supplied checked
state transformer with its original step count plus `2s+2t+4` routing steps for
input/output lengths `s,t`. `computableInPolyTime` uses the pinned generic
output-size bound to include all routing and scratch cleanup in a polynomial.
`AllDifferentCSPPairDispatch.lean` composes the actual continuation test with
complementary gates that preserve the original answer, so exactly one complete
inner/outer branch runs. `PairDispatch.selectedComputableInPolyTime` removes
the temporary answer using a checked `2s+2` erasure pass.
`PairDispatch.computableInPolyTime` additionally computes exhaustion and gates
that whole active step, implementing exactly `PairAdvance.advance` on every
checked state. Exhausted states retain every cell, including arbitrary stored
edges; no external decision or well-formedness assumption is required.
`run_step_outputsInTime` gives the exact next semantic state with all dispatch,
body, transfer and cleanup costs bounded by one fixed polynomial evaluated at
`12(s+1)^3` in original retained-section length `s`. Kernel-reduced examples
cover zero/singleton bounds, carry, wrapping, duplicate scopes and an exhausted
state whose endpoints would otherwise pass the edge test.
`AllDifferentCSPPairLoopMachine.lean` supplies the finite repeated controller.
Its body erases the old answer, invokes the complete dispatcher and computes
new active control. `iteration_cycle` charges the full body plus `2s+2t+4`
steps for input/output lengths `s,t`; `exit_run` removes the false answer and
returns the entire terminal state in `2s+2` steps. Every return restores wire
order and clears all scratch stacks.
`AllDifferentCSPPairLoop.lean` proves the total repeated runtime. The checked
internal entry encoding retains the complete initialized state plus one active
bit, rejecting a different state in its decoder. `PairLoop.run_bounded`
charges all remaining grid cells and the final false-answer exit. At complete
entry length `s`, every flagged working state is bounded by `B=12(s+1)^3+1`,
and the loop takes at most `(s^2+1)*(P(B)+4B+4)` steps, where `P` is the checked
complete-body polynomial. `PairLoop.entryComputableInPolyTime` constructs the
zero counters, empty edge list and computed control bit; it is composed with
the loop in `pairEnumerationComputableInPolyTime`.
`runtimeCompilerPairEnumerationComputableInPolyTime` starts from actual Boolean
compiler input and returns terminal counters `(n,0)`, all retained ranked
sections, and exactly the deduplicated primal-edge list. The full composition
includes preparation and entry costs, beyond the displayed loop polynomial.
Zero variables, empty/overlapping/repeated scopes and arbitrary binary values
are covered.

`AllDifferentCSPPairFinalization.lean` removes only the scan counters in
`2s+2` steps. `runtimeCompilerGraphSectionsComputableInPolyTime` returns the
ranked sections paired with the exact ordered graph.
`runtimeCompilerNegativeSectionsComputableInPolyTime` composes the checked
pair-right negative-row emitter from the actual Boolean compiler input,
preserving every ranked section. `GraphSections.negative_encode` identifies
the complete paired wire with the semantic compiler's ordered `unequalRows`;
`negative_length_le_cubic` bounds that whole paired output by `10(s+1)^3` in
the retained-section input length, including both retained data and rows.
`AllDifferentCSPEdgeCount.lean` reuses the complete row counter on the
constructed graph. `EdgeCount.outputsInTime` retains every endpoint and emits
one unary mark per edge in `20(s+1)^2` steps; the complete result is at most
`2s` cells. `runtimeCompilerCountedGraphSectionsComputableInPolyTime` composes
this pass from actual Boolean compiler input, retaining every ranked section.
`CountedGraphSections.count_eq` identifies its computed tally plus one with
the semantic pinning weight.

`AllDifferentCSPPinningWeight.lean` constructs that weight. Its finite
preparation pass appends one tally mark and routes the count in `2s+2` steps,
retaining every edge cell. `pinningWeightBinaryComputableInPolyTime` reuses the
checked binary-header machine and pair-right adapter to count the marks into
an exact reversed raw binary field, including its delimiter. The complete
`runtimeCompilerWeightedNegativeSectionsComputableInPolyTime` starts from
actual Boolean compiler input and returns all ranked sections, the exact
negative rows and the internally computed binary pinning weight.
`WeightedGraphSections.encode_eq` identifies both row and weight fields with
the semantic compiler, while `encode_length_le_cubic` bounds the entire output
by `11(s+1)^3+2` in the complete retained-section length `s`. Empty graphs have
weight one; repeated scopes do not inflate the count; binary carry is included.

`AllDifferentCSPPositiveEnumeration.lean` now specifies an executable scan of
variable indices and ranks bounded by the stored occurrence count.
`PositiveEnumeration.rows_eq_pinningRows` proves exact equality with the
semantic compiler's ordered positive rows, using the computed edge count plus
one as weight. Repeated entries produce one row, and empty domains preserve
later variable indices. `enumerate_nodup` and `enumerate_length_le` prove that
no pair repeats and output count cannot exceed stored occurrence count.
`enumerate_eq_filter` connects the scan to its explicit candidate grid;
`candidates_length_le_wire_quadratic` bounds that grid by `s(s+1)` in the
complete retained-section wire length. This executable specification and semantic/order proof are implemented by
`positiveEnumerationComputableInPolyTime`, described below.

`AllDifferentCSPPositiveBlock.lean` adds a concrete finite machine and checked
input/output encodings for one positive row. `positiveBlock_outputsInTime`
and `positiveBlockComputableInPolyTime` preserve all binary index, rank and
weight fields, prefix exactly `[4,0]`, and clear scratch stacks in `2s+2`
steps. The complete output adds exactly five cells to the three-field input.
`AllDifferentCSPPositiveRows.lean` checks concatenated positive-row blocks;
its decoder rejects negative rows and wrong arities.
`PositiveRows.outputEncode_ofRuntimeSystem` identifies the exact raw output
from weighted ranked sections with the semantic compiler's ordered pinning
rows. `outputEncode_length_le_wire_quadratic` bounds that whole positive
section by `11(s+1)^2` in the complete weighted-section wire length, including
the binary weight field. This is a wire-size theorem; the complete positive-scan runtime is checked
below, as are row assembly, variable/prime header attachment, final framing
and the whole-compiler correctness theorem.

`AllDifferentCSPOccurrenceCount.lean` reuses the checked row-counting machine
on the exact tagged ranked-occurrence wire in `20(s+1)^2` steps. The composed
`runtimeCompilerCountedPositiveSectionsComputableInPolyTime` starts from the
actual Boolean compiler input, counts every stored occurrence, and retains the
unary variable count, scopes, negative rows and binary weight.
`CountedPositiveSections.count_eq` identifies the computed tally with the
original domain-entry count; repeated entries contribute separate tally marks.
The complete retained output is at most twice its weighted-section input
length, and `gridSize_le_wire_quadratic` bounds both numerical scan dimensions
by the actual encoded length for every intermediate value. This constructs
the positive scan's bound; membership traversal and repeated row emission are
checked below, together with variable/prime header attachment and final composition.

`AllDifferentCSPPositiveWeight.lean` now stages the graph compiler's common
binary weight for one selected `(variable, rank)` pair. The concrete
`positiveWeightPrepare_outputsInTime` machine copies and restores the weight
in `3s+5` steps for complete input length `s`, including all field delimiters
and cleanup. `positiveRowWithWeightComputableInPolyTime` composes this pass
with the checked positive-row emitter while retaining the original weight.
`PositiveWeight.row_encode` identifies the emitted component with the exact
counted pinning row; the full row/weight output has at most `2s+7` cells.
`positiveRowWithWeight_steps_le` gives a uniform complete-call polynomial
bound for every bounded candidate in the retained positive-scan state.
The initialized membership decision and complete positive-row traversal are
checked below, together with variable/prime header attachment and final composition.

`AllDifferentCSPPositiveMembership.lean` checks the exact ordered-pair
membership predicate. `contains_cons` requires both fields to match the same
occurrence, and `enumerate_eq_filter` connects it to positive-row selection.
`positiveMembershipExtractionComputableInPolyTime` reuses the existing counted
row extractor and count-removal machine to expose one `[0,index,rank]` payload
while retaining both candidate fields and the exact remaining occurrence
stream. Its checked decoders reject incorrect tags and arities. Extraction
removes exactly three row-count cells; `remaining_length_balance` charges
both removed binary words plus six header/delimiter cells, proving strict
progress even for zero-valued fields. `input_length_le_sections` bounds the
whole candidate query by the retained positive-section wire length. The
ordered-pair comparison and repeated traversal are now checked below.

`AllDifferentCSPPositiveRouting.lean` reuses the existing finite scope router
to copy the candidate and retain the exact occurrence tail in `3s+3` steps.
`AllDifferentCSPPositiveComparison.lean` parses the checked `[0,index,rank]`
head into two separate singleton queries in another `3s+3` finite steps.
`PositiveQueries.output_length_balance` removes exactly the zero-tag delimiter
while preserving all four binary words and both field separators.
`positivePairMatchComputableInPolyTime` executes the existing binary equality
machinery once per coordinate and conjoins the answers, including all parsing,
transfers and cleanup. `PositivePairQuery.equal_eq_true` proves that its result
is true exactly when the ordered pairs agree. Zero coordinates and arbitrary
binary magnitudes are covered. Counted-record testing, OR accumulation and
repeated traversal now compose as described below.

`AllDifferentCSPPositiveTest.lean` composes extraction, candidate copying and
same-record comparison from the original contiguous counted occurrence wire.
`positiveTestComputableInPolyTime` returns that Boolean plus the unchanged
candidate and exact tail. `AllDifferentCSPPositiveIteration.lean` reuses the
checked finite OR accumulator in `2s+3` steps and composes the complete
`positiveIterationComputableInPolyTime`. Each iteration removes precisely the
head's two binary words and six structural cells, so it strictly shrinks even
when both fields are zero. `PositiveIteration.contains_invariant` proves that
the accumulated answer OR membership in the remaining tail stays unchanged.
`finish_false_eq_contains` verifies the executable recurrence, including empty
and repeated records and cross-record false positives.

`AllDifferentCSPRecordLoopMachine.lean` factors the existing scope dispatcher
into one shared finite controller for the exact CSP record alphabet. Both scope
and positive-occurrence loops reuse its scan, call, return and cleanup proofs.
`PositiveLoopMachine.iteration_cycle` runs the complete ordered-pair test and
returns its exact shortened state. `positiveLoopComputableInPolyTime` now
traverses every occurrence, returning the accumulated answer OR exact pair
membership. If `P(s)` bounds one checked body call, the complete loop costs at
most `(s+1)*(P(s)+4s+4)` in its original encoded state length `s`. This includes
all transfers and final query cleanup, even for empty lists or zero fields.
`AllDifferentCSPPositiveInitialization.lean` now reuses the scope initializer
on the identical serialized alphabet, adding the false answer in at most
`2s+2` steps with exactly one extra encoded cell.
`positiveMembershipComputableInPolyTime` composes this pass and the complete
loop from the original serialized candidate and counted occurrence list.
`PositiveInitialization.result_ofRuntimeSystem` identifies acceptance exactly
with membership in that variable's canonical relabelled domain.
`positiveMembership_steps_le` bounds every candidate call by the same polynomial
in the complete retained positive-section length. Empty lists, zero fields,
repeated records, swapped fields and large binary values are checked.
`AllDifferentCSPPositiveCandidateQueries.lean` now constructs the exact
candidate/occurrence query while retaining the entire positive-scan state:
both unary bounds, scopes, negative rows, common binary weight and accumulated
positive rows. `positiveCandidateQueriesComputableInPolyTime` supplies a
four-stack finite machine with bound `3s+3` in complete state length `s`.
`PositiveCandidateQueries.output_length` charges exactly one query copy and
`output_length_le` bounds the output by `2s`; all scratch stacks are cleared.
The caller supplies one serialized state, not an extracted occurrence query.

`AllDifferentCSPPositiveCandidateTest.lean` composes that constructor with the
complete membership decision through the checked generic pair-left adapter.
`positiveCandidateTestComputableInPolyTime` returns the acceptance bit and the
entire original state; its output adds exactly one cell.
`PositiveCandidateTest.accept_ofRuntimeSystem` proves exact relabelled-domain
acceptance, and `filter_eq_enumerate` recovers the existing positive scan in
its precise candidate order. `state_length_le_cubic` bounds every state with
closed candidate bounds and at most a grid of bounded, common-weight rows by
`16(s+1)^3` in immutable-section wire length `s`, including all weight bits.
`positiveCandidateTest_bounded_steps_le` then gives one polynomial bound for
all such complete calls. The reached-state invariants are established by `PositiveAdvance` below;
the repeated finite controller is checked in `PositiveScanLoop` below.

`AllDifferentCSPPositiveCandidateEmit.lean` now consumes the computed answer
and conditionally appends the exact counted positive row while retaining the
candidate, both unary bounds, ranked occurrences, scopes, negative rows,
common binary weight and all earlier positive rows.
`positiveCandidateEmitComputableInPolyTime` implements this with a finite
seven-stack machine in at most `6s+7` steps for complete tested-state length
`s`. Both coordinate fields and the reversed binary weight are copied into
row order; all scratch stacks are empty at halt. `output_length` charges
exactly the accepted row, including its eight tag/delimiter cells and every
weight bit; `output_length_le` bounds the result by `2s+8`.

`AllDifferentCSPPositiveCandidateFilter.lean` composes the complete test and
conditional emitter through the pinned generic sequential-machine API.
`positiveCandidateFilterComputableInPolyTime` now computes one full candidate
filter from its serialized state, including query copying, membership,
weight copying, emission and all transfers. `rows_ofRuntimeSystem` identifies
its output exactly with relabelled-domain membership. Repeated occurrences
produce only one row per candidate. `rows_bounded`, `rows_capacity` and
`rows_nodup` preserve the shared weight, coordinate bounds, grid capacity and
uniqueness under their explicit input/freshness hypotheses.
`PositiveCandidateFilter.state_length_le_cubic` preserves the `16(s+1)^3`
bit bound after emission when a grid slot remains, and
`positiveCandidateFilter_bounded_steps_le` bounds every complete call by one
polynomial in the immutable-section wire length. `PositiveAdvance` below now
establishes capacity and freshness for reached states.

`AllDifferentCSPPositiveAdvance.lean` now gives the executable rectangular
traversal, including its canonical terminal `(variableCount, 0)`.
`run_position`, `run_pair_at`, `run_exhausted` and `run_stable` prove that each
candidate is visited exactly once and that traversal stops after
`variableCount * (occurrenceCount + 1)` visits. `step_invariant`, `fresh` and
`active_capacity` establish the previously required row bounds, common weight,
freshness and capacity for every reached state. `run_rows_eq` identifies the
terminal ordered list exactly with the positive enumeration when the occurrence
header is consistent, and `run_ofRuntimeSystem` gives the actual semantic
compiler's pinning rows. `run_nodup` excludes duplicates. `run_length_le_cubic`
retains the complete `16(s+1)^3` bit bound; `run_filter_steps_le` bounds every
actual finite test-and-emit call by one polynomial in the original section
length. `PositiveScanLoop` below realizes this executable iteration with a
complete repeated finite-machine runtime bound.

`AllDifferentCSPPositiveCounters.lean` supplies both finite binary counter
continuations using the pinned successor, pair-left/right and sequential
machine APIs. `PositiveRankResetMachine.outputsInTime` erases the rank word
in its bit length plus one steps; the pair adapters preserve every other
state field. `positiveInnerCounterComputableInPolyTime` increments rank, and
`positiveOuterCounterComputableInPolyTime` increments index and resets rank.
Each continuation adds at most one bit to the full state. The complete
`positiveInnerStepComputableInPolyTime` and
`positiveOuterStepComputableInPolyTime` compose membership, conditional emission
and the appropriate counter, including all transfers. `PositiveCounters.run_succ_eq`
identifies the required branch of the reached semantic state, and
`positiveInnerStep_run_steps_le` / `positiveOuterStep_run_steps_le` bound each
complete branch by one polynomial in the original section wire length.

`AllDifferentCSPPositiveScanInitialization.lean` now constructs the exact
`PositiveAdvance.seed` with binary candidate `(0, 0)` and an empty positive-row
list. `positiveScanInitialization_outputsInTime` preserves every counted-section
bit in at most `2s+2` steps, with no increase in encoded length and all work
stacks cleared. `runtimeCompilerPositiveScanInitializationComputableInPolyTime`
composes this initializer from the actual Boolean compiler input. The initialized
state satisfies the existing complete reached-state invariant.

`AllDifferentCSPPositiveBound.lean` now selects either retained unary bound
in `3s+3` finite-machine steps, then converts it to canonical binary using the
checked counting and pair-left APIs. `binary_length_le` charges the full bound
copy and retained state by `2s+1`. `AllDifferentCSPPositiveControl.lean` routes
the appropriate candidate coordinate and computed bound into binary comparison
order in `5s+5` steps. `positiveActiveComputableInPolyTime` decides
`index < variableCount`; `positiveContinuesComputableInPolyTime` decides
`rank < occurrenceCount`, including the last-rank transition and zero counts.
Both return the entire original state with just one added Boolean cell.
`PositiveControl.advance_eq` matches these decisions to the existing exact
rectangular traversal; `run_active_iff` gives precisely
`variableCount * (occurrenceCount + 1)` active visits. The two
`*_iterate_steps_le` declarations bound complete calls uniformly by polynomials
in the original retained-section wire length, including count conversion,
comparison, transfers and cleanup.

`AllDifferentCSPPositiveDispatch.lean` now composes the complete finite
rectangular step. `PositiveDispatch.computableInPolyTime` computes exhaustion
and continuation, invokes exactly one membership/emission/counter branch, and
returns exhausted states unchanged. The conditional-call controller and
`decisionEraseComputableInPolyTime` are shared with the pair scan by
parameterizing the retained encoding. Every copy, decision and cleanup is
included; `iterate_steps_le` and `run_step_outputsInTime` bound the complete
next-state call in the original counted-section bit length.

`AllDifferentCSPPositiveScanLoopMachine.lean` and
`AllDifferentCSPPositiveScanLoop.lean` now check the entire repeated scan.
The pair and positive scans share `FlaggedLoopMachine`; each cycle executes
the complete dispatcher and computes the next active bit. `run_bounded`
charges every one of the `n(q+1)` candidate visits and the final false-bit exit.
At loop-entry bit length `s`, set `B=16(s+1)^3+1`: the loop takes at most
`(s(s+1)+1)*(P(B)+4B+4)` steps, where `P` is the checked complete-body polynomial.
`positiveEnumerationComputableInPolyTime` also constructs the seed and control
bit; `runtimeCompilerPositiveEnumerationComputableInPolyTime` includes all
preparation from the actual Boolean compiler input. Its result retains the
ranked sections, negative rows and weight, ends at counters `(n,0)`, and contains
exactly the ordered semantic pinning rows (`result_ofRuntimeSystem` and
`result_outputEncode_ofRuntimeSystem`). `result_nodup` proves uniqueness and
`result_length_le_cubic` bounds the complete retained output. Count consistency
is needed only for the intermediate row-correspondence lemma; the actual
compiler constructs that count internally.

`AllDifferentCSPObjectiveRows.lean` now collects the complete residual-row list.
`objectiveRowsComputableInPolyTime` retains the unary variable count and puts
all positive rows before all negative rows in at most `2s+4` finite-machine
steps, clearing every scratch stack. Its complete output is no larger than
its input. `runtimeCompilerObjectiveRowsComputableInPolyTime` composes this
assembly from actual Boolean compiler input; `ObjectiveRows.assemble_result`
proves exact equality with the variable count and rows of
`compileUsingDomainEntryBound`, including order, weights and multiplicity.
The row decoder checks every tag and arity.

`AllDifferentCSPObjectiveEncoding.lean` now serializes a complete objective
payload into the exact canonical Boolean `RuntimeObjective.finEncoding`.
`ObjectiveEncoding.computableInPolyTime` composes the existing counted-row
traversal, binary outer-header constructor and framing machine. It counts the
variable/prime header as well as every residual row internally: counting takes
at most `20(s+1)^2` steps in payload length `s`, header conversion takes at most
`8(t+1)^2` in counted-wire length `t`, and framing takes at most three times
raw-wire length. The tally-retaining wire is at most `2s`, and the raw wire is
at most `2s+1`. The checked payload already contains the variable/prime header.

`AllDifferentCSPObjectiveHeader.lean` now computes both header fields while
retaining the exact residual rows. `ObjectiveHeader.runtimeCompilerComputableInPolyTime`
starts from actual Boolean compiler input, copies the retained occurrence
count, selects the same prime as `compileUsingDomainEntryBound`, and converts
both that prime and the original variable count to binary. The finite unary
encoding bridge takes `2s+2` steps without changing length; all prime selection,
binary counting and pair transfers are included in the composed polynomial.
`prepare_result` proves exact compiler correspondence, and `output_length_le`
bounds the complete binary-header/row tuple by `3s+4` in terminal scan length.
`AllDifferentCSPObjectiveAssembly.lean` now attaches the computed binary fields
and all residual rows in at most `3s+4` finite-machine steps, adding exactly
three arity cells. `runtimeCompilerComputableInPolyTime` composes the entire
compiler from `RuntimeCompilerInput.finEncoding` to the canonical Boolean
`RuntimeObjective.finEncoding`; no prime, counter, rank, graph or row list is
supplied by the caller.

The final declaration is `AllDifferentCSPEncoding.all_different_csp` in
`AllDifferentCSPCorollary.lean`. It combines that genuine polynomial-time
machine, the `64(s+1)^4` complete output-bit bound, primality and a sufficiently
large prime, attainment, exact minimum-conflict minimizers, and the satisfiable
specialization. `RuntimeObjective.loss` interprets the emitted rows at the
emitted prime and dimension; `compileUsingDomainEntryBound_loss` proves exact
agreement with the dependent semantic objective. The input encoding includes
a checked unary occurrence header and is at most twice the compact input
length plus one. Well-formed inputs have nonempty domains and in-range scope
indices; repetitions use set semantics and conflicts count deduplicated primal
edges. This completes `cor:all-different-csp` under those explicit conventions.

The complete scope-section machine in `AllDifferentCSPScopeMachine.lean`
remains checked. `ScopeSectionMachine.computer` uses five
finite-alphabet stacks. For each count-prefixed row it saves the original
binary count, emits its successor and the scope tag, and copies exactly that
many entries using an explicit binary predecessor loop. It restores any
looked-ahead delimiter before proceeding, preserving empty rows, repeated
scopes, repeated entries, and final-row exhaustion. The exact execution proof
halts with every non-output stack empty.
`scopeSection_outputsInTime` and `scopeSectionComputableInPolyTime` prove the
identity on whole scope lists from `ScopeFieldSection.rowPayloadFinEncoding`
to `ScopeFieldSection.outputFinEncoding` in at most `20 * (s+1)^2` steps for
actual payload bit length `s`. `completeScopeSectionComputableInPolyTime`
uses the pinned generic sequential-composition theorem to run the checked
linear outer-count removal internally, starting from
`ScopeFieldSection.inputFinEncoding`.

The checked scope output interface in `AllDifferentCSPScopeSection.lean`
continues to provide exact decoding, tag rejection, and the `4s` complete
output-size bound. `StructuralFieldStream.encode_eq_header_sections` fixes
the exact record and variable headers followed by the domain and scope
outputs; `raw_encode_eq_reversed_sections` identifies their reverse staging
with the checked raw structural view. Both complete section machines are now
present, and source splitting with both paired section passes now composes
from the actual compiler input. Variable-count extraction and source retention
now also compose from that input and the count survives both section passes.
The structural view now assembles under its checked payload encoding, and a
separate pass retains it while computing the unary outer row count. Binary
header conversion, raw assembly, and the original Boolean framing bridge now
compose from the actual input as
`runtimeCompilerStructuralViewComputableInPolyTime`.

The complete indexed domain-section machine remains checked:
`DomainFieldSection.rowPayloadFinEncoding` parses count-prefixed rows through
exact payload exhaustion, rechecks every row count, preserves empty rows, and
is no longer than `DomainFieldSection.inputFinEncoding`.
`rowFields_injective` proves the outer-count-free payload loses no domain
boundaries. `domainRowPayloadStructuredComputableInPolyTime` repackages the
existing concrete three-stack header-removal pass as an identity machine on
the structured domain list in at most `2s+1` steps.
`domainSectionComputableInPolyTime` consumes that checked payload, maintains
and increments its canonical binary index, and emits exactly
`RuntimeStructuralView.indexedDomainOccurrences` in at most `100(s+1)^3`
steps for payload bit length `s`; empty sections, empty rows, singleton rows,
and index carry growth are all covered by the exact execution proof. The
composed `completeDomainSectionComputableInPolyTime` starts instead from
`DomainFieldSection.inputFinEncoding` and internally runs both verified passes
to the same exact occurrence stream. The accompanying
`occurrences_indexedRowsFrom` theorem advances consecutive indices across all
rows, including empty rows, while `outputEncode_eq_row_outputs` and
`outputEncode_eq_structuralFields` prove that concatenating the already
checked per-row machine outputs is exactly the domain portion of the complete
structural target. `domainFieldRowComputableInPolyTime` remains the checked
quadratic machine for each indexed row, and
`scopeFieldBlockComputableInPolyTime` supplies the intact-scope branch.
`StructuralFieldStream.raw_decode_encode_reverse` still supplies the complete
full-stream target, and the prior quadratic theorem bounds that target in the
actual compiler input bit length. Source splitting, paired domain expansion,
and paired scope processing now compose from that input. The exact structural
view, including its original variable count, now assembles under the checked
payload encoding and also under the original Boolean encoding. The complete
composition includes outer row counting, binary-header staging, and framing;
`binaryPredComputableInPolyTime` already supplies its empty- and
singleton-safe binary countdown operation.

The headline catalogue contains 24 labelled entries: 23 complete and 1
partial, with nothing pending. The remaining partial row has its mathematical
content checked and lacks the Smith-normal-form algorithm and polynomial
running time (`thm:max-polytime`). `cor:all-different-csp` is complete. The clause-wise theorem is complete without
qualification: `CNFNormalisation.lean` normalises arbitrary 3-CNF syntax into
the three-distinct-variable convention and transfers the theorem.

## Post-snapshot formalisation queue

The following statements were added to the active thesis after the 24 July
snapshot. They are queued separately so that the audited 24-statement baseline
and its source commit remain unchanged. All five are now formalised in
[`PhdThesisLean/PrecisionGrowth.lean`](PhdThesisLean/PrecisionGrowth.lean),
and the corresponding checkbox tasks in [`TODO.md`](TODO.md) are complete.

| Thesis label | Status | Lean declaration or remaining work |
|---|---|---|
| `prop:precision-growth-covering` | Complete | `PrecisionGrowth.precision_growth_covering` proves $N_{\mathcal H}(S,k)$ equals the covering number of the prediction set in `ℤ_[p]^m` by closed radius-$p^{-k}$ balls in the product sup metric. `mem_closedBall_iff_toZModPow` identifies same-ball membership with coordinatewise agreement under `PadicInt.toZModPow`, and `coveringNumber_eq_ncard_image` proves the class-counting identity for arbitrary vector sets. |
| `prop:precision-growth-vc` | Complete | `PrecisionGrowth.precision_growth_binary` identifies the precision-one growth function at $p=2$ with the ordinary growth function of the reduced class, and `precision_growth_vc` proves the shattering-defined VC dimension of the reduced class equals the largest $m$ with $\Pi_{\mathcal H}^{(2)}(m,1)=2^m$, via `shatters_iff_patternCount_eq`. |
| `thm:affine-precision-growth` | Complete | `PrecisionGrowth.affine_precision_growth` proves $\Pi = p^{k\min(m,d+1)}$ for the affine class on `ZMod (p ^ K)` reduced to precision $k \le K$: `affine_patternCount_le` bounds every sample through the reduced coefficient vector, and `affine_patternCount_basisSample` attains the bound on the thesis sample $0,e_1,\ldots,e_{r-1}$ padded by zeros. `affine_precision_growth_log` records the base-$p$ logarithm form $E = k\min(m,d+1)$. |
| `prop:tree-syntax-growth-bound` | Complete | `PrecisionGrowth.tree_syntax_growth_bound` bounds the pattern count of `syntaxClass` — any interpretation of a finite shape family with `R` split-rule choices per internal node and `ZMod (p ^ k)` leaf labels — by $\min(p^{km}, \sum_T R^{I(T)} p^{kL(T)})$. |
| `cor:binary-tree-precision-growth` | Complete | `PrecisionGrowth.binary_tree_precision_growth` specialises the bound to ordered full binary trees with at most $n$ internal nodes via mathlib's `Tree.treesOfNumNodesEq_card_eq_catalan` and `Tree.numLeaves_eq_numNodes_succ`, giving $\min(p^{km}, \sum_{i\le n} C_i R^i p^{k(i+1)})$. |

The cardinality equalities and inequalities are the primary Lean interface,
as planned. For the affine theorem the base-`p` logarithm identity
`E = k * min m (d + 1)` is also recorded via `Nat.log`; the real-logarithm
entropy formulas can be derived later if useful.

## Rational witnesses and conditional counting consequences (28 October additions)

Specification: `../phd-thesis/complexity-regimes/eth-addendum.tex`, at thesis
commit `c700eca04c2d8a819c0403252a97134475857038`, SHA-256
`25fa65a1b097da0b35a83074b9d4515d9a84aac7d4ea74dd45f267edee77b3c6`.
Audited on 13 November 2026 (Sydney). These additions are separate from the
earlier headline catalogue. `prop:regression-np-complete` is **Partial**.

| Obligation | Status | Checked declaration or remaining work |
|---|---|---|
| Independent-column reduction | Complete (semantic) | `RationalWitnesses.exists_column_reduction` selects exactly `A.rank` distinct original columns, proves their independence and equality of the entire rational prediction spaces. `mulVec_extend` and `extend_eq_zero` prove the original-coordinate embedding with zeros off those columns. Rank zero is included. |
| Contact refinement and rational attainment | Complete (semantic) | `contact_refinement` produces a full independent contact set in the reduced design without increasing any original residual norm. `finite_candidateModels`, `exists_candidate_le`, and `exists_global_minimizer` prove finite-family domination and attainment for arbitrary rational matrices and targets. `threshold_iff_candidate` covers every rational threshold. `exists_affine_global_minimizer` adds the column of ones. |
| Exact determinant representation | Complete (algebraic) | `contact_cramer` proves nonsingularity of the selected row minor and Cramer's formula. `exists_global_minimizer_cramer` exhibits an optimum supported on `rank A` columns whose coefficients are ratios of determinants of a nonsingular `rank A` square minor and its target-column replacements. This is not a coefficient-size bound. |
| Polynomial certificate bit length | Complete (size, ordinary and affine) | `RationalWitnessBounds.commonDen_le_pow`, `cleared_natAbs_le`, `det_size_le`, and `det_ratio_sizes_le` bound denominator clearing, integer determinants and reduced rational fields. `exists_global_minimizer_bits` applies the bound to a genuine global optimum. For actual binary input length `L`, `RationalWitnessEncoding.exists_global_minimizer_encoding` bounds a complete dense certificate by `12L³ + 9L + 1`; `threshold_iff_short_certificate` restricts threshold witnesses to that bound. `exists_affine_minimizer_encoding` bounds the intercept and all coefficients by `28(L+1)³ + 9(L+1) + 1` in the original input length. Binary dimensions, signs, denominators and framing are charged. |
| Fixed-prime valuation of binary magnitudes | Complete (machine primitive) | `FixedDivisorBinary.division_pass` retains quotient and remainder after exactly `2s+2` TM2 steps; `computableInPolyTime` outputs the canonical binary quotient after `2s+3`. `PadicValuationMachine.valuation_run` proves actual repeated binary division computes `padicValNat p n`, including zero. `outputsInTime` and `computableInPolyTime` give at most `4(s+1)²` steps from the standard binary input alone to the library unary output, with both work stacks empty and state reset. `valuation_le_size` bounds that output by `s` bits. Here `s = Nat.size n`; `p` is fixed in the finite control, not another binary input. |
| Intermediate verifier bit lengths | Complete (size and arithmetic correctness) | `RationalVerifierBounds` evaluates unreduced fractions without gcd normalization. `check_correct` proves exact agreement with the thesis loss, for arbitrary thresholds and all shapes. `residual_prefix_bounds`, `norm_power_bounds`, `loss_prefix_bounds` and `comparison_bounds` bound every stored accumulation prefix, norm power and final signed comparison product in actual combined input/certificate length `S` (positive row count). `compareWidth_polynomial` gives `2*size(p)*S³ + 3*size(p)*S² + (size(p)+3)*S + 1` bits for each comparison product. `Fraction.encode_length_le` charges signs and frames. `short_comparison_bounds` specializes to the proved cubic certificate bound; `threshold_iff_short_check` connects the executable arithmetic checker to short witnesses. No complete machine runtime follows. |
| Fixed-base powers and valuation composition | Complete (machine primitive) | `FixedBasePowerMachine.mulBits_encodeNat` and `multiply_run` prove canonical binary multiplication by a fixed positive base, with carry in `Fin p`; `multiplyTime_le` bounds a full pass by `2s+2*size(p)+3` TM2 steps. `power_run`, `outputsInTime` and `computableInPolyTime` compute `p^e` in at most `(2*size(p)+7)(e+1)²` steps from a **unary** exponent. `valuationPowerOutputsInTime` and `valuationPowerComputableInPolyTime` compose the existing binary valuation machine with powering and the checked transfer machine: binary `n` to binary `p^(padicValNat p n)` in at most `(2*size(p)+15)(size(n)+1)²` steps. All work stacks are cleared and control reset. |
| Exact rational norm on binary fractions | Complete (machine component) | `RationalNorm.computableInPolyTime` computes the existing `Fraction.norm p` in the original signed/framed binary input and output encoding for every fixed prime, allowing unreduced fractions and zero. `Prepare.outputsInTime` parses both frames and retains the zero flag in at most `2L+3` TM2 steps. `pairPowerComputableInPolyTime` and `fieldsPowerComputableInPolyTime` execute both valuation-power calls with checked pair retention; `Assemble.outputsInTime` swaps fields, restores frames, handles zero and clears all stacks in at most `5T+5` steps in its tagged input length. Checked composition supplies an actual polynomial TM2 runtime, including all transfers. `assemble_power_prepare` identifies the exact output with `Fraction.norm`; `rationalOutputsInTime` and `rational_value_correct` connect the thesis rational encoding and norm. |
| Fraction-string validity on arbitrary binary inputs | Complete (machine component) | `RationalFractionValidity.valid_iff` proves acceptance exactly for the existing `Fraction.encode` image: canonical binary magnitudes, positive zero sign and positive denominator, permitting unreduced fractions. `field_iff` characterizes framed prefixes with arbitrary unused suffixes. `Machine.step_cfg` connects each abstract transition to one actual finite TM2 step; `run`, `outputsInTime` and `computableInPolyTime` decide validity in at most `3L+10` steps for **every** Boolean string of length `L`. Missing signs/separators/payload, redundant high zeros, negative zero, zero denominators and trailing data are rejected. Both private stacks are emptied and control reset on all paths. |
| Signed integer and final cross-product comparison | Complete (machine component) | `SignedIntegerComparison.computableInPolyTime` compares two concatenated `SmithEncoding.encodeInt` words in at most `2L+1` actual TM2 steps, including sign/frame reading, stack reversals, magnitude comparison and cleanup/reset. All sign combinations, zero and unequal widths are covered. `RationalThresholdComparison.lossComparisonOutputsInTime` consumes the **already computed and serialized** final cross-products and takes at most `16*size(p)*S³ + 24*size(p)*S² + 8*(size(p)+3)*S + 17` steps in original combined input/certificate bits `S`; `loss_answer_correct` identifies the thesis threshold. Product construction is now supplied by `RationalArithmetic` below; malformed-input rejection remains separate. |
| Multiplication of two binary magnitudes | Complete (machine component) | `BinaryMultiplication.run` computes the canonical binary product with a concrete six-stack TM2. `outputsInTime` and `computableInPolyTime` bound all routing, Horner shifts, finite-carry additions, factor restoration and final cleanup by `6(L+1)² + 12(L+1)` transitions, where `L = size(m)+size(n)` is the tagged-pair input length. Both factors vary; no unbounded arithmetic register or runtime hypothesis is used. `output_length_le` bounds the result by `L` bits. This uses the library pair encoding over `Sum Bool Bool`; the following machine compositions bridge to signed/framed integers and fractions. |
| Signed integer multiplication | Complete (machine component) | `SignedIntegerMultiplication.computableInPolyTime` computes the exact signed/framed integer product, including routing, magnitude multiplication, sign retention, canonical zero, output assembly and all adapter transfers. See the 7 November increment below. |
| Fraction multiplication and comparison | Complete (machine components) | `RationalArithmetic.multiplicationComputableInPolyTime` and `comparisonComputableInPolyTime` consume two concatenated original Boolean fraction words. Both products, field routing, pair retention, output serialization and comparison are charged. `Prepare.outputsInTime` proves exactly `2L+10` steps; `Assemble.outputsInTime` proves at most `2T+2`. `crossProductsComputableInPolyTime` constructs the signed comparison input. The product and cross-product pair each have output length at most `L`. `boundedLossComparisonOutputsInTime` bounds this full final phase by an actual polynomial in original combined input/certificate bits, consuming an **already evaluated and serialized loss fraction** and threshold. Unreduced fractions, all numerator signs and zero are included; arbitrary malformed strings are outside the contract. |
| Subtraction of aligned binary magnitudes | Complete (machine component) | `BinarySubtraction.Machine.run`, `outputsInTime` and `computableInPolyTime` compute natural subtraction, returning zero on underflow, in exactly `2L+2` finite TM2 transitions. Here `L=max(size(m),size(n))` is the complete library aligned-pair length over `Option Bool × Option Bool`. Borrow propagation, high-zero removal, canonical empty zero, input/work cleanup and state reset are included. `subtract_borrow` identifies the underflow bit; `output_length_le` bounds output by `L`. Signed addition/subtraction on the original framed words is supplied by the following increment. |
| Signed integer addition and subtraction | Complete (machine components) | `SignedIntegerAddition.run`, `outputsInTime`, `additionComputableInPolyTime` and `subtractionComputableInPolyTime` consume two concatenated `SmithEncoding.encodeInt` words and return the exact sum or difference in that same format. A concrete six-stack finite TM2 takes at most `4L` transitions in all source Boolean bits, including parsing, comparison with digit retention, recovery, finite carry/borrow, high-zero removal, sign selection, framing and cleanup/reset. `output_length_le` bounds the complete result by `L`. No arithmetic-cost premise or adapter runtime assumption is used; arbitrary malformed-string rejection remains outside this encoded-pair contract. |
| Fraction addition and subtraction | Complete (machine components) | `RationalAddition.additionComputableInPolyTime` and `subtractionComputableInPolyTime` consume the original concatenated Boolean fraction words and return exactly the existing unreduced `Fraction.add`/`Fraction.sub` encoding. Three signed products, signed addition/subtraction, source duplication, denominator projection, preservation and every adapter transfer are charged. `Copy.run` takes exactly `3L+3` steps; `Right.run` takes `u+2v+2` for its tagged component lengths. `assemble_operation` proves exact serialization; `value_correct` gives rational semantics; `output_length_le` bounds the full result by `2L`. No arithmetic-cost or runtime premise is supplied. Malformed-input rejection and iteration across regression data remain separate. |
| Repeated fraction summation | Complete (machine component) | `RationalSum.computableInPolyTime` and `sumComputableInPolyTime` run a uniform finite TM2 over an initial fraction and a runtime-length delimited list. Every addition, delimiter, transfer, tail retention and final output is charged. An additive source-width budget bounds every accumulator prefix; the complete time is `(L+1)*(P(8L+6)+24L+24)` in actual serialized length, where `P` is the proved addition-machine polynomial. `boundedLossOutputsInTime` specializes to the already serialized norm list and charges summation against original combined input/certificate bits. Norm-list production from serialized residuals is supplied by the following increment; original regression parsing and residual computation remain pending. |
| Norm-list traversal and summed loss from residuals | Complete (machine components) | `RationalNormList.computableInPolyTime` maps the original binary norm machine over a runtime-length delimited fraction list, preserving order and multiplicities and producing the exact summation encoding. All calls, tail/prefix preservation, transfers, delimiters, reversal and the six-symbol zero prefix are charged. In complete source length `L`, time is `(L+1)*(P(L)+(8*size(p)+2)*L+20)` and output length is at most `(4*size(p)+8)*L+6`. `sumComputableInPolyTime` composes this with actual fraction summation; `boundedLossOutputsInTime` returns the exact stored loss fraction from serialized residuals in polynomial original combined input/certificate length. The original parser and residual-list generation remain open. |
| Polynomial-time verifier on binary rational data | Pending as a whole | Exact binary rational norms, individual fraction-string validity, signed-integer arithmetic components, fraction multiplication, addition, subtraction, comparison, runtime-length norm traversal and summation now have complete machine theorems; the unreduced-fraction arithmetic checker has semantic correctness and polynomial intermediate-width bounds. `RationalWitnessEncoding.encodeInput` specifies binary dimensions, indexed rational data and threshold. Still required: uniform runtime-dimension input/certificate parsing with dimension/count/structure rejection, residual evaluation/list production, composition with the completed norm/summation/comparison machines, and the end-to-end verifier time bound. The standalone validity machine is not yet composed with the norm machine or a whole regression-input parser. |
| NP membership and NP-completeness | Pending | Compose the certificate-size theorem and verifier, then connect the existing integral-row/natural-bound hardness language to the new binary rational language with a checked encoding reduction. Existing NP-hardness does not by itself supply this bridge. |
| `prop:sparse-compiled-subexp` | Pending | Counting-preserving 3-CNF with unique gate extensions and a linear balanced population-count circuit; conditional exact optimisation, optimum counting and recovery with time/space bounds. |
| `cor:compiled-subexp-approx` and applications | Pending | Uniform sampling with multiplicities, error/failure bounds and bounded sampling runtime; signed clauses, list-colouring and positive Max-Cut instantiations, with floor counts distinguished from nonzero-conflict optima. |

Correspondence: `RationalWitnesses.loss_eq_thesis` identifies the Lean objective
with `sum_i |y_i - (A beta)_i|_p`. The proved semantic statements are stronger
in dimensions: they allow empty rows/columns as well as the thesis's positive
dimensions. They impose no full-rank, distinct-row, consistent-response, or
minimizer-existence hypothesis. Indexed rows retain multiplicity. The candidate
family is finite only after selecting a column basis and zeroing the unused
coordinates; no finiteness claim is made about all minimizers of a deficient
design. Column selection is semantic, not a polynomial-time algorithm.

The size proof uses `b = dataBits (inputData A y)`, the sum of binary
numerator-magnitude and denominator lengths. The common denominator product is
at most `2^b`, cleared integer magnitudes are at most `2^(2b)`, and each
rank-`s` determinant has magnitude length at most `s*(2b + Nat.size s) + 1`.
Canonical rational reduction cannot increase either field. These coefficient
bounds allow empty shapes. The **dense serialized** bounds require `r > 0`,
as the thesis does: with binary dimensions and no rows, arbitrarily many zero
coordinates would otherwise have an uncharged dense output cost. No positivity
assumption on `d` is needed. The affine proof charges the added ones against
the original input (`affineData_bits` adds exactly `2r` payload bits).
The serializers are concrete; neither parser efficiency nor a uniform machine
follows from these length and round-trip theorems. No thesis claim was changed.

The proof reuses `RegularisedCandidates.hindependent_contact_refinement` and
`hfinite_candidateModels`; mathlib's `exists_linearIndependent'`,
`Matrix.range_mulVecLin`, row-independence/invertibility equivalence, and
adjugate identity supply the linear algebra. The size proof additionally uses
mathlib's Leibniz determinant bound, factorial/power bounds, `Nat.size`, and
divisibility of canonical rational fields. The earlier semantic/size audits
and the eighteen division/valuation endpoint audits use only `propext`, `Classical.choice`, and `Quot.sound`.
The new machine theorem checks the repeated-division ingredient in the
thesis proof of `prop:regression-np-complete`. Each long-division digit transition
uses only a remainder in `Fin p` and finitely many Boolean flags, so the
control arithmetic is a finite lookup at fixed `p`. The quotient is kept in
canonical binary, and its bit length strictly decreases on each positive
exact division. The exact runtime recurrence charges both scans, all empty
checks, the terminal failed division and quotient cleanup. Its quadratic bound
is in the supplied **binary** magnitude length, not in the integer value.
The valuation output is explicitly unary and has at most that length; this
is suitable for subsequent norm computation but is not yet a complete rational
input verifier. No uniform-in-`p` claim is made. Neither ordinary nor affine
NP membership follows yet. No thesis correction was needed or made.

The 1 November increment discharges the intermediate-width obligation for a
specific exact arithmetic evaluation. `Fraction` stores an integer numerator
and a positive natural denominator, without requiring coprimality. Addition,
subtraction and multiplication use cross-products; `Fraction.value_norm`
proves that `p^(v_p denominator) / p^(v_p |numerator|)` is the exact norm of
any nonzero stored fraction, with zero handled separately. No gcd is needed.
This is executable Lean arithmetic, not a finite-machine implementation.

For `S = length(encodeInput A y B) + length(encodeRats beta)`, put
`R = (S+1)(2S+1)`, `Q = size(p)*R+1`, and `F = 1+S*(Q+1)`.
Every original coefficient product has field width at most `2S`; each
left-to-right residual prefix has width at most `R`; each norm and each
power prefix used to compute it has width at most `Q`; and every accumulated
loss prefix has width at most `F`. Both final comparison cross-products have
width at most `F+S`. Generic cross-product bounds also bound the temporary
arithmetic products. A raw fraction with both fields bounded by `h` has at
most `4h+3` encoded bits, including sign and framing. All these bounds are on
unreduced fields; cancellation is not assumed. Substituting the existing short
certificate bound gives `S ≤ 12L³+10L+1`, hence a degree-nine size bound in
original input length. These are bounds on stored numbers, not operation counts
or execution times. `r > 0` charges dense dimensions, as in the thesis;
`d = 0`, rank deficiency, repeated/conflicting rows, negative thresholds and
zero residuals remain covered. Arithmetic correctness itself permits `r = 0`.
The independent endpoint audit includes the checker, valuation, certificate and
hardness declarations and uses only the standard foundational axioms.
No mathematical discrepancy with `prop:regression-np-complete` was found.
The remaining work is the explicit machine implementation/composition and
hardness encoding bridge, rather than another semantic or width proof.

The 2 November increment closes fixed-base powering and its **actual machine
composition** with binary valuation. Multiplication processes little-endian
bits with carry in `Fin p`; each control transition is a finite lookup for
fixed `p`. The final carry is emitted bit by bit, then the result is reversed
into canonical binary. `scanTime`, `multiplyTime` and `powerTime` describe exact
executions, charging empty checks, carry emission, reversals, loop control and
halting. `mulBits_encodeNat` includes zero magnitudes and arbitrary initial
natural carries; the machine uses bounded carries. The power machine permits
any positive fixed base, including one, and exponent zero returns one.

The standalone exponent is **unary**, exactly the encoding produced by
`PadicValuationMachine`. This does not assert polynomial time in arbitrary
binary exponents. The composed `valuationPowerOutputsInTime` uses
`valuation_le_size` and the library's checked `compositionMachine_outputsInTime`
(including `4v+4` steps for transfer of `v` unary valuation marks) to obtain the
explicit quadratic bound in the original binary magnitude length. The output
is the canonical binary encoding of `p^(padicValNat p n)` and has at most
`size(p)*size(n)+1` bits. For `n=0`, mathlib's valuation convention gives output
one; the existing `Fraction.norm` handles a zero numerator separately. Thus
the component matches both power fields in the thesis verifier's exact norm
formula, without asserting that their extraction, assembly, or the rest of the
rational verifier has been implemented. No new thesis assumption or correction
is needed, and no uniform-in-`p` runtime is claimed.

The 3 November increment closes the **complete exact-norm machine component**.
`RationalNormRouting.lean` reads the existing `Fraction.encode` bitstream: a
sign, framed binary magnitude, then framed positive denominator. Unary frame
lengths are held on a work stack, never in an unbounded control register. The
canonical numerator payload is empty exactly for zero. Its exact routing run
is `3*(a+b)+9` steps for payload lengths `a,b`, at most `2L+3` in the actual
input length `L=2a+2b+3`. `decodeFraction_encode` retains unreduced fields and
proves the new bundled encoding is the existing wire format.

`RationalNormMachine.lean` composes this router, the two existing binary
valuation-power machines, the checked left/right pair adapters and the output
assembler. The zero flag survives both calls. `RationalNormAssembly.lean`
swaps the fields into numerator `p^(v_p denominator)` and denominator
`p^(v_p |numerator|)`, generating the original Boolean frames and positive sign.
For zero it drains the computed result and emits `0/1`. The assembler takes at
most `5T+5` steps, including that drain. All scratch stacks are empty and finite
control is reset at each component boundary. Polynomial closure here invokes
actual machine/transfer execution theorems; no arithmetic-operation oracle,
supplied runtime hypothesis or unbounded integer control is introduced.

`assemble_power_prepare` proves literal output-bit equality with the prior
`Fraction.norm`; `value_correct` and `rational_value_correct` prove the thesis
norm. `ofRat_encode` identifies the input with `encodeRat`, and
`rationalOutputsInTime` supplies its actual execution. Shared numerator and
denominator factors are allowed; no gcd normalization is performed. The output
has at most `4*size(p)*L+7` bits. Runtime is polynomial for each **fixed** prime;
no tight degree or uniform-in-prime bound is claimed for the adapter-composed
machine. The independent audit covers all 63 explicitly declared public names
plus six earlier norm/certificate/hardness endpoints. All use only `propext`,
`Classical.choice`, `Quot.sound` or subsets. Eight concrete routing/assembly
executions check zero, negative and positive numerators, shared factors,
field order, unequal lengths, cleanup and reset; three kernel-checked examples
check the corresponding rational values.

This closes the norm operation in the rational-arithmetic sentence of
`prop:regression-np-complete`, with the unchanged thesis commit and addendum hash
above. It does not implement residual multiplication/addition, matrix traversal,
summing norms, threshold comparison, or a rejecting verifier for arbitrary
strings. The full verifier and NP-completeness remain pending. No mathematical
claim or thesis assumption changed.

`RationalFractionValidity.lean` and `RationalFractionValidityMachine.lean` close
the next parsing component. The parser's high-bit test is proved equivalent to
canonical binary magnitudes, including the empty zero encoding. Its prefix
theorem retains the unused suffix and requires a positive denominator without
requiring coprimality. `valid_rational` covers every original `encodeRat` input;
the larger accepted language is exactly the unreduced `Fraction` format used
by the evaluator, not an assertion that every accepted fraction is reduced.

The three-stack machine has finite labels and finite Boolean/optional-Boolean
state. Its unbounded frame counter is a stack of marks. A potential
`3 * remainingInput.length + 2 * count + phaseWeight` strictly decreases on
every nonhalting transition. `step_cfg` checks those transitions against the
actual program; `run` proves halting with the prescribed Boolean output, empty
input/count stacks and reset state. The initial potential is `3L+10`, including
all rejection and cleanup paths. This is an unconditional machine bound, not
an arithmetic-operation estimate or a well-formed-input-only contract.

The independent type/axiom audit checks all 42 explicit public declarations
and six prior norm/checker/certificate/hardness endpoints: 26 reports use only
`propext`, `Classical.choice`, `Quot.sound` or subsets, and 22 are axiom-free.
The full default and prototype build passes (9,309 jobs); neither new module
has warnings. Fourteen actual-machine examples cover valid/unreduced fractions
and malformed inputs, checking both cleanup and reset. All 2,047 strings of
length at most ten also agree with an independently enumerated finite set of
fraction encodings. Three concrete parser equalities are kernel-checked.

The thesis correspondence is the binary-rational verification ingredient of
`prop:regression-np-complete` at the unchanged commit and hash above. Individual
fraction recognition is complete; runtime-dimension parsing, signed arithmetic,
residuals, loss accumulation, comparison and complete verifier composition
remain open. The certificate-size, NP-membership and hardness milestones keep
their separate statuses. No thesis claim or mathematical assumption changed.

### Signed comparison increment (5 November 2026)

`SignedIntegerComparison.lean` supplies the finite comparison machine on the
concatenation of two existing signed/framed integer encodings. `field_run`
reads one sign and length frame and retains the canonical binary magnitude on
its stack; its count and reversal scratch are empty at the phase boundary.
`scan_run` compares aligned bits, reversing magnitude order for negative
pairs; different signs are handled separately. For magnitude widths `a,b`,
`run` proves exactly `3(a+b) + max(a,b) + 9` TM2 transitions, including all
empty-stack tests and final output. Since the complete input length is
`L = 2(a+b)+4`, `outputsInTime` gives `2L+1`. Every private stack and the input
are empty at halt, and the finite state is reset. `computableInPolyTime` has
no supplied parser, arithmetic or runtime premise. Its domain is encoded
integer pairs, not arbitrary Boolean strings.

`RationalThresholdComparison.lean` connects that actual machine to the
existing unreduced evaluator. `fraction_answer_correct` handles arbitrary
signed fractions with positive denominators, including unreduced and equal
fractions. `boundedOutputsInTime` compares two encoded integers of width at
most `w` in at most `8w+9` steps. With the previously proved comparison widths,
`lossComparisonOutputsInTime` gives
`16*size(p)*S³ + 24*size(p)*S² + 8*(size(p)+3)*S + 17` actual steps, where `S`
is the original combined regression-input and certificate length.
**The machine's input is the pair of already computed, serialized products.**
This theorem does not charge loss evaluation, multiplication, or construction
of that input. `loss_answer_correct` proves the output equals the thesis
threshold decision; no arithmetic-cost assumption is hidden in the statement.

Validation: the full `lake build PhdThesisLean DiscreteMetricRegression`
passes (9,313 jobs). The independent audit checks all 39 new public
declarations and six earlier norm/checker/certificate/hardness endpoints:
28 use only standard axioms and 17 are axiom-free. Neither new source module
has warnings. Twelve named executions (including 1,025-bit magnitudes), all
4,225 pairs in `[-32,32]²`, and five rational cross-product cases check actual
output, exact steps, cleanup and state reset. Three concrete comparisons are
kernel-checked. All 183 project/adapter sources pass the prohibited-token
scan; all ten dependency revisions and tracked sources match their pins.

The signed-comparison obligation in the rational-arithmetic sentence of
`prop:regression-np-complete` is closed, with no change to the thesis claim.
Signed addition/subtraction and multiplication, whole-input parsing,
residual/loss evaluation, product serialization and complete machine
composition still block NP membership and the hardness encoding bridge.


### Binary multiplication increment (6 November 2026)

`BinaryMultiplication.lean` closes multiplication of two variable natural
magnitudes, a required arithmetic component of the rational verifier. The
input is the existing library `PairEncoding` of two canonical binary words:
a left/right tag and one payload bit per symbol in `Sum Bool Bool`. Thus
`L = size(m)+size(n)` counts tagged symbols; this is not the concatenated
signed/framed `SmithEncoding.encodeInt` format or a raw Boolean-string parser.
The output is the canonical Boolean word for `m*n`, of length at most `L`.

The machine has six stacks, seven labels and finite Boolean/optional-symbol
control. It routes the first operand in most-significant-first order, retains
the second operand, then uses the Horner recurrence `a ↦ 2a + bit*n`.
`shift_encode` handles the empty zero word without introducing a redundant
zero digit. `add_run` proves each ripple-carry pass and preservation of the
factor; `round_run` includes restoration of both the result and factor.
`horner_encode` and `loop_run` identify the final stack with the product.
`run` proves the exact recursive runtime, including routing and draining the
retained factor at halt. All non-output stacks are empty and control is reset.

`next_size` bounds accumulator growth at each digit; `loopTime_le` then bounds
the actual repeated execution. `runtime_le`, `outputsInTime` and
`computableInPolyTime` give `6(L+1)²+12(L+1)` TM2 transitions. Both operands
are binary inputs of arbitrary width; the machine has no unbounded arithmetic
register, unit-cost multiplication instruction, supplied runtime hypothesis
or dependence on a fixed multiplier. Zero in either position is included.

Correspondence: this proves the natural-magnitude multiplication ingredient
in the rational-arithmetic sentence of `prop:regression-np-complete`, at the
unchanged thesis commit and addendum hash above. It is a partial component of
that proposition, not the complete signed/rational multiplication operation.
Sign/frame extraction, canonical zero-sign handling and product serialization
must still be composed with this machine. Signed addition/subtraction,
whole-input validation, residual/loss computation and complete verifier
composition remain open, followed by NP membership and the hardness encoding
bridge. No thesis claim or mathematical assumption changed.

Validation: `lake build PhdThesisLean DiscreteMetricRegression` passes (9,315
jobs). The independent type/axiom audit checks all 43 explicit public names
and seven prior norm/checker/certificate/comparison/hardness endpoints:
38 reports use only standard axioms, and 12 are axiom-free. The new module
has no warnings. Twelve named executions (including 128-bit carry chains
and 129-bit unequal operands), all 1,089 pairs in `[0,32]²`, and three
kernel-evaluated machine examples pass output, exact runtime, polynomial
bound, cleanup and control-reset checks. All 185 project/adapter sources
pass the prohibited-token scan; all ten dependency revisions and tracked
sources match their pins.

### Signed multiplication increment (7 November 2026)

`SignedIntegerMultiplication.computableInPolyTime` closes signed integer
multiplication on the original Boolean format: the input is the concatenation
of two `SmithEncoding.encodeInt` words and the output is exactly
`SmithEncoding.encodeInt (a*b)`. There is no arithmetic-cost or runtime premise.
The contract covers encoded integer pairs, including zero and arbitrary signs;
it does not assert rejection of malformed raw strings.

`SignedMultiplicationRouting.lean` extracts both canonical magnitudes and the
xor of their signs, using finite Boolean/optional-symbol control and a stack
counter for each length frame. `Prepare.run` proves exactly `3(u+v)+10` TM2
transitions, where `u,v` are magnitude widths. With full Boolean input length
`L=2(u+v)+4`, `Prepare.outputsInTime` gives `2L+2`.
`SignedMultiplicationAssembly.lean` serializes a magnitude and sign. It checks
whether the magnitude stack is empty before retaining a negative sign, so zero
is canonical even when supplied with a negative flag. `Assemble.run` proves
exactly `3w+4` transitions, or `3T+1` in its tagged input length `T=w+1`.
Both machines clear their input and scratch stacks and reset finite control.

The already-checked natural multiplier is lifted through the pair-retaining
adapter, then composed with these two machines using the checked sequential
adapter. Thus sign retention, all transfers, multiplication, framing and
cleanup have a polynomial TM2 bound. No tight degree is claimed for the
adapter-composed bound. `product_sign` and `assemble_multiply_prepare` prove
signed arithmetic and exact serialized-output agreement; `output_length_le`
bounds the complete framed output by the complete framed input length.

Correspondence: this closes signed integer multiplication within the rational
arithmetic sentence of `prop:regression-np-complete`, at thesis commit
`c700eca04c2d8a819c0403252a97134475857038`, with unchanged addendum SHA-256
`25fa65a1b097da0b35a83074b9d4515d9a84aac7d4ea74dd45f267edee77b3c6`.
It remains a component of that proposition. Rational field routing and operation
composition, signed addition/subtraction, whole-input/certificate parsing,
residual/loss traversal, and final comparison composition remain open, followed
by NP membership and the binary-rational hardness bridge. The existing
semantic, certificate-size and hardness milestones retain their separate
statuses. No thesis claim or mathematical assumption changed.

Validation: the full `lake build PhdThesisLean DiscreteMetricRegression`
passes (9,318 jobs). The independent audit covers all 59 new explicit public
declarations and eight earlier multiplication/norm/checker/certificate/
comparison/hardness endpoints: 42 reports use only `propext`, `Classical.choice`
and `Quot.sound` (or subsets); 25 are axiom-free. None of the three new modules
has warnings. Twelve named executions, including 128-bit carry chains and
129-bit unequal operands, and all 1,089 pairs in `[-16,16]²` pass actual
three-phase output checks and routing/assembly exact-step, cleanup and reset
checks. A separate negative-zero flag test and three kernel-evaluated examples
also pass. These executions test the three concrete phases; adapter transfers
are covered by the composition proof. All 188 project/adapter sources pass
the prohibited-token scan, and all ten dependency revisions and tracked sources
match their pins.

### Fraction multiplication and comparison increment (8 November 2026)

`RationalArithmetic.multiplicationComputableInPolyTime` and
`comparisonComputableInPolyTime` consume two concatenated `Fraction.encode`
words over `Bool`. The first returns exactly `Fraction.mul` in the same
unreduced representation. The second constructs the two signed cross-products,
serializes them and executes the signed comparison machine. No arithmetic-cost
or runtime premise is supplied. Positive denominators, arbitrary numerator
signs, zero, unequal widths and unreduced representations are covered. The
input contract is encoded fraction pairs; it does not reject arbitrary strings.
`decodePrefix_encode_append` and `decode_encode` check the encoding left inverse.

`RationalArithmeticRouting.lean` has finite Boolean field indices and a stack
counter for each frame. It retains the original frames and adds positive signs
to the two denominators. Its fixed mode selects ordinary or crossed products.
`Prepare.run` and `outputsInTime` prove exactly `2L+10` transitions in the full
original Boolean input length. Both field stacks and the counter are emptied,
and control resets. `RationalArithmeticAssembly.lean` removes pair tags and,
for multiplication only, the denominator sign. `Assemble.run` counts input
symbols plus retained output bits plus two transitions; `outputsInTime` bounds
this by `2T+2`. Its input and scratch stacks empty and control resets.

`productsComputableInPolyTime` executes both completed signed multipliers using
the checked left/right pair adapters. Sequential composition charges every
intermediate transfer, output assembly and final comparison. No tight degree
is claimed for the resulting polynomial. `assemble_mul`,
`assemble_crossProducts`, `multiplication_value_correct` and
`comparison_value_correct` prove exact representation and rational semantics.
Both the fraction product and serialized cross-product pair have length at
most the original input length.

`loss_input_length_le` bounds the full input of the final comparison phase by
`4W+6`, where `W=2*size(p)*S³+3*size(p)*S²+(size(p)+3)*S+1` and `S` is the
original combined regression input/certificate bit length. `lossComparisonTime`
is the actual composed comparison-machine polynomial evaluated at this cubic
bound. `boundedLossComparisonOutputsInTime` proves that bound on real machine
transitions, for positive row count. Unlike the earlier product-only phase,
it includes cross-product construction and serialization. It still consumes
an **already evaluated and serialized loss fraction** and the threshold;
computing that sum or traversing the regression data is not included.
`loss_answer_correct` identifies the result with the thesis summed-loss test.

Correspondence: these are multiplication and comparison ingredients of the
rational-arithmetic sentence in `prop:regression-np-complete`, checked against
thesis commit `c700eca04c2d8a819c0403252a97134475857038` and unchanged addendum
SHA-256 `25fa65a1b097da0b35a83074b9d4515d9a84aac7d4ea74dd45f267edee77b3c6`.
The 28 October agenda is also unchanged. No mathematical discrepancy or thesis
edit was needed. The whole verifier remains pending: signed and fraction
addition/subtraction, runtime-dimension parsing with bounded count rejection,
residual/loss traversal and accumulation, loss serialization and their complete
composition are still required. NP membership, the checked binary-rational
hardness bridge and NP-completeness remain separate pending milestones.

Validation: full `lake build PhdThesisLean DiscreteMetricRegression` passes
(9,321 jobs). The independent type/axiom audit covers all 84 new explicit public
declarations and nine earlier arithmetic/norm/checker/certificate/hardness
endpoints: 70 reports use only `propext`, `Classical.choice` and `Quot.sound`
(or subsets), and 23 are axiom-free. The full build has 1,317 standard-only
reports and 38 axiom-free reports. Its 555 warnings are in existing modules;
none is in the three new modules. Ten named fraction-pair executions, including
129-bit fields, and all 1,296 pairs with numerators in `[-4,4]` and denominators
in `[1,4]` pass both multiplication and comparison. The concrete arithmetic
phases, routing/assembly exact steps, bounds, cleanup and reset are checked;
adapter transfers are covered by the composition proof. Three kernel-reduced
routing/assembly examples pass. All 191 project/adapter sources pass the
prohibited-token scan. All ten dependency revisions and tracked source trees
match their pins; toolchain and Lake configuration are unchanged.

### Binary subtraction increment (9 November 2026)

`BinarySubtractionMachine.lean` closes a magnitude-subtraction component of the
rational verifier. `Machine.run` proves exactly `2L+2` actual transitions on the
library `BinaryNatPair.finEncoding`, where `L=max(size(m),size(n))`. This is a
finite aligned-pair alphabet, with missing high digits represented by `none`.
It is not concatenated `SmithEncoding.encodeInt` input, and this bound does not
include producing an aligned pair from signed/framed words.

The first pass emits difference bits with a Boolean borrow. The second pass
uses the final borrow to discard underflow results, or reverses the bits while
removing high zeros. The result is exactly the canonical binary word for
natural subtraction `m-n`, including empty zero. Both exhaustion tests, every
discarded bit, scratch cleanup and control reset are charged. `outputsInTime`
and `computableInPolyTime` use no arithmetic-cost or runtime premise.
`BinarySubtraction.subtract_identity` proves the exact positional borrow
invariant; `subtract_borrow` identifies the final bit with underflow.
`pushBit_encode` proves canonical normalization and `output_length_le` bounds
the output by the input length. The corresponding definitions and invariant
are in `BinarySubtraction.lean`.

This supplies the subtraction ingredient needed when signed addition combines
opposite signs. It is a component of the rational-arithmetic sentence of
`prop:regression-np-complete`, not a signed addition machine, the full verifier,
or an NP-membership result. The thesis commit and addendum hash above remain
unchanged; no mathematical discrepancy or thesis edit was needed. Next compose
sign/frame extraction, aligned magnitude addition/subtraction, sign selection,
zero normalization and serialization, then implement fraction addition and the
residual/loss traversal. The whole-input parser, end-to-end verifier runtime,
NP membership and hardness-encoding bridge remain separate obligations.

Validation: the full `lake build PhdThesisLean DiscreteMetricRegression` passes
(9,324 jobs). A separate type/axiom audit checks all 43 new explicit public
declarations and seven earlier verifier/certificate/hardness endpoints: 35
reports use only `propext`, `Classical.choice`, `Quot.sound` (or subsets), and
15 are axiom-free. The full build has 1,336 standard-only reports and 38
axiom-free reports. Its 555 warnings are in existing modules; the new modules
have none. Twelve named executions, including 1,025-bit operands, and all
4,225 pairs in `[0,64]^2` pass exact output, step count, scratch cleanup,
state reset, width and underflow checks. Three small actual-machine examples
on literal aligned inputs reduce in the kernel. All 194 project/adapter Lean
sources pass the prohibited-token scan. All ten dependency revisions and
tracked sources match their pins; toolchain and Lake configuration are unchanged.


### Signed addition and subtraction increment (10 November 2026)

`SignedAdditionBits.lean` and `SignedIntegerAddition.lean` close signed integer
addition and subtraction on the original Boolean input encoding. The public
endpoints are `SignedIntegerAddition.additionComputableInPolyTime` and
`subtractionComputableInPolyTime`. They use the same concrete machine with a
fixed Boolean parameter selecting whether to flip the second input sign.

The six stacks contain Boolean symbols; all registers are finite. The machine
parses both sign/length frames, compares magnitudes while retaining every bit,
restores the two operands, and runs addition for equal effective signs or
subtracts the smaller magnitude from the larger for unequal signs. The borrow
semantics reuse `BinarySubtraction`; addition uses the library's finite carry
step. Normalization removes only high zeros, counts retained digits on a stack,
and writes the sign and frame in exactly `SmithEncoding.encodeInt` format.
The sign is cleared on zero, including exact cancellation and subtraction of
zero. No magnitude or length is stored in an unbounded machine register.

For magnitude widths `u,v`, raw arithmetic bits `w=resultBits sub a b`, and
`z=value w`, `run` proves the exact transition count
`4(u+v)+2 max(u,v)+length(w)+size(z)+14`. `runtime_le` bounds it by `4L`, where
`L=2(u+v)+4` is the complete concatenated signed/framed Boolean input length.
`outputsInTime` includes all exhaustion transitions, empty scratch stacks and
reset finite control. `output_length_le` bounds the complete result by `L`.
`rawBits_value`, `signed_magnitude` and `operation_eq_signed` connect the bit
computation to integer addition/subtraction for all signs, zero, unequal widths
and arbitrary carry/borrow chains. The input contract is encoded integer pairs;
this does not claim to validate arbitrary malformed words.

**Thesis correspondence:** this proves the signed addition/subtraction part of
the rational-arithmetic sentence in `prop:regression-np-complete`, at the thesis
commit/hash recorded above. The specification and its mathematical claims are
unchanged. It is a machine component of that proposition, which remains Partial.
Fraction addition/subtraction, runtime-dimension parsing with bounded count
rejection, full residual/loss traversal and serialization, complete verifier
composition, NP membership and the binary-rational hardness bridge remain open.
Counting circuits, conditional transfers and sampling remain separate and
pending; no external SAT-counter hypothesis is used by this increment.

Validation: full `lake build PhdThesisLean DiscreteMetricRegression` passes
(9,327 jobs). The independent type/axiom audit checks 58 new explicit public
declarations and seven earlier verifier/certificate/hardness endpoints:
43 standard-only and 22 axiom-free reports. The full build has 1,361
standard-only and 38 axiom-free reports; 555 existing warnings, none in the
new modules. Sixteen named pairs are executed under both operation modes,
including 1,025-bit operands; all 8,450 operations on `[-32,32]^2` pass output,
exact transition count, `4L` bound, cleanup, reset and output-width checks.
Four small executions reduce in the kernel using literal step counts because
`Nat.size` does not reduce in those test expressions; the general exact-count
and bound theorems and all executable tests use the actual size formula.
All 197 project/adapter Lean sources pass the prohibited-token scan, and all
ten dependencies match their pins with clean tracked sources. Toolchain, Lake
configuration, adapters, sibling repositories and schedules are unchanged.
Failed intermediate diagnostics are excluded from the final evidence.


### Fraction addition and subtraction increment (11 November 2026)

`RationalAdditionRouting.lean` and `RationalAdditionMachine.lean` close addition
and subtraction on pairs of original Boolean `Fraction.encode` words. The
public endpoints are `RationalAddition.additionComputableInPolyTime` and
`subtractionComputableInPolyTime`. They return exactly the unreduced fraction
representation used by `RationalVerifierBounds`, without a gcd computation.

The machine copies the full source into a tagged pair. On the first copy it
computes both numerator cross-products and performs signed addition/subtraction;
on the second it routes the original fields, discards the numerators and
multiplies the denominators. Checked left/right pair adapters retain the other
component, then the existing assembler removes tags and the positive denominator
sign. Every arithmetic call, preservation and sequential/pair transfer is
charged by the existing finite-machine composition theorems. No supplied
arithmetic-cost or runtime assumption occurs; no tight composed degree is claimed.

`Copy.run` proves exactly `3L+3` steps in complete original input bits.
`Right.run` proves exactly `u+2v+2` steps for the tagged projection, bounded by
`2(u+v)+2`. Both include exhaustion, scratch cleanup and finite-control reset.
Their labels, state and alphabets are finite. `numerator_eq`, `denominator_eq`
and `assemble_operation` identify the precise stored output, and `value_correct`
proves its rational value. `output_length_le` separately bounds the complete
serialized result by `2L`. Unreduced fractions, all numerator signs, zero,
exact cancellation and unequal field widths are covered. The source contract
is a valid encoded fraction pair; arbitrary-word validation is not asserted.

**Thesis correspondence:** this closes fraction addition/subtraction in the
rational-arithmetic sentence of `prop:regression-np-complete`, at thesis commit
`c700eca04c2d8a819c0403252a97134475857038` and the unchanged addendum/agenda hashes
recorded above. No discrepancy or thesis edit was needed. Semantic attainment,
certificate size, component machine runtime, whole-verifier runtime and NP
results remain separate. The proposition remains Partial. Next implement the
runtime-dimension parser retaining source fields and rejecting oversized counts,
and the full residual/loss traversal and accumulation; compose these with the
completed arithmetic, norm and comparison machines. NP membership and the checked
binary-rational hardness bridge are still required. Counting circuits,
conditional transfers, sampling and their applications remain pending.

Validation: full `lake build PhdThesisLean DiscreteMetricRegression` passes
(9,329 jobs). Independent type/axiom checks cover all 41 new explicit public
declarations and seven earlier verifier/certificate/hardness endpoints:
39 standard-only and nine axiom-free reports. The full build has 1,370
standard-only and 38 axiom-free reports; 555 existing warnings, none in the
new modules. All 2,592 addition/subtraction operations on 1,296 fraction pairs
with numerators in `[-4,4]` and denominators in `[1,4]` pass; ten named pairs
also pass both modes, including 129-bit fields. The concrete phases execute
copying, all three products, signed arithmetic, projection and serialization;
composition proofs cover adapter transfers. Copy/projection checks include
exact steps, output, cleanup and reset, and all arithmetic checks include exact
output, rational value and the `2L` width bound. Five small copy/projection
executions also reduce in the kernel, including empty components. All 199
project/adapter Lean sources pass the prohibited-token scan. All ten dependency
revisions and tracked trees match their pins. Toolchain, Lake configuration,
adapters, siblings and schedules are unchanged. Failed intermediate diagnostics
are excluded from the final evidence.


### Repeated fraction summation increment (12 November 2026)

`RationalSumEncoding.lean`, `RationalSumMachine.lean` and `RationalSum.lean`
close runtime-length accumulation of binary fractions. The uniform finite TM2
returns exactly `xs.foldl Fraction.add z`, including its unreduced numerator and
denominator. `sumComputableInPolyTime` specializes to the existing evaluator's
`sum`, starting from zero. The input uses `Option Bool`: each original Boolean
fraction word is followed by one delimiter; the zero-initialized list includes
its fixed six-symbol prefix. This is an internal list encoding with a checked
round trip, not the original binary-counted regression record. Its full length
includes signs, frames, all bits, the initial fraction and every delimiter.

The controller scans the accumulator and next fraction, loads their concatenated
Boolean words into the existing checked addition machine, preserves the untouched
list tail on an external stack, collects the result and restores its delimiter
before continuing. `body_run` proves the embedded computation and preservation;
`iteration_cycle` charges both input scans, loading, the bounded
addition call and both return transfers. Its bound is
`P(u+v)+2(u+v)+2w+6`, where `u,v,w` are the complete operand/result lengths and
`P` is the existing actual addition-machine time polynomial. `exit_run` takes
`2u+3` transitions, including output, exhaustion, cleanup and control reset.
No unbounded register, supplied arithmetic-cost premise or uncharged call occurs.

`budget_step` proves that the sum of the accumulator's maximum field width and
all remaining source widths plus one per entry never increases. `prefix_bounded`
applies it to every accumulation prefix, even with unreduced denominators.
`budget_le_length` charges it to the original serialized input length `L`.
`run_bounded` and `time_eval` therefore give actual full execution time
`(L+1)*(P(8L+6)+24L+24)`; `output_length_le` bounds output length by `4L+3`.
This is a checked polynomial machine bound, with no tight degree claim.
Empty lists, zero, negative numerators, cancellation, repeated entries and
unequal widths are covered. Malformed-string rejection is outside this contract.

`lossOutputsInTime` returns the evaluator's exact stored loss fraction from its
already serialized list of norms. `loss_input_length_le` bounds that source by
`6+S*(4*Q+4)`, where `S` is original combined input/certificate length and
`Q=size(p)*(S+1)*(2S+1)+1`. `boundedLossOutputsInTime` composes this cubic with
the actual summation polynomial, assuming positive row count only for source
size charging. Computing residuals and producing the norm list are not charged
by this endpoint and remain to be implemented and composed.

**Thesis correspondence:** this completes repeated summation within the
rational-arithmetic sentence of `prop:regression-np-complete`, at thesis commit
`c700eca04c2d8a819c0403252a97134475857038`. Addendum SHA-256 remains
`25fa65a1b097da0b35a83074b9d4515d9a84aac7d4ea74dd45f267edee77b3c6`;
agenda SHA-256 remains
`9a1de32f9ee6c359fd92447f4492671f8a7dbbaac90b665b611223408a3b3768`.
There is no mathematical discrepancy or thesis change. This is a completed
machine component of a Partial proposition. Original-input/certificate parsing,
residual/product traversal, norm-list production and whole-verifier composition
remain open, followed by NP membership and the checked binary-rational hardness
bridge. Counting circuits, conditional transfer, sampling and applications
remain separate pending milestones.

Validation: full `lake build PhdThesisLean DiscreteMetricRegression` passes
(9,332 jobs). A separate type/axiom audit covers all 69 new explicit public
declarations and eight prior arithmetic/verifier/certificate/hardness endpoints:
74 standard-only and three axiom-free reports. Full-build reports are 1,377
standard-only and 38 axiom-free, with 551 existing warnings and none in the new
modules. Three literal controller executions reduce in the kernel: two-field
routing with tail preservation, empty-remainder output, and delimiter/result
restoration. Executable decoder/arithmetic/width checks pass 252 varying-list
cases and five named cases, including cancellation, 64 repeated zero fractions,
and 129-bit numerators. These checks do not execute the noncomputable composed
addition witness end to end; the embedded-machine and complete-loop proofs
establish that execution. All 202 project/adapter sources pass the prohibited-token
scan; all ten dependency pins and tracked trees are clean. Toolchain, Lake
configuration and adapters are unchanged. Failed intermediate diagnostics are
excluded from the final evidence.

No external SAT counter is used. Such a counter must remain an explicit theorem
hypothesis until its actual theorem, encoding, machine model, toolchain and axioms are compatible
and checked; assuming it will not verify an ETH refutation.


### Norm-list traversal and loss composition increment (13 November 2026)

`RationalNormListMachine.lean` and `RationalNormList.lean` close production of
all norms and their exact sum from a serialized runtime-length residual list.
`computableInPolyTime` maps `Fraction.norm p`; `sumComputableInPolyTime` then
composes it with the checked `RationalSum` machine. These are actual uniform
finite TM2 computations for each fixed prime, with no supplied arithmetic-cost
or runtime assumption. The source alphabet is `Option Bool`, retaining each
original `Fraction.encode` Boolean word and adding one delimiter per fraction.
Unlike the prior summation source, it has no initial accumulator. `encoding`
has a checked decoder round trip. The produced norm list includes the exact
six-symbol zero prefix expected by `RationalSum.listEncoding`.

The controller scans and loads each source word, embeds the existing norm
machine while preserving both the remaining tail and the accumulated output,
collects each result into a reversed output list and appends its delimiter.
After exhaustion it reverses that list once, emits the constant zero prefix,
clears scratch stacks and resets control. `body_run` proves preservation during
every embedded step. `iteration_cycle` charges `P(u)+2u+v+4`, with `u,v` the
complete source/result word lengths and `P` the previously checked norm-machine
time polynomial. `exit_run` charges `a+2` for an accumulated list of length `a`,
including empty input. The constant prefix is a fixed finite TM2 statement,
not a variable-length operation hidden in one transition.

`run_bounded` charges all later output reversal as well as each call.
`time_eval` gives `(L+1)*(P(L)+(8*size(p)+2)*L+20)` in full internal input length
`L`. `output_length_le` gives `(4*size(p)+8)*L+6` for the complete produced list.
No tight degree is claimed for the composed map/sum machine. Fractions may be
unreduced, signed or zero; empty lists, repeated fractions and unequal widths
are included. Order and observation multiplicities are preserved.

`map_residuals` identifies the produced list with `RationalVerifierBounds.losses`.
`lossOutputsInTime` returns its exact stored sum fraction; `loss_value_correct`
identifies its rational value with the thesis summed loss. The internal source
has length at most `S*(4*(S+1)*(2S+1)+4)`, where `S` is the original combined
input/certificate bit length. `boundedLossOutputsInTime` composes this bound
with the actual map/sum runtime, assuming positive row count only for that size
charging. It starts with serialized residuals: their generation, the original
binary-counted input/certificate parser, malformed-structure rejection and
final threshold assembly/comparison are not part of this endpoint. Existing
comparison machines still need composition with these phases.

Correspondence: this closes norm traversal and its summation composition in the
rational-arithmetic sentence of `prop:regression-np-complete`, checked against
thesis `c700eca04c2d8a819c0403252a97134475857038` and the unchanged addendum hash
above. The agenda hash is
`9a1de32f9ee6c359fd92447f4492671f8a7dbbaac90b665b611223408a3b3768`.
There is no mathematical discrepancy or thesis claim change. The proposition
remains Partial; semantic existence and certificate size remain complete,
whereas the whole verifier, NP membership, the hardness encoding bridge and
NP-completeness remain open. No external SAT-counter hypothesis is used.
Counting circuits, conditional transfers, approximation and applications remain
pending. Next implement the original bounded-count parser and residual-list
production, then compose the existing norm/sum phase and final comparison.

Validation: full `lake build PhdThesisLean DiscreteMetricRegression` passes
(9,335 jobs). Independent type/axiom audit covers all 52 new explicit public
declarations and nine prior endpoints: 57 standard-only and four axiom-free
reports. Full-build reports: 1,393 standard-only, 39 axiom-free and 551 existing
warnings, none new. Four literal controller executions reduce in the kernel
(scanning with tail/prefix retention, empty exit, returned-result delimiter,
and final reversal/prefix). Executable decoder, arithmetic-value, order/count
and width checks pass 1,080 varying-list/prime cases and 18 named/prime cases
at primes 2, 3 and 5, including unreduced fractions, repeated zeros, opposite
signs and 129-bit numerators. A rank-deficient design with conflicting repeated
rows has the checked expected loss. These examples do not execute the composed
noncomputable norm/summation witnesses end to end; the embedding, loop and
composition proofs establish that execution. All 205 project/adapter sources
pass the prohibited-token scan, all ten dependencies match pins with clean
tracked sources, and diff checks pass. Failed intermediate diagnostics are
excluded. Toolchain, Lake configuration, adapters, siblings and schedules are
unchanged. Remote CI is not claimed.


## Supporting-statement formalisations

These active-thesis statements are outside the headline catalogue. They are
recorded here once a statement-faithful Lean declaration exists.

| Thesis label | Status | Lean declaration or remaining work |
|---|---|---|
| `prop:chapter-residual-medoid` | Complete | `ResidualMedoid.exists_medoid_multiset` (nonempty finite multiset in `ℚ_[p]`; the minimiser of `∑_{r∈R}‖r-a‖` lies in `R`), with `exists_medoid` and `exists_medoid_finset` for indexed families. |
| `cor:chapter-monotone-update` | Complete | `ResidualMedoid.monotone_coordinate_update`: for the additive binary-tag model, an observed partial residual globally minimises the coordinate objective `F_j` and substituting it does not increase the full fitting objective (`loss_update_eq`). Rows and tags are arbitrary finite types; the current coefficient vector is arbitrary. |
| `thm:main` with `lem:toobig`, `lem:binary`, `lem:magnitude`, `lem:rounding` | Complete | `PublishedMaxCut.published_main`: the literal published `2`-adic reduction with uniform multiplicity `M = m + 1` over `ℚ_[2]`: `binary_lemma` (every prime), `loss_zero_eq`/`not_optimal_of_ge`, `not_optimal_of_norm_gt_one`, `rounding_le` (with the strict `rounding_lt` and `globalMin_boolean` as a bonus), `publishedLoss_embed` (`L(s) = Mn + m − cutsize(s)`), a Boolean optimum, `optimal_value` (`cutsize* = Mn + m − L*`), and `cut_ge_iff` (the `K`-decision form); `homogeneousLoss_publishedRows` identifies the objective with the explicit `{0,1}` instance of `m + 2Mn` rows. The theorem's NP-hardness claim is `FixedPrimeMaxCutMachine.encodedRegression_NPHard 2` (and its unary form), proved through the edge-streamed variant of the same Max-Cut reduction; as in the thesis's own proof scheme, hardness of the `p = 2` restriction is the content of the claim. |
| `lem:large-prime-unit-residuals` | Complete | `LargePrime.large_prime_unit_residuals`: with `ℋ = candidateFamily X y` (chosen rational interpolants of all affinely independent `(d+1)`-subsets, `d+1 = affineRank X`, degenerate data allowed via the rank-general `rank_refinement`), there is an explicit data-only bound `primeBound X y` such that for every larger prime the optimum is attained in `ℋ` and every residual of every member has `p`-adic norm `0` or `1`. `card_candidateFamily_le` gives `|ℋ| ≤ C(k, d+1)`. |
| `lem:large-prime-stability` | Complete | `LargePrime.large_prime_stability` and `large_prime_optimal_iff_most_contacts`: for primes above the bound, a member of `ℋ` is `q₁`-optimal iff `q₂`-optimal, and the optimal members are exactly those with the fewest misses (`loss_eq_missCount_of_large_prime`). |
| `poly-corollary` | Complete | `PolynomialCorollary.poly_corollary`: a degree-`≤ n` minimiser of `∑ |P(xᵢ) − yᵢ|_p` over data with at least `n+1` distinct abscissae interpolates at least `n+1` points. `poly_corollary_of_minimizes` drops the unused thesis hypotheses `k ≥ n+1` and `xᵢ = xⱼ ⇒ yᵢ = yⱼ`; `n = 0` is covered uniformly. |
| `poly-approxy` | Complete | `PolynomialCorollary.poly_approxy`: an optimal degree-`≤ n` `p`-adic approximant `Q` of `P` on a finite set of at least `n+1` points leaves a residual `P − Q` with at least `n+1` distinct rational zeros (`poly_approxy_filter` locates them inside the set). |
| `cor:residual-simple-roots` | Complete | `PolynomialCorollary.residual_simple_roots`: a polynomial residual of degree `n+1` (thesis definition `IsPolynomialResidual`, with the standing hypothesis of at least `n+1` evaluation points) has `Nodup` roots. |
| `cor:residual-rational-roots` | Complete | `PolynomialCorollary.residual_rational_roots`, `residual_splits`, `residual_roots_map`: a degree-`n+1` residual has exactly `n+1` distinct rational roots, factors into distinct linear factors over `ℚ`, and acquires no new roots in any field extension. |
| `thm:widespread-equioptimal` | Complete | `PolynomialCorollary.widespread_equioptimal`: for `n+1` points with pairwise `p`-adically equidistant abscissae (`c ≠ 0`) and an interpolant of degree exactly `n` (`1 ≤ n`), the degree-`≤ n−1` minimisers are exactly the `n+1` distinct candidates `P − a∏_{i≠j}(X − xᵢ)`, each missing exactly one point, all with loss `|a|_p cⁿ`. The hypotheses `1 ≤ n` and `c ≠ 0` are implicit in the thesis and made explicit. |
| `prop:3sat-hole-filling` | Complete | `ClauseErasure.clause_erasure`: for `p > 3`, filling the hole at `t_C` makes every clause well the constant `3` on Boolean inputs (`well_valueRange_embeddedBoolean`), the erased objective is the constant `αn + 3m` on `{0,1}^n`, and under the explicit domination hypothesis `4Δ < α` its global minimisers over `ℚ_[p]^n` are exactly the Boolean assignments. `well_at_mem`/`well_at_notMem`/`well_minimised_iff` are the well facts; `positiveLoss_globalMin_iff_maximizesSatisfied` is the positive-encoding analogue of `thm:3sat-clausewise`. |
| approximate negation (unlabelled lemma, `app:approximate-negation`) | Complete | `ClauseErasure.approximate_negation`: replacing negated-literal coefficients by integers `≡ −1 (mod p)` preserves the clause residual norm on Boolean-labelled inputs for `p > 3`; `pow_sub_one_modEq_neg_one` covers `p^k − 1`, and `modifiedClausewiseLoss_embeddedBoolean` transfers the identity to the compiled clause-wise objective. |
| sparse junta case (unlabelled corollary of `thm:sparse-medoid-representation`) | Complete | `SparseJunta.sparse_junta_case`: if `F(x) = H(x_T)` with `|T| ≤ s` and `H` non-expansive (`NonExpansive`, equivalent to the thesis valuation form by `nonExpansive_iff_val`), the medoid ensemble with constant active set `T` represents `F` exactly and every regressor uses only the features in `T`. |
| `prop:sudoku-locator-fingerprint` | Complete | `SudokuDiagnostics.locator_fingerprint` and `locator_fingerprint_prob`: over any finite field, a committed polynomial of degree `≤ D` different from the locator `Λ_x = ∏_{violated c}(Z − α_c)` agrees with it at most `D` points, so the uniform-sample collision probability is `≤ D/Q`; `locator_monic`, `natDegree_locator`, `roots_locator` record the locator's algebra. |
| `prop:sudoku-robust-decoding` | Complete | `SudokuDiagnostics.unique_nearest_dmin` and `separation_dmin`: under robust soundness `L(x) ≥ γ d_H(x, 𝒮)`, every `x` with `L(x) < γ d_min/2` has a unique nearest solution, and two low-loss assignments with different nearest solutions are at Hamming distance `≥ d_min − 2ℓ/γ`; the general forms take any pairwise lower bound `d` in place of `d_min`. |
| `lem:reg-finite-candidates` | Complete | `RegularisedCandidates.reg_finite_candidates`: for the six-point dataset at `p = 5` with per-point loss `2^{-v_5}` and slope penalty `λ 2^{-v_5(a)}`, every `λ ≥ 0` has an attained minimum, attained by a line through two distinct data points or a horizontal line through a data point; `not_fits_one_three` excludes the vertical pair and `nonvertical_pair_count = 14`, `distinct_horizontal_count = 4` check the thesis counts. Built on `weighted_exists_global_minimizer`, a weighted norm-monotone version of the finite-search theorem for arbitrary homogeneous designs. |
| `lem:row-swap-locality` | Complete | `RowSwapLocality.row_swap_locality` and `Hcb_swap_locality`: the change of the duplicated unit-scope objective under a within-row swap is exactly the change of the two column terms and the one or two box terms containing the swapped cells; `Hcb_swap_locality_of_box_eq` sharpens the shared-box case, and `H_eq_Hcb_of_rowsArePerms` records that row terms vanish on the row-permutation state space. |
| `lem:pow2-landscape` | Complete | `PowersOfTwoLandscape.pow2_landscape`: for odd `p`, `|2^a − 2^b|_p = |2^{|a−b|} − 1|_p`, a unit iff `ord_p(2) ∤ |a−b|`; every move is a unit step for `p ∈ {11,13,23,47,73,97}` (orders `10,12,11,23,9,48` by `decide`) and for `p > 255`; strict decrease iff `ε ≡ r (mod p^{v_p(r)+1})`; and `|r|_p < |ε|_p ⇒ |r − ε|_p = |ε|_p`. `seven_inversion` gives the `p = 7` example with exact values. |
| `prop:medoid-prefix-consensus` | Complete | `PrefixConsensus.prefix_consensus_identity` (`∑_j |c − z_j|_p = m − (1 − p⁻¹) ∑_{r≥1} p^{−(r−1)} #{j : z_j ≡ c mod p^r}`, with the series proved convergent) and `medoid_iff_maximises_score` (medoid argmin = weighted prefix-score argmax on any finite candidate set); `capped_medoid_iff_maximises_score` covers the implemented bounded medoid with non-integral predictions discarded as constants. |
| `prop:strict-refinement` | Complete | `StrictRefinement.valuation_sum_eq_valuation_head` and `valuation_sum_univ_eq_valuation_head`: nonzero coefficients with strictly increasing `p`-adic valuations have every tail sum of valuation equal to its first term; `tailSum_ne_zero` shows the tails are nonzero, and `norm_sum_eq_norm_head` is the norm form without a nonvanishing hypothesis. |

## The active thesis contains more than the headline catalogue

The active thesis checkout contains 54 theorem, corollary, proposition, or
lemma environments. The 24-row catalogue above intentionally records the main
mathematical contributions, not every supporting or applied statement.

Several of the additional environments already have Lean support even though
they do not have separate catalogue rows: the independent-contact refinement,
the coreset witness-point lemma, the 3-SAT row indicator, Boolean/domain
snapping, the all-different edge and unary identities, and the Sudoku
difference-indicator calculation. The supporting-statement table above records
the additional environments that now have their own statement-faithful
declarations.

Every theorem, corollary, proposition, or lemma environment of the active
thesis now has a corresponding Lean declaration, either in the headline
catalogue or in the supporting-statement table. The only remaining gaps are
the external complexity ingredient recorded in the Partial row, together
with the following items that are prose or data rather than stated results:
the APX-hardness discussion (left open by the thesis itself), the numerical
enumeration table of the six-point regularisation example, and the Sudoku
heuristic traces.

The separate question about how many distinct solutions occur along a
regularisation path remains an open research question in the thesis. It is not
counted as an unproved theorem because the thesis does not assert it as one.
