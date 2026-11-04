# Polynomial-bit-complexity Smith decomposition

The mathematical max-objective formula is already checked in
`PhdThesisLean/MaxObjectiveSmith.lean`. Its assumptions provide integral matrices
`U,U',V,V'`, `U' * U = 1`, `V * V' = 1`, and a rectangular matrix `U*A*V`
whose off-diagonal entries vanish. It does **not** compute those matrices. The
remaining target is a uniform polynomial-time algorithm, measured in encoded bits,
not a theorem assuming its own runtime witness.

Latest weekly human-literature review:
[30 October 2026 UTC](2026-10-30-literature-review.md). Ji's scope is unchanged;
the newer descriptive-complexity release and norm-oracle paper do not discharge
the rectangular Smith or encoded-machine obligations below.

## Output and input contracts

Return an executable finite record containing dimensions, `U,U',V,V',S`, with
`U*A*V=S`, integral inverse identities, and rectangular diagonality. For canonical
Smith form additionally require nonnegative diagonal entries, nonzero entries
before zero entries, and successive divisibility. Those stronger conditions are
useful for the standard Smith interface but are not needed by the existing
max-objective formula. Keep the weaker projection and the canonical result named
separately; do not claim the max formula assumes a divisibility chain.

Use decoder-checked finite Boolean encodings: signed binary integers (canonical
zero), framed row-major entries, and explicit dimension headers. A suitable first
interface uses unary dimensions and binary integer entries so each dimension is
bounded by actual source bit length `s`. Binary dimensions alone cause an edge
case: a `0 × 2^k` input has a short dimension header but a dense `2^k × 2^k`
identity transformation cannot be polynomial output. Either pay for dimensions
explicitly, or use compact transformation descriptions and prove their connection
to the matrix interface. State the choice before attempting a runtime theorem.
Preserve rectangular and empty cases. Do not generalize this encoding claim to
other matrix representations without efficient conversion proofs.

## Checked encoding increment (22 October 2026)

`PhdThesisLean.SmithEncoding.Dense` stores runtime dimensions and a row-major
`List ℤ` with length exactly `rows * cols`; `Dense.toMatrix` interprets it as
`Matrix (Fin rows) (Fin cols) ℤ`. No square or nonempty restriction is imposed.
`SmithEncoding.lean` reuses `LeanNPHardness.BinaryNatLists` framing and parsing
rather than implementing another generic binary-natural foundation.

The concrete format is `true^m, false, true^n, false`, then `m*n` signed fields.
Each field is a sign bit (`false` for nonnegative), followed by the library's
unary-length-framed standard binary encoding of its absolute value. Zero uses
positive sign and the empty binary magnitude. The structural parser checks both
entry count and exhaustion; the complete decoder re-encodes the parsed matrix
and rejects noncanonical strings, including negative zero. `decode_encode`
proves `decode (encode A) = some A`; `encode_of_decode` proves every accepted
string equals that canonical encoding. The exact cost is

```
m + n + 2 + sum_entries (2 * binaryLength(abs(z)) + 2).
```

`dimensions_le_length`, `cells_le_length` and
`accepted_dimensions_le_length` charge headers even for `0 × n` and `m × 0`.
`encode_length_le_of_entry_bits` gives the upper bound
`m + n + 2 + m*n*(2*b + 2)` when every entry's binary magnitude has length at
most `b`. This is a conditional serialization bound, not a global growth bound.
The same codec is available for each returned matrix; no combined decomposition
result, conversion machine, serializer runtime, or polynomial bound on its entries
is supplied by that increment. The output-contract portion of its next step
is addressed below; constructing a decomposition remains open.

## Supplied-output contract increment (23 October 2026)

`SmithDecomposition.Block m n` is a shape-checked view of the existing `Dense`
storage. `Result m n` stores `U,Uinv,V,Vinv,S`. The decidable `Valid` predicate
checks both integral inverse directions, `U*A*V=S`, and rectangular diagonality;
`check_eq_true_iff` specifies the executable checker exactly. `Canonical` adds
nonnegative diagonal entries, nonzeros before zeros, and consecutive divisibility,
with all diagonal conditions indexed by `Fin (min m n)` to preserve empty cases.
`Valid.maxHypotheses` supplies the weaker optimizer assumptions, and
`rhoMax_of_valid` derives the rational max formula for a valid supplied result.
Neither theorem computes that result.

Output serialization consists of five `BinaryNatLists.frame`-framed matrix
encodings in the fixed order `U,Uinv,V,Vinv,S`. Its exact length is twice the
sum of the five matrix encoding lengths plus five. When every stored entry's
binary magnitude length is at most `b`, `encode_length_le_of_entry_bits` gives

```
2 * (5*m + 5*n + 10 + (2*m*m + 2*n*n + m*n)*(2*b+2)) + 5.
```

`encode_length_le_of_input_bits` bounds this by `2*(5s+10+2s²*(2b+2))+5`
for actual input bit length `s`. These are conditional serialization bounds;
there is no proved polynomial bound on `b`, combined output decoder, serializer
machine, or runtime bound for the checker. The first algorithmic obligation is
still to construct a result satisfying `Valid` with controlled coefficient growth.
No paper-dependent algorithm was chosen in this interface increment. The latest
Smith-specific weekly human literature findings were unavailable in the saved
workspace; the first check was reportedly scheduled for 24 October Sydney.
This limits the source review and does not establish absence of external progress.

## Trace execution increment (25 October 2026, Australia/Sydney)

The first unfinished construction obligation is approached through an executable
trace interpreter, not a supplied final decomposition. `SmithTrace.Op m n`
contains distinct-row and distinct-column additions with integer multipliers.
`step` updates the current matrix and the relevant forward/inverse maps together;
row updates accumulate the inverse on the right, column updates on the left.
`run_invariant` proves all four integer inverse identities and `U*A*V=S` for
every finite trace. It has no nonempty, square, rank or determinant hypothesis.

`pack_matrix` proves that enumerating a matrix into the existing dense row-major
storage preserves every entry. `executeDense` accepts `SmithEncoding.Dense` and
returns a finite `Result` after executing the additional trace.
`execute_equivalence` proves its five algebraic identities;
`execute_valid_of_diagonal` yields `Valid` **only given diagonality of the computed
output**. No trace selection is provided. Kernel execution examples cover
noncommuting row and column updates, a rank-deficient rectangular matrix, and
both empty orientations with nontrivial updates to transformations.

The existing signed-binary/unary-dimension input and five-matrix output formats
are reused. Their bit-count theorems still apply, conditional on an entry-bit
bound; the trace is extra input with no claimed encoding, size or runtime bound.
There is no new growth theorem. Permutations, sign normalization and bounded
Bezout/pivot selection are not yet implemented in this interpreter. The next
construction step needs a computable pivot operation and a controlled-growth
selection invariant for singular rectangular inputs, including inverse widths.

Source comparison, accessed **25 October 2026 Australia/Sydney**: reused the
[24 October review](2026-10-24-literature-review.md) and inspected Ji's
[v2, §§4.1, 6.2, 7.3–7.4](https://arxiv.org/html/2607.22524v2), together with
[`Bounds.lean`](https://github.com/JJYYY-JJY/lean-normal-forms/blob/3f80f9524d88a124a49330eb36a2acb5ed41e179/NormalForms/Research/KannanBachem/Bounds.lean)
and [`PolynomialBounds.lean`](https://github.com/JJYYY-JJY/lean-normal-forms/blob/3f80f9524d88a124a49330eb36a2acb5ed41e179/NormalForms/Research/KannanBachem/PolynomialBounds.lean)
at commit `3f80f9524d88a124a49330eb36a2acb5ed41e179`.
The source endpoint requires nonzero determinant; inverse accumulation reverses
composition order. Its width recurrences use pivot-size descent and a determinant
width controlling recursive blocks. Our arbitrary rectangular traces have neither
invariant, so that bound cannot be transferred here. Structural operations and
serialization runtime remain excluded there. This is targeted source inspection,
not independent replay or axiom audit of the external artifact; its Lean 4.32.0
runtime was not installed. No code was copied. The original Kannan–Bachem full-text
access limitation in the weekly review remains; no new broad search is claimed.

## Proof sequence

### Two-row pivot increment (25 October 2026 UTC)

The first unfinished target is still an executable function
`decompose (A : SmithEncoding.Dense) : SmithDecomposition.Result A.rows A.cols`
with `∀ A, Valid A.toMatrix (decompose A)`, followed by the separate global
encoded-bit and uniform-runtime obligations. `SmithPivot.lean` advances its
local pivot component; it does not provide that function.

For arbitrary `State m n`, distinct `r,s : Fin m`, and `j : Fin n`, `gcdTrace`
computes a finite row-addition trace from the two current entries `a,b`.
One quotient subtraction and three additions implementing the signed swap
`(x,y) ↦ (y,-x)` give `(a,b) ↦ (b,-(a.tmod b))`, where the quotient is
`a.tdiv b` (truncated toward zero). The exact absolute remainder is
`a.natAbs % b.natAbs`; strict descent proves termination without a rank or
nonzero-pivot hypothesis. `gcdTrace_correct` proves the second selected entry
is zero, the first has magnitude `Int.gcd a b`, and every outside row is
unchanged. `gcdTrace_preserves_zero` preserves a column whenever both selected
rows were zero there. The sign of the resulting gcd pivot is unspecified.

`pivotDense` materializes all five matrices in the existing unary-dimension,
signed-binary storage. `pivotDense_correct`, `pivotDense_equivalence` and
`pivotDense_preserves_zero` prove the corresponding stored-output properties,
including both inverse directions and `U*A*V=S`. Indices are supplied finite
data; no index/trace codec or machine runtime is claimed. Existing complete
output-bit bounds remain conditional on the width of all five output matrices.
This primitive needs two distinct rows and a column; the eventual controller
must handle missing rows/columns, including empty inputs, without invoking it.
The existing unrestricted interpreter and storage contracts remain in force.

**Retired attempt:** nonnegative Euclidean remainder combined with the signed
swap is a poor complexity choice: `(-N,-(N-1))` goes to
`(-(N-1),-(N-2))` for `N ≥ 3`, admitting linearly many divisions in magnitude.
Truncation sends the same pair to `(-(N-1),1)` and then `(1,0)`. This algebraic
observation motivated the implementation change; only the truncating variant
is committed. The checked termination theorem is not a proved logarithmic
operation bound. No uncontrolled-growth pivoting scheme is promoted to a
polynomial-bit algorithm.

Reused the [24 October weekly review](2026-10-24-literature-review.md) and the
prior source comparison above, read on **25 October 2026 UTC**. Ji
[v2, Theorem 2.1 and §6.2](https://arxiv.org/html/2607.22524v2), accessed in the
recorded 24/25 October reviews, requires nonsingular square matrices and omits
structural machine costs. It does not supply this project's singular rectangular
growth invariant. No new external theorem or code is used, and no fresh broad
search, external replay or new source-access claim is made here. The existing
Kannan–Bachem full-text limitation remains. Local pinned Lean integer APIs supply
truncating division, absolute-value remainder and gcd identities. Read-only
inspection of the pinned `lean-np-hardness` binary arithmetic machines found no
signed binary division/gcd machine to reuse; its unary divisibility machinery
does not establish the required binary costs.

The next mathematical obstacle is a rectangular active-block controller and
controlled-growth invariant for both transformations and inverses. Pairwise
termination and preserved zeros alone do not bound growth over alternating
row/column pivots. Sign normalization, pivot divisibility/selection, full
diagonalization, global widths, machine costs and optimizer composition remain
separate open obligations.

### Active-column controller increment (27 October 2026 UTC)

The target remains `decompose A : Result A.rows A.cols` with
`∀ A, Valid A.toMatrix (decompose A)`, followed by separate polynomial encoded-bit
and uniform-machine proofs. `SmithColumn.lean` advances one controller pass.

`clearColumn Q k` internally enumerates exactly the rows `i.val > k`, computing
each pair pivot from the **updated** entries in column `k`. Its list recursion
and the existing truncating-division pivot are total. If either the kth row or
column is missing, it returns `Q`. No rank, square, nonzero-pivot or nonempty
hypothesis is imposed on this controller. `sweep_clears` proves every listed
nonpivot entry is zero afterward and every pre-existing nonpivot zero survives;
it even permits repeated target rows. `sweep_outside` fixes unselected rows.
`sweep_preserves_zero` preserves columns zero on the pivot and all targets.

The exact protected-prefix invariant is

```
(∀ i l, k ≤ i.val → l.val < k → Q.S i l = 0) →
  ∀ i l, (i.val < k ∨ l.val < k) → (clearColumn Q k).S i l = Q.S i l.
```

`clearColumn_next_zero` advances that zero lower-left block boundary to `k+1`:
all rows `i.val ≥ k+1` are zero in columns `l.val < k+1`. Entries above the
diagonal can remain, so this is a column-elimination invariant.

`clearColumnDense A k` materializes all five matrices using the existing dense
storage. The stored-output theorems prove clearing, that prefix invariant, both
integral inverse directions and `U*A*V=S`. For `A.cols ≤ 1`, the pass at zero
already returns `Valid` (`clearColumnDense_valid_of_cols_le_one`), including
zero-column inputs; this is the weak diagonal contract, not canonical Smith
normalization. General empty orientations also retain the no-op/equivalence
theorems. Kernel-checked specializations cover a 4-by-3 protected prefix with
successive pivots, the weak contract for a signed/initially-zero one-column
input, both empty orientations, `0 × 0`, and a missing diagonal position in a
nonempty rectangle. Separate evaluator regression checks return `[-3,0,0]`
from `[0,-30,21]` and leave an all-zero active column unchanged. Those evaluated
outputs are computational evidence; the universal theorems supply the proofs.

The input remains unary-dimension/signed-binary `Dense`, and the output remains
the five framed matrix encodings. `k` is supplied control data, without a new
index encoding or machine claim. The existing complete-output length bound is
still conditional on the entry width of **all five** matrices. Finitely many
pair calls and terminating division do not prove polynomial arithmetic counts,
global width or serialization time. A following column-operation pass can
reintroduce entries cleared here; a general alternating controller still needs
a progress measure and a controlled-growth invariant for both maps and inverses.
No full diagonalization, sign normalization, divisibility chain, global bound,
uniform machine or optimizer composition is supplied by this increment.

Source record: read the [24 October human-literature review](2026-10-24-literature-review.md)
and the recorded 25 October source comparison on **27 October 2026 UTC**.
Ji [v2, Theorem 2.1 and §6.2](https://arxiv.org/html/2607.22524v2), with artifact
[`3f80f9524d88a124a49330eb36a2acb5ed41e179`](https://github.com/JJYYY-JJY/lean-normal-forms/tree/3f80f9524d88a124a49330eb36a2acb5ed41e179),
was externally accessed in those 24/25 October records, not re-accessed today.
Its nonsingular-square arithmetic-trace hypotheses still do not supply the
singular/rectangular growth or structural TM2 invariants above. This controller
uses the already checked local pivot, without a new paper-dependent step or code
copying; no broad daily search, external replay or new literature finding is
claimed. The original Kannan–Bachem full-text access restriction remains a source
limitation, and the signed nonnegative-remainder approach remains retired.
Read-only inspection of pinned `lean-np-hardness` `FinEncoding` and
`BinaryArithmetic` reuses its existing encoding/machine boundary; its binary
successor, predecessor, comparison and addition machines do not supply signed
binary division/gcd or matrix-controller costs. No dependency changes are made.

### Divisibility-aware reduction increment (28 October 2026 UTC)

Question: can the existing pairwise gcd sweeps simply be alternated to isolate
each diagonal entry? **Retired approach:** unmodified alternating gcd pivots
can cycle even on a nonsingular 2-by-2 matrix. Kernel-checked examples in
`SmithReduction.lean` show the transformed matrix
`[[2,2],[0,2]]` becoming `[[2,0],[2,2]]` after a column-operation gcd pivot,
then returning to the original matrix after the corresponding row-operation
pivot. The accumulated transformations need not return; the cycle is in `S`.
Thus termination of each pairwise Euclidean pivot alone is insufficient for
termination of that alternating controller.

`reduceRows` instead tests whether the current pivot `a` divides target `b`.
If so it adds `-(b.tdiv a)` times the pivot row to the target row, fixing the
entire pivot row and clearing the target. This includes `(a,b)=(0,0)`; a zero
pivot with nonzero target goes through the existing terminating gcd branch.
`reduceRows_correct` proves target clearing, gcd magnitude and outside-row
preservation. `reduceRows_preserves_zero` retains common zero columns.
For **nonzero** `a`, `reduceRows_strict` proves strict `natAbs` descent when
`a` does not divide `b`; `reduceRows_progress` gives the alternative of a fixed
pivot row or strict descent. There is no claim that a zero pivot cannot increase.

`transposeState` exchanges the forward maps and inverses using transposition,
with `transposeState_invariant` proving both integral inverse directions and
`U*A*V=S` in the transposed shape. `reduceCols` reuses that construction rather
than a second Euclidean implementation. `reduceCols_clear_or_descend` proves
that a column reduction at a nonzero pivot either retains every zero in the
pivot column outside the pivot row or strictly decreases its magnitude. This
is the local progress invariant needed before assembling alternating passes;
it does not prove termination or growth for such a controller.

`reduceAtColumn` and `reduceAtRow` accept natural control indices and are no-ops
when the pivot/target is missing or equal. `reduceDense` materializes all five
matrices; `reduceDense_equivalence` proves their five integral identities for
both orientations without rank, square or nonempty hypotheses. Universal guards
and kernel-checked examples include both empty orientations, `0 × 0`, a missing
position, equal indices, negative exact division, a nondivisible pair and a zero
pivot. The cycle example also becomes weakly diagonal under exact division.
These specializations are proofs of finite cases, not evidence of an asymptotic
complexity bound.

Encoding remains the existing unary-dimension/signed-binary `Dense` input and
five framed dense output matrices, including both inverse matrices. The Boolean
orientation and two natural control indices are additional input, without a
new control codec or machine claim. The existing output-bit bound is still
conditional on the entry width of **all five** matrices. Strict descent in
numeric magnitude is not a polynomial bit-cost bound: it supplies neither a
logarithmic descent count nor bounds on the other entries or transformations.

Source record: read the [24 October human-literature review](2026-10-24-literature-review.md)
and the recorded 25 October comparison on **28 October 2026 UTC**. Ji
[v2, Theorem 2.1 and §6.2](https://arxiv.org/html/2607.22524v2), with artifact
[`3f80f9524d88a124a49330eb36a2acb5ed41e179`](https://github.com/JJYYY-JJY/lean-normal-forms/tree/3f80f9524d88a124a49330eb36a2acb5ed41e179),
was externally accessed in the 24/25 October records, not re-accessed today.
Its nonsingular-square arithmetic-trace hypotheses still do not supply our
singular/rectangular global-growth or structural TM2 obligations. This increment
uses only the existing local pivot and pinned integer/matrix APIs; it is not
derived from a newly inspected external theorem or copied code. No broad daily
search, external replay or fresh source-access claim is made. The original
Kannan–Bachem full-text restriction remains a source limitation. Read-only
inspection of pinned `lean-np-hardness` `FinEncoding` and `BinaryArithmetic`
confirmed the existing binary successor, predecessor, comparison and addition
machines, without a signed binary division/gcd machine to discharge these costs.
No dependencies or pins changed.

Validation/research log: sourced the prepared environment and ran
`python3 /workspace/shared/theorem-provers/check.py` successfully; verified the
clean authorized origin and ancestry, preserved generated `work`, and created
tracking `main` at `8ef42f0`. The saved Start skill was absent from exposed
`.agents` and executor skills; shared `START.md` and repository `AGENTS.md` were
read. Guarded `lake env lean PhdThesisLean/SmithReduction.lean`,
`lake build PhdThesisLean.SmithReduction` and `lake build` passed (the full build
completed 9290 jobs). The source scan found no proof placeholders, unsafe code
or project axiom declarations; the recorded pin hashes stayed identical.
Twenty new `#print axioms` checks, plus `MaxObjectiveSmith.rhoMax_rational_smith`
and `SmithDecomposition.rhoMax_of_valid`, use only `propext`, `Classical.choice`,
`Quot.sound` or subsets. Early proof-script failures concerned a simplification/equality
orientation and a nested finite example, and were repaired; no mathematical
assumption was added. Resource-guarded commands use the prepared Lean 4.35.0
runtime with two threads, without installation or cache changes.

Next: assemble active-block passes using the exact-division branch and lift
the fixed-column/strict-descent alternative across a finite sweep, handling
zero pivots explicitly before claiming an alternating controller terminates.
Controlled global growth of `S,U,Uinv,V,Vinv`, polynomial operation counts,
uniform encoded machines and optimizer composition remain open. The headline
`thm:max-polytime` remains partial.

### Remaining construction sequence

1. Establish elementary operations over **integers**, with explicit inverse
   transformations and local growth bounds. `SmithRowOperations.lean` is the first
   increment: reversible row addition, equality with mathlib transvection
   multiplication, `natAbs ≤ (C+1)*H`, and the power-of-two bound
   `natAbs ≤ 2^(a+b+1)`. It has no operation-count or machine-runtime theorem.
   `SmithTrace.lean` now connects row/column additions to a finite transformation
   trace preserving `U*A*V=S` and both inverse identities, with dense output.
   `SmithPivot.lean` adds a signed swap and terminating pairwise gcd pivot;
   sign normalization and controlled active-block selection remain to connect.
2. Select and cite a controlled-coefficient polynomial Smith algorithm, such as
   the Kannan–Bachem route already cited by the thesis. Inspect the primary
   algorithm before fixing invariants. The [24 October literature baseline](2026-10-24-literature-review.md)
   identifies Ji's existing Lean Kannan–Bachem artifact as a priority comparison:
   inspect its growth recurrences and inverse accumulation, while retaining our
   singular/rectangular cases and full structural TM2 costs. Its stated theorem
   covers nonsingular square inputs and arithmetic traces only.
   Existence of Smith form over a PID or
   termination of naive Euclidean pivoting does not provide this complexity bound.
   Mathlib's field-valued transvection diagonalization is not an integer
   unimodular replacement.
3. Formalize executable pivot/gcd/divisibility steps and an invariant proving
   termination, integral equivalence, and the required normal form. Prove the
   global coefficient-growth invariant: the local row bound by itself can
   compound exponentially when repeated, so it is insufficient.
4. Prove polynomial operation count, polynomial intermediate binary lengths, and
   bounds for transformation matrices **and inverses**, not only `S`. Supply
   finite-machine costs for signed binary arithmetic, gcd/division, indexing,
   copying and serialization. Compose to one `TM2ComputableInPolyTime` witness
   uniform over all runtime dimensions, with no unit-cost integer arithmetic.
5. Instantiate the checked max-objective formula. Include rational denominator
   clearing and its output-bit cost, rational optimizer serialization, the cost of
   `U*b`, and prime/valuation/threshold handling under the thesis's actual input
   model. Specify fixed-prime versus prime-as-input costs explicitly. A polynomial
   decomposition alone does not automatically finish these remaining adapters.

No canonical-library upgrade or duplicated complexity core is part of this queue.
The separate Complexitylib adapter is coordinated independently.

## Exact daily research prompt

> Work in phd-thesis-lean on the missing polynomial-bit-complexity Smith
> decomposition ingredient of thm:max-polytime. Read repository instructions,
> TODO.md, docs/smith-complexity-plan.md and THEOREM_STATUS.md; inspect current
> HEAD/status and preserve unrelated work. Bootstrap the repository's pinned
> stable Lean/mathlib environment using docs/cloud-bootstrap.md; check disk and
> resources before builds. Review the latest weekly human literature findings
> as required by TODO.md before choosing research. Begin with the first unfinished
> proof-plan obligation, state its exact theorem, computational encoding and
> unresolved invariant, and
> make a bounded serious attempt at one coherent increment. Preserve integer
> unimodularity, rectangular/empty cases, and actual binary input/output costs.
> Keep local arithmetic, algorithm correctness, global growth bounds and uniform
> machine runtime as separate claims. Build changed modules and the library,
> audit headline declarations, update status and commit/push verified increments
> to the existing authorized origin. Do not reopen the completed all-different
> CSP queue, duplicate the Complexitylib adapter, upgrade pins, change schedules,
> publish environment configuration, or count routine maintenance as mathematics.
> Report exact verified progress, failed approaches and the next unresolved step;
> an inconclusive run is acceptable.

## Stopping criteria

- Stop an increment at one coherent proved invariant or interface with successful
  builds and explicit axiom audits. No `sorry`, project axioms or assumed runtime
  evidence may be hidden in a completed claim.
- If the selected algorithm's global growth invariant is unresolved, record the
  obstacle rather than promoting local bounds or scalar-operation counts to a
  polynomial-bit theorem. Do not fill an inconclusive run with certificate churn.
- Stop commands at bootstrap disk/memory/time guards, pin drift, unexpected remote
  identity, conflicting work, or unsupported required setup. Report the exact
  command and blocker. Do not delete unrelated caches or force a build into the
  roughly 3 GiB remaining in the current validation worker.
- Mark `thm:max-polytime` complete only after a concrete uniform machine,
  encoded-bit polynomial bound, total correctness and the final max-objective
  composition all build and pass axiom audits.

## Research log — 30 October 2026 (Australia/Sydney)

**Question and exact obligation.** The first unfinished construction target is
still a computable `decompose (A : Dense) : Result A.rows A.cols` with
`∀ A, Valid A.toMatrix (decompose A)`. Can the pairwise fixed-pivot/strict-descent
alternative now be lifted across complete active sweeps? The unresolved
controller invariant must survive *later* pair reductions, rather than just
establishing progress at one intermediate matrix. Controlled global growth of
all five matrices is a further, separate unresolved invariant.

**Checked increment.** `SmithSweep.lean` computes `sweepRows` with the existing
divisibility-aware pair reduction and quotients from the updated entries.
`sweepRows_nonzero_le` proves that a nonzero pivot stays nonzero and never grows
in magnitude. Thus later operations cannot undo an earlier strict decrease.
`sweepRows_progress` proves that the whole pivot row is fixed or its magnitude
strictly decreases. Visited nonpivot entries and pre-existing zeros are cleared
and remain clear, including with repeated targets; outside rows and common
zero columns are preserved.

`cross Q k` computes an active-column sweep followed by the transposed
active-row sweep, reusing `SmithColumn.activeRows`. For `r = ⟨k, hr⟩`,
`c = ⟨k, hc⟩`, `P = cross Q k`, the exact new controller theorem is

```
Q.S r c ≠ 0 →
  ((∀ i, k < i.val → P.S i c = 0) ∧
   (∀ j, k < j.val → P.S r j = 0)) ∨
  (P.S r c).natAbs < (Q.S r c).natAbs.
```

`cross_isolated_or_descend` proves this without square, rank or determinant
hypotheses. `cross_nonzero_le` retains nonzeroness and nonincrease.
`cross_prefix` fixes every earlier row or column provided both zero blocks
between the protected prefix and active block were zero. That preservation
does not require a nonzero pivot. Missing diagonal positions are no-ops,
including both empty orientations. `crossDense_equivalence` materializes all
five outputs and proves both integral inverse directions and `U*A*V=S`;
`crossDense_isolated_or_descend` and `crossDense_prefix` apply to those outputs.

The encoding remains unary dimension headers and signed binary row-major
entries, with all five framed dense output matrices, including both inverses.
`k` is additional control data, without a new codec or machine-cost claim.
The existing complete-output bit bound remains conditional on *all five*
matrices' entry widths. Numeric descent alone is not a polynomial bound in
binary input length. There is no recursive diagonalizer, global coefficient
bound, operation-count theorem, uniform machine or optimizer composition here.
Zero pivots are processed by the total passes but excluded from the nonzero
progress theorem; the checked `1 × 2` specialization `[0,6]` becomes `[6,0]`.

**Sources and reuse.** Read the latest [24 October human-literature review](2026-10-24-literature-review.md)
and its recorded 25 October source comparison before selecting this increment.
Ji [v2, Theorem 2.1 and §6.2](https://arxiv.org/html/2607.22524v2), with artifact
[`3f80f9524d88a124a49330eb36a2acb5ed41e179`](https://github.com/JJYYY-JJY/lean-normal-forms/tree/3f80f9524d88a124a49330eb36a2acb5ed41e179),
was externally accessed in the 24/25 October records, not re-accessed today.
Its nonsingular-square arithmetic-trace theorem does not supply our rectangular
global-growth invariant or structural TM2 costs. No new external theorem or
code is used, external artifact replayed, or broad daily search claimed. The
original Kannan–Bachem publisher full-text restriction remains a source limit.
The signed nonnegative-remainder variant and unmodified alternating gcd sweeps
remain retired. Read-only inspection of the pinned `lean-np-hardness`
`FinEncoding`, `BinaryNatLists` and `BinaryArithmetic` APIs confirmed existing
framing and binary successor/predecessor/comparison/addition machines; none
supplies the signed binary division/gcd or matrix-controller cost obligation.
No generic encoding or machine foundations were duplicated.

**Attempts and validation.** Verified the selected published environment source
version, clean authorized origin and fetched ancestry; preserved generated
`work`, then created tracking `main` at `d9e3a29`. No other Lean worker was
running. The saved Start skill was absent from exposed skill locations and the
executor catalog; shared `START.md` and repository `AGENTS.md` were read.
Sourced `/workspace/shared/theorem-provers/env.sh`; the required
`python3 /workspace/shared/theorem-provers/check.py` passed with exact runtime,
pins, dependency HEADs and imports, without installation. Used `prepare.py`'s
resource-guarded runner with two threads, the existing cache and unchanged
limits. The general proofs checked on the first attempt; subsequent finite
examples needed explicit row-list/Euclidean unfolding and the repository's
existing `backward.isDefEq.respectTransparency=false` elaboration setting.
Those proof-script repairs added no mathematical assumptions.

`lake env lean -Dbackward.isDefEq.respectTransparency=false PhdThesisLean/SmithSweep.lean`,
`lake build PhdThesisLean.SmithSweep`, and `lake build` passed; the final library
build completed 9292 jobs. Thirty new `#print axioms` checks and the existing
`MaxObjectiveSmith.rhoMax_rational_smith` / `SmithDecomposition.rhoMax_of_valid`
use only `propext`, `Classical.choice`, `Quot.sound` or subsets. Kernel-checked
examples cover negative exact division with repeated targets, a protected
prefix in a rectangle, a zero pivot, both empty orientations,
`0 × 0` and a missing position. Separate guarded evaluator outputs show
`[[6,4,0],[0,6,0]]` becoming `[[-2,0,0],[6,-18,0]]` after one pass and
`[[-2,0,0],[0,-18,0]]` after two; these are regression evidence, not a universal
two-pass theorem or an asymptotic bound. Source scanning found no proof
placeholders, unsafe code or project axiom declarations; recorded pin hashes
remain identical.

**Next.** Define a recursive active-pivot isolator from the checked alternative,
with explicit zero-pivot seeding/block selection and protected-prefix induction,
then connect active-block recursion to `Valid`. Before claiming polynomial bit
complexity, still establish a suitable global growth invariant for
`S,U,Uinv,V,Vinv`, polynomial operation counts, concrete binary arithmetic and
structural machines, and final optimizer composition. `thm:max-polytime` remains
partial. This run stops at the audited finite-pass invariant.

### Recursive single-position isolation (30 October 2026 UTC)

**Question and exact obligation.** The first unfinished construction target
remains `decompose A : Result A.rows A.cols` with
`∀ A, Valid A.toMatrix (decompose A)`. The next coherent component now checked
in `SmithIsolation.lean` is the total function `isolate Q k`. For arbitrary
runtime rectangular dimensions and `hr : k < m`, `hc : k < n`, its exact
isolation theorem is

```
Isolated (isolate Q k) k hr hc
```

where `Isolated P k hr hc` means
`(∀ i, k < i.val → P.S i ⟨k,hc⟩ = 0) ∧
 (∀ j, k < j.val → P.S ⟨k,hr⟩ j = 0)`.
There is no nonzero, square, rank or determinant hypothesis.

**Zero handling and termination.** `sweepRows_eq_of_zero` proves that if the
resulting pivot of a finite row sweep is zero, the entire state is unchanged,
including both maps and both inverses. Its proof uses the pair's gcd identity:
a zero gcd forces both input entries to be zero, so exact division has multiplier
zero. Thus `cross_isolated_of_zero` proves that a seeding pair of passes whose
resulting pivot is zero already has both active arms clear. Otherwise the result
enters `isolateNonzero`, which repeats the existing `cross` until the decidable
arm test succeeds. Every recursive call strictly reduces the **numeric** pivot
magnitude by `cross_isolated_or_descend`; `cross_nonzero_le` keeps it nonzero.
The initial seeding pass is outside that descent claim and can increase a zero
pivot. No new nonzero-entry search is necessary for this weak contract: an
isolated zero may precede a nonzero trailing block. Canonical zero ordering
remains a separate problem.

**Preserved invariants and encoding.** `isolate_invariant` retains both integral
inverse directions and `U*A*V=S`. `isolate_prefix` fixes every earlier row or
column under the two prior zero-block hypotheses. `isolate_next_zero` advances
both boundaries to `k+1`, including when the isolated pivot is zero. Missing
positions return the original state (`isolate_of_missing`), covering `0 × n`,
`m × 0` and `0 × 0`. `isolateDense` packs all five computed matrices into the
existing unary-dimension/signed-binary row-major format; its equivalence,
isolation and prefix theorems refer to that stored output. The natural control
index is still additional input with no new codec or machine claim. Existing
complete-output bit bounds remain conditional on the entry width of **all five**
matrices. Numeric descent gives termination, not a polynomial bound in binary
input length, intermediate widths, arithmetic cost or structural machine steps.

**Sources and reuse.** Before choosing work, searched the current repository
for newer literature reviews; the latest remains the
[24 October human-authored-research review](2026-10-24-literature-review.md).
Read it and the recorded 25 October comparison on **30 October 2026 UTC**.
Ji [v2, Theorem 2.1 and §6.2](https://arxiv.org/html/2607.22524v2), artifact
[`3f80f9524d88a124a49330eb36a2acb5ed41e179`](https://github.com/JJYYY-JJY/lean-normal-forms/tree/3f80f9524d88a124a49330eb36a2acb5ed41e179),
was externally accessed in the 24/25 October source records, not re-accessed
today. Its nonsingular-square arithmetic-trace result still lacks our
rectangular/global-growth and uniform-machine scope. This increment depends
only on the existing checked local reductions and sweeps, without a new external
theorem or copied code. No broad daily literature search, external replay or
fresh source-access claim is made. The Kannan–Bachem publisher full-text access
limitation remains. The signed nonnegative-remainder and unmodified alternating
gcd-sweep approaches stay retired. Read-only inspection of pinned
`lean-np-hardness` `FinEncoding`, `BinaryNatLists` and `BinaryArithmetic`
reconfirmed existing codecs and binary successor/predecessor/comparison/addition
machines; they do not provide signed division/gcd or matrix-controller costs.
No generic foundation, dependency or pin was changed.

**Attempts and checked evidence.** Verified the selected published source version
and clean authorized origin, fetched `main` at `d702a27`, checked ancestry and
preserved generated `work` while creating tracking `main`. No overlapping Lean
worker was running. The saved Start skill is still absent from the exposed
executor catalog and `.agents` skill locations; used repository `AGENTS.md` and
shared `START.md`. Sourced the published environment; required `check.py` passed
for exact toolchains, pins, dependency sources and imports, without installation.
Used the unchanged resource-guarded runner and two threads. Early proof scripts
needed conditional reduction in the hypothesis, explicit zero-update function
equalities and an explicit `Fin.val = k` goal; these were elaboration repairs,
not additional assumptions or a repeated failed mathematical approach.

Targeted `lake build PhdThesisLean.SmithIsolation` and full
`lake build PhdThesisLean DiscreteMetricRegression` passed (9297 full-build jobs).
An import/type/axiom audit of eighteen new declarations plus
`MaxObjectiveSmith.rhoMax_rational_smith` and `SmithDecomposition.rhoMax_of_valid`
passed with only `propext`, `Classical.choice`, `Quot.sound` or subsets.
Kernel-checked specializations cover protected prefixes, an initially zero pivot,
both empty orientations, `0 × 0` and a missing position. Guarded evaluator
regressions show multi-pass isolation of `[[6,4,0],[0,6,0]]` to
`[[-2,0,0],[0,-18,0]]`, row and column seeding of zero pivots, and an isolated
zero with trailing entry `5`. Those outputs are computation evidence; the
universal theorems prove the claims. A comment/string-aware scan of 167
project/adapter Lean files found no prohibited proof placeholders, axiom
declarations, unsafe code or `native_decide`; recorded pin hashes and all
dependency HEADs/clean tracked sources were unchanged. `git diff --check` passed.
Detailed build, audit and scan evidence is in the ignored
`.research/smith-isolation-2026-10-30/` directory.

**Next unresolved step.** Recurse over all diagonal positions, using
`isolate_next_zero` and prefix preservation to prove rectangular diagonality
and return `Valid` for every input. That will still be correctness of a weak
diagonalizer, not a polynomial-bit Smith result. Global bounds for
`S,U,Uinv,V,Vinv`, bit-polynomial operation counts, concrete binary arithmetic
and structural machines, and optimizer composition remain separate obligations.
`thm:max-polytime` stays Partial. This run stops at audited single-position
isolation rather than starting another research increment.

### Full weak diagonal decomposition (31 October 2026 UTC)

**Checked increment.** The first unfinished construction obligation is now
proved exactly:

```lean
decompose (A : SmithEncoding.Dense) : SmithDecomposition.Result A.rows A.cols
decompose_valid (A : SmithEncoding.Dense) :
  SmithDecomposition.Valid A.toMatrix (decompose A)
```

Both declarations are in `PhdThesisLean.SmithDiagonalization`. This is the weak
integer diagonal contract consumed by the optimizer, without canonical signs,
zero ordering or successive divisibility. The function takes the input alone;
there is no supplied trace, decomposition, nonzero-pivot witness or assumed
runtime witness. It covers arbitrary singular/rectangular matrices and empty
orientations. All five matrices are materialized, including integral inverses
in both directions.

**Invariant and proof.** `Prefix Q k` says every off-diagonal entry touching a
row or column strictly before `k` is zero. This includes the completed diagonal
block as well as both zero-block boundaries; the boundaries alone would not
state that earlier diagonal positions were completed. `isolate_prefix_succ`
combines the existing protected-prefix theorem and advancement of both block
boundaries. The new `finish Q k` recurses on `min m n - k`, using the existing
terminating isolation at each available position. `finish_invariant` retains
`Uinv*U=U*Uinv=1`, `V*Vinv=Vinv*V=1` and `U*A*V=S`. `finish_diagonal` concludes
that every off-diagonal entry is zero when all available positions are done.
Packing the final state therefore yields `decompose_valid` and
`decompose_check`. `finish_of_done` and `decompose_of_empty` retain the complete
initial state when the rectangular diagonal is empty. A zero diagonal entry
may still precede a nonzero entry; that is permitted by `Valid`.

**Encoding and limits.** Input is still the checked unary-dimension,
row-major signed-binary `Dense` encoding. Output is still the five framed dense
matrices, charging signs, dimensions, all four transformations and their entries.
There is no extra control-index input to `decompose`. The existing full-output
bound `2*(5s+10+2s²*(2b+2))+5` remains conditional on a common bit-width bound
`b` for all entries. No polynomial bound on `b` is proved, and this terminating
algorithm is not asserted to have controlled growth. The outer dimension
recursion does not bound the inner numeric-magnitude descent, intermediate
coefficients, arithmetic operations, parsing, traversal or serialization.
There is no uniform machine or final optimizer composition. Consequently
`thm:max-polytime` remains Partial.

**Literature and reuse.** Read the newer
[30 October weekly review](2026-10-30-literature-review.md) before choosing work
on **31 October 2026 UTC**; it supersedes the 24 October review as the current
checkpoint. Reuse its source inspection and versions/access dates, without a
new external access or broad daily search. Ji
[v2, Theorem 2.1 and §6.2](https://arxiv.org/html/2607.22524v2)
(1 August 2026), artifact
[`3f80f9524d88a124a49330eb36a2acb5ed41e179`](https://github.com/JJYYY-JJY/lean-normal-forms/tree/3f80f9524d88a124a49330eb36a2acb5ed41e179),
was re-accessed **30 October** by that review. Its explicit `hdet : A.det ≠ 0`
and square input are stronger assumptions than our arbitrary rectangular,
possibly singular input, and its arithmetic-trace bound excludes structural
machine costs. The review classifies that evidence as source inspection, not
independent replay or axiom audit. The review's descriptive-complexity v1.4.0
artifact and norm-oracle preprint likewise supply no Smith runtime theorem.
The Kannan–Bachem full-text access gap remains. This increment uses only the
existing isolation theorems, with no copied external proof or new dependency.
The signed nonnegative-remainder and unmodified alternating gcd-sweep
approaches remain retired. Read-only inspection of pinned `lean-np-hardness`
`FinEncoding`, `BinaryNatLists` and `BinaryArithmetic` confirms the reusable
binary codecs and finite-machine addition interface; it provides no global
matrix-growth invariant or general signed division/gcd controller here.

**Validation and attempt record.** Read repository `AGENTS.md` and the saved
shared `START.md`; no separately exposed Start skill was found. Sourced
`/workspace/shared/theorem-provers/env.sh` and passed the required `check.py`
before any proof command; no installation was needed. Verified the clean
`solresol/phd-thesis-lean` origin, fetched `b812845`, preserved generated `work`
and created tracking `main` after verifying identical ancestry. Refreshed pins
still matched the prepared receipt. The runtime status exposes a `cecfg`
identifier different from the parent's supplied `asenvcfg` identifier; no
identity equivalence is inferred. The exact runtime/toolchain/pin/artifact
checks passed, without configuration changes.

The first elaboration failed only when rewriting an ordinary conditional in a
dependent-conditional goal in `finish_of_done`. Explicit case splitting repaired
it; failed output containing elaborator-generated placeholders is not accepted
proof evidence. The final guarded target build passed (3,202 jobs) and full
`lake build PhdThesisLean DiscreteMetricRegression` passed (9,300 jobs), with
two threads, the existing cache and unchanged resource guards. A separate
import/type/axiom audit covers all eleven new declarations and the existing
`MaxObjectiveSmith.rhoMax_rational_smith` and `SmithDecomposition.rhoMax_of_valid`.
Only `propext`, `Classical.choice`, `Quot.sound` or subsets occur. Kernel-checked
specializations cover rectangular, negative/rank-deficient and empty inputs;
guarded evaluations separately check multi-pass output, a zero diagonal before
a nonzero one, and supplied-output checker acceptance. These computations are
regression evidence, not the universal proof or a complexity bound. Build/audit
and source-scan evidence is retained under ignored
`.research/smith-diagonalization-2026-10-31/`.

The comment/string-aware scan of 170 project/adapter Lean files found no
prohibited tokens. All 1,215 axiom reports in the full build likewise use only
the three standard axioms above or subsets. Build logs replay existing module
and deprecation warnings (22 in the target closure, 551 in the full library);
the new module and separate final audit have no warnings or errors. The exact
prepared pin hashes, all dependency HEADs and clean tracked dependency sources
were rechecked. `git diff --check` passed.

**Next unresolved step.** Establish a controlled-growth algorithm/invariant for
all five matrices, including inverse widths, and bit-polynomial operation
counts; the current naive recursion has no such guarantee. Compare the
rectangular/singular hypotheses before transferring any Kannan–Bachem bound.
Then implement the actual signed-binary arithmetic and structural machines and
compose the optimizer with denominator clearing and residual evaluation costs.
This run stops at the audited total-correctness increment.

### Binary descent for one isolation (1 November 2026 UTC)

**Question and chosen subobligation.** Can the numeric descent of the existing
weak diagonalizer be sharpened to a bit-length bound before attempting a global
growth proof? The first unfinished obligation remains a controlled-growth
algorithm, not mere existence of diagonal form. The bounded increment here is
the semantic sweep-pair count for one call of its already checked isolator:

```lean
isolationPasses_le_input_length (A : SmithEncoding.Dense) (k : ℕ) :
  isolationPasses (SmithTrace.initial A.toMatrix) k ≤
    (SmithEncoding.encode A).length + 1

isolate_eq_bounded_crosses (A : SmithEncoding.Dense) (k : ℕ) :
  ∃ count ≤ (SmithEncoding.encode A).length + 1,
    crosses (SmithTrace.initial A.toMatrix) k count =
      SmithIsolation.isolate (SmithTrace.initial A.toMatrix) k
```

The namespace is `PhdThesisLean.SmithIsolationCount`. The counter follows the
existing branches; replay equality covers the entire five-matrix state. A
semantic transition has no assigned arithmetic, evaluation or machine cost.

**Proof and encoding.** Each selected gcd divides the incoming pivot magnitude;
this composes across both sweeps. Strict descent therefore implies
`2*new ≤ old` (`cross_failure_halves`) and strict binary-size descent
(`cross_failure_size`). `nonzeroPasses_le_size` counts at most one pair per
incoming pivot bit, including the successful pair. For zero seeding,
`cross_pivot_le` bounds the seed by the incoming matrix height: a column sweep
ending in zero was entirely idle, while a nonzero result cannot grow during
the row sweep. The dependency's `BinaryNatLists.encodeNat_length_eq_size`
and new `entry_size_le_input_length` charge pivot bits to the exact encoding.
The extra one pays for seeding; missing positions take zero pairs.

The existing unary-dimension/signed-binary dense input and five framed output
matrices retain signs, canonical zero, framing, empty-dimension costs and both
integer inverses. Supplied `k` has no new codec. There are no square, rank or
nonzero initial-pivot hypotheses; exact replay preserves integral equivalence.

**Unresolved invariant.** Later diagonal stages receive transformed matrices;
their encoded lengths have no proved polynomial bound in the original input.
Repeated local row-addition bounds compound their factors. Pivot halving alone
bounds neither the other entries of `S,U,Uinv,V,Vinv` nor internal Euclidean
work. The inspected controlled-Hermite route requires nonzero-minor hypotheses
unavailable for a general singular rectangle; no global-bound transfer was
proved. This bounded attempt stops at the checked semantic iteration invariant.

**Sources and reuse.** Read the [30 October weekly review](2026-10-30-literature-review.md)
on **1 November 2026 UTC**. Targeted re-access that day covered Ji
[arXiv:2607.22524v2](https://arxiv.org/html/2607.22524v2) (1 August 2026),
§§3.2, 5, 6.2 and 7.2, and its
[pinned endpoint](https://github.com/JJYYY-JJY/lean-normal-forms/blob/3f80f9524d88a124a49330eb36a2acb5ed41e179/NormalForms/Research/KannanBachem/Bounds.lean)
at `3f80f9524d88a124a49330eb36a2acb5ed41e179`. Its square/nonsingular
input and prepared nonzero-minor invariant do not cover this arbitrary
rectangular/singular target; its arithmetic trace excludes structural machine
costs. The elementary binary-divisor argument also appears in its §5.
This increment independently proves it for the existing local controller;
no external code, theorem or dependency was imported. This was source
inspection, without external replay or axiom audit. The review's original
Kannan–Bachem full-text access gap remains; no new access to it or broad daily
search is claimed. Read-only inspection of pinned `lean-np-hardness`
`BinaryNatLists`, `FinEncoding` and `BinaryArithmetic` reused the codec bridge,
without finding a ready signed division/gcd or global matrix machine here.

**Validation and attempts.** Read `AGENTS.md` and saved shared
`/workspace/shared/theorem-provers/START.md`; no separate Start skill was exposed
in filesystem or executor/cloud catalogs. Published environment version/readiness
matched. Sourced `env.sh` and passed `check.py` before proofs and after the
builds, using exact prepared Lean 4.35.0, pins and clean dependency artifacts.
Verified clean authorized `solresol/phd-thesis-lean` origin and fetched `main`.
Generated `work` and `origin/main` both equalled
`7bc0d35e4a0b6b4691d895b4508aca1fbbcc5fb3`; preserved `work` before creating
tracking `main`. No unrelated checkout, dependency, configuration or schedule
changes occurred; Raksasa was not accessed.

The general proofs elaborated without mathematical changes. A missing
`Nat.size_mul` API probe led to the existing `Nat.size_bit` bridge. Nonzero
well-founded traces did not kernel-reduce under `decide`; explicitly labeled
guarded evaluations check them instead. Universal proofs are independent of
those computations. Kernel examples cover all-zero, both empty orientations,
`0 × 0` and missing counts. An unreachable tactic warning was removed.

Guarded `lake build PhdThesisLean.SmithIsolationCount` (3,202 jobs) and
`lake build PhdThesisLean DiscreteMetricRegression` (9,302 jobs) passed. The
separate import/`#print axioms` audit covers all 26 new public declarations,
`SmithDiagonalization.decompose_valid`, `rhoMax_rational_smith` and
`rhoMax_of_valid`; only `propext`, `Classical.choice`, `Quot.sound` or subsets
occur. All 1,197 full-build axiom reports satisfy the same check. The
comment/string-aware scan of 172 project/adapter Lean files found no prohibited
tokens; `git diff --check` passed. The new module/audit have no warnings or
errors; the builds replay 22/551 existing warnings. Resource guards and two
threads were retained. Logs, scan and intermediate failures remain in ignored
`.research/smith-isolation-count-2026-11-01/`.

**Next.** Establish a polynomial global width invariant for
`S,U,Uinv,V,Vinv` through every rectangular/singular diagonal stage, with a
controlled reduction algorithm if necessary. Then combine semantic pass
counts with internal Euclidean/arithmetic counts and actual binary machines,
including parsing, traversal, copying and complete serialization. Finish the
optimizer composition with denominator clearing and residual costs. The weak
diagonalizer is correct; the headline `thm:max-polytime` remains Partial.

### Local pivot widths and complete output size (2 November 2026 UTC)

**Question and exact increment.** The first unfinished obligation remains a
controlled-growth algorithm for arbitrary singular rectangles. Can the internal
Euclidean work, including both inverse maps and temporary signed-swap additions,
be bounded before attempting its global invariant? In the new namespace
`PhdThesisLean.SmithPivotBounds`, `gcdTrace_length_le` proves

```lean
(gcdTrace (n := n) r s h a b).length ≤ 8 * b.natAbs.size
```

Two nonterminal divisions at least halve the second magnitude. Every multiplier
is bounded by the incoming pair's common height (`gcdTrace_coefficient_le`).
`gcdTrace_prefix_pow_bound` then bounds all five matrices after **any prefix**
of the actual addition trace by `2^(d+8c(c+1))`, given incoming state height
`2^d` and pair magnitudes strictly below `2^c`. This controls even incomplete
signed swaps and the inverse updates in their opposite composition order.

For complete dense input length `s`, `pivot_prefix_bound` supplies the bound
`2^(8s²+9s)` with no supplied trace or output-width assumption.
`pivotDense_output_length_le` and `reduceDense_output_length_le` consequently
bound the full five-matrix encoding by `64s⁴+72s³+16s²+10s+25` bits. The latter
is the existing total single-entry reduction in either orientation, including
exact division, zero pivots, equal/missing indices and empty shapes. Input is
the unchanged unary-dimension, row-major signed-binary encoding; output charges
every sign, field frame, dimension and inverse entry. Supplied control indices
have no new codec. Existing integer equivalence theorems are unchanged.

**Attempt and unresolved invariant.** To compose the general bound using only
its incoming state height, one can take `c=d+1`; repeatedly applying that
quadratic width update does not produce a polynomial in the original input.
The new local proof therefore does not close even a whole isolation's global
width bound. A sharper invariant must control the selected active entries
independently across reductions and diagonal stages, while retaining bounds on
`U,Uinv,V,Vinv,S`. This is a limitation of the available bound, not a proved
superpolynomial lower bound for the algorithm. The trace length counts row
additions; division, multiplication, parsing, traversal, copying, list
construction and complete serialization have no assigned machine runtime here.

**Sources and reuse.** Read the latest
[30 October weekly review](2026-10-30-literature-review.md) on **2 November**.
Reuse its source/access record without fresh external access: Ji
[arXiv:2607.22524v2](https://arxiv.org/html/2607.22524v2), dated 1 August 2026,
and artifact
[`3f80f9524d88a124a49330eb36a2acb5ed41e179`](https://github.com/JJYYY-JJY/lean-normal-forms/tree/3f80f9524d88a124a49330eb36a2acb5ed41e179),
accessed 30 October by the review and re-accessed 1 November as recorded above.
Its square/nonsingular hypotheses and arithmetic-trace scope still exclude
this general target. This is reviewed preprint/source evidence, not an external
replay or axiom audit. The original Kannan–Bachem full-text access gap remains.
No external theorem is needed for this elementary local proof; the retired
nonnegative-remainder and unmodified alternating-gcd approaches remain retired.
Read-only inspection of pinned `lean-np-hardness` `BinaryNatLists`,
`FinEncoding` and `BinaryArithmetic` reuses the binary-size bridge and confirms
the existing addition/codec APIs; no generic foundations, dependencies or pins
were duplicated or changed. No broad daily search is claimed.

**Commands, repairs and checked evidence.** Read `AGENTS.md` and shared saved
`START.md`; the executor skill catalog is empty, so no separate Start skill was
available. The published environment version and current readiness matched.
Sourced `env.sh` and passed required `check.py` before proofs and after builds,
without installation. Clean generated `work` and live `origin/main` both equalled
`0f1b6dfc4a8ee80e20dc643a80e790dc25f8fb64`; preserved `work` and created tracking
`main`. No unrelated checkout, configuration or schedule was changed; Raksasa
was not accessed. The initial auxiliary natural lemma needed an explicit positive
divisor: modulo zero does not justify descent. Its callers supply that fact
from the existing nonzero branch. Controlled unfolding repaired recursive
simplification; the prefix-length API was corrected to bound by the full trace.
These repairs added no target assumption.

Using the unchanged guarded runner and two threads,
`lake build PhdThesisLean.SmithPivotBounds` passed (3,203 jobs), followed by
`lake build PhdThesisLean DiscreteMetricRegression` (9,304 jobs). A separate
import/type/`#print axioms` audit of all 21 new public declarations and
`decompose_valid`, `rhoMax_rational_smith`, `rhoMax_of_valid` passed with only
`propext`, `Classical.choice`, `Quot.sound` or subsets. All 1,260 full-build
axiom reports satisfy the same check. Kernel computations cover Fibonacci and
signed/zero division traces, both empty orientations, `0 × 0`, missing indices
and the documented quartic expansion. The new module and final audit have no
warnings/errors; builds replay 22/555 existing warnings. The comment/string-aware
scan of 174 project/adapter Lean files found no prohibited tokens, and
`git diff --check` passed. Logs and intermediate failures are retained under
ignored `.research/smith-pivot-bounds-2026-11-02/`.

**Next.** Establish a global controlled-growth invariant for selected active
entries and all four integral transformations, valid for singular rectangles,
then combine it with the local bounds and semantic counts. Concrete uniform
signed-binary arithmetic and structural machines, their polynomial encoded-bit
costs and final optimizer composition remain absent. `thm:max-polytime` stays
Partial. This run stops at the audited local increment.

### Complete sweep-pair widths (3 November 2026 UTC)

**Question and exact increment.** The first unfinished obligation remains a
controlled-growth algorithm for arbitrary singular rectangles. Can the existing
selected-column invariant avoid compounding the single-pivot width update at
every target in a finite sweep? Yes: `SmithSweepBounds.lean` now proves

```lean
sweepRows_prefix_pow_bound ... (hc : 0 < c)
    (hQ : Bounded Q (2 ^ d))
    (hS : ∀ i, (Q.S i j).natAbs < 2 ^ c) :
  Bounded (run Q ((sweepRowsTrace Q r j rows).take t))
    (2 ^ (d + rows.length * (8 * c * (c + 1))))
```

The column hypothesis concerns only the incoming selected column. The existing
`reduceRows_column_bound` preserves it at pair boundaries, including a zero
pivot, so every pair uses the same `c`. `sweepRowsTrace_run` replays the actual
divisibility-aware controller on all five matrices. Repeated targets and the
pivot itself are permitted. Prefixes include temporary signed-swap additions;
the inverse updates retain their opposite composition order.

For actual complete dense input length `s`, put `W=s+8s²(s+1)` and
`C=W+8s(W+1)(W+2)`. Transposition turns the second sweep into actual column
instructions. `crossTrace_run` proves `run Q (crossTrace Q k) = cross Q k`;
`crossTrace_input_prefix_bound` bounds **every** prefix magnitude of all five
matrices by `2^C`. `crossTrace_length` and
`crossAdditions_le_input_length` bound the semantic addition count by
`8s²+8s(W+1)`. `crossDense_output_length_le` bounds the complete five-matrix
output by `2*(5s+10+2s²*(2(C+1)+2))+5`. Thus one pair has degree-seven widths,
degree-four addition counts and degree-nine output size. This proves the
suggested fixed-column exponent for the current controller rather than assuming
it or iterating the prior coarse bound blindly.

**Encoding and remaining invariant.** Input remains the decoder-checked unary
dimension headers and row-major signed binary integers; output includes five
framed dense matrices, signs, zero fields, dimensions and both integral inverses.
There are no square, rank or nonzero-pivot hypotheses. Missing positions and both
empty orientations have empty traces. The runtime position `k` still has no new
codec. Addition counts assign no cost to division, multiplication, traversal,
trace construction, copying, tests or serialization. A pair need not isolate
the pivot: the rectangular regression still has a nonzero lower arm afterward.
Iterating this degree-seven width update over a bit-bounded number of pairs does
not yield a polynomial global bound. That is a limitation of the available bound,
not a superpolynomial lower bound on the algorithm. Repeated isolation and all
later diagonal stages need a sharper invariant or controlled reduction method,
followed by uniform binary machines and optimizer composition.
`thm:max-polytime` stays Partial.

**Sources and reuse.** Read the latest available
[30 October review](2026-10-30-literature-review.md) on **3 November UTC**;
no newer review was present after fetching current main. Reuse its version and
access record for Ji [arXiv:2607.22524v2](https://arxiv.org/html/2607.22524v2),
dated 1 August 2026, artifact
[`3f80f9524d88a124a49330eb36a2acb5ed41e179`](https://github.com/JJYYY-JJY/lean-normal-forms/tree/3f80f9524d88a124a49330eb36a2acb5ed41e179),
accessed 30 October by the review and 1 November as recorded above. Its square,
nonsingular arithmetic model is not the rectangular encoded-machine theorem.
This remains source inspection, without external replay or an external axiom
audit. The original Kannan–Bachem full text remains unverified here under the
recorded access limitation; no fresh access or broad literature search is claimed.
This increment needs no new external theorem. Read-only inspection of pinned
`lean-np-hardness` `FinEncoding`, `BinaryNatLists` and `BinaryArithmetic` reuses
the existing size/codec and machine boundary; no generic foundations or signed
division/gcd machine were duplicated, and no dependencies changed.

**Attempts, commands and checked evidence.** Read `AGENTS.md`, saved shared
`START.md`, TODO and status. The independent fresh-task runtime gate passed
before proof work, with source/receipt persistence recorded before sourcing.
Verified the clean authorized origin, fetched `main` at
`b4da47e5dc9c4f0a18cbfe48bb00a1d47ae888ba`, verified ancestry and unchanged pins,
preserved generated `work` at `038f365`, and created tracking `main`.
The initial elaborations needed explicit simplification of an empty-trace branch
and the correct `List.map_take` orientation. These proof-script repairs added
no mathematical assumption. All failures remain in ignored logs.

Using `prepare.py`'s guarded runner, exact absolute Lean/Lake 4.35.0 binaries,
two threads and existing caches, `lake build PhdThesisLean.SmithSweepBounds`
passed (3,204 jobs), then `lake build PhdThesisLean DiscreteMetricRegression`
passed (9,310 jobs). The separate import/type/`#print axioms` audit covers all
34 new public declarations and eight correctness/optimizer endpoints; all use
only `propext`, `Classical.choice`, `Quot.sound` or subsets. All 1,306 full-build
axiom reports satisfy the same check. The new module and separate audit have
no warnings or errors; builds replay 22/551 existing warnings. Six kernel
computations cover exact division, repeated targets, zeros, missing indices and
empty shapes. Two explicitly labeled evaluator regressions check nonzero
Euclidean recursion, a protected prefix, trace counts and a still-unisolated
rectangle; these computations do not prove the universal bounds. The
comment/string-aware scan of 180 project/adapter Lean files found no prohibited
tokens. Final runtime/pin/dependency checks and `git diff --check` passed.
Evidence remains under ignored `.research/smith-sweep-bounds-2026-11-03/`.
No other repository, configuration, schedule or user computer was changed.

**Next.** Control widths across repeated sweep pairs and diagonal stages in the
original input bits, retaining all four transformation matrices and inverse
identities. Then assign actual binary arithmetic and structural machine costs
and compose denominator clearing, optimizer construction and residual evaluation.
This run stops at the audited single-pair increment.

### Forward maps suffice for state widths (4 November 2026 UTC)

**First unfinished obligation and bounded attempt.** The missing ingredient is
still a controlled-growth decomposition for every singular rectangular `Dense`
input: find a fixed polynomial in its original encoded length bounding every
intermediate coefficient through repeated sweep pairs and diagonal stages,
then implement and bound a uniform machine. The existing weak diagonalizer's
correctness is already proved. Iterating `crossWidth` is still inadequate;
this run does not repeat that substitution as a proposed polynomial proof.
Instead, remove the need for independent growth recurrences for three of the
five state matrices.

The exact new implication in `SmithForwardBounds.lean` is

```lean
bounded_of_input_forward (A : Dense) (Q : State A.rows A.cols) (d : ℕ)
    (hQ : Invariant A.toMatrix Q)
    (hU : ∀ i j, (Q.U i j).natAbs ≤ 2 ^ d)
    (hV : ∀ i j, (Q.V i j).natAbs ≤ 2 ^ d) :
  Bounded Q (2 ^ stateWidth (SmithEncoding.encode A).length d)
```

Here `stateWidth s d = (s+2)*(d+s+1)`. For an integral square map `T` with
integral left inverse `B`, `inverse_entry_natAbs_eq_adjugate` proves
`|(B)ij| = |(adjugate T)ij|`, since `det T` is a unit. Reusing
`RationalWitnessBounds.det_natAbs_le_pow` on the cofactor row-replacement
formula gives `inverse_natAbs_le_pow`:

```
|Tij| <= 2^d and B*T=1  ==>  |Bij| <= 2^(m*(d+size(m))).
```

`mul_entry_natAbs_le` charges every summand of a rectangular product.
Consequently `U*A*V=S` gives `|Sij| <= 2^(2d+3s)` using dimensions and input
entries charged to the original encoding. The common exponent above dominates
both inverse bounds and this product bound. `trace_prefix_bound` applies the
implication to any actual addition prefix; the existing `run_invariant` proves
its integral identities, including unfinished signed swaps. No square,
nonsingular, rank, sign or nonempty hypothesis is imposed on the input.

**Encoding, output and exact remaining invariant.** Input is still unary
runtime dimension headers followed by signed/framed row-major binary entries.
For `B=(s+2)*(d+s+1)`, `output_length_le_of_forward` bounds all five stored
matrix encodings by `2*(5s+10+2s²*(2(B+1)+2))+5`, including both inverses,
signs, canonical zero fields, framing and dimensions. Thus a polynomial bound
on the two forward maps would suffice for polynomial state and output widths.
The two forward-map bounds are **hypotheses of this implication**, not completed
evidence for the global target. No uniform polynomial `d=P(s)` through the
computed repeated sweeps and diagonal stages has been proved. This is the next
unresolved invariant; a different controlled reduction may still be necessary.
Arithmetic identities, existing algorithm correctness, this conditional size
reduction, global growth, semantic operation counts and actual uniform-machine
runtime remain separate claims. Division, multiplication, traversal, copying,
trace construction and serialization receive no machine cost here. Final
optimizer composition is unchanged and `thm:max-polytime` remains Partial.

**Literature and reuse.** Before choosing the increment, read the latest
[30 October weekly human-literature review](2026-10-30-literature-review.md);
no newer review exists on the fetched `main`. Its source record is reused:
Ji [arXiv:2607.22524v2](https://arxiv.org/html/2607.22524v2), v2 dated
1 August 2026, artifact
[`3f80f9524d88a124a49330eb36a2acb5ed41e179`](https://github.com/JJYYY-JJY/lean-normal-forms/tree/3f80f9524d88a124a49330eb36a2acb5ed41e179),
accessed 30 October in the review and 1 November in the recorded source check.
Its Theorem 2.1 and section 6.2 require nonsingular square inputs and exclude
structural machine costs, so they do not discharge our singular rectangular
encoded-machine target. This remains reviewed preprint/artifact inspection,
not an independent external build or axiom audit. No new external theorem is
used or fresh paper access claimed on 4 November; this step uses the existing
kernel-checked determinant bound and inspected pinned mathlib adjugate APIs.
The original Kannan–Bachem full text remains unverified under the recorded
access restriction. No broad daily search or author contact occurred. The
nonnegative-remainder and unmodified alternating-gcd approaches remain retired.
Read-only inspection of pinned `lean-np-hardness` `BinaryNatLists` and
`BinaryArithmetic` reuses the existing codec/size boundary; no signed gcd or
matrix-controller machine was found or duplicated. Dependencies are unchanged.

**Validation and attempts.** The saved Start skill is absent from the executor
and cloud catalogues and checkout `.agents/skills`; read the saved shared
`START.md` and repository `AGENTS.md`. The fresh task passed the complete
published runtime gate before proof work, without installation. Verified the
public authorized repository ID `1307230856`, origin and clean generated `work`
at `b1d0934330b861ceb7ee85d53cae8f11708c2b19`; fetched identical live `main`,
verified ancestry, preserved `work` and created tracking `main`. Exact pins,
dependency sources and prepared artifacts remained unchanged.

The core proof checked after two API corrections (`Nat.size_le` with
`Nat.lt_two_pow_self`, and the finite-sum interface). One empty-case example
needed the existing dense zero matrix rather than an unnecessary definitional
equality to the abstract zero function. These were proof-script repairs,
without changed assumptions. Seven kernel-checked specializations cover a
negative determinant, an unfinished swap in a rectangle, both empty orientations
with nontrivial transformation maps, `0 × 0`, and an empty product dimension.
Using the saved guarded runner, exact Lean/Lake 4.35.0 and two threads,
`lake build PhdThesisLean.SmithForwardBounds` passed (3,212 jobs), then
`lake build PhdThesisLean DiscreteMetricRegression` passed (9,311 jobs).
The separate import/type/axiom audit covers all nine new declarations and six
prior endpoints, including `decompose_valid`, `rhoMax_rational_smith` and
`rhoMax_of_valid`: fourteen reports use only `propext`, `Classical.choice`,
`Quot.sound` or subsets; `stateWidth` is axiom-free. All 1,315 full-build axiom
reports pass the same check. New module and independent audit have no warnings;
builds replay 47/551 existing warnings. All 181 project/adapter Lean sources
pass the comment/string-aware prohibited-token scan; diff checks pass.
The final complete runtime/pin/dependency startup gate also passed unchanged.
Evidence and failed intermediate scripts remain in ignored
`.research/smith-forward-bounds-2026-11-04/`. No other checkout, adapter,
configuration, schedule or user computer was changed. Stop at this one audited
conditional increment; the coordinator handles any later Raksasa synchronization.
