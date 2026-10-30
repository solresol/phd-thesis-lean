# Polynomial-bit-complexity Smith decomposition

The mathematical max-objective formula is already checked in
`PhdThesisLean/MaxObjectiveSmith.lean`. Its assumptions provide integral matrices
`U,U',V,V'`, `U' * U = 1`, `V * V' = 1`, and a rectangular matrix `U*A*V`
whose off-diagonal entries vanish. It does **not** compute those matrices. The
remaining target is a uniform polynomial-time algorithm, measured in encoded bits,
not a theorem assuming its own runtime witness.

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
