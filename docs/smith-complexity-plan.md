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

1. Establish elementary operations over **integers**, with explicit inverse
   transformations and local growth bounds. `SmithRowOperations.lean` is the first
   increment: reversible row addition, equality with mathlib transvection
   multiplication, `natAbs ≤ (C+1)*H`, and the power-of-two bound
   `natAbs ≤ 2^(a+b+1)`. It has no operation-count or machine-runtime theorem.
   `SmithTrace.lean` now connects row/column additions to a finite transformation
   trace preserving `U*A*V=S` and both inverse identities, with dense output.
   Swaps, sign changes and bounded Bezout/pivot operations remain to connect.
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
