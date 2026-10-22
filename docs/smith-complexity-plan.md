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

## Proof sequence

1. Establish elementary operations over **integers**, with explicit inverse
   transformations and local growth bounds. `SmithRowOperations.lean` is the first
   increment: reversible row addition, equality with mathlib transvection
   multiplication, `natAbs ≤ (C+1)*H`, and the power-of-two bound
   `natAbs ≤ 2^(a+b+1)`. It has no operation-count or machine-runtime theorem.
   Next connect column operations, swaps and sign changes to a transformation
   trace whose product maintains `U*A*V=S` and inverse identities.
2. Select and cite a controlled-coefficient polynomial Smith algorithm, such as
   the Kannan–Bachem route already cited by the thesis. Inspect the primary
   algorithm before fixing invariants. Existence of Smith form over a PID or
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
> resources before builds. Begin with the first unfinished proof-plan obligation,
> state its exact theorem, computational encoding and unresolved invariant, and
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
