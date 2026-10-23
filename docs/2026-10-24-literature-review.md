# Weekly literature review — 24 October 2026 (Australia/Sydney)

First weekly baseline: no earlier successful weekly review was found in the
checkout. This reviews human-attributed research, with AI assistance disclosed
where the authors disclose it; autonomous-agent activity is not research evidence.
All sources below were accessed on **24 October 2026 Australia/Sydney**
(23 October UTC). Publication/version dates are source dates, not crawl dates.

## Exact target and internal baseline

At `219c51bd392e792d5605756c63f4f04d60da5a87`, `thm:max-polytime` is partial.
For a runtime rectangular integer matrix, including empty and rank-deficient
cases, construct `U,Uinv,V,Vinv,S` satisfying `SmithDecomposition.Valid`;
canonical signs/zero order/divisibility are an additional contract. Prove
termination, global coefficient/output growth and a uniform
`TM2ComputableInPolyTime` implementation in actual encoded input bits, then
compose the rational/p-adic adapters. Unary dimension headers charge even empty
matrices. The supplied-output checker and serialization bounds conditional on
entry bit length are internal progress, not such an algorithm.

## Newly located external leads (baseline discoveries, not this week's publications)

### Ji: the closest formal algorithm lead

Junye Ji, [*Machine-Checked Arithmetic Bit Complexity of the Kannan–Bachem Smith
Normal Form in Lean 4*](https://arxiv.org/abs/2607.22524v2): v1 **24 July 2026**,
v2 **1 August 2026**, no later version displayed. Read the
[statement and cost boundary](https://arxiv.org/html/2607.22524v2#S2.SS4),
algorithm description, §6.2 and §10. Theorem 2.1 requires a **square matrix with
nonzero determinant** and returns all five matrices, inverse identities,
canonical Smith form, and fixed polynomial arithmetic-trace/output-length bounds.
Indexing, traversal, allocation, conversion, decoding and serialization runtime
are excluded. Bounded XGCD is charged as an opaque arithmetic block.

Classification: **human-authored preprint with an author-reported Lean artifact**,
not an independently replayed result here. The AI-use statement says Codex
generated proofs, with ideas and manual statement/assumption review attributed to
the author. It is not evidence from an autonomous bot's status report.
Full algorithm/proof reading is worthwhile before choosing our growth invariant;
the two missing scope bridges (singular/rectangular inputs and structural TM2
costs) prevent treating it as completion of our target.

The public source was inspected at
[`3f80f9524d88a124a49330eb36a2acb5ed41e179`](https://github.com/JJYYY-JJY/lean-normal-forms/tree/3f80f9524d88a124a49330eb36a2acb5ed41e179)
(commit dated **1 August 2026**):
[scope](https://github.com/JJYYY-JJY/lean-normal-forms/blob/3f80f9524d88a124a49330eb36a2acb5ed41e179/SCOPE.md),
[actual endpoint](https://github.com/JJYYY-JJY/lean-normal-forms/blob/3f80f9524d88a124a49330eb36a2acb5ed41e179/NormalForms/Research/KannanBachem/Bounds.lean)
`verifiedSmithPolynomialBitCost`, and
[polynomial-envelope calculus](https://github.com/JJYYY-JJY/lean-normal-forms/blob/3f80f9524d88a124a49330eb36a2acb5ed41e179/NormalForms/Research/KannanBachem/Polynomial.lean).
The endpoint explicitly takes `hdet : A.det ≠ 0`; its cost field is the fold of
`run.charges`, not a TM2 runtime. The artifact uses Lean **4.32.0**, whereas this
project uses **4.35.0**. Its code is Apache-2.0. No code was copied, dependency
added, toolchain installed, or external artifact built. A source inspection is
not an axiom-closure audit or a successful independent replay.

### Senellart–Gnatenko: complexity foundations with a different interface

Pierre Senellart and Anton Gnatenko,
[*Descriptive Complexity in Lean: Completeness by First-Order Reductions*](https://arxiv.org/abs/2609.18261v1),
v1 **16 September 2026**, no revision displayed. Read
[§§3–5 and §8](https://arxiv.org/html/2609.18261v1): problems are predicates on
finite structures, classes use logical definability, and hardness uses
first-order reductions. The machine bridge represents a machine/computation as
structure data with a universe-size time bound; it is not our TM2-to-tidy-CSLib
simulation. The paper reports a Lean development, including Cook–Levin, using
Lean/mathlib 4.33.0 and release 1.2.2 of its
[source](https://github.com/PierreSenellart/descriptive-complexity).
Its acknowledgements disclose Claude-assisted code and author responsibility.

Classification: **preprint/formalization report; not replayed here**.
Full reading is useful for future hardness-interface comparisons, after the
Smith algorithm work. It does not discharge the existing adapter's explicit
`SimulationObligation`, justify changing pins, or reopen the completed
all-different CSP queue. The separate Complexitylib prototype at our current
HEAD is already-known internal work, not a discovery from this review.

## Established background and screened alternatives

| Primary source; version/date | Finding and effect on this plan | Reading decision |
| --- | --- | --- |
| Kannan–Bachem, [SIAM J. Comput. 8(4), 499–507 (1979)](https://epubs.siam.org/doi/10.1137/0208040) | Publisher abstract explicitly bounds both algebraic operations and intermediate binary digits and includes multipliers. This is the classical algorithmic baseline, not new progress. Full publisher text was access-restricted in this review; no uninspected rectangular/inverse implementation detail is asserted. | Full primary algorithm reading remains necessary before fixing invariants; Ji is a useful companion. |
| Birmpilis–Labahn–Storjohann, [arXiv:2111.09949v2](https://arxiv.org/abs/2111.09949v2), 21 September 2022; [J. Symbolic Comput. 116 (2023), 146–182](https://doi.org/10.1016/j.jsc.2022.09.002) | Nonsingular integer matrices, Las Vegas expected-time multipliers with equation `AV=US`. This differs in transformation convention and randomized resource model from our deterministic uniform-machine goal. | Defer performance-oriented route; not a drop-in formal theorem. |
| Wang–Birmpilis–Labahn–Storjohann, [arXiv:2605.19254v1](https://arxiv.org/abs/2605.19254v1), 19 May 2026 | C implementation of a nonsingular Smith massager algorithm and timing experiments. Computation/implementation evidence, not a Lean proof of our full contract. | Abstract screened; defer full reading unless choosing a randomized implementation. |
| Giesbrecht, [arXiv:2607.05800v1](https://arxiv.org/abs/2607.05800v1), 7 July 2026 | Monte Carlo invariant-count algorithm over `ℤ/p²ℤ` with a sparse black-box hypothesis and ring-operation costs. Wrong coefficient ring/output contract for the present integer transformations. | Abstract screened; no full reading needed for this target. |
| Divasón, [AFP Smith_Normal_Form](https://isa-afp.org/entries/Smith_Normal_Form.html), entry 23 May 2020; [JAR paper (2022)](https://doi.org/10.1007/s10817-022-09631-5) | Established Isabelle algorithm/correctness background over Euclidean domains. A current generated PDF date is not a new publication or a polynomial-bit theorem. | Reuse as correctness background; do not infer the missing runtime bound. |

## Research implication

Before independently rebuilding a Kannan–Bachem proof architecture, compare Ji's
actual coefficient recurrences, inverse accumulation and pivot-size descent with
our finite `Result` contract. Record exactly what can be reused and what requires
new singular/rectangular and encoded-machine proofs. Do not weaken the target to
nonsingular square inputs, count arithmetic leaves as full runtime, or change the
stable pins to import an artifact. The current local primitives and supplied
decomposition bounds remain useful but partial.

## Search checkpoint and limits

Baseline search covered indexed new submissions **and revisions**, not only the
latest seven days. On 24 October Sydney, queried the
[arXiv API](https://export.arxiv.org/api/query) with
`sortBy=lastUpdatedDate`, `sortOrder=descending`:

- `ti:"Smith normal form" OR all:"Kannan-Bachem"`: 34 results, all retrieved.
- `all:"Smith normal form" AND (all:algorithm OR all:complexity OR all:verified)`:
  55 results, all retrieved. Recent application-specific Smith forms and
  multivariate polynomial-matrix equivalence were screened out by scope.
- `ti:complexity AND (all:Lean OR all:verified OR all:formalization)`: first 100
  of 2,212 results; this broad, noisy query was **not** exhaustive. Targeted
  title/source searches found the descriptive-complexity paper above.

Also searched primary publisher/author sources, including SIAM, Journal of
Symbolic Computation, JAR/AFP and the authors' linked formal artifacts, using
Smith/Kannan–Bachem with polynomial, bit complexity, verified and Lean terms.
No later source located here closes our complete rectangular TM2 target.
This is a scoped negative search result, not proof of absence or a novelty claim.
Next review should search updates since this checkpoint with at least a
seven-day overlap (start **17 October 2026 UTC**) for delayed indexing and recheck
the selected papers' abstract pages for revisions/withdrawals.

Operational limits: the requested saved Start skill was absent from the exposed
`.agents/skills`, user skill locations and available skill catalog; the shared
environment's `START.md` and repository `AGENTS.md` were read. All four authorized
origins/worktrees were checked, generated `work` branches preserved, and tracking
`main` created only after ancestry checks. The prepared-runtime `check.py` passed
for thesis, Littlewood and Scholz after sourcing `env.sh`. This documentation-only
review does not rerun unrelated proof builds or the separate adapter.
