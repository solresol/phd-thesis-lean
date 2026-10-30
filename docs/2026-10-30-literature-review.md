# Weekly literature review — 30 October 2026 UTC

Follow-up to the [24 October baseline](2026-10-24-literature-review.md),
accessed 23 October UTC. Sources below were accessed **30 October 2026 UTC**.
Search overlap starts **17 October 2026 UTC**, covering new submissions and
revisions. Human-attributed research and author-maintained artifacts are the
evidence; autonomous-agent progress reports are excluded.

## Current target and decision

Read the current [Smith plan](smith-complexity-plan.md) and the separate
[complexity adapter](../adapters/complexitylib/README.md) at
`4ea1d6d97aedc6fa88b8c7724df54b9a428f1e17`. Recursive single-position isolation
is checked, including zero pivots and empty rectangular cases; a total
`decompose` satisfying `Valid` is still the next construction obligation.
Polynomial global widths for all five matrices, operation counts and actual
encoded-machine costs remain separate. The binary p-adic valuation increment
does not supply those Smith bounds.

**No new source located closes that target or the adapter's simulation
obligation.** Continue the existing diagonal-position recursion and controlled
growth work. The two scoped updates below do not justify changing dependencies
or reopening completed compiler work.

## Rechecked closest Smith result

Ji, [arXiv:2607.22524v2](https://arxiv.org/abs/2607.22524v2), is unchanged:
v1 **24 July**, v2 **1 August 2026**. Re-read Theorem 2.1 and §6.2 in the
[paper](https://arxiv.org/html/2607.22524v2). Its input remains a **nonsingular
square integer matrix**. The five-matrix correctness, canonical form,
arithmetic-trace and output-length polynomial bounds exclude structural
indexing, traversal, allocation, decoding and serialization costs.

The author artifact's live main still resolves to
[`3f80f9524d88a124a49330eb36a2acb5ed41e179`](https://github.com/JJYYY-JJY/lean-normal-forms/tree/3f80f9524d88a124a49330eb36a2acb5ed41e179),
dated **1 August 2026**. Re-read its
[scope](https://github.com/JJYYY-JJY/lean-normal-forms/blob/3f80f9524d88a124a49330eb36a2acb5ed41e179/SCOPE.md)
and [endpoint](https://github.com/JJYYY-JJY/lean-normal-forms/blob/3f80f9524d88a124a49330eb36a2acb5ed41e179/NormalForms/Research/KannanBachem/Bounds.lean):
`hdet : A.det ≠ 0` remains explicit and `arithmeticCost_eq` folds `run.charges`.
Classification: preprint/formal-artifact source inspection, not an independent
replay or axiom audit. Full algorithm reading remains worthwhile for coefficient
invariants; this is not a new weekly result or a TM2 runtime theorem.

## Descriptive-complexity artifact: newly located release, same interface limit

Senellart–Gnatenko's [paper](https://arxiv.org/abs/2609.18261) remains **v1,
16 September 2026**. Its author-maintained artifact has
[v1.4.0, published 21 October 2026](https://github.com/PierreSenellart/descriptive-complexity/releases/tag/v1.4.0),
after the paper's v1.2.2 artifact; this release predates the last review and is
newly located in this overlap search. The annotated tag resolves to commit
`4f35579400754757b1e6b1f13e74ac1913f64162`.

Read the release notes, pinned
[README](https://github.com/PierreSenellart/descriptive-complexity/blob/4f35579400754757b1e6b1f13e74ac1913f64162/README.md),
`Complexity.lean`, `Machines.lean` and toolchain. The release adds counting/FP
interfaces, uses Lean/mathlib **4.35.0**, and makes implementation helpers
private. The decision-problem interface still uses finite structures and
first-order interpretations; its relational machine acceptance budget counts
universe positions. The inspected interfaces do not provide our TM2-to-tidy-CSLib
simulation. Classification: author-reported release plus inspected source, not
a locally rebuilt theorem. Review its public interface when planning a future
hardness integration; full counting-library reading is not a current Smith
priority. Matching the root toolchain does not establish API compatibility or
authorize a new dependency.

## New p-adic complexity paper: a representation boundary

Fromonot–Haiech–Vaccon,
[*On the Complexity of Computing with p-adic Lattices*, arXiv:2610.38535v1](https://arxiv.org/abs/2610.38535v1),
**28 October 2026**, no revision displayed. Read §§2.1–2.3 and Theorems 4.1,
5.1 and 5.4 in the [PDF](https://arxiv.org/pdf/2610.38535v1). For finite-dimensional
Q_p spaces, the orthogonalization lower bound is a worst-case
`Omega(p^(nu_max-1))` **norm-oracle query** bound, also for randomized algorithms
with success probability at least 2/3. Orthogonality decision uses the largest
commensurability block of the supplied family. An explicit diagonal norm
representation permits an arithmetic algorithm; §2.1 assumes polynomial cost
per arithmetic operation.

Classification: mathematical preprint with proofs, not a Lean verification or
an encoded-bit Smith theorem. Inference for this project: retain the explicit
rational-data/fixed-norm input contract; the oracle lower bound does not obstruct
it. Focused reading is useful before any future arbitrary-norm generalization;
full reading is not needed for the next Smith correctness increment.

## Search checkpoint and access limits

Successful [arXiv API](https://export.arxiv.org/api/query) queries used
`sortBy=lastUpdatedDate`, descending, and inspected all retrieved titles/abstracts:

| Query | Retrieved / total | Overlap result |
| --- | --- | --- |
| `ti:"Smith normal form" OR all:"Kannan-Bachem"` | 34 / 34 | No update since 17 October. |
| `all:"Smith normal form" AND (all:algorithm OR all:complexity OR all:verified)` | 55 / 55 | No update since 17 October. |
| `ti:complexity AND (all:Lean OR all:verified OR all:formalization)` | 100 / 2,219 | 24 overlap records; the p-adic paper above is relevant to input-model scope. Broad query is not exhaustive. |
| `(all:Lean OR all:Coq OR all:Isabelle) AND (ti:Turing OR ti:"polynomial time" OR ti:"Cook-Levin" OR ti:"verified complexity" OR ti:"bit complexity")` | 12 / 12 | One overlap record, a problem-specific Numberlink verification; no reusable machine-cost bridge identified. |

Supplementary targeted searches covered SIAM/SICOMP, Journal of Symbolic
Computation, JAR/AFP, ACM, Springer and author sources. The accessible
[Kannan–Bachem publisher abstract](https://epubs.siam.org/doi/10.1137/0208040)
and [AFP entry](https://isa-afp.org/entries/Smith_Normal_Form.html) retain the
established background scopes. The former's full text still requires access;
no fresh full-algorithm inspection is claimed. A **23 October** Journal of
Algebra [publisher abstract](https://doi.org/10.1016/j.jalgebra.2026.10.015)
concerns multivariate-polynomial-matrix equivalence, not our integer
bit-complexity obligation; its full article returned HTTP 403 and was not
verified. These gaps do not block the present research choice.

This is a bounded negative result for the exact target, not a completeness or
novelty claim. Next review: use this checkpoint with overlap beginning
**23 October 2026 UTC**, recheck versions/withdrawals and the known access gaps.
Only literature documentation changed; no proof build, external artifact replay,
dependency, pin, runtime, schedule, author contact or Raksasa access was needed.
