# Weekly human-literature checkpoint — 6 November 2026 UTC

Scheduled for 23:00 UTC / 7 November Sydney; sources accessed **6 November
2026 UTC**. Previous successful review: [30 October](2026-10-30-literature-review.md).
Search overlap begins **23 October UTC**. Human-attributed papers and author
artifacts were screened; autonomous-agent activity was excluded.

**No usable new or revised source was located for the current Smith growth or
uniform-machine obligation.** This is a bounded search conclusion.

## Exact target and consequence

Read `TODO.md`, the [Smith plan](smith-complexity-plan.md), current status and
the prior literature record on fetched live main
`41345e663660507f52eaf592562cbc918dbb0b11`. Correctness of the weak diagonalizer
is already proved. The missing invariant is a single fixed polynomial `P(s)`
bounding both forward transformations by `2^(P(s))` at **every addition prefix**,
for every singular/rectangular/empty dense input of original encoded length `s`.
The existing global addition-count theorem assumes such prefix widths. Actual
binary/structural machine costs, full output handling and optimizer composition
remain separate. Signed binary multiplication is already present on this main;
it should not be reopened in response to this review.

## Primary-source rechecks

- Ji, [2607.22524v2](https://arxiv.org/abs/2607.22524), remains v2 dated
  **1 August 2026**, following v1 on 24 July. Re-read
  [Theorem 2.1 and §6.2](https://arxiv.org/html/2607.22524v2).
  The input is nonsingular and square; the fixed polynomial bounds cover an
  execution-derived arithmetic-leaf cost and five-matrix encoding length.
  Structural operations remain outside that cost model. The author artifact's
  live main is still
  [`3f80f9524d88a124a49330eb36a2acb5ed41e179`](https://github.com/JJYYY-JJY/lean-normal-forms/commit/3f80f9524d88a124a49330eb36a2acb5ed41e179),
  dated 1 August. Inspected its
  [scope](https://github.com/JJYYY-JJY/lean-normal-forms/blob/3f80f9524d88a124a49330eb36a2acb5ed41e179/SCOPE.md)
  and [Bounds.lean](https://github.com/JJYYY-JJY/lean-normal-forms/blob/3f80f9524d88a124a49330eb36a2acb5ed41e179/NormalForms/Research/KannanBachem/Bounds.lean):
  the nonzero-determinant premise persists. Classification: preprint and
  inspected formal-artifact source, without independent replay. Full algorithm
  reading remains useful for controlled-growth design; no new revision or
  transferable rectangular prefix bound was found.
- Senellart–Gnatenko, [2609.18261](https://arxiv.org/abs/2609.18261), is still
  **v1, 16 September 2026**. The author repository's
  [latest release](https://github.com/PierreSenellart/descriptive-complexity/releases/tag/v1.4.0)
  is still **v1.4.0, 21 October**. No newer release was displayed. The prior
  review's source-level interface limitations are retained; no new simulation
  or API compatibility claim is made. No additional full reading is needed for
  the immediate Smith invariant.
- The [Kannan–Bachem publisher abstract](https://epubs.siam.org/doi/10.1137/0208040)
  confirms polynomial operation/intermediate-bit bounds and multipliers for
  its algorithms. Full text still requires access. This does not establish a
  bound for our particular diagonalizer. The 23 October multivariate-matrix
  [Journal of Algebra paper](https://doi.org/10.1016/j.jalgebra.2026.10.015)
  was again accessible only in publisher search/preview text; direct article
  access returned HTTP 403. Its constructive equivalence scope does not
  verify our integer prefix or encoded-machine theorem.

## Search checkpoint

The [arXiv API](https://export.arxiv.org/api/query) was queried with
`sortBy=lastUpdatedDate`, descending, `start=0`, `max_results=100`. Retrieved
dates/titles were screened; relevant candidates received primary-text checks.

| Query | Retrieved / total | Updates from 23 October |
| --- | --- | --- |
| `ti:"Smith normal form" OR all:"Kannan-Bachem"` | 34 / 34 | 0 |
| `all:"Smith normal form" AND (all:algorithm OR all:complexity OR all:verified)` | 55 / 55 | 0 |
| `ti:complexity AND (all:Lean OR all:verified OR all:formalization)` | 100 / 2,232 | 24; no applicable new invariant or machine bridge |
| `(all:Lean OR all:Coq OR all:Isabelle) AND (ti:Turing OR ti:"polynomial time" OR ti:"Cook-Levin" OR ti:"verified complexity" OR ti:"bit complexity")` | 15 / 15 | 3; problem-specific algorithms or reversible-machine size, outside this target |

Supplementary searches covered SIAM/SICOMP, Journal of Symbolic Computation,
Journal of Algebra, ACM, Springer/JAR, AFP and Dagstuhl primary sources. Recent
Smith applications and unrelated meanings of complexity were screened out.
The broad 100-result query is incomplete; unpublished, unindexed and differently
named work remain outside coverage. The p-adic norm-oracle paper already in the
30 October review is not counted again as new progress.

Continue the forward-map invariant or a controlled-growth replacement. No
dependency or target change follows. Next weekly overlap: **30 October UTC**.
Documentation checks only: the full shared startup check failed at missing
`/workspace/shared/theorem-provers/scholz-ready.json` after thesis/Littlewood
imports passed. `START.md` gates Lean work; no proof build, external artifact
replay, preparation, pin change or environment publication was performed.
