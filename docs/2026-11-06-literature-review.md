# Weekly human-literature checkpoint — 6 November 2026 UTC

Latest checkpoint: [13 November 2026](#13-november-2026-checkpoint).

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

## 13 November 2026 checkpoint

Previous successful review: 6 November above. Search cutoff **13 November
2026, 23:43 UTC**, overlap **30 October UTC**, including revisions. Sources
accessed 13 November. Read current README, TODO, Smith plan and recent records
on fetched main `71682bb471e07f161ba2539cbc0066bc9c58a038`, including completed
Smith increment `0d05ef4684655f3958170fd374c4947f76ade4ac`.

The target remains an actual uniform polynomial binary-time integer unimodular
decomposition with all five outputs and singular, rectangular and empty inputs.
The computed-trace reduction equates polynomial transformed-entry and
forward-map prefix growth obligations. The exact-division increment requires
divisible incoming arms; it does not propagate these premises through pivot
changes or later stages. No located source supplies that global invariant or
the full encoded-machine algorithm.

### New release: binary-language class bridge, with explicit boundaries

Senellart's [v1.4.1 release](https://github.com/PierreSenellart/descriptive-complexity/releases/tag/v1.4.1),
published **12 November 2026, 13:26:46 UTC**, resolves through annotated tag
`9fa60768fbe21643144e37b832380b3af233c5e2` to commit
`18e9b92a2f4782ff5d2051935ca3adfb619030b8`. The
[paper](https://arxiv.org/abs/2609.18261) remains **v1, 16 September**.
Read the release, pinned `Strings` interface, `NP.lean`, `PTime.lean`,
`Lax/Captures.lean`, both machine-class definitions, structure encoding and
[archive proof wrapper](https://github.com/PierreSenellart/descriptive-complexity/blob/18e9b92a2f4782ff5d2051935ca3adfb619030b8/lax/machine-bridge/proofs/Lax832283Proofs/Bridge.lean).
For a finite relational vocabulary and an invariant decision problem, the new
bridge relates logical NP/PTIME to finite TM2 machines on binary encodings.
Root-library machine theorems take `FaginCaptures` or `ImmermanVardiCaptures`
as explicit hypotheses. The machine-class definitions measure polynomial time
in bit length and exclude malformed encodings. The codec uses a unary universe
header and relation truth tables, not our signed dense-matrix words.

[Lax 832283](https://laxarchive.org/lax-832283/), created **3 November**, displays
source `f06e25b`, Lean 4.33.0 and checked claim dependencies on
[988886](https://laxarchive.org/lax-988886/) and
[751879](https://laxarchive.org/lax-751879/). The inspected proof wrapper applies
their registered capture statements. Distinguish the concepts declarations
from the accompanying proof dependency graph; no independent replay or
transitive axiom audit was performed. Archive pages were available through HTTP
after browser-tool failures. Classification: human-maintained release and
inspected formal source/archive records, with disclosed AI assistance. The root
release uses Lean 4.35.0; matching our version establishes no API compatibility.

This supersedes the prior assessment that only the older relational interface
is available. Read these new modules before future class-level integration.
They do not construct a Smith function, convert our codec, or prove our machine
simulation/composition obligation. No dependency change follows. Full paper
reading is less urgent than the controlled-growth problem.

### Rechecks and search coverage

Ji's [2607.22524v2](https://arxiv.org/abs/2607.22524v2) is still **1 August**;
Theorem 2.1 and §6.2 were re-read: nonsingular square input and arithmetic-leaf
cost remain explicit, with structural work excluded. The author artifact's
main remains `3f80f9524d88a124a49330eb36a2acb5ed41e179`. Full algorithm reading
remains useful for controlled growth, without a transferable rectangular or
uniform-machine result. [Kannan–Bachem](https://doi.org/10.1137/0208040) still
offers the publisher abstract and subscription access; the earlier
[Journal of Algebra item](https://doi.org/10.1016/j.jalgebra.2026.10.015)
was inaccessible directly. Neither full text was audited here.

The arXiv API reran the exact four queries in the 6 November table above,
`lastUpdatedDate` descending, `start=0`, `max_results=100`:

| Query (specified above) | Retrieved / total | Updates from 30 October |
| --- | --- | --- |
| Smith title / Kannan–Bachem | 34 / 34 | 0 |
| Smith algorithm / complexity / verified | 55 / 55 | 1; physics application outside the target |
| Complexity title with Lean / verified / formalization | 100 / 2,245 | 32 screened; broad historical coverage incomplete |
| Formal machine / polynomial-time titles | 16 / 16 | 4 screened; no applicable Smith invariant or codec bridge |

Supplementary primary-source discovery covered SIAM/SICOMP, Journal of Symbolic
Computation, Journal of Algebra, ACM, Dagstuhl and Springer. No applicable new
journal theorem was located. This bounded search supports no absence or novelty
claim. Next overlap: **6 November UTC**. Parent cleared research overlap; only
this existing literature record changes. Documentation validation only: no
Lean build, shared startup execution, experiment, external artifact replay,
pin/runtime, schedule or user-machine change was needed or performed.
