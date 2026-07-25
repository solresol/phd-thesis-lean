# Daily all-different CSP formalisation log

## 2026-07-26 05:21 AEST

- Starting repository commit: `1ad90ac0515abedd03eb510daf039e06de3266cb`
  on `main`; the working tree was clean, and local `HEAD`, `origin/main`, and
  the live `refs/heads/main` all agreed.
- Active thesis claim reviewed:
  `../phd-thesis/sudoku-via-padic-regression/body.tex`,
  `cor:all-different-csp`, especially the proof's explicit domain-value
  relabelling, prime choice, deduplicated primal graph, and appeal to
  `thm:all-different`.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` at `9193996`. It currently
  provides `FinEncoding`/`TM2ComputableInPolyTime` reduction wrappers and
  checked identity/composition adapters, but no reusable concrete CSP syntax,
  encoding, primal-graph construction, or primality-search implementation.
- Chosen increment: explicit finite-domain all-different syntax,
  well-formedness, deduplicated primal-graph construction, and its discrete
  semantic bridge.
- Declarations added in `PhdThesisLean/AllDifferentCSP.lean`:
  `ExplicitSystem`, `WellFormed`, `domainValues`, `primalEdges`,
  `satisfies_iff_isProper`, `conflictCount_eq_zero_iff`,
  `satisfies_iff_inDomain_and_conflictCount_eq_zero`, and
  `minimizesConflicts_iff_satisfies_of_satisfiable`, with supporting
  definitions and endpoint lemmas. `PhdThesisLean.lean` now imports the module.
- Semantics and edge handling: variables are `Fin n`; domains and scopes are
  `Finset`s; shared natural-number domain symbols retain equality across
  domains; primal edges are increasing endpoint pairs in a `Finset`, so
  repeated scopes and co-occurrences produce one conflict edge.
- Verification: `lake env lean PhdThesisLean/AllDifferentCSP.lean` and
  `lake build` succeeded. The new `#print axioms` audits report only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Failed proof-shape attempts resolved during the increment: a subtype endpoint
  equality did not simplify automatically in `conflictCount_eq_zero_iff`, and
  this mathlib revision has no
  `Finset.eq_empty_iff_forall_not_mem.mpr`/`Finset.not_mem_empty` constants.
  Explicit endpoint unfolding plus `Finset.nonempty_iff_ne_empty` gave a
  checked proof.
- Status/README: `cor:all-different-csp` remains **Partial**. No encoder,
  bit-size, prime-selection, or polynomial-time claim is inferred from this
  semantic layer.
- Ending state: one verified source/documentation/log increment ready for a
  normal commit and push; no unrelated user work was present.
- Best next step: define canonical rank relabelling of `domainValues` and prove
  that membership and equality across every variable domain are preserved,
  including the zero- and one-symbol cases needed before prime selection.
