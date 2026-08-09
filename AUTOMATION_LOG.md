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

## 2026-07-27 05:26 AEST

- Starting repository commit:
  `b5ea80c90a8674553cd98a37c74c195ce2d529d1` on `main`. The working tree was
  clean; after fetching, local `HEAD` and `origin/main` had no divergence.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` (thesis checkout
  `480b4fe5389777cfb70c8c360afac35fc8ee1f42`). The chosen increment is the
  proof's canonical relabelling of the shared domain-value union onto
  `{1, ..., q}`.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` at
  `0869697c5e61a9198fd8978b38d90281826ba2a2`. Its new work embeds a finite
  machine into combined stacks, but it still has no reusable CSP encoder,
  finite-set rank compiler, or prime-search implementation.
- `PhdThesisLean/AllDifferentCSP.lean` now defines the executable
  `symbolCount`, `relabelValue`, `relabeledValues`, `relabeledDomain`,
  `relabeled`, and `relabelAssignment`. `symbolCount_le_sum_domain_card` proves
  the thesis bound \(q\leq\sum_i |D_i|\), and
  `relabeledValues_eq_Icc` proves that the rank image is exactly
  `{1, ..., q}`.
- The relabelling preserves shared-symbol equality across different variable
  domains. `domainValues_relabeled_eq_Icc`,
  `relabeled_satisfies_relabelAssignment_iff`,
  `conflictCount_relabelAssignment`,
  `relabeled_minimizesConflicts_relabelAssignment_iff`, and
  `relabeled_satisfiable_iff` give the checked semantic correspondence.
  `exists_inDomain_relabelAssignment_eq` supplies every relabelled
  domain-respecting assignment with an original preimage.
- Empty and singleton symbol unions are explicit:
  `relabeledValues_eq_empty_of_symbolCount_eq_zero` and
  `relabeledValues_eq_singleton_of_symbolCount_eq_one`. The general image
  theorem also covers the zero-variable system.
- Verification succeeded:
  `lake env lean PhdThesisLean/AllDifferentCSP.lean`, `lake build` (3081
  jobs), and `git diff --check`. A project-source scan found no `sorry`,
  `admit`, project `axiom`, `unsafe`, or `proof_wanted`; the new headline
  `#print axioms` audits report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Resolved proof/API issues: `omega` did not unfold the wrapped rank/cardinality
  definitions in the first upper-bound proof, so the proof now uses a strict
  `Finset` subset and `card_lt_card`; the natural interval cardinality lemma is
  `Nat.card_Icc`, not `Finset.card_Icc`.
- `README.md` and `THEOREM_STATUS.md` now record canonical relabelling as
  checked. `cor:all-different-csp` remains **Partial**: p-adic dataset emission,
  compiler-selected prime construction, finite encodings, bit-size bounds, and
  genuine polynomial runtime still remain.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes present.
- Best next step: define the concrete supplied-prime p-adic domains and
  deduplicated-edge dataset, prove global unit separation from
  `p > symbolCount`, and instantiate `all_different_correctness`. Mark that
  theorem explicitly intermediate until a checked polynomial-time
  compiler-selected prime is composed with it.

## 2026-07-28 05:27 AEST

- Starting repository commit:
  `18459a3df91cf6f6d1cf0f10954ecb75bb696532` on `main`. The working tree was
  clean; after fetching, local `HEAD`, `origin/main`, and the live remote
  `refs/heads/main` agreed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` (thesis checkout
  `3829f8caf4b81a07ee5b40901e774e96f44cc3cb`). The chosen increment is the
  supplied-prime p-adic objective and its exact semantic composition with
  canonical relabelling and `AllDifferent.all_different_correctness`.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` at
  `bf3487b76ecac4875a2b2721e4400fe6495fe8f5`. Its combined-stack simulation
  work advances generic finite-machine composition, but it still has no
  reusable CSP encoder, domain-rank compiler, prime-search implementation, or
  concrete all-different runtime theorem.
- `PhdThesisLean/AllDifferentCSP.lean` now defines `padicDomain`,
  `padicAssignment`, `pinningWeight`, and `suppliedPrimeLoss`. For a supplied
  prime `p > symbolCount`, `padicDomain_globallyUnitSeparated` proves that the
  canonical ranks are unit-separated in `ℚ_[p]`; the proof uses
  `Padic.norm_natCast_eq_one_iff` and `Nat.coprime_of_lt_prime`.
- The emitted objective has one negative unit-weight residual per
  deduplicated primal edge and uniform positive pinning weight `|E| + 1`.
  `incidentEdgeWeight_lt_pinningWeight` proves the required strict domination,
  while `conflictWeight_padicAssignment` identifies its weighted conflict term
  exactly with the original natural-number deduplicated `conflictCount`.
- `suppliedPrime_allDifferent_correctness` proves existence of a global
  minimiser and characterises every global minimiser exactly as the embedded
  image of an original domain-respecting minimum-conflict assignment.
  `suppliedPrime_globalMin_iff_satisfies_of_satisfiable` proves the corresponding
  exact satisfying-assignment characterisation when the input is satisfiable.
  The converse direction extracts an original assignment from every p-adic
  product-domain point, so the theorem is not only a forward soundness result.
- Resolved proof/API issues: `Finset ℚ_[p]` construction and membership require
  local classical decidability; rewriting membership in `Finset.Icc` exposed a
  list-level representation, so bounds are recovered explicitly with
  `Finset.mem_Icc.mp`; the conflict-count bridge uses
  `Finset.univ_eq_attach`, `Finset.sum_attach`, and `Finset.sum_boole` rather
  than a failed cast/rewrite through the filtered-card expression.
- Verification succeeded:
  `lake env lean PhdThesisLean/AllDifferentCSP.lean`, `lake build` (3081 jobs),
  `git diff --check`, and the project Lean-source forbidden-construct scan.
  The new headline `#print axioms` audits report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `README.md` and `THEOREM_STATUS.md` now record the supplied-prime p-adic
  semantics while keeping `cor:all-different-csp` **Partial**. The compiler
  still does not select a prime or provide a finite output encoding, bit-size
  bound, or `TM2ComputableInPolyTime` construction theorem.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes present.
- Best next step: define an executable compiler-selected prime covering
  `q = 0`, `q = 1`, and `q > 1`, prove its primality and `q < p` (using
  Bertrand for the nontrivial branch), then keep prime-search runtime separate
  from the later finite-encoding and full compiler-runtime proof.

## 2026-07-29 05:21 AEST

- Starting repository commit:
  `fa057f0c31c9368437cac605db527d1319bdd3e4` on `main`. The automation began
  with a clean working tree; after fetching, local `HEAD`, `origin/main`, and
  the live remote `refs/heads/main` agreed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` (thesis checkout
  `3829f8caf4b81a07ee5b40901e774e96f44cc3cb`, with its pre-existing working
  tree edit left untouched). The chosen increment is its executable
  compiler-selected prime and composition with the supplied-prime semantics.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` at
  `7169f0588d58c42f73f5a01a39e2d76add95cc78`. Its new finite-control work
  advances generic machine composition but still supplies no reusable CSP
  encoder, prime search, concrete all-different compiler, or corresponding
  runtime theorem.
- `PhdThesisLean/AllDifferentCSP.lean` now defines the executable finite scan
  `primeCandidates`, `selectPrimeAbove`, and the system-level `compilerPrime`.
  Bertrand's postulate proves the positive-input scan nonempty.
  `selectPrimeAbove_prime` and `lt_selectPrimeAbove` prove primality and
  `q < p`; `selectPrimeAbove_lt_two_mul` proves the strict `p < 2q` bound for
  `q > 1`, while `selectPrimeAbove_zero` and `selectPrimeAbove_one` handle the
  two small edge cases explicitly.
- `compilerPrime_allDifferent_correctness` composes the selected prime with
  `suppliedPrime_allDifferent_correctness`, characterising the global
  minimisers exactly as embedded original minimum-conflict assignments.
  `compilerPrime_globalMin_iff_satisfies_of_satisfiable` gives the exact
  satisfying-assignment characterization in the satisfiable case.
- One proof-shape issue was resolved: the first
  `mem_primeCandidates_iff` simplification left only a conjunction-order goal;
  adding the checked `and_comm` normalization discharged it. No unresolved
  Lean blocker remains in this increment.
- Verification succeeded:
  `lake env lean PhdThesisLean/AllDifferentCSP.lean`, `lake build` (3089 jobs),
  and `git diff --check`. A project Lean-source scan found no `sorry`, `admit`,
  project `axiom`, `unsafe`, or `proof_wanted`; the new `#print axioms` audits
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- `README.md` and `THEOREM_STATUS.md` now record executable prime selection and
  its semantic composition while keeping `cor:all-different-csp` **Partial**.
  The finite output encoding, bit-size bounds, and genuine polynomial-time
  theorem for the complete compiler, including the prime scan, remain open.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes in this repository.
- Best next step: define a finite, computable syntax for the selected-prime
  compiled domains and signed residual rows, prove that its interpretation is
  the checked `compilerPrime` objective, and establish explicit encoded
  output-size bounds before attempting the `TM2ComputableInPolyTime` machine.

## 2026-07-30 05:40 AEST

- Starting repository commit:
  `e086c7bc3a3a6e5314739cbb32738552dcdcd82c` on `main`. The automation began
  with a clean working tree; after fetching, local `HEAD`, `origin/main`, and
  the live remote `refs/heads/main` agreed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` (thesis checkout
  `3829f8caf4b81a07ee5b40901e774e96f44cc3cb`). Its extensive pre-existing
  tracked and untracked work, including the active `body.tex` edit, was left
  untouched.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` at
  `a28b57f2eba67abdfb175d134f683399ac525cd9`. Its checked machine-composition
  work has advanced, but it still provides no reusable CSP encoder,
  prime-search machine, list/pair `FinEncoding`, or complete generic
  `TM2ComputableInPolyTime` composition theorem; mathlib's generic composition
  declaration remains `proof_wanted`.
- Chosen increment: an executable finite selected-prime sparse residual output
  and a semantic bridge from that concrete row list to the existing checked
  all-different objective.
- `PhdThesisLean/AllDifferentCSP.lean` now defines `ResidualRow`,
  `CompiledObjective`, `pinningRows`, `unequalRows`, and `compileObjective`.
  The compiler uses deterministic `Finset.sort` traversals, emits one positive
  row for each relabelled domain entry and one negative unit row for each
  deduplicated primal edge, and stores the already-checked `compilerPrime`.
- `ResidualRow.observation` interprets each output row as a signed weighted
  affine observation. `rowsLoss_compileObjective` proves that summing the
  interpreted finite row list is exactly `suppliedPrimeLoss`.
  `compileObjective_allDifferent_correctness` therefore characterises its
  global minimisers exactly as embedded original minimum-conflict assignments;
  `compileObjective_globalMin_iff_satisfies_of_satisfiable` gives the exact
  satisfying-assignment characterisation in the satisfiable case.
- `compileObjective_rows_length` proves the exact output row count
  `sum_i |D_i| + |E|`, using injectivity of canonical relabelling, and
  `compileObjective_rows_length_le` gives the sparse row-count bound
  `sum_i |D_i| + n^2`. The latter is explicitly documented as a row-count
  result, not a binary bit-size or machine-runtime theorem.
- Resolved proof/API issues: `Finset.toList` was noncomputable at this pinned
  revision, so the executable compiler now uses ordered `Finset.sort`;
  componentwise product order was not total, so primal edges use `Prod.Lex`;
  nested `List.flatMap`/`List.map` sums required small checked helper lemmas
  rather than direct simplification.
- Verification succeeded:
  `lake env lean PhdThesisLean/AllDifferentCSP.lean`, `lake build` (3089 jobs),
  `git diff --check`, and the project Lean-source forbidden-construct scan.
  The new headline `#print axioms` audits report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `README.md` and `THEOREM_STATUS.md` now record the concrete row-list output
  while keeping `cor:all-different-csp` **Partial**. Standard binary
  input/output `FinEncoding`s, encoded bit-size bounds, deterministic
  primality-test runtime, and a genuine whole-compiler
  `TM2ComputableInPolyTime` theorem remain.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated changes in this repository.
- Best next step: define standard binary `FinEncoding`s for a runtime-sized
  explicit CSP syntax and the compiled sparse objective, then prove encoded
  length bounds for variables, relabelled targets, weights, prime, and row
  delimiters before constructing the full compiler machine.

## 2026-07-31 05:30 AEST

- Starting repository commit:
  `d482a10e8f8fa1aa61cab9d27c01c3ca2e456700` on `main`. The automation began
  with a clean working tree; after fetching, local `HEAD`, `origin/main`, and
  the live remote `refs/heads/main` agreed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` (clean thesis checkout
  `b363995058eceabe79c3fbf38d5e34f7c135d8f1`). The chosen increment is the
  standard finite binary representation layer required before a genuine
  machine theorem.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` at
  `a28b57f2eba67abdfb175d134f683399ac525cd9`. It provides checked generic
  `FinEncoding`/`TM2ComputableInPolyTime` wrappers and partial finite-machine
  composition infrastructure, but no concrete list/pair binary encoding,
  all-different compiler, primality-search machine, or completed generic
  polynomial-time composition theorem reusable here.
- Added `PhdThesisLean/AllDifferentCSPEncoding.lean`. `BinaryNatLists` builds a
  self-delimiting codec over the literal alphabet `Bool` using mathlib's
  standard `Computability.encodeNat`, proves decoder/encoder round trips, and
  packages it as a checked `FinEncoding (List (List Nat))`.
- Added runtime-sized `RuntimeSystem`, `RuntimeResidualRow`, and
  `RuntimeObjective` syntax. `RuntimeSystem.finEncoding` and
  `RuntimeObjective.finEncoding` are checked `Bool`-alphabet `FinEncoding`s;
  `RuntimeSystem.toExplicitSystem` connects the runtime input to the existing
  range-checked semantic syntax and preserves nonempty-domain well-formedness.
  `compile` erases the existing checked dependent compiler output into the
  serializable runtime objective.
- `BinaryNatLists.encode_length`,
  `RuntimeSystem.encodedSize_eq_wireSize`, and
  `RuntimeObjective.encodedSize_eq_wireSize` give exact bit counts for the
  chosen binary representation. The actual input bit length is proved to
  dominate variable, domain-entry, and scope-entry counts.
  `compile_rows_length_le_encodedSize_polynomial` then bounds the emitted
  sparse row count by `s + s^2`, where `s` is the actual binary input length.
  This remains deliberately separate from the still-open bound on every
  encoded output field.
- Failed proof shapes resolved during the increment: direct induction on
  `wireSize` did not preserve the changing outer length prefix, so the checked
  proof first bounds the sums of per-element wire sizes; `rw
  [Fin.sum_univ_succ]` did not match the dependent `List.get` sum, while
  `simpa [Fin.sum_univ_succ]` over an explicitly constructed additive bound
  did. No unresolved Lean blocker remains in this increment.
- Verification succeeded: `lake env lean
  PhdThesisLean/AllDifferentCSPEncoding.lean`, `lake build` (3099 jobs),
  `git diff --check`, and the project Lean-source forbidden-construct scan.
  The headline axiom audits contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- `README.md` and `THEOREM_STATUS.md` now record the binary encoding and
  exact-wire-size layer while keeping `cor:all-different-csp` **Partial**.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated changes in this repository.
- Best next step: prove a polynomial bound for
  `(compile C).encodedSize` from the selected-prime, canonical-target,
  pinning-weight, endpoint, and row-count bounds; then implement and verify the
  complete compiler, including deterministic prime selection, using
  `TM2ComputableInPolyTime`.

## 2026-08-01 05:31 AEST

- Starting repository commit:
  `bcee8b59430783383861af369e2d26bbe5caec2b` on `main`. The automation began
  with a clean working tree; after fetching, local `HEAD`, `origin/main`, and
  the live remote `refs/heads/main` agreed, so no fast-forward was needed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` (clean thesis checkout
  `b363995058eceabe79c3fbf38d5e34f7c135d8f1`). The chosen increment is the
  complete encoded-output polynomial bound named by the preceding run.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` at
  `a28b57f2eba67abdfb175d134f683399ac525cd9`. Its checked
  `FinEncoding`/`TM2ComputableInPolyTime` wrappers and partial combined-machine
  infrastructure still provide no reusable all-different compiler,
  prime-search machine, or completed generic polynomial-time composition
  theorem.
- `PhdThesisLean/AllDifferentCSPEncoding.lean` now proves a coarse checked
  bound on mathlib's binary `Computability.encodeNat`, lifts it through the
  self-delimiting list and nested-list frames, and checks bounds for every
  emitted field: variable indices, canonical targets, pinning weights,
  deduplicated-edge endpoints, the selected prime, tags, and length frames.
- `compile_encodedSize_le_polynomial` gives the field-sensitive complete
  wire-size inequality. `compile_encodedSize_le_quartic` packages it as
  `(compile C).encodedSize ≤ 64 * (C.encodedSize + 1)^4`, where the size on the
  right is the actual input encoding length. This is an encoded bit-size
  theorem, not a unit-cell count or a machine-runtime claim.
- Proof-shape issues resolved during the increment: the `PosNum.bit0` branch
  of the binary-length induction needed the explicit positivity theorem
  `PosNum.cast_pos`; membership in `pinningRows` exposes already relabelled
  targets, so their bound is obtained through
  `domainValues_relabeled_eq_Icc` rather than applying `relabelValue` again;
  and literal-list membership needed the empty-tail case simplified before
  substitution. No unresolved Lean error remains in this increment.
- Verification succeeded: `lake env lean
  PhdThesisLean/AllDifferentCSPEncoding.lean`, `lake build` (3099 jobs), and
  `git diff --check`. The project Lean-source scan found no `sorry`, `admit`,
  project `axiom`, `unsafe`, or `proof_wanted`; the new headline `#print
  axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `README.md`, `THEOREM_STATUS.md`, and the source correspondence notes now
  record the full quartic encoded-output bound while keeping
  `cor:all-different-csp` **Partial**. The remaining obligation is a checked
  whole-compiler `TM2ComputableInPolyTime` theorem, including deterministic
  primality testing and selection.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes present.
- Best next step: construct the finite-machine compiler in separately checked
  stages, beginning with the encoded natural/list traversals and a deterministic
  polynomial-time primality/prime-scan component, then compose those stages
  into the final `TM2ComputableInPolyTime` declaration without relying on
  mathlib's `proof_wanted` composition result.

## 2026-08-02 05:27 AEST

- Starting repository commit:
  `15ab85eed9b359af244b967d79c6a507af022524` on `main`. The automation began
  with a clean working tree; after fetching, local `HEAD`, `origin/main`, and
  the live remote `refs/heads/main` agreed, so no fast-forward was needed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` (clean thesis checkout
  `b363995058eceabe79c3fbf38d5e34f7c135d8f1`). The proof still claims a
  deterministic polynomial-time prime scan as part of the complete compiler,
  so this increment does not weaken that obligation or mark the corollary
  complete.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` and its live `main` ref both
  remain at `a28b57f2eba67abdfb175d134f683399ac525cd9`. Its checked finite-control
  and one-step simulation infrastructure still does not supply an encoded CSP
  traversal, primality/prime-scan machine, or completed generic
  `TM2ComputableInPolyTime` composition theorem reusable here.
- Chosen increment: begin the genuine machine layer with the natural-field
  framing pass used throughout the runtime CSP and objective encodings.
  `PhdThesisLean/AllDifferentCSPMachine.lean` adds the exact framed-natural
  `FinEncoding`, a concrete four-stack Boolean `FinTM2`, and checked phase
  simulations for stashing the payload, restoring it, and prefixing its unary
  bit length and separator.
- Headline declaration:
  `AllDifferentCSPMachine.framedNatComputableInPolyTime` is a genuine
  `TM2ComputableInPolyTime` witness from mathlib's raw binary natural encoding
  to the self-delimiting natural encoding used by this compiler. The machine
  computes the identity on natural numbers while carrying out the nontrivial
  wire-format conversion in exactly `3s + 3` machine steps for raw payload
  length `s`. `frame_outputsInTime` records the exact arbitrary-bit-string
  execution bound, including the empty payload case.
- Proof/API issues resolved: TM2 evaluation evidence is data in `Type`, so the
  recursive executions must be defined with `def`, not declared as theorems;
  repeated `Function.update` stack equalities required extensional proofs by
  the four stack constructors; homogeneous unary prefixes needed an explicit
  replicate/cons commuting lemma; and `Equiv.refl` had to be unfolded when
  discharging the input/output alphabet maps in the final machine witness.
  Initial direct `rfl` attempts and an over-aggressive `simp` did not close
  those goals, but no blocker remains.
- Correspondence/status updates: imported the machine module from
  `PhdThesisLean.lean` and updated `README.md`, `THEOREM_STATUS.md`, and the
  CSP/encoding module notes. `cor:all-different-csp` remains **Partial**:
  whole-list/CSP traversals, deterministic primality testing and prime
  selection, and final finite-machine composition are still required.
- Verification succeeded: targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3105 jobs);
  `git diff --check`; and the project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. The new `#print axioms`
  audits report only `propext`, `Classical.choice`, and `Quot.sound`.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes in this repository.
- Best next step: construct a checked polynomial-time traversal for the
  length-prefixed natural-list layer using the framed-natural pass, then use
  the same finite-machine discipline for deterministic binary arithmetic,
  primality testing, and the Bertrand-interval prime scan before final compiler
  assembly.

## 2026-08-03 05:31 AEST

- Starting repository commit:
  `3d93751e0c8bbd79ee7e32f7d225762534e9f90e` on `main`. The automation began
  with a clean working tree; after fetching, local `HEAD`, `origin/main`, and
  the live remote `refs/heads/main` agreed, so no fast-forward was needed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` (clean thesis checkout
  `b363995058eceabe79c3fbf38d5e34f7c135d8f1`). The proof still requires a
  deterministic polynomial-time prime scan and a whole-compiler machine; this
  increment does not weaken those obligations or mark the corollary complete.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` and its live `main` ref have
  advanced to `1e90d19f6c58deec211e7e878ca439ae5bf38ac8`. The new checked
  `liftRightControl_step` completes exact one-step simulation of the second
  component in combined control, but the generic transfer loop, multi-step
  composition, and polynomial runtime theorem remain pending; it still has no
  reusable list serializer, binary arithmetic, primality test, or prime scan.
- Chosen increment: the next finite-machine wire-format layer.
  `FramedNatList.finEncoding` packages the compiler's exact length-prefixed
  framed natural-list codec. `RawNatList.finEncoding` gives a checked,
  executable stack-oriented source codec whose natural fields and bits are
  reversed and explicitly delimited, matching how a stack compiler can
  accumulate output fields.
- Headline declaration:
  `AllDifferentCSPMachine.framedNatListComputableInPolyTime` is a genuine
  `TM2ComputableInPolyTime` witness. Its concrete heterogeneous three-stack
  machine traverses every raw field, restores bit and field order, prefixes
  every field with its unary bit length, and emits exactly
  `BinaryNatLists.encodeNatList xs` in at most `3s` steps for raw input length
  `s`. `listFrame_outputsInTime` checks the full execution, including empty
  naturals and the empty list.
- Proof/API issues resolved: the dependent input alphabet needed an explicit
  `Fintype (Option Bool)` witness; the previous one-step evaluation helper was
  specialized to `frameComputer`, so this machine needed its own checked
  helper; this Lean revision uses list nonemptiness as `xs ≠ []` rather than a
  `List.Nonempty` proposition; and the nested `EvalsToInTime.trans` bounds
  needed an explicit monotonicity lemma plus normalized `omega` arithmetic.
  Initial direct inference/reuse attempts failed at those exact boundaries,
  but no blocker remains in this increment.
- Correspondence/status updates: synchronized the machine module notes,
  `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md`. `cor:all-different-csp` remains **Partial**: the new
  theorem serializes natural lists but does not yet traverse the nested CSP
  input, perform binary arithmetic or primality testing, select the prime in a
  checked runtime, or assemble the whole compiler machine.
- Verification succeeded: targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3105 jobs);
  `git diff --check`; and the project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. The new `#print axioms`
  audits report only `propext`, `Classical.choice`, and `Quot.sound`.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes in this repository.
- Best next step: construct a checked traversal that exposes each framed field
  of `BinaryNatLists.encode` to subsequent finite-machine passes, then add
  deterministic binary increment/comparison as the first arithmetic component
  needed by canonical relabelling and the Bertrand-interval prime scan.

## 2026-08-04 05:29 AEST

- Starting repository commit:
  `33d737d33671dfc9ad3298113450087c1c2bb0fc` on `main`. The automation began
  with a clean working tree; after fetching, local `HEAD`, `origin/main`, and
  the live remote `refs/heads/main` agreed, so no fast-forward was needed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` (clean thesis checkout
  `b363995058eceabe79c3fbf38d5e34f7c135d8f1`). The proof still requires the
  complete deterministic compiler, including prime selection, so this run
  keeps `cor:all-different-csp` **Partial**.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` and its live `main` ref have
  advanced to `d56e608fa83fac95d89ae9ceac17b8173242909d`. Its new
  `liftLeftThenTransfer_step` redirects a first component's halt into transfer
  control, but the transfer loop, multi-step composition, and polynomial
  runtime theorem remain pending; it still supplies no reusable CSP traversal,
  binary arithmetic, primality test, or prime scan.
- Chosen increment: expose the standard nested-list input's fields to later
  compiler passes. `RawNatLists.finEncoding` is a checked stack-oriented codec
  containing the outer length, every inner length, and every value as raw
  binary payloads with explicit delimiters. Its round trip restores the exact
  `BinaryNatLists.encode` stream.
- Headline declaration:
  `AllDifferentCSPMachine.unframedNatListsComputableInPolyTime` is a genuine
  `TM2ComputableInPolyTime` witness from the standard `Bool` nested-list
  encoding to the raw-field encoding. Its concrete heterogeneous three-stack
  machine scans each unary prefix, copies the counted payload, reverses fields
  into stack order, and emits `RawNatLists.encode xss` in at most `3s` steps
  for standard input length `s`. The proof includes zero-length binary fields,
  empty inner lists, and the empty outer list.
- Proof issues resolved: a pipeline expression in a theorem type was rejected
  at the parser boundary and was replaced by an explicit `List.flatMap`; the
  raw-payload/framed-payload equality required an explicit function equality
  between raw framing and `BinaryNatLists.encodeNat`; and the final recursive
  execution bounds needed separate `omega` equalities before configuration
  simplification. No unresolved Lean error remains in this increment.
- Correspondence/status updates: synchronized the machine module notes,
  `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md`. The remaining obligations are CSP structural
  compilation, binary arithmetic, deterministic primality testing and prime
  selection, and final whole-machine assembly.
- Verification succeeded: targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3105 jobs);
  `git diff --check`; and the project Lean-source scans for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. The new `#print axioms` audits
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes in this repository.
- Best next step: add a checked raw-binary increment/comparison pass over the
  exposed fields, then use it for deterministic candidate enumeration before
  implementing divisibility/primality testing and the Bertrand-interval scan.

## 2026-08-05 05:27 AEST

- Starting repository commit:
  `80391839c54bbf12f65730289d0d6aeb0afa5d59` on `main`. The automation began
  with a clean working tree; after fetching, local `HEAD`, `origin/main`, and
  the live remote `refs/heads/main` agreed, so no fast-forward was needed. The
  automation memory file was absent, so continuity was reconstructed from this
  log, theorem status, recent commits, and the repository sources.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` in thesis checkout
  `f8161beb7546aafe3fdd85aa61b18a5917a7d00f`. That sibling checkout already had
  unrelated modifications to `.gitignore` and `todo.md`; this automation did
  not alter them. The thesis proof still requires deterministic primality
  testing, prime scanning, and the complete compiler machine, so
  `cor:all-different-csp` remains **Partial**.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` and its live `main` ref agreed
  at `6473f3bc46d10d2ea34d8ca1009b612cda47ae5d`. Its new scratch-stack layout
  supports the unfinished generic machine transfer construction, but it still
  has no reusable checked binary arithmetic, primality test, prime scan, or
  completed polynomial-time composition theorem.
- Chosen increment: the first checked arithmetic primitive needed by candidate
  enumeration. `binarySuccBits` defines carry propagation on mathlib's
  least-significant-bit-first binary words and
  `binarySuccBits_encodeNat` proves that it emits exactly `encodeNat (n + 1)`,
  including the empty encoding of zero and carry growth.
- Headline declaration:
  `AllDifferentCSPMachine.binarySuccComputableInPolyTime` is a genuine
  `TM2ComputableInPolyTime` witness from `finEncodingNatBool` to itself. Its
  concrete three-stack `FinTM2` propagates carry, copies the untouched suffix,
  restores canonical bit order, and halts in at most `2s + 3` steps for input
  length `s`. `binarySucc_outputsInTime` checks the stronger arbitrary-bit-word
  execution claim.
- Files changed: `PhdThesisLean/AllDifferentCSPMachine.lean` adds the executable
  machine, phase simulations, semantic connection, runtime bound, and axiom
  audits. `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` now distinguish the completed successor primitive from
  the remaining arithmetic and whole-compiler obligations.
- One failed proof attempt supplied useful evidence: leaving the target time of
  `evalsToInTimeMono` implicit produced an unresolved upper-bound metavariable,
  so `omega` reported a possible counterexample at the final runtime bound.
  Giving the result the explicit `2 * bits.length + 3` type exposed the intended
  inequality and closed it using `binarySuccBits_length_le`. No blocker remains
  in this increment.
- Verification succeeded: targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3105 jobs);
  `git diff --check`; and the project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. The new `#print axioms` audits
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes in this repository.
- Best next step: add a checked polynomial-time comparison pass for canonical
  binary naturals, then combine successor and comparison for bounded candidate
  enumeration before divisibility, deterministic primality testing, and the
  Bertrand-interval prime scan.

## 2026-08-06 05:33 AEST

- Starting repository commit:
  `ef0e13ed2f2ffb451f2793ade3c3705084e8f821` on `main`. The automation began
  with a clean working tree; after fetching, local `HEAD`, `origin/main`, and
  the live remote `refs/heads/main` agreed, so no fast-forward was needed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` in thesis checkout
  `f8161beb7546aafe3fdd85aa61b18a5917a7d00f`. That sibling checkout retains
  unrelated modifications to `.gitignore` and `todo.md`; this automation did
  not alter them. The proof still requires deterministic primality testing,
  prime scanning, and the complete compiler machine, so
  `cor:all-different-csp` remains **Partial**.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` and its live `main` ref agree
  at `745b81a3f188e12060ffccbfba979740abcb9f25`. Its latest checked work lifts
  the two component programs into the combined scratch-stack layout, but the
  transfer loop, complete composition theorem, and polynomial runtime proof
  remain unfinished; it still has no reusable checked comparison, division,
  primality test, or prime scan.
- Chosen increment: the next binary arithmetic primitive needed for bounded
  candidate enumeration. `BinaryNatPair.finEncoding` is a checked finite
  aligned-pair encoding that preserves both mathlib canonical binary natural
  words, including zero and unequal-length inputs. `binaryLEBitsAux_encodeNat`
  proves that the least-to-most-significant comparison fold emits exactly
  `decide (left ≤ right)`.
- Headline declaration:
  `AllDifferentCSPMachine.binaryLEComputableInPolyTime` is a genuine
  `TM2ComputableInPolyTime` witness from `BinaryNatPair.finEncoding` to
  `finEncodingBoolBool`. Its concrete two-stack `FinTM2` scans one aligned bit
  pair per step, lets each more significant unequal bit replace the earlier
  decision, handles exhausted sides explicitly, and emits the comparison bit
  in `s + 1` steps for encoded input length `s`. `binaryLE_outputsInTime`
  records the exact machine execution bound.
- Files changed: `PhdThesisLean/AllDifferentCSPMachine.lean` adds the encoding,
  semantic comparison proof, finite machine, exact runtime proof, polynomial
  witness, and axiom audits. `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` now distinguish the completed comparison primitive from
  the remaining arithmetic and whole-compiler obligations.
- Failed proof/API approaches supplied two useful corrections. First,
  simplifying `List.filterMap Prod.fst` and `Prod.snd` through the dependent
  aligned recursion left unhelpful membership goals, so the checked decoder
  projections were replaced by direct structural recursions. Second, a final
  `.halt` retains finite control rather than restoring `initialState`; the
  output branch therefore now pushes the stored decision and then explicitly
  loads `compareInitialState`, making its final configuration exactly
  `haltList`. No blocker remains in this increment.
- Verification succeeded: targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3105 jobs);
  `git diff --check`; and the project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. The new headline
  `#print axioms` audits report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes in this repository.
- Best next step: combine the checked successor and comparison primitives into
  bounded candidate enumeration, then add binary remainder/divisibility and a
  deterministic primality predicate before proving the Bertrand-interval
  prime scan's machine runtime.

## 2026-08-07 05:29 AEST

- Starting repository commit:
  `cc9c0762a79d6a80b67ffa915077f03022dc3111` on `main`. The automation began
  with a clean working tree; after fetching, local `HEAD`, `origin/main`, and
  the live remote `refs/heads/main` agreed, so no fast-forward was needed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` in thesis checkout
  `f8161beb7546aafe3fdd85aa61b18a5917a7d00f`. That sibling checkout retains
  unrelated modifications to `.gitignore` and `todo.md`; this automation did
  not alter them. The proof still requires a deterministic polynomial-time
  prime scan and the complete compiler machine, so
  `cor:all-different-csp` remains **Partial**.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean at
  `5bcaa737ed38c260124506e1e0aad080c93edd5b`. Its latest checked increment
  verifies the reverse-output loop of the unfinished generic machine transfer,
  but the fill-input phase, complete composition theorem, and polynomial
  runtime proof remain pending; it still provides no reusable binary
  arithmetic, divisibility, primality test, or prime scan.
- Chosen increment: checked binary addition, which constructs the Bertrand
  interval endpoint `2q` and supplies ripple-carry arithmetic needed by later
  bounded enumeration. `binaryAddBitsAux_encodeNat` proves that the aligned
  least-significant-bit-first fold emits exactly `encodeNat (left + right)`,
  including zero operands and a final carry bit.
- Headline declaration:
  `AllDifferentCSPMachine.binaryAddComputableInPolyTime` is a genuine
  `TM2ComputableInPolyTime` witness from `BinaryNatPair.finEncoding` to
  `finEncodingNatBool`. Its concrete three-stack `FinTM2` scans each aligned
  pair once, stores only the current carry in finite control, reverses the work
  stack into canonical output order, and halts in at most `2s + 3` steps for
  paired input length `s`. `binaryAdd_outputsInTime` records the stronger
  execution bound and exact output.
- Files changed: `PhdThesisLean/AllDifferentCSPMachine.lean` adds the semantic
  ripple-carry fold, finite machine, phase simulations, runtime bound,
  polynomial witness, and axiom audits. `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` now distinguish checked addition from the remaining
  bounded-enumeration, remainder/divisibility, primality, and assembly work.
- Failed proof approaches supplied three useful corrections. Expressing the
  finite addition truth table through arithmetic counts left opaque `if` and
  `decide` terms under structural rewriting, so it was replaced by an explicit
  exhaustive finite-control table. Direct simplification of `PosNum.add` did
  not expose its constructor cases, so the semantic proof now states each
  normalized constructor target explicitly. Finally, the runtime inequality
  initially left the local `result` abbreviation opaque to `omega`; changing
  the checked length bound to `result.length ≤ input.length + 1` exposed the
  required relation. No blocker remains in this increment.
- Verification succeeded: targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3105 jobs);
  `git diff --check`; and the project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. The new headline
  `#print axioms` audits report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes in this repository.
- Best next step: use successor, comparison, and addition to build a checked
  bounded candidate enumerator for `[q + 1, 2q]`; then add binary
  remainder/divisibility and a deterministic primality predicate before
  proving the Bertrand-interval prime scan's machine runtime.

## 2026-08-08 05:33 AEST

- Starting repository commit:
  `56492c3c020aa2be22d025036dbebadd10a9713d` on `main`. The automation began
  with a clean working tree; `git fetch --prune origin` confirmed local
  `HEAD` and `origin/main` had divergence count `0 0`, and the live remote
  `refs/heads/main` agreed, so no fast-forward was needed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` in thesis checkout
  `f8161beb7546aafe3fdd85aa61b18a5917a7d00f`. That sibling checkout retains
  unrelated modifications to `.gitignore` and `todo.md`; this automation did
  not alter them. The proof still requires deterministic primality testing,
  prime filtering/selection, structural compiler composition, and the complete
  polynomial-time machine, so `cor:all-different-csp` remains **Partial**.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and agreed with its
  tracked remote at `3f2ccabb51f9804e403ccb4b3046805e17c269db`. Its latest
  checked increment verifies the fill-input transfer iteration, but the full
  generic composition program, semantic simulation, and polynomial runtime
  theorem remain unfinished. It still supplies no reusable remainder,
  divisibility, primality-test, or prime-scan implementation.
- Chosen increment: checked enumeration of the complete Bertrand interval.
  `intervalFrom`, `bertrandCandidates`, and
  `mem_bertrandCandidates_iff` define and characterize exactly the `q`
  candidates in `[q + 1, 2q]`, including the empty `q = 0` case and the
  singleton `q = 1` case.
- Headline declaration:
  `AllDifferentCSPMachine.bertrandCandidatesComputableInPolyTime` is a genuine
  `TM2ComputableInPolyTime` witness from mathlib's `unaryFinEncodingNat` to
  `RawNatList.finEncoding`. Its concrete five-stack finite machine counts the
  unary bound into canonical binary, preserves a unary iteration copy,
  repeatedly increments and emits raw binary fields, clears every non-output
  stack, and produces exactly the checked encoding of
  `[q + 1, ..., 2q]` in at most `16 * (q + 1)^2` steps.
- The unary input is a statement-faithful interface, not a weakened complexity
  claim: enumerating `q` explicit candidates is not polynomial in the bit
  length of standalone binary `q`. The eventual structural pass must produce
  the unary distinct-symbol bound while scanning the full explicit CSP input,
  whose bit length is already at least `q`. README and theorem-status notes now
  state this boundary explicitly.
- Files changed: `PhdThesisLean/AllDifferentCSPMachine.lean` adds the interval
  semantics, finite enumerator, phase simulations, exact output connection,
  quadratic runtime bound, polynomial witness, and axiom audits.
  `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` distinguish completed unary-bound enumeration from
  unary-bound production and the remaining prime-selection and assembly work.
- Failed proof/design approaches supplied useful corrections. Treating binary
  `q` as the standalone input would make explicit interval enumeration
  exponential in input bit length, so the machine was redesigned around the
  full-compiler unary-bound invariant. The first recursive interval clause
  needed parentheses around `current + 1` to avoid parsing addition against a
  list. Core Lean did not expose a `List.reverse_map` theorem under the assumed
  name, so the exact raw-output proof now uses a checked structural induction
  for reversed mapped fields. No blocker remains in this increment.
- Verification succeeded: targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3105 jobs);
  `git diff --check`; and the project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. The new headline
  `#print axioms` audits report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes in this repository.
- Best next step: implement checked binary remainder/divisibility on canonical
  naturals, then use it for deterministic trial-division primality filtering
  over the enumerated candidates. Structural production of the unary
  distinct-symbol bound and final machine composition remain separate
  obligations.

## 2026-08-09 05:38 AEST

- Starting repository commit:
  `bec29346b0a82480c96242ad5e4463c0746776a2` on `main`. The automation began
  with a clean working tree; `git fetch --prune origin` confirmed divergence
  count `0 0`, and local `HEAD`, `origin/main`, and the live remote
  `refs/heads/main` agreed, so no fast-forward was needed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` in thesis checkout
  `67aeb9bddf458fd79182470a70a17952bcc305a1`. That checkout retains unrelated
  modifications to `.gitignore` and `todo.md`; this automation did not alter
  them. The proof still requires deterministic primality testing, candidate
  filtering/selection, structural compiler composition, and the complete
  polynomial-time machine, so `cor:all-different-csp` remains **Partial**.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and agreed with its
  tracked remote at `d675fe391b9f19684d90a983082e87d6d0bf5a1c`. Its latest
  checked increment proves whole-list fill-input transfer, but generic
  composition remains unfinished and it still supplies no reusable
  remainder, divisibility, primality-test, or prime-scan implementation.
- Chosen increment: checked divisibility on unary-padded natural pairs. This is
  the shortest statement-faithful route after the existing unary Bertrand
  interface: every candidate and trial divisor is `O(q)`, while the full CSP
  input establishes `q ≤ s`. The result is deliberately not presented as a
  polynomial-time theorem for standalone binary integers.
- `UnaryNatPair.finEncoding` gives a checked delimiter-separated encoding with
  exact length `n + d + 1`. The concrete five-stack `unaryDvdComputer`
  cyclically partitions one divisor copy between `remaining` and `used`,
  restores it between cycles, clears every non-output stack, and handles
  `0 ∣ 0`, `0 ∣ n` for positive `n`, and `d ∣ 0` explicitly.
- Headline declarations:
  `AllDifferentCSPMachine.unaryDvd_outputsInTime` proves the concrete machine
  emits exactly `decide (d ∣ n)` in at most `6s + 16` steps for actual input
  length `s`; `unaryDvdComputableInPolyTime` packages this as a genuine
  `TM2ComputableInPolyTime` witness. The cycle proof covers exact, partial, and
  repeated divisor cycles rather than appealing to an unchecked arithmetic
  oracle.
- Files changed: `PhdThesisLean/AllDifferentCSPMachine.lean` adds the encoding,
  finite program, exact step simulations, divisibility semantics, runtime
  bound, polynomial witness, and axiom audits. `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` record the padded interface and keep the full corollary
  open.
- Failed/design approaches supplied useful corrections. A standalone binary
  remainder machine was not pursued because it is unnecessary for the checked
  full-input padding invariant and would lengthen the path to prime filtering.
  In the proof, `Nat.strong_induction_on` rejected the Type-valued
  `EvalsToInTime` motive, so the checked definition uses `Nat.strongRecOn`;
  eliminating `Nat.exists_eq_succ_of_ne_zero` into that Type-valued motive was
  also rejected, so positive remainders are decomposed constructively with
  `Nat.pred` and `Nat.succ_pred_eq_of_pos`. No unresolved Lean blocker remains.
- Verification succeeded: targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3105 jobs);
  `git diff --check`; and the project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. The new headline
  `#print axioms` audits report only `propext`, `Classical.choice`, and
  `Quot.sound` (the pair decoder itself uses only `propext`).
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes present in this repository.
- Best next step: build a checked deterministic trial-division primality
  predicate over unary-padded candidates and divisors, then filter/select the
  first prime in the already checked Bertrand interval. Structural production
  of the padded distinct-symbol bound and final compiler composition remain
  separate obligations.

## 2026-08-10 05:28 AEST

- Starting repository commit:
  `a3b36cd28d043651c008cd09130e9b27df2db133` on `main`. The automation began
  with a clean working tree; `git fetch --prune origin` confirmed divergence
  count `0 0`, and local `HEAD`, `origin/main`, and the live remote
  `refs/heads/main` agreed, so no fast-forward was needed. The two commits
  since the preceding CSP run formalise the separate precision-growth queue
  and were preserved unchanged.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` in thesis checkout
  `5294a3754f4987514ed9f03e73658df37a684156`. That checkout retains unrelated
  modifications to `.gitignore` and `todo.md`; this automation did not alter
  them. The proof still requires a genuine polynomial-time whole compiler, so
  `cor:all-different-csp` remains **Partial**.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized at
  `2a95106fdfa11258046ce9457d65536407942def`. Its checked
  `reverseOutput_whole_list` and `fillInput_whole_list` transfer lemmas are
  useful future composition components, but a complete generic composition
  theorem and reusable primality/filtering machine are still absent.
- Chosen increment: the exact executable deterministic trial-division and
  first-prime specification that the next finite-machine pass must realize.
  `trialDivisors` enumerates precisely `[2,n)`, and
  `trialPrime_eq_true_iff` proves that its bounded `List.all` divisibility test
  is equivalent to `Nat.Prime`, including `n = 0,1,2`.
- `trialDivisionPairs` gives the exact unary-padded inputs to the existing
  divisibility machine. Every pair has length at most `2n`, and
  `trialDivisionInputSize_le` bounds their aggregate unary cell count by
  `2 * n * (n - 2)`. This is deliberately recorded as an input-size lemma,
  not misrepresented as a bit-level or machine-runtime theorem.
- `bertrandPrimeCandidates` filters the already checked ordered list
  `[q+1,...,2q]`. `mem_bertrandPrimeCandidates_iff` proves exact membership,
  `pairwise_lt_bertrandPrimeCandidates` proves the survivors remain strictly
  ordered, and `firstBertrandPrime` handles `q = 0` explicitly before taking
  the first survivor for positive `q`.
- Headline declaration:
  `firstBertrandPrime_eq_selectPrimeAbove` proves that this executable
  first-survivor trial-division scan returns exactly the least prime already
  used by the semantic compiler. Consequently the checked prime bounds and
  the existing p-adic minimizer theorems apply without changing the compiled
  objective.
- Files changed: `PhdThesisLean/AllDifferentCSPMachine.lean` adds the trial
  specification, exact semantics, padding bounds, filtered scan, selector
  equality, and axiom audits. `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` record the completed semantic bridge while keeping the
  finite-machine filter and full corollary open.
- Failed proof/API probes supplied useful corrections. Mathlib at the pinned
  revision has no `List.rel_get_of_lt`; the least-head argument is instead a
  checked structural lemma over `List.pairwise_cons`. `Finset.min'_le` takes a
  candidate and membership proof rather than an explicit nonemptiness proof,
  so the selector equality unfolds the positive branch and uses exact filtered
  membership. No blocker remains in this increment.
- Verification succeeded: targeted `lake env lean` checks for
  `AllDifferentCSP.lean`, `AllDifferentCSPEncoding.lean`, and
  `AllDifferentCSPMachine.lean`; full `lake build` (3114 jobs);
  `git diff --check`; and the project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. New `#print axioms` audits for
  `trialPrime_eq_true_iff`, `trialDivisionInputSize_le`,
  `mem_bertrandPrimeCandidates_iff`, and
  `firstBertrandPrime_eq_selectPrimeAbove` report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes present in this repository.
- Best next step: implement a concrete finite-machine loop that generates the
  padded trial pairs, realizes `trialPrime` with `unaryDvdComputer`, filters
  the ordered Bertrand stream, and emits its first survivor. Keep structural
  CSP bound production and final whole-compiler composition as later,
  separately audited obligations.
