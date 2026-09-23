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

## 2026-08-11 05:47 AEST

- Starting repository commit:
  `345c1437a501a7d434cc22448c4368286ea1b74f` on `main`. The automation began
  with a clean working tree; `git fetch --prune origin` confirmed divergence
  count `0 0`, and local `HEAD`, `origin/main`, and the live remote
  `refs/heads/main` agreed, so no fast-forward was needed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` in thesis checkout
  `5294a3754f4987514ed9f03e73658df37a684156`. That checkout retains unrelated
  modifications to `.gitignore` and `todo.md`; this automation did not alter
  them. The proof still requires a genuine polynomial-time whole compiler, so
  `cor:all-different-csp` remains **Partial**.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized at
  `516000d`. Its new `MachineComposition.transfer_whole_list` gives a checked
  order-preserving intermediate-stack transfer, but the total composed
  `FinTM2`, multi-step component simulation, and polynomial runtime theorem
  remain pending. It still supplies no reusable trial-filter or prime-scan
  machine.
- Chosen increment: finite-machine production of the complete unary-padded
  trial-division input list for one candidate. `RawUnaryPairList.finEncoding`
  gives the stack-oriented pair stream a checked `Option Bool` alphabet and
  `RawUnaryPairList.decode_encode` proves exact round-trip decoding.
- Headline declarations:
  `trialDivisionPairs_outputsInTime` proves that the concrete six-stack
  `trialDivisionPairComputer` emits exactly
  `[(n,2), ..., (n,n-1)]` in at most `8 * (n + 1)^2` steps from unary `n`.
  The proof explicitly handles the empty `n = 0,1,2` cases, preserves the
  dividend while emitting each delimited pair, increments the unary divisor,
  and clears every non-output stack. `trialDivisionPairsComputableInPolyTime`
  packages this execution as a genuine `TM2ComputableInPolyTime` witness from
  `unaryFinEncodingNat` to `RawUnaryPairList.finEncoding`.
- Files changed: `PhdThesisLean/AllDifferentCSPMachine.lean` adds the checked
  pair-list encoding, concrete finite program, phase simulations, exact list
  semantics, quadratic runtime bound, polynomial witness, and axiom audits.
  `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` record that padded-pair generation is complete while
  repeated divisibility, Boolean aggregation, candidate filtering/selection,
  structural bound production, and final assembly remain open.
- Failed proof approaches supplied a useful audit correction. The first
  emission proof left exact time normalisation and the unary/pair-encoding
  bridge unresolved; Lean continued elaboration with `sorryAx`, which the new
  headline `#print axioms` audit exposed. The proof was split into checked
  phase-composition lemmas, the time equalities were normalised explicitly
  with `two_mul`, and `unaryEncodeNat_eq_replicate` now connects mathlib's
  unary input to the pair encoder. The final declarations have no `sorryAx`
  dependency.
- Verification succeeded: targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3114 jobs);
  `git diff --check`; and the project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. New `#print axioms` audits for
  `RawUnaryPairList.decode_encode`, `trialPairsFrom_sub_two`,
  `trialDivisionPairs_outputsInTime`, and
  `trialDivisionPairsComputableInPolyTime` report only `propext`,
  `Classical.choice`, and `Quot.sound` (the encoding round trip omits
  `Classical.choice`, and the exact list identity uses only `propext`).
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes present in this repository.
- Best next step: drive `unaryDvdComputer` repeatedly over the checked padded
  pair stream, aggregate its Boolean results into exact `trialPrime`, and then
  use that checked predicate to filter the ordered Bertrand candidates and
  emit the first survivor. Structural production of the unary distinct-symbol
  bound and final compiler composition remain separate later obligations.

## 2026-08-12 05:26 AEST

- Starting repository commit:
  `73b1ffa6bbaf3ae0331b17594a67997959e1c03f` on `main`. The automation began
  with a clean working tree; `git fetch --prune origin` confirmed that local
  `HEAD`, `origin/main`, and the live remote `refs/heads/main` agreed, so no
  fast-forward was needed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` in thesis checkout
  `5294a3754f4987514ed9f03e73658df37a684156`. Its unrelated modifications to
  `.gitignore` and `todo.md` were left untouched. The complete corollary still
  requires a genuine polynomial-time whole compiler, including compiler-owned
  prime selection.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized at
  `85c5c181662b2d33eb71b3a22e8a05bd44d2810c`. Its new
  `MachineComposition.compositionMachine` constructs the total finite machine
  for sequential composition and proves one-step component simulations, but
  deliberately supplies no computation or polynomial-runtime theorem yet. It
  therefore cannot discharge this run's repeated prime-test composition
  obligation without additional checked runtime work.
- Chosen increment: the Boolean aggregation pass that follows repeated padded
  divisibility. `RawBoolList.finEncoding` gives the intermediate result stream
  a literal checked Boolean-list encoding; `trialDivisionResults` fixes the
  exact per-pair result contract; and
  `allFalse_trialDivisionResults_eq_true_iff` proves that for every `n ≥ 2`,
  accepting precisely when every divisibility result is false is equivalent to
  `n.Prime`.
- Headline machine declarations: `allFalse_outputsInTime` proves the concrete
  two-stack `allFalseComputer` emits the exact aggregate in at most `s + 1`
  steps for result-list length `s`;
  `allFalseComputableInPolyTime` packages this as a genuine linear
  `TM2ComputableInPolyTime` witness. Empty lists are accepted, as required for
  the prime candidate `n = 2`; the separate lower-bound conjunct in
  `trialPrime_eq_lowerBound_and_allFalse` handles `n = 0,1` faithfully.
- Files changed: `PhdThesisLean/AllDifferentCSPMachine.lean` adds the checked
  result semantics, finite machine, exact execution proof, polynomial witness,
  and axiom audits. `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` record Boolean aggregation as checked while keeping
  `cor:all-different-csp` **Partial**.
- Failed proof shapes supplied useful corrections. The first semantic equality
  omitted parentheses around a Boolean conjunction, so Lean parsed it as a
  proposition-valued conjunction; the corrected statement makes the Boolean
  equality explicit. The first transition proofs also needed function
  extensionality for stack updates, and the output proof needed to normalize
  `encodeBool`'s list `pure` to a singleton before rewriting `haltList`. The
  initial targeted check consequently reported `sorryAx` in the unfinished
  declarations; after these changes, the declarations elaborate with no
  `sorryAx` dependency.
- Verification succeeded: targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3114 jobs);
  `git diff --check`; and a project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. New `#print axioms` audits for
  `allFalse_trialDivisionResults_eq_true_iff`, `allFalse_outputsInTime`, and
  `allFalseComputableInPolyTime` report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes present in this repository.
- Best next step: implement the finite-machine driver that consumes
  `RawUnaryPairList`, invokes the checked divisibility logic for every pair,
  and emits `trialDivisionResults`; then compose that driver with
  `allFalseComputer` and the lower-bound check to realize `trialPrime` before
  filtering the ordered Bertrand candidate stream.

## 2026-08-13 05:42 AEST

- Starting repository commit:
  `167ef534efc7e433372d7d2707bdadde21d21fab` on `main`. The automation began
  with a clean working tree; `git fetch --prune origin` confirmed divergence
  count `0 0`, so no fast-forward was needed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` in thesis checkout
  `5294a3754f4987514ed9f03e73658df37a684156`. Its unrelated modifications to
  `.gitignore` and `todo.md` were preserved. The proof still claims a genuine
  polynomial-time compiler-owned prime scan and whole compiler, so
  `cor:all-different-csp` remains **Partial**.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized at
  `41bbee6e21b1d19f397cf8539d47955eab0cc4f4`. Its structural composition
  machine now proves the complete order-preserving transfer under the total
  program, but still has no theorem that the composed machine computes the
  composed function or runs in polynomial time. This increment therefore used
  a concrete checked component lift without editing or importing the sibling.
- Chosen increment: repeated divisibility across the complete padded pair
  stream. `pairDvdComputer` restores each reversed raw field on the existing
  `unaryDvdComputer` input stack, executes that checked program, redirects its
  halt to the next field, and pushes results so their final order matches the
  source pair order.
- Headline declarations: `pairDvd_outputsInTime` proves exact output
  `pairDivisionResults pairs` in at most `17s + 1` steps for actual
  `RawUnaryPairList` encoded length `s`;
  `pairDivisionResultsComputableInPolyTime` packages the concrete finite
  machine as a genuine `TM2ComputableInPolyTime` witness. The proof includes
  empty streams, arbitrary pairs (including zero cases inherited from the
  component checker), exact outer/inner reversal restoration, component-state
  cleanup, and complete result order.
- Size bridge: `RawUnaryPairList.encode_length` counts every padded payload and
  field separator exactly, while `trialDivisionPairStream_length_le` bounds the
  concrete stream for candidate `n` by `(2 * n + 1) * (n - 2)`. Thus the new
  linear driver and the existing quadratic pair generator expose compatible
  checked representations; their machine-level composition remains separate.
- Files changed: `PhdThesisLean/AllDifferentCSPMachine.lean` adds the reusable
  output-preserving divisibility execution, outer driver, simulations, exact
  semantics, runtime and size bounds, polynomial witness, and axiom audits.
  `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` record the completed standalone repeated-divisibility
  stage without claiming the whole corollary.
- Failed proof/API shapes supplied useful corrections. Generalizing the
  component execution initially passed one extra list to
  `dvd_step_start_positive_zero`. The first iteration simulation used
  `Function.iterate_succ_apply'`, which exposes the last rather than first
  step; `Function.iterate_succ_apply` and a separate `unaryDvd_iterate_none`
  lemma established the needed forward simulation. The raw-separator step also
  required an explicit dependent stack-family extensionality proof. Targeted
  checks exposed temporary `sorryAx` dependencies while these goals were open;
  every such dependency was removed before the final checks.
- Verification succeeded: targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3114 jobs);
  `git diff --check`; and the project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. New `#print axioms` audits for
  `RawUnaryPairList.encode_length`, `trialDivisionPairStream_length_le`,
  `pairDvd_outputsInTime`, and
  `pairDivisionResultsComputableInPolyTime` report only `propext`,
  `Classical.choice`, and `Quot.sound` (the exact encoding-length identity
  omits `Classical.choice`).
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated changes in this repository.
- Best next step: compose `trialDivisionPairsComputableInPolyTime`,
  `pairDivisionResultsComputableInPolyTime`, and
  `allFalseComputableInPolyTime` into a checked `trialPrime` machine (including
  its `n < 2` guard), then use it to filter the ordered Bertrand candidate
  stream and emit the first survivor. Keep CSP structural unary-bound
  production and final whole-compiler assembly as later obligations.

## 2026-08-14 05:32 AEST

- Starting repository commit:
  `59178b816c524eb9f9f4c788d18587d39bd20b74` on `main`. The automation began
  with a clean working tree; `git fetch origin` confirmed divergence count
  `0 0`, so no fast-forward was needed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` in thesis checkout
  `5294a3754f4987514ed9f03e73658df37a684156`. Its unrelated modifications to
  `.gitignore` and `todo.md` were preserved. The proof still claims a genuine
  polynomial-time compiler-owned prime scan and whole compiler, so
  `cor:all-different-csp` remains **Partial**.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized at
  `7e59f0b`. Its generic composition development now lifts a complete exact
  first-machine run to the transfer entry, but still has no checked complete
  transfer-plus-second-machine computation or polynomial-runtime theorem. This
  increment therefore used a concrete fused driver without editing or
  importing the sibling.
- Chosen increment: fuse repeated padded divisibility with the Boolean
  no-divisor fold. `pairAllFalseComputer` restores each reversed pair field,
  executes the existing checked `unaryDvdProgram`, immediately consumes its
  one-bit result, and keeps only the conjunction of negated results in finite
  control; the divisibility output stack is empty between fields and is reused
  for the final Boolean.
- Headline declarations:
  `pairAllFalse_outputsInTime` proves exact output
  `allFalseDivisibilityResults pairs` in at most `18s + 1` steps for actual
  `RawUnaryPairList` encoded length `s`, and
  `allFalseDivisibilityResultsComputableInPolyTime` packages the concrete
  machine as a genuine linear `TM2ComputableInPolyTime` witness. The empty
  input returns `true`, as required for candidate `n = 2`.
  `allFalseDivisibilityResults_trialDivisionPairs_eq_true_iff` proves that on
  the exact checked stream `trialDivisionPairs n`, the emitted bit is true
  exactly when `n.Prime` for `n ≥ 2`.
- Files changed: `PhdThesisLean/AllDifferentCSPMachine.lean` adds the fused
  finite machine, component simulation, exact execution/runtime theorem,
  polynomial witness, semantic bridge, and axiom audits.
  `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` record this completed stage while retaining the
  corollary's Partial status.
- Failed proof shapes supplied useful corrections. Unfolding the fused stack
  wrapper too early prevented the stack-update rewrite, so the proof reused
  the already checked underlying `pairDvdStackContents_update` identity. The
  first Boolean helper again omitted parentheses around a Boolean conjunction,
  causing Lean to elaborate a proposition-valued expression; explicit
  parentheses restored the intended equality and eliminated temporary
  `sorryAx` dependencies. The final time proof initially asked `omega` to
  compare separately simplified raw-stream sums; normalizing the transitive
  bound by addition commutativity avoided that irrelevant arithmetic goal.
- Verification succeeded: targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3114 jobs);
  `git diff --check`; and a project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. New `#print axioms` audits for
  `allFalseDivisibilityResults_trialDivisionPairs_eq_true_iff`,
  `pairAllFalse_outputsInTime`, and
  `allFalseDivisibilityResultsComputableInPolyTime` report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Ending state before commit: one coherent verified source/status/log
  increment, with no unrelated user changes present in this repository.
- Best next step: compose `trialDivisionPairsComputableInPolyTime` with the
  fused `allFalseDivisibilityResultsComputableInPolyTime` pass to obtain the
  checked unary-candidate primality machine, then filter the ordered Bertrand
  candidate stream and emit its first survivor. Keep CSP structural unary-bound
  production and final whole-compiler assembly as later obligations.

## 2026-08-15 05:58 AEST

- Starting repository commit:
  `ba6032f109fa73b6ab4d5ed5cdcaf7d5f18570e4` on `main`. The automation began
  with a clean working tree; local `HEAD`, `origin/main`, and the live remote
  ref agreed, so no fast-forward was needed.
- Active thesis proof reviewed at
  `../phd-thesis/sudoku-via-padic-regression/body.tex` in thesis checkout
  `5294a3754f4987514ed9f03e73658df37a684156`. Its unrelated modifications to
  `.gitignore` and `todo.md` were preserved. The proof still claims a genuine
  polynomial-time compiler-owned prime scan and whole compiler, so
  `cor:all-different-csp` remains **Partial**.
- Read-only sibling review:
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized at
  `367ff9dac248488d7a7f454d41c36c0b02a7f6c6`. Its checked composition API now
  covers exact left-component execution, order-preserving transfer, and exact
  right-component execution. This repository now pins that exact commit as a
  Lake dependency instead of duplicating the generic composition foundations;
  the sibling repository was not edited.
- Chosen increment: compose `trialDivisionPairComputer` with
  `pairAllFalseComputer`. `unaryCandidatePrimeComputer` generates the complete
  padded trial-pair stream, transfers it in source order with the checked
  generic machinery, and runs the fused divisibility/no-divisor component.
  `unaryCandidatePrime_outputsInTime` proves exact output in at most
  `64 * (n + 1)^2` steps on unary `n`, and
  `unaryCandidatePrimeComputableInPolyTime` packages the construction as a
  genuine `TM2ComputableInPolyTime` witness.
- Semantic boundary: `unaryCandidatePrime_eq_true_iff` proves the emitted bit
  is true exactly when `n.Prime` under `2 <= n`. The machine is deliberately
  candidate-only: its empty divisor list accepts `n = 0, 1`, while every
  actual Bertrand candidate used by the next stage is at least two. The
  lower-bound guard is therefore still listed explicitly as unfinished rather
  than being silently assumed in a full primality claim.
- Composition detail: the generic `compositionMachine` exposes the left
  component's initial state, whereas its completed right phase remains tagged
  with the right component's state and therefore does not directly match
  mathlib's `haltList` state convention. The concrete machine selects the
  right component's reset state externally and proves that the generator's
  first scan step immediately installs the correct left state. Separate exact
  execution lemmas then compose generator, transfer, and right phase without
  changing either component's semantics.
- Failed proof/API shapes supplied useful corrections. Direct use of the
  generic machine's default initial state could not prove equality with the
  final `haltList`; the concrete reset-state alignment and first-step lemma
  resolved that mismatch. The transfer configuration proof also exposed the
  middle-alphabet identity map explicitly before simplification. The runtime
  inequality required separate `n = 0`, `n = 1`, and `n >= 2` cases before the
  checked stream-length bound closed the quadratic estimate.
- Files changed: `lakefile.lean` and `lake-manifest.json` add the exact pinned
  `lean-np-hardness` dependency; `PhdThesisLean/AllDifferentCSPMachine.lean`
  adds the composed machine, exact simulations, semantics, runtime theorem,
  polynomial witness, and axiom audits. `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` record the completed candidate-only composition while
  retaining the corollary's Partial status.
- Verification succeeded: full `lake build` (3121 jobs), including the new
  dependency and machine module; `git diff --check`; and the project
  Lean-source scan for `sorry`, `admit`, project `axiom`, `unsafe`, and
  `proof_wanted`. New `#print axioms` audits for
  `unaryCandidatePrime_eq_true_iff`, `unaryCandidatePrime_outputsInTime`, and
  `unaryCandidatePrimeComputableInPolyTime` report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Ending state before commit: one coherent verified source, dependency,
  status, and log increment, with no unrelated user changes present in this
  repository.
- Best next step: add the checked `n < 2` guard (or prove and use the generated
  Bertrand-candidate invariant at the machine boundary), then filter the
  ordered candidate stream and emit the first survivor, including the
  `q = 0, 1` cases. CSP structural unary-bound production and final
  whole-compiler assembly remain later obligations.

## 2026-08-16 05:23:21 AEST — discharge the generated-candidate lower bound

- **Starting commit:** `26b2b5ced081673c42753e27a6085e340551846c`;
  the checkout was clean and synchronized with `origin/main`, and a fetch
  confirmed that no fast-forward was needed.
- **Thesis/source review:** re-read `AGENTS.md`, `THEOREM_STATUS.md`, the
  all-different correspondence in `README.md`, the relevant correctness
  declarations in `AllDifferent.lean` and `FiniteDomainCompiler.lean`, the
  active proof of `cor:all-different-csp`, this journal, and the existing
  candidate/primality machine boundary.
- **Read-only reusable-API review:** sibling `lean-np-hardness` was clean and
  synchronized at `d867de1e06290dc42d8c38f4134e8eb58a774efa`. Its new
  `compositionProgram_complete_run` checks the exact three-phase execution,
  but canonical composed-machine output normalization and the generic
  polynomial-runtime composition theorem remain pending. The pinned dependency
  was therefore left unchanged, and the sibling repository was not edited.
- **Chosen increment:** proved
  `two_le_of_mem_bertrandCandidates`, including the impossible `q = 0` stream
  and the `q = 1` singleton candidate `2`; proved
  `unaryCandidatePrime_eq_trialPrime_of_mem_bertrandCandidates`; and proved
  `filter_unaryCandidatePrime_bertrandCandidates`, which identifies filtering
  the exact enumerator output with the existing guarded semantic prime list.
  The lower-bound guard is now an established producer invariant rather than
  an unimplemented machine stage.
- **Semantic boundary:** this increment does not claim a stream-processing
  filter machine. It proves that the already checked candidate-primality
  machine supplies the correct predicate at every position of the already
  checked Bertrand enumeration, so the next pass may filter and stop at the
  first accepted value without rechecking `2 <= n`.
- **Failed approaches/blockers:** no Lean proof route failed. A separate
  lower-bound machine was rejected as unnecessary after the interval bounds
  discharged the precondition with `omega`; `Bool.eq_iff_iff` and
  `List.filter_congr` then connected the Boolean predicates directly. The
  remaining blocker is the concrete finite-machine candidate filter and
  first-survivor selection, followed by structural unary-bound production and
  whole-compiler composition.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the three
  checked bridge declarations and their axiom audits.
  `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` record that the separate lower-bound guard is no longer
  open while retaining `cor:all-different-csp` as **Partial**; this journal
  records the run.
- **Verification succeeded:** direct checking with
  `lake env lean PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build`
  (3121 jobs); `git diff --check`; and the project Lean-source scan for
  `sorry`, `admit`, project `axiom`, `unsafe`, and `proof_wanted`. The new
  `#print axioms` audits report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- **Ending state before commit:** one coherent verified source, status, and log
  increment, with no unrelated user changes present in this repository.
- **Best next step:** implement a finite-machine pass over the ordered
  `RawNatList` Bertrand stream that invokes `unaryCandidatePrimeComputer`,
  discards rejected candidates, and emits the first survivor; its semantics
  can now use `filter_unaryCandidatePrime_bertrandCandidates` directly,
  including the explicit `q = 0, 1` conventions.

## 2026-08-17 05:31:45 AEST — generate the native unary candidate stream

- **Starting commit:** `48f79963e763b0f6b9009a3527f235f2feb518db` on
  `main`. The checkout was clean and synchronized with `origin/main`; a fetch
  confirmed divergence count `0 0`, so no fast-forward was needed.
- **Thesis/source review:** re-read `AGENTS.md`, `THEOREM_STATUS.md`, the
  relevant `README.md` correspondence, `AllDifferent.lean`,
  `FiniteDomainCompiler.lean`, the active proof of `cor:all-different-csp`,
  this journal, and the current candidate/primality machine boundary. The
  thesis checkout remains at `5294a3754f4987514ed9f03e73658df37a684156` with
  unrelated user modifications to `.gitignore` and `todo.md`; neither was
  changed. The proof still claims compiler-owned prime selection and a genuine
  polynomial-time whole compiler, so the corollary remains **Partial**.
- **Read-only reusable-API review:** sibling `lean-np-hardness` was clean and
  synchronized with its live remote at
  `ed4478c09fa26c1146b648e0ab4d32c08bc1d41b`. It now proves canonical
  list-output correctness for `compositionMachine`, but generic polynomial
  runtime composition remains pending. The pinned dependency was left
  unchanged, and the sibling repository was not edited.
- **Chosen increment:** added `RawUnaryNatList.finEncoding`, a checked
  length-prefixed unary-delimited list representation, and the concrete
  `unaryBertrandCandidateComputer`. The producer copies unary `q` into an
  iteration counter and current value, emits the count field, then emits the
  exact ordered semantic list `[q+1, ..., 2q]` in the stack orientation needed
  by a subsequent field driver. This avoids converting the existing binary
  `RawNatList` fields back to unary before invoking
  `unaryCandidatePrimeComputer`; the binary enumerator remains available for
  final objective serialization.
- **Headline declarations:** `unaryBertrandCandidate_outputsInTime` proves
  exact output in at most `6 * (q + 1)^2` steps, including `q = 0` and `q = 1`;
  `unaryBertrandCandidatesComputableInPolyTime` packages the machine as a
  genuine `TM2ComputableInPolyTime` witness; and
  `unaryBertrandCandidateStream_length_le` bounds the complete encoded stream
  by `2 * q^2 + 2 * q + 1` cells. `RawUnaryNatList.encode_length` records its
  exact size as `xs.sum + 2 * xs.length + 1`.
- **Failed proof shapes supplied useful corrections:** the unary parser's
  accumulator proof needed both associativity and commutativity to normalize
  successor addition. Exact `EvalsToInTime.trans` witnesses expose their time
  sums in the library's opposite addition order, so the final composition
  required explicit addition normalization. The stream-size proof initially
  passed the `List.sum_le_card_nsmul` result directly to `nlinarith`; first
  normalizing natural scalar multiplication to `2 * q^2` supplied the needed
  arithmetic fact. No placeholder or project axiom was retained.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the unary
  encoding, concrete finite machine, exact simulations, runtime and size
  theorems, polynomial witness, and axiom audits.
  `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` record the checked native candidate-stream stage while
  retaining `cor:all-different-csp` as **Partial**; this journal records the
  run.
- **Verification succeeded:** targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3121 jobs);
  `git diff --check`; and a project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. New `#print axioms` audits for
  `RawUnaryNatList.decode_encode`, `RawUnaryNatList.encode_length`,
  `unaryBertrandCandidate_outputsInTime`,
  `unaryBertrandCandidatesComputableInPolyTime`, and
  `unaryBertrandCandidateStream_length_le` report only `propext`,
  `Classical.choice`, and `Quot.sound`; the decoder omits the latter two.
- **Ending state before commit:** one coherent verified source, status, and log
  increment, with no unrelated user changes present in this repository.
- **Best next step:** implement a finite-machine driver over
  `RawUnaryNatList` that restores one unary candidate field, invokes
  `unaryCandidatePrimeComputer`, stops at the first accepted field, and emits
  it. Then compose that driver with `unaryBertrandCandidateComputer` and use
  `filter_unaryCandidatePrime_bertrandCandidates` plus
  `firstBertrandPrime_eq_selectPrimeAbove` for exact selected-prime semantics.

## 2026-08-18 05:51:21 AEST — select the first prime from the unary stream

- **Starting commit:** `1ba0e353b14547e7de2c568bda83f9060d858122` on
  `main`. The checkout was clean; `git fetch --prune origin` confirmed
  divergence count `0 0`, and local `HEAD`, `origin/main`, and the live remote
  ref agreed, so no fast-forward was needed.
- **Thesis/source review:** re-read `AGENTS.md`, `THEOREM_STATUS.md`, the
  relevant `README.md` correspondence, `AllDifferent.lean`,
  `FiniteDomainCompiler.lean`, the active proof of `cor:all-different-csp`,
  this journal, and the existing unary producer/candidate-primality boundary.
  The thesis checkout remains at
  `5294a3754f4987514ed9f03e73658df37a684156` with unrelated user changes to
  `.gitignore` and `todo.md`; neither was modified. The thesis proof still
  requires a compiler-owned whole polynomial-time construction, so the
  corollary remains **Partial**.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized
  with its live remote at
  `6a40461ad2c84a907d3d3bfd9e0324d30813b1c4`. It now has checked
  function-level composition correctness, but still no generic polynomial
  runtime composition theorem. The pinned dependency was therefore left
  unchanged and the sibling repository was not edited.
- **Chosen increment:** added the concrete `primeSelectorComputer`. The raw
  unary encoding exposes value fields in reverse source order, so stopping at
  the first physically encountered prime would select the wrong endpoint.
  Instead, the driver tests every value with `unaryCandidatePrimeComputer` and
  overwrites its saved unary value on acceptance; scanning largest to smallest
  therefore leaves the first accepted source-order value. One-symbol
  lookahead distinguishes the trailing count field, which is erased from both
  the outer candidate stack and the embedded component input before the
  canonical halt.
- **Headline declarations:** `primeSelector_outputsInTime` proves exact output
  for every checked `RawUnaryNatList`; `primeSelectorComputableInPolyTime`
  packages the driver as a genuine `TM2ComputableInPolyTime` witness with
  bound `80 * (s + 1)^3` in complete encoded stream length `s`.
  `selectUnaryCandidatePrime_bertrandCandidates` and
  `primeSelector_selects_firstBertrandPrime` identify the output on the
  generated Bertrand list with `firstBertrandPrime`, hence with the already
  checked semantic `selectPrimeAbove`, including `q = 0` and `q = 1`.
- **Proof/API corrections:** the first control sketch attempted to halt on the
  first physically read survivor, but inspection of
  `RawUnaryNatList.encode` showed that stack order is reversed; overwrite-on-
  acceptance restored the required least-prime semantics. The count cleanup
  initially erased only the outer copy and could not reach `haltList`; the
  final program erases the duplicated component input in lockstep. Dependent
  stack updates required explicit extensional lemmas, and
  `EvalsToInTime.trans` exposes bounds as `m₂ + m₁`, so intermediate runtime
  witnesses were normalized with checked monotonicity lemmas. No placeholder
  or project axiom remains.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the
  semantic selector, concrete finite machine, component lift, exact execution
  proofs, cubic wire-length bound, polynomial witness, Bertrand bridge, and
  axiom audits. `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` record the completed selector stage while retaining the
  corollary's **Partial** status; this entry records the run.
- **Verification succeeded:** targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3121 jobs);
  `git diff --check`; and a project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. New `#print axioms` audits for
  `selectUnaryCandidatePrime_bertrandCandidates`,
  `primeSelector_outputsInTime`, `primeSelectorComputableInPolyTime`, and
  `primeSelector_selects_firstBertrandPrime` report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- **Ending state before commit:** one source/status/log increment in this
  repository, with the thesis checkout's unrelated work preserved.
- **Best next step:** compose `unaryBertrandCandidateComputer` with
  `primeSelectorComputer` and prove the combined unary-`q` machine emits
  `selectPrimeAbove q` in polynomial time; then construct the structural CSP
  pass that produces the unary distinct-symbol bound and assemble the full
  compiler.

## 2026-08-19 05:32:53 AEST — compose compiler-owned prime selection

- **Starting commit:** `8c4e5b8173ca4cd229883cd8e92c66af396c32bf` on
  `main`. The checkout was clean; `git fetch --prune origin` confirmed
  divergence count `0 0`, and local `HEAD`, `origin/main`, and the live remote
  ref agreed, so no fast-forward was needed.
- **Thesis/source review:** re-read `AGENTS.md`, `THEOREM_STATUS.md`, the
  relevant `README.md` correspondence, `AllDifferent.lean`,
  `FiniteDomainCompiler.lean`, the active proof of `cor:all-different-csp`,
  this journal, and the unary producer/selector boundary. The thesis checkout
  remains at `5294a3754f4987514ed9f03e73658df37a684156` with unrelated user
  changes to `.gitignore` and `todo.md`; neither was modified. The corollary
  remains **Partial** because no machine yet constructs the structural bound
  or emits the complete encoded objective from a runtime CSP.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized
  with its live remote at
  `020763e0a494befbe2e032580945e31c57c6b6ef`. It now proves an output-length
  consequence for polynomial-time machines, but still does not supply generic
  polynomial-runtime composition. The project therefore retained its pinned
  dependency `367ff9dac248488d7a7f454d41c36c0b02a7f6c6` and reused that version's
  exact left-run, order-preserving transfer, and right-run APIs; the sibling
  repository was not edited.
- **Chosen increment:** added `selectedPrimeComputer`, the concrete sequential
  composition of `unaryBertrandCandidateComputer` and
  `primeSelectorComputer`. It consumes unary `q`, generates the complete
  checked unary Bertrand stream, transfers it in source order, runs the
  first-survivor selector, and emits exactly `selectPrimeAbove q`, including
  the explicit `q = 0,1` conventions.
- **Headline declarations:** `selectedPrime_outputsInTime` proves the exact
  selected-prime output in at most `1000 * (q + 1)^6` steps. The bound combines
  the quadratic producer/stream-size theorem with the selector's cubic bound
  in complete stream length. `selectedPrimeComputableInPolyTime` packages the
  composed finite machine as a genuine `TM2ComputableInPolyTime` witness from
  unary naturals to unary naturals.
- **Failed proof shapes supplied useful corrections:** directly unfolding the
  selector's nested component stacks left dependent `Function.update` casts;
  splitting only on the canonical input-stack index and unfolding `initList`
  resolved them without a component-specific axiom. The first low-order
  runtime estimate incorrectly tried to bound `14t + 4` by `14t^3`; retaining
  the constant term gives the checked `18t^3` bound and leaves ample room in
  the stated coefficient `1000`. Intermediate unresolved goals appeared as
  `sorryAx` in the audit output, and the final successful audit confirms that
  dependency is absent.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the
  component auxiliaries, concrete composed machine, exact three-stage
  simulations, degree-six runtime proof, polynomial witness, and axiom audits.
  `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` now record that producer-selector runtime composition is
  complete while preserving the corollary's **Partial** status; this entry
  records the run.
- **Verification succeeded:** targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3121 jobs);
  `git diff --check`; and a project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. New `#print axioms` audits for
  `selectedPrime_outputsInTime` and
  `selectedPrimeComputableInPolyTime` report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- **Ending state before commit:** one coherent verified source, status, and log
  increment, with no unrelated user changes present in this repository.
- **Best next step:** define a runtime structural scan bound from the explicit
  domain occurrence stream, prove `symbolCount` is at most that unary bound
  and the bound is at most the encoded CSP length, then compose
  `selectedPrimeComputer` with that producer. This can select a prime above a
  checked upper bound without requiring the machine to deduplicate symbols;
  the supplied-prime semantic theorem already needs only `symbolCount < p`.

## 2026-08-20 05:30:24 AEST — select the runtime prime above domain occurrences

- **Starting commit:** `3ac912068688fb3ad70492806875c7229155bc3a` on
  `main`. The checkout was clean at the start; `git fetch --prune origin`
  confirmed divergence count `0 0`, and the live remote ref matched, so no
  fast-forward was needed.
- **Thesis/source review:** re-read `AGENTS.md`, `THEOREM_STATUS.md`, the
  relevant `README.md` correspondence, `AllDifferent.lean`,
  `FiniteDomainCompiler.lean`, the active proof of
  `cor:all-different-csp`, this journal, and the current encoding/machine
  boundary. The thesis checkout remains at
  `5294a3754f4987514ed9f03e73658df37a684156` with unrelated user changes to
  `.gitignore` and `todo.md`; neither was changed. The corollary remains
  **Partial** because structural row emission and a whole-compiler machine are
  still absent.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized
  with its live remote at
  `527e16c1d0b5616a3e388c907a12added116806a`. Its new
  `MachineComposition.compositionComputableInPolyTime` theorem supplies the
  generic polynomial-time sequential composition previously missing. This
  project remains pinned at `367ff9dac248488d7a7f454d41c36c0b02a7f6c6`;
  the dependency was not changed because this increment did not yet compose a
  new machine, and the sibling repository was not edited.
- **Chosen increment:** aligned the semantic runtime compiler with an easily
  machine-produced upper bound. `RuntimeSystem.domainEntryPrime` selects a
  prime above the explicit domain-entry count. The checked chain
  `symbolCount_le_domainEntryCount` and
  `symbolCount_lt_domainEntryPrime` proves that this prime is large enough for
  canonical ranks without deduplicating arbitrary input symbols; the existing
  `domainEntryCount_le_encodedSize` theorem keeps the unary bound within the
  actual input length, including empty and singleton cases.
- **Headline declarations:** `ExplicitSystem.compileObjectiveAt` places the
  prime-independent canonical row list under any checked prime header.
  `compileObjectiveAt_allDifferent_correctness` and its satisfiable
  specialization transfer the exact supplied-prime semantics to that finite
  output. `compileUsingDomainEntryBound` erases the dependent output to the
  runtime encoding;
  `compileUsingDomainEntryBound_allDifferent_correctness` and
  `compileUsingDomainEntryBound_globalMin_iff_satisfies_of_satisfiable` prove
  exact minimum-conflict and satisfiable-case semantics at the new compiler
  prime. `compileUsingDomainEntryBound_encodedSize_le_quartic` proves the full
  encoded output, including its larger prime header and every delimiter,
  remains at most `64 * (s + 1)^4` bits.
- **Proof/API corrections:** an initial theorem statement indexed the p-adic
  parameter type by `(C.compileObjectiveAt p).prime`; elaboration could not
  synthesize `Fact (C.compileObjectiveAt p).prime.Prime` before reducing that
  projection. Stating the semantic theorem over `p` and separately proving
  `compileObjectiveAt_prime` preserves the exact header claim and resolves the
  typeclass boundary. The first downstream direct-Lean check also saw the old
  imported `.olean`; rebuilding `PhdThesisLean.AllDifferentCSP` through Lake
  exposed the new API. No placeholder or project axiom remains.
- **Files changed:** `PhdThesisLean/AllDifferentCSP.lean` adds the arbitrary-
  prime finite-output interface and semantic theorems.
  `PhdThesisLean/AllDifferentCSPEncoding.lean` adds the domain-entry-bound
  prime, runtime output, exact semantics, and complete quartic bound.
  `PhdThesisLean/AllDifferentCSPMachine.lean`, `README.md`, and
  `THEOREM_STATUS.md` record the shortened structural target while retaining
  **Partial** status; this entry records the run.
- **Verification succeeded:** targeted `lake build
  PhdThesisLean.AllDifferentCSP PhdThesisLean.AllDifferentCSPEncoding`; full
  `lake build` (3121 jobs); `git diff --check`; and a project Lean-source scan
  for `sorry`, `admit`, project `axiom`, `unsafe`, and `proof_wanted`. New
  `#print axioms` audits report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- **Ending state before commit:** one coherent verified source, status, and log
  increment, with the thesis checkout's unrelated work preserved.
- **Best next step:** build a finite-machine pass from
  `RuntimeSystem.finEncoding` to unary `domainEntryCount`, using the existing
  raw nested-list traversal to count only domain value occurrences. Then pin
  and use the sibling's checked generic polynomial-time composition API to
  feed that result to `selectedPrimeComputableInPolyTime`, before implementing
  canonical row emission.

## 2026-08-21 05:37:41 AEST — extract and compose the runtime occurrence bound

- **Starting commit:** `ead69c2234feea747dbde7dc2cd36ee159f50bb9` on
  `main`. The working tree was clean; `git fetch --prune origin` and
  `git ls-remote` confirmed that local `HEAD`, `origin/main`, and the live
  remote ref agreed, so no fast-forward was needed. The intervening Palomar
  README commit was unrelated and preserved.
- **Thesis/source review:** re-read `AGENTS.md`, `THEOREM_STATUS.md`, the
  relevant `README.md` correspondence, `AllDifferent.lean`,
  `FiniteDomainCompiler.lean`, the active proof of
  `cor:all-different-csp`, this journal, and the current encoding/machine
  boundary. The thesis checkout remains at
  `5294a3754f4987514ed9f03e73658df37a684156` with unrelated user changes to
  `.gitignore` and `todo.md`; neither was changed. The corollary remains
  **Partial** because no finite machine yet emits the canonical relabelled,
  deduplicated objective rows or assembles the complete compiler.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized
  with its live remote at
  `b28f357bc55b7e822a6585e2cfbe44300872cc09`. Its checked generic
  `MachineComposition.compositionComputableInPolyTime` theorem was available
  from commit `527e16c1d0b5616a3e388c907a12added116806a`. This project now pins that
  exact checked foundation revision; the sibling repository was not edited.
- **Chosen increment and representation boundary:** added
  `RuntimeCompilerInput.finEncoding`, a Boolean compiler-facing encoding that
  prefixes the existing compact nested-list payload with the explicit
  `domainEntryCount` in unary. `decode` recomputes and checks the count after
  decoding the payload, so the header is verified redundancy rather than a
  supplied semantic assumption. `encode_length` and `encode_length_le` prove
  exact length and at-most-linear overhead, and
  `compileUsingDomainEntryBound_encodedSize_le_compilerInput_quartic` retains
  the complete quartic output bound against the actual compiler input. A
  separate transducer would be needed to transfer the runtime result back to
  the smaller header-free `RuntimeSystem.finEncoding`; that representation
  theorem is not claimed here.
- **Headline machine declarations:** `domainEntryCountComputer` is a concrete
  two-stack finite machine that copies the checked unary header, consumes the
  compact payload, and halts with exactly unary `domainEntryCount`.
  `domainEntryCount_outputsInTime` proves the exact bound `s + 1` for complete
  compiler-input length `s`, and
  `domainEntryCountComputableInPolyTime` packages the linear polynomial
  witness. `runtimeDomainEntryPrimeComputableInPolyTime` uses the newly pinned
  generic composition theorem with `selectedPrimeComputableInPolyTime` and
  computes exactly `RuntimeSystem.domainEntryPrime`, the same prime used by
  `compileUsingDomainEntryBound` and its semantic correctness theorems.
- **Dependency migration and failed proof shapes:** after repinning, a direct
  source check first found the new runtime-composition `.olean` absent; a
  targeted dependency build supplied it. The newer checked composition
  dispatcher canonicalizes the composed machine's initial state at both entry
  and halt, so the two older local `initialState := rightState ...`
  workarounds no longer matched their halt configurations. Removing those
  overrides and their now-obsolete one-step state bridges restored the
  existing candidate-prime and selected-prime exact-runtime proofs. The first
  header-length proof also needed explicit additive normalization and the
  named `domainEntryCount_le_encodedSize` inequality. All intermediate
  `sorryAx` dependencies disappeared in the successful build.
- **Files changed:** `AllDifferentCSPEncoding.lean` adds the compiler input,
  decoder check, length bounds, and compiler-input quartic theorem;
  `AllDifferentCSPMachine.lean` adds the exact extractor and composed runtime
  prime theorem and aligns the older local compositions with the checked
  dependency semantics; `lakefile.lean` and `lake-manifest.json` update the
  exact foundation pin. `AllDifferentCSP.lean`, `README.md`, and
  `THEOREM_STATUS.md` record the representation boundary and retain
  **Partial** status; this entry records the run.
- **Verification succeeded:** targeted builds of
  `PhdThesisLean.AllDifferentCSPEncoding` and
  `PhdThesisLean.AllDifferentCSPMachine`; full `lake build` (3123 jobs);
  `git diff --check`; and a tracked Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. New `#print axioms` audits for
  the compiler-input decoder/size theorem, exact occurrence extractor,
  polynomial occurrence computation, composed runtime prime, and compiler-
  input quartic bound report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- **Ending state before commit:** one coherent verified encoding, finite-
  machine, foundation-pin, status, and log increment; the thesis checkout's
  unrelated work remains untouched.
- **Best next step:** construct the first structural emission pass over
  `RuntimeCompilerInput.finEncoding`: preserve the compact payload after the
  unary header, emit canonical relabelled pin rows and deduplicated primal
  edges in the already checked `RuntimeObjective` syntax, and keep its runtime
  proof separate from the now-complete compiler-input prime-selection pass.

## 2026-08-22 05:25:06 AEST — preserve and expose the runtime CSP payload

- **Starting commit:** `925cef25ec86143cf5a6738d11853c393f1ad527` on
  `main`. The working tree was clean; local `HEAD`, `origin/main`, and the live
  remote ref agreed, so no fast-forward was needed.
- **Thesis/source review:** re-read `AGENTS.md`, `THEOREM_STATUS.md`, the
  relevant `README.md` correspondence, `AllDifferent.lean`,
  `FiniteDomainCompiler.lean`, the active proof of
  `cor:all-different-csp`, this journal, and the current runtime encoding and
  machine boundary. The thesis checkout remains at
  `5294a3754f4987514ed9f03e73658df37a684156` with unrelated user changes to
  `.gitignore` and `todo.md`; neither was changed. The corollary remains
  **Partial** because canonical relabelling, primal-edge deduplication, encoded
  objective emission, and final whole-compiler assembly are still absent.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized
  with its live remote at
  `7ede17421d2b7213417187e933dc9e8d8d4fdc96`. Its checked generic
  `MachineComposition.compositionComputableInPolyTime` API remains the right
  assembly primitive. This project stays pinned at the already checked
  foundation revision `527e16c1d0b5616a3e388c907a12added116806a`; the sibling
  repository was not edited.
- **Chosen increment:** added `compilerPayloadComputer`, a concrete
  three-stack finite machine that discards exactly the decoder-checked unary
  occurrence header, reverses the compact Boolean payload onto scratch, and
  restores the payload byte-for-byte in its original order. This supplies the
  previously missing preservation path from the actual compiler input to the
  compact structural encoding.
- **Headline declarations:** `compilerPayload_outputsInTime` proves exact
  compact-payload output in at most `2s+1` steps for complete compiler-input
  length `s`; `compilerPayloadComputableInPolyTime` packages the pass as a
  genuine linear-time encoding transducer. The specialization
  `runtimeSystemUnframedComputableInPolyTime` exposes the semantic
  `RuntimeSystem.toNatLists` payload through the existing checked raw-field
  traversal, and `runtimeCompilerRawFieldsComputableInPolyTime` composes both
  passes using the pinned generic composition theorem. Its exact output is the
  outer length, every inner length, and every natural value field of the full
  runtime CSP.
- **Proof and representation details:** the payload cannot be pushed directly
  from the input stack to the output stack because that would reverse its bit
  order. The checked machine therefore uses a scratch-stack reversal followed
  by restoration. The direct proof compiled without a failed Lean approach;
  no new encoding header, semantic assumption, placeholder, or project axiom
  was introduced.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the
  payload transducer, exact execution proofs, polynomial witnesses,
  composition, and axiom audits. `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` record the completed raw-structural-input boundary while
  retaining **Partial** status; this entry records the run.
- **Verification succeeded:** targeted `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; full `lake build` (3123 jobs);
  `git diff --check`; and a project Lean-source scan for `sorry`, `admit`,
  project `axiom`, `unsafe`, and `proof_wanted`. New `#print axioms` audits for
  `compilerPayload_outputsInTime`,
  `compilerPayloadComputableInPolyTime`,
  `runtimeSystemUnframedComputableInPolyTime`, and
  `runtimeCompilerRawFieldsComputableInPolyTime` report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- **Ending state before commit:** one coherent verified finite-machine,
  documentation, status, and log increment, with unrelated work in the thesis
  checkout preserved.
- **Best next step:** consume the checked raw `RuntimeSystem.toNatLists` field
  stream to emit the variable-count header and a tagged domain-occurrence
  stream while preserving the scope fields. That provides the concrete input
  for canonical equality-preserving relabelling before pin-row emission and
  primal-edge deduplication.

## 2026-08-23 05:26:18 AEST — specify the tagged structural compiler view

- **Starting commit:** `832eccf126b9c965f22e17848845c77faed45d32` on
  `main`. The working tree was clean; `git fetch --prune origin` confirmed
  divergence count `0 0`, and local `HEAD`, `origin/main`, and the live remote
  ref agreed, so no fast-forward was needed.
- **Thesis/source review:** re-read `AGENTS.md`, `THEOREM_STATUS.md`, the
  relevant `README.md` correspondence, `AllDifferent.lean`,
  `FiniteDomainCompiler.lean`, the active proof of
  `cor:all-different-csp`, this journal, and the runtime encoding/machine
  boundary. The thesis checkout remains at
  `5294a3754f4987514ed9f03e73658df37a684156` with unrelated user changes to
  `.gitignore` and `todo.md`; neither was changed. The corollary remains
  **Partial** because no finite machine yet emits the new structural target,
  and canonical relabelling, primal-edge deduplication, row emission, and final
  assembly remain.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized
  with its live remote at
  `850af1c4024e585c7fa1893c489028cf90219621`. The commits after this project's
  pinned `527e16c1d0b5616a3e388c907a12added116806a` add general encoded-language,
  `P`, and verifier-based `NP` declarations, but no structural-stream
  transducer needed here. The sibling repository and dependency pin were not
  changed.
- **Chosen increment:** defined the exact finite target for the next structural
  machine rather than leaving its output layout informal.
  `RuntimeStructuralRecord` uses tag `0` for a three-field domain occurrence
  `(variable index, original value)` and tag `1` for an intact scope.
  `RuntimeStructuralView` retains a separate variable-count header, so zero
  variables and empty domains remain explicit even though domain values are
  flattened.
- **Checked declarations:** `ofRuntimeSystem_domainOccurrences` proves that
  every explicitly listed domain entry is emitted once, in original order and
  without deduplication; `indexedDomainOccurrences_values` proves the value
  projection is exactly the flattened original domains;
  `indexedDomainOccurrences_variable_lt` proves every attached variable index
  is in range; `ofRuntimeSystem_scopes` recovers the scope stream verbatim;
  the occurrence and record length lemmas give exact counts.
  `RuntimeStructuralView.finEncoding`, `ofNatLists_toNatLists`, and
  `encodedSize_eq_wireSize` provide a checked Boolean encoding and exact wire
  length.
- **Failed approaches and corrections:** the first direct check exposed that
  constructor binders named `variable`/`variables` conflict with current Lean
  parser syntax; they were renamed to `index`/`entries`. A first `zipIdx`-based
  induction changed the tail's starting index from `0` to `1`, so the induction
  hypothesis did not apply. Replacing it with the executable
  `indexedDomainOccurrencesFrom start` definition made index shifts explicit
  and yielded the range, value-order, and length proofs. The `filterMap` and
  `mapM` round-trip goals then required direct list inductions rather than
  relying on broad simplification. No placeholder remains.
- **Files changed:** `PhdThesisLean/AllDifferentCSPEncoding.lean` adds the
  tagged structural syntax, executable conversion, projections, correctness
  lemmas, checked encoding, wire-size identity, and axiom audits.
  `PhdThesisLean/AllDifferentCSPMachine.lean`, `README.md`, and
  `THEOREM_STATUS.md` record this exact target while retaining **Partial**
  status; this entry records the run.
- **Verification succeeded:** `lake env lean
  PhdThesisLean/AllDifferentCSPEncoding.lean`; targeted `lake build
  PhdThesisLean.AllDifferentCSPEncoding
  PhdThesisLean.AllDifferentCSPMachine` (3100 jobs); full `lake build` (3123
  jobs); `git diff --check`; and a project Lean-source scan for `sorry`,
  `admit`, project `axiom`, `unsafe`, and `proof_wanted`. New `#print axioms`
  audits report only `propext`, `Classical.choice`, and `Quot.sound`.
- **Ending state before commit:** one coherent verified encoding,
  correspondence, status, and log increment; unrelated thesis work remains
  untouched.
- **Best next step:** implement a finite-machine transducer from the checked
  raw `RuntimeSystem.toNatLists` fields to
  `RuntimeStructuralView.finEncoding`, with a polynomial bound in the complete
  compiler-input length. Then canonicalise the occurrence values while
  retaining their variable tags before emitting pin rows.

## 2026-08-24 05:22:22 AEST — frame the raw tagged structural target

- **Starting commit:** `9ac73e94eca35483d26eb52f60e99171a447a8ce` on
  `main`. The working tree was clean; `git fetch --prune origin` confirmed
  divergence count `0 0`, and local `HEAD`, `origin/main`, and the live remote
  ref agreed, so no fast-forward was needed.
- **Thesis/source review:** re-read `AGENTS.md`, `THEOREM_STATUS.md`, the
  relevant `README.md` correspondence, `AllDifferent.lean`,
  `FiniteDomainCompiler.lean`, the active proof of
  `cor:all-different-csp`, this journal, and the runtime encoding and machine
  boundary. The thesis checkout remains at
  `5294a3754f4987514ed9f03e73658df37a684156` with unrelated user changes to
  `.gitignore` and `todo.md`; neither was changed. The corollary remains
  **Partial** because the raw structural producer, canonical relabelling,
  primal-edge deduplication, objective emission, and final compiler assembly
  are still absent.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized
  with its live remote at
  `e416760763f22b4dba5ef2f6c92b55cd47d7447a`. Its commits after this
  project's pinned `527e16c1d0b5616a3e388c907a12added116806a` extend the
  encoded complexity-class layer but add no structural-stream transducer. The
  sibling repository and dependency pin were not changed.
- **Chosen increment:** separated structural emission from canonical Boolean
  serialization. `RuntimeStructuralView.rawFinEncoding` is a checked
  stack-oriented raw-field encoding of the exact tagged structural target.
  It covers the variable-count header, every record field, empty lists, and
  zero-variable views through the general nested-list representation.
- **Headline finite-machine declarations:**
  `nestedListFrame_outputsInTime` generalizes the existing serializer proof
  from one natural list to every raw nested-list field stream and proves exact
  Boolean output in at most three times the raw input length.
  `runtimeStructuralViewFramingComputableInPolyTime` packages that same
  concrete finite machine as a linear-time transducer from the new raw
  structural encoding to `RuntimeStructuralView.finEncoding`. The next
  structural producer can therefore target the simpler raw contract and
  compose with this checked bridge.
- **Failed approach and correction:** the first decoder definition used an
  unqualified `ofNatLists` inside the new machine-local
  `RuntimeStructuralView` namespace. Lean reported `Unknown identifier
  ofNatLists`, left the round-trip goal unsolved, and the temporary declaration
  therefore audited with `sorryAx`. Qualifying
  `AllDifferentCSPEncoding.RuntimeStructuralView.ofNatLists` resolved the
  namespace boundary; the successful direct check and final audits contain no
  `sorryAx`.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the raw
  checked encoding, generalized exact execution theorem, polynomial-time
  wrapper, and axiom audits. `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` record the new serialization boundary while retaining
  **Partial** status; this entry records the run.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; targeted `lake build
  PhdThesisLean.AllDifferentCSPMachine` (3100 jobs); full `lake build` (3123
  jobs); `git diff --check`; and project Lean-source scans for `sorry`,
  `admit`, project `axiom`, `unsafe`, and `proof_wanted`. New `#print axioms`
  audits for `RuntimeStructuralView.rawFinEncoding`,
  `nestedListFrame_outputsInTime`, and
  `runtimeStructuralViewFramingComputableInPolyTime` report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- **Ending state before commit:** one coherent verified finite-machine,
  correspondence, status, and log increment; unrelated thesis work remains
  untouched.
- **Best next step:** implement a finite-machine pass from
  `runtimeCompilerRawFieldsComputableInPolyTime` to
  `RuntimeStructuralView.rawFinEncoding`, proving that it emits exactly
  `RuntimeStructuralView.ofRuntimeSystem`; then compose it with the new linear
  framing bridge before canonicalizing occurrence values with their variable
  tags intact.

## 2026-08-25 05:27:19 AEST — normalize runtime fields to semantic source order

- **Starting commit:** `eb2b43b1bc0a3a90d6db25f4c5c0d0809da39316` on
  `main`. The working tree was clean; `git fetch --prune origin` and a live
  `git ls-remote` lookup confirmed that local `HEAD`, `origin/main`, upstream,
  and the live remote ref agreed, so no fast-forward was needed.
- **Thesis/source review:** re-read `AGENTS.md`, `THEOREM_STATUS.md`, the
  relevant `README.md` correspondence, `AllDifferent.lean`,
  `FiniteDomainCompiler.lean`, the active proof of
  `cor:all-different-csp`, this journal, and the current encoding/machine
  boundary. The thesis checkout remains at
  `5294a3754f4987514ed9f03e73658df37a684156` with unrelated user changes to
  `.gitignore` and `todo.md`; neither was changed. The corollary remains
  **Partial** because tagged structural emission, canonical relabelling,
  primal-edge deduplication, objective-row emission, and final assembly are
  still absent.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized
  with its live remote at
  `744c3b4d001012be016c98f0691468c37ce20b7c`. Its newer encoded-complexity
  declarations and the pinned generic composition theorem remain available,
  but it has no checked structural-list transducer to reuse. The sibling
  repository and this project's existing dependency pin were not changed.
- **Chosen increment and representation boundary:** added
  `SourceOrderRawNatLists.finEncoding`, a checked encoding of the same nested
  natural lists as `RawNatLists`, but with fields in semantic source order.
  `encode_eq_payloads` proves that the outer length and every inner length/value
  field occur in the `RawNatLists.payloads` order, with a leading delimiter and
  canonical least-significant-bit-first payload. This is the order needed to
  see the compact CSP's outer length and domain-count separator before its
  domains and scopes.
- **Headline finite-machine declarations:** `sourceOrderRawFieldComputer` is a
  concrete two-stack finite machine that reverses the complete stack-oriented
  stream. `sourceOrderRawFields_outputsInTime` proves exact source-order output
  in `s+1` steps for raw input length `s`, and
  `sourceOrderRawFieldsComputableInPolyTime` packages the linear polynomial
  witness. `runtimeCompilerSourceOrderFieldsComputableInPolyTime` composes this
  pass with `runtimeCompilerRawFieldsComputableInPolyTime`, so the actual
  checked compiler input now yields `RuntimeSystem.toNatLists` in this
  source-order encoding.
- **Failed proof shapes and corrections:** an exploratory proof named a
  nonexistent `List.flatMap_congr_left`; after rewriting by
  `List.reverse_flatMap`, ordinary simplification proved the exact segment
  identity. Lean also could not infer `Fintype` through the reducible dependent
  stack-alphabet definition for the machine's input stack; supplying the
  explicit `show Fintype (Option Bool) from inferInstance` witness resolved the
  boundary. No placeholder or project axiom remains.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the
  checked encoding, exact stream identity, finite machine, exact runtime proof,
  polynomial wrapper, compiler-input composition, and axiom audits.
  `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` synchronize the new boundary while retaining
  **Partial** status; this entry records the run.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; targeted `lake build
  PhdThesisLean.AllDifferentCSPMachine` (3100 jobs); full `lake build` (3123
  jobs); `git diff --check`; and a tracked project Lean-source scan for
  `sorry`, `admit`, project `axiom`, `unsafe`, and `proof_wanted`. New
  `#print axioms` audits report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- **Ending state before commit:** one coherent verified finite-machine,
  correspondence, status, and log increment; unrelated thesis work remains
  untouched.
- **Best next step:** consume `SourceOrderRawNatLists.finEncoding` with a
  finite structural emitter. It should stage transformed records while
  counting them, attach the current domain index to every value occurrence,
  copy scopes under tag `1`, emit the exact outer record count, and prove the
  result is `RuntimeStructuralView.ofRuntimeSystem` under
  `RuntimeStructuralView.rawFinEncoding`; then compose with the checked framing
  bridge.

## 2026-08-26 05:31:35 AEST — check canonical binary predecessor

- **Starting state:** clean synchronized `main` at
  `6d13b55f5bcd7eabe92844788a295828728b7b3f`. A fresh fetch and live
  `ls-remote` check confirmed that local `HEAD`, `origin/main`, upstream, and
  the live remote ref agreed, so no fast-forward was needed.
- **Thesis/source review:** re-read `AGENTS.md`, `THEOREM_STATUS.md`, the
  relevant `README.md` correspondence, `AllDifferent.lean`,
  `FiniteDomainCompiler.lean`, the active proof of
  `cor:all-different-csp`, this journal, and the current encoding/machine
  boundary. The thesis checkout remains at
  `5294a3754f4987514ed9f03e73658df37a684156`; its unrelated changes to
  `.gitignore`, `bibfile.bib`, `sudoku-via-padic-regression/body.tex`,
  `sudoku-via-padic-regression/integration-notes-2026-07-29.md`, `todo.md`,
  and two untracked CSP projection images were preserved. The corollary
  remains **Partial**.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean, synchronized with
  its live remote, and had advanced to
  `1c0b1ce11276cbf9fa4af98b1693aec4db6e32ac`. Its checked composition APIs
  remain available, but a search of it and mathlib found no finite-machine
  canonical binary predecessor to reuse. The sibling repository and this
  project's dependency pin were not changed.
- **Chosen increment and exact need:** the source-order structural parser must
  count down both the remaining domain lists and the remaining values in each
  domain or scope. The repository already checked binary successor,
  comparison, and addition, but had no canonical predecessor. This run added
  the missing finite primitive instead of starting the larger record-staging
  loop with an unproved counter operation.
- **Headline declarations:** `binaryPredBits_encodeNat` proves that the
  executable bit transformation sends mathlib's canonical `encodeNat n` to
  `encodeNat (Nat.pred n)`. `binaryPredComputer` is a concrete three-stack
  finite machine with borrow, leading-zero inspection, suffix-copy, and
  reversal phases. `binaryPred_outputsInTime` proves exact output on every bit
  word in at most `2s + 3` steps, and
  `binaryPredComputableInPolyTime` packages saturated natural predecessor
  under mathlib's standard `FinEncoding`. Zero, one, powers of two, arbitrary
  borrow chains, and malformed all-zero words are covered by the general
  bit-level machine theorem; canonical inputs produce canonical outputs.
- **Failed proof shapes and corrections:** the first `borrow` step proof left
  a dependent-stack `Function.update` equality unresolved; an explicit
  extensional case split on the three stack indices closed it. The composed
  true-bit branch initially differed only by reassociation of its exact time
  expression, and the preparatory-time bound was not discharged by
  simplification alone; normalizing natural addition and using `omega` after
  unfolding the cases resolved both. No placeholder or project axiom remains.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the
  executable predecessor, finite program, exact executions, linear bound,
  polynomial wrapper, and three axiom audits. `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` synchronize the new runtime boundary while retaining
  **Partial** status; this entry records the run.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; targeted `lake build
  PhdThesisLean.AllDifferentCSPMachine` (3100 jobs); full `lake build` (3123
  jobs); `git diff --check`; and a tracked project Lean-source scan for
  `sorry`, `admit`, project `axiom`, `unsafe`, and `proof_wanted`. The new
  `#print axioms` audits report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- **Ending state before commit:** one coherent verified finite-machine,
  correspondence, status, and log increment; unrelated thesis and sibling
  work remains untouched.
- **Best next step:** implement the source-order structural emitter's parser
  and staging loop using `binaryPredBits` for domain/list countdowns and
  `binarySuccBits` for current indices and the emitted-record count. It should
  attach the current domain index to every value occurrence, preserve empty
  and singleton lists, copy each scope under tag `1`, emit the exact outer
  record count, prove exact `RuntimeStructuralView.ofRuntimeSystem` output
  under `RuntimeStructuralView.rawFinEncoding`, and compose with the checked
  framing bridge.

## 2026-08-27 05:35:59 AEST — bound the tagged structural encoding by input bits

- **Starting state:** clean synchronized `main` at
  `71b61e0991f19a44acf996baa06e73a07f6f7d05`. A fresh fetch and live
  `ls-remote` check confirmed that local `HEAD`, `origin/main`, upstream, and
  the live remote ref agreed, so no fast-forward was needed.
- **Thesis/source review:** re-read `AGENTS.md`, `THEOREM_STATUS.md`, the
  relevant `README.md` correspondence, `AllDifferent.lean`,
  `FiniteDomainCompiler.lean`, the active proof of
  `cor:all-different-csp`, this journal, and the current encoding/machine
  boundary. The thesis checkout is at
  `381523a9a4fb2516555c159e17cc92315ab4b29f` with unrelated modified and
  untracked files; all were preserved. The corollary remains **Partial**.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean on synchronized
  `main` at `9ee16bb006e04c1ac049f2a67bff5bb5ce1e6c10`. Its checked composition
  and pair-splitting APIs remain available, but it has no structural-stream
  emitter or bit-size theorem that subsumes this target. The sibling repository
  and this project's dependency pin were not changed.
- **Chosen increment:** closed the bit-size obligation for the exact tagged
  structural intermediate before implementing its larger finite-machine
  emitter. The proof compares every copied domain-value and scope-entry frame
  with its original compact-input frame, so arbitrary large natural symbols
  are measured by binary length rather than incorrectly bounded by the input
  cell count as numeric magnitudes.
- **Headline declarations:** `RuntimeStructuralView.ofRuntimeSystem_encodedSize_le_quadratic`
  proves that the complete canonical tagged Boolean encoding has at most
  `32 * (s + 1)^2` bits for compact input length `s`.
  `RuntimeStructuralView.ofRuntimeSystem_encodedSize_le_compilerInput_quadratic`
  transfers the same bound to the complete compiler-facing input, including
  its decoder-checked unary occurrence header. The general proofs cover zero
  variables, empty domains and scopes, singleton rows, repeated occurrences,
  and arbitrarily large symbol values.
- **Failed proof shape and correction:** an initial experiment discharged the
  fixed wire sizes for tags and short row lengths with `native_decide`; its
  axiom audit exposed `Lean.ofReduceBool` and `Lean.trustCompiler`. The final
  proof instead uses the checked general inequality
  `natWireSize_le_two_mul_add_one` for those constants. The resulting audits
  contain only `propext`, `Classical.choice`, and `Quot.sound`.
- **Files changed:** `PhdThesisLean/AllDifferentCSPEncoding.lean` adds the
  field-sensitive accounting lemmas, both public quadratic bounds, and axiom
  audits. `PhdThesisLean/AllDifferentCSP.lean`, `README.md`, and
  `THEOREM_STATUS.md` synchronize the correspondence while retaining
  **Partial** status; this entry records the run.
- **Verification succeeded:** direct `lake env lean` checks of
  `PhdThesisLean/AllDifferentCSP.lean` and
  `PhdThesisLean/AllDifferentCSPEncoding.lean`; targeted `lake build
  PhdThesisLean.AllDifferentCSPEncoding PhdThesisLean.AllDifferentCSPMachine`
  (3100 jobs); full `lake build` (3123 jobs); `git diff --check`; and tracked
  project Lean-source scans for `sorry`, `admit`, project `axiom`, `unsafe`,
  and `proof_wanted` (all empty). The new `#print axioms` audits report only
  `propext`, `Classical.choice`, and `Quot.sound`.
- **Ending state before commit:** one coherent verified encoding-size,
  correspondence, status, and log increment; unrelated thesis and sibling
  work remains untouched.
- **Best next step:** implement the source-order structural emitter's parser
  and record-staging loop. It should use the checked predecessor/successor
  primitives, attach the current domain index to every value occurrence, copy
  scopes intact under tag `1`, emit the exact outer record count, prove exact
  `RuntimeStructuralView.ofRuntimeSystem` raw output, and then compose with the
  framing bridge; the new quadratic theorem supplies the intermediate
  bit-size invariant for that composition.

## 2026-08-28 05:32:19 AEST — fix the exact structural emitter field contract

- **Starting state:** clean synchronized `main` at
  `e274acf50de6bc1ea93ddcc5178abda966135a18`. A fresh fetch and live
  `ls-remote` check confirmed that local `HEAD`, `origin/main`, upstream, and
  the live remote ref agreed, so no fast-forward was needed. The active thesis
  checkout was clean and synchronized at
  `f1107f5db8ddf3bb2bb529e1afadf1fc3dff7e9d`.
- **Thesis/source review:** re-read `AGENTS.md`, `THEOREM_STATUS.md`, the
  relevant `README.md` correspondence, `AllDifferent.lean`,
  `FiniteDomainCompiler.lean`, the active proof of
  `cor:all-different-csp`, this journal, and the current structural
  encoding/machine boundary. The corollary remains **Partial** because the
  field-stream specification added here is not yet realized by a finite
  record-staging machine, and canonical relabelling, edge deduplication,
  objective emission, and final composition remain.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized
  with its live remote at
  `db130fb7041f0035355783c2b24569838a1fe27f`. Its new checked tagged-pair
  classification and order-restoration phases are not yet integrated into one
  composable adapter and do not implement this structural emitter. The sibling
  repository and this project's dependency pin were not changed.
- **Chosen increment:** added executable `StructuralFieldStream.flatten`,
  `domainFieldsFrom`, `scopeFields`, `ofRuntimeSystem`, and `encode` to make
  the pending machine's exact field contract explicit. Every domain value is
  emitted as the complete field block `[3, 0, index, value]`; every scope is
  emitted intact as `[scope.length + 1, 1, ...scope]`; and the outer count is
  exactly `1 + domainEntryCount + scopes.length`.
- **Checked correspondence declarations:**
  `StructuralFieldStream.ofRuntimeSystem_eq_flatten` identifies those fields
  with the checked `RuntimeStructuralView.toNatLists` payload;
  `encode_eq_sourceOrderRawNatLists` identifies their delimited binary form;
  `encode_reverse_eq_raw` proves final stack reversal gives exactly
  `RawNatLists.encode`; and `raw_decode_encode_reverse` proves the checked raw
  decoder accepts that stream as exactly `RuntimeStructuralView.ofRuntimeSystem`.
  The general definitions cover zero variables, empty domains, singleton
  domains and scopes, repeats, and empty scopes without separate assumptions.
- **Failed proof shapes and corrections:** the first domain induction left a
  `List.map` composition opaque; unfolding `Function.comp` exposed the exact
  occurrence row. The complete-stream proof also needed the definitional
  equality between `indexedDomainOccurrences` and its start-at-zero form plus
  commutative normalization of the record count. Finally, the raw-decoder
  theorem was initially placed before `rawFinEncoding` was declared; moving it
  immediately below that declaration fixed the namespace/declaration-order
  error. No representation change or placeholder was needed.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the
  executable contract, four checked correspondence theorems, and axiom audits.
  `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` synchronize the new boundary while retaining **Partial**
  status; this entry records the run.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; targeted `lake build
  PhdThesisLean.AllDifferentCSPMachine
  PhdThesisLean.AllDifferentCSPEncoding PhdThesisLean.AllDifferentCSP` (3100
  jobs); full `lake build` (3123 jobs); `git diff --check`; and tracked
  Lean-source scans for `sorry`, `admit`, project `axiom`, `unsafe`, and
  `proof_wanted` (all empty). The four new `#print axioms` audits report only
  `propext`, `Classical.choice`, and `Quot.sound`.
- **Ending state before commit:** one coherent verified field-contract,
  correspondence, status, and log increment; no unrelated work was changed.
- **Best next step:** implement the finite source-order parser and staging
  loop against `StructuralFieldStream.encode`. Maintain binary countdowns for
  remaining domains and row entries, increment the variable index and final
  record count, stage record fields through the two reversals required to put
  the computed outer/header fields at the bottom of the raw output stack, and
  prove exact output with `encode_reverse_eq_raw` before composing the framing
  bridge.

## 2026-08-29 05:33:01 AEST — emit one tagged domain-occurrence block

- **Starting state:** clean synchronized `main` at
  `20cf0d2b9f3ff1217c795441b60ea9daf134cb8a`. A fresh fetch confirmed local
  `HEAD` and `origin/main` agreed. The active thesis checkout was clean and
  synchronized at `f1107f5db8ddf3bb2bb529e1afadf1fc3dff7e9d`; the proof of
  `cor:all-different-csp` still claims explicit relabelling, compiler-selected
  prime construction, deduplicated primal edges, polynomial-time output, and
  exact minimum-conflict/satisfiable semantics. The corollary remains
  **Partial**.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized
  at `aff35e5959c5d4a8e3cc120009323f113ddc9ffd`. Its new integrated tagged-pair
  preprocessing adapter is useful generic machinery but is newer than this
  project's pinned dependency and does not implement the required structural
  list emitter. Neither the sibling repository nor the dependency pin was
  changed.
- **Chosen increment:** realized the repeated local domain-expansion operation
  of the pending structural emitter as a genuine finite machine. The input is
  an arbitrary current variable index and domain value in a checked uncounted
  source-order raw-field encoding; the output is the exact field block
  `[3, 0, index, value]` required by `StructuralFieldStream.domainFieldsFrom`
  and `RuntimeStructuralRecord.domainOccurrence`.
- **Headline declarations:** `SourceOrderRawFields.finEncoding` checks
  uncounted delimiter-first canonical binary natural fields.
  `DomainOccurrenceFieldBlock.inputFinEncoding` and `outputFinEncoding` check
  the local pair/block boundary; `fields_eq_record` identifies the four
  semantic fields with the length-prefixed tagged structural record.
  `domainOccurrenceBlockComputer` is a concrete three-stack finite machine;
  `domainOccurrenceBlock_outputsInTime` proves exact output in `2s+2` steps,
  and `domainOccurrenceBlockComputableInPolyTime` packages the linear
  polynomial-time witness. Arbitrary zero or nonzero indices and values are
  copied byte-for-byte; only the fixed row-length and tag fields are added.
- **Failed proof shapes and corrections:** the first source-field reversal
  proof named a nonexistent `List.reverse_map`; ordinary simplification
  already knew the required map/reverse identity. The identifier `prefix` is
  reserved in this Lean parser, so the fixed cells were renamed
  `headerPrefix`. Direct reduction and `decide` could not normalize mathlib's
  `Nat`-to-`Num` cast in `encodeNat 3`; rewriting through `Num.ofNat'_bit` and
  `Num.ofNat'_one` produced the checked constant encoding without compiler
  trust. Finally, `EvalsToInTime.trans` normalized the summed phase times in
  the reverse syntactic order; an explicit arithmetic equality closed the
  exact `2s+2` bound. No placeholder, project axiom, or representation
  weakening was introduced.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the
  checked raw-field encoding, local domain-block encodings, finite machine,
  exact execution/runtime proofs, and four axiom audits.
  `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` synchronize the new boundary while retaining
  **Partial** status; this entry records the run.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; targeted `lake build
  PhdThesisLean.AllDifferentCSPMachine
  PhdThesisLean.AllDifferentCSPEncoding PhdThesisLean.AllDifferentCSP` (3100
  jobs); full `lake build` (3123 jobs); `git diff --check`; and a tracked
  project Lean-source scan for `sorry`, `admit`, project `axiom`, `unsafe`, and
  `proof_wanted` (all empty). New `#print axioms` audits report only `propext`,
  `Classical.choice`, and `Quot.sound`; `fields_eq_record` is axiom-free.
- **Ending state before commit:** one coherent verified local structural-
  emitter increment plus synchronized correspondence/status documentation;
  no unrelated repository, thesis, or sibling work was changed.
- **Best next step:** implement the outer source-order domain parser that uses
  binary countdowns to emit this checked block once per domain value, advance
  the variable index including empty/singleton domains, stage the accumulated
  record count, and prove exact agreement with
  `StructuralFieldStream.domainFieldsFrom`; then add the intact tagged-scope
  branch and compose the complete stream with `encode_reverse_eq_raw`.

## 2026-08-30 05:30:36 AEST — emit one intact tagged scope block

- **Starting state:** clean synchronized `main` at
  `32f32b51c90d891ad9610eea55697e9de144df1e`. A fresh fetch confirmed local
  `HEAD` and `origin/main` agreed, so no fast-forward was needed. The active
  thesis checkout remained clean at
  `f1107f5db8ddf3bb2bb529e1afadf1fc3dff7e9d`; its proof of
  `cor:all-different-csp` still requires the complete structural compiler,
  canonical relabelling, deduplicated primal edges, compiler-selected prime,
  polynomial runtime, and exact minimizer semantics. The corollary remains
  **Partial**.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean at
  `3718fe5a90615ed99c04a406427efcc3c0238080`. Its newly checked tagged-pair
  adapter and reduction-machine lifting theorems separate and preserve pair
  components, but they do not yet provide a complete polynomial-time map or
  repeated-record driver that implements this structural parser. The sibling
  repository and this project's pinned dependency were not changed.
- **Chosen increment:** completed the scope-side local branch of the pending
  structural emitter. The checked input contains one scope's explicit entry
  count followed by all source-order entry fields. The new fused machine
  increments only that first canonical binary field, inserts tag `1`, copies
  all remaining fields byte-for-byte, and restores semantic source order.
- **Headline declarations:** `ScopeFieldBlock.inputFinEncoding` and
  `outputFinEncoding` check the local count/entry and tagged-record boundaries;
  `ScopeFieldBlock.fields_eq_record` identifies the semantic output with
  `RuntimeStructuralRecord.scope`. `scopeFieldBlockComputer` is a concrete
  three-stack finite machine. `scopeFieldBlock_outputsInTime` proves exact
  `[|S|+1, 1, ...S]` output in at most `3s+8` steps for complete input length
  `s`, and `scopeFieldBlockComputableInPolyTime` packages the linear machine
  witness. The general proof includes empty scopes, singleton scopes, binary
  carry growth, and arbitrary natural entry values.
- **Failed proof shapes and corrections:** the first direct Lean check exposed
  four local normalization gaps rather than a machine error. Constant tag
  output needed an explicit checked `encodeNat 1 = [true]` lemma; two empty-
  stack transitions needed extensional proofs for dependent stack-family
  updates; the empty-scope endpoint needed explicit zero/one encoding
  rewrites; and the final time inequality needed the input/output encoding
  equalities rewritten into the already proved output-length bound. Those
  changes closed all goals without weakening the representation or runtime
  claim.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the local
  encodings, semantic correspondence, finite program, exact phase executions,
  linear runtime theorem, polynomial wrapper, and three axiom audits.
  `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` synchronize the checked boundary while retaining
  **Partial** status; this entry records the run.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; targeted `lake build
  PhdThesisLean.AllDifferentCSPMachine
  PhdThesisLean.AllDifferentCSPEncoding PhdThesisLean.AllDifferentCSP` (3100
  jobs); full `lake build` (3123 jobs); `git diff --check`; and a project
  Lean-source scan for `sorry`, `admit`, project `axiom`, `unsafe`, and
  `proof_wanted` (all empty). The new `#print axioms` audits report only the
  standard `propext`, `Classical.choice`, and `Quot.sound` dependencies.
- **Ending state before commit:** one coherent verified scope-record finite-
  machine increment plus synchronized correspondence/status documentation;
  no thesis, sibling, or unrelated repository work was changed.
- **Best next step:** implement the outer source-order structural driver that
  parses the domain-count boundary, applies the checked domain-occurrence
  block once per value, advances the current variable index across empty and
  singleton domains, switches to the checked scope block for every remaining
  row, and stages the variable header and exact total record count. Prove its
  output agrees with `StructuralFieldStream.encode`, then reverse it into
  `RuntimeStructuralView.rawFinEncoding` and compose the existing framing
  bridge.

## 2026-08-31 05:55 AEST — expand one complete indexed domain row

- **Starting state:** clean synchronized `main` at
  `2252803590ef8d14670429e76364b2059c0d2d70`. A fresh fetch confirmed local
  `HEAD`, `origin/main`, and the live tracking state agreed, so no fast-forward
  was needed. The active thesis checkout was clean at
  `f1107f5db8ddf3bb2bb529e1afadf1fc3dff7e9d`; the exact
  `cor:all-different-csp` proof still requires the complete polynomial
  compiler, including source-order structural traversal, canonical shared-
  value relabelling, deduplicated primal edges, selected-prime construction,
  dataset emission, and semantic composition. The corollary remains
  **Partial**.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean at
  `bbda24607069652e00e54541387e01505f6411df`. Its latest checked ordered-
  reduction input transfer remains useful for later composition, but it has no
  complete repeated-record driver for one source domain. The sibling and this
  project's pinned dependency were not changed.
- **Chosen increment:** closed the inner domain-row loop of the structural
  emitter. A checked input row contains the current variable index, an
  explicit value count, and every source-order value field. The machine keeps
  the index on a persistent stack, emits one exact tagged occurrence block per
  value, reverses the accumulated output once, and clears every non-output
  stack before halting.
- **Headline declarations:** `DomainFieldRow.inputFinEncoding` checks the
  explicit row count; `DomainFieldRow.outputFinEncoding` accepts only complete
  `[3, 0, index, value]` groups; `DomainFieldRow.inputEncode_length` and
  `outputEncode_occurrences_length` expose exact bit-level sizes.
  `domainFieldRowComputer` is a concrete five-stack finite machine;
  `domainFieldRow_outputsInTime` proves the exact occurrence list is emitted
  in at most `20 * (s+1)^2` steps for complete encoded row length `s`; and
  `domainFieldRowComputableInPolyTime` packages the corresponding
  `TM2ComputableInPolyTime` witness. Empty and singleton domains are handled by
  the general proof, with equality-preserving reuse of the same supplied index
  for every value.
- **Failed proof shapes and corrections:** the first complete run exposed that
  a standard `haltList` configuration requires all work stacks empty; the
  initial program retained the persistent index stack. A finite `clearIndex`
  phase now discharges it before halt. Early closed-form length proofs asked
  `omega` to distribute products, so the checked proofs now isolate exact
  block lengths and use semiring normalization. The phase-composition proof
  also revealed the library's accumulated-time association; explicit `omega`
  equalities normalize those sums without changing the machine or bound.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the
  checked row encodings, semantic occurrence function, finite program, exact
  phase and end-to-end executions, quadratic bit-level runtime theorem,
  polynomial wrapper, and three axiom audits.
  `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` synchronize the new boundary while retaining
  **Partial** status; this entry records the run.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; targeted `lake build
  PhdThesisLean.AllDifferentCSPMachine
  PhdThesisLean.AllDifferentCSPEncoding PhdThesisLean.AllDifferentCSP` (3100
  jobs); full `lake build`; `git diff --check`; and a tracked project Lean-
  source scan for `sorry`, `admit`, project `axiom`, `unsafe`, and
  `proof_wanted` (all empty). New `#print axioms` audits report only the
  standard `propext`, `Classical.choice`, and `Quot.sound` dependencies.
- **Ending state before commit:** one coherent verified domain-row finite-
  machine increment plus synchronized correspondence/status documentation;
  no thesis, sibling, or unrelated repository work was changed.
- **Best next step:** build the outer source-order driver around this row
  machine: consume the domain-count boundary, advance the current index after
  every domain including empty and singleton rows, switch to
  `scopeFieldBlockComputer`, stage the variable header and exact record count,
  and prove agreement with `StructuralFieldStream.encode` before composing the
  existing raw reversal and framing bridge.

## 2026-09-01 05:38 AEST — check the complete domain-section contract

- **Starting state:** clean synchronized `main` at
  `900925f9dd46dca17daa118f4ff852f188577c97`. A fresh fetch confirmed local
  `HEAD`, `origin/main`, and the live remote `main` ref agreed, so no
  fast-forward was needed. The active thesis checkout was clean at
  `f1107f5db8ddf3bb2bb529e1afadf1fc3dff7e9d`; its proof of
  `cor:all-different-csp` still claims the complete polynomial compiler. The
  corollary remains **Partial**.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean at
  `fb9798f`. Its latest pair-preprocessing and composition APIs do not provide
  a generic repeated-record/list-map machine, so no generic foundation was
  duplicated or changed in that repository.
- **Chosen increment:** fixed a checked whole-domain-section interface for the
  next structural finite driver. The source-order input contains the exact
  domain count followed by count-prefixed rows; its decoder checks the outer
  count, every inner count, and exhaustion of all fields. Consecutive row
  indices are explicit and advance across empty as well as nonempty domains.
- **Headline declarations:** `DomainFieldSection.inputFinEncoding` is the
  complete checked domain-section encoding;
  `inputEncode_eq_sourceOrderRawNatLists` proves it is exactly the existing
  source-order nested-list wire format. `occurrences_indexedRowsFrom` identifies
  the indexed row expansion with
  `RuntimeStructuralView.indexedDomainOccurrencesFrom`, including empty-row
  index advancement. `outputEncode_eq_row_outputs` proves the section output
  is the concatenation of the already checked per-row outputs, and
  `outputEncode_eq_structuralFields` identifies that output exactly with
  `StructuralFieldStream.domainFieldsFrom`.
- **Failed proof shapes and corrections:** simplification did not initially
  expose the recursive `parseRows` equation under the computed successor
  length; changing the goal to an explicit `Nat.succ` and source-row append
  made the count invariant available. The structural-output induction also
  needed the row output and raw-field encoders unfolded on the induction
  hypothesis before the append equality could rewrite. Both corrections are
  proof-local and leave the executable definitions unchanged.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the
  parser, checked encoding, indexed-row specification, exact row-concatenation
  and structural-target lemmas, module correspondence note, and five axiom
  audits. `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` synchronize the new boundary while retaining
  **Partial** status; this entry records the run.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; targeted `lake build
  PhdThesisLean.AllDifferentCSPMachine
  PhdThesisLean.AllDifferentCSPEncoding PhdThesisLean.AllDifferentCSP` (3100
  jobs); and full `lake build` (3123 jobs). New `#print axioms` audits report
  only the standard `propext`, `Classical.choice`, and `Quot.sound`
  dependencies. The final diff and prohibited-token scans follow this entry
  before commit.
- **Ending state before commit:** one coherent checked domain-section contract
  plus synchronized correspondence/status documentation; no thesis, sibling,
  or unrelated repository work was changed.
- **Best next step:** implement the finite driver for
  `DomainFieldSection.inputFinEncoding`: count down the checked rows and their
  values, maintain and increment the current binary index even for an empty
  row, reuse the checked per-row output contract, and package the exact
  `RuntimeStructuralView.indexedDomainOccurrences` map as a
  `TM2ComputableInPolyTime` witness. Then splice the scope branch and stage the
  variable/record-count header.

## 2026-09-02 05:34 AEST — extract the complete domain-row payload

- **Starting state:** clean synchronized `main` at
  `67a09ba210a12f5e4b2ef005e5bf88b64fa6b430`. A fresh live fetch confirmed
  local `HEAD` and `origin/main` agreed, so no fast-forward was needed. The
  active thesis checkout was clean at `f1107f5db8ddf3bb2bb529e1afadf1fc3dff7e9d`;
  its proof of `cor:all-different-csp` still claims the complete polynomial
  compiler, so the Lean corollary remains **Partial**.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized at
  `e80f20bdc5f5238a504ac28927cebc69b8b957d9`. Its new pair-preprocessing to
  reduction-control bridge remains useful for later paired phases, but it does
  not provide the exhaustion-delimited indexed-row loop required here. The
  sibling and active thesis were not changed.
- **Chosen increment:** removed the decoder-checked outer domain count with a
  concrete finite machine and preserved the complete count-prefixed row
  payload byte-for-byte in semantic source order. This removes one live binary
  counter from the pending indexed-row loop: after this pass, that loop can
  halt exactly when its checked row payload is exhausted.
- **Headline declarations:** `domainRowPayloadComputer` is a concrete
  three-stack finite machine. `domainRowPayload_outputsInTime` proves that it
  maps `DomainFieldSection.inputEncode domains` to exactly
  `SourceOrderRawFields.encode (DomainFieldSection.rowFields domains)` in at
  most `2s+1` steps for complete input length `s`.
  `domainRowPayloadComputableInPolyTime` packages the corresponding
  `TM2ComputableInPolyTime` witness. The execution proof treats the empty
  domain section separately and retains the first row delimiter for every
  nonempty section.
- **Failed proof shapes and corrections:** the first stack-step proofs left
  `Function.update` equalities unresolved; extensional stack-case proofs close
  those obligations. A nested payload-staging induction inherited the wrong
  outer state, so it was replaced by a reusable state-general
  `domainRowPayload_stash_evals` lemma. Finally, splitting an arbitrary encoded
  payload made its leading delimiter difficult to recover; splitting the
  semantic domain list instead exposes the empty case and the nonempty
  delimiter by definition. These were proof-shape failures, not changes to the
  machine contract.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the finite
  program, exact phase and end-to-end executions, linear runtime theorem,
  polynomial wrapper, and two axiom audits. `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` synchronize the new boundary while retaining **Partial**
  status; this entry records the run.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; targeted `lake build
  PhdThesisLean.AllDifferentCSPMachine
  PhdThesisLean.AllDifferentCSPEncoding PhdThesisLean.AllDifferentCSP` (3100
  jobs); and full `lake build` (3123 jobs). The new `#print axioms` audits for
  `domainRowPayload_outputsInTime` and
  `domainRowPayloadComputableInPolyTime` report only `propext`,
  `Classical.choice`, and `Quot.sound`. Final diff and prohibited-token scans
  follow this entry before commit.
- **Ending state before commit:** one coherent checked outer-header removal
  pass plus synchronized correspondence/status documentation; no thesis,
  sibling, or unrelated repository work was changed.
- **Best next step:** build the exhaustion-delimited indexed-row driver over
  `DomainFieldSection.rowFields`: read each binary row count, attach and
  increment the canonical index even for empty rows, reuse the checked
  `DomainFieldRow` output contract, and prove exact agreement with
  `DomainFieldSection.outputEncode`. Then splice the scope branch and stage the
  variable and exact record-count headers.

## 2026-09-04 06:22 AEST — execute the complete indexed domain section

- **Starting state:** clean synchronized `main` at
  `96b0b17533c8b1ba045a5923dc5f228e66007cb6`; a fresh fetch confirmed local
  `HEAD` and `origin/main` agreed, so no fast-forward was needed. The active
  thesis checkout remains at `f1107f5db8ddf3bb2bb529e1afadf1fc3dff7e9d`;
  its proof of `cor:all-different-csp` still claims a complete polynomial
  compiler, so the Lean corollary remains **Partial**.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized at
  `863291d64ba4f3da798d4232514e98b9933917ea`. Its checked sequential and
  composition APIs remain available, but it has no exhaustion-delimited
  count-prefixed-row driver to reuse. The sibling and thesis were not changed.
- **Chosen increment:** implemented the complete domain-section transducer over
  `DomainFieldSection.rowPayloadFinEncoding`. The machine parses every checked
  row count, explicitly counts down the remaining values, retains and copies a
  canonical binary variable index, increments it after every row, and emits
  every exact `[3, 0, index, value]` occurrence block in source order. Empty
  sections, empty rows, singleton rows, payload exhaustion, and binary carry
  growth are handled by the general execution proof.
- **Headline declarations:** the new
  `PhdThesisLean/AllDifferentCSPStructuralMachine.lean` module defines
  `domainSectionProgram` and `domainSectionComputer`;
  `domainSection_outputsInTime` proves exact output
  `DomainFieldSection.outputEncode domains` within `100 * (s+1)^3` steps for
  checked payload bit length `s`; and
  `domainSectionComputableInPolyTime` packages the concrete machine as a
  `TM2ComputableInPolyTime` witness for exactly
  `RuntimeStructuralView.indexedDomainOccurrences`. `PhdThesisLean.lean` now
  imports the module.
- **Failed proof shapes and corrections:** a direct structural recursive call
  in the end-versus-boundary time lemma did not expose Lean's induction
  hypothesis; using the named hypothesis closed the shared suffix. Initial
  `nlinarith`/`omega` attempts could not normalize products and squares in the
  value-loop recurrence, so explicit ring equalities exposed the linear
  differences before `omega`. The first section-time proof case-split after
  introducing dependent hypotheses, leaving mismatched payload expressions;
  moving the split into a separate `domainSectionRunTime_le` lemma specialized
  all bounds cleanly. An attempted reuse of `evalsToInTimeMono` failed because
  the imported helper is private; the module's already-present local monotonic
  helper was used instead.
- **Files changed:** added
  `PhdThesisLean/AllDifferentCSPStructuralMachine.lean`; imported it from
  `PhdThesisLean.lean`; and synchronized the runtime boundary and remaining
  obligations in `AllDifferentCSP.lean`, `AllDifferentCSPEncoding.lean`,
  `AllDifferentCSPMachine.lean`, `README.md`, and `THEOREM_STATUS.md`.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPStructuralMachine.lean`; full `lake build`
  (3124 jobs); `git diff --check`; and a repository Lean-source scan for
  `sorry`, `admit`, project `axiom` declarations, `unsafe`, and
  `proof_wanted` (all empty). The two new `#print axioms` audits report only
  `propext`, `Classical.choice`, and `Quot.sound`.
- **Ending state before commit:** one coherent checked outer domain-row driver
  plus synchronized correspondence/status documentation; no thesis, sibling,
  or unrelated repository work was changed.
- **Best next step:** compose the checked outer-count removal pass with
  `domainSectionComputableInPolyTime`, then implement the analogous
  exhaustion-delimited scope-section loop using
  `scopeFieldBlockComputableInPolyTime` and stage the variable and exact
  record-count headers for the complete raw `RuntimeStructuralView`.

## 2026-09-03 05:32 AEST — retain structured domain-row payloads

- **Starting state:** clean synchronized `main` at
  `06e163b2e4c68519ae39cb1f254af3ea5a4b6e6e`. The initial sandboxed fetch was
  blocked by restricted DNS; the approved network retry succeeded and
  confirmed local `HEAD` and `origin/main` still agreed, so no fast-forward was
  needed. The active thesis checkout remains at
  `f1107f5db8ddf3bb2bb529e1afadf1fc3dff7e9d` but now contains broader user
  edits, including `sudoku-via-padic-regression/body.tex`; all were read only
  and preserved. Its proof still states the complete polynomial compiler, so
  the Lean corollary remains **Partial**.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` is clean and synchronized at
  `c262973e844d7f3d3292816adc30af18276ac185`. Its latest paired-reduction
  dispatcher does not supply the required repeated count-prefixed-row driver,
  so no generic foundation was duplicated and the sibling was not changed.
- **Chosen increment:** gave the existing outer-count removal machine a
  checked structured codomain instead of treating its result only as a flat
  list of naturals. The new decoder parses count-prefixed rows to exact payload
  exhaustion, consumes a count even for an empty row, rejects partial rows,
  and proves that no row boundary is lost.
- **Headline declarations:** `DomainFieldSection.parseRowPayload_rowFields`
  proves the exhaustion parser reconstructs every domain list;
  `rowFields_injective` and `rowPayloadEncode_injective` prove the flat payload
  uniquely determines its rows; `rowPayloadFinEncoding` is the resulting
  checked `FinEncoding (List (List ℕ))`;
  `rowPayloadEncode_length_le_inputEncode_length` proves removal of the outer
  count is nonexpansive; and
  `domainRowPayloadStructuredComputableInPolyTime` reuses the concrete
  `domainRowPayloadComputer` as an identity machine on structured domains in
  at most `2s+1` steps.
- **Failed proof shapes and corrections:** an attempted proof used the
  nonexistent lemma `List.length_drop_le`; simplifying the well-founded goal
  exposed the arithmetic inequality directly, which `omega` closes. Rewriting
  the well-founded recursive parser by its bare definition name also failed;
  Lean's generated `parseRowPayload.eq_def` is the correct equation theorem.
- **Files changed:** `PhdThesisLean/AllDifferentCSPMachine.lean` adds the
  structured encoding, semantic and size lemmas, polynomial wrapper, and six
  axiom audits. `PhdThesisLean/AllDifferentCSP.lean`,
  `PhdThesisLean/AllDifferentCSPEncoding.lean`, `README.md`, and
  `THEOREM_STATUS.md` synchronize the new boundary while retaining **Partial**
  status; this entry records the run.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPMachine.lean`; targeted `lake build
  PhdThesisLean.AllDifferentCSPMachine
  PhdThesisLean.AllDifferentCSPEncoding PhdThesisLean.AllDifferentCSP` (3100
  jobs); full `lake build` (3123 jobs); `git diff --check`; and a null-delimited
  tracked Lean-source scan for `sorry`, `admit`, project `axiom`, `unsafe`, and
  `proof_wanted` (all empty). The new `#print axioms` audits report only
  `propext`, `Classical.choice`, and `Quot.sound`.
- **Ending state before commit:** one coherent checked structured-payload
  increment plus synchronized correspondence/status documentation; no thesis,
  sibling, or unrelated repository work was changed.
- **Best next step:** use `DomainFieldSection.rowPayloadFinEncoding` as the
  direct input to the exhaustion-delimited indexed-row driver: read each row
  count, preserve and increment the canonical index even for empty rows, emit
  the exact checked `DomainFieldRow` output, and prove agreement with
  `DomainFieldSection.outputEncode`. Then splice the scope branch and stage the
  variable and exact record-count headers.

## 2026-09-05 05:23 AEST — compose the complete domain-section passes

- **Starting state:** clean synchronized `main` at
  `d2ab12ffdb4db921684045f34fe3a2d05e49375d`; local `HEAD`, the tracking ref,
  and the live `origin/main` ref agreed, so no fast-forward was needed. The
  active thesis checkout remained at
  `f1107f5db8ddf3bb2bb529e1afadf1fc3dff7e9d` with broader user edits,
  including the relevant chapter, all preserved. Its proof still claims the
  complete polynomial compiler, so `cor:all-different-csp` remains **Partial**.
- **Read-only reusable-API review:** sibling
  `/Users/gregb/Documents/devel/lean-np-hardness` was clean and synchronized at
  `f0c5f6d75b7059349ba95744a8320f832110fed1`. Its checked generic
  `compositionComputableInPolyTime` API remains the correct reusable
  foundation; its new pair-output reassembly code does not provide a counted
  scope-list driver. The sibling and thesis were not changed.
- **Chosen increment:** closed the composition gap between the complete
  counted domain-section input and the exact tagged domain-occurrence output.
  The outer-count-free row payload is now produced, decoded, and consumed
  inside one checked sequential finite-machine composition rather than being
  assumed at the public boundary.
- **Headline declaration:**
  `completeDomainSectionComputableInPolyTime` composes
  `domainRowPayloadStructuredComputableInPolyTime` with
  `domainSectionComputableInPolyTime`. Its source is
  `DomainFieldSection.inputFinEncoding`, its target is
  `DomainFieldRow.outputFinEncoding`, and its function is exactly
  `RuntimeStructuralView.indexedDomainOccurrences`, including empty sections,
  empty and singleton rows, and index advancement across every row.
- **Proof/API notes:** the existing generic composition theorem accepted the
  two checked components directly. A small wrapper discharges only the
  definitional `indexedDomainOccurrences ∘ id` equality; no failed proof
  approach or new machine assumption was introduced.
- **Files changed:** `PhdThesisLean/AllDifferentCSPStructuralMachine.lean`
  adds the composed theorem and axiom audit. `AllDifferentCSP.lean`,
  `AllDifferentCSPEncoding.lean`, `AllDifferentCSPMachine.lean`, `README.md`,
  and `THEOREM_STATUS.md` synchronize the verified boundary while retaining
  **Partial** status; this entry records the run.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPStructuralMachine.lean`; full `lake build`
  (3124 jobs); `git diff --check`; and null-delimited tracked Lean-source scans
  for `sorry`, `admit`, project `axiom` declarations, `unsafe`, and
  `proof_wanted` (all empty). The new `#print axioms` audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- **Ending state before commit:** one coherent checked composition from the
  complete domain-section input to its exact structural occurrence stream,
  plus synchronized correspondence/status documentation; no thesis, sibling,
  or unrelated repository work was changed.
- **Best next step:** define the checked exhaustion-delimited scope-section
  contract and implement its repeated finite-machine driver using the existing
  `scopeFieldBlockComputableInPolyTime`; then stage the variable and exact
  record-count headers around the composed domain and scope outputs.

## 2026-09-06 05:23 AEST — check the complete scope-section contract and assembly

- **Starting state:** clean synchronized `main` at
  `f5bca30bdbb2aed69801b2b129e92e78c6806bd0`; `git fetch origin`
  confirmed no upstream advance. The active thesis remained at
  `f1107f5db8ddf3bb2bb529e1afadf1fc3dff7e9d` with broader user edits,
  including the relevant chapter, all preserved. Its current corollary and
  proof still require the full polynomial compiler; the corollary stays
  **Partial**.
- **Read-only reusable-API review:** sibling `lean-np-hardness` was clean and
  synchronized at `be2e978b974bb7b80a62537f4c7090457691e01d`.
  Its checked sequential-composition API remains available through the pinned
  dependency. Its newer pair-left execution result does not supply a generic
  repeated-scope/list-map driver. Neither sibling repository was changed.
- **Chosen increments:** define the checked complete scope-section output,
  reuse the existing counted-row source parser and header-removal machine,
  prove a linear bound on the complete tagged output, and identify the exact
  header/section assembly for the whole raw structural target.
- **Declarations:** `ScopeFieldSection.inputFinEncoding` and
  `rowPayloadFinEncoding` reuse the existing domain-section encodings without
  duplicating the parser. `outputFinEncoding`, `outputDecode_encode`, and
  `outputEncode_injective` recover all scopes and entries exactly, preserving
  empty scopes, repeated scopes, repeated entries, and source order. The
  decoder reuses checked count-prefixed parsing before checking each tag;
  `outputDecode_rejects_missing_tag` and `outputDecode_rejects_wrong_tag`
  certify the malformed-tag cases. `outputEncode_eq_taggedRowPayload`,
  `rowPayloadEncode_eq_block_inputs`, and `outputEncode_eq_structuralFields`
  connect the shared parser, existing per-scope machine interfaces, and the
  precise structural target.
- **Size and runtime boundaries:** `outputEncode_length_le_payload_add`
  charges at most three extra raw bit-or-delimiter cells per scope.
  `outputEncode_length_le_linear` bounds all tagged output by `4s` in the
  actual raw payload length, and `outputEncode_length_le_input_linear` gives
  the same bound against the complete counted section input. These are
  output-size results, not a running-time theorem for repeated scope
  processing. `scopeRowPayloadStructuredComputableInPolyTime` reuses the
  existing concrete `2s+1`-step machine unchanged to remove the outer count.
- **Exact assembly:** `StructuralFieldStream.headerEncode` carries the
  `1 + domainEntryCount + scopes.length` outer count and the singleton
  variable-count row. `encode_eq_header_sections` proves the full stream is
  those headers followed by the complete domain and scope outputs.
  `raw_encode_eq_reversed_sections` identifies reverse section/header staging
  exactly with `RuntimeStructuralView.rawFinEncoding`, the existing framing
  machine's checked input. These equations do not supply executable staging.
- **Failed proof shapes and correction:** a broad `simp` left unapplied
  `ScopeFieldBlock.outputEncode`/`inputEncode` constants inside `List.flatMap`;
  structural induction on the scope list exposed applied heads and closed the
  equalities. Broad simplification also rewrote `List.mapM` through `List.map`
  before the reconstruction lemma matched; `simp only` on the shared decoder
  round trip followed by `mapM_untag_tagged` solved that goal. No failed
  machine construction or new semantic assumption was introduced.
- **Files changed:** new `PhdThesisLean/AllDifferentCSPScopeSection.lean` and
  its root import; correspondence comments in `AllDifferentCSP.lean`,
  `AllDifferentCSPEncoding.lean`, `AllDifferentCSPMachine.lean`, and
  `AllDifferentCSPStructuralMachine.lean`; synchronized `README.md` and
  `THEOREM_STATUS.md`; and this log.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPScopeSection.lean`; full `lake build` (3125
  jobs); `git diff --check`; and scans of all 21 project Lean files, including
  the new file, for `sorry`, `admit`, `axiom`, `unsafe`, and `proof_wanted`
  (zero matches). All nine new headline `#print axioms` audits report only
  `propext`, `Classical.choice`, and `Quot.sound`; the new module has no
  warnings.
- **Ending state before commit:** checked scope input/output contracts,
  linear complete-output bounds, reused finite-machine payload extraction,
  and exact whole-stream assembly identities, with the full corollary still
  **Partial**. No unrelated work was changed.
- **Best next step:** construct the finite driver from
  `ScopeFieldSection.rowPayloadFinEncoding` to
  `ScopeFieldSection.outputFinEncoding`, computing the identity on complete
  scope lists. The existing `scopeFieldBlockComputer` copies its entire input
  suffix to exhaustion, so it cannot simply be run on a concatenated section:
  isolate one counted row at a time or fuse a binary-count-limited copying
  loop. Preserve empty rows and use canonical binary predecessor to count
  entries. Then implement the exact `headerEncode` staging and full input
  splitting, using the new assembly/reversal equalities for correctness.

## 2026-09-07 AEST — execute and compose the complete scope section

- **Starting state:** clean synchronized `main` at
  `a31d02841b12981aa939f41547236038e98ad997`; `git fetch origin`
  confirmed no upstream advance. Read the repository instructions, theorem
  status, correspondence notes, recent automation log/memory, and relevant
  semantic, encoding, domain-machine, and scope-interface declarations.
- **Statement and reusable-API review:** the active thesis remained at
  `f1107f5db8ddf3bb2bb529e1afadf1fc3dff7e9d`, with broader user edits
  including `sudoku-via-padic-regression/body.tex`; all were preserved.
  Its current `cor:all-different-csp` still requires polynomial construction
  and exact minimum-conflict/satisfiable semantics. Read-only sibling
  `lean-np-hardness` was clean and synchronized at
  `3852bc43c125d8f1005662496b6feefd57a00a66`. Its newer canonical
  pair-left output result does not supply a repeated counted-row driver.
  Reused `compositionComputableInPolyTime` from the existing pinned dependency
  without changing either sibling or updating dependency pins.
- **Chosen increments:** implement the whole scope-payload driver, prove its
  exact execution and quadratic bit-level time bound, and compose the checked
  outer-count-removal pass so the full counted section is accepted internally.
- **Concrete machine:** `ScopeSectionMachine.program` and `computer` use five
  stacks over `Option Bool` and eleven control labels. The first-field pass
  saves the original binary length while emitting its successor, then inserts
  the exact scope tag. The entry loop explicitly decrements a canonical binary
  count and copies precisely one raw field per iteration. Looking ahead puts
  a delimiter back on the input stack, so the same execution proof handles
  empty rows, empty sections, repetitions, singleton scopes, and final-row
  exhaustion. All non-output stacks are empty at halt.
- **Checked declarations:** `scopeSection_outputsInTime` proves exact
  `ScopeFieldSection.outputEncode` output in at most `20 * (s+1)^2` steps
  for actual checked payload bit length `s`.
  `scopeSectionComputableInPolyTime` packages the identity on whole scope
  lists from `rowPayloadFinEncoding` to `outputFinEncoding` using mathlib's
  standard finite-machine API. `completeScopeSectionComputableInPolyTime`
  composes the existing linear header-removal machine with that driver from
  `ScopeFieldSection.inputFinEncoding`. No caller-supplied intermediate is
  needed for this complete-section result.
- **Bit-size reasoning:** entry countdowns are bounded by the number of
  explicitly encoded fields, each costing at least one delimiter; arbitrary
  entry magnitudes are charged only by their binary word lengths. Per-row
  work is bounded by twelve times the squared row wire length. Summing rows
  and restoring the existing linearly bounded output gives the displayed
  quadratic whole-section bound.
- **Failed proof shapes and corrections:** the identifier `stacks` conflicts
  with imported TM2 syntax, so the local function is `stackContents`.
  Positional construction of `EvalsToInTime` tried to fill its inherited
  `EvalsTo` field with a natural; named `steps`, `evals_in_steps`, and
  `steps_le_m` fields resolve the exact API shape. Configuration equality
  needed `congr 1` before stack extensionality. Broad simplification left
  equivalent reverse/map payloads and differently associated step sums;
  explicit boundary normalization followed by `convert` and `omega` closed
  those goals. The previously logged suffix-to-exhaustion scope machine was
  not rerun on a concatenated section: the new driver limits copying with a
  binary countdown and restores lookahead delimiters.
- **Files changed:** new `PhdThesisLean/AllDifferentCSPScopeMachine.lean`
  and root import; synchronized README, theorem status, semantic/encoding/
  machine correspondence comments, scope-interface comments, and this log.
  `cor:all-different-csp` remains **Partial**.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPScopeMachine.lean`; full `lake build`
  (3126 jobs); staged `git diff --check`; and a null-delimited inventory scan
  of all 22 tracked/new Lean files, including the new module and Lake config,
  for `sorry`, `admit`, project `axiom` declarations, `unsafe`, and
  `proof_wanted` (zero matches). All four new `#print axioms` audits report
  only `propext`, `Classical.choice`, and `Quot.sound`. The new module has no
  warnings. The complete final tree was rebuilt after a stale source
  correspondence comment was corrected.
- **Ending state before commit:** both full section machines are checked,
  including scope execution, its explicit payload time bound, and its
  complete-counted-input composition. Status/correspondence notes are
  synchronized and no unrelated work was changed. The full corollary remains
  **Partial**; the next structural composition obligations are explicit.
- **Best next step:** split the complete source-order compiler input into its
  counted domain and scope sections while retaining the variable count and
  exact output-record count. Stage `StructuralFieldStream.headerEncode`, run
  both complete section machines, and use `encode_eq_header_sections` and
  `raw_encode_eq_reversed_sections` to assemble the full raw structural view
  before the checked framing pass. Canonical relabelling, edge deduplication,
  objective emission, and final compiler composition still remain after that.

## 2026-09-08 AEST — split the complete source and compose paired domain expansion

- **Starting state:** clean synchronized `main` at
  `ff4d8a195669a1702feead62280f982374c95f1f`; `git fetch origin` and
  the ahead/behind check confirmed no upstream advance. Read the repository
  instructions, theorem status, correspondence notes, relevant Lean sources,
  recent log, and automation memory before choosing the increment.
- **Statement and reusable-API review:** the active thesis remained at
  `f1107f5db8ddf3bb2bb529e1afadf1fc3dff7e9d`, with broader user edits
  including the active `sudoku-via-padic-regression/body.tex` corollary and
  proof; all were preserved. The read-only `lean-np-hardness` sibling was
  clean at `fb7ca30caecc88ffacea9a91fc292ee35b54fdd7`, matching its live
  remote. Its new `MachineAdapters.pairReductionComputableInPolyTime` now
  supplies the checked generic operation needed to transform domains while
  preserving scopes. Updated this project's dependency pin and manifest to
  that exact commit; `lake update lean_np_hardness` changed no other package
  revision or toolchain. Neither sibling repository was edited.
- **Chosen increments:** split the complete source into the existing checked
  domain/scope encodings, compose that split from the actual compiler input,
  and reuse the generic pair-left machine to expand all domains while
  retaining every scope.
- **Concrete source splitter:** new
  `PhdThesisLean/AllDifferentCSPSourceSections.lean` defines
  `RuntimeSourceSections.inputFinEncoding` by reusing the existing complete
  source-order runtime encoding and its decoder. `outputFinEncoding` reuses
  `PairEncoding.finEncoding` with the counted domain section and the
  exhaustion-delimited scope payload. `inputEncode_eq_sections` exposes the
  exact two removable source fields followed by those sections;
  `output_length_le_input` proves the entire tagged output has no more
  finite-alphabet cells than the raw input.
- **Exact execution and runtime:** `SourceSectionMachine.program`/`computer`
  use six finite-alphabet stacks, with independent canonical binary row and
  entry countdowns. They skip the outer list count and singleton header
  length, retain the domain count, copy exactly the declared domain rows,
  and tag the remaining scope payload separately. A shared counter proof
  checks binary borrow for both counters; looked-ahead delimiters are
  restored before the next phase. `sourceSections_outputsInTime` and
  `sourceSectionsComputableInPolyTime` prove exact canonical paired output
  within `40 * (s+1)^2` steps for complete raw input length `s`. The theorem
  covers empty sections, empty rows, repetitions, zero-valued entries, and
  arbitrary entry magnitudes charged by binary length; every non-output
  stack is empty at halt.
- **Composed declarations:** `runtimeCompilerSourceSystemComputableInPolyTime`
  reuses the existing compiler-to-source witness at the runtime-system type.
  `runtimeCompilerSectionsComputableInPolyTime` composes preparation and
  splitting from `RuntimeCompilerInput.finEncoding`.
  `pairedDomainSectionComputableInPolyTime` applies the pinned generic
  pair-left API to `completeDomainSectionComputableInPolyTime`, preserving
  the scope payload. `runtimeCompilerDomainAndScopesComputableInPolyTime`
  composes the actual Boolean compiler input to exactly
  `(RuntimeStructuralView.indexedDomainOccurrences C.domains, C.scopes)`
  under the existing paired output encoding. The explicit quadratic bound
  belongs to the splitter; full-input compositions use the checked generic
  polynomial bounds, not that same quadratic constant.
- **Failed proof shapes and corrections:** checking the new import before its
  dependency build reported missing `PairReductionComputable.olean`; the
  targeted dependency build resolved it. A repeated-row `convert` left a
  configuration equality with local `after`/`count` definitions opaque to
  `omega`; unfolding those local definitions closed the equality before
  arithmetic. Whole-run composition initially mismatched differently
  associated delimiter/append expressions; `List.cons_append` and
  `List.append_assoc` normalization made the boundaries agree. Rewriting
  only the reversed output equation left canonical forward output and length
  goals; applying `congrArg List.reverse` supplied the forward equation,
  after which `simp` and `omega` closed both. No unproved machine assumption
  or unresolved proof error remains.
- **Files changed:** the new source-section module and root import; dependency
  pin and manifest; correspondence comments in the semantic, encoding,
  primitive-machine, and domain-machine modules; synchronized README and
  theorem status; and this log. The full corollary remains **Partial**.
- **Best next step:** preserve the variable-count header before domain
  expansion, apply the scope machine within the paired representation while
  retaining the domain output and necessary counts, then stage
  `StructuralFieldStream.headerEncode` and use the existing assembly/reversal
  equations before framing. Indexed occurrences alone lose the number of
  trailing empty domains, so they cannot reconstruct the header on all runtime
  inputs. Canonical relabelling, edge deduplication, objective emission, and
  final compiler composition remain after structural assembly.
- **Verification succeeded:** targeted
  `lake build LeanNPHardness.PairReductionComputable` (1145 jobs), direct
  `lake env lean PhdThesisLean/AllDifferentCSPSourceSections.lean`, and full
  `lake build` (3136 jobs). All eight new headline axiom audits report only
  `propext`, `Classical.choice`, and `Quot.sound`; the new module has no
  warnings. The null-delimited tracked/new inventory scan covered all 23
  project Lean files, including the Lake config, with zero matches for
  `sorry`, `admit`, project `axiom` declarations, `unsafe`, or `proof_wanted`.
  `git diff --check` passed.
- **Ending state before commit:** the complete source split and the actual
  compiler-to-indexed-domains-with-scopes composition are checked, with
  synchronized status and correspondence notes. No unrelated work changed;
  the complete corollary is still **Partial**. The verified increment is
  ready to commit and push to `main`.

## 2026-09-09 AEST — compose both processed structural sections from compiler input

- **Starting state:** clean synchronized `main` at
  `a6767ed402506a48fa9e828565dc658ccb9169d3`. Read the repository
  instructions, theorem status, relevant README and Lean correspondence,
  active corollary/proof, recent automation log, and automation memory.
  `git fetch origin` and the ahead/behind check confirmed no upstream advance.
- **Statement and reusable-API review:** the active thesis remained at
  `f1107f5db8ddf3bb2bb529e1afadf1fc3dff7e9d`, with broader user edits
  including the all-different chapter, all preserved. The read-only
  `lean-np-hardness` sibling was clean at
  `dd5df1a63e0c3970b9bf8b5c012dca9cfe9459b0`, matching its live remote.
  Its latest increment transports NP membership; its checked pair API still
  transforms the left component only. Reused the existing
  `pairReductionComputableInPolyTime` and sequential-composition APIs at the
  current `fb7ca30` dependency pin. No dependency or sibling was changed.
- **Chosen increments:** implement a small raw-section exchange, use it to
  compose the existing scope machine while preserving the expanded domains,
  and compose the complete result from the actual Boolean compiler input.
- **Concrete exchange:** new
  `PhdThesisLean/AllDifferentCSPProcessedSections.lean` defines
  `SectionPairExchange.program` and `computer`, with four finite-alphabet
  stacks and three labels. The program classifies and retags both section
  streams, then restores their cells in exchanged section order.
  `SectionPairExchange.outputsInTime` checks exact canonical output in at
  most `2s+3` steps for complete paired wire length `s`. It covers arbitrary
  raw words, empty sections, and every bit and delimiter; all non-output
  stacks and the control register are empty at halt. The local exchange uses
  the sibling's existing pair encoding/projections and does not duplicate
  generic machine composition or pair-reduction foundations.
- **Checked compositions:**
  `exchangeDomainScopePayloadComputableInPolyTime` puts scopes first;
  `exchangeScopeDomainOutputComputableInPolyTime` restores the original order
  after processing. `pairedScopeSectionComputableInPolyTime` composes those
  exchanges with the pinned generic pair-left scope machine. Its semantic
  function is identity on the pair, but the scope wire representation changes
  from counted-row payload to exact tagged records. Domain occurrences and
  every scope, entry, boundary, and repetition are retained.
  `pairedScopeSection_output_length_le` bounds the complete paired output by
  four times its complete paired input length, including the retained domains.
  `runtimeCompilerProcessedSectionsComputableInPolyTime` composes source
  preparation, splitting, domain expansion, and scope processing from
  `RuntimeCompilerInput.finEncoding`, emitting both exact tagged sections
  internally. The full composition has the checked generic polynomial bound;
  the displayed linear constant is for each exchange alone.
- **Failed proof shapes and corrections:** `List.reverse_map` is not a
  declaration in the pinned API; the checked lemma is `List.map_reverse`.
  Normalizing only the transfer lemma then left its starting configuration
  different from the scanner endpoint. Normalizing `hscan`, `hleft`, and
  `hright` together with `List.map_reverse` and `List.reverse_reverse` made
  all boundaries match. The remaining goal was only step-count arithmetic.
  Removed unused simplifier arguments and an unnecessary `<;>` after the
  successful direct check. No unresolved error or unproved machine premise
  remains.
- **Files changed:** the new processed-section module and root import;
  synchronized README, theorem status, correspondence comments in the
  semantic, encoding, primitive-machine, source-section, and domain-machine
  modules; and this log. `cor:all-different-csp` remains **Partial**.
- **Best next step:** retain the variable count and exact output-record count
  before domain expansion, carry them through both checked section passes,
  and stage `StructuralFieldStream.headerEncode`. Then assemble/reverse the
  sections using the existing exact identities and apply the framing bridge.
  Trailing empty domains make recovery of the variable count from occurrence
  records invalid on general runtime inputs. Canonical relabelling, edge
  deduplication, objective emission, and final compiler composition remain.
- **Verification succeeded:** direct `lake env lean
  PhdThesisLean/AllDifferentCSPProcessedSections.lean`, followed by full
  `lake build` (3137 jobs) after all source/comment edits. All seven new
  headline axiom audits report only `propext`, `Classical.choice`, and
  `Quot.sound`; the new module has no warnings in the final build. The
  null-delimited tracked/new inventory scan covered all 24 project Lean
  files, including the Lake configuration, with zero matches for `sorry`,
  `admit`, project `axiom` declarations, `unsafe`, or `proof_wanted`.
  `git diff --check` passed.
- **Ending state before commit:** both exact processed sections are now
  constructed by a checked polynomial-time machine from the actual compiler
  input, with synchronized status/correspondence notes and no unrelated work
  changed. The full corollary remains **Partial**. The completed verified
  increment is ready to commit and push to `main`.

### 2026-09-09 17:18 AEST — status explanation and correspondence correction

- Answered the follow-up about progress against current checked commit
  `37378ade457faa1824c9865a1e7f6b69c6182714`, with a clean worktree.
- Found stale prose in four parts of `THEOREM_STATUS.md`: the headline row
  reflected the new processed-section composition, but the detailed notes
  still called it unfinished. Corrected those paragraphs against the checked
  declarations; no Lean code or theorem classification changed.
- The tracked tables contain 29 statements: 20 complete (including one
  qualified), two partial, and seven pending. The all-different corollary's
  semantics, encoding/size bounds, prime selection, and paired structural
  section passes are checked. Header assembly, machine-level relabelling,
  graph deduplication, objective emission, and end-to-end composition remain.
  Statement counts do not measure remaining proof effort.
- Validation: reviewed the documentation diff and ran `git diff --check`.
  The prior successful 3137-job build still applies to unchanged Lean sources.
  This documentation correction is a separate verified increment.


## 2026-09-09 — move reusable foundations upstream and consume the library

- **Authorization and starting state:** the user explicitly requested moving
  the identified reusable components into `../lean-np-hardness`, superseding
  the automation's normal read-only sibling boundary for this migration.
  This repository started clean/synchronized at `84be78d`; the sibling started
  clean/synchronized at `4475e98`. Both fetch/ahead-behind checks showed no
  upstream advance. The thesis prose repository was not changed.
- **Upstream core increment:** committed and pushed `7f90b04` with ten library
  modules: binary/nested-list codecs, raw field encodings, execution helpers,
  framing/serialization, source-order conversion, binary arithmetic, counted-row
  decoding and header removal, Boolean aggregation, and generic pair exchange.
  Generalized exchange to arbitrary finite component alphabets, including empty
  alphabets, and added `MachineAdapters.pairRightComputableInPolyTime`.
  Carrying symbols in finite labels removes any default-symbol assumption.
  Its bound is `4s+6`, replacing the former specialized exchange's `2s+3`.
  Upstream full build passed (1164 jobs), with twenty new headline audits.
- **Upstream prime increment:** committed and pushed
  `db20c69186d2f717155392ed08772a3c03de1398`, adding `BoundedPrime`,
  `IntervalMachines`, `UnaryDivisibilityMachine`, and `PrimeSelectionMachine`.
  Preserved exact unary/padded encodings and all displayed runtime bounds,
  including `1000(q+1)^6` for final selection on unary input. Thirteen new
  headline audits and the final 2195-job full build passed. The library has
  no imports from the downstream thesis and its 40-file prohibited-code scan
  passed. Both upstream commits are pushed and the live remote matches HEAD.
- **Downstream migration:** updated only the `lean_np_hardness` revision in
  `lakefile.lean`/`lake-manifest.json` to `db20c69`; toolchain and all other
  package revisions are unchanged. Removed the generic implementation bodies
  from the semantic, encoding, primitive-machine, and processed-section files.
  Compatibility exports retain the old public theorem names. Renamed generic
  counted-row machines retain thin downstream aliases. The scope composition
  now specializes the upstream right-component API directly.
- **Scope retained here:** `RuntimeSystem`, `RuntimeStructuralView`, CSP record
  tags, indexed domain/scope processing, the source splitter, objective
  construction, and p-adic correctness. The structural field-level specification
  and runtime-system compositions remain downstream. The full all-different
  corollary remains Partial, with its remaining headers/relabelling/graph/
  objective/final-composition obligations unchanged.
- **Extraction corrections:** repaired clipped/dangling comments at source
  boundaries; exported named helper lemmas needed across the new modules;
  moved the shared replication identity into the execution helper module.
  Generic exchange needed explicit intermediate configurations for empty-list
  transitions. The generic arithmetic still advertises its aligned-pair input,
  and the prime machinery still advertises its unary-bound input. Existing
  simplifier-style warnings were carried with the prime proofs.
- **Correspondence:** README and detailed/theorem-table status now identify the
  upstream implementation ownership and the generalized exchange bound.
  Historical automation entries are retained as records of their original
  checked states.

- **Final verification:** downstream `lake build` passed (3151 jobs), including
  the original semantic theorems, encoding/size proofs, structural machines,
  and `runtimeCompilerProcessedSectionsComputableInPolyTime` under the new
  pinned dependency. Parsed every reported axiom set from the final upstream
  and downstream builds; all contain only the three standard axioms.
  The final downstream prohibited-code scan covered all 24 project Lean files.
  `git diff --check` passed, and manifest comparison confirmed that only the
  requested dependency revision changed. No unrelated work was modified.
- **Ending state before downstream commit:** all fourteen reusable modules are
  upstream, built, audited, committed and pushed. Downstream consumes the exact
  verified upstream commit and retains compatibility names with its generic
  implementation bodies removed. Both projects build and the full corollary
  remains Partial. Next formalisation work is the existing structural-header
  retention/assembly target; the normal automation sibling boundary returns
  to read-only after this explicitly authorized migration.

## 2026-09-10 — retain the variable header before structural expansion

- **Starting state:** clean and synchronized `main` at
  `2836d833533f435f0e35597626705c219dde69f8`; fetch confirmed zero divergence.
  Read the run memory, status, correspondence notes, current structural
  modules, and active `cor:all-different-csp` statement/proof. The thesis
  remained at `f1107f5` with its existing user edits preserved. The read-only
  `lean-np-hardness` sibling was clean at `db20c69`, matching its live remote;
  the existing dependency pin already supplies the needed pair-left,
  pair-right, sequential composition, and execution-bound APIs.
- **Chosen increment:** preserve the variable count before domain expansion,
  since occurrence records do not determine the number of trailing empty
  domains. Added `AllDifferentCSPVariableHeader.lean` and its root import.
  `VariableHeader.outputFinEncoding` reuses the source encoding paired with
  mathlib's standard binary `finEncodingNatBool`; `retain` returns the
  unchanged system and its domain-list length. Its decoder reuses the checked
  codecs, and `output_length_le` bounds the complete pair by `2s` cells.
- **Concrete machine:** `VariableHeaderMachine.computer` has four finite
  stacks. It explicitly scans the first three source fields, copies the third
  field's bits to a private header stack, retains every input cell, and emits
  the canonical tagged source/count pair. It preserves all domains, scope
  entries, delimiters, and repetitions; zero variables and trailing empty
  domains need no extra assumption. Every non-output stack is empty at halt.
  `variableHeader_outputsInTime` and `variableHeaderComputableInPolyTime`
  bound the exact output run by `3s+6` for full raw source length `s`.
  `runtimeCompilerVariableHeaderComputableInPolyTime` composes extraction
  from the actual Boolean compiler input, so the count is computed internally.
- **Proof corrections:** the pinned standard natural codec is named
  `finEncodingNatBool`, not `finEncodingNat`; length simplification also needs
  its underlying `encodingNatBool`. `variables` is reserved syntax when used
  as a binder, so the raw-word proof uses `countBits`. The first complete
  execution proof then checked; removed its unused `List.cons_append` simp
  argument. No unresolved machine/API error remains.
- **Correspondence and next step:** README and detailed/headline status now
  record source/count construction. The full corollary remains **Partial**.
  Next carry the retained count through the already checked source split and
  both section passes using the upstream pair-left API. Record-count
  construction, header/section assembly and framing, canonical relabelling,
  deduplicated edges, objective emission, and final compiler composition remain.
- **Verification and ending state:** the direct module check and full
  `lake build` passed (3152 jobs). All five new headline audits and every
  reported build axiom set use only `propext`, `Classical.choice`, and
  `Quot.sound`; the new module has no warnings. The null-delimited tracked/new
  inventory scan covered all 25 project Lean files with zero prohibited-code
  matches. `git diff --check` passed. This verified source/header increment is
  ready to commit and push; no sibling or thesis files were changed.

### 2026-09-10 — carry the saved variable count through both section machines

- **Starting state:** the first verified increment is committed and pushed as
  `5b1e28b8e6ebdfbac4700414f09baf8b78e0c335`. Local HEAD, tracking main, and
  the live remote ref agreed, with a clean worktree before this increment.
- **Checked composition:** added `AllDifferentCSPCountedSections.lean` and
  its root import. `sourceProcessedSectionsComputableInPolyTime` composes the
  existing splitter and both section machines at the raw source boundary.
  `processWithVariableCountComputableInPolyTime` applies the upstream generic
  pair-left API to preserve the copied standard binary count throughout that
  complete pass. `runtimeCompilerCountedSectionsComputableInPolyTime` composes
  from the actual Boolean compiler input to exactly
  `((indexedDomainOccurrences C.domains, C.scopes), C.domains.length)`.
  The complete machine has a checked polynomial bound; `3s+6` remains only the
  local header-copy bound. No generic foundations were copied or repinned.
- **Exact remaining assembly contract:** `CountedSections.finEncoding` reuses
  the existing nested pair and component encodings. The executable
  `toStructuralView` reconstructs the target from this tuple;
  `toStructuralView_ofRuntimeSystem` checks exact equality without any axioms.
  `recordCount_ofRuntimeSystem` counts every occurrence and scope, including
  repetitions and empty scopes. `recordCount_le_encode_length` charges every
  record to its encoded cells and bounds the total by the actual tuple length,
  independently of entry/index magnitude. `headerEncode_ofRuntimeSystem` and
  `raw_encode_eq_sections` identify the header and full reversed assembly
  exactly with the existing raw structural-view target. These are encoding
  identities, not an assertion that the final merge machine already exists.
- **Proof corrections:** simultaneous simplification unfolded `ofRuntimeSystem`
  before the named `recordCount_ofRuntimeSystem` rewrite could match; doing
  that rewrite first fixed the header identity. The raw-source composition
  needed `CountedSections.sectionsFinEncoding` unfolded on both sides to match
  the encoded output after simplification. The corrected direct module check
  passed without warnings. All eight new headline axiom audits use only the
  standard axioms, with the reconstruction equality axiom-free.
- **Correspondence and best next step:** synchronized the headline catalogue,
  detailed status, README, and relevant module correspondence comments,
  including a stale semantic comment that still listed paired scope processing
  as unfinished. The full corollary remains **Partial**. Next build the concrete
  record-count/merge machine over `CountedSections.finEncoding`, emit
  `CountedSections.headerEncode`, and realize `raw_encode_eq_sections` before
  composing the existing framing bridge. After that, machine-level canonical
  relabelling, deduplicated graph construction, objective emission, and final
  compiler composition remain. The sibling and active thesis were read-only.
- **Final verification and ending state:** the direct counted-section check
  and full `lake build` passed (3153 jobs). All 190 nonempty reported axiom
  sets contain only `propext`, `Classical.choice`, and `Quot.sound`; the new
  reconstruction equality is axiom-free. Neither new module has warnings.
  The prohibited-code scan covered all 26 project Lean files with zero
  matches, and `git diff --check` passed. The sibling remains clean at the
  unchanged pin, and the thesis retains its original dirty-file inventory.
  This second verified increment is ready to commit and push; record-count
  generation and raw structural assembly remain the next machine target.

### 2026-09-11 — assemble the complete structural payload

- **Starting state:** clean `main` at `e1eae4197a3d87e462934d5f4a7f6d93c2a3313e`,
  with tracking and live remote parity after fetch. The active thesis still
  has its existing user edits; its live `cor:all-different-csp` statement and
  proof retain the explicit-input, canonical relabelling, deduplicated graph,
  and polynomial construction obligations. Read-only `lean-np-hardness` is
  clean at `9852d948abae3d35c49b5ebd4021bf1627e7328c`; the new CNF encoding
  does not supply outer-record-count construction. Kept dependency pin `db20c69`.
- **Chosen increment:** separate exact singleton-header/section assembly from
  the still-missing total-row counter. Added `AllDifferentCSPStructuralAssembly.lean`
  and `AllDifferentCSPAssemblyMachine.lean`, plus root imports. The new
  `RuntimeStructuralView.payloadFinEncoding` reuses the upstream exhaustion-
  delimited counted-row decoder and the existing structural tag parser.
  It encodes every semantic field; only the redundant outer row count is
  absent. `payloadDecode_encode` proves exact recovery and
  `payloadEncode_toStructuralView_length` proves exactly three added header
  cells relative to the complete counted-section input.
- **Checked machine:** `StructuralAssemblyMachine.computer` uses four finite
  stacks to remove the pair transport tags, retain all record tags and numeric
  fields, and move the saved variable count into its singleton row.
  `structuralAssembly_outputsInTime` / `structuralAssemblyComputableInPolyTime`
  prove the exact merged output in at most `2s+3` steps for actual tuple wire
  length `s`, clearing every non-output stack. Zero variables, trailing empty
  domains, empty scopes, repetitions, and arbitrary binary payloads are covered.
  `runtimeCompilerStructuralPayloadComputableInPolyTime` composes from the
  actual Boolean compiler input to exactly `RuntimeStructuralView.ofRuntimeSystem`
  under the payload encoding, with a checked polynomial bound. The `2s+3`
  constant is only the final local pass.
- **Remaining boundary:** `raw_encode_eq_count_payload` proves that prepending
  the total row count and reversing produces the original raw encoding.
  This is an encoding identity; the count producer and its composition with
  the Boolean framing bridge remain missing. Canonical relabelling, primal-edge
  deduplication, objective emission, and end-to-end compiler assembly still
  remain. README and headline/detailed theorem status retain **Partial**.
- **Proof corrections and API evidence:** a reverse rewrite against
  `SourceOrderRawNatLists.encode` did not match; applying `List.reverse_injective`
  then the checked counted-input identity resolved the exact raw bridge.
  Simplifying `encodeNat 1` also needed `encodeNum` and `encodePosNum`.
  `section` is a reserved binder; renamed it `part`. This Lean version has no
  `List.filterMap_none`; used `List.filterMap_eq_nil_iff` for constant-none
  projections and unfolded `Function.comp_def`, then normalized body reversal
  before sequential composition. No unresolved proof/API error remains.
- **Verification and ending state:** both direct module checks and full
  `lake build` passed (3155 jobs). All nine new headline axiom audits use only
  `propext`, `Classical.choice`, and `Quot.sound`; neither new module has warnings.
  The tracked/new inventory scan covered all 28 project Lean files with zero
  prohibited-code matches. A first scan also matched the prose phrase
  “axiom audits”; declaration-sensitive scanning correctly distinguishes it
  from a project-defined axiom. `git diff --check` passed. No sibling or thesis
  files changed. This verified assembly increment is ready to commit and push.
- **Best next step:** bound this newly constructed payload and its row count
  in actual encoded length, then construct the outer row count and compose
  reversal/framing to the original Boolean structural encoding.

### 2026-09-11 — bound the assembled payload and its required outer count

- **Starting state:** the assembly increment was committed and pushed as
  `27b2ba1e9b67668ef94fb3204cc546686f28aa4d`; local HEAD, tracking main,
  and the live remote ref agreed, with a clean worktree before this increment.
- **Checked size bridge:** `RuntimeStructuralView.payloadEncode_length_le_encodedSize`
  charges each raw field bit/delimiter to the corresponding framed field,
  bounding the entire payload by the already checked Boolean structural size.
  `payloadEncode_ofRuntimeSystem_length_le_quadratic` and
  `payloadEncode_ofRuntimeSystem_length_le_compilerInput_quadratic` retain the
  `32 * (s+1)^2` bound in compact and actual compiler input bit lengths.
  These bound the exact output of the new composed structural assembly machine;
  no numeric symbol magnitude is substituted for bit length.
- **Counter input invariant:** `rowCount_le_payloadEncode_length` bounds the
  missing outer row count, including the singleton variable header, by the
  actual payload length. It reuses the existing checked counted-row length
  theorem, including the empty-record case. This is a size invariant for the
  next counting machine, not a claim that counting has been implemented.
- **Proof approach and checks:** a minimal size experiment checked before
  integration; no new failed approach or unresolved API error occurred.
  The direct module check and final `lake build` passed (3155 jobs). All four
  new headline audits use only standard axioms, and the complete build's
  203 nonempty axiom reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`. Both new modules are warning-free. The final scan of all 28
  tracked/new project Lean files found no prohibited code; `git diff --check`
  passed. README, headline/detailed status, and semantic/encoding source
  correspondence notes are synchronized; `cor:all-different-csp` stays **Partial**.
- **Ending state and next step:** no sibling or active-thesis files changed;
  their HEADs remain `9852d94` and `f1107f5`, respectively, and the thesis's
  original dirty-file inventory is preserved. This second verified increment
  is ready to commit and push. Next implement the outer-row counter on the
  exact checked payload, preserve that payload, realize
  `raw_encode_eq_count_payload`, and compose the existing framing bridge.
  Relabelling, deduplicated edge construction, objective emission, and final
  compiler composition remain after that structural-format bridge.

### 2026-09-12 — compute the outer structural row count while retaining the payload

- **Starting state:** clean, synchronized `main` at
  `f0a23a0dcabf8e8ddc6bf381822a01302f6da80e`; fetch confirmed zero divergence.
  Read the run memory, theorem status, relevant source/correspondence notes,
  previous log, and the active thesis corollary and proof. The active thesis
  remained at `f1107f5` with its existing dirty-file inventory preserved.
  Read-only `lean-np-hardness` was clean at `2b546d6`, matching the live remote;
  its new SAT certificate results supply no row counter. Kept pin `db20c69`
  and reused its counted-row encoding, binary predecessor semantics, encoded
  length bounds, and standard pair codec without editing the sibling.
- **Chosen increment:** added `AllDifferentCSPRowCount.lean` and its root
  import. `StructuralCountedPayload.finEncoding` pairs the existing checked
  structural payload with mathlib's unary natural encoding.
  `encode_retain` identifies its exact canonical tagged wire. The concrete
  five-stack `StructuralRowCountMachine.computer` traverses each binary row
  length using explicit predecessor loops, saves all original fields, and
  emits one unary tally mark per row. It never substitutes a numeric value
  for the cost of reading that value's binary encoding.
- **Checked declarations:** `structuralRowCount_outputsInTime` and
  `structuralRowCountComputableInPolyTime` construct exactly
  `(view, view.records.length + 1)` in at most `20 * (s+1)^2` finite-machine
  steps for actual payload bit/delimiter length `s`. Every non-output stack
  is empty at halt. The proof includes zero variables, the singleton variable
  header, empty scopes, repeated scopes, and repeated entries. The underlying
  traversal also covers empty row lists and empty rows.
- **Failed approach and correction:** the first full traversal proof normalized
  the expected tally as `true :: replicate n true`, while the recursive run
  produced `replicate n true ++ [true]`. Using `List.replicate_succ'` rather
  than `List.replicate_succ` resolves that exact append orientation. Removed
  two unused simplifier arguments. The corrected direct check is warning-free,
  with no remaining proof/API error; failed elaborations are not evidence.
- **Verification:** the direct module check and full `lake build` passed
  (3156 jobs). All four new headline audits use only `propext`,
  `Classical.choice`, and `Quot.sound`; the full build's reported axiom sets
  contain no unexpected axiom. The scan covered all 29 project Lean files
  with zero prohibited-code matches, and `git diff --check` passed.
  README, headline/detailed status, and source correspondence notes agree.
- **Ending state and next step:** this verified increment is ready to commit
  and push. The full corollary remains **Partial**. Next compose counting from
  actual compiler input and bound the complete payload/tally pair; then convert
  the computed unary tally to the binary outer header, reverse, and frame.
  Canonical relabelling, deduplicated graph construction, objective emission,
  and final compiler composition remain after that structural-format bridge.

### 2026-09-12 — compose counted payload construction and bound its complete output

- **Starting state:** the first verified increment was committed and pushed as
  `a600f8549a88b0b15283ebeea8c5ee659fc3d3f5`; local HEAD, tracking main,
  and the live remote ref agreed, and the worktree was clean.
- **Checked composition:** `runtimeCompilerStructuralCountedPayloadComputableInPolyTime`
  uses the pinned generic sequential-machine API to compose complete payload
  construction with the new row counter. Starting from the actual Boolean
  compiler input, it constructs exactly the structural view together with
  `C.domainEntryCount + C.scopes.length + 1`, without a supplied row count.
  Its polynomial bound covers the whole composition; `20 * (s+1)^2` remains
  the local counter bound in the intermediate payload length.
- **Checked size bridge:** `StructuralCountedPayload.encode_retain_length`
  gives exact output length as payload length plus the number of rows.
  `encode_retain_length_le` bounds the pair by twice the payload length.
  `retain_ofRuntimeSystem` identifies the count with domain occurrences,
  scopes, and one singleton header. The compiler-input specialization
  `encode_retain_ofRuntimeSystem_length_le_compilerInput_quadratic` bounds
  the entire tagged output by `64 * (s+1)^2` cells in actual Boolean compiler
  input length `s`. This is an intermediate finite-alphabet output; final
  Boolean framing remains distinct.
- **Proof approach:** all five new declarations checked on the first direct
  module run, without warnings or failed approaches. The size bridge reuses
  the prior payload row-count bound; no symbol magnitude is used as bit size.
- **Verification and ending state:** the direct check and final full
  `lake build` passed (3156 jobs). All new headline axiom sets and the full
  build's 212 nonempty reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`. All 29 project Lean files passed prohibited-code scanning,
  and `git diff --check` passed. README and headline/detailed status are
  synchronized. The sibling remains clean at `2b546d6`; the active thesis
  retains its original dirty-file inventory at `f1107f5`. This second verified
  increment is ready to commit and push.
- **Best next step:** convert the internally constructed unary row tally to
  canonical binary while preserving the payload, emit the outer count field,
  and compose reversal plus the existing framing bridge. The needed unary
  count is at most the payload length. No checked standalone unary-to-binary
  adapter was found in the current public upstream API; its interval enumerator
  has an internal counting loop, but no exported adapter for this boundary.
  Relabelling, deduplicated graph construction, objective emission, and final
  compiler composition remain. `cor:all-different-csp` stays **Partial**.

### 2026-09-13 — stage the computed row tally as the exact binary outer header

- **Starting state:** clean `main` at
  `7e8763f3943b3ca400935c9c7cc3f7b27402fc7b`; fetch confirmed no divergence.
  Read run memory, theorem status, source/correspondence notes, the previous
  log, and the active thesis corollary and proof. The active thesis remains
  at `f1107f5` with its existing eleven dirty files preserved. Read-only
  `lean-np-hardness` is clean at `127cf2f`, matching its live remote; the new
  exact-three-SAT normalization does not add a public unary-to-binary adapter.
  Retained pin `db20c69` and reused its binary successor semantics, encoded
  natural length bound, standard pair codec, and finite-machine composition APIs.
- **Chosen increment:** added `AllDifferentCSPBinaryHeader.lean` and its root
  import. `StructuralCountedPayload.checkedFinEncoding` treats the existing
  view/tally pair as a structural-view encoding and checks tally equality.
  The existing row counter is repackaged under that codec as
  `structuralRowCountCheckedComputableInPolyTime`; no external count is assumed.
  The five-stack `StructuralBinaryHeaderMachine.computer` saves every payload
  cell, consumes each unary mark with explicit binary carry/restore transitions,
  emits the outer count, and reverses into `RuntimeStructuralView.rawFinEncoding`.
  `structuralBinaryHeader_outputsInTime` and
  `structuralBinaryHeaderComputableInPolyTime` state an `8 * (s+1)^2` bound in
  actual complete counted-payload length `s`, with empty non-output stacks at
  halt. The internal execution proof covers zero tallies and arbitrary carries.
- **Proof corrections:** fixed a nested tactic indentation parse error;
  `encodeNat 0` needs `simp [encodeNat, encodeNum]` rather than `rfl` in this
  version, and there is no `three_mul` lemma. Addition reassociation left
  expressions such as `1+(1+(2+k))` versus `2+(2+k)` in time indices; instead
  of repeating simplifier normalization, used run monotonicity followed by
  `omega`. Earlier failed elaborations and their `sorryAx` reports are not
  completed evidence.
- **Correspondence:** synchronized README, headline/detailed status, and all
  relevant source comments, including stale text that still listed payload
  assembly and row counting as absent. The full corollary stays **Partial**.
  Next compose actual compiler-input preparation, checked row counting, binary
  header staging, and the existing Boolean framing machine. Canonical
  relabelling, deduplicated graph construction, encoded objective emission,
  and end-to-end compiler composition remain afterwards.
- **Verification and ending state:** the corrected direct module check and
  full `lake build` passed (3157 jobs). All five new headline axiom audits
  and all 217 nonempty reports in the full build use only `propext`,
  `Classical.choice`, and `Quot.sound`. The new module has no warnings.
  All 30 project Lean files passed the prohibited-code scan, and
  `git diff --check` passed. Sibling and active-thesis HEADs and dirty-file
  inventories are unchanged. This verified increment is ready to commit and
  push; the prepared composition is the next increment.

### 2026-09-13 — complete structural preprocessing in the original Boolean encoding

- **Starting state:** the first increment was committed and pushed as
  `9a08b4e945f672efcf17b5b402d48169d919c183`; local HEAD, tracking main,
  and live remote main agreed, and the worktree was clean.
- **Checked composition:** added `AllDifferentCSPStructuralCompiler.lean`
  and its root import. `structuralRawComputableInPolyTime` composes the checked
  redundant row-count pass with binary-header staging and reversal.
  `runtimeCompilerStructuralRawComputableInPolyTime` starts that complete path
  from the actual Boolean compiler input. The headline
  `runtimeCompilerStructuralViewComputableInPolyTime` adds the checked framing
  machine and constructs exactly `RuntimeStructuralView.ofRuntimeSystem`
  under its original Boolean `FinEncoding`.
- **Evidence boundary:** every structural header and intermediate wire is
  produced internally. The pinned generic composition theorem includes the
  intermediate transfer cost and yields an overall polynomial bound in actual
  compiler input length. The local `8(s+1)^2` header bound is not presented as
  the bound for the entire composition. The existing
  `ofRuntimeSystem_encodedSize_le_compilerInput_quadratic` theorem now bounds
  the actual final Boolean machine output by `32(s+1)^2` bits. Zero variables,
  trailing empty domains, empty scopes, repetitions, and arbitrary encoded
  natural symbols remain covered. The smaller header-free input is still a
  distinct representation boundary, as documented in README.
- **Proof approach:** all three new composition declarations checked on their
  first direct run without warnings. They reuse `compositionComputableInPolyTime`
  and normalize only function composition with identity. Their axiom audits
  use only `propext`, `Classical.choice`, and `Quot.sound`; no new failed
  approach or unresolved API error occurred.
- **Correspondence and next step:** synchronized README, headline/detailed
  theorem status, and source correspondence notes. Structural construction
  and original Boolean framing are now composed. The full corollary remains
  **Partial** because canonical relabelling, deduplicated graph construction,
  encoded objective emission, and composition with prime selection remain.
  Next reuse `RuntimeStructuralView.ofRuntimeSystem_domainOccurrences` and
  `indexedDomainOccurrences_values` (already checked) to specify a finite
  domain-symbol extraction pass and connect its deduplicated value set to
  `ExplicitSystem.domainValues`. Then implement the canonical rank
  `(domainValues.filter (· < a)).card + 1`, reusing the upstream binary
  comparison API and preserving equality across domains.
- **Final verification and ending state:** the direct composition check and
  final full `lake build` passed (3158 jobs). All three new headline audits
  and all 220 nonempty build axiom reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`. Both new modules are warning-free.
  All 31 project Lean files passed prohibited-code scanning;
  `git diff --check` passed. The read-only sibling remains clean at `127cf2f`,
  and the active thesis retains its original eleven-file dirty inventory at
  `f1107f5`. This second verified increment is ready to commit and push.

### 2026-09-14 — connect occurrence symbols and executable ranks to the semantic compiler

- **Starting state:** clean `main` at
  `ffb9f12a5bb10e485f1d8542efe165476ff6d014`; fetch and live remote inspection
  confirmed synchronization. Read instructions, status, relevant sources,
  correspondence notes, run memory, previous log, and the active corollary and
  proof. The active thesis is at `f1107f5` with twelve pre-existing dirty files;
  its complete diff and status were saved for preservation checks. Read-only
  `lean-np-hardness` is clean at `4521457`, matching its live remote. Its new
  `BinaryEquality` kernel compares separately supplied binary stacks in
  `max(left.length,right.length)+1` steps; loading serialized pairs and repeated
  lookup remain separate obligations. Retained dependency pin `db20c69`.
- **Checked increment:** added `AllDifferentCSPSymbols.lean` and its root import.
  `DomainSymbols.extract_toFinset` identifies the exact structural symbol set
  with `ExplicitSystem.domainValues`. The executable list `rank` deduplicates
  smaller symbols before counting. `rank_extract_eq_relabelValue` proves exact
  agreement with the semantic rank; `rank_eq_iff`, `rank_lt_domainEntryPrime`,
  and `relabeled_domain` give equality, prime-bound, and per-domain guarantees.
  An ordinary kernel-checked example covers repeated shared symbols and
  nonconsecutive values. No well-formedness assumption is needed for extraction.
- **Proof correction:** simplification did not close the deduplicated filtered
  finset equality under cardinality, and `List.toFinset_map` was unavailable.
  Finset extensionality and membership simplification resolved both boundaries.
  The failed elaboration's `sorryAx` reports are not evidence; the corrected
  check has no unexpected axioms and no warnings.
- **Verification:** direct `lake env lean PhdThesisLean/AllDifferentCSPSymbols.lean`
  and full `lake build` passed (3159 jobs). All five new headline axiom audits
  and the full build's nonempty reports use only `propext`, `Classical.choice`,
  and `Quot.sound`. Project Lean sources pass the prohibited-code scan and
  `git diff --check` passes. README, status and source correspondence agree.
- **Ending state and next target:** this verified increment is ready to commit
  and push. The next increment implements symbol-field extraction while
  retaining the exact occurrence wire, then composes it through the existing
  counted sections. Deduplication/rank machine construction, deduplicated graph
  construction, objective emission, and final prime composition remain;
  `cor:all-different-csp` remains **Partial**.

### 2026-09-14 — extract domain symbols in a finite machine and compose from Boolean input

- **Starting state:** the first increment was committed and pushed as
  `51322a324c11ac6700446a77939196087c9d538b`; HEAD, tracking main, and the live
  remote ref agreed. Only this second increment's new module was untracked.
- **Checked machine:** added `AllDifferentCSPSymbolMachine.lean` and its root
  import. `DomainSymbolMachine.computer` uses four finite-alphabet stacks and
  four field phases to recognize the symbol field of each existing checked
  `[3, 0, index, value]` record. It copies the entire original occurrence wire
  and separately extracts complete symbol fields in source order. The exact
  execution proof preserves zeros, repetitions, and arbitrary binary values,
  includes the empty occurrence list, and empties all non-output stacks.
  `domainSymbolExtraction_outputsInTime` and
  `domainSymbolExtractionComputableInPolyTime` prove at most `3s+3` steps in
  the actual occurrence bit/delimiter length `s`. The raw-field and pair
  encodings are reused from the pinned dependency; no generic codec is copied.
- **Checked full-input composition:** the pinned generic pair-left API carries
  all scopes and the variable count through extraction. The headline
  `runtimeCompilerSymbolSectionsComputableInPolyTime` starts from actual
  Boolean compiler input and outputs `CountedSymbolSections.ofRuntimeSystem`.
  `symbols_ofRuntimeSystem` identifies the attached list with `domains.flatten`;
  `toStructuralView_ofRuntimeSystem` proves exact reconstruction of the original
  structural view, and `rank_symbols_eq_relabelValue` connects these internally
  produced symbols to the semantic compiler's rank. The composition includes
  every preprocessing and transfer cost; its polynomial bound is distinct
  from the local `3s+3` extraction bound.
- **Checked sizes:** `DomainSymbolExtraction.symbolsEncode_length_le` charges
  extracted fields to their original encoded cells. Both local and complete
  `retain_encode_length_le` theorems bound the augmented encoding by twice its
  input length, including scopes and the variable count in the complete case.
  This intermediate uses finite tagged alphabets, not a new claimed Boolean
  encoding or a magnitude-based arithmetic cost model.
- **Proof corrections:** the initial empty scan goal needed the pure trace
  unfolded before the transition tactic; the value-phase bit induction needed
  substitution before simplifying its hypothesis; the final `omega` bound
  needed the local input alias unfolded. These local corrections resolved all
  three errors. The machine and full-input composition then passed direct
  `lake env lean` checks without warnings; all new audits contain only standard
  axioms, and the exact reconstruction theorem is axiom-free.
- **Next target:** implement deduplicated symbol membership and rank counting
  on the extracted source-order raw fields, while retaining the original
  sections. The sibling's new `BinaryEquality.natural_evalsToInTime` is a
  reusable separately-loaded-stack kernel; a checked serialized-field loader
  and repeated membership driver are still needed before using it for this
  target. Review the upstream pin when integrating that API; do not copy the
  generic equality kernel or edit the sibling from this automation. Then prove
  the finite machine computes `DomainSymbols.rank`, construct deduplicated
  edges and objective rows, and compose prime selection. The full corollary
  remains **Partial**.
- **Final verification and ending state:** direct machine and composition
  checks and the final full `lake build` passed (3160 jobs). All 232 nonempty
  axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`;
  both new modules are warning-free. All 33 project Lean files pass the
  prohibited-code scan; its sole raw text match is an existing explanatory
  comment about axiom audits. `git diff --check` passes. README, headline and
  detailed status, source correspondence, and this log are synchronized.
  The active thesis's full binary diff and twelve-file status inventory match
  the starting snapshots exactly; the read-only sibling remains clean at
  `4521457`. This second verified increment is ready to commit and push.

### 2026-09-15 — decide membership in serialized domain-symbol fields

- **Starting state:** clean `main` at `e643092c8926d07bca2cc804943aa27bd56440a8`;
  a fresh fetch and live remote check agreed, so no fast-forward was needed.
  The active thesis remained at `f1107f5` with its twelve pre-existing dirty
  files preserved. Its active `cor:all-different-csp` statement and proof were
  reread, including canonical relabelling and deduplicated conflicts.
- **Read-only upstream review:** `lean-np-hardness` was clean at published
  `ad20a2e92ec5eb85379ac31df255671416f83b3d`. Its new
  `PreservingBinaryEquality.whole_list` preserves the query while consuming a
  candidate, but has no serialized loader or membership traversal. Updated
  only this project's dependency pin from `db20c69` to `ad20a2e`; the Lean
  toolchain, mathlib revision, and other package pins are unchanged. The
  sibling checkout was not edited. Initial sandboxed network attempts failed
  to resolve GitHub; the authorized network-capable fetch and update succeeded.
- **Checked increment:** added `AllDifferentCSPSymbolMembership.lean` and its
  root import. `DomainSymbolMembership.finEncoding` reuses the standard
  binary-natural and source-order raw-field encodings in the existing tagged
  pair codec. `SymbolMembershipMachine.computer` parses this complete wire,
  loads and compares every candidate, restores the query between comparisons,
  accumulates the membership Boolean, and empties all non-output stacks.
  `domainSymbolMembership_outputsInTime` and
  `domainSymbolMembershipComputableInPolyTime` prove exactly `contains` in at
  most `6 * (s+1)^2` steps for the complete tagged input length `s`. Empty
  lists, zero, repetitions, unequal word lengths, and all loading/cleanup
  costs are included. No numeric-magnitude bound or supplied stack alignment
  is assumed.
- **Reuse boundary:** the comparison statements and exact execution theorem
  come from the upstream preserving kernel. The local lift only embeds those
  statements in the CSP parser, preserves its input and finite control, and
  redirects kernel halt to the next membership iteration. Both loaded words
  are reversed, so equality remains exact without extra reversal passes.
  `compare_iterate` handles only successful finite runs, allowing the kernel's
  halt to return to the driver without assuming halted steps still commute.
- **Proof corrections:** Lean has no `namespace Alias := ...` syntax, and
  `stacks` is reserved; use the imported namespace and `stackContents`.
  The dependent stack update needed substitution in its equal-index case.
  The lifted iteration needed an explicit `step`-shaped hypothesis and the
  fixed-point fact for iteration from `none`. Arithmetic reassociation was
  closed with `omega`; encoded pair length uses its checked length theorem,
  not definitional equality. Corrected direct checks have no warnings or
  unexpected axioms; failed elaborations are not completion evidence.
- **Verification:** the direct module check and full `lake build` passed
  (3163 jobs); the build has 234 nonempty-format axiom reports, all using only
  `propext`, `Classical.choice`, and `Quot.sound`. All 34 project Lean files
  pass the comment/string-aware prohibited-code scan, and `git diff --check`
  passes. README, theorem status, and source correspondence comments retain
  the full corollary as **Partial**. The final full build also passed (3163
  jobs) after synchronizing those correspondence comments.
- **Ending state and next target:** this completed membership increment is
  ready for commit and push. The next small increment
  connects its Boolean to the canonical-rank recurrence and establishes the
  exact query/tail bit-size boundary. A repeated deduplication/rank machine,
  retention of the remaining compiler sections, deduplicated graph construction,
  objective emission, and final prime-selection composition remain.
- **Run time:** 2026-09-15 05:29 AEST (2026-09-14 19:29 UTC).

### 2026-09-15 — connect membership to canonical rank steps and exact field sizes

- **Starting state:** the membership increment was committed and pushed as
  `1c9739abea8d76513b4bd4102ca39a606a15477f`; HEAD, origin/main, and the
  live remote main ref agreed, with a clean worktree before this increment.
- **Checked increment:** added `AllDifferentCSPSymbolRankStep.lean` and its
  root import. `DomainSymbolMembership.contains_extracted` connects the exact
  machine predicate to `ExplicitSystem.domainValues`. `dedup_cons` identifies
  the predicate with the branch that removes a repeated symbol.
  `DomainSymbols.rank_cons` and `DomainSymbolMembership.rank_cons` prove that
  a smaller symbol contributes one position only at its final source-order
  occurrence. This connects the checked membership Boolean directly to the
  existing canonical semantic rank, including repeated values across domains.
- **Exact size boundary:** `input_cons_length` proves that the query/tail
  encoding is precisely one delimiter shorter than the corresponding original
  raw field stream. `tailMembership_outputsInTime` therefore reuses the
  concrete membership machine with bound `6 * r^2` for that original stream
  length `r`. The query's bits remain charged. `dedup_fields_length_le` uses
  `List.dedup_sublist` and the sublist-preserving field encoding to show that
  deduplication never enlarges the binary wire, without bounds on numeric
  symbol magnitudes. This is a size theorem, not a deduplication time theorem.
- **Verification:** the direct rank-step module check passed without warnings;
  all six new headline axiom reports use only `propext`, `Classical.choice`,
  and `Quot.sound`. The final full `lake build` passed (3164 jobs), with 240
  nonempty-format axiom reports containing only those standard axioms. All
  35 project Lean files pass the comment/string-aware prohibited-code scan,
  and `git diff --check` passes. Ordinary kernel-checked examples cover zero,
  absence, an empty list, and repeated smaller values contributing just once.
  The exploratory rank proof checked on its first attempt; unused simp
  arguments were removed before the final direct check.
- **Preservation:** the active thesis's complete binary diff and twelve-file
  status inventory exactly match the starting snapshots. The read-only
  sibling remains clean at `ad20a2e`; no files there were edited. README,
  headline and detailed theorem status, and the new module's correspondence
  note keep the full `cor:all-different-csp` **Partial**.
- **Ending state and next target:** this second verified increment is ready
  to commit and push. Implement a repeated rank driver that retains the
  remaining symbol stream and target, applies the checked membership test
  against each tail, compares the symbol with the target using the binary
  comparison API, and increments only for a new smaller symbol. Prove exact
  agreement with the recurrence and charge all copying and loop costs before
  claiming polynomial-time ranking. Retention/composition with the original
  sections, deduplicated primal edges, objective rows, and prime selection
  still remain before the full corollary is complete.
- **Run time:** 2026-09-15 05:32 AEST (2026-09-14 19:32 UTC).

### 2026-09-16 — load serialized symbol comparisons into the checked binary kernel

- **Starting state:** clean `main` at `55e71e50c3ee6170060aa628a3b2ecdb1f1a821d`;
  fetch confirmed equality with `origin/main`. The active thesis remained at
  `f1107f5` with twelve existing dirty files, including the current all-different
  proof; its status and binary diff were snapshotted and left untouched.
- **Read-only dependency review:** the sibling is clean at published
  `11479ccca957fe8d460d3fc7b4a5dcf1f2fa5e1c`. Its new `FrameExtraction` kernel
  extracts a length-framed Boolean payload while retaining a suffix; this is
  a different input contract from the tagged symbol pair. The existing pinned
  `BinaryNatPair` codec and `binaryLEComputableInPolyTime` supply the aligned
  comparison boundary but no tagged-pair loader. Kept pin `ad20a2e` and reused
  these APIs without editing the sibling or duplicating its comparison kernel.
- **Checked increment:** added `AllDifferentCSPSymbolComparison.lean` and its
  root import. `DomainSymbolComparison.finEncoding` reuses the checked tagged
  pair of standard binary naturals. The seven-stack `SymbolComparisonLoader`
  reads both words, restores their bit order, aligns corresponding positions,
  and restores the final stream order. Exhausted sides carry explicit `none`
  padding, including the two-zero empty-word case. All work stacks are empty
  and finite control is reset at halt.
- **New declarations:** `domainSymbolAlignment_outputsInTime` and
  `domainSymbolAlignmentComputableInPolyTime` prove exact canonical aligned
  output in at most `4s+5` finite-machine steps for complete serialized input
  length `s`. `domainSymbolAlignment_output_length_le` bounds the entire
  output by that input length; the exact aligned length is the maximum of
  the two bit lengths. No bound on numeric symbol magnitude is assumed.
- **Proof corrections:** `rfl` did not unfold the imported `zipBits` empty
  case; explicit simplification of that definition resolved both the length
  base case and the terminal alignment configuration. No repeated failed
  approach, unproved assumption, or placeholder was retained.
- **Verification:** direct module check passed without warnings; full
  `lake build` passed (3166 jobs). All 243 nonempty-format axiom reports use
  only `propext`, `Classical.choice`, and `Quot.sound`; all 36 project Lean
  files passed the comment/string-aware prohibited-code scan. `git diff --check`
  passed. README and theorem status describe the constructed loading boundary
  and keep `cor:all-different-csp` **Partial**.
- **Ending state and next target:** this verified increment is ready to commit
  and push. Compose strict comparison using the existing less-or-equal kernel,
  then connect that computed bit and tail membership to the rank recurrence.
  The repeated rank driver, retained-section composition, deduplicated edges,
  objective emission, and final prime-selection composition remain pending.
- **Run time:** 2026-09-16 05:23 AEST (2026-09-15 19:23 UTC).

### 2026-09-16 — compose strict symbol comparison with a complete linear bound

- **Starting state:** the loader increment was committed and pushed as
  `145940f2136e0d13e2b924edccbbc86b94a385ae`. HEAD, `origin/main`, and live
  remote main agreed before this increment.
- **Checked increment:** `alignedSymbolLessComputableInPolyTime` reuses
  `binaryLEComputer`, with explicit finite-alphabet equivalences swapping
  aligned components and complementing the kernel's result. This proves
  strict comparison of the original symbol and target without introducing a
  second arithmetic implementation. The decoded result is exactly
  `DomainSymbolComparison.less`, including zero and equal inputs.
- **Complete local runtime:** `domainSymbolLessComputableInPolyTime` uses
  the pinned `compositionMachine_outputsInTime` execution theorem to compose
  the loader and comparison kernel. Its explicit `9s+10` bound includes all
  loading, alignment, reversal, and intermediate transfer costs for serialized
  pair length `s`. The proof combines `4s+5` loading, `m+1` comparison, and
  `4m+4` transfer, with checked aligned length `m ≤ s`.
  `domainSymbolLess_time` exposes that exact polynomial evaluation. The output
  equivalence converts the kernel bit to the standard Boolean meaning; the
  theorem does not omit that recoding.
- **Rank correspondence and size:** `DomainSymbolComparison.rank_cons`
  connects the now-checked strict-comparison and membership bits to the
  semantic rank recurrence. `input_head_length` proves the exact equation
  between the complete target/symbol query, its comparison pair, the head
  delimiter, and remaining raw fields. `input_length_le_rank_query` gives
  the resulting local size bound without assuming small numeric values.
  These contracts do not assert that a machine already retains or repeatedly
  extracts those pairs.
- **Proof corrections:** the Boolean negation needed parentheses around the
  whole negated value in an equality: otherwise Lean parsed the equality
  under `!` and coerced it to a Boolean. Literal polynomial coefficients
  simplify with `Polynomial.eval_ofNat`; `eval_natCast` alone left the
  coefficients opaque to `omega`. Explicit rewriting staged the aligned
  swap before applying the imported execution theorem. Corrected module
  checks contain no warnings, unfinished proofs, or unexpected axioms.
- **Verification:** direct module check and final full `lake build` passed
  (3166 jobs). All 249 nonempty-format axiom reports use only `propext`,
  `Classical.choice`, and `Quot.sound`; all 36 project Lean files passed the
  comment/string-aware prohibited-code scan; `git diff --check` passed.
  README, theorem status, and module correspondence remain synchronized, and
  `cor:all-different-csp` remains **Partial**.
- **Preservation:** the active thesis's binary diff and twelve-file status
  inventory exactly match their starting snapshots. The read-only sibling
  remains clean at `11479cc`; the dependency pin remains `ad20a2e`.
- **Ending state and best next step:** this second verified increment is ready
  to commit and push. Build the repeated rank driver: retain the target and
  remaining source, copy the head/tail query for membership, stage the checked
  symbol/target pair for strict comparison, and increment only for a smaller
  symbol absent from its tail. Charge all retention/copying and loop costs.
  Then compose ranks with the preserved compiler sections; deduplicated primal
  edges, objective emission, and final prime selection still remain.
- **Run time:** 2026-09-16 05:29 AEST (2026-09-15 19:29 UTC).

### 2026-09-17 — prepare all predicate inputs for one canonical-rank iteration

- **Starting state:** clean `main` at `579f819f2af9ddc0dc3de5d9b88b24c889a0e30e`;
  fetch confirmed equality with `origin/main` and live remote main. The active
  thesis remained at `f1107f5`, with twelve existing dirty files, including
  the current all-different proof. Its status and binary diff were snapshotted.
- **Read-only dependency review:** `lean-np-hardness` was clean at published
  `4409f67`. Its new `FrameComparisonMachine` composes framed extraction and
  query-preserving equality, but that framed/preloaded interface differs from
  the current tagged source-order rank query. Reused the already pinned
  `ad20a2e` encoding and composition APIs; no dependency or sibling edits.
- **Checked increment:** added `AllDifferentCSPRankQueries.lean` and the root
  import. `RankQueries.inputFinEncoding` uses exactly the existing
  `(target, symbol :: tail)` wire; its decoder rejects an empty symbol list.
  The eight-stack `RankQueryMachine.computer` copies each target, symbol, and
  tail cell into two finite buffers and emits the canonical nested pair
  `((symbol, tail), ((symbol, target), (target, tail)))`. No pre-split queries
  or free input copies are assumed. Every work stack is empty at halt.
- **New declarations:** `rankQueries_outputsInTime` and
  `rankQueriesComputableInPolyTime` prove the complete preparation in at most
  `3s+5` steps for actual serialized rank-input length `s`.
  `RankQueries.output_length` proves the exact equation `output + 2 = 2s`:
  every payload cell is copied twice and the consumed head delimiter is
  discarded. Zero targets/symbols, empty tails, repetitions, and unbounded
  binary magnitudes are included in the checked proofs.
- **Proof corrections:** `EvalsToInTime.refl` needs explicit function and
  configuration arguments. Final output simplification left partially applied
  `tag` functions under `List.map`; `rfl` closed the remaining definitional
  equality. A redundant sequencing linter warning was removed. Failed-check
  axiom output was discarded; the corrected direct check has no `sorryAx`.
- **Verification:** direct module check passed without warnings; full
  `lake build` passed (3167 jobs). All 253 nonempty-format axiom reports use
  only `propext`, `Classical.choice`, and `Quot.sound`; the comment/string-aware
  prohibited-code scan passed all 37 project Lean files. `git diff --check`
  passed. README, theorem status, and source correspondence were synchronized;
  `cor:all-different-csp` remains **Partial**. The thesis binary diff and sibling
  status still match their starting snapshots.
- **Ending state and next target:** this increment is verified for commit and
  push. Next compose membership and comparison through the existing pair
  adapters while retaining `(target, tail)`, connect their outputs to
  `rank_cons`, and prove that the retained wire strictly shrinks. The repeated
  loop, empty-list branch, accumulator, full-input composition, deduplicated
  edges, objective emission, and final prime-selection composition remain.
- **Run time:** 2026-09-17 05:25 AEST (2026-09-16 19:25 UTC).

### 2026-09-17 — execute both rank predicates and retain a strictly smaller query

- **Starting state:** the preparation increment was committed and pushed as
  `7a0fa6063938b366779dbc78e51e86f0e187984e`. HEAD, `origin/main`, and the
  live remote main ref agreed before this increment.
- **Checked increment:** added `AllDifferentCSPRankPredicates.lean` and its
  root import. `rankPredicatesComputableInPolyTime` composes the checked
  preparation with `domainSymbolMembershipComputableInPolyTime` and
  `domainSymbolLessComputableInPolyTime`. The pinned upstream
  `MachineAdapters.pairReductionComputableInPolyTime` and
  `pairRightComputableInPolyTime` preserve all unconsumed data. The exact result
  is `(symbol ∈ tail, (symbol < target, (target, tail)))`, with Boolean
  predicates and the canonical nested-pair encoding. The composed polynomial
  accounts for copies, predicate runs, transfers, and output reassembly; the
  preparation pass's `3s+5` bound is not claimed for this whole composition.
- **Rank and size correspondence:** `RankPredicates.rank_step` identifies the
  two machine-produced bits with the rank recurrence: count a smaller symbol
  only when it does not occur in the tail. `remaining_length` proves the
  retained wire loses exactly the head symbol's binary length plus its
  delimiter; `remaining_length_lt` therefore holds even for a zero head.
  `output_length` counts the two Boolean cells exactly, and `output_length_le`
  bounds the entire result by `s+1` for original rank-query length `s`.
- **Proof corrections:** output composition initially stopped at the local
  `remaining` encoding alias and `RankPredicates.outputFinEncoding`; unfolding
  both in the final `simpa` resolved it. The Boolean-length proof needs
  `encodeBool` unfolded. Adding `Nat.add_comm` to this simplification left
  `1+(1+n)=2+n`; the smaller `simp` set closes the original goal directly.
  An unnecessary following `omega` caused `No goals to be solved` in one full
  build and was removed. The subsequent complete build is the final evidence.
- **Verification:** final `lake build` passed (3168 jobs). All 258
  nonempty-format axiom reports use only `propext`, `Classical.choice`, and
  `Quot.sound`; all 38 project Lean files passed the comment/string-aware
  prohibited-code scan. Both new modules are warning-free, and
  `git diff --check` passed. README, theorem status, and new module
  correspondence are synchronized; `cor:all-different-csp` remains **Partial**.
- **Preservation:** active thesis status and binary diff exactly match the
  starting twelve-file snapshots. The read-only sibling is still clean at
  `4409f67`; its status and binary diff are unchanged. The dependency remains
  pinned to `ad20a2e`, with no toolchain changes.
- **Ending state and best next step:** this second increment is verified for
  commit and push. Build the finite repeated rank loop over the shrinking
  target/tail wire: handle empty lists, retain a binary or unary accumulator,
  use the checked predicate bits to increment, and charge all loop/control
  and accumulator costs. Prove agreement with `DomainSymbols.rank`, then
  compose with the retained compiler sections. Primal-edge deduplication,
  objective emission, and final prime-selection composition remain pending.
  No new missing upstream API was established; the blocker is the still
  unconstructed loop, rather than either local predicate or input staging.
- **Run time:** 2026-09-17 05:28 AEST (2026-09-16 19:28 UTC).


### 2026-09-18 — conditionally update the rank accumulator in linear time

- **Starting state:** clean `main` at
  `d88106f97672b44f6cfca86f0eff325ae0461ad8`; fetch and live remote lookup
  confirmed upstream parity. Read AGENTS, status, relevant README/source
  correspondence, prior log/memory, and the active all-different theorem and
  proof. The active thesis stayed at `f1107f5` with twelve existing dirty
  files; its binary diff SHA-256 is unchanged.
- **Read-only dependency review:** sibling `lean-np-hardness` started clean at
  `c0a50ea`. Its certificate-count initialization and zero test retain a framed
  binary count; that interface does not implement our source-order rank loop.
  Its separate task advanced it to `7f83b99` during this run, adding framed
  comparison with count retention. Reviewed that interface too; it still leaves
  traversal control separate. No sibling edits or dependency/toolchain changes
  were made here. Reused pinned `ad20a2e` encodings and machine APIs.
- **Checked increment:** added `AllDifferentCSPRankAccumulator.lean` and root
  import. `RankAccumulator.update` consumes membership and strict-order bits,
  retains the target/tail query, and adds one unary cell exactly for a smaller
  symbol absent from its tail. The concrete three-stack machine handles empty
  queries, zero tallies, both Boolean choices, ordering, and complete cleanup.
- **Declarations:** `RankAccumulator.input_length` and `output_length` charge
  all predicate bits, query cells, and unary tally cells. The headline
  `rankAccumulator_outputsInTime` and `rankAccumulatorComputableInPolyTime`
  prove a bound of `2s` finite-machine steps in the complete input wire length.
  This is the conditional update pass, not the runtime of the whole rank loop.
- **Proof corrections:** Lean rejects `simp [← unaryDecodeNat]` because a
  definition cannot be refolded by that modifier; used the checked
  `unaryEncodeNat_eq_replicate_true` lemma. The zero-count execution case
  needed `unaryEncodeNat` reduced before the machine-step simplifier.
  `convert` discharged the output configuration definitionally, so the next
  goal was the arithmetic time equation, not another configuration equality.
  Removed an extra `omega` after a closing `simp`, plus unused simp arguments.
  The first failed direct check was stopped after these errors appeared;
  failed-build axiom reports are not completion evidence.
- **Verification:** final `lake build` passed (3169 jobs). All 262 reported
  axiom lists use only `propext`, `Classical.choice`, and `Quot.sound`; the new
  module has no warnings. The comment/string-aware prohibited-code scan passed
  all 40 current project Lean sources, including the next unimported working
  module; only the accumulator increment is claimed checked here.
  `git diff --check` passed. README and THEOREM_STATUS are synchronized, with
  `cor:all-different-csp` still **Partial**.
- **Ending state and next target:** this increment is verified for commit and
  push. Compose the retained-accumulator predicate pass with this machine,
  prove the rank invariant and nonexpansion of the full serialized state, and
  connect its recursive specification to the semantic canonical rank. The
  finite repeated driver, empty-list control, and full compiler composition
  remain pending.
- **Run time:** 2026-09-18 01:20:47 UTC.


### 2026-09-18 — compose a complete rank iteration and prove its counting invariant

- **Starting state:** the preceding accumulator increment was committed and
  pushed as `4e54067bfd4b16c0d97086a5cbba731b962baca6`. Local HEAD,
  `origin/main`, and the live remote main ref agreed. Only this run's next
  untracked iteration module remained in progress.
- **Checked increment:** added `AllDifferentCSPRankIteration.lean` and root
  import. `rankIterationComputableInPolyTime` lifts the checked predicate
  machine over a retained unary accumulator with upstream
  `pairReductionComputableInPolyTime`, then composes the conditional update
  through `compositionComputableInPolyTime`. The source is the original
  nonempty target/symbol-list query paired with its tally; its output is
  exactly the target/tail query and updated tally. The polynomial charges
  preparation, both predicates, all copies, transfers, and reassembly.
  The preceding pass's `2s` bound is not claimed for this full iteration.
- **Semantic and size evidence:** `RankIteration.rank_invariant` preserves
  tally plus remaining canonical rank. `remaining_symbols_length` removes
  exactly one symbol. `output_length_balance` gives the exact equation
  `output + headBits + 1 = input + contribution`; `output_length_le` proves
  nonexpansion of the complete state including the tally. A counted zero head
  can leave the wire length equal, so termination uses remaining list length.
- **Executable loop specification:** `RankIteration.finish` tail-recursively
  applies this step and returns the tally for an empty list. `finish_add_one`
  proves its accumulator invariant; `finish_one_eq_rank` and
  `finish_extracted_eq_relabelValue` identify the result with canonical rank
  and the thesis compiler's relabelling. `finish_le_count_add_length` bounds
  the unary result by starting tally plus explicit occurrences, independently
  of symbol magnitude. Kernel-checked examples cover repetitions, zero values,
  and empty lists. These are semantic proofs for executable recursion, not a
  finite-machine running-time theorem for the whole repeated loop.
- **Verification and corrections:** the targeted module build passed on its
  first attempt (3142 jobs). Removed one unused `Nat.add_left_comm` simp
  argument; the final full `lake build` then passed (3170 jobs). All 269
  reported axiom lists use only `propext`, `Classical.choice`, and `Quot.sound`.
  Both new modules are warning-free. All 40 project Lean sources passed the
  comment/string-aware prohibited-code scan, and `git diff --check` passed.
  README and THEOREM_STATUS record the checked iteration and remaining driver
  boundary; the full `cor:all-different-csp` stays **Partial**.
- **Preservation:** the active thesis remains at `f1107f5`; its twelve dirty
  files and binary diff match the starting snapshot exactly. The separately
  advanced sibling is clean at `7f83b99` and was only read by this task.
  Dependency pin `ad20a2e` and all toolchains are unchanged.
- **Ending state and best next step:** this increment is verified for commit
  and push. Construct a finite repeated driver that initializes tally one,
  detects empty symbol lists while retaining the query, invokes the checked
  iteration otherwise, and returns the final tally. Use strict symbol-count
  decrease and the nonexpanding full-state bound to charge every repetition,
  transfer, branch, and cleanup. Then compose canonical relabelling with the
  retained compiler sections. Primal-edge deduplication, objective emission,
  and final prime-selection composition still remain. No new missing upstream
  API was established; the finite loop/control construction is still pending.
- **Run time:** 2026-09-18 01:24:22 UTC.


### 2026-09-19 — initialize the rank loop from the complete query

- **Starting state:** clean `main` at
  `21e5ef05f44d1ff0b5890c3d67a363402020b236`. Fetch, local tracking ref,
  and live remote main agreed. Read AGENTS, status, relevant README and Lean
  source correspondence, prior log/memory, and the active thesis statement
  and proof. The thesis was at `f1107f5` with twelve pre-existing dirty files;
  its binary diff SHA-256 was
  `b6318d9412925b69a2affddec98bd9c09d0dabd6b2924882dab0cd2408c582ac`.
- **Read-only dependency review:** sibling `lean-np-hardness` was clean at
  `7f83b99`. Reviewed its certificate-count initialization/test and framed
  comparison interface: these retain an extracted binary certificate count,
  whereas our rank state has exhaustion-delimited source fields and a unary
  accumulator. They do not directly implement this rank control pass.
  Reused pinned `ad20a2e` encodings and machine APIs; made no sibling edits,
  dependency changes, or toolchain changes.
- **Checked increment:** added `AllDifferentCSPRankInitialization.lean` and
  its root import. `RankInitialization.seed` appends tally one to the complete
  target/symbol query. The concrete three-stack machine retains every query
  cell, restores source order, and clears its work stacks, including for the
  entirely empty encoding of target zero and no symbols.
- **Declarations:** `rankInitialization_outputsInTime` and
  `rankInitializationComputableInPolyTime` prove a `2s+2` bound in the actual
  query wire length. `RankInitialization.output_length` proves exactly one
  added cell; `finish_initialize` connects the constructed state to the
  already checked semantic canonical rank. This is initialization, not the
  full finite repeated loop.
- **Failed approach and correction:** Lean reserves the identifier
  `initialize` as a command; declaring `def initialize` produced parser errors
  and downstream unknown identifiers. Renamed it `seed`, then rebuilt.
  Removed an unnecessary `<;>` tactic linter warning. Failed-build axiom
  reports were discarded; only the subsequent successful audits count.
- **Verification:** targeted build passed (3143 jobs), then full `lake build`
  passed (3171 jobs). All 273 reported axiom lists contain only `propext`,
  `Classical.choice`, and `Quot.sound`. The new module has no warnings.
  The comment/string-aware prohibited-code scan passed all 42 project Lean
  sources (including the next unimported control module, not claimed checked
  here). `git diff --check` passed. README and THEOREM_STATUS agree with the
  build; `cor:all-different-csp` remains **Partial**.
- **Ending state and next step:** verified initializer ready for commit and
  push. Next check the empty-list control pass while retaining the complete
  target/symbol/tally state, especially zero-valued symbol fields. Repeated
  iteration, final tally output, and full compiler composition remain open.
- **Run time:** 2026-09-18 19:22:37 UTC (2026-09-19 05:22:37 AEST).


### 2026-09-19 — check rank-loop entry, empty-list testing, and tally exit

- **Starting state:** initializer committed and pushed as
  `0353503840b39778c075bb9e631857f62fbb348d`. Local HEAD, `origin/main`, and
  the live remote main ref agreed. Only the next untracked control module
  remained in progress.
- **Checked control increment:** added `AllDifferentCSPRankControl.lean`.
  `rankControl_outputsInTime` and `rankControlComputableInPolyTime` prove
  that the concrete three-stack machine emits a nonempty-symbol-list bit and
  the unchanged target/symbol/tally state in `2s+2` steps for its full encoded
  length `s`. All copies, order restoration, and work-stack cleanup are
  included. `RankControl.output_length` gives exactly one added output cell.
- **Branch correspondence:** `RankControlMachine.source_present` proves
  that detecting source-field tags computes the exact branch bit. A zero
  symbol has no binary payload but still has its delimiter; it must and does
  select the nonempty branch. `RankControl.nonempty_encode` identifies the
  retained nonempty wire definitionally with the existing checked iteration
  input. `inspect_nil` and `inspect_cons` specify both outcomes, including
  zero tallies and arbitrary target/symbol magnitudes.
- **Checked entry composition:** `rankEntryComputableInPolyTime` reuses the
  pinned upstream sequential-machine API to compose initialization and the
  test from the original target/symbol query. The composed polynomial includes
  the intermediate transfer; the local `2s+2` bounds are not claimed for this
  combined entry machine.
- **Checked exit increment:** added `AllDifferentCSPRankFinalization.lean`.
  `rankFinalization_outputsInTime` and
  `rankFinalizationComputableInPolyTime` project the unary tally and clear the
  complete query in `s+1` steps. `output_length_le` proves nonexpansion.
  `result_eq_finish_of_empty` connects that output to the recursive rank
  result only when the checked nonempty-list bit is false. Projecting an
  arbitrary nonempty state's tally is not claimed to compute its final rank.
- **Proof corrections:** removed one unused encoding abbreviation from the
  test's simp list. In the exit proof, simplification left
  `List.filterMap (fun _ => none) query` unevaluated under reverse/append.
  Proved this concrete discarded-query list equals `[]` using the standard
  `List.filterMap_eq_nil_iff` simplification, then supplied that equality to
  the final wire normalization. The subsequent successful audit excludes all
  failed-build axiom reports.
- **Verification:** targeted control build passed (3144 jobs), and the final
  exit module build passed (3145 jobs). Final full `lake build` passed
  (3173 jobs); all 283 reported axiom lists use only `propext`,
  `Classical.choice`, and `Quot.sound`. All three new modules are warning-free.
  The comment/string-aware prohibited-code scan passed all 43 project Lean
  sources; `git diff --check` passed. Root imports, README and THEOREM_STATUS
  are synchronized; the full `cor:all-different-csp` remains **Partial**.
- **Preservation:** thesis HEAD remains `f1107f5` and its binary diff SHA-256
  matches the starting snapshot exactly; all twelve unrelated dirty files
  are preserved. The sibling remains clean at `7f83b99`. Neither repository
  was edited by this task. Dependency pin `ad20a2e` and toolchains unchanged.
- **Ending state and best next step:** entry, nonempty testing, and tally exit
  are checked and ready for commit/push. Implement the finite driver that
  consumes the branch bit, invokes `rankIterationComputableInPolyTime` on
  the unchanged nonempty wire, transfers the resulting state back to the
  test, and calls finalization on the empty branch. Bound repetitions by
  strict symbol-count decrease and use the existing full-state nonexpansion
  to bound each pass and all transfers. No missing upstream API was newly
  established. Composition with retained compiler sections, primal-edge
  deduplication, objective emission, and prime selection remains afterward.
- **Run time:** 2026-09-18 19:27:14 UTC (2026-09-19 05:27:14 AEST).

### 2026-09-20 — execute a complete rank cycle inside finite loop control

- **Starting state:** clean `main` at `97f6f25e94c7356d6c66ee40a62cb5286a262f8a`;
  fetched `origin`, verified `0 0` ahead/behind and matching live remote main.
  Read AGENTS, current status/README, the Lean rank pipeline and supporting
  modules, prior log/memory, and the active thesis corollary/proof. Thesis
  HEAD is `f1107f5`, with twelve unrelated dirty files and binary diff SHA-256
  `b6318d9412925b69a2affddec98bd9c09d0dabd6b2924882dab0cd2408c582ac`.
- **Read-only sibling review:** `lean-np-hardness` is clean at `d7a1bc1`.
  Its new `CertificatePredecessor.natural_evalsToInTime` and
  `list_tail_evalsToInTime` preserve framed traversal data but do not supply
  this tagged rank loop. Reviewed the checked embedding, composition, transfer,
  and polynomial-monotonicity APIs. Kept dependency pin `ad20a2e`; neither
  sibling nor thesis was edited.
- **Increment:** added `AllDifferentCSPRankLoopMachine.lean`. Its finite
  controller reuses `rankIterationComputableInPolyTime` as its complete body.
  `body_run` proves exact execution with a reached body halt redirected to
  the live collection continuation. `enter_run` scans the preserved state,
  uses the existing `source_present` criterion (including zero delimiters),
  and loads the body in original order. `return_run` restores the body's
  output and clears its output/scratch stacks before the next scan.
  `iteration_cycle` checks the whole cycle in `P(s) + 2s + 2t + 4` steps for
  complete input/output wire lengths `s,t` and the existing body polynomial P.
  `exit_run` returns the exact unary tally from the empty branch in `2s+2`
  steps; every non-output stack is empty. Zero target/tally are covered.
- **Proof corrections:** used `stackContents` after accidentally reusing the
  reserved parser token `stacks`. Alphabet equivalences point from machine
  alphabets to encoded alphabets, so loading uses `.symm` and collection uses
  the forward equivalence. Dependent single-stack contents need the same
  equality transport as `initList`/`haltList`. For the return wire, explicitly
  typed `List.append` avoids an alias-related HAppend elaboration failure;
  `List.append_eq`, `List.map_id_fun'`, and `← List.map_reverse` normalize it.
  Unfold the two local encoding aliases before arithmetic compares lengths.
  Failed-check axiom reports were discarded; only successful audits count.
- **Verification:** direct module check and full `lake build` passed (3174
  jobs). All 286 reported axiom lists use only `propext`, `Classical.choice`,
  and `Quot.sound`; the new module is warning-free. Comment/string-aware
  prohibited-code scan passed all 44 project Lean sources; diff checks passed.
  Root imports, README, and THEOREM_STATUS synchronized. The full
  `cor:all-different-csp` remains **Partial**.
- **Ending state and next step:** checked finite cycles and exit ready for
  commit/push. Next induct on the remaining symbol list, reuse full-state
  nonexpansion and upstream polynomial monotonicity, charge every cycle and
  final scan, and package the complete repeated rank machine. Full compiler
  relabelling, edge deduplication, objective emission, and final prime
  selection composition remain afterward.
- **Run time:** 2026-09-19 19:25:11 UTC (2026-09-20 05:25:11 AEST).

### 2026-09-20 — prove total polynomial-time canonical rank

- **Starting state:** finite loop controller committed and pushed as
  `cf7fd08c41a3bad713fa7a6a27651c5509e402c3`; local HEAD, `origin/main`, and
  live remote main agreed. Worktree was clean before this increment.
- **Increment:** added `AllDifferentCSPRankLoop.lean`. `state_length` gives
  the exact target-bits/source-fields/unary-tally size. `symbols_length_le_state`
  charges every occurrence to its delimiter, including zero-valued fields.
  `RankLoop.run_bounded` inducts on the remaining symbol list and reuses
  `RankIteration.output_length_le` plus the upstream
  `MachineRuntime.polynomial_eval_mono`. This proves actual repeated finite
  execution, including every loaded body call and return to the next scan.
- **Total runtime:** `RankLoop.outputsInTime` and
  `rankLoopComputableInPolyTime` prove at most
  `(s+1) * (P(s) + 4s + 4)` steps from a complete encoded query/tally state
  of length `s`, where `P` is the already checked iteration polynomial.
  The bound includes all scans, loading, body calls, return transfers,
  final target disposal, and tally output. The number of symbols decreases
  strictly even when the full wire does not. Every work stack is empty at halt.
- **Canonical-rank composition:** `canonicalRankComputableInPolyTime`
  composes the initializer and full loop through the pinned checked sequential
  API. Its input is the original checked serialized `(target, symbols)` query;
  its output is the exact one-based rank in `unaryFinEncodingNat`.
  `canonicalRank_extracted_outputsInTime` specializes that actual machine
  execution to `ExplicitSystem.relabelValue` on the extracted domain symbols.
  Its full polynomial charges initialization and the intermediate transfer;
  the preceding `(s+1)*(P(s)+4s+4)` formula is specifically the state-loop bound.
  Empty lists, zero target/symbols/tallies, duplicates and arbitrary binary
  magnitudes are covered by the general execution proof.
- **Boundary:** the local rank machine is now complete. Its specialized
  theorem starts from an already serialized target/extracted-symbol query.
  It does not yet construct all queries from, or preserve and relabel, the
  complete compiler sections. Primal-edge deduplication, encoded objective
  emission, and final prime-selection composition also remain; the thesis
  `cor:all-different-csp` remains **Partial**.
- **Proof corrections:** the exact size equation needed `Nat.add_assoc`;
  after destructuring a state, `change symbols.length ≤ _` exposes the list
  projection to `omega`. The repeated finite-execution induction and its
  arithmetic runtime bound checked without a new API blocker. Discarded the
  earlier failed-check axiom reports. No new generic foundation was duplicated.
- **Verification:** direct new-module check and final full `lake build` passed
  (3175 jobs). All 292 reported axiom lists use only `propext`,
  `Classical.choice`, and `Quot.sound`. Both new modules are warning-free;
  comment/string-aware prohibited-code scanning passed all 45 project Lean
  sources and `git diff --check` passed. Root imports, README correspondence,
  theorem status, and rank pipeline source comments synchronized.
- **Preservation:** active thesis remains at `f1107f5`, with all twelve dirty
  files and the exact starting binary-diff hash preserved. Read-only sibling
  remains clean at `d7a1bc1`; dependency pin and toolchains are unchanged.
- **Ending state and best next step:** complete local rank theorem ready for
  commit/push. Build a query-staging pass over `CountedSymbolSections.Value`
  that copies each target with the retained complete symbol list, invokes
  `canonicalRankComputableInPolyTime`, and emits the relabelled indexed
  occurrence while preserving scopes, variable count, and remaining source.
  Charge copying and rank-output conversion and prove exact agreement with
  the existing canonical relabelled domains before full compiler composition.
- **Run time:** 2026-09-19 19:30:29 UTC (2026-09-20 05:30:29 AEST).

## 2026-09-21 — stage the next retained occurrence rank query

- **Starting commit:** `bd8f58806d8ade22aef0012268e79943b520bec7`; clean
  `main`, fetched `origin/main` unchanged. Read AGENTS, theorem status, README
  correspondence, active rank/encoding/section modules, prior log and memory,
  and the active thesis corollary/proof at `sudoku-via-padic-regression/body.tex`
  lines 530–537. Thesis HEAD remains `f1107f5` with twelve existing dirty files;
  initial binary-diff SHA-256 is
  `b6318d9412925b69a2affddec98bd9c09d0dabd6b2924882dab0cd2408c582ac`.
- **Read-only upstream review:** sibling `lean-np-hardness` is clean at
  `181e969`, with a new ordered certificate-count transfer kernel. Its binary
  count layout does not supply CSP occurrence query staging. Reused the pinned
  `ad20a2e` pair codecs and machine composition/adapter APIs; no sibling edits,
  dependency changes, or duplicated generic composition foundations.
- **Checked increment:** added `AllDifferentCSPOccurrenceQuery.lean`.
  `OccurrenceQuery.inputFinEncoding` decoder-checks a nonempty occurrence list
  on exactly the existing occurrence/symbol wire. The seven-stack finite
  machine constructs `(value, fullSymbols)` and retains `(index, tail,
  fullSymbols)`. `occurrenceQuery_outputsInTime` and
  `occurrenceQueryComputableInPolyTime` prove `3s+6` steps in complete input
  length, including all copies, source-order restoration, and stack cleanup.
  `output_length` proves `output + 6 = input + symbols`; the complete output
  is at most `2s`. Zero indices/values, empty remaining records/symbol lists,
  repetitions, and arbitrary binary magnitudes are covered.
- **Verification:** full `lake build` passed (3176 jobs). The four new audits
  and all 296 reported axiom lists use only `propext`, `Classical.choice`, and
  `Quot.sound`. New module is warning-free; comment/string-aware project
  prohibited-code scan and `git diff --check` passed. README, theorem status,
  and root import synchronized; `cor:all-different-csp` remains **Partial**.
- **Failed approaches / useful API evidence:** unfolding `encodeNat` on
  symbolic values in the length proof exhausted 200000 heartbeats. Reused
  `DomainOccurrenceFieldBlock.outputEncode_eq_prefix` instead, leaving numeric
  fields opaque and closing the residual arithmetic with `omega`. Direct
  five-step unfolding stopped at `TM2.step`; replaced it with five explicit
  checked one-step transitions. Parenthesized the complete suffix passed to
  `header_run` to align append grouping. After `rw [input_length]`, `dsimp only`
  exposes tuple projections before `omega`. All failed-build audit reports
  were discarded; only the final successful build is evidence.
- **Ending state / next step:** query preparation is checked and ready for
  commit/push. Compose it with canonical rank through the existing pair-left
  adapter, retain scopes and the variable count, and prove the emitted rank
  agrees with thesis relabelling. Binary record emission and the outer
  occurrence loop, primal-edge deduplication, objective rows, and final
  prime-selection composition remain open.
- **Run time:** 2026-09-20 19:25 UTC (2026-09-21 05:25 AEST).

## 2026-09-21 — compute an occurrence rank while retaining complete sections

- **Starting commit:** `370f3777a67df62ba9ec64e0fbb2203c77d7e4c5`, the
  preceding verified query-staging increment. Its local HEAD, tracking ref,
  and live remote main were verified equal after push.
- **Checked increment:** added `AllDifferentCSPOccurrenceRank.lean`.
  `occurrenceRankComputableInPolyTime` composes preparation and the complete
  canonical-rank machine through the pinned generic pair-left adapter. It
  emits the exact unary rank while retaining the index, remaining occurrence
  stream, and complete source symbol list. `countedOccurrenceRankComputableInPolyTime`
  additionally preserves all scopes and the original variable count.
  `CountedOccurrenceRank.input_encode_eq_source` proves the input wire is
  exactly the existing nonempty counted-symbol-section encoding, without a
  preassembled query. `step_eq_relabelValue` proves exact index/rank agreement
  with the thesis compiler on its produced source sections.
- **Size and next-loop evidence:** `OccurrenceQuery.rank_le_length_add_one`
  bounds the tally by explicit symbols, independent of numeric magnitudes.
  `ranked_length_le` and the complete section `output_length_le` bound output
  by twice the input. `remaining_step` retains exactly the tail/symbols/scopes/
  count; `remaining_length` removes one occurrence. The stronger
  `remaining_encoded_length_balance` removes the head's index/value bit lengths
  plus six format cells, and `remaining_encoded_length_lt` proves strict wire
  decrease even for zero indices and values. These bounds concern the next
  source separately from any future accumulated emitted records.
- **Verification:** direct module checks passed without errors or warnings.
  Final full `lake build` passed (3177 jobs). The ten new audit commands report
  nine accepted axiom lists and one axiom-free declaration; all 305 reported
  axiom lists in the full build use only `propext`, `Classical.choice`, and
  `Quot.sound`. The comment/string-aware scan passed all 47 project Lean
  files; `git diff --check` passed. Concrete duplicate/zero examples also check.
- **Documentation:** root imports, README, theorem status, and semantic/
  encoding/rank source correspondence comments now describe the complete
  local rank and this one-occurrence composition. Corrected stale comments
  that still called the local rank machine unproved. The full corollary
  remains **Partial**, and the `3s+6` staging cost is explicitly separate from
  the complete composed polynomial and its adapter/transfer costs.
- **Failed approaches / blockers:** the second module, including the stronger
  retained-wire decrease lemma, checked on its first attempts. No new missing
  upstream API blocker was established. The rank is still unary; this result
  does not yet emit binary occurrence records or execute the outer loop.
- **Preservation:** thesis HEAD `f1107f5`, all twelve dirty-file statuses, and
  binary-diff hash match the initial snapshot exactly. The read-only sibling
  remains clean at `181e969`; the dependency pin and toolchains are unchanged.
- **Ending state / best next step:** verified second increment ready for
  commit/push; final ref parity is recorded in automation memory. Implement a
  finite pass that converts the unary rank to canonical binary, emits the
  exact `[3,0,index,rank]` record, and preserves the remaining counted sections.
  Then iterate using strict retained-source decrease, charging copied symbols
  and accumulated output against the initial source size. Primal-edge
  deduplication, objective rows, and final prime-selection composition remain.
- **Run time:** 2026-09-20 19:30 UTC (2026-09-21 05:30 AEST).

## 2026-09-22 — emit the computed rank as an exact binary occurrence

- **Starting commit:** `c1f7bc9a47901df51a6c463f4d4cc634fbaa56d3`; clean
  `main`, fetched upstream unchanged and live remote equal. Read repository
  instructions, theorem status, README correspondence, project module headers,
  active occurrence/rank/encoding/section proofs, automation memory/log, and
  the active thesis corollary/proof at `sudoku-via-padic-regression/body.tex`
  lines 530–537. Thesis remains `f1107f5` with twelve existing dirty files;
  binary-diff SHA-256 is
  `b6318d9412925b69a2affddec98bd9c09d0dabd6b2924882dab0cd2408c582ac`.
- **Read-only sibling review:** `lean-np-hardness` is clean at `5cbd76f`.
  Reviewed its new in-place certificate decrement/transfer, unary interval
  counting, and pinned pair/composition APIs. The new decrement has a framed
  binary-count interface, not this ranked occurrence wire. Reused upstream
  canonical binary-successor correctness, natural bit-length bounds, checked
  pair encodings, and composition foundations. Kept dependency `ad20a2e`;
  no sibling edits or duplicated generic codec/composition API.
- **Checked increment:** added `AllDifferentCSPOccurrenceEmit.lean`.
  `occurrenceEmit_outputsInTime` and `occurrenceEmitComputableInPolyTime`
  convert the unary rank, retain the original variable index, and emit exactly
  `[3,0,index,rank]` while preserving all remaining occurrences and symbols.
  The concrete six-stack machine includes binary carry propagation, both
  bit-order restorations, source copying, and complete work-stack cleanup.
  Its bound is `12(s+1)^2` steps for complete ranked-input wire length `s`.
  Zero rank/index, empty retained source, and carry growth are covered.
- **Size evidence:** `OccurrenceEmit.output_length` identifies every output
  bit plus six record-format cells. `output_length_le` bounds the full result
  by input length plus six, using canonical binary length at most unary tally
  length; large original symbols are never charged by their numeric value.
- **Verification:** direct Lean check passed without warnings; all three new
  axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
  Comment/string-aware scan passed all 47 current project Lean sources, and
  `git diff --check` passed. The full `lake build` is still rebuilding dependent
  modules; its final result will be recorded with the next increment.
  Root import, README, theorem status, and source correspondence synchronized;
  `cor:all-different-csp` remains **Partial**.
- **Failed approaches / exact proof evidence:** inline `apply mono (by simpa`
  continuation failed Lean's layout parser; moved the tactic onto an indented
  line. `rfl` does not prove `encodeNat 0 = []`; `simp [encodeNat, encodeNum]`
  does. `omega` initially treated local `index`/`source` lengths independently
  from their defining expressions; `dsimp [index, source]` exposes them.
  The corrected direct check passes. Failed-check axiom reports were discarded.
- **Next step:** compose query/rank/emission and preserve scopes/count through
  the checked pair adapter; prove exact replacement-size balance and thesis
  record correspondence. The outer occurrence loop, primal-edge deduplication,
  objective rows, and final prime-selection composition remain open.
- **Ending state:** the direct-checked emission increment is ready for commit
  and push; no source changes to the thesis or sibling repository. The full
  build remains in progress while the composition increment is prepared.
- **Run time:** 2026-09-21 19:31 UTC (2026-09-22 05:31 AEST).

## 2026-09-22 — compose a complete binary occurrence relabelling step

- **Starting commit:** `e11cb3955eb01363cfc7ad50309d3d8c4c3ce805`, the
  preceding emission increment. HEAD, `origin/main`, and the live remote ref
  agreed after push. Its subsequently completed full `lake build` passed
  (3178 jobs); all 308 reported axiom lists used only the three accepted
  standard axioms, with four further declarations reported axiom-free.
- **Checked increment:** added `AllDifferentCSPOccurrenceStep.lean`.
  `occurrenceStepComputableInPolyTime` composes query staging, the complete
  canonical rank machine, and binary record emission.
  `countedOccurrenceStepComputableInPolyTime` retains scopes and the original
  variable count via the pinned checked pair adapter. Its input is the
  existing decoder-checked nonempty counted-symbol-section wire; no supplied
  rank or preconstructed query is assumed. All transfer and adapter costs
  are included in the composed polynomial. The `12(s+1)^2` bound belongs
  only to the final emitter pass.
- **Semantic and size evidence:** `record_encode_eq` identifies exactly the
  thesis `[3,0,index,relabelValue value]` field block. `record_rank_bounds`
  places every actual emitted rank strictly between zero and
  `domainEntryPrime`. `record_eq_relabelValue_of_symbols` applies to later
  suffixes using the retained original symbol list; `remaining_symbols`
  preserves that invariant. `output_length_balance` proves that the only
  length change is replacement of the original value bits by rank bits.
  `output_length_le` bounds the whole result by `2s`, and
  `output_length_eq_record_add_remaining` splits that total exactly into the
  emitted block and remaining source. `record_encoded_length_le` bounds a
  single emitted block; the remaining source strictly decreases, losing
  exactly the original head's index/value bits and six format cells, while
  `remaining_length` removes one occurrence. These are useful loop bounds;
  no accumulated-output loop runtime theorem is asserted here.
- **Verification:** both direct module checks passed without warnings. All
  eleven new headline audits use only `propext`, `Classical.choice`, and
  `Quot.sound`. The comment/string-aware prohibited-code scan passes all 48
  project Lean files, and `git diff --check` passes. The final full `lake build`
  passed (3179 jobs); all 319 reported axiom lists use only the accepted
  standard axioms, with four additional declarations reported axiom-free.
  Both new modules are warning-free.
- **Proof experiments:** the smaller semantic experiment exposed a mismatch
  between `OccurrenceQuery.ranked` and its expanded tuple in `omega` atoms;
  unfolding that alias in both the length hypothesis and goal closed the
  exact balance. The composed declaration needed `outputsFun` on its own
  indented structure-update line for Lean's layout parser. All remaining
  size, retention, suffix-relabelling, and prime-bound lemmas checked without
  further errors. Failed-check axiom reports were discarded. No new upstream
  API blocker was established.
- **Documentation:** root imports, README, theorem status, and relevant source
  correspondence comments now describe the complete one-occurrence binary
  step. The full `cor:all-different-csp` remains **Partial**.
- **Best next step:** implement the finite outer occurrence loop with an
  emitted-record accumulator. Use strict remaining-source decrease to bound
  iterations and every query by the initial source; use the separate emitted
  record bound to charge accumulation and transfers. Prove exact relabelled
  domain correspondence, then address primal-edge deduplication, objective
  rows, and final prime-selection composition.
- **Preservation / ending state:** the thesis remains at `f1107f5`, with the
  same twelve dirty statuses and binary-diff hash as the starting snapshot.
  The read-only sibling remains clean at `5cbd76f`; dependency pins and
  toolchains are unchanged. The verified second increment is ready for
  commit/push; final ref parity and commit identity are recorded in the
  automation memory after pushing.
- **Run time:** 2026-09-21 19:42:49 UTC (2026-09-22 05:42:49 AEST).

## 2026-09-23 — retain ordered emitted occurrences with a finite accumulator

- **Starting commit:** `ee94d0bd377688931550c7780aac63984268f832`;
  clean `main`, fetched upstream unchanged, live remote equal. Read instructions,
  theorem status, relevant README correspondence, all project module summaries,
  active occurrence/rank/encoding proofs, automation memory/log, and the active
  thesis corollary/proof at `sudoku-via-padic-regression/body.tex` lines 530–537.
  Thesis HEAD remains `f1107f5`, with twelve existing dirty statuses and
  binary-diff SHA-256
  `b6318d9412925b69a2affddec98bd9c09d0dabd6b2924882dab0cd2408c582ac`.
- **Read-only sibling review:** clean `lean-np-hardness` at `0e6e8a4`.
  Reviewed its certificate comparison/decrement composition, checked pair
  encoding and pair-left runtime, and polynomial composition. The certificate
  wire does not supply this CSP accumulator. Reused the pinned pair encoding;
  kept dependency `ad20a2e`, with no sibling edits or duplicated generic codec.
- **Checked increment:** added `AllDifferentCSPOccurrenceAccumulator.lean`.
  `occurrenceAccumulator_outputsInTime` and
  `occurrenceAccumulatorComputableInPolyTime` append the new binary occurrence
  after all prior emitted records while preserving the next occurrence/symbol
  source. The five-stack finite machine routes and restores all tagged cells
  in `2s+4` steps for complete input length `s`; every work stack is empty at
  halt. Empty accumulators/sources, duplicates, and zero fields are included.
  `OccurrenceAccumulator.output_length` proves exact size preservation.
- **Verification:** direct module check and full `lake build` passed (3180
  jobs). The three new axiom reports use only `propext`, `Classical.choice`,
  and `Quot.sound`. Comment/string-aware prohibited-code scan and diff checks
  passed. Root import, README, and theorem status describe the actual checked
  boundary; the full corollary remains **Partial**.
- **Proof experiments:** `stacks` is reserved syntax in this environment;
  renamed the local helper `stackContents`. The size equation needed explicit
  associativity. Final output simplification exposed erased-tag `filterMap`
  terms; an explicitly typed all-`none` projection lemma, as in the prior
  control proof, closes them without unfolding numeric encodings. Discarded
  all failed-check audit output; the final check is warning-free.
- **Ending state / next increment:** accumulator verified and ready for
  commit/push. An untracked traversal module is in progress, intentionally
  excluded from this increment. Compose the rank/emitter and accumulator,
  prove ordered full traversal and a quadratic bound on every accumulated
  state, then implement the repeated finite dispatcher and its total runtime.
  Primal-edge deduplication, objective rows, and prime composition remain.
- **Run time:** 2026-09-22 19:24 UTC (2026-09-23 05:24 AEST).

## 2026-09-23 — compose ordered rank iteration and bound all traversal states

- **Starting commit:** `ce302ebf38b1f24d484a0bd2980d558580e1b0f4`, the
  preceding verified accumulator increment. Local HEAD, `origin/main`, and
  live remote main agreed after its push. Its full 3180-job build passed;
  all 322 axiom lists used only the accepted standard axioms, with four
  further axiom-free reports.
- **Checked increment:** added `AllDifferentCSPOccurrenceIteration.lean`.
  `occurrenceIterationComputableInPolyTime` composes the complete occurrence
  rank/emitter with the ordered accumulator using the pinned pair-left and
  composition APIs. It retains all prior output, removes precisely one
  source occurrence, and preserves the full symbol list. The composed
  polynomial charges every adapter and transfer; `2s+4` belongs only to the
  final accumulator pass.
- **Size proof:** `step_length_balance` replaces exactly the old value bits
  by rank bits. `budget` adds to the full serialized state a reserve of
  `remaining occurrences * (symbol-list length + 1)`. `step_budget_le` shows
  that this reserve pays for output growth. `iterate_length_le_quadratic`
  bounds every executable traversal state by `2(s+1)^2` for original complete
  wire length `s`, even with a nonempty initial accumulator.
  `finish_encoded_length_le_quadratic` bounds the full final record stream
  against the original occurrence/symbol wire, including every binary field
  and record delimiter. This is a bit-size theorem, not a repeated-machine
  runtime theorem.
- **Semantic evidence:** `finish` executes the exact checked step recursively.
  `finish_eq_append_map` preserves indices, source order, and repetitions;
  `iterate_eq_finish` proves exhaustion after exactly one step per original
  occurrence. `finish_extracted_eq_relabelValue` agrees with the thesis
  compiler, and `finish_rank_bounds` puts every actual output rank strictly
  between zero and the checked domain-entry prime. Executable examples cover
  repeated shared symbols, zero-valued repeated occurrences, and empty input
  retaining previous output.
- **Verification:** final direct Lean check and full `lake build` passed
  (3181 jobs). Eight new axiom lists use only `propext`, `Classical.choice`,
  and `Quot.sound`; the exact-exhaustion theorem is axiom-free. All 330 lists
  reported by the final build use only the accepted axioms, with five further
  axiom-free reports. Comment/string-aware prohibited-code scan passes all
  51 project Lean files, and diff checks pass. Both new modules are
  warning-free. README, theorem-status catalogue/detail, and root imports
  are synchronized; `cor:all-different-csp` remains **Partial**.
- **Proof experiments:** `nlinarith` initially saw the expanded source and
  step encodings as different atoms from the length-balance hypothesis;
  stating the goal with those same encoding expressions using `change`
  resolved it. The output-size `omega` proof needed `dsimp only at h` for
  tuple projections after `iterate_eq_finish`. Broad composition `simpa`
  unfolded only one side's pair encoding; `simpa only` with the composition
  and step definitions retained definitional agreement. One intermediate
  build failed before the tuple-projection correction; only the subsequent
  successful checks/audits are completion evidence. No missing upstream API
  blocker was established.
- **Next target:** wrap this complete body in a finite scan/load/return/exit
  dispatcher. Its state alphabet is `Sum (Sum (Option Bool) (Option Bool))
  (Option Bool)`; `.inl (.inl _)` detects remaining occurrences, including
  zero fields, and `.inr _` carries emitted output. Reuse the local checked
  rank-loop embedding design, and bound each full cycle at the uniform
  `B = 2(s+1)^2` using the decreasing budget. A prospective total bound is
  `(s+1)*(P(B)+4B+4)`; it is not yet proved for this loop. Then add the
  empty-accumulator entry and lift the complete traversal over scopes/count.
  Primal-edge deduplication, objective emission, and final prime composition
  remain separate obligations.
- **Preservation / ending state:** thesis HEAD, twelve dirty statuses, and
  binary-diff hash match the initial snapshot. The sibling remains clean at
  `0e6e8a4`; dependency pins and toolchains are unchanged. The verified second
  increment is ready for commit/push; final ref parity is recorded in
  automation memory after pushing.
- **Run time:** 2026-09-22 19:28 UTC (2026-09-23 05:28 AEST).

## 2026-09-24 — finite dispatcher for complete occurrence relabelling

- **Starting commit:** `5abf42e92b744ed3a15b439879d08b57c09e49d3`;
  clean `main`, fetched upstream unchanged, HEAD/tracking/live remote agree.
  Read instructions, current theorem status/correspondence, active Lean
  traversal and rank-loop proofs, recent journal/memory, and the active thesis
  corollary/proof in `sudoku-via-padic-regression/body.tex`.
- **Read-only context:** thesis remains `f1107f5` with twelve dirty files and
  binary-diff SHA-256
  `b6318d9412925b69a2affddec98bd9c09d0dabd6b2924882dab0cd2408c582ac`.
  Sibling `lean-np-hardness` is clean at `0360035`; reviewed its new certificate
  membership accumulation, checked pair-left polynomial adapter and composition
  APIs. It provides no reusable complete occurrence dispatcher. Reused the
  existing pinned APIs and local rank-loop design; dependency stays `ad20a2e`.
- **Checked increment:** `AllDifferentCSPOccurrenceLoopMachine.lean` wraps the
  checked rank/binary-emission/accumulation body in finite scan/load/collect/
  restore/exit control. `source_present` detects remaining occurrences by
  their tagged cells, including zero-field delimiters. `body_run` embeds the
  body with its exact checked cost. `iteration_cycle` includes every scan and
  transfer in `P(s)+2s+2t+4`, for full input/output bit lengths `s,t`.
  `exit_run` returns all accumulated binary records in `2s+2`, preserving
  source order, discarding retained symbols, and clearing all work stacks.
  Empty source/output and prior nonempty accumulation are included.
- **Verification:** direct module check and full `lake build` pass (3182 jobs).
  Four new axiom audits use only `propext`, `Classical.choice`, `Quot.sound`;
  every reported build audit uses only these standard axioms. The
  comment/string-aware project Lean scan and diff check pass. No new warnings.
  Root imports, README and theorem-status catalogue/detail are synchronized;
  full `cor:all-different-csp` stays **Partial**.
- **Failed approach / useful evidence:** arithmetic automation treated the
  nonempty state and body-input wire lengths as different atoms. An explicit
  definitional equality between these lengths resolves the cycle bound.
  Failed intermediate audit output is not completion evidence; the corrected
  check and full build are the evidence above. No missing upstream API blocker.
- **Ending state / next target:** finite cycle/exit verified, ready for commit
  and push. The separate untracked full-runtime module is in progress and
  excluded from this increment. Use the decreasing budget to bound every
  state at `B=2(s+1)^2`, then charge at most `s+1` passes at `P(B)+4B+4`.
  Compiler entry, retained scopes/count, primal-edge deduplication, objective
  rows and final prime composition remain afterward.
- **Run time:** 2026-09-23 19:21 UTC (2026-09-24 05:21 AEST).

## 2026-09-24 — polynomial runtime for the complete occurrence loop

- **Starting commit:** `f804ffb5d000196d33f61dcc197909b0d0c142dd`;
  preceding dispatcher increment pushed, local/tracking/live remote agree.
- **Checked increment:** `AllDifferentCSPOccurrenceLoop.lean` proves actual
  repeated finite execution, including every body call and transfer.
  `run_bounded` inducts on the remaining occurrences while carrying a bound
  on the decreasing size budget. It does not assume wire lengths decrease:
  ranks can require more bits than the original values. `outputsInTime` and
  `occurrenceLoopComputableInPolyTime` charge at most `s+1` passes at
  `P(B)+4B+4`, where `s` is original complete input bit length,
  `B=2(s+1)^2`, and `P` is the already checked whole-body polynomial.
  The output is exactly prior accumulated records followed by the ordered
  canonical-rank mapping. Empty input preserves prior accumulated output.
- **Verification:** standalone Lean check and full `lake build` pass
  (3183 jobs), with five new accepted axiom audits. All 339 build axiom lists
  use only `propext`, `Classical.choice`, `Quot.sound`; five further reports
  are axiom-free. Project prohibited-code scan and diff checks pass; no new
  warnings. Root imports, README and theorem-status catalogue/detail agree.
  Full `cor:all-different-csp` remains **Partial**.
- **Proof approach:** the budget invariant made the runtime induction check
  on its first attempt. Polynomial composition supplies the uniform quadratic
  size substitution without turning a semantic operation count into runtime.
  No new failed approach or missing API blocker. Corrected the previous log's
  manually entered minute to its observed run time.
- **Ending state / next target:** verified complete traversal ready for commit
  and push. A separate untracked initializer is in progress and excluded.
  Add the finite empty-accumulator initializer, compose it with the loop,
  retain scopes/count using the existing pair adapter, and connect the
  actual Boolean compiler input. Then construct deduplicated primal edges,
  objective rows, and final prime composition.
- **Run time:** 2026-09-24 05:23:35 AEST.

## 2026-09-24 — compose complete relabelling from Boolean compiler input

- **Starting commit:** `19d571b82ba835e40da0e92e14661e5b0c33ca12`;
  preceding runtime increment pushed, local/tracking/live remote agree.
- **Checked increment:** `AllDifferentCSPOccurrenceInitialization.lean` tags
  the existing occurrence/symbol wire into the exact loop state with an empty
  accumulator. `occurrenceInitialization_outputsInTime` and its polynomial
  witness include both copying passes and cleanup in `2s+2`; wire length is
  preserved, including completely empty input.
- **Compiler composition:** `AllDifferentCSPRelabelling.lean` composes entry
  and the complete traversal, then uses the pinned pair-left adapter to
  retain scopes and the original variable count. The headline
  `runtimeCompilerRelabelledSectionsComputableInPolyTime` starts at actual
  Boolean `RuntimeCompilerInput.finEncoding`, internally prepares source and
  symbols, relabels every domain occurrence, and returns the existing checked
  `CountedSections.finEncoding`. All preparation and adapter transfers belong
  to the composed polynomial, beyond the loop's own displayed bound.
- **Correspondence:** `domains_ofRuntimeSystem` gives the exact ordered map
  to `C.toExplicitSystem.relabelValue`. Scopes, variable count, occurrence
  order and repetitions survive; `recordCount_ofRuntimeSystem` retains the
  exact occurrence-plus-scope count. `rank_bounds` proves every output rank
  positive and below `domainEntryPrime`. `relabel_encoded_length_le` gives
  the quadratic output-size bound. Checked examples include shared/repeated
  symbols, empty intermediate domains, repeated scope entries, and a wholly
  empty occurrence list retaining the original variable count.
- **Verification:** targeted initialization build, direct relabelling check,
  and final full `lake build` pass (3185 jobs). Twelve new audits and all 351
  build axiom lists use only `propext`, `Classical.choice`, `Quot.sound`;
  five further reports are axiom-free. All four new modules are warning-free.
  Existing upstream prime-selector and three unchanged structural-module
  linter warnings remain; they also occur in the preceding build. The
  comment/string-aware scan passes all 55 project Lean source/config files,
  and `git diff --check` passes. Root imports, README, theorem-status
  catalogue/detail and stale source correspondence comments are synchronized.
  Full `cor:all-different-csp` remains **Partial**.
- **Failed approaches / useful evidence:** the initializer's adapted run
  proof left an empty-list append equality before the arithmetic goal.
  Normalize that equality separately, then use arithmetic; applying a
  no-progress simplifier to every goal fails. Removed one unnecessary
  `change` tactic flagged by the linter. A final audit script initially
  rejected all project warnings, then confirmed the three structural-module
  warnings were unchanged before narrowing the new-module warning check.
  Failed intermediate audits/builds were discarded; only final successful
  checks count. No unresolved API blocker.
- **Preservation:** thesis HEAD, twelve dirty statuses and binary-diff hash
  match the starting snapshot. Sibling remains clean at `0360035`.
  Dependency pins and toolchains are unchanged; no sibling edits.
- **Ending state / next target:** three coherent verified increments complete;
  this compiler-composition increment is ready for commit/push. Next build
  deduplicated primal edges from retained scopes, with increasing endpoints
  and exact agreement with `ExplicitSystem.primalEdges`. Objective emission
  must also sort/deduplicate each relabelled domain to match `pinningRows`,
  which uses a sorted finite set rather than the occurrence stream. Then
  compose residual-row emission and the already checked prime-selection
  machine into the final corollary. Final ref parity is recorded in run memory.
- **Run time:** 2026-09-24 05:30:22 AEST.
