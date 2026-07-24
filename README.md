# Lean formalisation companion to a PhD thesis

This repository is the Lean 4 formalisation companion to Greg Baker's PhD
thesis on p-adic and ultrametric regression. It is a supplementary research
artifact, not part of the thesis PDF.

The initial Lean project was extracted from the thesis repository with its Git
history intact. The catalogue in [`thesis-statements/`](thesis-statements/)
copies the core theorem statements from thesis commit
[`2c6418bcf9643fc6e039237f0f59ace14b2557fc`](https://github.com/solresol/phd-thesis/tree/2c6418bcf9643fc6e039237f0f59ace14b2557fc).
The one uncommitted edit in the thesis working tree at extraction time did not
touch any copied theorem statement.

## Current status

The central contact theorem now has a statement-faithful proof in
[`PhdThesisLean/ContactTheorem.lean`](PhdThesisLean/ContactTheorem.lean). The
formalisation:

- represents the dataset by functions on `Fin k`, so repeated observations are
  retained and contacts count distinct observation indices;
- represents an affine model by `Fin (n + 1) → ℚ`, with the intercept in
  coordinate zero;
- uses mathlib's rational `p`-adic norm under an explicit primality assumption;
- proves the nonzero direction lemma by finite-dimensional rank-nullity;
- proves the pointwise ultrametric perturbation bound; and
- proves that every global minimiser has at least `n + 1` contacts or the data
  admit a nonzero affine function vanishing on every predictor.

The algorithmic supplement is formalised in the same module. It proves that,
for non-degenerate data:

- any affine model can be lifted to one through `n + 1` affinely independent
  observations without increasing its loss;
- those interpolation conditions determine a unique affine model;
- the family of all such independent interpolants is finite; and
- a global minimiser exists and is attained within that finite family.

The additive generalisation is formalised in
[`PhdThesisLean/AdditiveContact.lean`](PhdThesisLean/AdditiveContact.lean).
For every monotone transform on nonnegative residual magnitudes that strictly
distinguishes zero from every positive magnitude, it proves that each global
minimiser has `n + 1` contacts or the predictors are degenerate. The wrapper
`PhdThesisLean.AdditiveContact.additive_contact_theorem` corresponds to thesis
Theorem `thm:additive-contact`.

The same module also formalises Corollary
`cor:additive-contact-special-cases`: count loss is realised by the step
transform on nonnegative magnitudes, while `qLoss` implements
`q ^ (-v_p(r))` with the thesis convention that exact residuals contribute
zero. It also proves Theorem `thm:q-lexicographic`: when `q` exceeds the data
count, the first differing finite valuation bin determines the strict ordering
of two additive `q`-losses. Exact residuals are explicitly omitted from the
integer-valued histogram rather than being assigned a spurious finite
valuation.

Max-loss attainment is formalised in
[`PhdThesisLean/MaxContact.lean`](PhdThesisLean/MaxContact.lean). The pointwise
form of the independent-contact refinement shows that every model is dominated
by a member of the finite independent-interpolant family. Minimising over that
family proves that the max loss attains its global minimum and that at least one
minimiser has `n + 1` contacts, as required by
`thm:max-contact-existence`.

The medoid results are formalised in
[`PhdThesisLean/Medoid.lean`](PhdThesisLean/Medoid.lean) and
[`PhdThesisLean/SparseMedoid.lean`](PhdThesisLean/SparseMedoid.lean).
The robustness proof works directly in mathlib's completed field `ℚ_[p]`,
proves the factor-`p` separation between a precision ball and an outside
candidate, and establishes `prop:medoid-robustness` for indexed candidate
multisets. The finite-precision development uses `ZMod (p ^ K)`, constructs
the full centre-and-slope ensemble, and proves `thm:sparse-medoid-representation`:
`F x` is an ensemble output, is a medoid value, and is the output value of
every medoid index. Thus duplicate indices are retained while the medoid value
is unique, exactly as required for the thesis multiset.

The thresholded-loss coreset obstruction is formalised in
[`PhdThesisLean/Coreset.lean`](PhdThesisLean/Coreset.lean). It proves the
uniform-cost witness-point argument, constructs an injectively indexed
`k`-point dataset in `ℚ_[p]^(d-1) × ℚ_[p]` for every `d ≥ 2`, and establishes
`thm:threshold-coreset` for positive-weight subset objectives with support
smaller than `k` whenever `0 < ε < 1/(2k-1)`. The dataset range is proved to
have cardinality exactly `k`, and `exactFit_coreset` records the `τ = 0`
special case.

The complementary decoder-based lower bound is formalised in
[`PhdThesisLean/SubsetSummary.lean`](PhdThesisLean/SubsetSummary.lean).
It constructs the standard-basis datasets from
`prop:subset-summary-lower-bound`, proves their unique minimisers, counts the
unweighted and finite-weight-alphabet summary spaces by support size, and
proves that any decoder fails by more than `Δ` on at least one separated
parameter vector under the thesis cardinality bounds.

The finite-domain signed affine compiler is formalised in
[`PhdThesisLean/FiniteDomainCompiler.lean`](PhdThesisLean/FiniteDomainCompiler.lean).
It proves the coordinate-snapping inequality over all of `ℚ_[p]`, existence of
a global minimiser in the finite product domain, exclusion of every
off-domain point from the global minimisers, and the constant-plus-finite
signed-objective formula on the domain. This proves both
`thm:compiler-template` and its stronger `cor:qp-extension`; the Lean theorem
also permits arbitrary coefficient values of p-adic norm at most one.

The all-different/list-colouring instantiation is formalised in
[`PhdThesisLean/AllDifferent.lean`](PhdThesisLean/AllDifferent.lean). It proves
the exact constant-minus-total-edge-weight plus weighted-conflict identity,
existence of global minimisers, equivalence between global minimisation and
minimum conflict on the finite product domain, and—when a proper assignment
exists with positive edge weights—equivalence between global minimisers and
proper list-colourings. Edges are indexed, so parallel or repeated constraints
retain their multiplicity.

The direct clause-wise 3-SAT compiler is formalised in
[`PhdThesisLean/ClauseCompiler.lean`](PhdThesisLean/ClauseCompiler.lean). It
defines literals and distinct-variable three-literal clauses, proves the
`p > 3` clause-row indicator, proves that the compiled objective equals
`α n - sat` on Boolean assignments, and characterises global minimisers as
maximum-satisfaction assignments. It also proves the thesis equivalence
between formula satisfiability and attainment of the value
`α n - numberOfClauses`.

The fixed-prime reduction is formalised in
[`PhdThesisLean/FixedPrimeHardness.lean`](PhdThesisLean/FixedPrimeHardness.lean).
It defines finite 3-CNF syntax and explicit signed affine decision instances
at `p = 5`, chooses `α = 1 + Δ`, and proves that a formula is satisfiable
exactly when the compiled objective attains the threshold `α n - m`. It also
proves that any exact global optimiser decides the source formula. The dense
expansion has exactly `2n + m` observations, and both its output size and
straightforward construction cost are proved quadratic in the documented
unit-cell syntax model.

This completes the concrete reduction premise of `cor:signed-nphard`.
Mathlib at the pinned revision has finite encodings and structures for
polynomial-time two-stack Turing-machine computation, but it has no P/NP or
Cook--Levin development, and composition of those polynomial-time machines is
still marked `proof_wanted`. The final transfer from the proved 3-SAT
reduction to a library-native `NP-hard` predicate is therefore not represented
as complete. `PolynomialCellReduction` states the precise complexity model
currently proved; a future bit-level complexity foundation can consume the
semantic and size theorems without changing the p-adic argument. See
[`docs/FORMAL_NP_HARDNESS.md`](docs/FORMAL_NP_HARDNESS.md) for the research
survey and recommended route.

The wrapper theorem `PhdThesisLean.ContactTheorem.contact_theorem` retains the
thesis's positivity, dataset-size, and response-consistency hypotheses for exact
correspondence with `core-theorem` at thesis commit
`2c6418bcf9643fc6e039237f0f59ace14b2557fc`. The underlying Lean theorem is
slightly stronger: the perturbation proof does not need those three hypotheses
to establish the dichotomy. The completed declaration contains no placeholders,
builds with the default project target, and its axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Discrete-metric regularisation is formalised in
[`PhdThesisLean/DiscreteRegularization.lean`](PhdThesisLean/DiscreteRegularization.lean).
It defines `K(t)` as the maximum of the finite set of contact counts actually
attained by models with exactly `t` nonzero slopes, proves every support class
`0 ≤ t ≤ n` is nonempty, and proves that `K(t)` is attained. The theorem
`discrete_regularized_regression` then supplies an actual global minimiser at a
support size maximising `K(t) - rt`, together with the displayed minimum-loss
identity from `thm:discrete-regularised`. The theorem `discrete_algorithm`
formalises `cor:discrete-algorithm`: given one attaining witness per support
size, finite candidate-gain selection returns a global minimiser.

The old top-level `DiscreteMetricRegression.lean` is now only a compatibility
import for the statement-faithful module. Its unattained supremum and vacuous
regularisation-path placeholder have been removed. The number of distinct
regularisation-path solutions remains an open thesis question and is not
misrepresented as a completed theorem.

The proof library builds locally with `lake build`, and the repository has a
GitHub Actions build check. `PhdThesisLean` is an explicit default target, so a
bare build checks both the contact theorem and the imported inherited module.
The inherited trivial executable has been removed so verification does not
require native compilation of all mathlib imports.

## Source theorem catalogue

The current statement-by-statement audit, including pending and partial
results, is in [`THEOREM_STATUS.md`](THEOREM_STATUS.md).

The copied statements are grouped by mathematical contribution:

- [`contact-theorem.tex`](thesis-statements/contact-theorem.tex): the central
  hyperplane-contact theorem, formalised as
  `PhdThesisLean.ContactTheorem.contact_theorem`.
- [`complexity.tex`](thesis-statements/complexity.tex): fixed-prime homogeneous
  hardness and affine-model hardness.
- [`medoids-and-coresets.tex`](thesis-statements/medoids-and-coresets.tex): the
  sparse medoid representation, medoid robustness, and the coreset obstruction;
  `prop:medoid-robustness` and `thm:sparse-medoid-representation` are formalised
  in namespace `PhdThesisLean.Medoid`, while `thm:threshold-coreset` is
  formalised in `PhdThesisLean.Coreset` and
  `prop:subset-summary-lower-bound` in `PhdThesisLean.SubsetSummary`.
- [`complexity-regimes.tex`](thesis-statements/complexity-regimes.tex):
  polynomial-time max loss, the equidistributed refinement result, and the
  nested easy--hard--easy family.
- [`regularisation.tex`](thesis-statements/regularisation.tex): discrete
  regularisation and the additive, lexicographic, and max-loss contact results;
  `thm:discrete-regularised` and `cor:discrete-algorithm` are formalised in
  `PhdThesisLean.DiscreteRegularization`; `thm:additive-contact`,
  `cor:additive-contact-special-cases`, and
  `thm:q-lexicographic` are formalised in `PhdThesisLean.AdditiveContact`, and
  `thm:max-contact-existence` is formalised in `PhdThesisLean.MaxContact`.
- [`finite-domain-compilers.tex`](thesis-statements/finite-domain-compilers.tex):
  clause, finite-domain, all-different, hardness, and Sudoku results;
  `thm:compiler-template` and `cor:qp-extension` are formalised in
  `PhdThesisLean.FiniteDomainCompiler`, and `thm:all-different` is formalised in
  `PhdThesisLean.AllDifferent`; `thm:3sat-clausewise` is formalised in
  `PhdThesisLean.ClauseCompiler`. The concrete `p = 5` reduction premise of
  `cor:signed-nphard` is formalised in `PhdThesisLean.FixedPrimeHardness`.

These files are provenance snapshots, not standalone LaTeX documents and not
Lean source. Supporting definitions and lemmas should be copied or restated
only as their target theorem is formalised.

## What needs to be done

### 1. Establish the formal foundations

- Replace the prototype's ad hoc structures with a small, reusable namespace
  for finite datasets, affine maps, residuals, and loss aggregations.
- Decide theorem by theorem whether the domain is `ℚ`, `ℤ_p`, or `ℚ_p`, and
  use mathlib's existing p-adic definitions wherever possible.
- Represent multisets or indexed observations faithfully. A `Finset` silently
  removes duplicate observations and is not always equivalent to the thesis's
  datasets.
- Separate mathematical optimisation statements from computability and
  polynomial-time complexity statements.
- Record all finiteness, non-degeneracy, existence, and attainment assumptions
  explicitly.

### 2. Discrete-metric development

- `exists_model_with_slopeSupportCount` proves every support size through `n`
  is feasible.
- `exists_model_attaining_K` proves the finite maximum defining `K(t)` has a
  witness.
- `discrete_regularized_regression` proves the exact optimisation and
  minimum-loss statement.
- `discrete_algorithm` proves correctness of finite candidate-gain selection
  from supplied attaining witnesses.

The two discrete regularisation statements in the thesis snapshot are
complete. The separate regularisation-path counting question remains open.

### 3. Central contact development

- `contact_theorem` proves the mathematical contact-or-degeneracy dichotomy.
- `independent_contact_refinement` supplies `n + 1` independent contacts without
  increasing any residual norm, and hence without increasing summed or max
  loss.
- `unique_interpolant` proves uniqueness for a full independent contact set.
- `finite_candidateModels` proves that the candidate family is finite.
- `exists_global_minimizer_on_independent_contacts` proves that exact global
  minimisation reduces to that finite family.

The mathematical theorem and its exact finite-search refinement are complete.
Formal complexity bounds for implementing the enumeration belong with the
later complexity-theoretic development.

### 4. Formalise the remaining mathematical results

A practical order is:

1. a bit-level P/NP and polynomial-time reduction foundation;
2. the remaining positive-polynomial and Sudoku hardness reductions; and
3. complexity-theoretic encodings for those reductions.

The NP-hardness results require more than proving the displayed objective
identity. A complete formalisation must define the source and target decision
or optimisation problems, their encodings and size measures, the reduction,
and the relevant complexity class.

### 5. Add repository-level verification

- Move the Lean files into a conventional library namespace as the project
  grows.
- Pin a Lean toolchain and compatible mathlib revision deliberately; the
  inherited toolchain is an RC version.
- Keep the `lake build` GitHub Actions check required and passing.
- Reject `sorry`, `admit`, and vacuous placeholder conclusions in review.
- Use `#print axioms` or an equivalent audit for completed headline theorems.
- Add small executable examples where they clarify that a definition matches
  the thesis objective.

### 6. Maintain thesis correspondence

For every formal theorem, record:

- the thesis path and LaTeX label;
- the thesis commit or release to which it corresponds;
- whether the Lean statement is exact, stronger, weaker, or only partial;
- any changed assumptions or representation choices; and
- the Lean declaration and module containing the proof.

A theorem is complete only when the correspondence is reviewed, the proof has
no placeholders, the project builds from a clean checkout, and the declaration
uses only accepted axioms.

## Building

Install Lean with [elan](https://github.com/leanprover/elan), then run:

```bash
lake build
```

The first build downloads mathlib and its dependencies.

## Scope

This repository is intended to formalise the mathematical claims of the
thesis. It does not reproduce the empirical experiments, browser
demonstrations, or the thesis document itself. Experimental propositions can
be added later when they express reusable mathematics rather than contingent
measurements.
