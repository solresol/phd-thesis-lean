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
zero.

The wrapper theorem `PhdThesisLean.ContactTheorem.contact_theorem` retains the
thesis's positivity, dataset-size, and response-consistency hypotheses for exact
correspondence with `core-theorem` at thesis commit
`2c6418bcf9643fc6e039237f0f59ace14b2557fc`. The underlying Lean theorem is
slightly stronger: the perturbation proof does not need those three hypotheses
to establish the dichotomy. The completed declaration contains no placeholders,
builds with the default project target, and its axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

`DiscreteMetricRegression.lean` remains the inherited regularisation prototype.
It currently contains:

- definitions for finite rational datasets, affine hyperplanes, contact counts,
  coefficient-support counts, gain, and regularised discrete-metric loss;
- a proof that the discrete metric satisfies the ultrametric inequality;
- a lower-bound theorem for the regularised loss; and
- two declarations whose names or comments are stronger than their formal
  conclusions.

The inherited code therefore needs a statement-correspondence audit before it
can be described as a formal proof of the thesis results:

- `optimal_loss_in_finite_set` proves that one candidate expression is a lower
  bound for every hyperplane. It does not currently state that the value is
  attained or equals the optimal loss claimed by
  `thm:discrete-regularised`.
- `finite_critical_r_values` has a conclusion ending in `True` and is only a
  placeholder. It should not be counted as a formalised theorem. The current
  thesis also lists the number of distinct regularisation-path solutions as an
  open question, so the intended replacement statement must first be settled.

No theorem should be marked complete merely because Lean accepts a weaker or
vacuous formulation.

The proof library builds locally with `lake build`, and the repository has a
GitHub Actions build check. `PhdThesisLean` is an explicit default target, so a
bare build checks both the contact theorem and the imported inherited module.
The inherited trivial executable has been removed so verification does not
require native compilation of all mathlib imports.

## Source theorem catalogue

The copied statements are grouped by mathematical contribution:

- [`contact-theorem.tex`](thesis-statements/contact-theorem.tex): the central
  hyperplane-contact theorem, formalised as
  `PhdThesisLean.ContactTheorem.contact_theorem`.
- [`complexity.tex`](thesis-statements/complexity.tex): fixed-prime homogeneous
  hardness and affine-model hardness.
- [`medoids-and-coresets.tex`](thesis-statements/medoids-and-coresets.tex): the
  sparse medoid representation and the coreset obstruction.
- [`complexity-regimes.tex`](thesis-statements/complexity-regimes.tex):
  polynomial-time max loss, the equidistributed refinement result, and the
  nested easy--hard--easy family.
- [`regularisation.tex`](thesis-statements/regularisation.tex): discrete
  regularisation and the additive, lexicographic, and max-loss contact results;
  `thm:additive-contact` and `cor:additive-contact-special-cases` are formalised
  in `PhdThesisLean.AdditiveContact`.
- [`finite-domain-compilers.tex`](thesis-statements/finite-domain-compilers.tex):
  clause, finite-domain, all-different, hardness, and Sudoku results.

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

### 2. Repair the inherited discrete-metric development

- State and prove the exact correspondence with
  `thm:discrete-regularised`, including existence of a witness hyperplane,
  attainment of `K(t)`, and equality with the minimum loss.
- Define `K(t)` so impossible support sizes and empty suprema cannot make a
  theorem true for the wrong reason.
- Remove or replace `finite_critical_r_values` after reconciling it with the
  thesis's open regularisation-path question.
- Remove unused prototype definitions and add focused tests or examples.

### 3. Central contact development

- `contact_theorem` proves the mathematical contact-or-degeneracy dichotomy.
- `independent_contact_refinement` supplies `n + 1` independent contacts without
  increasing loss.
- `unique_interpolant` proves uniqueness for a full independent contact set.
- `finite_candidateModels` proves that the candidate family is finite.
- `exists_global_minimizer_on_independent_contacts` proves that exact global
  minimisation reduces to that finite family.

The mathematical theorem and its exact finite-search refinement are complete.
Formal complexity bounds for implementing the enumeration belong with the
later complexity-theoretic development.

### 4. Formalise the remaining mathematical results

A practical order is:

1. discrete regularisation, after repairing the prototype;
2. the `q > m` lexicographic valuation-histogram theorem;
3. sparse medoid representation and robustness;
4. thresholded-loss coreset obstruction;
5. max-loss and valuation-histogram results;
6. finite-domain pinning, clause indicators, and all-different correctness;
7. the mathematical parts of the hardness reductions; and
8. the complexity-theoretic encodings and polynomial-time claims.

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
