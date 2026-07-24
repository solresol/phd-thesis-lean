# Thesis theorem formalisation status

Audited against the active thesis checkout and the copied statements at thesis
commit `2c6418bcf9643fc6e039237f0f59ace14b2557fc` on 24 July 2026.

“Complete” means that the mathematical content has a checked Lean declaration,
the project contains no `sorry` or `admit`, and the correspondence has been
reviewed. “Partial” means that the semantic reduction is checked but a
complexity or encoding claim in the LaTeX statement is not. “Pending” means
that no statement-faithful Lean theorem is currently present.

## Headline statement catalogue

| Thesis label | Status | Lean declaration or remaining work |
|---|---|---|
| `core-theorem` | Complete | `ContactTheorem.contact_theorem`; the underlying theorem is slightly stronger. |
| `thm:fixed-prime-hardness` | Pending | Formalise the positive homogeneous Max-Cut reduction for every fixed prime. The existing fixed-prime module is a different signed 3-SAT reduction at \(p=5\). |
| `cor:affine-hardness` | Pending | Formalise intercept pinning and inherit the preceding homogeneous result. |
| `thm:sparse-medoid-representation` | Complete | `SparseMedoid.sparse_medoid_representation`. |
| `prop:medoid-robustness` | Complete | `Medoid.medoid_robustness`. |
| `thm:threshold-coreset` | Complete | `Coreset.threshold_coreset`. |
| `prop:subset-summary-lower-bound` | Complete | `SubsetSummary.bounded_information_subset_summaries` and its weighted/unweighted component theorems. |
| `thm:max-polytime` | Pending | Formalise the Smith-normal-form algorithm, rational optimal witness, encoding, and polynomial running time. `MaxContact` proves attainment/contact, not this algorithmic theorem. |
| `thm:equidistributed-sum-refines-max` | Pending | No corresponding Lean development yet. |
| `thm:nested-easy-hard-easy` | Pending | No corresponding nested positive-regression construction yet. |
| `thm:discrete-regularised` | Complete | `DiscreteRegularization.discrete_regularized_regression`. |
| `cor:discrete-algorithm` | Complete | `DiscreteRegularization.discrete_algorithm`. |
| `thm:additive-contact` | Complete | `AdditiveContact.additive_contact_theorem`. |
| `cor:additive-contact-special-cases` | Complete | `AdditiveContact.additive_contact_special_cases` and the count/\(q\)-loss component theorems. |
| `thm:q-lexicographic` | Complete | `AdditiveContact.q_lexicographic_theorem`. |
| `thm:max-contact-existence` | Complete | `MaxContact.max_contact_existence`. |
| `thm:3sat-clausewise` | Complete, qualified | `ClauseCompiler.three_sat_clausewise` and `satisfiable_iff_minimum_value`. Lean makes the distinct-variable three-literal clause convention explicit. |
| `thm:compiler-template` | Complete | `FiniteDomainCompiler.finite_domain_signed_affine_compiler`; the coefficient-norm formulation is slightly stronger. |
| `cor:qp-extension` | Complete | Included in `finite_domain_signed_affine_compiler` and the global-minimiser lemmas over all of \(\mathbb Q_p^n\). |
| `thm:all-different` | Complete | `AllDifferent.all_different_correctness`. |
| `cor:all-different-csp` | Partial | Semantic correctness and finite-domain minimisation are proved. A general input syntax, encoder, bit-size measure, and polynomial-time theorem are not. |
| `cor:signed-nphard` | Partial | `FixedPrimeHardness.fixed_prime_signed_decision_is_three_sat_hard_in_cell_model` proves the explicit \(p=5\) reduction, correctness, output size, and a quadratic unit-cell construction bound. A library-native `NP-hard` transfer from a formally NP-hard 3-SAT language is not present. |
| `cor:sudoku-polynomial-dyadic-hardness` | Pending | Formalise the positive multilinear \(p=2\) reduction and its complexity transfer. |
| `cor:sudoku-special-case` | Pending wrapper | The general all-different theorem supplies the mathematics, but the 81-cell peer graph, degree-20 bound, clue domains, and Sudoku equivalence have not been instantiated in Lean. |

The headline catalogue therefore contains 24 statements: 15 complete, 2
partial, and 7 pending. The qualified clause theorem is included in the
complete count because its explicit Lean syntax captures the intended
three-distinct-variable convention; a normalisation theorem for arbitrary
3-CNF syntax would remove that qualification.

## The active thesis contains more than the headline catalogue

The active thesis checkout contains 54 theorem, corollary, proposition, or
lemma environments. The 24-row catalogue above intentionally records the main
mathematical contributions, not every supporting or applied statement.

Several of the additional environments already have Lean support even though
they do not have separate catalogue rows: the independent-contact refinement,
the coreset witness-point lemma, the 3-SAT row indicator, Boolean/domain
snapping, the all-different edge and unary identities, and the Sudoku
difference-indicator calculation.

Additional active-thesis results still lacking direct Lean declarations fall
into these groups:

- the large-prime unit-residual and prime-stability lemmas;
- the polynomial-approximation corollary, the residual-root corollaries, and
  the equioptimal interpolation theorem;
- the six-point regularisation finite-candidate lemma;
- the sparse-junta wrapper for the medoid representation;
- clause erasure by positive hole-filling;
- medoid/prefix-consensus equivalence;
- strict-refinement/no-cancellation for coefficients of distinct valuation;
- the Sudoku locator fingerprint, robust-sublevel decoding, and row-swap
  locality propositions; and
- the older \(p=2\) Max-Cut helper lemmas in the published-hardness chapter.
  These would be subsumed by a proof of `thm:fixed-prime-hardness` rather than
  needing to be copied one by one.

The separate question about how many distinct solutions occur along a
regularisation path remains an open research question in the thesis. It is not
counted as an unproved theorem because the thesis does not assert it as one.

