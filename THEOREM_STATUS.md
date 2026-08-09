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
| `cor:all-different-csp` | Partial | `AllDifferentCSP.ExplicitSystem` supplies explicit syntax, nonempty-domain well-formedness, a deduplicated primal graph, and canonical rank relabelling onto \(\{1,\ldots,q\}\). `selectPrimeAbove` executably scans the Bertrand interval and proves the selected prime satisfies \(q<p<2q\) for \(q>1\), with explicit \(q=0,1\) cases. `ResidualRow`, `CompiledObjective`, and `compileObjective` emit the selected prime and a finite sparse row list; `rowsLoss_compileObjective`, `compileObjective_allDifferent_correctness`, and its satisfiable specialization connect that output exactly to the checked p-adic semantics. `AllDifferentCSPEncoding.RuntimeSystem` and `RuntimeObjective` have checked `Bool`-alphabet `FinEncoding`s with exact wire-size equations. `compile_rows_length_le_encodedSize_polynomial` bounds emitted sparse rows quadratically, while `compile_encodedSize_le_quartic` bounds the complete encoded output—including every numeric field and delimiter—by \(64(s+1)^4\) in the actual input bit length \(s\). `AllDifferentCSPMachine.framedNatComputableInPolyTime` constructs each self-delimiting natural field from raw binary in linear time; `framedNatListComputableInPolyTime` traverses a stack-oriented reverse raw-field stream and emits the exact framed natural-list wire format in at most \(3s\) steps; `unframedNatListsComputableInPolyTime` traverses the standard nested-list input and exposes its outer length, inner lengths, and values as an explicitly delimited raw-field stream in at most \(3s\) steps; `binarySuccComputableInPolyTime` computes canonical binary successor in at most \(2s+3\) steps; `binaryLEComputableInPolyTime` decides less-than-or-equal on an aligned canonical binary pair in \(s+1\) steps; `binaryAddComputableInPolyTime` adds an aligned canonical pair by ripple carry in at most \(2s+3\) steps; `bertrandCandidatesComputableInPolyTime` emits exactly \([q+1,\ldots,2q]\) from a unary scan bound in at most \(16(q+1)^2\) steps; `unaryDvdComputableInPolyTime` decides \(d\mid n\) on a delimiter-separated unary-padded pair in at most \(6s+16\) steps for exact encoded length \(s=n+d+1\), including zero cases. These unary interfaces faithfully record the eventual full-input invariant \(q\le s\); they are not polynomial-time claims in the bit length of standalone binary values. CSP structural compilation and padded-bound production, deterministic primality testing and filtering, prime selection, and final machine assembly remain. |
| `cor:signed-nphard` | Partial | `FixedPrimeHardness.fixed_prime_signed_decision_is_three_sat_hard_in_cell_model` proves the explicit \(p=5\) reduction, correctness, output size, and a quadratic unit-cell construction bound. A library-native `NP-hard` transfer from a formally NP-hard 3-SAT language is not present. |
| `cor:sudoku-polynomial-dyadic-hardness` | Pending | Formalise the positive multilinear \(p=2\) reduction and its complexity transfer. |
| `cor:sudoku-special-case` | Pending wrapper | The general all-different theorem supplies the mathematics, but the 81-cell peer graph, degree-20 bound, clue domains, and Sudoku equivalence have not been instantiated in Lean. |

The headline catalogue therefore contains 24 statements: 15 complete, 2
partial, and 7 pending. The qualified clause theorem is included in the
complete count because its explicit Lean syntax captures the intended
three-distinct-variable convention; a normalisation theorem for arbitrary
3-CNF syntax would remove that qualification.

## Post-snapshot formalisation queue

The following statements were added to the active thesis after the 24 July
snapshot. They are queued separately so that the audited 24-statement baseline
and its source commit remain unchanged. All five are now formalised in
[`PhdThesisLean/PrecisionGrowth.lean`](PhdThesisLean/PrecisionGrowth.lean),
and the corresponding checkbox tasks in [`TODO.md`](TODO.md) are complete.

| Thesis label | Status | Lean declaration or remaining work |
|---|---|---|
| `prop:precision-growth-covering` | Complete | `PrecisionGrowth.precision_growth_covering` proves $N_{\mathcal H}(S,k)$ equals the covering number of the prediction set in `ℤ_[p]^m` by closed radius-$p^{-k}$ balls in the product sup metric. `mem_closedBall_iff_toZModPow` identifies same-ball membership with coordinatewise agreement under `PadicInt.toZModPow`, and `coveringNumber_eq_ncard_image` proves the class-counting identity for arbitrary vector sets. |
| `prop:precision-growth-vc` | Complete | `PrecisionGrowth.precision_growth_binary` identifies the precision-one growth function at $p=2$ with the ordinary growth function of the reduced class, and `precision_growth_vc` proves the shattering-defined VC dimension of the reduced class equals the largest $m$ with $\Pi_{\mathcal H}^{(2)}(m,1)=2^m$, via `shatters_iff_patternCount_eq`. |
| `thm:affine-precision-growth` | Complete | `PrecisionGrowth.affine_precision_growth` proves $\Pi = p^{k\min(m,d+1)}$ for the affine class on `ZMod (p ^ K)` reduced to precision $k \le K$: `affine_patternCount_le` bounds every sample through the reduced coefficient vector, and `affine_patternCount_basisSample` attains the bound on the thesis sample $0,e_1,\ldots,e_{r-1}$ padded by zeros. `affine_precision_growth_log` records the base-$p$ logarithm form $E = k\min(m,d+1)$. |
| `prop:tree-syntax-growth-bound` | Complete | `PrecisionGrowth.tree_syntax_growth_bound` bounds the pattern count of `syntaxClass` — any interpretation of a finite shape family with `R` split-rule choices per internal node and `ZMod (p ^ k)` leaf labels — by $\min(p^{km}, \sum_T R^{I(T)} p^{kL(T)})$. |
| `cor:binary-tree-precision-growth` | Complete | `PrecisionGrowth.binary_tree_precision_growth` specialises the bound to ordered full binary trees with at most $n$ internal nodes via mathlib's `Tree.treesOfNumNodesEq_card_eq_catalan` and `Tree.numLeaves_eq_numNodes_succ`, giving $\min(p^{km}, \sum_{i\le n} C_i R^i p^{k(i+1)})$. |

The cardinality equalities and inequalities are the primary Lean interface,
as planned. For the affine theorem the base-`p` logarithm identity
`E = k * min m (d + 1)` is also recorded via `Nat.log`; the real-logarithm
entropy formulas can be derived later if useful.

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
