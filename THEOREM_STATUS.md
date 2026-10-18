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
| `thm:fixed-prime-hardness` | Complete | `FixedPrimeMaxCut.fixed_prime_hardness` proves the complete Max-Cut reduction for every prime over `ℚ_[p]`: `local_boolean_snapping` (`lem:local-boolean-snapping`), the forcing objective `maxCutLoss` with `M_j = d_j + 1`, Booleanity of every global minimiser (`globalMin_boolean`), existence, the characterisation of global minimisers as embeddings of maximum cuts (`isGlobalMin_iff`), the Boolean value `∑ M_j + #monochromatic`, and the optimal value `∑ M_j + |E| - maxcut`. `homogeneousLoss_maxCutRows` identifies the objective with the homogeneous summed loss of an explicit `{0,1}`-valued row family of `5|E| + 2n` rows. Edges are an arbitrary finite index type (multigraphs allowed). The complexity statement is checked end to end: `PadicRegressionLanguage` states the decision problem as a `lean-np-hardness` `EncodedLanguage` (integral rows, natural bound, unary and binary CNF-style encodings); `FixedPrimeMaxCutReduction.maxCut_iff_regression` proves for every prime that the edge-streamed variant of the reduction (one forcing pair per edge endpoint, plus a pendant edge to a fresh vertex and `K + 2` constant rows absorbing the threshold) preserves membership, with snapping over `ℚ`; `FixedPrimeMaxCutMachine.fmcR_exits` and `cost_le` give an exact TM2 run within `10⁶(n+1)²` steps; and `encodedUnaryRegression_NPHard p` / `encodedRegression_NPHard p` derive NP-hardness from the library's Cook–Levin-based `encodedUnaryMaxCut_NPHard`. |
| `cor:affine-hardness` | Complete | `FixedPrimeMaxCut.intercept_pinning` proves `lem:intercept-pinning` for any integral instance (`L_aff(β,0) ≤ L_aff(β,c) - (T - r)‖c‖`, with `affineLoss_zero_lt` and `isGlobalMin_affine_iff` for `T ≥ r + 1`, and `affineRowLoss_pinnedRows` realising the pinning rows literally). `affine_hardness` then shows the affine minimisers of the pinned Max-Cut instance are exactly `(embed s, 0)` for maximum cuts `s`, with the same optimal value and `10|E| + 4n + 1` rows. The complexity statement is checked: the rows emitted by `FixedPrimeMaxCutMachine` include `r + 1` zero rows for `r` other rows, `FixedPrimeMaxCutReduction.loss_le_affineLoss` is intercept pinning over `ℚ` for these instances, `maxCut_iff_affine` proves the reduction to `PadicRegressionLanguage.AffineRegressionLang p`, and `encodedUnaryAffineRegression_NPHard p` / `encodedAffineRegression_NPHard p` conclude NP-hardness for every prime. |
| `thm:sparse-medoid-representation` | Complete | `SparseMedoid.sparse_medoid_representation`. |
| `prop:medoid-robustness` | Complete | `Medoid.medoid_robustness`. |
| `thm:threshold-coreset` | Complete | `Coreset.threshold_coreset`. |
| `prop:subset-summary-lower-bound` | Complete | `SubsetSummary.bounded_information_subset_summaries` and its weighted/unweighted component theorems. |
| `thm:max-polytime` | Partial | `MaxObjective.max_objective_attained` proves the minimum defining `ρ_max` is attained (for arbitrary `p`-adic data), and `max_objective_rational_optimum` proves that for rational data an optimal `β` may be chosen in `ℚ^n`, realising `ρ_max` (`max_objective_rational_optimum_rhoMax`); `exists_rat_solution_of_padic_solution` closes the exact-fit case by base change. The algorithm's reductions are checked: sup-norm invariance under `GL_m(ℤ)` (`norm_mulVec_generalLinearGroup`) and denominator clearing (`isGlobalMin_clear_denominators_iff`); `sum_objective_not_unimodular_invariant` witnesses the thesis's closing remark. `MaxObjectiveSmith` proves the algorithm's formula for any Smith decomposition `UAV = S` (`U`, `V` unimodular, `S` with zero off-diagonal): `smith_isGlobalMin` exhibits the optimiser `β = Vγ` with `γ_i = b'_i/s_i` (the image of a rational vector, `smith_optimizer_rational`), `rhoMax_smith` gives `ρ_max = max_{i>t}|b'_i|_p` over the zero rows of `S`, and `rhoMax_rational_smith` gives the thesis's `ρ_max(X, y) = |D|_p⁻¹ max_{i>t}|b'_i|_p`. Remaining: computing the Smith decomposition and the polynomial running time (Kannan–Bachem) are external. |
| `thm:equidistributed-sum-refines-max` | Complete | `EquidistributedSumRefinesMax.equidistributed_sum_refines_max`: for `x_i ∈ ℤ_p^d` exactly equidistributed modulo `p`, an intercept in the model, and no exact affine fit, every `L_1` minimiser is an `L_∞` minimiser. The stronger `isGlobalMin_Linf_of_isGlobalMin_L1` drops the no-exact-fit hypothesis. The Lean proof is purely finite (a counting lemma `card_affZ_zero_mul_le` for nonzero affine functions on `𝔽_p^d` plus an average over `p` intercept shifts) and replaces the thesis's compactness and Haar-measure steps; the conclusion is identical. |
| `thm:nested-easy-hard-easy` | Complete | `NestedEasyHardEasy.nested_easy_hard_easy` constructs the literal multiset nesting `A_G ≤ A'_G ≤ A''_G` over `ℚ_[5]` for any self-loop-free (multi)graph and proves all three stages: `stage1_globalMin_iff` (unique optimum `0`, loss `0`); `loss_A'` and `card_A'` (the loss of `A'_G` is exactly the fixed-prime Max-Cut objective, with `5|E|+2|V|` rows); and `stage3_globalMin_iff`, `stage3_optimum`, `loss_A''_optimum` (for every `L ≥ 1` the global minimisers of `A''_G` are exactly the grid `T^n`, with `(c,…,c)` optimal at the closed-form value `m_H 5^L + 4nN5^L`). `NestedEasyHardEasyHardness.loss_A'_eq_maxCutLoss` identifies the Stage 2 loss with `FixedPrimeMaxCut.maxCutLoss`, so `stage2_globalMin_iff` and `stage2_optimal_value` give the Max-Cut characterisation of the hard stage; `nested_easy_hard_easy_with_hardness` bundles all three stages. The Stage 2 complexity clause is checked: `NestedStage2Reduction.maxCut_iff_stage2` proves that the map to the rows of `A'_{G''}` (for `G''` the graph with a pendant edge to a fresh vertex absorbing the threshold, padded to the input length `L`) preserves Max-Cut membership with bound `3|E| + 2 + L - K`; `stage2_rows_eq_A'_G` shows the produced rows are literally the multiset `A'_G` of that loopless graph; `NestedStage2Machine` computes the map with the two-pass machine (the second pass reads the reversed input and uses a flag so that the threshold's marks do not enter the bound, avoiding subtraction); and `satStage2_NPHard` with `satStage2_dataset_eq_A'_G` gives a polynomial-time reduction from CNF-SAT, through the library's chain and Max-Cut gadget reductions, all of whose datasets are `A'_G` of loopless graphs. |
| `thm:discrete-regularised` | Complete | `DiscreteRegularization.discrete_regularized_regression`. |
| `cor:discrete-algorithm` | Complete | `DiscreteRegularization.discrete_algorithm`. |
| `thm:additive-contact` | Complete | `AdditiveContact.additive_contact_theorem`. |
| `cor:additive-contact-special-cases` | Complete | `AdditiveContact.additive_contact_special_cases` and the count/\(q\)-loss component theorems. |
| `thm:q-lexicographic` | Complete | `AdditiveContact.q_lexicographic_theorem`. |
| `thm:max-contact-existence` | Complete | `MaxContact.max_contact_existence`. |
| `thm:3sat-clausewise` | Complete | `ClauseCompiler.three_sat_clausewise` and `satisfiable_iff_minimum_value` for the distinct-variable three-literal convention, and `CNFNormalisation.normalise_satisfiable_iff`, `general_satisfiable_iff_minimum_value`, `general_three_sat_clausewise` for arbitrary 3-CNF syntax (repeated literals, tautological and empty clauses), via a computable normalisation with three fresh variables and at most eight clauses per source clause (`normalise_cellSize_le`). |
| `thm:compiler-template` | Complete | `FiniteDomainCompiler.finite_domain_signed_affine_compiler`; the coefficient-norm formulation is slightly stronger. |
| `cor:qp-extension` | Complete | Included in `finite_domain_signed_affine_compiler` and the global-minimiser lemmas over all of \(\mathbb Q_p^n\). |
| `thm:all-different` | Complete | `AllDifferent.all_different_correctness`. |
| `cor:all-different-csp` | Partial | `AllDifferentCSP.ExplicitSystem` supplies explicit syntax, nonempty-domain well-formedness, a deduplicated primal graph, and canonical rank relabelling onto \(\{1,\ldots,q\}\). `selectPrimeAbove` executably scans the Bertrand interval and proves the selected prime satisfies \(q<p<2q\) for \(q>1\), with explicit \(q=0,1\) cases. `ResidualRow`, `CompiledObjective`, and `compileObjective` emit the selected prime and a finite sparse row list; `rowsLoss_compileObjective`, `compileObjective_allDifferent_correctness`, and its satisfiable specialization connect that output exactly to the checked p-adic semantics. `compileObjectiveAt` exposes those same rows under any checked supplied-prime header. `AllDifferentCSPEncoding.RuntimeSystem` and `RuntimeObjective` have checked `Bool`-alphabet `FinEncoding`s with exact wire-size equations. `compile_rows_length_le_encodedSize_polynomial` bounds emitted sparse rows quadratically, while `compile_encodedSize_le_quartic` bounds the complete encoded output—including every numeric field and delimiter—by \(64(s+1)^4\) in the actual input bit length \(s\). `compileUsingDomainEntryBound` chooses a prime above the explicit domain-entry count; `symbolCount_lt_domainEntryPrime` proves this input-length-bounded choice is large enough for the canonical ranks, its two correctness theorems give exact minimum-conflict and satisfiable-case semantics, and `compileUsingDomainEntryBound_encodedSize_le_quartic` preserves the complete quartic output bound. `RuntimeCompilerInput.finEncoding` adds the explicit occurrence count as a decoder-checked unary header with at most linear overhead, and `compileUsingDomainEntryBound_encodedSize_le_compilerInput_quartic` retains the full quartic output bound against this actual compiler input. `RuntimeStructuralView` gives the structural machine an exact checked target: its header retains the variable count, each explicitly listed domain value becomes a tagged indexed occurrence without deduplication or reordering, every attached index is proved in range, and every scope remains an intact tagged record; its Boolean `FinEncoding` round-trips exactly. `ofRuntimeSystem_encodedSize_le_quadratic` bounds that complete tagged encoding by \(32(s+1)^2\) bits in the compact input length, and `ofRuntimeSystem_encodedSize_le_compilerInput_quadratic` retains the same bound against the actual compiler input without treating numeric symbol magnitude as bit length. `RuntimeStructuralView.rawFinEncoding` checks the corresponding stack-oriented raw-field representation, and `runtimeStructuralViewFramingComputableInPolyTime` converts it to the exact Boolean encoding in at most three times the raw input length. `AllDifferentCSPMachine.framedNatComputableInPolyTime` constructs each self-delimiting natural field from raw binary in linear time; `framedNatListComputableInPolyTime` traverses a stack-oriented reverse raw-field stream and emits the exact framed natural-list wire format in at most \(3s\) steps; `unframedNatListsComputableInPolyTime` traverses the standard nested-list input and exposes its outer length, inner lengths, and values as an explicitly delimited raw-field stream in at most \(3s\) steps; `domainEntryCountComputableInPolyTime` extracts the checked unary occurrence header in exactly \(s+1\) steps for complete compiler-input length \(s\); `compilerPayloadComputableInPolyTime` removes that header while preserving the compact payload byte-for-byte in at most \(2s+1\) steps, and `runtimeCompilerRawFieldsComputableInPolyTime` composes this pass with unframing to emit the exact nested-list structural fields from the actual compiler input. `SourceOrderRawNatLists.finEncoding` checks the same fields in semantic source order, with each delimiter before its canonical binary payload; `sourceOrderRawFieldsComputableInPolyTime` constructs that representation in exactly \(s+1\) steps, and `runtimeCompilerSourceOrderFieldsComputableInPolyTime` composes it from the actual compiler input so the outer length and domain-count separator precede all domain and scope fields. `SourceOrderRawFields.finEncoding` checks uncounted local field sequences. `domainOccurrenceBlockComputableInPolyTime` emits the exact `[3, 0, index, value]` domain-occurrence block in at most \(2s+2\) steps, while `scopeFieldBlockComputableInPolyTime` emits the exact intact `[|S|+1, 1, ...S]` scope block from its count-checked source fields in at most \(3s+8\) steps, including empty and singleton scopes. `domainFieldRowComputableInPolyTime` expands a complete count-checked `[index, |D|, ...D]` row into every exact `[3, 0, index, value]` block in at most \(20(s+1)^2\) steps in the complete row wire length, including empty and singleton domains. `DomainFieldSection.inputFinEncoding` checks the complete domain count and every row count in the existing source-order nested-list encoding; `occurrences_indexedRowsFrom` advances indices across all rows, including empty rows, and `outputEncode_eq_structuralFields` identifies the concatenated checked row outputs exactly with `StructuralFieldStream.domainFieldsFrom`. `DomainFieldSection.rowPayloadFinEncoding` rechecks the outer-count-free row payload through exhaustion, `rowFields_injective` proves its domain boundaries are unique, and `domainRowPayloadStructuredComputableInPolyTime` maps the complete section to that structured payload in at most \(2s+1\) steps without increasing its encoded length. `domainSectionComputableInPolyTime` consumes that payload, advances a canonical binary index across every row including empty rows, and emits exactly `RuntimeStructuralView.indexedDomainOccurrences` in at most \(100(s+1)^3\) bit-level steps. `completeDomainSectionComputableInPolyTime` composes the count-removal and indexed-row machines from the complete counted domain section to the same exact occurrence stream. `ScopeFieldSection.outputFinEncoding` checks the complete tagged scope output using the existing counted-row parser; its exact round trip retains empty scopes and repetitions, and `outputEncode_length_le_linear` bounds that output by four times the actual raw payload length. `scopeRowPayloadStructuredComputableInPolyTime` reuses the linear count-removal machine for scopes. `scopeSectionComputableInPolyTime` emits the exact complete tagged scope list in at most \(20(s+1)^2\) bit-level steps for payload length \(s\), preserving empty rows and repetitions with explicit binary countdowns; `completeScopeSectionComputableInPolyTime` composes it with count removal from the complete checked section. `sourceSectionsComputableInPolyTime` splits the full source-order runtime input into the existing checked pair of counted domains and scope payloads in at most \(40(s+1)^2\) steps, preserving empty sections, empty rows, repetitions, and arbitrary binary values without increasing encoded length. `runtimeCompilerSectionsComputableInPolyTime` composes that split from the actual compiler input. `pairedDomainSectionComputableInPolyTime` reuses the checked generic pair-left API at dependency commit `db20c69` to expand domains while preserving scopes; `runtimeCompilerDomainAndScopesComputableInPolyTime` composes the full input to that exact paired output. `LeanNPHardness.PairExchange.outputsInTime` checks exact canonical section exchange in at most `4s+6` steps for complete paired wire length `s`. `pairedScopeSectionComputableInPolyTime` composes two such exchanges with the pinned generic pair-left scope machine, preserving the exact domain output and restoring section order; `pairedScopeSection_output_length_le` bounds the entire paired output by four times its input length. `runtimeCompilerProcessedSectionsComputableInPolyTime` constructs both exact tagged sections from the actual Boolean compiler input with a checked polynomial bound. `variableHeaderComputableInPolyTime` copies the variable count from the third checked source field while preserving the complete source in at most `3s+6` steps, with paired output length at most `2s`; `runtimeCompilerVariableHeaderComputableInPolyTime` constructs this source/count pair from the actual compiler input. `runtimeCompilerCountedSectionsComputableInPolyTime` carries that count through the source split and both section passes using the checked generic pair-left API, constructing the exact occurrence/scope/count tuple from the actual Boolean input. `CountedSections.toStructuralView_ofRuntimeSystem` proves exact reconstruction, and `recordCount_le_encode_length` bounds the record count by the complete tuple encoding length. `runtimeCompilerStructuralPayloadComputableInPolyTime` now assembles the exact structural view under `RuntimeStructuralView.payloadFinEncoding`, reusing the exhaustion-delimited counted-row decoder. `structuralAssemblyComputableInPolyTime` performs the final merge in at most `2s+3` steps and adds exactly three header cells. `payloadEncode_ofRuntimeSystem_length_le_compilerInput_quadratic` bounds the constructed payload by `32 * (s+1)^2` in the actual Boolean compiler input length, while `rowCount_le_payloadEncode_length` bounds the required outer row count by the payload length. The full input composition has a checked polynomial bound. `structuralRowCountComputableInPolyTime` now retains the complete payload and constructs its unary outer row count in at most `20 * (s+1)^2` finite-machine steps for payload length `s`; its exact paired output is `(view, view.records.length + 1)`. `runtimeCompilerStructuralCountedPayloadComputableInPolyTime` composes that pass from the actual Boolean compiler input to the exact view and `C.domainEntryCount + C.scopes.length + 1`. `StructuralCountedPayload.encode_retain_length_le` bounds the pair by twice the payload length, and its compiler-input specialization bounds the whole output by `64 * (s+1)^2`. Binary conversion, raw staging, and framing now compose from the actual Boolean compiler input. `StructuralFieldStream.encode_eq_header_sections` and `raw_encode_eq_reversed_sections` specify exact section/header assembly and reversal into the checked raw structural view; the binary-header machine now realizes that raw target from the computed row count. `binarySuccComputableInPolyTime` computes successor on mathlib's canonical binary natural encoding in at most \(2s+3\) steps; `binaryLEComputableInPolyTime` decides less-than-or-equal on an aligned canonical binary pair in \(s+1\) steps; `binaryAddComputableInPolyTime` adds an aligned canonical pair by ripple carry in at most \(2s+3\) steps; `bertrandCandidatesComputableInPolyTime` emits exactly \([q+1,\ldots,2q]\) from a unary scan bound in at most \(16(q+1)^2\) steps. `RawUnaryNatList.finEncoding` checks the internal unary-delimited candidate stream; `unaryBertrandCandidatesComputableInPolyTime` emits the same list in at most \(6(q+1)^2\) steps, and `unaryBertrandCandidateStream_length_le` bounds it by \(2q^2+2q+1\) cells. `unaryDvdComputableInPolyTime` decides \(d\mid n\) on a delimiter-separated unary-padded pair in at most \(6s+16\) steps for exact encoded length \(s=n+d+1\), including zero cases. `trialPrime_eq_true_iff` proves that testing exactly the divisors in \([2,n)\) decides primality; `trialDivisionInputSize_le` bounds all unary trial pairs for one candidate by \(2n(n-2)\) cells; `RawUnaryPairList.finEncoding` checks the stack-oriented padded-pair stream; `trialDivisionPairsComputableInPolyTime` emits exactly \([(n,2),\ldots,(n,n-1)]\) from unary \(n\) in at most \(8(n+1)^2\) steps, including the empty \(n=0,1,2\) cases. `pairDivisionResultsComputableInPolyTime` consumes any such stream, applies divisibility to every field, and emits the exact Boolean results in at most \(17s+1\) steps for stream length \(s\); `trialDivisionPairStream_length_le` bounds the concrete trial stream by \((2n+1)(n-2)\). `allFalseComputableInPolyTime` folds a Boolean result stream in at most \(s+1\) steps, and `allFalse_trialDivisionResults_eq_true_iff` connects that fold exactly to primality for \(n\ge2\). `allFalseDivisibilityResultsComputableInPolyTime` fuses repeated divisibility with the fold, consumes the padded pair stream directly, and emits the exact no-divisor bit in at most \(18s+1\) steps; on `trialDivisionPairs n`, `allFalseDivisibilityResults_trialDivisionPairs_eq_true_iff` proves that bit is true exactly when \(n\) is prime for \(n\ge2\). `unaryCandidatePrimeComputableInPolyTime`, built with the pinned `lean-np-hardness` sequential-machine API, composes the pair generator with the fused pass and computes the candidate-only bit in at most \(64(n+1)^2\) steps on unary \(n\); `unaryCandidatePrime_eq_true_iff` gives exact primality semantics for \(n\ge2\). `two_le_of_mem_bertrandCandidates` checks the enumerator precondition, and `filter_unaryCandidatePrime_bertrandCandidates` proves the machine predicate induces exactly the guarded semantic prime filter. `primeSelectorComputableInPolyTime` consumes any checked unary candidate list and emits its first accepted source-order value in at most \(80(s+1)^3\) steps for complete encoded stream length \(s\); `primeSelector_selects_firstBertrandPrime` identifies its Bertrand-stream output with `firstBertrandPrime`, while `firstBertrandPrime_eq_selectPrimeAbove` identifies that value with the semantic compiler's selected prime, including \(q=0,1\). `selectedPrimeComputableInPolyTime` composes the unary Bertrand producer and selector and emits `selectPrimeAbove q` in at most \(1000(q+1)^6\) steps. `runtimeDomainEntryPrimeComputableInPolyTime`, using the pinned generic composition theorem, maps the checked compiler input to exactly `domainEntryPrime`. The header is verified redundancy rather than a supplied semantic assumption. The same input now also has checked header removal, raw traversal, and source-order normalization. `structuralBinaryHeaderComputableInPolyTime` now converts the computed unary row tally and stages the exact raw structural output in `8(s+1)^2` steps for the counted-payload length `s`. `runtimeCompilerStructuralViewComputableInPolyTime` now composes all structural passes and framing from the actual Boolean compiler input to exactly `RuntimeStructuralView.ofRuntimeSystem` under its original Boolean encoding, with an overall polynomial bound and the existing `32(s+1)^2` output-bit bound. `DomainSymbols.extract_toFinset` connects the structural occurrence symbols exactly to the semantic domain union; `rank_extract_eq_relabelValue` identifies executable list ranking with canonical semantic relabelling, with checked equality, prime-bound, and per-domain correspondence lemmas. `domainSymbolExtractionComputableInPolyTime` retains the exact occurrence wire and extracts its symbol fields in at most `3s+3` steps; `runtimeCompilerSymbolSectionsComputableInPolyTime` composes it from actual Boolean compiler input while preserving scopes and the variable count. The complete augmented tuple is bounded by twice the counted-section encoding length. `domainSymbolMembershipComputableInPolyTime` now decides membership from the checked serialized query/symbol pair in `6(s+1)^2` bit-level steps, reusing the upstream query-preserving equality kernel at dependency `ad20a2e`; loading and cleanup are included. `DomainSymbolMembership.rank_cons` now connects the computed membership bit to counting each smaller symbol once; `input_cons_length` and `tailMembership_outputsInTime` charge the complete query/tail wire exactly. `domainSymbolAlignmentComputableInPolyTime` now constructs aligned canonical comparison input from the complete tagged symbol/target pair in `4s+5` steps, including all loading, reversal, and cleanup, with output length at most `s`. `domainSymbolLessComputableInPolyTime` now composes that loader with the existing binary comparison kernel in `9s+10` steps, including transfer; `DomainSymbolComparison.rank_cons` identifies its exact strict-comparison bit with the rank recurrence, and `input_head_length` charges both words to the complete rank query. `rankQueriesComputableInPolyTime` now constructs both predicate queries and the next target/tail query from the checked nonempty rank wire in `3s+5` steps, including all copies and cleanup; its complete output length satisfies `output + 2 = 2s`. `rankPredicatesComputableInPolyTime` composes that preparation with both predicate machines through the upstream pair adapters, preserving the next query and charging all transfers. `RankPredicates.rank_step` identifies the exact rank contribution; `remaining_length_lt` proves strict wire-size decrease, and the complete result has at most `s+1` cells. The later rank loop uses these checked predicates; primal-edge deduplication, encoded objective emission, and composition with prime selection remain. `rankAccumulatorComputableInPolyTime` consumes both predicate bits, conditionally increments a unary count, and retains the complete remaining query in at most `2s` finite-machine steps for complete input length `s`. `rankIterationComputableInPolyTime` composes preparation, both predicates, and accumulation for the complete nonempty query/tally input with a checked polynomial bound. `RankIteration.rank_invariant`, `output_length_balance`, and `output_length_le` prove exact rank progress and nonexpansion of the entire retained state. `finish_one_eq_rank` and `finish_extracted_eq_relabelValue` identify its executable recursive specification with canonical relabelling, and `rankInitializationComputableInPolyTime` constructs its one-based starting state in `2s+2` steps while retaining the complete query. `rankControlComputableInPolyTime` tests nonemptiness while preserving the full state in `2s+2` steps, correctly distinguishing zero-valued fields; `rankEntryComputableInPolyTime` composes initialization and that test. `rankFinalizationComputableInPolyTime` returns the tally in `s+1` steps, with exact recursive-result semantics when the symbol list is empty. `RankLoopMachine.iteration_cycle` checks actual repeated-call control with exact `P(s)+2s+2t+4` cycle cost, and `exit_run` checks the empty exit. `RankLoop.outputsInTime` and `rankLoopComputableInPolyTime` prove total repeated computation in `(s+1)*(P(s)+4s+4)` steps for initial full-state length `s`. `canonicalRankComputableInPolyTime` composes initialization and returns the exact one-based rank from the original serialized target/symbol query; `canonicalRank_extracted_outputsInTime` identifies its result with the thesis relabelling. `occurrenceQueryComputableInPolyTime` now stages the next occurrence query in `3s+6` steps; `countedOccurrenceRankComputableInPolyTime` computes its exact unary rank while retaining the index, remaining occurrences, symbols, scopes, and variable count. `occurrenceEmitComputableInPolyTime` now converts a computed unary rank to the exact binary occurrence record while preserving remaining occurrences and symbols in `12(s+1)^2` steps, adding at most six cells. `countedOccurrenceStepComputableInPolyTime` composes query/rank/emission while retaining scopes/count; exact binary-field replacement, full output at most `2s`, strictly shrinking retained source, and rank bounds below the selected prime are checked. `occurrenceAccumulatorComputableInPolyTime` appends the emitted record in order in `2s+4` steps with no size increase. `occurrenceIterationComputableInPolyTime` composes ranking, binary emission, and accumulation; `OccurrenceIteration.iterate_length_le_quadratic` bounds every executable traversal state by `2(s+1)^2`, and its full-traversal correspondence and prime bounds are checked. `OccurrenceLoopMachine.iteration_cycle` now checks the finite dispatcher with cycle cost `P(s)+2s+2t+4`; `exit_run` returns accumulated records in `2s+2` steps with complete cleanup. `occurrenceLoopComputableInPolyTime` now proves the complete traversal in `(s+1)*(P(B)+4B+4)` steps, where `B=2(s+1)^2`, including every cycle and final exit. `occurrenceInitializationComputableInPolyTime` constructs the empty accumulator in `2s+2` steps; `runtimeCompilerRelabelledSectionsComputableInPolyTime` composes the whole traversal from actual Boolean compiler input while retaining scopes/count, with exact thesis-rank correspondence and prime bounds. Positive-row emission and final objective/prime assembly remain; the complete pair loop below now constructs deduplicated primal edges. `PrimalEdgeEnumeration.enumerate_eq_sorted_primalEdges` now checks an executable bounded pair scan against the exact sorted semantic edge list, with no duplicate output and at most `n^2` edges; its finite-machine runtime is supplied by the complete pair loop below. `negativeRowsComputableInPolyTime` reuses the scope machine to emit the exact raw negative residual-row section from checked endpoint pairs in `20(s+1)^2` steps. Its enumeration specialization agrees exactly with semantic `unequalRows` and has a cubic compiler-input bit-size bound; the complete pair loop below constructs those edges; the finite projection below composes negative-row emission; positive/full objective assembly remain open. `completeDomainVariableCountComputableInPolyTime` also derives and retains the unary variable count from original domain rows, including empty domains, reusing the checked quadratic row counter. `runtimeCompilerBoundedRelabelledSectionsComputableInPolyTime` carries this tally through complete relabelling with unchanged scopes; the candidate grid is quadratic in the resulting actual wire length for every intermediate value. `scopeQueriesComputableInPolyTime` constructs both serialized membership queries for one scope in `3s+3` steps, with at most double the input length. `scopeCooccurrenceComputableInPolyTime` composes both checked membership calls and finite conjunction into the exact same-scope predicate, including preparation and transfer costs. `scopeHeadComputableInPolyTime` now separates one counted scope from the exact remaining section in `20(s+1)^2` steps, reusing the checked source parser; the split preserves wire length and removes at least one cell from the remaining section. `scopePayloadComputableInPolyTime` reuses the pinned header-removal machine on one scope in `2s+1` steps. `scopeExtractionComputableInPolyTime` composes full extraction while retaining both endpoints and the exact tail, with checked size decrease and same-scope recurrence. `scopeRoutingComputableInPolyTime` now duplicates both endpoints and routes the exact head/tail in `3s+3` steps with output at most `2s`. `scopeTestComputableInPolyTime` composes extraction, routing and same-scope testing from the unsplit counted input while retaining both endpoints and all later scopes; the complete result does not grow. `scopeAccumulatorComputableInPolyTime` merges the old and tested answers in `2s+3` steps. `scopeIterationComputableInPolyTime` composes the complete iteration, with exact adjacency invariant, strictly shrinking wire size even for empty scopes, and semantic recursion agreeing with adjacency. `scopeLoopComputableInPolyTime` now supplies the finite repeated dispatcher and total runtime bound `(s+1) * (P(s)+4s+4)` in the full original state length; `scopeLoop_adjacent_outputsInTime` proves exact adjacency from a false initial accumulator, with every transfer and cleanup included. `scopeInitializationComputableInPolyTime` constructs the false accumulator in `2s+2` steps; `scopeAdjacencyComputableInPolyTime` composes complete adjacency testing from the bare serialized endpoints and counted scopes. `scopeAdjacency_query_length_le` and `scopeAdjacency_steps_le` bound each complete bounded-pair call by a polynomial evaluated at twice the retained intermediate length. `pairQueriesComputableInPolyTime` now constructs strict-order and full-scope adjacency queries while retaining endpoints, ranked domains, unary count, scopes and emitted pairs, in `4s+4` steps with at most `3s` output. `pairTestComputableInPolyTime` composes query construction, strict comparison, full adjacency and conjunction while preserving the whole state, adding exactly one answer cell. `PairTest.accept_ofRuntimeSystem` identifies the bounded-pair filter with the thesis primal graph; `state_length_le_cubic` and `pairTest_bounded_steps_le` bound full candidate calls conditionally on bounded counters and accumulated edges. `pairInitializationComputableInPolyTime` constructs zero endpoints and an empty edge accumulator in `2s+2` steps without changing wire length; `runtimeCompilerPairInitializationComputableInPolyTime` constructs this state from the actual compiler input. `PairAdvance.run_edges_eq` proves that the executable conditional-emission/counter loop returns exactly the ordered primal-edge list after `n^2` cycles; its invariant gives a cubic wire bound on every state and a uniform polynomial bound for complete predicate calls. `pairEmitComputableInPolyTime` now consumes the computed test bit and conditionally appends the exact counted edge row in `4s+5` finite-machine steps, retaining the complete scan state. `pairFilterComputableInPolyTime` composes the full computed candidate test with emission, with exact thesis primal-edge membership, cubic reached-state output bounds and a uniform polynomial call bound; `pairInnerCounterComputableInPolyTime` and `pairOuterCounterComputableInPolyTime` now implement the two binary counter actions, using checked successor/pair adapters and a `2s+2` reset pass; either adds at most one encoded cell. `pairInnerStepComputableInPolyTime` and `pairOuterStepComputableInPolyTime` compose the full computed filter/emitter with these counter actions; the selected branch agrees with `advance`, preserves the scan invariant and cubic wire bound, and the last outer call returns canonical exhaustion with the exact edge list. `pairBoundComputableInPolyTime` now computes the binary variable bound from the retained unary field while preserving the complete state, reusing the existing structural-header counting machine; preparation costs `3s+3`, unary counting costs `8(n+1)^2`, and the complete output is bounded by `2s+1`. `pairActiveComputableInPolyTime` and `pairContinuesComputableInPolyTime` now compute `i<n` and `j+1<n` from the complete original state, including bound conversion, successor, comparison, transfers and cleanup. Each adds one answer cell, preserves all state and has a uniform original-input polynomial bound; `PairControl.advance_eq` identifies the computed decisions with the scan recurrence and `run_active_iff` proves exact exhaustion after `n^2` cycles. `PairGateMachine.computableInPolyTime` now supplies a finite conditional-call wrapper, with an exact untouched skip path and checked body invocation including all transfers and cleanup. `PairDispatch.computableInPolyTime` now composes the actual control tests, complementary branch gates and checked answer erasure to implement exactly `PairAdvance.advance`, including unchanged exhausted states. `run_step_outputsInTime` supplies the exact next state and a uniform original-input polynomial bound for complete dispatched calls. `PairLoopMachine.iteration_cycle` and `exit_run` now check the finite repeated controller, complete body/transfer costs and exact terminal-state retention; `PairLoop.run_bounded` and `outputsInTime` now bound the complete repeated scan by `(s^2+1)*(P(B)+4B+4)` for `B=12(s+1)^3+1` in checked entry length `s`. `runtimeCompilerPairEnumerationComputableInPolyTime` composes seed construction, computed entry control and the whole loop from actual Boolean compiler input to canonical terminal counters, retained ranked sections and exactly the deduplicated primal-edge list. `runtimeCompilerNegativeSectionsComputableInPolyTime` now projects off the exhausted counters and composes negative-row emission from actual Boolean compiler input while retaining ranked sections. `GraphSections.negative_encode` proves exact semantic row correspondence, and `negative_length_le_cubic` bounds the whole paired output by `10(s+1)^3` in retained-section length. Positive rows and final objective/prime assembly remain open. `runtimeCompilerCountedGraphSectionsComputableInPolyTime` additionally computes the exact unary edge count while retaining all ranked sections and graph endpoints; `CountedGraphSections.count_eq` ties that count plus one to the semantic pinning weight. `runtimeCompilerWeightedNegativeSectionsComputableInPolyTime` now also constructs the exact binary pinning weight and retains it with the ranked sections and negative rows. `WeightedGraphSections.encode_eq` proves exact semantic row/weight correspondence, and `encode_length_le_cubic` bounds the complete raw output by `11(s+1)^3+2` in retained-section length. `PositiveEnumeration.rows_eq_pinningRows` now proves exact ordered positive-row correspondence for a bounded executable membership scan, with no duplicate pairs; `candidates_length_le_wire_quadratic` bounds the candidate grid by `s(s+1)` in retained-section bit length. A finite-machine implementation of this positive scan and final objective/prime composition remain open. `positiveBlockComputableInPolyTime` now emits one exact positive row in `2s+2` finite-machine steps. `PositiveRows.outputEncode_ofRuntimeSystem` proves exact complete raw positive-section correspondence, and `outputEncode_length_le_wire_quadratic` bounds this section by `11(s+1)^2` in weighted-section wire length. `runtimeCompilerCountedPositiveSectionsComputableInPolyTime` now computes the unary occurrence bound from actual Boolean input while retaining every ranked section, negative row and binary weight. `CountedPositiveSections.count_eq` gives its exact domain-entry meaning; `gridSize_le_wire_quadratic` bounds the candidate rectangle by full encoded length, and the whole tally-retaining pass at most doubles its input length. `positiveWeightPrepare_outputsInTime` now stages and retains the exact common binary weight in `3s+5` steps; `positiveRowWithWeightComputableInPolyTime` composes it with the local row emitter, with exact row correspondence, output length at most `2s+7`, and a uniform bounded-candidate call cost. `positiveMembershipExtractionComputableInPolyTime` now reuses the checked counted-row machine to expose one ordered occurrence while retaining the candidate and remaining records; exact length balance proves strict progress and the semantic recurrence requires both fields to match the same record. `positiveRoutingComputableInPolyTime` now constructs the ordered head query and retained continuation in `3s+3` steps, reusing the scope router. `positivePairMatchComputableInPolyTime` parses the two head fields, executes exact binary equality for each coordinate, and conjoins the answers; `PositivePairQuery.equal_eq_true` identifies precisely ordered-pair equality. `positiveTestComputableInPolyTime` now composes extraction, routing and same-record comparison from the contiguous counted occurrence wire. `positiveIterationComputableInPolyTime` also accumulates the result with OR while preserving the candidate and exact tail; its exact size balance removes both head words plus six cells. `PositiveIteration.contains_invariant` and `finish_false_eq_contains` prove the executable recurrence. `positiveLoopComputableInPolyTime` now checks the repeated finite dispatcher with bound `(s+1)*(P(s)+4s+4)`, including all transfers and final cleanup. It shares `RecordLoopMachine` with the existing scope loop. `positiveMembershipComputableInPolyTime` now includes false-bit initialization from the original serialized query. `PositiveInitialization.result_ofRuntimeSystem` proves exact relabelled-domain acceptance, and `positiveMembership_steps_le` gives a uniform retained-section polynomial bound. `positiveCandidateQueriesComputableInPolyTime` now constructs the exact membership query and retains the full positive-scan state in `3s+3` finite-machine steps, with output at most `2s`. `positiveCandidateTestComputableInPolyTime` now composes query construction and complete membership testing while retaining all state, with exact relabelled-domain acceptance and one extra output cell. `PositiveCandidateTest.state_length_le_cubic` and `positiveCandidateTest_bounded_steps_le` bound complete calls including accumulated common-weight rows. `positiveCandidateEmitComputableInPolyTime` conditionally appends the exact counted pinning row in `6s+7` steps while retaining the complete state and binary weight; its whole output is at most `2s+8`. `positiveCandidateFilterComputableInPolyTime` composes complete testing and emission with exact relabelled-domain semantics, bounded-row/capacity/freshness preservation and a uniform polynomial call bound. `PositiveAdvance.run_ofRuntimeSystem` now proves that the executable rectangular traversal emits exactly the ordered semantic pinning rows. Its reached-state invariant proves freshness, capacity, uniqueness and the cubic bit bound; `run_filter_steps_le` bounds all complete finite filter calls. `positiveInnerStepComputableInPolyTime` and `positiveOuterStepComputableInPolyTime` now provide complete finite filter-and-counter continuations, with uniform original-section polynomial call bounds. `positiveScanInitializationComputableInPolyTime` now constructs the exact invariant-bearing seed in `2s+2` steps without increasing bit length; `runtimeCompilerPositiveScanInitializationComputableInPolyTime` composes it from actual compiler input. `positiveBoundComputableInPolyTime` computes either bound internally; `positiveActiveComputableInPolyTime` and `positiveContinuesComputableInPolyTime` decide the exact rectangular conditions, preserve all state and have uniform original-section polynomial call bounds. `PositiveDispatch.computableInPolyTime` now implements the complete conditional finite step, reusing generalized gate/decision-erasure machines; exact next-state calls have uniform original-section polynomial bounds. `runtimeCompilerPositiveEnumerationComputableInPolyTime` now constructs the complete positive scan from actual Boolean compiler input, sharing `FlaggedLoopMachine` with the pair scan; the rectangular total runtime includes every body call, transfer and final exit. `PositiveScanLoop.result_ofRuntimeSystem` and `result_outputEncode_ofRuntimeSystem` identify the exact ordered semantic pinning rows. `runtimeCompilerObjectiveRowsComputableInPolyTime` now assembles the exact complete positive-then-negative residual rows and retained unary variable count from actual Boolean input. `ObjectiveRows.assemble_result` proves exact semantic compiler correspondence; the finite assembly takes at most `2s+4` steps without increasing wire length. Header construction, final framing and selected-prime composition remain open. |
| `cor:signed-nphard` | Complete | `FixedPrimeHardness.fixed_prime_signed_decision_is_three_sat_hard_in_cell_model` proves the explicit \(p=5\) reduction, correctness, output size, and a quadratic unit-cell construction bound; `CNFNormalisation.general_compileFixedPrime_correct` and `fixed_prime_signed_decision_is_general_three_sat_hard_in_cell_model` extend it to arbitrary 3-CNF syntax with a `392 · size²` cell bound. The library-native transfer is checked: `PadicRegressionLanguage.SignedRegressionLang` states the signed threshold problem (signed rows, natural bound, unary and binary encodings); `SignedThreeSatReduction.signed_iff` proves, for every prime `p > 3` and every formula of exact width three, that the streaming variant (one negative clause-reward row per clause, one forcing pair per literal occurrence, bound `2m`) preserves satisfiability; `SignedThreeSatMachine.sgR_exits`/`cost_le` give an exact two-pass TM2 run within `10⁶(n+1)²` steps; and `satReduction` composes it with the library's chain reduction, so `encodedUnarySignedRegression_NPHard`, `encodedSignedRegression_NPHard` and `signed_nphard_five` follow from the library's Cook–Levin theorem. |
| `cor:sudoku-polynomial-dyadic-hardness` | Complete | `PolynomialResidualHardness.dyadic_no_tractability_transfer` and `dyadic_compilePolynomial_correct` prove the positive polynomial-residual reduction at `p = 2` (and `polynomial_residual_hardness`, `compilePolynomial_correct` at every prime): the unit-weight objective with `α = 1 + Δ` has global minimisers on `ℤ_2^n`, all of them Boolean (`globalMinOnBall_boolean`), its minimum is `α n` iff the 3-CNF formula is satisfiable, any exact optimiser decides satisfiability, every clause residual is an `MvPolynomial` of total degree `≤ 3` and degree `≤ 1` in each variable, and the instance has `2n + m` rows. The complexity statement is checked: `PolynomialResidualLanguage.PolyRegressionLangML` states the problem over `ℤ_p` with residuals given as products of affine factors and restricted to `MultilinearDeg3` residuals (at most three factors on pairwise disjoint coordinates); `PolynomialResidualReduction.poly_iff` proves for every prime and every formula of exact width three that a per-occurrence variant (an occurrence coordinate carrying each literal's failure value, an affine linking residual, the clause product `y_k y_{k+1} y_{k+2}` on distinct coordinates, forcing pairs per occurrence, bound `9m`) preserves satisfiability, with `multilinear_polyReduce` checking the restriction; `PolynomialResidualMachine` computes it with the two-pass machine of `TwoPassMachine`; and `encodedUnaryPolyML_NPHard`, `encodedPolyML_NPHard` and `dyadic_poly_nphard` follow from the library's chain reduction and Cook–Levin theorem. |
| `cor:sudoku-special-case` | Complete | `SudokuSpecialCase.sudoku_special_case`: on the 81-cell deduplicated peer graph (`PeerEdge`, 810 edges, `degree_eq_twenty` by kernel `decide`), with clue singletons and `{1,…,9}` domains for `p > 9` and `α > 20`, the minimal objective (`sudokuLoss_eq` unfolds it to the displayed form) has a global minimiser, its global minimisers are exactly the clue-respecting digit assignments minimising the peer-conflict count, and when the puzzle is satisfiable they are exactly the valid completions (`validCompletion_iff_isProper`). `digit_difference_norm` is `cor:sudoku-differences`; `unit_complete` records that every row, column and box of a valid completion contains every digit once. |

For the partial `cor:all-different-csp` runtime path,
`AllDifferentCSPSourceSections.lean` splits the complete runtime
source into the existing checked pair of domain and scope encodings.
`SourceSectionMachine.computer` uses six stacks with separate binary row and
entry countdowns. It removes the outer count and singleton header length,
retains the domain count, copies exactly the declared domain rows, and tags
the remaining scope payload separately. The exact execution proof clears all
non-output stacks and handles empty sections, empty rows, repeated entries,
and arbitrary natural values through their encoded bit lengths.
`sourceSections_outputsInTime` and `sourceSectionsComputableInPolyTime` give
an explicit `40 * (s+1)^2` bound for the full raw input length `s`;
`RuntimeSourceSections.output_length_le_input` proves the complete paired
output is no longer than the input.
`runtimeCompilerSectionsComputableInPolyTime` starts from the actual checked
Boolean compiler input and constructs both sections internally.

The dependency is now pinned to `lean-np-hardness` commit
`ad20a2e92ec5eb85379ac31df255671416f83b3d`. Its checked generic pair-left
machine supplies `pairedDomainSectionComputableInPolyTime`, which expands
domains while preserving every scope. The composed
`runtimeCompilerDomainAndScopesComputableInPolyTime` maps the actual compiler
input to exactly `(indexedDomainOccurrences C.domains, C.scopes)` under the
existing tagged pair encoding.
The generic codec, arithmetic, framing, counted-row, Boolean-fold and
unary-prime machine implementations have moved to `lean-np-hardness`;
compatibility exports retain the old thesis-facing names.
`AllDifferentCSPProcessedSections.lean` now also composes scope processing
within that pair: `LeanNPHardness.PairExchange.outputsInTime` checks each canonical
section exchange in at most `4s+6` steps for full paired wire length `s`;
`pairedScopeSectionComputableInPolyTime` specializes the dependency
`MachineAdapters.pairRightComputableInPolyTime` while preserving domain output.
`runtimeCompilerProcessedSectionsComputableInPolyTime` constructs both exact
tagged sections from the actual Boolean compiler input, with a checked
polynomial bound. `AllDifferentCSPVariableHeader.lean` now preserves the
variable count before expansion: `variableHeader_outputsInTime` and
`variableHeaderComputableInPolyTime` copy the third checked source field in
at most `3s+6` steps while retaining the complete source. The paired output is
at most `2s` cells, and `runtimeCompilerVariableHeaderComputableInPolyTime`
constructs it from the actual Boolean compiler input. This includes zero
variables and trailing empty domains. `AllDifferentCSPCountedSections.lean`
now carries that count through the source split and both section passes using
the checked generic pair-left API.
`runtimeCompilerCountedSectionsComputableInPolyTime` constructs the exact
occurrence/scope/count tuple from the actual Boolean compiler input with a
checked polynomial bound. `CountedSections.toStructuralView_ofRuntimeSystem`
proves that tuple reconstructs exactly the intended structural view;
`recordCount_le_encode_length` bounds its record count by the actual tuple
encoding length, and `raw_encode_eq_sections` gives the exact assembly and
reversal contract. `AllDifferentCSPStructuralAssembly.lean` now checks the
complete variable-header/record payload through exhaustion, reusing the
upstream counted-row decoder and existing structural tag parser.
`payloadDecode_encode` proves exact recovery; the complete merged wire has
exactly three more cells than the counted-section tuple.
`payloadEncode_length_le_encodedSize` bounds this payload by the existing framed
encoding; `payloadEncode_ofRuntimeSystem_length_le_compilerInput_quadratic`
therefore retains the `32 * (s+1)^2` bound in actual Boolean compiler input
length `s`. `rowCount_le_payloadEncode_length` bounds the required outer row
count, including its singleton header, by the payload's actual length.
`AllDifferentCSPAssemblyMachine.lean` realizes that merge in at most `2s+3`
steps using four finite stacks, clearing every non-output stack at halt.
`runtimeCompilerStructuralPayloadComputableInPolyTime` composes from the
actual Boolean compiler input to exactly `RuntimeStructuralView.ofRuntimeSystem`
under `RuntimeStructuralView.payloadFinEncoding`, with a polynomial bound.
The local `2s+3` bound is only for the final assembly pass. Empty scopes,
repetitions, zero variables, and trailing empty domains are retained.
`raw_encode_eq_count_payload` identifies the original-format bridge:
prepend the outer row count, then reverse and frame the complete stream.
`AllDifferentCSPRowCount.lean` now computes the count in unary while retaining
every payload cell. `structuralRowCount_outputsInTime` and
`structuralRowCountComputableInPolyTime` traverse the binary row lengths with
explicit predecessor loops, emitting one tally mark for each complete row.
Their exact output is `(view, view.records.length + 1)` in the standard tagged
pair encoding, in at most `20 * (s+1)^2` steps for actual payload length `s`.
The singleton variable header, empty scopes, and repetitions are counted;
all non-output stacks are empty at halt.
`runtimeCompilerStructuralCountedPayloadComputableInPolyTime` now composes this
pass from the actual Boolean compiler input, producing exactly the view and
`C.domainEntryCount + C.scopes.length + 1` with a checked polynomial bound.
`StructuralCountedPayload.encode_retain_length` gives the exact paired length;
`encode_retain_length_le` bounds it by twice the payload length, and
`encode_retain_ofRuntimeSystem_length_le_compilerInput_quadratic` bounds the
complete output by `64 * (s+1)^2` in actual Boolean input length `s`.
`AllDifferentCSPBinaryHeader.lean` now supplies the checked redundant-count
codec `StructuralCountedPayload.checkedFinEncoding` and the concrete
`StructuralBinaryHeaderMachine.computer`. `structuralBinaryHeader_outputsInTime`
and `structuralBinaryHeaderComputableInPolyTime` increment a binary counter
once per tally mark, insert the outer count, and reverse into exactly
`RuntimeStructuralView.rawFinEncoding`, preserving every payload cell.
The bound is `8 * (s+1)^2` finite-machine steps in the complete counted-payload
wire length `s`, with all non-output stacks empty at halt. The internal proof
includes zero tallies and arbitrary carry growth. The existing counter is
repackaged as `structuralRowCountCheckedComputableInPolyTime` under the checked
redundant codec. `AllDifferentCSPStructuralCompiler.lean` now composes the
complete structural path. `structuralRawComputableInPolyTime` connects row
counting to binary-header staging;
`runtimeCompilerStructuralRawComputableInPolyTime` constructs that exact raw
view from the actual Boolean compiler input.
`runtimeCompilerStructuralViewComputableInPolyTime` adds the existing framing
machine and emits exactly `RuntimeStructuralView.ofRuntimeSystem` under the
original Boolean `FinEncoding`, with every header and intermediate stream
computed internally. Its polynomial bound covers all passes and intermediate
transfers. The existing `32 * (s+1)^2` output-size bound is now the bound for
this actual Boolean output, measured against the complete Boolean compiler
input length `s`. The local header bound is not the full composition bound.
The later canonical relabelling stage is now complete. Finite-machine edge
construction, positive-row emission and complete objective/prime assembly
remain; the developments below check the ordered edge specification and
negative-row emitter.
`AllDifferentCSPSymbols.lean` specifies executable occurrence extraction and
canonical rank computation on lists. `DomainSymbols.extract_toFinset` proves
that the extracted symbols have exactly `ExplicitSystem.domainValues` as
their set, including repeated values within and between domains.
`rank_extract_eq_relabelValue` identifies the list rank (deduplicate the
smaller values, count them, and add one) with the semantic compiler's rank.
`rank_eq_iff`, `rank_lt_domainEntryPrime`, and `relabeled_domain` connect it
to equality preservation, the selected prime, and each exact relabeled domain.
These semantic contracts connect to the complete local rank machine described
below. Its composition across retained compiler sections remains outstanding.
`AllDifferentCSPSymbolMachine.lean` now implements the extraction step.
`domainSymbolExtractionComputableInPolyTime` retains the exact occurrence
wire and extracts every symbol field in source order in at most `3s+3`
finite-machine steps for occurrence-wire length `s`. Its four field phases
use only finite control; zeros, repetitions, and empty occurrence lists are
covered, and every non-output stack is empty at halt.
`runtimeCompilerSymbolSectionsComputableInPolyTime` uses the pinned generic
pair-left and sequential composition APIs to start from the actual Boolean
compiler input and construct the symbol list while preserving all indexed
occurrences, scopes, and the original variable count. Its overall polynomial
bound includes preprocessing and transfer costs; `3s+3` is only the local
extraction bound. `CountedSymbolSections.toStructuralView_ofRuntimeSystem`
proves exact reconstruction, `rank_symbols_eq_relabelValue` connects the
machine-produced list to the semantic rank, and `retain_encode_length_le`
bounds the complete augmented tuple by twice the counted-section wire length.
`AllDifferentCSPSymbolMembership.lean` now supplies the serialized membership
pass. `domainSymbolMembershipComputableInPolyTime` takes a checked pair of a
canonical binary query and source-order symbol fields and returns exactly
whether the query occurs, in at most `6 * (s+1)^2` steps for complete tagged
input length `s`. It loads every candidate internally, reuses the upstream
query-preserving equality kernel, and counts loading, comparison, restoration,
and final cleanup. Empty lists, zero, repeated symbols, and unequal bit
lengths are covered; every non-output stack is empty at halt. Both loaded
words are reversed, which preserves equality and avoids a separate reversal
pass. This local membership machine is reused inside the complete rank driver
below; composition from the complete compiler input remains open.
`AllDifferentCSPSymbolRankStep.lean` connects that machine result to the next
loop. `DomainSymbolMembership.contains_extracted` identifies membership with
the semantic union of domains; `dedup_cons` uses the returned bit to skip
repeated symbols, and `rank_cons` counts a smaller symbol only at its final
source-order occurrence. `input_cons_length` proves that taking the head as
the query removes exactly one field delimiter from the original stream.
`tailMembership_outputsInTime` therefore bounds this local query by six times
the square of that stream's length. `dedup_fields_length_le` proves that
removing duplicates cannot increase the raw binary field length. These are
checked recurrence and size contracts used by the complete rank loop below.
`AllDifferentCSPSymbolComparison.lean` now constructs the aligned binary
input needed by the rank loop's comparison. Its seven-stack loader reads the
checked tagged symbol/target pair, restores each word's original bit order,
aligns corresponding bit positions with explicit padding on the exhausted
side, and restores the complete output order. `domainSymbolAlignment_outputsInTime`
and `domainSymbolAlignmentComputableInPolyTime` give a `4s+5` bound in the
complete serialized pair length; `domainSymbolAlignment_output_length_le`
proves that alignment does not enlarge that wire. Empty words (zero), unequal
bit lengths, and cleanup of every work stack are included. This constructs
comparison input from the complete serialized pair.
`alignedSymbolLessComputableInPolyTime` reuses the upstream less-or-equal
kernel with explicit alphabet recodings that swap the aligned components and
complement the result. `domainSymbolLessComputableInPolyTime` composes that
kernel with the loader and proves an explicit `9s+10` bound, including the
complete intermediate transfer. Its encoded Boolean is exactly `symbol < target`.
`DomainSymbolComparison.rank_cons` connects that computed bit and the checked
membership bit to the existing rank recurrence. `input_head_length` charges
both comparison words and the remaining fields to the complete target/symbol
query; `input_length_le_rank_query` gives the corresponding comparison-size
bound. `AllDifferentCSPRankQueries.lean` now constructs all three queries from
the original target/nonempty-symbol-list wire: `(symbol, tail)` for membership,
`(symbol, target)` for comparison, and `(target, tail)` for the next iteration.
Its decoder checks nonemptiness without adding a header or assuming a pre-split
input. `rankQueries_outputsInTime` and `rankQueriesComputableInPolyTime` prove
a `3s+5` bound for the eight-stack preparation pass in complete input length
`s`, including every copy, ordering pass, and cleanup. Zero symbols, empty
tails, repeated values, and arbitrary binary magnitudes are included.
`RankQueries.output_length` proves the exact output equation `output + 2 = 2s`.
`AllDifferentCSPRankPredicates.lean` now calls both predicates while preserving
that next query. `rankPredicatesComputableInPolyTime` composes preparation,
query membership, and strict comparison with the checked upstream pair-left
and pair-right adapters. Its result is exactly
`(symbol ∈ tail, (symbol < target, (target, tail)))`, with Boolean predicates
and all copying, transfers, and reassembly included in the polynomial bound.
`RankPredicates.rank_step` connects those exact outputs to canonical rank:
add one only when the symbol is smaller than the target and absent from the
tail. `remaining_length` proves that the retained input loses precisely the
head's bit length plus its delimiter; `remaining_length_lt` includes zero
heads. The complete predicate output is at most `s+1` cells.
`AllDifferentCSPRankAccumulator.lean` adds the concrete three-stack conditional
accumulator machine. It consumes the two predicate bits, retains the exact
remaining query, and adds one unary tally mark exactly when the symbol is
smaller and absent from its tail. `rankAccumulator_outputsInTime` and
`rankAccumulatorComputableInPolyTime` bound this complete update by `2s`
finite-machine steps in the full predicate/query/accumulator wire length.
Every copy and order-restoration pass is charged, all work stacks are empty
at halt, and zero accumulators and empty remaining symbol lists are included.
`rankIterationComputableInPolyTime` now composes query preparation, both
predicates, and this accumulator update from the original nonempty query and
its unary tally. It reuses the pinned generic pair-left and sequential-machine
APIs, charging all intermediate copies and transfers to the complete input.
`RankIteration.rank_invariant` preserves the tally plus the remaining canonical
rank. `output_length_balance` charges the consumed head's binary length and
its delimiter against the optional tally cell; `output_length_le` proves the
complete retained state never grows. Exactly one symbol disappears even when
the complete wire length stays constant (a counted zero-valued symbol).
`RankIteration.finish` is an executable recursive specification with an
empty-list branch; `finish_one_eq_rank` and `finish_extracted_eq_relabelValue`
prove its exact canonical-rank and thesis-relabelling semantics. Its tally is
bounded by the initial tally plus the number of explicit occurrences, not by
symbol magnitudes. `AllDifferentCSPRankInitialization.lean` now constructs
the initial state from the complete target/symbol query. Its
`rankInitializationComputableInPolyTime` appends the unary tally one while
preserving every query cell in `2s+2` finite-machine steps, with exactly one
additional output cell. The empty query (zero target, empty symbol list) is
included. `RankInitialization.finish_initialize` connects this starting state
to the semantic one-based rank. `AllDifferentCSPRankControl.lean` now checks
whether symbols remain while retaining the complete query and tally.
`rankControlComputableInPolyTime` emits that bit and the unchanged state in
`2s+2` steps, with exactly one added output cell. `source_present` proves that
a zero symbol's delimiter still selects the nonempty branch, and
`RankControl.nonempty_encode` identifies that branch's retained wire exactly
with the existing iteration input. `rankEntryComputableInPolyTime` composes
initialization and testing from the original query, including transfers.
`AllDifferentCSPRankFinalization.lean` supplies
`rankFinalizationComputableInPolyTime`, returning the unary tally and clearing
the query in `s+1` steps without increasing output length.
`result_eq_finish_of_empty` identifies that tally with the recursive result
only when the checked nonempty-list bit is false.
`AllDifferentCSPRankLoopMachine.lean` now supplies the finite loop controller.
`RankLoopMachine.iteration_cycle` scans a nonempty state, loads and runs the
existing checked iteration, restores its output in order, and returns to the
next scan with all body and scratch stacks empty. Its complete cycle cost is
`P(s) + 2s + 2t + 4`, where `P` is the checked iteration polynomial and `s`,
`t` are the complete input and output wire lengths. `exit_run` checks the
empty branch in `2s+2` steps, including target disposal and tally output.
The driver fuses the existing source-field test with its loading scan and
uses the same checked zero-field criterion. `AllDifferentCSPRankLoop.lean` proves the complete repeated execution.
`RankLoop.run_bounded` uses strict source-list decrease and nonexpanding full
state to bound every cycle by the same input size; `RankLoop.outputsInTime`
proves a total bound of `(s+1) * (P(s) + 4s + 4)` for the complete state length
`s`, including all control, loading, return transfers, and the final exit.
`rankLoopComputableInPolyTime` packages this finite machine under the checked
state and unary-result encodings. `canonicalRankComputableInPolyTime` composes
it with initialization from the original serialized target/symbol query and
returns the exact one-based rank. Its full polynomial also charges that
initialization and intermediate transfer. `canonicalRank_extracted_outputsInTime`
identifies the machine output with `ExplicitSystem.relabelValue` on extracted
domain symbols. Empty lists, zero values, repetitions, arbitrary binary
magnitudes, and cleanup of all work stacks are covered. This completes the
local rank machine. The following step stages its query from the retained
compiler sections and computes the rank of their next occurrence.

`AllDifferentCSPOccurrenceQuery.lean` now constructs the next rank query from
the existing occurrence/symbol wire, whose decoder checks that an occurrence
is present. `occurrenceQueryComputableInPolyTime` removes that head record,
pairs its value with the complete symbol list, and retains its variable index,
the exact remaining occurrence stream, and a second copy of the complete
symbol list in at most `3s+6` finite-machine steps. The bound uses the full
input wire length and includes copying, order restoration, and cleanup.
`OccurrenceQuery.output_length` proves `output + 6 = input + symbols`;
`output_length_le` consequently bounds the complete result by twice its input.
Zero indices/values, empty tails, repeated symbols, and arbitrary binary
magnitudes are covered.
`AllDifferentCSPOccurrenceRank.lean` composes that preparation with the complete
rank machine. `occurrenceRankComputableInPolyTime` returns the exact unary rank
while preserving the index, remaining records, and full symbol list.
`countedOccurrenceRankComputableInPolyTime` carries the complete scopes and
original variable count through the same step using the pinned pair-left API.
`CountedOccurrenceRank.input_encode_eq_source` proves its input is exactly the
existing nonempty counted-symbol-section wire; no preassembled query is assumed.
`step_eq_relabelValue` identifies the emitted index/rank pair with the thesis
compiler's canonical relabelling when the source is compiler-produced.
`remaining_step` and `remaining_length` preserve all remaining data and remove
exactly one occurrence. `remaining_encoded_length_balance` proves that the next
source loses the head's index/value bits plus six record-format cells, so its
encoded length strictly decreases even for zeros. The complete output,
including the unary rank, is at most twice the input length.
All adapter and transfer costs are included in the composed polynomial.
`AllDifferentCSPOccurrenceEmit.lean` now converts that unary rank and emits the
exact canonical binary `[3,0,index,rank]` record while preserving the remaining
occurrences and complete symbol list. `occurrenceEmitComputableInPolyTime`
proves `12(s+1)^2` steps in the complete ranked-input wire length, including
carry propagation, order restoration, source copying, and stack cleanup.
`OccurrenceEmit.output_length` accounts for exactly six record-format cells;
`output_length_le` bounds the result by the input length plus six. Zero ranks
and indices, empty retained sources, and binary carry growth are included.
`AllDifferentCSPOccurrenceStep.lean` composes query staging, canonical ranking,
and binary emission as `occurrenceStepComputableInPolyTime`.
`countedOccurrenceStepComputableInPolyTime` carries scopes and the original
variable count through that complete step on the existing nonempty counted
section wire. The composed polynomial includes every adapter and transfer;
`12(s+1)^2` is the emitter's bound alone. `output_length_balance` proves that
the only wire-size change is replacing the old value's binary word by the
rank's binary word, and `output_length_le` bounds the complete result by `2s`.
`output_length_eq_record_add_remaining` separates the emitted record from the
remaining source with no extra cells. The remaining source strictly shrinks;
its full symbol list survives, and `record_eq_relabelValue_of_symbols` supplies
the canonical-rank invariant for later suffixes as well as the initial input.
`record_encode_eq` identifies the exact thesis record, and `record_rank_bounds`
proves each actual emitted rank is positive and below `domainEntryPrime`.
`AllDifferentCSPOccurrenceAccumulator.lean` adds the ordered-output update.
`occurrenceAccumulatorComputableInPolyTime` appends the newly emitted binary
record after all prior records while retaining the complete next source, in
`2s+4` steps for the full input wire. The five-stack finite machine charges
each routed cell and each order-restoration pass, clears every work stack,
and handles empty prior output and zero-valued fields. `output_length` proves
that this update adds no cells.
`AllDifferentCSPOccurrenceIteration.lean` composes rank, binary emission, and
ordered append as `occurrenceIterationComputableInPolyTime`, carrying all
prior output through the checked pair adapter and charging its transfers.
`step_length_balance` replaces only the old value bits by rank bits.
`step_budget_le` reserves space for every remaining rank and proves that this
full-state budget never increases. `iterate_length_le_quadratic` bounds every
executable traversal state, including accumulated records, by `2(s+1)^2` in
the original complete wire length; `finish_encoded_length_le_quadratic` gives
the same bound for all final emitted records from an empty accumulator.
`finish_eq_append_map` and `iterate_eq_finish` prove exact ordered traversal
and exhaustion after one step per source occurrence. The compiler-specific
`finish_extracted_eq_relabelValue` and `finish_rank_bounds` identify every
final index/rank with the thesis relabelling and place each rank strictly
between zero and `domainEntryPrime`. Duplicate and zero-valued occurrences
survive; empty input preserves any prior output.
`AllDifferentCSPOccurrenceLoopMachine.lean` now supplies the finite dispatcher.
`source_present` detects remaining occurrence cells, including zero fields;
`body_run` embeds the complete checked body and redirects its halt to the
return transfer. `iteration_cycle` charges `P(s)+2s+2t+4` steps for a cycle
with input/output lengths `s,t` and body polynomial `P`. `exit_run` scans the
exhausted state and returns the accumulated records in `2s+2` steps, discarding
the retained symbols and clearing every work stack.
`AllDifferentCSPOccurrenceLoop.lean` completes the repeated runtime proof.
`OccurrenceLoop.run_bounded` carries the decreasing budget through induction
on remaining occurrences, and `occurrenceLoopComputableInPolyTime` returns
exactly the prior output followed by the ordered canonical-rank records.
With initial bit length `s`, `B=2(s+1)^2` bounds every intermediate state and
the complete machine takes at most `(s+1)*(P(B)+4B+4)` steps. This includes
all body calls, dispatch scans, transfers and the final empty exit.
`AllDifferentCSPOccurrenceInitialization.lean` constructs the empty-accumulator
state in `2s+2` steps, preserving the input wire length. The composed
`occurrenceRelabellingComputableInPolyTime` starts at the existing
occurrence/symbol encoding without requiring any preconstructed loop state.
`AllDifferentCSPRelabelling.lean` then retains scopes and the original variable
count through the checked pair adapter. Its headline
`runtimeCompilerRelabelledSectionsComputableInPolyTime` starts at the actual
Boolean `RuntimeCompilerInput.finEncoding` and returns the exact existing
`CountedSections.finEncoding` with all domain values replaced by thesis ranks.
`CountedRelabelledSections.domains_ofRuntimeSystem` proves that correspondence;
scopes, occurrence order, repetitions, and variable count are preserved, and
`rank_bounds` puts every output rank strictly between zero and the selected
domain-entry prime. The complete composed runtime includes source preparation,
symbol extraction, initialization, the whole loop and both retained-section
adapters; the displayed loop polynomial alone is not the whole compiler cost.
The pair-loop composition below now constructs deduplicated primal edges.
Positive-row emission and final objective/prime assembly remain open;
the full corollary is still **Partial**.

`AllDifferentCSPPrimalEdges.lean` now defines an executable bounded pair scan
from the retained variable count and scope lists. `PrimalEdgeEnumeration.enumerate`
emits increasing endpoints in strict lexicographic order, so scope repetitions,
shared edges and repeated entries cannot duplicate an edge. The theorem
`enumerate_eq_sorted_primalEdges` identifies the exact ordered list with the
semantic compiler's sorted primal graph, including its treatment of out-of-range
scope entries. `enumerate_relabelledSections` connects the scan input to the
completed relabelling stage. `enumerate_length_le` bounds the list by `n^2`
for `n` explicitly listed variables. These executable semantics and size
results are realized by the complete finite pair loop below, with a checked
polynomial runtime from actual compiler input. Positive-row emission and final
objective/prime composition remain separate.

`AllDifferentCSPNegativeRows.lean` adds checked endpoint-pair and negative-row
section encodings by reusing the counted-row codecs. Its
`negativeRowsComputableInPolyTime` reuses the complete scope-tagging machine:
`[2,i,j]` becomes the exact raw negative residual row `[3,1,i,j]` in at most
`20(s+1)^2` steps for the supplied edge-stream wire length `s`. Decoders check
pair arity, tags and row exhaustion. `NegativeRows.rows_enumerate_eq` and
`outputEncode_enumerate_eq` give exact agreement with the semantic compiler's
ordered negative rows; `pinningWeight_eq_edgeCount` also connects edge counting
to its positive pinning weight. `outputEncode_length` charges exactly two added
cells per edge. `compiler_output_length_le_cubic` bounds the whole negative
section by `9(s+1)^3` in the actual Boolean compiler-input length. The finite
emitter starts with an already enumerated edge list. The pair loop and
projection below now construct that list and compose this emitter from actual
compiler input. Positive rows, full objective assembly and prime composition
remain.
`AllDifferentCSPRowCount.lean` now reuses the existing row-counting machine
on the original domain rows. `domainVariableCountComputableInPolyTime`
retains every domain cell and constructs the exact unary variable count in
`20(s+1)^2` steps for payload length `s`, including empty domains.
`completeDomainVariableCountComputableInPolyTime` includes removal of the
checked outer count. `DomainCountedPayload.encode_retain_length_le` bounds
the complete retained payload and tally by `2s`.
`AllDifferentCSPBoundedSections.lean` carries that computed tally and every raw
scope through the complete domain-relabelling path using existing pair
adapters. Its headline
`runtimeCompilerBoundedRelabelledSectionsComputableInPolyTime` starts at the
actual Boolean compiler input and produces exact thesis-ranked occurrences,
the unary variable count, and unchanged scopes. `toCountedSections_ofRuntimeSystem`
identifies the result with the established relabelling semantics.
`variableCount_le_encode_length` holds for every value of this checked
intermediate encoding, so `candidates_length_le_square` bounds the complete
pair grid by its actual input length squared. `negativeRows_length_le_cubic`
also bounds the negative-row target in this intermediate length. These size
lemmas prepare the missing finite pair scanner; they do not assert its runtime.
Empty domains, an empty occurrence stream, and zero variables are covered.

`AllDifferentCSPScopeQueries.lean` now constructs both endpoint-membership
queries for one scope from a checked serialized endpoint-pair/scope input.
`scopeQueriesComputableInPolyTime` proves the finite routing machine takes at
most `3s+3` steps in the complete input length, including copying every scope
cell twice, restoring both query orders and clearing all scratch stacks.
`ScopeQueries.output_length` charges exactly one additional copy of the scope;
`output_length_le` bounds the entire paired output by `2s`.
`AllDifferentCSPScopeCooccurrence.lean` composes this preparation with both
existing serialized membership calls, the checked pair adapters, and a fixed
finite conjunction of their two result cells.
`scopeCooccurrenceComputableInPolyTime` supplies a genuine finite-machine
polynomial bound for the complete one-scope predicate; copying, transfers and
cleanup are included. `scopeCooccurrence_correct` identifies its answer with
the singleton-scope predicate in the exact primal-edge enumeration.
`ScopeCooccurrence.adjacent_cons` specifies the outer OR of these same-scope
answers, and `query_length_le` bounds each bounded-pair/scope query by twice the
full retained intermediate wire length. `scopeCooccurrence_steps_le` then
bounds the actual composed predicate steps by its polynomial evaluated at `2s`.
The pair scan still supplies the separate `i < j` condition. Checked examples
distinguish endpoints in different scopes from a pair occurring in one scope, including
zero, repeated entries and empty scopes.

`ScopeHead.inputFinEncoding` now checks a nonempty contiguous scope section,
without requiring an externally supplied split. `scopeHeadComputableInPolyTime`
reuses the existing source parser at its first-row entry point to separate the
first counted scope from the exact remaining section in at most `20(s+1)^2`
steps. Every work stack is clear at halt. `ScopeHead.output_length` proves
that the split changes only alphabet tags, and `tail_length_lt` proves strict
progress even when the removed scope is empty. Removing the isolated scope's
count and retaining both endpoints now compose as described below.

`AllDifferentCSPScopePayload.lean` reuses the pinned counted-row header-removal
machine with a new proof for one scope's arbitrary entry fields.
`scopePayloadComputableInPolyTime` removes only that scope's count in at most
`2s+1` steps, including empty scopes and complete cleanup.
`AllDifferentCSPScopeExtraction.lean` composes the split and header removal,
then uses the pinned pair adapters to retain both binary endpoints and every
later scope. `scopeExtractionComputableInPolyTime` starts with one contiguous
nonempty counted section and includes parsing, copying, transfers and cleanup
in its standard finite-machine polynomial bound. `output_length_balance`
charges precisely the removed count bits and delimiter; `remaining_length_lt`
proves strict progress, and `query_length_le` bounds the next membership query
by the actual incoming state length. `adjacent_step` connects the extracted
head and unchanged tail to the exact primal-edge recurrence.

`AllDifferentCSPScopeRouting.lean` now constructs both the predicate query and
its continuation, duplicating the binary endpoints while preserving the exact
head and tail order. `scopeRoutingComputableInPolyTime` proves `3s+3` steps
including restoration and scratch cleanup. `ScopeRouting.output_length`
charges exactly one extra copy of the two endpoints and bounds output by `2s`.
`AllDifferentCSPScopeTest.lean` composes extraction, routing and the existing
co-occurrence machine through the pinned pair-left adapter.
`scopeTestComputableInPolyTime` starts at the unsplit nonempty counted section
and returns the first scope's answer with both endpoints and the entire tail.
No split, copied index or membership answer is supplied externally.
`ScopeTest.output_length_balance` accounts for replacing the first counted
scope with one Boolean cell, so the complete result never grows, including
empty scopes. `result_eq_true` and `adjacent_step` give the exact same-scope
semantics and primal-edge recurrence.

`AllDifferentCSPScopeAccumulator.lean` combines the old and tested answers by
Boolean OR, copies the full retained state in order, and clears all scratch
stacks in at most `2s+3` steps. It removes exactly one Boolean cell.
`AllDifferentCSPScopeIteration.lean` composes extraction, query construction,
both membership tests and accumulation as `scopeIterationComputableInPolyTime`.
`nonempty_encode` proves that a nonempty loop state already has the exact
iteration wire format. `adjacent_invariant` preserves the accumulated answer
OR the remaining adjacency question. `output_length_balance` charges the
precise counted head removed, and `output_length_lt` proves strict progress
even for empty scopes. The executable recursion `finish` agrees with the exact
primal-edge predicate by `finish_false_eq_adjacent`, including repeated and
empty scopes. `AllDifferentCSPScopeLoopMachine.lean` now supplies the finite
dispatcher: it scans for counted scope cells, loads the complete iteration,
returns its output in order, and clears all work stacks on exit. An empty
scope has a count delimiter and cannot be mistaken for an exhausted list.
`AllDifferentCSPScopeLoop.lean` proves the complete repeated execution.
`scopeLoopComputableInPolyTime` computes the accumulated adjacency answer in
at most `(s+1) * (P(s)+4s+4)` steps, where `P` is the checked iteration's
polynomial and `s` is the original full state encoding length. The bound
includes scans, loading, all body calls, return transfers, and final cleanup.
`scopeLoop_adjacent_outputsInTime` proves exact adjacency from a false initial
accumulator. `AllDifferentCSPScopeInitialization.lean` now constructs that
false accumulator from the bare serialized endpoints and counted scope section
in `2s+2` steps, adding exactly one cell. Its composed
`scopeAdjacencyComputableInPolyTime` decides whether both endpoints occur in
one common scope, including initialization, all scope tests and cleanup.
`scopeAdjacency_query_length_le` bounds the complete query by twice the
retained intermediate length for a pair bounded by its unary variable tally;
`scopeAdjacency_steps_le` supplies a uniform polynomial bound for that call.
`AllDifferentCSPPairQueries.lean` now constructs strict-order and complete
adjacency queries from the serialized candidate-pair state. Its checked
`PairQueries.inputFinEncoding` retains binary endpoints, ranked occurrences,
the unary variable count, full scopes and previously emitted edge rows.
`pairQueriesComputableInPolyTime` copies and restores every required cell in
`4s+4` steps and clears all scratch stacks. `PairQueries.output_length` charges
two extra endpoint copies and one complete scope copy; output is at most `3s`.
`AllDifferentCSPPairTest.lean` composes those queries with the existing binary
comparison, full adjacency traversal and finite conjunction.
`pairTestComputableInPolyTime` returns precisely the increasing-endpoint,
same-scope filter while retaining the complete state, adding one answer cell.
`accept_iff_mem_enumerate` identifies it with the checked edge enumeration for
bounded candidates, and `accept_ofRuntimeSystem` connects it to the thesis
primal graph. `state_length_le_cubic` bounds a candidate state with at most
`n^2` bounded emitted edges by `12(s+1)^3` cells in the original retained-section
length `s`; `pairTest_bounded_steps_le` supplies the corresponding uniform
polynomial bound for a complete call. These are conditional bounds for the
outer loop. `AllDifferentCSPPairInitialization.lean` now constructs the exact
zero-endpoint, empty-edge state in `2s+2` steps, preserving its wire length.
`runtimeCompilerPairInitializationComputableInPolyTime` composes this from the
actual Boolean compiler input, including complete domain relabelling and unary
variable counting. `zero_edges` checks that zero variables yield no candidates,
even if malformed scopes mention indices. `AllDifferentCSPPairAdvance.lean`
now defines the executable conditional emission and row-major counter step.
`afterTest_invariant` preserves bounded counters, a bounded accumulated row
count, sound edge membership and strict output order. `advance_budget` removes
exactly one candidate from the grid budget; `run_position`, `run_exhausted` and
`run_stable` prove that `n^2` steps visit the entire grid and then stop changing.
`run_edges_eq` proves exact list equality with the existing deduplicated edge
enumerator, and `run_ofRuntimeSystem` connects this to compiler-produced input.
`iterate_length_le_cubic` bounds every state, including terminal and zero-variable
states, by `12(s+1)^3`; `iterate_test_steps_le` bounds complete predicate calls
uniformly in the original section length with no external invariant assumptions.
The executable scan's cycle count is at most `s^2`.
`AllDifferentCSPPairEmit.lean` now realizes conditional edge emission as a finite
machine. `pairEmitComputableInPolyTime` consumes the computed answer bit and
appends exactly the counted `[2,i,j]` row when true, preserving endpoints,
ranked domains, the unary bound, scopes and previous edge order. The bound
`4s+5` includes every copy, all five row framing cells and scratch cleanup;
`output_length_le` bounds the complete result by `2s+5`.
`PairEmit.afterTest_eq` identifies this result as the exact retained portion of
the abstract advancement step. `AllDifferentCSPPairFilter.lean` now composes
testing and emission: `pairFilterComputableInPolyTime` computes its own decision
from serialized endpoints and scopes, with all transfers included.
`mem_rows_iff_primalEdges` gives the exact old-or-new edge membership condition
on compiler-produced sections. `output_length_le_cubic` preserves the original
`12(s+1)^3` bound after filtering a reached active state, before counter advance;
`pairFilter_iterate_steps_le` uniformly bounds complete calls along the semantic
scan. `exhausted_eq` confirms that filtering the terminal `(n,0)` state changes
nothing, including zero variables. `AllDifferentCSPPairCounters.lean` now implements both counter actions.
`pairInnerCounterComputableInPolyTime` increments the second binary endpoint;
`pairOuterCounterComputableInPolyTime` resets it to canonical zero and increments
the first. They reuse the pinned successor and pair adapters, preserving every
retained section and edge. The reset pass takes `2s+2` steps including cleanup;
either continuation adds at most one encoded cell. `PairCounters.nextPair_eq`
identifies the two actions with the branches of the abstract row-major step.
`AllDifferentCSPPairStepBranches.lean` composes each counter action with the
complete computed filter and emitter. `pairInnerStepComputableInPolyTime` and
`pairOuterStepComputableInPolyTime` execute those complete branches, including
all transfers. `run_succ_eq` identifies the correct branch with the next
semantic scan state; its invariant, one-candidate budget decrease and cubic
wire bound follow without a new assumed invariant. `final_outer` proves the
last active outer call reaches `(n,0)` with exactly the complete ordered edge
list, for every positive `n`. Both complete branch calls have uniform polynomial
bounds in the original retained-section length.
`AllDifferentCSPPairBound.lean` now computes a binary copy of the retained unary
variable count. Its preparation pass takes `3s+3` steps, preserves the complete
scan state, and feeds the existing structural-header machine with an empty
payload. `unaryBoundComputableInPolyTime` reuses that machine's checked carry
loop in `8(n+1)^2` steps for unary length `n`; no new arithmetic machine is
assumed. `pairBoundComputableInPolyTime` composes preparation and counting,
including transfers and cleanup; its complete output has at most `2s+1` cells.
`AllDifferentCSPPairControl.lean` now implements both control predicates:
`pairActiveComputableInPolyTime` computes `i<n`, and
`pairContinuesComputableInPolyTime` computes `j+1<n`, from the complete original
state. The bound conversion, endpoint copy, successor, binary comparison,
transfers and cleanup are internal. The finite query router costs `5s+5` for
its bound-bearing input; each completed test adds exactly one answer cell and
preserves the original state. `PairControl.advance_eq` identifies the two
computed answers with the exact scan recurrence; `run_active_iff` proves
exhaustion occurs after precisely `n^2` cycles, including zero variables.
Both complete tests have uniform polynomial bounds in the original retained
section length.
`AllDifferentCSPPairGate.lean` now provides checked conditional calls on the
Boolean/pair-state wire. `PairGateMachine.skip_run` returns every cell unchanged
in `2s+2` steps without entering the body; `call_run` invokes a supplied checked
state transformer with its original step count plus `2s+2t+4` routing steps for
input/output lengths `s,t`. `computableInPolyTime` uses the pinned generic
output-size bound to include all routing and scratch cleanup in a polynomial.
`AllDifferentCSPPairDispatch.lean` composes the actual continuation test with
complementary gates that preserve the original answer, so exactly one complete
inner/outer branch runs. `PairDispatch.selectedComputableInPolyTime` removes
the temporary answer using a checked `2s+2` erasure pass.
`PairDispatch.computableInPolyTime` additionally computes exhaustion and gates
that whole active step, implementing exactly `PairAdvance.advance` on every
checked state. Exhausted states retain every cell, including arbitrary stored
edges; no external decision or well-formedness assumption is required.
`run_step_outputsInTime` gives the exact next semantic state with all dispatch,
body, transfer and cleanup costs bounded by one fixed polynomial evaluated at
`12(s+1)^3` in original retained-section length `s`. Kernel-reduced examples
cover zero/singleton bounds, carry, wrapping, duplicate scopes and an exhausted
state whose endpoints would otherwise pass the edge test.
`AllDifferentCSPPairLoopMachine.lean` supplies the finite repeated controller.
Its body erases the old answer, invokes the complete dispatcher and computes
new active control. `iteration_cycle` charges the full body plus `2s+2t+4`
steps for input/output lengths `s,t`; `exit_run` removes the false answer and
returns the entire terminal state in `2s+2` steps. Every return restores wire
order and clears all scratch stacks.
`AllDifferentCSPPairLoop.lean` proves the total repeated runtime. The checked
internal entry encoding retains the complete initialized state plus one active
bit, rejecting a different state in its decoder. `PairLoop.run_bounded`
charges all remaining grid cells and the final false-answer exit. At complete
entry length `s`, every flagged working state is bounded by `B=12(s+1)^3+1`,
and the loop takes at most `(s^2+1)*(P(B)+4B+4)` steps, where `P` is the checked
complete-body polynomial. `PairLoop.entryComputableInPolyTime` constructs the
zero counters, empty edge list and computed control bit; it is composed with
the loop in `pairEnumerationComputableInPolyTime`.
`runtimeCompilerPairEnumerationComputableInPolyTime` starts from actual Boolean
compiler input and returns terminal counters `(n,0)`, all retained ranked
sections, and exactly the deduplicated primal-edge list. The full composition
includes preparation and entry costs, beyond the displayed loop polynomial.
Zero variables, empty/overlapping/repeated scopes and arbitrary binary values
are covered.

`AllDifferentCSPPairFinalization.lean` removes only the scan counters in
`2s+2` steps. `runtimeCompilerGraphSectionsComputableInPolyTime` returns the
ranked sections paired with the exact ordered graph.
`runtimeCompilerNegativeSectionsComputableInPolyTime` composes the checked
pair-right negative-row emitter from the actual Boolean compiler input,
preserving every ranked section. `GraphSections.negative_encode` identifies
the complete paired wire with the semantic compiler's ordered `unequalRows`;
`negative_length_le_cubic` bounds that whole paired output by `10(s+1)^3` in
the retained-section input length, including both retained data and rows.
`AllDifferentCSPEdgeCount.lean` reuses the complete row counter on the
constructed graph. `EdgeCount.outputsInTime` retains every endpoint and emits
one unary mark per edge in `20(s+1)^2` steps; the complete result is at most
`2s` cells. `runtimeCompilerCountedGraphSectionsComputableInPolyTime` composes
this pass from actual Boolean compiler input, retaining every ranked section.
`CountedGraphSections.count_eq` identifies its computed tally plus one with
the semantic pinning weight.

`AllDifferentCSPPinningWeight.lean` constructs that weight. Its finite
preparation pass appends one tally mark and routes the count in `2s+2` steps,
retaining every edge cell. `pinningWeightBinaryComputableInPolyTime` reuses the
checked binary-header machine and pair-right adapter to count the marks into
an exact reversed raw binary field, including its delimiter. The complete
`runtimeCompilerWeightedNegativeSectionsComputableInPolyTime` starts from
actual Boolean compiler input and returns all ranked sections, the exact
negative rows and the internally computed binary pinning weight.
`WeightedGraphSections.encode_eq` identifies both row and weight fields with
the semantic compiler, while `encode_length_le_cubic` bounds the entire output
by `11(s+1)^3+2` in the complete retained-section length `s`. Empty graphs have
weight one; repeated scopes do not inflate the count; binary carry is included.

`AllDifferentCSPPositiveEnumeration.lean` now specifies an executable scan of
variable indices and ranks bounded by the stored occurrence count.
`PositiveEnumeration.rows_eq_pinningRows` proves exact equality with the
semantic compiler's ordered positive rows, using the computed edge count plus
one as weight. Repeated entries produce one row, and empty domains preserve
later variable indices. `enumerate_nodup` and `enumerate_length_le` prove that
no pair repeats and output count cannot exceed stored occurrence count.
`enumerate_eq_filter` connects the scan to its explicit candidate grid;
`candidates_length_le_wire_quadratic` bounds that grid by `s(s+1)` in the
complete retained-section wire length. This executable specification and semantic/order proof are implemented by
`positiveEnumerationComputableInPolyTime`, described below.

`AllDifferentCSPPositiveBlock.lean` adds a concrete finite machine and checked
input/output encodings for one positive row. `positiveBlock_outputsInTime`
and `positiveBlockComputableInPolyTime` preserve all binary index, rank and
weight fields, prefix exactly `[4,0]`, and clear scratch stacks in `2s+2`
steps. The complete output adds exactly five cells to the three-field input.
`AllDifferentCSPPositiveRows.lean` checks concatenated positive-row blocks;
its decoder rejects negative rows and wrong arities.
`PositiveRows.outputEncode_ofRuntimeSystem` identifies the exact raw output
from weighted ranked sections with the semantic compiler's ordered pinning
rows. `outputEncode_length_le_wire_quadratic` bounds that whole positive
section by `11(s+1)^2` in the complete weighted-section wire length, including
the binary weight field. This is a wire-size theorem; the complete positive-scan runtime is checked
below. Full objective headers/row assembly, final framing and selected-prime
composition remain open.

`AllDifferentCSPOccurrenceCount.lean` reuses the checked row-counting machine
on the exact tagged ranked-occurrence wire in `20(s+1)^2` steps. The composed
`runtimeCompilerCountedPositiveSectionsComputableInPolyTime` starts from the
actual Boolean compiler input, counts every stored occurrence, and retains the
unary variable count, scopes, negative rows and binary weight.
`CountedPositiveSections.count_eq` identifies the computed tally with the
original domain-entry count; repeated entries contribute separate tally marks.
The complete retained output is at most twice its weighted-section input
length, and `gridSize_le_wire_quadratic` bounds both numerical scan dimensions
by the actual encoded length for every intermediate value. This constructs
the positive scan's bound; membership traversal and repeated row emission are
checked below. Final objective/prime assembly remains open.

`AllDifferentCSPPositiveWeight.lean` now stages the graph compiler's common
binary weight for one selected `(variable, rank)` pair. The concrete
`positiveWeightPrepare_outputsInTime` machine copies and restores the weight
in `3s+5` steps for complete input length `s`, including all field delimiters
and cleanup. `positiveRowWithWeightComputableInPolyTime` composes this pass
with the checked positive-row emitter while retaining the original weight.
`PositiveWeight.row_encode` identifies the emitted component with the exact
counted pinning row; the full row/weight output has at most `2s+7` cells.
`positiveRowWithWeight_steps_le` gives a uniform complete-call polynomial
bound for every bounded candidate in the retained positive-scan state.
The initialized membership decision and complete positive-row traversal are
checked below. Full objective/framing/prime composition remains open.

`AllDifferentCSPPositiveMembership.lean` checks the exact ordered-pair
membership predicate. `contains_cons` requires both fields to match the same
occurrence, and `enumerate_eq_filter` connects it to positive-row selection.
`positiveMembershipExtractionComputableInPolyTime` reuses the existing counted
row extractor and count-removal machine to expose one `[0,index,rank]` payload
while retaining both candidate fields and the exact remaining occurrence
stream. Its checked decoders reject incorrect tags and arities. Extraction
removes exactly three row-count cells; `remaining_length_balance` charges
both removed binary words plus six header/delimiter cells, proving strict
progress even for zero-valued fields. `input_length_le_sections` bounds the
whole candidate query by the retained positive-section wire length. The
ordered-pair comparison and repeated traversal are now checked below.

`AllDifferentCSPPositiveRouting.lean` reuses the existing finite scope router
to copy the candidate and retain the exact occurrence tail in `3s+3` steps.
`AllDifferentCSPPositiveComparison.lean` parses the checked `[0,index,rank]`
head into two separate singleton queries in another `3s+3` finite steps.
`PositiveQueries.output_length_balance` removes exactly the zero-tag delimiter
while preserving all four binary words and both field separators.
`positivePairMatchComputableInPolyTime` executes the existing binary equality
machinery once per coordinate and conjoins the answers, including all parsing,
transfers and cleanup. `PositivePairQuery.equal_eq_true` proves that its result
is true exactly when the ordered pairs agree. Zero coordinates and arbitrary
binary magnitudes are covered. Counted-record testing, OR accumulation and
repeated traversal now compose as described below.

`AllDifferentCSPPositiveTest.lean` composes extraction, candidate copying and
same-record comparison from the original contiguous counted occurrence wire.
`positiveTestComputableInPolyTime` returns that Boolean plus the unchanged
candidate and exact tail. `AllDifferentCSPPositiveIteration.lean` reuses the
checked finite OR accumulator in `2s+3` steps and composes the complete
`positiveIterationComputableInPolyTime`. Each iteration removes precisely the
head's two binary words and six structural cells, so it strictly shrinks even
when both fields are zero. `PositiveIteration.contains_invariant` proves that
the accumulated answer OR membership in the remaining tail stays unchanged.
`finish_false_eq_contains` verifies the executable recurrence, including empty
and repeated records and cross-record false positives.

`AllDifferentCSPRecordLoopMachine.lean` factors the existing scope dispatcher
into one shared finite controller for the exact CSP record alphabet. Both scope
and positive-occurrence loops reuse its scan, call, return and cleanup proofs.
`PositiveLoopMachine.iteration_cycle` runs the complete ordered-pair test and
returns its exact shortened state. `positiveLoopComputableInPolyTime` now
traverses every occurrence, returning the accumulated answer OR exact pair
membership. If `P(s)` bounds one checked body call, the complete loop costs at
most `(s+1)*(P(s)+4s+4)` in its original encoded state length `s`. This includes
all transfers and final query cleanup, even for empty lists or zero fields.
`AllDifferentCSPPositiveInitialization.lean` now reuses the scope initializer
on the identical serialized alphabet, adding the false answer in at most
`2s+2` steps with exactly one extra encoded cell.
`positiveMembershipComputableInPolyTime` composes this pass and the complete
loop from the original serialized candidate and counted occurrence list.
`PositiveInitialization.result_ofRuntimeSystem` identifies acceptance exactly
with membership in that variable's canonical relabelled domain.
`positiveMembership_steps_le` bounds every candidate call by the same polynomial
in the complete retained positive-section length. Empty lists, zero fields,
repeated records, swapped fields and large binary values are checked.
`AllDifferentCSPPositiveCandidateQueries.lean` now constructs the exact
candidate/occurrence query while retaining the entire positive-scan state:
both unary bounds, scopes, negative rows, common binary weight and accumulated
positive rows. `positiveCandidateQueriesComputableInPolyTime` supplies a
four-stack finite machine with bound `3s+3` in complete state length `s`.
`PositiveCandidateQueries.output_length` charges exactly one query copy and
`output_length_le` bounds the output by `2s`; all scratch stacks are cleared.
The caller supplies one serialized state, not an extracted occurrence query.

`AllDifferentCSPPositiveCandidateTest.lean` composes that constructor with the
complete membership decision through the checked generic pair-left adapter.
`positiveCandidateTestComputableInPolyTime` returns the acceptance bit and the
entire original state; its output adds exactly one cell.
`PositiveCandidateTest.accept_ofRuntimeSystem` proves exact relabelled-domain
acceptance, and `filter_eq_enumerate` recovers the existing positive scan in
its precise candidate order. `state_length_le_cubic` bounds every state with
closed candidate bounds and at most a grid of bounded, common-weight rows by
`16(s+1)^3` in immutable-section wire length `s`, including all weight bits.
`positiveCandidateTest_bounded_steps_le` then gives one polynomial bound for
all such complete calls. The reached-state invariants are established by `PositiveAdvance` below;
repeated finite control remains outstanding.

`AllDifferentCSPPositiveCandidateEmit.lean` now consumes the computed answer
and conditionally appends the exact counted positive row while retaining the
candidate, both unary bounds, ranked occurrences, scopes, negative rows,
common binary weight and all earlier positive rows.
`positiveCandidateEmitComputableInPolyTime` implements this with a finite
seven-stack machine in at most `6s+7` steps for complete tested-state length
`s`. Both coordinate fields and the reversed binary weight are copied into
row order; all scratch stacks are empty at halt. `output_length` charges
exactly the accepted row, including its eight tag/delimiter cells and every
weight bit; `output_length_le` bounds the result by `2s+8`.

`AllDifferentCSPPositiveCandidateFilter.lean` composes the complete test and
conditional emitter through the pinned generic sequential-machine API.
`positiveCandidateFilterComputableInPolyTime` now computes one full candidate
filter from its serialized state, including query copying, membership,
weight copying, emission and all transfers. `rows_ofRuntimeSystem` identifies
its output exactly with relabelled-domain membership. Repeated occurrences
produce only one row per candidate. `rows_bounded`, `rows_capacity` and
`rows_nodup` preserve the shared weight, coordinate bounds, grid capacity and
uniqueness under their explicit input/freshness hypotheses.
`PositiveCandidateFilter.state_length_le_cubic` preserves the `16(s+1)^3`
bit bound after emission when a grid slot remains, and
`positiveCandidateFilter_bounded_steps_le` bounds every complete call by one
polynomial in the immutable-section wire length. `PositiveAdvance` below now
establishes capacity and freshness for reached states.

`AllDifferentCSPPositiveAdvance.lean` now gives the executable rectangular
traversal, including its canonical terminal `(variableCount, 0)`.
`run_position`, `run_pair_at`, `run_exhausted` and `run_stable` prove that each
candidate is visited exactly once and that traversal stops after
`variableCount * (occurrenceCount + 1)` visits. `step_invariant`, `fresh` and
`active_capacity` establish the previously required row bounds, common weight,
freshness and capacity for every reached state. `run_rows_eq` identifies the
terminal ordered list exactly with the positive enumeration when the occurrence
header is consistent, and `run_ofRuntimeSystem` gives the actual semantic
compiler's pinning rows. `run_nodup` excludes duplicates. `run_length_le_cubic`
retains the complete `16(s+1)^3` bit bound; `run_filter_steps_le` bounds every
actual finite test-and-emit call by one polynomial in the original section
length. The executable iteration is not yet a repeated finite-machine runtime
result.

`AllDifferentCSPPositiveCounters.lean` supplies both finite binary counter
continuations using the pinned successor, pair-left/right and sequential
machine APIs. `PositiveRankResetMachine.outputsInTime` erases the rank word
in its bit length plus one steps; the pair adapters preserve every other
state field. `positiveInnerCounterComputableInPolyTime` increments rank, and
`positiveOuterCounterComputableInPolyTime` increments index and resets rank.
Each continuation adds at most one bit to the full state. The complete
`positiveInnerStepComputableInPolyTime` and
`positiveOuterStepComputableInPolyTime` compose membership, conditional emission
and the appropriate counter, including all transfers. `PositiveCounters.run_succ_eq`
identifies the required branch of the reached semantic state, and
`positiveInnerStep_run_steps_le` / `positiveOuterStep_run_steps_le` bound each
complete branch by one polynomial in the original section wire length.

`AllDifferentCSPPositiveScanInitialization.lean` now constructs the exact
`PositiveAdvance.seed` with binary candidate `(0, 0)` and an empty positive-row
list. `positiveScanInitialization_outputsInTime` preserves every counted-section
bit in at most `2s+2` steps, with no increase in encoded length and all work
stacks cleared. `runtimeCompilerPositiveScanInitializationComputableInPolyTime`
composes this initializer from the actual Boolean compiler input. The initialized
state satisfies the existing complete reached-state invariant.

`AllDifferentCSPPositiveBound.lean` now selects either retained unary bound
in `3s+3` finite-machine steps, then converts it to canonical binary using the
checked counting and pair-left APIs. `binary_length_le` charges the full bound
copy and retained state by `2s+1`. `AllDifferentCSPPositiveControl.lean` routes
the appropriate candidate coordinate and computed bound into binary comparison
order in `5s+5` steps. `positiveActiveComputableInPolyTime` decides
`index < variableCount`; `positiveContinuesComputableInPolyTime` decides
`rank < occurrenceCount`, including the last-rank transition and zero counts.
Both return the entire original state with just one added Boolean cell.
`PositiveControl.advance_eq` matches these decisions to the existing exact
rectangular traversal; `run_active_iff` gives precisely
`variableCount * (occurrenceCount + 1)` active visits. The two
`*_iterate_steps_le` declarations bound complete calls uniformly by polynomials
in the original retained-section wire length, including count conversion,
comparison, transfers and cleanup.

`AllDifferentCSPPositiveDispatch.lean` now composes the complete finite
rectangular step. `PositiveDispatch.computableInPolyTime` computes exhaustion
and continuation, invokes exactly one membership/emission/counter branch, and
returns exhausted states unchanged. The conditional-call controller and
`decisionEraseComputableInPolyTime` are shared with the pair scan by
parameterizing the retained encoding. Every copy, decision and cleanup is
included; `iterate_steps_le` and `run_step_outputsInTime` bound the complete
next-state call in the original counted-section bit length.

`AllDifferentCSPPositiveScanLoopMachine.lean` and
`AllDifferentCSPPositiveScanLoop.lean` now check the entire repeated scan.
The pair and positive scans share `FlaggedLoopMachine`; each cycle executes
the complete dispatcher and computes the next active bit. `run_bounded`
charges every one of the `n(q+1)` candidate visits and the final false-bit exit.
At loop-entry bit length `s`, set `B=16(s+1)^3+1`: the loop takes at most
`(s(s+1)+1)*(P(B)+4B+4)` steps, where `P` is the checked complete-body polynomial.
`positiveEnumerationComputableInPolyTime` also constructs the seed and control
bit; `runtimeCompilerPositiveEnumerationComputableInPolyTime` includes all
preparation from the actual Boolean compiler input. Its result retains the
ranked sections, negative rows and weight, ends at counters `(n,0)`, and contains
exactly the ordered semantic pinning rows (`result_ofRuntimeSystem` and
`result_outputEncode_ofRuntimeSystem`). `result_nodup` proves uniqueness and
`result_length_le_cubic` bounds the complete retained output. Count consistency
is needed only for the intermediate row-correspondence lemma; the actual
compiler constructs that count internally.

`AllDifferentCSPObjectiveRows.lean` now collects the complete residual-row list.
`objectiveRowsComputableInPolyTime` retains the unary variable count and puts
all positive rows before all negative rows in at most `2s+4` finite-machine
steps, clearing every scratch stack. Its complete output is no larger than
its input. `runtimeCompilerObjectiveRowsComputableInPolyTime` composes this
assembly from actual Boolean compiler input; `ObjectiveRows.assemble_result`
proves exact equality with the variable count and rows of
`compileUsingDomainEntryBound`, including order, weights and multiplicity.
The row decoder checks every tag and arity. Header construction, final framing
and selected-prime composition remain open; `cor:all-different-csp` is partial.

The complete scope-section machine in `AllDifferentCSPScopeMachine.lean`
remains checked. `ScopeSectionMachine.computer` uses five
finite-alphabet stacks. For each count-prefixed row it saves the original
binary count, emits its successor and the scope tag, and copies exactly that
many entries using an explicit binary predecessor loop. It restores any
looked-ahead delimiter before proceeding, preserving empty rows, repeated
scopes, repeated entries, and final-row exhaustion. The exact execution proof
halts with every non-output stack empty.
`scopeSection_outputsInTime` and `scopeSectionComputableInPolyTime` prove the
identity on whole scope lists from `ScopeFieldSection.rowPayloadFinEncoding`
to `ScopeFieldSection.outputFinEncoding` in at most `20 * (s+1)^2` steps for
actual payload bit length `s`. `completeScopeSectionComputableInPolyTime`
uses the pinned generic sequential-composition theorem to run the checked
linear outer-count removal internally, starting from
`ScopeFieldSection.inputFinEncoding`.

The checked scope output interface in `AllDifferentCSPScopeSection.lean`
continues to provide exact decoding, tag rejection, and the `4s` complete
output-size bound. `StructuralFieldStream.encode_eq_header_sections` fixes
the exact record and variable headers followed by the domain and scope
outputs; `raw_encode_eq_reversed_sections` identifies their reverse staging
with the checked raw structural view. Both complete section machines are now
present, and source splitting with both paired section passes now composes
from the actual compiler input. Variable-count extraction and source retention
now also compose from that input and the count survives both section passes.
The structural view now assembles under its checked payload encoding, and a
separate pass retains it while computing the unary outer row count. Binary
header conversion, raw assembly, and the original Boolean framing bridge now
compose from the actual input as
`runtimeCompilerStructuralViewComputableInPolyTime`.

The complete indexed domain-section machine remains checked:
`DomainFieldSection.rowPayloadFinEncoding` parses count-prefixed rows through
exact payload exhaustion, rechecks every row count, preserves empty rows, and
is no longer than `DomainFieldSection.inputFinEncoding`.
`rowFields_injective` proves the outer-count-free payload loses no domain
boundaries. `domainRowPayloadStructuredComputableInPolyTime` repackages the
existing concrete three-stack header-removal pass as an identity machine on
the structured domain list in at most `2s+1` steps.
`domainSectionComputableInPolyTime` consumes that checked payload, maintains
and increments its canonical binary index, and emits exactly
`RuntimeStructuralView.indexedDomainOccurrences` in at most `100(s+1)^3`
steps for payload bit length `s`; empty sections, empty rows, singleton rows,
and index carry growth are all covered by the exact execution proof. The
composed `completeDomainSectionComputableInPolyTime` starts instead from
`DomainFieldSection.inputFinEncoding` and internally runs both verified passes
to the same exact occurrence stream. The accompanying
`occurrences_indexedRowsFrom` theorem advances consecutive indices across all
rows, including empty rows, while `outputEncode_eq_row_outputs` and
`outputEncode_eq_structuralFields` prove that concatenating the already
checked per-row machine outputs is exactly the domain portion of the complete
structural target. `domainFieldRowComputableInPolyTime` remains the checked
quadratic machine for each indexed row, and
`scopeFieldBlockComputableInPolyTime` supplies the intact-scope branch.
`StructuralFieldStream.raw_decode_encode_reverse` still supplies the complete
full-stream target, and the prior quadratic theorem bounds that target in the
actual compiler input bit length. Source splitting, paired domain expansion,
and paired scope processing now compose from that input. The exact structural
view, including its original variable count, now assembles under the checked
payload encoding and also under the original Boolean encoding. The complete
composition includes outer row counting, binary-header staging, and framing;
`binaryPredComputableInPolyTime` already supplies its empty- and
singleton-safe binary countdown operation.

The headline catalogue therefore contains 30 statements: 28 complete and 2
partial, with nothing pending. Every partial row has its mathematical content
checked and lacks only an external complexity ingredient: the Smith-normal-form algorithm and running time
(`thm:max-polytime`), or the remaining runtime machine composition
(`cor:all-different-csp`). The clause-wise theorem is complete without
qualification: `CNFNormalisation.lean` normalises arbitrary 3-CNF syntax into
the three-distinct-variable convention and transfers the theorem.

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

## Supporting-statement formalisations

These active-thesis statements are outside the headline catalogue. They are
recorded here once a statement-faithful Lean declaration exists.

| Thesis label | Status | Lean declaration or remaining work |
|---|---|---|
| `prop:chapter-residual-medoid` | Complete | `ResidualMedoid.exists_medoid_multiset` (nonempty finite multiset in `ℚ_[p]`; the minimiser of `∑_{r∈R}‖r-a‖` lies in `R`), with `exists_medoid` and `exists_medoid_finset` for indexed families. |
| `cor:chapter-monotone-update` | Complete | `ResidualMedoid.monotone_coordinate_update`: for the additive binary-tag model, an observed partial residual globally minimises the coordinate objective `F_j` and substituting it does not increase the full fitting objective (`loss_update_eq`). Rows and tags are arbitrary finite types; the current coefficient vector is arbitrary. |
| `thm:main` with `lem:toobig`, `lem:binary`, `lem:magnitude`, `lem:rounding` | Complete | `PublishedMaxCut.published_main`: the literal published `2`-adic reduction with uniform multiplicity `M = m + 1` over `ℚ_[2]`: `binary_lemma` (every prime), `loss_zero_eq`/`not_optimal_of_ge`, `not_optimal_of_norm_gt_one`, `rounding_le` (with the strict `rounding_lt` and `globalMin_boolean` as a bonus), `publishedLoss_embed` (`L(s) = Mn + m − cutsize(s)`), a Boolean optimum, `optimal_value` (`cutsize* = Mn + m − L*`), and `cut_ge_iff` (the `K`-decision form); `homogeneousLoss_publishedRows` identifies the objective with the explicit `{0,1}` instance of `m + 2Mn` rows. The theorem's NP-hardness claim is `FixedPrimeMaxCutMachine.encodedRegression_NPHard 2` (and its unary form), proved through the edge-streamed variant of the same Max-Cut reduction; as in the thesis's own proof scheme, hardness of the `p = 2` restriction is the content of the claim. |
| `lem:large-prime-unit-residuals` | Complete | `LargePrime.large_prime_unit_residuals`: with `ℋ = candidateFamily X y` (chosen rational interpolants of all affinely independent `(d+1)`-subsets, `d+1 = affineRank X`, degenerate data allowed via the rank-general `rank_refinement`), there is an explicit data-only bound `primeBound X y` such that for every larger prime the optimum is attained in `ℋ` and every residual of every member has `p`-adic norm `0` or `1`. `card_candidateFamily_le` gives `|ℋ| ≤ C(k, d+1)`. |
| `lem:large-prime-stability` | Complete | `LargePrime.large_prime_stability` and `large_prime_optimal_iff_most_contacts`: for primes above the bound, a member of `ℋ` is `q₁`-optimal iff `q₂`-optimal, and the optimal members are exactly those with the fewest misses (`loss_eq_missCount_of_large_prime`). |
| `poly-corollary` | Complete | `PolynomialCorollary.poly_corollary`: a degree-`≤ n` minimiser of `∑ |P(xᵢ) − yᵢ|_p` over data with at least `n+1` distinct abscissae interpolates at least `n+1` points. `poly_corollary_of_minimizes` drops the unused thesis hypotheses `k ≥ n+1` and `xᵢ = xⱼ ⇒ yᵢ = yⱼ`; `n = 0` is covered uniformly. |
| `poly-approxy` | Complete | `PolynomialCorollary.poly_approxy`: an optimal degree-`≤ n` `p`-adic approximant `Q` of `P` on a finite set of at least `n+1` points leaves a residual `P − Q` with at least `n+1` distinct rational zeros (`poly_approxy_filter` locates them inside the set). |
| `cor:residual-simple-roots` | Complete | `PolynomialCorollary.residual_simple_roots`: a polynomial residual of degree `n+1` (thesis definition `IsPolynomialResidual`, with the standing hypothesis of at least `n+1` evaluation points) has `Nodup` roots. |
| `cor:residual-rational-roots` | Complete | `PolynomialCorollary.residual_rational_roots`, `residual_splits`, `residual_roots_map`: a degree-`n+1` residual has exactly `n+1` distinct rational roots, factors into distinct linear factors over `ℚ`, and acquires no new roots in any field extension. |
| `thm:widespread-equioptimal` | Complete | `PolynomialCorollary.widespread_equioptimal`: for `n+1` points with pairwise `p`-adically equidistant abscissae (`c ≠ 0`) and an interpolant of degree exactly `n` (`1 ≤ n`), the degree-`≤ n−1` minimisers are exactly the `n+1` distinct candidates `P − a∏_{i≠j}(X − xᵢ)`, each missing exactly one point, all with loss `|a|_p cⁿ`. The hypotheses `1 ≤ n` and `c ≠ 0` are implicit in the thesis and made explicit. |
| `prop:3sat-hole-filling` | Complete | `ClauseErasure.clause_erasure`: for `p > 3`, filling the hole at `t_C` makes every clause well the constant `3` on Boolean inputs (`well_valueRange_embeddedBoolean`), the erased objective is the constant `αn + 3m` on `{0,1}^n`, and under the explicit domination hypothesis `4Δ < α` its global minimisers over `ℚ_[p]^n` are exactly the Boolean assignments. `well_at_mem`/`well_at_notMem`/`well_minimised_iff` are the well facts; `positiveLoss_globalMin_iff_maximizesSatisfied` is the positive-encoding analogue of `thm:3sat-clausewise`. |
| approximate negation (unlabelled lemma, `app:approximate-negation`) | Complete | `ClauseErasure.approximate_negation`: replacing negated-literal coefficients by integers `≡ −1 (mod p)` preserves the clause residual norm on Boolean-labelled inputs for `p > 3`; `pow_sub_one_modEq_neg_one` covers `p^k − 1`, and `modifiedClausewiseLoss_embeddedBoolean` transfers the identity to the compiled clause-wise objective. |
| sparse junta case (unlabelled corollary of `thm:sparse-medoid-representation`) | Complete | `SparseJunta.sparse_junta_case`: if `F(x) = H(x_T)` with `|T| ≤ s` and `H` non-expansive (`NonExpansive`, equivalent to the thesis valuation form by `nonExpansive_iff_val`), the medoid ensemble with constant active set `T` represents `F` exactly and every regressor uses only the features in `T`. |
| `prop:sudoku-locator-fingerprint` | Complete | `SudokuDiagnostics.locator_fingerprint` and `locator_fingerprint_prob`: over any finite field, a committed polynomial of degree `≤ D` different from the locator `Λ_x = ∏_{violated c}(Z − α_c)` agrees with it at most `D` points, so the uniform-sample collision probability is `≤ D/Q`; `locator_monic`, `natDegree_locator`, `roots_locator` record the locator's algebra. |
| `prop:sudoku-robust-decoding` | Complete | `SudokuDiagnostics.unique_nearest_dmin` and `separation_dmin`: under robust soundness `L(x) ≥ γ d_H(x, 𝒮)`, every `x` with `L(x) < γ d_min/2` has a unique nearest solution, and two low-loss assignments with different nearest solutions are at Hamming distance `≥ d_min − 2ℓ/γ`; the general forms take any pairwise lower bound `d` in place of `d_min`. |
| `lem:reg-finite-candidates` | Complete | `RegularisedCandidates.reg_finite_candidates`: for the six-point dataset at `p = 5` with per-point loss `2^{-v_5}` and slope penalty `λ 2^{-v_5(a)}`, every `λ ≥ 0` has an attained minimum, attained by a line through two distinct data points or a horizontal line through a data point; `not_fits_one_three` excludes the vertical pair and `nonvertical_pair_count = 14`, `distinct_horizontal_count = 4` check the thesis counts. Built on `weighted_exists_global_minimizer`, a weighted norm-monotone version of the finite-search theorem for arbitrary homogeneous designs. |
| `lem:row-swap-locality` | Complete | `RowSwapLocality.row_swap_locality` and `Hcb_swap_locality`: the change of the duplicated unit-scope objective under a within-row swap is exactly the change of the two column terms and the one or two box terms containing the swapped cells; `Hcb_swap_locality_of_box_eq` sharpens the shared-box case, and `H_eq_Hcb_of_rowsArePerms` records that row terms vanish on the row-permutation state space. |
| `lem:pow2-landscape` | Complete | `PowersOfTwoLandscape.pow2_landscape`: for odd `p`, `|2^a − 2^b|_p = |2^{|a−b|} − 1|_p`, a unit iff `ord_p(2) ∤ |a−b|`; every move is a unit step for `p ∈ {11,13,23,47,73,97}` (orders `10,12,11,23,9,48` by `decide`) and for `p > 255`; strict decrease iff `ε ≡ r (mod p^{v_p(r)+1})`; and `|r|_p < |ε|_p ⇒ |r − ε|_p = |ε|_p`. `seven_inversion` gives the `p = 7` example with exact values. |
| `prop:medoid-prefix-consensus` | Complete | `PrefixConsensus.prefix_consensus_identity` (`∑_j |c − z_j|_p = m − (1 − p⁻¹) ∑_{r≥1} p^{−(r−1)} #{j : z_j ≡ c mod p^r}`, with the series proved convergent) and `medoid_iff_maximises_score` (medoid argmin = weighted prefix-score argmax on any finite candidate set); `capped_medoid_iff_maximises_score` covers the implemented bounded medoid with non-integral predictions discarded as constants. |
| `prop:strict-refinement` | Complete | `StrictRefinement.valuation_sum_eq_valuation_head` and `valuation_sum_univ_eq_valuation_head`: nonzero coefficients with strictly increasing `p`-adic valuations have every tail sum of valuation equal to its first term; `tailSum_ne_zero` shows the tails are nonzero, and `norm_sum_eq_norm_head` is the norm form without a nonvanishing hypothesis. |

## The active thesis contains more than the headline catalogue

The active thesis checkout contains 54 theorem, corollary, proposition, or
lemma environments. The 24-row catalogue above intentionally records the main
mathematical contributions, not every supporting or applied statement.

Several of the additional environments already have Lean support even though
they do not have separate catalogue rows: the independent-contact refinement,
the coreset witness-point lemma, the 3-SAT row indicator, Boolean/domain
snapping, the all-different edge and unary identities, and the Sudoku
difference-indicator calculation. The supporting-statement table above records
the additional environments that now have their own statement-faithful
declarations.

Every theorem, corollary, proposition, or lemma environment of the active
thesis now has a corresponding Lean declaration, either in the headline
catalogue or in the supporting-statement table. The only remaining gaps are
the external complexity ingredients recorded in the Partial rows, together
with the following items that are prose or data rather than stated results:
the APX-hardness discussion (left open by the thesis itself), the numerical
enumeration table of the six-point regularisation example, and the Sudoku
heuristic traces.

The separate question about how many distinct solutions occur along a
regularisation path remains an open research question in the thesis. It is not
counted as an unproved theorem because the thesis does not assert it as one.
