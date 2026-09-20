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
| `cor:all-different-csp` | Partial | `AllDifferentCSP.ExplicitSystem` supplies explicit syntax, nonempty-domain well-formedness, a deduplicated primal graph, and canonical rank relabelling onto \(\{1,\ldots,q\}\). `selectPrimeAbove` executably scans the Bertrand interval and proves the selected prime satisfies \(q<p<2q\) for \(q>1\), with explicit \(q=0,1\) cases. `ResidualRow`, `CompiledObjective`, and `compileObjective` emit the selected prime and a finite sparse row list; `rowsLoss_compileObjective`, `compileObjective_allDifferent_correctness`, and its satisfiable specialization connect that output exactly to the checked p-adic semantics. `compileObjectiveAt` exposes those same rows under any checked supplied-prime header. `AllDifferentCSPEncoding.RuntimeSystem` and `RuntimeObjective` have checked `Bool`-alphabet `FinEncoding`s with exact wire-size equations. `compile_rows_length_le_encodedSize_polynomial` bounds emitted sparse rows quadratically, while `compile_encodedSize_le_quartic` bounds the complete encoded output—including every numeric field and delimiter—by \(64(s+1)^4\) in the actual input bit length \(s\). `compileUsingDomainEntryBound` chooses a prime above the explicit domain-entry count; `symbolCount_lt_domainEntryPrime` proves this input-length-bounded choice is large enough for the canonical ranks, its two correctness theorems give exact minimum-conflict and satisfiable-case semantics, and `compileUsingDomainEntryBound_encodedSize_le_quartic` preserves the complete quartic output bound. `RuntimeCompilerInput.finEncoding` adds the explicit occurrence count as a decoder-checked unary header with at most linear overhead, and `compileUsingDomainEntryBound_encodedSize_le_compilerInput_quartic` retains the full quartic output bound against this actual compiler input. `RuntimeStructuralView` gives the structural machine an exact checked target: its header retains the variable count, each explicitly listed domain value becomes a tagged indexed occurrence without deduplication or reordering, every attached index is proved in range, and every scope remains an intact tagged record; its Boolean `FinEncoding` round-trips exactly. `ofRuntimeSystem_encodedSize_le_quadratic` bounds that complete tagged encoding by \(32(s+1)^2\) bits in the compact input length, and `ofRuntimeSystem_encodedSize_le_compilerInput_quadratic` retains the same bound against the actual compiler input without treating numeric symbol magnitude as bit length. `RuntimeStructuralView.rawFinEncoding` checks the corresponding stack-oriented raw-field representation, and `runtimeStructuralViewFramingComputableInPolyTime` converts it to the exact Boolean encoding in at most three times the raw input length. `AllDifferentCSPMachine.framedNatComputableInPolyTime` constructs each self-delimiting natural field from raw binary in linear time; `framedNatListComputableInPolyTime` traverses a stack-oriented reverse raw-field stream and emits the exact framed natural-list wire format in at most \(3s\) steps; `unframedNatListsComputableInPolyTime` traverses the standard nested-list input and exposes its outer length, inner lengths, and values as an explicitly delimited raw-field stream in at most \(3s\) steps; `domainEntryCountComputableInPolyTime` extracts the checked unary occurrence header in exactly \(s+1\) steps for complete compiler-input length \(s\); `compilerPayloadComputableInPolyTime` removes that header while preserving the compact payload byte-for-byte in at most \(2s+1\) steps, and `runtimeCompilerRawFieldsComputableInPolyTime` composes this pass with unframing to emit the exact nested-list structural fields from the actual compiler input. `SourceOrderRawNatLists.finEncoding` checks the same fields in semantic source order, with each delimiter before its canonical binary payload; `sourceOrderRawFieldsComputableInPolyTime` constructs that representation in exactly \(s+1\) steps, and `runtimeCompilerSourceOrderFieldsComputableInPolyTime` composes it from the actual compiler input so the outer length and domain-count separator precede all domain and scope fields. `SourceOrderRawFields.finEncoding` checks uncounted local field sequences. `domainOccurrenceBlockComputableInPolyTime` emits the exact `[3, 0, index, value]` domain-occurrence block in at most \(2s+2\) steps, while `scopeFieldBlockComputableInPolyTime` emits the exact intact `[|S|+1, 1, ...S]` scope block from its count-checked source fields in at most \(3s+8\) steps, including empty and singleton scopes. `domainFieldRowComputableInPolyTime` expands a complete count-checked `[index, |D|, ...D]` row into every exact `[3, 0, index, value]` block in at most \(20(s+1)^2\) steps in the complete row wire length, including empty and singleton domains. `DomainFieldSection.inputFinEncoding` checks the complete domain count and every row count in the existing source-order nested-list encoding; `occurrences_indexedRowsFrom` advances indices across all rows, including empty rows, and `outputEncode_eq_structuralFields` identifies the concatenated checked row outputs exactly with `StructuralFieldStream.domainFieldsFrom`. `DomainFieldSection.rowPayloadFinEncoding` rechecks the outer-count-free row payload through exhaustion, `rowFields_injective` proves its domain boundaries are unique, and `domainRowPayloadStructuredComputableInPolyTime` maps the complete section to that structured payload in at most \(2s+1\) steps without increasing its encoded length. `domainSectionComputableInPolyTime` consumes that payload, advances a canonical binary index across every row including empty rows, and emits exactly `RuntimeStructuralView.indexedDomainOccurrences` in at most \(100(s+1)^3\) bit-level steps. `completeDomainSectionComputableInPolyTime` composes the count-removal and indexed-row machines from the complete counted domain section to the same exact occurrence stream. `ScopeFieldSection.outputFinEncoding` checks the complete tagged scope output using the existing counted-row parser; its exact round trip retains empty scopes and repetitions, and `outputEncode_length_le_linear` bounds that output by four times the actual raw payload length. `scopeRowPayloadStructuredComputableInPolyTime` reuses the linear count-removal machine for scopes. `scopeSectionComputableInPolyTime` emits the exact complete tagged scope list in at most \(20(s+1)^2\) bit-level steps for payload length \(s\), preserving empty rows and repetitions with explicit binary countdowns; `completeScopeSectionComputableInPolyTime` composes it with count removal from the complete checked section. `sourceSectionsComputableInPolyTime` splits the full source-order runtime input into the existing checked pair of counted domains and scope payloads in at most \(40(s+1)^2\) steps, preserving empty sections, empty rows, repetitions, and arbitrary binary values without increasing encoded length. `runtimeCompilerSectionsComputableInPolyTime` composes that split from the actual compiler input. `pairedDomainSectionComputableInPolyTime` reuses the checked generic pair-left API at dependency commit `db20c69` to expand domains while preserving scopes; `runtimeCompilerDomainAndScopesComputableInPolyTime` composes the full input to that exact paired output. `LeanNPHardness.PairExchange.outputsInTime` checks exact canonical section exchange in at most `4s+6` steps for complete paired wire length `s`. `pairedScopeSectionComputableInPolyTime` composes two such exchanges with the pinned generic pair-left scope machine, preserving the exact domain output and restoring section order; `pairedScopeSection_output_length_le` bounds the entire paired output by four times its input length. `runtimeCompilerProcessedSectionsComputableInPolyTime` constructs both exact tagged sections from the actual Boolean compiler input with a checked polynomial bound. `variableHeaderComputableInPolyTime` copies the variable count from the third checked source field while preserving the complete source in at most `3s+6` steps, with paired output length at most `2s`; `runtimeCompilerVariableHeaderComputableInPolyTime` constructs this source/count pair from the actual compiler input. `runtimeCompilerCountedSectionsComputableInPolyTime` carries that count through the source split and both section passes using the checked generic pair-left API, constructing the exact occurrence/scope/count tuple from the actual Boolean input. `CountedSections.toStructuralView_ofRuntimeSystem` proves exact reconstruction, and `recordCount_le_encode_length` bounds the record count by the complete tuple encoding length. `runtimeCompilerStructuralPayloadComputableInPolyTime` now assembles the exact structural view under `RuntimeStructuralView.payloadFinEncoding`, reusing the exhaustion-delimited counted-row decoder. `structuralAssemblyComputableInPolyTime` performs the final merge in at most `2s+3` steps and adds exactly three header cells. `payloadEncode_ofRuntimeSystem_length_le_compilerInput_quadratic` bounds the constructed payload by `32 * (s+1)^2` in the actual Boolean compiler input length, while `rowCount_le_payloadEncode_length` bounds the required outer row count by the payload length. The full input composition has a checked polynomial bound. `structuralRowCountComputableInPolyTime` now retains the complete payload and constructs its unary outer row count in at most `20 * (s+1)^2` finite-machine steps for payload length `s`; its exact paired output is `(view, view.records.length + 1)`. `runtimeCompilerStructuralCountedPayloadComputableInPolyTime` composes that pass from the actual Boolean compiler input to the exact view and `C.domainEntryCount + C.scopes.length + 1`. `StructuralCountedPayload.encode_retain_length_le` bounds the pair by twice the payload length, and its compiler-input specialization bounds the whole output by `64 * (s+1)^2`. Binary conversion, raw staging, and framing now compose from the actual Boolean compiler input. `StructuralFieldStream.encode_eq_header_sections` and `raw_encode_eq_reversed_sections` specify exact section/header assembly and reversal into the checked raw structural view; the binary-header machine now realizes that raw target from the computed row count. `binarySuccComputableInPolyTime` computes successor on mathlib's canonical binary natural encoding in at most \(2s+3\) steps; `binaryLEComputableInPolyTime` decides less-than-or-equal on an aligned canonical binary pair in \(s+1\) steps; `binaryAddComputableInPolyTime` adds an aligned canonical pair by ripple carry in at most \(2s+3\) steps; `bertrandCandidatesComputableInPolyTime` emits exactly \([q+1,\ldots,2q]\) from a unary scan bound in at most \(16(q+1)^2\) steps. `RawUnaryNatList.finEncoding` checks the internal unary-delimited candidate stream; `unaryBertrandCandidatesComputableInPolyTime` emits the same list in at most \(6(q+1)^2\) steps, and `unaryBertrandCandidateStream_length_le` bounds it by \(2q^2+2q+1\) cells. `unaryDvdComputableInPolyTime` decides \(d\mid n\) on a delimiter-separated unary-padded pair in at most \(6s+16\) steps for exact encoded length \(s=n+d+1\), including zero cases. `trialPrime_eq_true_iff` proves that testing exactly the divisors in \([2,n)\) decides primality; `trialDivisionInputSize_le` bounds all unary trial pairs for one candidate by \(2n(n-2)\) cells; `RawUnaryPairList.finEncoding` checks the stack-oriented padded-pair stream; `trialDivisionPairsComputableInPolyTime` emits exactly \([(n,2),\ldots,(n,n-1)]\) from unary \(n\) in at most \(8(n+1)^2\) steps, including the empty \(n=0,1,2\) cases. `pairDivisionResultsComputableInPolyTime` consumes any such stream, applies divisibility to every field, and emits the exact Boolean results in at most \(17s+1\) steps for stream length \(s\); `trialDivisionPairStream_length_le` bounds the concrete trial stream by \((2n+1)(n-2)\). `allFalseComputableInPolyTime` folds a Boolean result stream in at most \(s+1\) steps, and `allFalse_trialDivisionResults_eq_true_iff` connects that fold exactly to primality for \(n\ge2\). `allFalseDivisibilityResultsComputableInPolyTime` fuses repeated divisibility with the fold, consumes the padded pair stream directly, and emits the exact no-divisor bit in at most \(18s+1\) steps; on `trialDivisionPairs n`, `allFalseDivisibilityResults_trialDivisionPairs_eq_true_iff` proves that bit is true exactly when \(n\) is prime for \(n\ge2\). `unaryCandidatePrimeComputableInPolyTime`, built with the pinned `lean-np-hardness` sequential-machine API, composes the pair generator with the fused pass and computes the candidate-only bit in at most \(64(n+1)^2\) steps on unary \(n\); `unaryCandidatePrime_eq_true_iff` gives exact primality semantics for \(n\ge2\). `two_le_of_mem_bertrandCandidates` checks the enumerator precondition, and `filter_unaryCandidatePrime_bertrandCandidates` proves the machine predicate induces exactly the guarded semantic prime filter. `primeSelectorComputableInPolyTime` consumes any checked unary candidate list and emits its first accepted source-order value in at most \(80(s+1)^3\) steps for complete encoded stream length \(s\); `primeSelector_selects_firstBertrandPrime` identifies its Bertrand-stream output with `firstBertrandPrime`, while `firstBertrandPrime_eq_selectPrimeAbove` identifies that value with the semantic compiler's selected prime, including \(q=0,1\). `selectedPrimeComputableInPolyTime` composes the unary Bertrand producer and selector and emits `selectPrimeAbove q` in at most \(1000(q+1)^6\) steps. `runtimeDomainEntryPrimeComputableInPolyTime`, using the pinned generic composition theorem, maps the checked compiler input to exactly `domainEntryPrime`. The header is verified redundancy rather than a supplied semantic assumption. The same input now also has checked header removal, raw traversal, and source-order normalization. `structuralBinaryHeaderComputableInPolyTime` now converts the computed unary row tally and stages the exact raw structural output in `8(s+1)^2` steps for the counted-payload length `s`. `runtimeCompilerStructuralViewComputableInPolyTime` now composes all structural passes and framing from the actual Boolean compiler input to exactly `RuntimeStructuralView.ofRuntimeSystem` under its original Boolean encoding, with an overall polynomial bound and the existing `32(s+1)^2` output-bit bound. `DomainSymbols.extract_toFinset` connects the structural occurrence symbols exactly to the semantic domain union; `rank_extract_eq_relabelValue` identifies executable list ranking with canonical semantic relabelling, with checked equality, prime-bound, and per-domain correspondence lemmas. `domainSymbolExtractionComputableInPolyTime` retains the exact occurrence wire and extracts its symbol fields in at most `3s+3` steps; `runtimeCompilerSymbolSectionsComputableInPolyTime` composes it from actual Boolean compiler input while preserving scopes and the variable count. The complete augmented tuple is bounded by twice the counted-section encoding length. `domainSymbolMembershipComputableInPolyTime` now decides membership from the checked serialized query/symbol pair in `6(s+1)^2` bit-level steps, reusing the upstream query-preserving equality kernel at dependency `ad20a2e`; loading and cleanup are included. `DomainSymbolMembership.rank_cons` now connects the computed membership bit to counting each smaller symbol once; `input_cons_length` and `tailMembership_outputsInTime` charge the complete query/tail wire exactly. `domainSymbolAlignmentComputableInPolyTime` now constructs aligned canonical comparison input from the complete tagged symbol/target pair in `4s+5` steps, including all loading, reversal, and cleanup, with output length at most `s`. `domainSymbolLessComputableInPolyTime` now composes that loader with the existing binary comparison kernel in `9s+10` steps, including transfer; `DomainSymbolComparison.rank_cons` identifies its exact strict-comparison bit with the rank recurrence, and `input_head_length` charges both words to the complete rank query. `rankQueriesComputableInPolyTime` now constructs both predicate queries and the next target/tail query from the checked nonempty rank wire in `3s+5` steps, including all copies and cleanup; its complete output length satisfies `output + 2 = 2s`. `rankPredicatesComputableInPolyTime` composes that preparation with both predicate machines through the upstream pair adapters, preserving the next query and charging all transfers. `RankPredicates.rank_step` identifies the exact rank contribution; `remaining_length_lt` proves strict wire-size decrease, and the complete result has at most `s+1` cells. The later rank loop uses these checked predicates; primal-edge deduplication, encoded objective emission, and composition with prime selection remain. `rankAccumulatorComputableInPolyTime` consumes both predicate bits, conditionally increments a unary count, and retains the complete remaining query in at most `2s` finite-machine steps for complete input length `s`. `rankIterationComputableInPolyTime` composes preparation, both predicates, and accumulation for the complete nonempty query/tally input with a checked polynomial bound. `RankIteration.rank_invariant`, `output_length_balance`, and `output_length_le` prove exact rank progress and nonexpansion of the entire retained state. `finish_one_eq_rank` and `finish_extracted_eq_relabelValue` identify its executable recursive specification with canonical relabelling, and `rankInitializationComputableInPolyTime` constructs its one-based starting state in `2s+2` steps while retaining the complete query. `rankControlComputableInPolyTime` tests nonemptiness while preserving the full state in `2s+2` steps, correctly distinguishing zero-valued fields; `rankEntryComputableInPolyTime` composes initialization and that test. `rankFinalizationComputableInPolyTime` returns the tally in `s+1` steps, with exact recursive-result semantics when the symbol list is empty. `RankLoopMachine.iteration_cycle` checks actual repeated-call control with exact `P(s)+2s+2t+4` cycle cost, and `exit_run` checks the empty exit. `RankLoop.outputsInTime` and `rankLoopComputableInPolyTime` prove total repeated computation in `(s+1)*(P(s)+4s+4)` steps for initial full-state length `s`. `canonicalRankComputableInPolyTime` composes initialization and returns the exact one-based rank from the original serialized target/symbol query; `canonicalRank_extracted_outputsInTime` identifies its result with the thesis relabelling. Constructing all such queries while retaining and relabelling the complete compiler sections remains pending, followed by primal-edge deduplication, objective emission, and final prime-selection composition. |
| `cor:signed-nphard` | Partial | `FixedPrimeHardness.fixed_prime_signed_decision_is_three_sat_hard_in_cell_model` proves the explicit \(p=5\) reduction, correctness, output size, and a quadratic unit-cell construction bound. A library-native `NP-hard` transfer from a formally NP-hard 3-SAT language is not present. |
| `cor:sudoku-polynomial-dyadic-hardness` | Pending | Formalise the positive multilinear \(p=2\) reduction and its complexity transfer. |
| `cor:sudoku-special-case` | Pending wrapper | The general all-different theorem supplies the mathematics, but the 81-cell peer graph, degree-20 bound, clue domains, and Sudoku equivalence have not been instantiated in Lean. |

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
Canonical relabelling, deduplicated graph construction, encoded objective
emission, and composition with prime selection remain.
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
local rank machine; constructing all rank queries while retaining and
relabelling the complete compiler sections remains open.

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
magnitudes are covered. Ranking this query while retaining the complete
compiler sections, binary rank emission, and the outer occurrence loop remain.

The full corollary remains **Partial**.

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
