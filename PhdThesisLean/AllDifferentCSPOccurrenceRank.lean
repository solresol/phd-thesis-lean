import PhdThesisLean.AllDifferentCSPOccurrenceQuery

/-!
# Rank the next occurrence while retaining compiler sections

Query preparation and the complete canonical-rank machine compose through the
upstream pair adapter. The scopes, variable count, remaining occurrences, and
full symbol list survive. The result rank is unary; `AllDifferentCSPOccurrenceEmit`
and `AllDifferentCSPOccurrenceStep` supply and compose binary record emission.
`AllDifferentCSPOccurrenceLoop` supplies the complete repeated traversal;
`AllDifferentCSPRelabelling` composes it from the actual compiler input.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace OccurrenceQuery

abbrev Ranked := ℕ × Retained

def rankedFinEncoding : FinEncoding Ranked :=
  LeanNPHardness.PairEncoding.finEncoding unaryFinEncodingNat retainedFinEncoding

def ranked (input : Input) : Ranked :=
  (DomainSymbols.rank input.2.2 input.1.2, input.1.1, input.2)

/-- An actual rank is bounded by explicit occurrences, even for arbitrarily
large symbol values or a target absent from the list. -/
theorem rank_le_length_add_one (symbols : List ℕ) (value : ℕ) :
    DomainSymbols.rank symbols value ≤ symbols.length + 1 := by
  have h := RankIteration.finish_le_count_add_length value symbols 1
  rw [RankIteration.finish_one_eq_rank] at h
  omega

theorem symbols_length_le_wire (symbols : List ℕ) :
    symbols.length ≤ (SourceOrderRawFields.encode symbols).length := by
  induction symbols with
  | nil => simp [SourceOrderRawFields.encode]
  | cons value symbols ih =>
      simp only [SourceOrderRawFields.encode, List.flatMap_cons, List.length_append,
        List.length_cons, List.length_map] at *
      omega

/-- The unary rank and complete retained source have a linear size bound. -/
theorem ranked_length_le (input : Input) :
    (rankedFinEncoding.encode (ranked input)).length ≤ 2 * (inputEncode input).length := by
  have hr := rank_le_length_add_one input.2.2 input.1.2
  have hs := symbols_length_le_wire input.2.2
  rw [input_length]
  simp only [rankedFinEncoding, ranked, retainedFinEncoding,
    DomainSymbolExtraction.finEncoding, LeanNPHardness.PairEncoding.finEncoding_encode_length]
  simp only [unaryFinEncodingNat, unaryEncodeNat_eq_replicate_true, List.length_replicate,
    finEncodingNatBool, encodingNatBool, DomainFieldRow.outputFinEncoding,
    SourceOrderRawFields.finEncoding]
  omega

/-- The saved index and all remaining occurrences and symbols are unchanged. -/
theorem ranked_retains (input : Input) :
    (ranked input).2 = (input.1.1, input.2) := rfl

theorem remaining_occurrences_length (input : Input) :
    (ranked input).2.2.1.length + 1 = (source input).1.length := rfl

/-- Exact thesis relabelling for any occurrence selected from the retained
compiler source. The premise identifies the complete source symbol list. -/
theorem ranked_eq_relabelValue (C : RuntimeSystem) (input : Input)
    (symbols : input.2.2 = (CountedSymbolSections.ofRuntimeSystem C).1.1.2) :
    ((ranked input).2.1, (ranked input).1) =
      (input.1.1, C.toExplicitSystem.relabelValue input.1.2) := by
  simp only [ranked, symbols, CountedSymbolSections.rank_symbols_eq_relabelValue]

example : ranked ((4, 42), [(5, 7)], [100, 7, 100, 42, 7]) =
    (2, 4, [(5, 7)], [100, 7, 100, 42, 7]) := by decide
example : ranked ((0, 0), [], [0, 0]) = (1, 0, [], [0, 0]) := by decide

end OccurrenceQuery

/-- Prepare and rank the head value, preserving its variable index, the exact
remaining occurrence stream, and the complete symbol list. All copies and
transfers are part of the composed polynomial, not just the rank body. -/
noncomputable def occurrenceRankComputableInPolyTime :
    @TM2ComputableInPolyTime OccurrenceQuery.Input OccurrenceQuery.Ranked
      OccurrenceQuery.inputFinEncoding OccurrenceQuery.rankedFinEncoding OccurrenceQuery.ranked := by
  let retainedRank := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    DomainSymbolMembership.finEncoding unaryFinEncodingNat OccurrenceQuery.retainedFinEncoding
    (fun query => DomainSymbols.rank query.2 query.1) canonicalRankComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _
    occurrenceQueryComputableInPolyTime retainedRank
  exact { composed with
    outputsFun := fun input => by
      simpa [Function.comp_def, OccurrenceQuery.prepare, OccurrenceQuery.ranked,
        OccurrenceQuery.outputFinEncoding, OccurrenceQuery.rankedFinEncoding] using
        composed.outputsFun input }

namespace CountedOccurrenceRank

abbrev Input := (OccurrenceQuery.Input × List (List ℕ)) × ℕ
abbrev Output := (OccurrenceQuery.Ranked × List (List ℕ)) × ℕ

def inputSectionsFinEncoding : FinEncoding (OccurrenceQuery.Input × List (List ℕ)) :=
  LeanNPHardness.PairEncoding.finEncoding OccurrenceQuery.inputFinEncoding
    ScopeFieldSection.outputFinEncoding

def outputSectionsFinEncoding : FinEncoding (OccurrenceQuery.Ranked × List (List ℕ)) :=
  LeanNPHardness.PairEncoding.finEncoding OccurrenceQuery.rankedFinEncoding
    ScopeFieldSection.outputFinEncoding

def inputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding inputSectionsFinEncoding finEncodingNatBool

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding outputSectionsFinEncoding finEncodingNatBool

def source (input : Input) : CountedSymbolSections.Value :=
  ((OccurrenceQuery.source input.1.1, input.1.2), input.2)

def step (input : Input) : Output :=
  ((OccurrenceQuery.ranked input.1.1, input.1.2), input.2)

/-- No extra header or pre-split query is assumed: this is exactly the existing
counted-symbol-section wire, with nonemptiness checked by the decoder. -/
theorem input_encode_eq_source (input : Input) :
    inputFinEncoding.encode input = CountedSymbolSections.finEncoding.encode (source input) := rfl

theorem retains_scopes_and_count (input : Input) :
    ((step input).1.2, (step input).2) = ((source input).1.2, (source input).2) := rfl

/-- Forgetting the emitted index/rank leaves exactly the next full section
state, with the complete symbol list retained for the next query. -/
def remaining (output : Output) : CountedSymbolSections.Value :=
  ((output.1.1.2.2, output.1.2), output.2)

theorem remaining_step (input : Input) :
    remaining (step input) = ((input.1.1.2, input.1.2), input.2) := rfl

theorem remaining_length (input : Input) :
    (remaining (step input)).1.1.1.length + 1 = (source input).1.1.1.length := rfl

/-- The next query source strictly shrinks in actual encoded length, charging
all six record-format cells as well as the removed index and value bits. -/
theorem remaining_encoded_length_balance (input : Input) :
    (CountedSymbolSections.finEncoding.encode (remaining (step input))).length +
      (encodeNat input.1.1.1.1).length + (encodeNat input.1.1.1.2).length + 6 =
      (inputFinEncoding.encode input).length := by
  have h := OccurrenceQuery.input_length input.1.1
  simp only [inputFinEncoding, inputSectionsFinEncoding, CountedSymbolSections.finEncoding,
    CountedSymbolSections.sectionsFinEncoding, remaining_step,
    DomainSymbolExtraction.finEncoding, LeanNPHardness.PairEncoding.finEncoding_encode_length]
  change (DomainFieldRow.outputEncode input.1.1.2.1).length +
      (SourceOrderRawFields.encode input.1.1.2.2).length + _ + _ + _ + _ + 6 =
      (OccurrenceQuery.inputEncode input.1.1).length + _ + _
  omega

theorem remaining_encoded_length_lt (input : Input) :
    (CountedSymbolSections.finEncoding.encode (remaining (step input))).length <
      (inputFinEncoding.encode input).length := by
  have h := remaining_encoded_length_balance input
  omega

theorem output_length_le (input : Input) :
    (outputFinEncoding.encode (step input)).length ≤
      2 * (inputFinEncoding.encode input).length := by
  have h := OccurrenceQuery.ranked_length_le input.1.1
  simp only [outputFinEncoding, inputFinEncoding, inputSectionsFinEncoding,
    outputSectionsFinEncoding, step, LeanNPHardness.PairEncoding.finEncoding_encode_length]
  change _ ≤ 2 * ((OccurrenceQuery.inputEncode input.1.1).length + _ + _)
  omega

/-- The emitted pair agrees with the thesis's canonical relabelling whenever
the checked section source is the compiler-produced source. -/
theorem step_eq_relabelValue (C : RuntimeSystem) (input : Input)
    (h : source input = CountedSymbolSections.ofRuntimeSystem C) :
    ((step input).1.1.2.1, (step input).1.1.1) =
      (input.1.1.1.1, C.toExplicitSystem.relabelValue input.1.1.1.2) := by
  apply OccurrenceQuery.ranked_eq_relabelValue
  exact congrArg (fun sections : CountedSymbolSections.Value => sections.1.1.2) h

end CountedOccurrenceRank

/-- One complete rank step on the original nonempty section wire, retaining
scopes and the original variable count through upstream checked adapters. -/
noncomputable def countedOccurrenceRankComputableInPolyTime :
    @TM2ComputableInPolyTime CountedOccurrenceRank.Input CountedOccurrenceRank.Output
      CountedOccurrenceRank.inputFinEncoding CountedOccurrenceRank.outputFinEncoding
      CountedOccurrenceRank.step := by
  let sections := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    OccurrenceQuery.inputFinEncoding OccurrenceQuery.rankedFinEncoding
    ScopeFieldSection.outputFinEncoding _ occurrenceRankComputableInPolyTime
  exact LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    CountedOccurrenceRank.inputSectionsFinEncoding CountedOccurrenceRank.outputSectionsFinEncoding
    finEncodingNatBool _ sections

#print axioms OccurrenceQuery.ranked_length_le
#print axioms OccurrenceQuery.ranked_eq_relabelValue
#print axioms occurrenceRankComputableInPolyTime
#print axioms CountedOccurrenceRank.input_encode_eq_source
#print axioms CountedOccurrenceRank.remaining_encoded_length_balance
#print axioms CountedOccurrenceRank.remaining_encoded_length_lt
#print axioms CountedOccurrenceRank.remaining_length
#print axioms CountedOccurrenceRank.output_length_le
#print axioms CountedOccurrenceRank.step_eq_relabelValue
#print axioms countedOccurrenceRankComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
