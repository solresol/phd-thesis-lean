import PhdThesisLean.AllDifferentCSPOccurrenceEmit

/-!
# Complete one binary occurrence relabelling step

Compose query staging, canonical ranking, and binary record emission while
preserving the remaining occurrences, full symbols, scopes, and variable count.
The input is exactly the existing nonempty counted-symbol-section wire. This
supplies the body of the checked `AllDifferentCSPOccurrenceLoop` traversal.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace OccurrenceEmit

def step (input : OccurrenceQuery.Input) : Output := emit (OccurrenceQuery.ranked input)

theorem step_eq (input : OccurrenceQuery.Input) :
    step input = ((input.1.1, DomainSymbols.rank input.2.2 input.1.2), input.2) := rfl

theorem step_length_le (input : OccurrenceQuery.Input) :
    (outputFinEncoding.encode (step input)).length ≤ 2 * (OccurrenceQuery.inputEncode input).length + 6 := by
  exact (output_length_le _).trans (Nat.add_le_add_right (OccurrenceQuery.ranked_length_le input) 6)

end OccurrenceEmit

/-- Compute and emit the next binary rank record, charging query preparation,
rank iteration, conversion, and all composition transfers. -/
noncomputable def occurrenceStepComputableInPolyTime :
    @TM2ComputableInPolyTime OccurrenceQuery.Input OccurrenceEmit.Output
      OccurrenceQuery.inputFinEncoding OccurrenceEmit.outputFinEncoding OccurrenceEmit.step := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    occurrenceRankComputableInPolyTime occurrenceEmitComputableInPolyTime
  exact { composed with
    outputsFun := fun input => by
      simpa [Function.comp_def, OccurrenceEmit.step] using composed.outputsFun input }

namespace CountedOccurrenceStep

abbrev Input := CountedOccurrenceRank.Input
abbrev Output := (OccurrenceEmit.Output × List (List ℕ)) × ℕ

def sectionsFinEncoding : FinEncoding (OccurrenceEmit.Output × List (List ℕ)) :=
  LeanNPHardness.PairEncoding.finEncoding OccurrenceEmit.outputFinEncoding
    ScopeFieldSection.outputFinEncoding

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding sectionsFinEncoding finEncodingNatBool

def step (input : Input) : Output := ((OccurrenceEmit.step input.1.1, input.1.2), input.2)

def record (output : Output) : ℕ × ℕ := output.1.1.1

def remaining (output : Output) : CountedSymbolSections.Value :=
  ((output.1.1.2, output.1.2), output.2)

theorem remaining_step (input : Input) :
    remaining (step input) = CountedOccurrenceRank.remaining (CountedOccurrenceRank.step input) := rfl

/-- One record is removed from the query source; scopes, count, and all source
symbols are unchanged. Accumulated emitted output is deliberately separate. -/
theorem remaining_encoded_length_balance (input : Input) :
    (CountedSymbolSections.finEncoding.encode (remaining (step input))).length +
      (encodeNat input.1.1.1.1).length + (encodeNat input.1.1.1.2).length + 6 =
      (CountedOccurrenceRank.inputFinEncoding.encode input).length :=
  CountedOccurrenceRank.remaining_encoded_length_balance input

theorem remaining_encoded_length_lt (input : Input) :
    (CountedSymbolSections.finEncoding.encode (remaining (step input))).length <
      (CountedOccurrenceRank.inputFinEncoding.encode input).length :=
  CountedOccurrenceRank.remaining_encoded_length_lt input

theorem remaining_length (input : Input) :
    (remaining (step input)).1.1.1.length + 1 =
      (CountedOccurrenceRank.source input).1.1.1.length := rfl

/-- Splitting off the emitted record adds no cells to the complete state. -/
theorem output_length_eq_record_add_remaining (input : Input) :
    (outputFinEncoding.encode (step input)).length =
      (DomainOccurrenceFieldBlock.outputEncode (record (step input))).length +
        (CountedSymbolSections.finEncoding.encode (remaining (step input))).length := by
  simp [outputFinEncoding, sectionsFinEncoding, step, record, remaining,
    OccurrenceEmit.outputFinEncoding, CountedSymbolSections.finEncoding,
    CountedSymbolSections.sectionsFinEncoding, DomainOccurrenceFieldBlock.outputFinEncoding,
    Nat.add_assoc]

/-- The only change in total length is replacing the old symbol's binary
word by its rank's binary word; pair tags add no extra cells. -/
theorem output_length_balance (input : Input) :
    (outputFinEncoding.encode (step input)).length + (encodeNat input.1.1.1.2).length =
      (CountedOccurrenceRank.inputFinEncoding.encode input).length +
        (encodeNat (DomainSymbols.rank input.1.1.2.2 input.1.1.1.2)).length := by
  have hi := OccurrenceQuery.input_length input.1.1
  have ho := OccurrenceEmit.output_length (OccurrenceQuery.ranked input.1.1)
  simp only [outputFinEncoding, sectionsFinEncoding, step,
    CountedOccurrenceRank.inputFinEncoding, CountedOccurrenceRank.inputSectionsFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length]
  change (OccurrenceEmit.outputFinEncoding.encode (OccurrenceEmit.step input.1.1)).length + _ + _ + _ =
    (OccurrenceQuery.inputEncode input.1.1).length + _ + _ + _
  dsimp only [OccurrenceQuery.ranked] at ho
  simp only [DomainSymbolExtraction.finEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length,
    DomainFieldRow.outputFinEncoding, SourceOrderRawFields.finEncoding] at ho
  dsimp only [OccurrenceEmit.step, OccurrenceQuery.ranked]
  omega

/-- On a real nonempty input, the six existing format cells pay for the rank's
one-based offset. The complete binary result is at most twice the input. -/
theorem output_length_le (input : Input) :
    (outputFinEncoding.encode (step input)).length ≤
      2 * (CountedOccurrenceRank.inputFinEncoding.encode input).length := by
  have hb := output_length_balance input
  have hr := OccurrenceQuery.rank_le_length_add_one input.1.1.2.2 input.1.1.1.2
  have hs := OccurrenceQuery.symbols_length_le_wire input.1.1.2.2
  have hn := BinaryNatLists.encodeNat_length_le (DomainSymbols.rank input.1.1.2.2 input.1.1.1.2)
  have hi := OccurrenceQuery.input_length input.1.1
  have hwhole : (OccurrenceQuery.inputEncode input.1.1).length ≤
      (CountedOccurrenceRank.inputFinEncoding.encode input).length := by
    simp only [CountedOccurrenceRank.inputFinEncoding, CountedOccurrenceRank.inputSectionsFinEncoding,
      LeanNPHardness.PairEncoding.finEncoding_encode_length]
    change _ ≤ (OccurrenceQuery.inputEncode input.1.1).length + _ + _
    omega
  omega

theorem record_encoded_length_le (input : Input) :
    (DomainOccurrenceFieldBlock.outputEncode (record (step input))).length ≤
      2 * (CountedOccurrenceRank.inputFinEncoding.encode input).length := by
  have h := output_length_eq_record_add_remaining input
  have hb := output_length_le input
  omega

/-- This invariant applies at every suffix of the future loop, not only to
its initial complete compiler source. -/
theorem remaining_symbols (input : Input) :
    (remaining (step input)).1.1.2 = input.1.1.2.2 := rfl

theorem record_eq_relabelValue_of_symbols (C : RuntimeSystem) (input : Input)
    (symbols : input.1.1.2.2 = C.domains.flatten) :
    record (step input) = (input.1.1.1.1, C.toExplicitSystem.relabelValue input.1.1.1.2) := by
  change (input.1.1.1.1, DomainSymbols.rank input.1.1.2.2 input.1.1.1.2) = _
  rw [symbols, DomainSymbols.rank_flatten_eq_relabelValue]

/-- The concrete record agrees with the thesis relabelling whenever the
source is the compiler-produced counted section. -/
theorem record_eq_relabelValue (C : RuntimeSystem) (input : Input)
    (h : CountedOccurrenceRank.source input = CountedSymbolSections.ofRuntimeSystem C) :
    record (step input) = (input.1.1.1.1, C.toExplicitSystem.relabelValue input.1.1.1.2) :=
  CountedOccurrenceRank.step_eq_relabelValue C input h

/-- The emitted field block is exactly the structural domain record at the
original variable index and the thesis's canonical rank. -/
theorem record_encode_eq (C : RuntimeSystem) (input : Input)
    (h : CountedOccurrenceRank.source input = CountedSymbolSections.ofRuntimeSystem C) :
    DomainOccurrenceFieldBlock.outputEncode (record (step input)) =
      SourceOrderRawFields.encode [3, 0, input.1.1.1.1, C.toExplicitSystem.relabelValue input.1.1.1.2] := by
  rw [record_eq_relabelValue C input h]
  rfl

/-- Each actual emitted rank is positive and below the prime selected from
explicit domain-entry count, as required by the residual-objective semantics. -/
theorem record_rank_bounds (C : RuntimeSystem) (input : Input)
    (h : CountedOccurrenceRank.source input = CountedSymbolSections.ofRuntimeSystem C) :
    0 < (record (step input)).2 ∧ (record (step input)).2 < C.domainEntryPrime := by
  have hocc : input.1.1.1 :: input.1.1.2.1 =
      RuntimeStructuralView.indexedDomainOccurrences C.domains :=
    congrArg (fun sections : CountedSymbolSections.Value => sections.1.1.1) h
  have hmem : input.1.1.1.2 ∈ C.domains.flatten := by
    rw [← RuntimeStructuralView.indexedDomainOccurrences_values C.domains, ← hocc]
    simp
  have hsymbols : input.1.1.2.2 = C.domains.flatten := by
    exact (congrArg (fun sections : CountedSymbolSections.Value => sections.1.1.2) h).trans
      (CountedSymbolSections.symbols_ofRuntimeSystem C)
  change 0 < DomainSymbols.rank input.1.1.2.2 input.1.1.1.2 ∧
    DomainSymbols.rank input.1.1.2.2 input.1.1.1.2 < C.domainEntryPrime
  rw [hsymbols]
  exact ⟨by unfold DomainSymbols.rank; omega, DomainSymbols.rank_lt_domainEntryPrime C hmem⟩

end CountedOccurrenceStep

/-- Complete next-occurrence relabelling on the original nonempty counted
section wire, retaining scopes and variable count through checked adapters. -/
noncomputable def countedOccurrenceStepComputableInPolyTime :
    @TM2ComputableInPolyTime CountedOccurrenceStep.Input CountedOccurrenceStep.Output
      CountedOccurrenceRank.inputFinEncoding CountedOccurrenceStep.outputFinEncoding
      CountedOccurrenceStep.step := by
  let sections := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    OccurrenceQuery.inputFinEncoding OccurrenceEmit.outputFinEncoding
    ScopeFieldSection.outputFinEncoding _ occurrenceStepComputableInPolyTime
  exact LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    CountedOccurrenceRank.inputSectionsFinEncoding CountedOccurrenceStep.sectionsFinEncoding
    finEncodingNatBool _ sections

#print axioms occurrenceStepComputableInPolyTime
#print axioms CountedOccurrenceStep.remaining_encoded_length_balance
#print axioms CountedOccurrenceStep.output_length_eq_record_add_remaining
#print axioms CountedOccurrenceStep.output_length_balance
#print axioms CountedOccurrenceStep.output_length_le
#print axioms CountedOccurrenceStep.record_encoded_length_le
#print axioms CountedOccurrenceStep.record_eq_relabelValue_of_symbols
#print axioms CountedOccurrenceStep.record_eq_relabelValue
#print axioms CountedOccurrenceStep.record_encode_eq
#print axioms CountedOccurrenceStep.record_rank_bounds
#print axioms countedOccurrenceStepComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
