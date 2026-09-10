import PhdThesisLean.AllDifferentCSPCountedSections

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-!
# Assemble the variable header and both structural sections

The payload encoding uses the upstream exhaustion-delimited counted-row
codec: the first row is the singleton variable header, followed by all tagged
records. Every row length and record tag is checked. Only the redundant outer
row count is absent. Adding that count and converting to the existing framed
Boolean encoding remain distinct machine obligations.
-/

namespace RuntimeStructuralView

/-- Exact structural rows, checked through exhaustion without an outer row count. -/
def payloadEncode (view : AllDifferentCSPEncoding.RuntimeStructuralView) :
    List (Option Bool) :=
  DomainFieldSection.rowPayloadEncode view.toNatLists

def payloadDecode (input : List (Option Bool)) :
    Option AllDifferentCSPEncoding.RuntimeStructuralView :=
  (DomainFieldSection.rowPayloadDecode input).bind
    AllDifferentCSPEncoding.RuntimeStructuralView.ofNatLists

@[simp]
theorem payloadDecode_encode (view : AllDifferentCSPEncoding.RuntimeStructuralView) :
    payloadDecode (payloadEncode view) = some view := by
  simp [payloadDecode, payloadEncode]

/-- This encodes the full semantic view, including zero or trailing empty variables. -/
def payloadFinEncoding : FinEncoding AllDifferentCSPEncoding.RuntimeStructuralView where
  Γ := Option Bool
  encode := payloadEncode
  decode := payloadDecode
  decode_encode := payloadDecode_encode
  ΓFin := inferInstance

theorem payloadEncode_injective : Function.Injective payloadEncode := by
  intro left right heq
  have h := congrArg payloadDecode heq
  simpa using h

private theorem rowPayloadEncode_append (left right : List (List ℕ)) :
    DomainFieldSection.rowPayloadEncode (left ++ right) =
      DomainFieldSection.rowPayloadEncode left ++ DomainFieldSection.rowPayloadEncode right := by
  simp [DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
    SourceOrderRawFields.encode]

private theorem domainPayload (occurrences : List (ℕ × ℕ)) :
    DomainFieldSection.rowPayloadEncode
      (occurrences.map fun occurrence => [0, occurrence.1, occurrence.2]) =
      DomainFieldRow.outputEncode occurrences := by
  induction occurrences with
  | nil => rfl
  | cons occurrence occurrences ih =>
      simpa [DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
        DomainFieldRow.outputEncode, DomainOccurrenceFieldBlock.outputEncode,
        SourceOrderRawFields.encode] using ih

/-- Assembly requires just the singleton variable header and the two existing
wire streams. Numeric payloads, duplicates, and empty scopes are unchanged. -/
theorem payloadEncode_toStructuralView (sections : CountedSections.Value) :
    payloadEncode (CountedSections.toStructuralView sections) =
      [none, some true, none] ++ (encodeNat sections.2).map some ++
      DomainFieldRow.outputEncode sections.1.1 ++ ScopeFieldSection.outputEncode sections.1.2 := by
  unfold payloadEncode CountedSections.toStructuralView
  simp only [AllDifferentCSPEncoding.RuntimeStructuralView.toNatLists,
    List.map_append, List.map_map, Function.comp_def,
    RuntimeStructuralRecord.toNatList]
  rw [show ([sections.2] ::
      (sections.1.1.map (fun occurrence => [0, occurrence.1, occurrence.2]) ++
        sections.1.2.map (fun entries => 1 :: entries))) =
      [[sections.2]] ++ (sections.1.1.map (fun occurrence => [0, occurrence.1, occurrence.2]) ++
        sections.1.2.map (fun entries => 1 :: entries)) by rfl]
  rw [rowPayloadEncode_append, rowPayloadEncode_append, domainPayload,
    ← ScopeFieldSection.outputEncode_eq_taggedRowPayload]
  simp [DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
    SourceOrderRawFields.encode, encodeNat, encodeNum, encodePosNum, List.append_assoc]

/-- The merged output adds exactly three fixed header cells to the complete
counted-section input; all existing encoded numeric fields are retained. -/
theorem payloadEncode_toStructuralView_length (sections : CountedSections.Value) :
    (payloadEncode (CountedSections.toStructuralView sections)).length =
      (CountedSections.finEncoding.encode sections).length + 3 := by
  rw [payloadEncode_toStructuralView]
  simp [CountedSections.finEncoding, CountedSections.sectionsFinEncoding,
    DomainFieldRow.outputFinEncoding, ScopeFieldSection.outputFinEncoding,
    finEncodingNatBool, encodingNatBool]
  omega

/-- Exact boundary to the existing raw/framed path: prepend the outer row
count, then reverse all cells. This equation alone does not construct that count. -/
theorem raw_encode_eq_count_payload (view : AllDifferentCSPEncoding.RuntimeStructuralView) :
    rawFinEncoding.encode view =
      (SourceOrderRawFields.encode [view.records.length + 1] ++ payloadEncode view).reverse := by
  change RawNatLists.encode view.toNatLists = _
  apply List.reverse_injective
  simp only [List.reverse_reverse]
  change SourceOrderRawNatLists.encode view.toNatLists = _
  rw [← DomainFieldSection.inputEncode_eq_sourceOrderRawNatLists]
  simp [DomainFieldSection.inputEncode, DomainFieldSection.inputFields,
    payloadEncode, DomainFieldSection.rowPayloadEncode, SourceOrderRawFields.encode,
    AllDifferentCSPEncoding.RuntimeStructuralView.toNatLists]

private theorem fields_length_le (fields : List ℕ) :
    (SourceOrderRawFields.encode fields).length ≤
      (fields.map BinaryNatLists.natWireSize).sum := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      simp [SourceOrderRawFields.encode, BinaryNatLists.natWireSize] at *
      omega

private theorem rows_length_le (rows : List (List ℕ)) :
    (DomainFieldSection.rowPayloadEncode rows).length ≤
      (rows.map BinaryNatLists.listWireSize).sum := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have hf := fields_length_le row
      simp [DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
        SourceOrderRawFields.encode, BinaryNatLists.listWireSize,
        BinaryNatLists.natWireSize] at *
      omega

/-- Every raw payload bit/delimiter is charged to its framed counterpart.
The comparison uses encoded lengths, not the magnitudes of natural values. -/
theorem payloadEncode_length_le_encodedSize (view : AllDifferentCSPEncoding.RuntimeStructuralView) :
    (payloadEncode view).length ≤ view.encodedSize := by
  rw [AllDifferentCSPEncoding.RuntimeStructuralView.encodedSize_eq_wireSize]
  have h := rows_length_le view.toNatLists
  simp only [BinaryNatLists.wireSize]
  exact h.trans (Nat.le_add_left _ _)

/-- The missing outer row count includes the singleton header and is bounded
by the actual payload length, including for an empty record list. -/
theorem rowCount_le_payloadEncode_length (view : AllDifferentCSPEncoding.RuntimeStructuralView) :
    view.records.length + 1 ≤ (payloadEncode view).length := by
  have h := ScopeFieldSection.length_le_rowPayloadEncode_length view.toNatLists
  simpa [payloadEncode, AllDifferentCSPEncoding.RuntimeStructuralView.toNatLists] using h

/-- Quadratic payload-size bound in the complete compact Boolean input length. -/
theorem payloadEncode_ofRuntimeSystem_length_le_quadratic (C : RuntimeSystem) :
    (payloadEncode (AllDifferentCSPEncoding.RuntimeStructuralView.ofRuntimeSystem C)).length ≤
      32 * (C.encodedSize + 1) ^ 2 :=
  (payloadEncode_length_le_encodedSize _).trans
    (AllDifferentCSPEncoding.RuntimeStructuralView.ofRuntimeSystem_encodedSize_le_quadratic C)

/-- The same bound in the actual compiler input, including its checked unary
occurrence header. This bounds the output of the composed assembly machine. -/
theorem payloadEncode_ofRuntimeSystem_length_le_compilerInput_quadratic (C : RuntimeSystem) :
    (payloadEncode (AllDifferentCSPEncoding.RuntimeStructuralView.ofRuntimeSystem C)).length ≤
      32 * ((RuntimeCompilerInput.encode C).length + 1) ^ 2 :=
  (payloadEncode_length_le_encodedSize _).trans
    (AllDifferentCSPEncoding.RuntimeStructuralView.ofRuntimeSystem_encodedSize_le_compilerInput_quadratic C)

end RuntimeStructuralView

#print axioms RuntimeStructuralView.payloadDecode_encode
#print axioms RuntimeStructuralView.payloadEncode_injective
#print axioms RuntimeStructuralView.payloadEncode_toStructuralView
#print axioms RuntimeStructuralView.payloadEncode_toStructuralView_length
#print axioms RuntimeStructuralView.raw_encode_eq_count_payload
#print axioms RuntimeStructuralView.payloadEncode_length_le_encodedSize
#print axioms RuntimeStructuralView.rowCount_le_payloadEncode_length
#print axioms RuntimeStructuralView.payloadEncode_ofRuntimeSystem_length_le_quadratic
#print axioms RuntimeStructuralView.payloadEncode_ofRuntimeSystem_length_le_compilerInput_quadratic

end PhdThesisLean.AllDifferentCSPMachine
