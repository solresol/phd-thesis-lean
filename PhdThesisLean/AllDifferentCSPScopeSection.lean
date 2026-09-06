import PhdThesisLean.AllDifferentCSPMachine

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability
open Turing
open PhdThesisLean.AllDifferentCSPEncoding

/-!
# Checked complete scope-section interface

Scope sections use the same counted-row source format as domain sections.
Reuse that parser and its concrete outer-count removal machine. The output
retains each scope as one tagged row, including empty scopes, repeated scopes,
and repeated entries. Its decoder rechecks the row lengths and every tag.

`AllDifferentCSPScopeMachine` implements and composes the repeated-scope
machine against these exact encodings, with a quadratic bit-level time bound.
The structural assembly identities here specify the remaining executable
header staging and complete structural-machine assembly.
-/

namespace ScopeFieldSection

/-- The complete counted scope list has the existing nested-row encoding. -/
abbrev inputFinEncoding : FinEncoding (List (List ℕ)) :=
  DomainFieldSection.inputFinEncoding

/-- The scope driver consumes the existing exhaustion-delimited row payload.
The same checked parser preserves all row boundaries, even for empty scopes. -/
abbrev rowPayloadFinEncoding : FinEncoding (List (List ℕ)) :=
  DomainFieldSection.rowPayloadFinEncoding

/-- Complete tagged scope output in source order, without an outer count. -/
def outputEncode (scopes : List (List ℕ)) : List (Option Bool) :=
  scopes.flatMap ScopeFieldBlock.outputEncode

/-- Remove a checked scope tag after the shared parser has checked row bounds. -/
def untag : List ℕ → Option (List ℕ)
  | 1 :: entries => some entries
  | _ => none

/-- Decode the entire tagged scope section through exact row exhaustion. -/
def outputDecode (input : List (Option Bool)) : Option (List (List ℕ)) := do
  let rows ← DomainFieldSection.rowPayloadDecode input
  rows.mapM untag

/-- Tagged scopes are ordinary count-prefixed rows with one extra entry. -/
theorem outputEncode_eq_taggedRowPayload (scopes : List (List ℕ)) :
    outputEncode scopes = DomainFieldSection.rowPayloadEncode
      (scopes.map fun entries => 1 :: entries) := by
  induction scopes with
  | nil => rfl
  | cons entries scopes ih =>
      simpa [outputEncode, ScopeFieldBlock.outputEncode,
        DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
        SourceOrderRawFields.encode] using ih

private theorem mapM_untag_tagged (scopes : List (List ℕ)) :
    (scopes.map fun entries => 1 :: entries).mapM untag = some scopes := by
  induction scopes with
  | nil => rfl
  | cons entries scopes ih => simp [untag, ih]

/-- Every scope and every entry is recovered exactly, including empty rows. -/
@[simp]
theorem outputDecode_encode (scopes : List (List ℕ)) :
    outputDecode (outputEncode scopes) = some scopes := by
  rw [outputEncode_eq_taggedRowPayload]
  simp only [outputDecode, DomainFieldSection.rowPayloadDecode_encode]
  exact mapM_untag_tagged scopes

/-- Checked finite-alphabet output interface for the whole scope driver. -/
def outputFinEncoding : FinEncoding (List (List ℕ)) where
  Γ := Option Bool
  encode := outputEncode
  decode := outputDecode
  decode_encode := outputDecode_encode
  ΓFin := inferInstance

/-- No scope boundary, repetition, or entry is lost by the output encoding. -/
theorem outputEncode_injective : Function.Injective outputEncode := by
  intro left right heq
  have hdecoded := congrArg outputDecode heq
  simpa using hdecoded

/-- A counted empty row cannot be mistaken for an empty tagged scope. -/
theorem outputDecode_rejects_missing_tag (rows : List (List ℕ)) :
    outputDecode (DomainFieldSection.rowPayloadEncode ([] :: rows)) = none := by
  simp [outputDecode, untag]

/-- A domain tag or any other incorrect tag cannot be decoded as a scope. -/
theorem outputDecode_rejects_wrong_tag (tag : ℕ) (htag : tag ≠ 1)
    (entries : List ℕ) (rows : List (List ℕ)) :
    outputDecode
      (DomainFieldSection.rowPayloadEncode ((tag :: entries) :: rows)) = none := by
  simp [outputDecode, untag, htag]

/-- The whole scope output is exactly the scope part of the structural target. -/
theorem outputEncode_eq_structuralFields (scopes : List (List ℕ)) :
    outputEncode scopes =
      SourceOrderRawFields.encode (StructuralFieldStream.scopeFields scopes) := by
  induction scopes with
  | nil => rfl
  | cons entries scopes ih =>
      simpa [outputEncode, ScopeFieldBlock.outputEncode,
        SourceOrderRawFields.encode, StructuralFieldStream.scopeFields] using ih

/-- Each source row is exactly one already checked local scope input. -/
theorem rowPayloadEncode_eq_block_inputs (scopes : List (List ℕ)) :
    DomainFieldSection.rowPayloadEncode scopes =
      scopes.flatMap ScopeFieldBlock.inputEncode := by
  induction scopes with
  | nil => rfl
  | cons entries scopes ih =>
      simpa [DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
        ScopeFieldBlock.inputEncode, SourceOrderRawFields.encode] using ih

/-- Adding one tag and incrementing one length field costs at most three
raw bit-or-delimiter cells per scope, independent of entry magnitudes. -/
theorem outputEncode_length_le_payload_add (scopes : List (List ℕ)) :
    (outputEncode scopes).length ≤
      (DomainFieldSection.rowPayloadEncode scopes).length + 3 * scopes.length := by
  rw [rowPayloadEncode_eq_block_inputs]
  induction scopes with
  | nil => simp [outputEncode]
  | cons entries scopes ih =>
      have hblock := ScopeFieldBlock.outputEncode_length_le entries
      simp only [outputEncode, List.flatMap_cons, List.length_append,
        List.length_cons] at *
      omega

/-- Every scope, including an empty one, occupies at least its row delimiter. -/
theorem length_le_rowPayloadEncode_length (scopes : List (List ℕ)) :
    scopes.length ≤ (DomainFieldSection.rowPayloadEncode scopes).length := by
  rw [rowPayloadEncode_eq_block_inputs]
  induction scopes with
  | nil => simp
  | cons entries scopes ih =>
      have hblock : 1 ≤ (ScopeFieldBlock.inputEncode entries).length := by
        simp [ScopeFieldBlock.inputEncode, SourceOrderRawFields.encode]
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega

/-- The full output is linear in the actual encoded scope payload length.
This is an output-size bound, not a running-time theorem for the scope loop. -/
theorem outputEncode_length_le_linear (scopes : List (List ℕ)) :
    (outputEncode scopes).length ≤
      4 * (rowPayloadFinEncoding.encode scopes).length := by
  have hout := outputEncode_length_le_payload_add scopes
  have hcount := length_le_rowPayloadEncode_length scopes
  change (outputEncode scopes).length ≤
    4 * (DomainFieldSection.rowPayloadEncode scopes).length
  omega

/-- The same linear bound holds against the complete counted section input. -/
theorem outputEncode_length_le_input_linear (scopes : List (List ℕ)) :
    (outputEncode scopes).length ≤
      4 * (inputFinEncoding.encode scopes).length := by
  have hout := outputEncode_length_le_linear scopes
  have hinput := DomainFieldSection.rowPayloadEncode_length_le_inputEncode_length scopes
  change (outputEncode scopes).length ≤
    4 * (DomainFieldSection.inputEncode scopes).length
  change (outputEncode scopes).length ≤
    4 * (DomainFieldSection.rowPayloadEncode scopes).length at hout
  omega

end ScopeFieldSection

/-- Reuse the concrete linear-time counted-row header-removal machine on the
scope section. It preserves the entire structured scope list in at most
`2s + 1` steps for complete section wire length `s`. -/
noncomputable def scopeRowPayloadStructuredComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ)) (List (List ℕ))
      ScopeFieldSection.inputFinEncoding
      ScopeFieldSection.rowPayloadFinEncoding id :=
  domainRowPayloadStructuredComputableInPolyTime

namespace StructuralFieldStream

/-- Exact count and variable headers preceding the two structural sections.
The outer count includes the singleton variable-header row. -/
def headerEncode (C : RuntimeSystem) : List (Option Bool) :=
  SourceOrderRawFields.encode
    [1 + C.domainEntryCount + C.scopes.length, 1, C.domains.length]

/-- The full structural output consists of its explicit headers and the
already specified complete domain and scope outputs, in that order. -/
theorem encode_eq_header_sections (C : RuntimeSystem) :
    encode C = headerEncode C ++ DomainFieldSection.outputEncode C.domains ++
      ScopeFieldSection.outputEncode C.scopes := by
  rw [DomainFieldSection.outputEncode_eq_structuralFields,
    ScopeFieldSection.outputEncode_eq_structuralFields]
  simp [encode, ofRuntimeSystem, headerEncode, SourceOrderRawFields.encode,
    List.append_assoc]

/-- Staging the scope section, domain section, and headers in reverse order
is exactly the checked raw structural-view output, ready for framing. -/
theorem raw_encode_eq_reversed_sections (C : RuntimeSystem) :
    RuntimeStructuralView.rawFinEncoding.encode
        (RuntimeStructuralView.ofRuntimeSystem C) =
      (ScopeFieldSection.outputEncode C.scopes).reverse ++
        (DomainFieldSection.outputEncode C.domains).reverse ++
        (headerEncode C).reverse := by
  change RawNatLists.encode (RuntimeStructuralView.ofRuntimeSystem C).toNatLists = _
  rw [← encode_reverse_eq_raw, encode_eq_header_sections]
  simp [List.reverse_append, List.append_assoc]

end StructuralFieldStream

#print axioms ScopeFieldSection.outputDecode_encode
#print axioms ScopeFieldSection.outputEncode_injective
#print axioms ScopeFieldSection.outputDecode_rejects_missing_tag
#print axioms ScopeFieldSection.outputDecode_rejects_wrong_tag
#print axioms ScopeFieldSection.outputEncode_length_le_linear
#print axioms ScopeFieldSection.outputEncode_length_le_input_linear
#print axioms scopeRowPayloadStructuredComputableInPolyTime
#print axioms StructuralFieldStream.encode_eq_header_sections
#print axioms StructuralFieldStream.raw_encode_eq_reversed_sections

end PhdThesisLean.AllDifferentCSPMachine
