import PhdThesisLean.AllDifferentCSPVariableHeader

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-!
# Process both sections while retaining the variable header

The upstream pair-left API carries the saved binary variable count through
source splitting, domain expansion, and scope processing. The resulting
checked tuple determines the exact structural view, even for trailing empty
domains. Its record count is bounded by its actual encoded length. Constructing
that count and merging the tuple into the raw structural encoding still need
a finite-machine proof; the assembly identities below specify that boundary.
-/

namespace CountedSections

abbrev Sections := List (ℕ × ℕ) × List (List ℕ)
abbrev Value := Sections × ℕ

def sectionsFinEncoding : FinEncoding Sections :=
  LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
    ScopeFieldSection.outputFinEncoding

/-- Both checked tagged sections, followed by the retained standard binary count. -/
def finEncoding : FinEncoding Value :=
  LeanNPHardness.PairEncoding.finEncoding sectionsFinEncoding finEncodingNatBool

def ofRuntimeSystem (C : RuntimeSystem) : Value :=
  ((RuntimeStructuralView.indexedDomainOccurrences C.domains, C.scopes), C.domains.length)

/-- The retained variable count and exact section values suffice for reconstruction. -/
def toStructuralView (sections : Value) : RuntimeStructuralView where
  variableCount := sections.2
  records := sections.1.1.map (fun occurrence =>
    RuntimeStructuralRecord.domainOccurrence occurrence.1 occurrence.2) ++
    sections.1.2.map RuntimeStructuralRecord.scope

theorem toStructuralView_ofRuntimeSystem (C : RuntimeSystem) :
    toStructuralView (ofRuntimeSystem C) = RuntimeStructuralView.ofRuntimeSystem C := rfl

/-- Count emitted records, retaining repetitions and empty scopes. -/
def recordCount (sections : Value) : ℕ := sections.1.1.length + sections.1.2.length

theorem recordCount_ofRuntimeSystem (C : RuntimeSystem) :
    recordCount (ofRuntimeSystem C) = C.domainEntryCount + C.scopes.length := by
  simp [recordCount, ofRuntimeSystem, RuntimeSystem.domainEntryCount]

private theorem domainCount_le_output_length (occurrences : List (ℕ × ℕ)) :
    occurrences.length ≤ (DomainFieldRow.outputEncode occurrences).length := by
  induction occurrences with
  | nil => simp [DomainFieldRow.outputEncode]
  | cons occurrence occurrences ih =>
      simp [DomainFieldRow.outputEncode, DomainOccurrenceFieldBlock.outputEncode,
        SourceOrderRawFields.encode] at *
      omega

private theorem scopeCount_le_output_length (scopes : List (List ℕ)) :
    scopes.length ≤ (ScopeFieldSection.outputEncode scopes).length := by
  induction scopes with
  | nil => simp [ScopeFieldSection.outputEncode]
  | cons scope scopes ih =>
      simp [ScopeFieldSection.outputEncode, ScopeFieldBlock.outputEncode,
        SourceOrderRawFields.encode] at *
      omega

/-- The next counting pass may charge each record to its own encoded cells,
independently of the numerical magnitude of any entry or variable index. -/
theorem recordCount_le_encode_length (sections : Value) :
    recordCount sections ≤ (finEncoding.encode sections).length := by
  have hd := domainCount_le_output_length sections.1.1
  have hs := scopeCount_le_output_length sections.1.2
  simp only [finEncoding, sectionsFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length]
  change recordCount sections ≤ (DomainFieldRow.outputEncode sections.1.1).length +
    (ScopeFieldSection.outputEncode sections.1.2).length + _
  dsimp only [recordCount]
  omega

/-- The exact still-to-be-emitted structural header, including its singleton row. -/
def headerEncode (sections : Value) : List (Option Bool) :=
  SourceOrderRawFields.encode [1 + recordCount sections, 1, sections.2]

theorem headerEncode_ofRuntimeSystem (C : RuntimeSystem) :
    headerEncode (ofRuntimeSystem C) = StructuralFieldStream.headerEncode C := by
  rw [headerEncode, recordCount_ofRuntimeSystem]
  simp [ofRuntimeSystem, StructuralFieldStream.headerEncode, Nat.add_assoc]

/-- Exact assembly/reversal contract on the internally constructed tuple.
This is an encoding identity, not the running-time proof of the merge pass. -/
theorem raw_encode_eq_sections (C : RuntimeSystem) :
    RuntimeStructuralView.rawFinEncoding.encode
        (toStructuralView (ofRuntimeSystem C)) =
      (ScopeFieldSection.outputEncode (ofRuntimeSystem C).1.2).reverse ++
      (DomainFieldRow.outputEncode (ofRuntimeSystem C).1.1).reverse ++
      (headerEncode (ofRuntimeSystem C)).reverse := by
  rw [toStructuralView_ofRuntimeSystem, headerEncode_ofRuntimeSystem]
  exact StructuralFieldStream.raw_encode_eq_reversed_sections C

end CountedSections

/-- Both structural section passes, starting from the already normalized raw source. -/
noncomputable def sourceProcessedSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem CountedSections.Sections
      RuntimeSourceSections.inputFinEncoding CountedSections.sectionsFinEncoding
      (fun C => (RuntimeStructuralView.indexedDomainOccurrences C.domains, C.scopes)) := by
  let domains := compositionComputableInPolyTime _ _ _ _ _
    sourceSectionsComputableInPolyTime pairedDomainSectionComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _
    domains pairedScopeSectionComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa [Function.comp_def, RuntimeSourceSections.split,
        CountedSections.sectionsFinEncoding] using composed.outputsFun C }

/-- Apply source splitting and both section machines while preserving the saved count. -/
noncomputable def processWithVariableCountComputableInPolyTime :
    @TM2ComputableInPolyTime (RuntimeSystem × ℕ) CountedSections.Value
      VariableHeader.outputFinEncoding CountedSections.finEncoding
      (fun pair => ((RuntimeStructuralView.indexedDomainOccurrences pair.1.domains,
        pair.1.scopes), pair.2)) :=
  LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    RuntimeSourceSections.inputFinEncoding CountedSections.sectionsFinEncoding
    finEncodingNatBool _ sourceProcessedSectionsComputableInPolyTime

/-- The actual Boolean input internally constructs both exact tagged sections
and the original variable count, with a checked polynomial bit-level bound. -/
noncomputable def runtimeCompilerCountedSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem CountedSections.Value
      RuntimeCompilerInput.finEncoding CountedSections.finEncoding
      CountedSections.ofRuntimeSystem := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerVariableHeaderComputableInPolyTime processWithVariableCountComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa [Function.comp_def, VariableHeader.retain, CountedSections.ofRuntimeSystem]
        using composed.outputsFun C }

#print axioms CountedSections.toStructuralView_ofRuntimeSystem
#print axioms CountedSections.recordCount_ofRuntimeSystem
#print axioms CountedSections.recordCount_le_encode_length
#print axioms CountedSections.headerEncode_ofRuntimeSystem
#print axioms CountedSections.raw_encode_eq_sections
#print axioms sourceProcessedSectionsComputableInPolyTime
#print axioms processWithVariableCountComputableInPolyTime
#print axioms runtimeCompilerCountedSectionsComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
