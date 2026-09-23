import PhdThesisLean.AllDifferentCSPOccurrenceInitialization

/-!
# Complete canonical domain relabelling from the actual compiler input

Initialize an empty accumulator, run the complete checked occurrence loop,
retain scopes and the original variable count through the upstream pair
adapter, and compose the existing Boolean-input source preparation. The output
uses the existing counted-section encoding with every domain value replaced
by its exact thesis rank. Edge construction and objective emission are later
compiler stages.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace OccurrenceRelabelling

def relabel (input : DomainSymbolExtraction.Value) : List (ℕ × ℕ) :=
  OccurrenceIteration.finish input.2 input.1 []

theorem relabel_eq (input : DomainSymbolExtraction.Value) :
    relabel input = input.1.map
      (fun occurrence => (occurrence.1, DomainSymbols.rank input.2 occurrence.2)) := by
  simp [relabel, OccurrenceIteration.finish_eq_append_map]

theorem relabel_length (input : DomainSymbolExtraction.Value) :
    (relabel input).length = input.1.length := by simp [relabel_eq]

theorem relabel_encoded_length_le (input : DomainSymbolExtraction.Value) :
    (DomainFieldRow.outputEncode (relabel input)).length ≤
      2 * ((DomainSymbolExtraction.finEncoding.encode input).length + 1) ^ 2 :=
  OccurrenceIteration.finish_encoded_length_le_quadratic input

end OccurrenceRelabelling

/-- Start from the existing occurrence/symbol wire. The accumulator is
constructed inside the finite computation, including all tagging costs. -/
noncomputable def occurrenceRelabellingComputableInPolyTime :
    @TM2ComputableInPolyTime DomainSymbolExtraction.Value (List (ℕ × ℕ))
      DomainSymbolExtraction.finEncoding DomainFieldRow.outputFinEncoding
      OccurrenceRelabelling.relabel := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    occurrenceInitializationComputableInPolyTime occurrenceLoopComputableInPolyTime
  exact { composed with
    outputsFun := fun input => by
      simpa only [Function.comp_def, OccurrenceLoop.result, OccurrenceInitialization.seed,
        OccurrenceRelabelling.relabel] using composed.outputsFun input }

namespace CountedRelabelledSections

/-- Relabel all domain occurrences; preserve whole scopes and variable count. -/
def relabel (input : CountedSymbolSections.Value) : CountedSections.Value :=
  ((OccurrenceRelabelling.relabel input.1.1, input.1.2), input.2)

def ofRuntimeSystem (C : RuntimeSystem) : CountedSections.Value :=
  relabel (CountedSymbolSections.ofRuntimeSystem C)

theorem retains_scopes_and_count (input : CountedSymbolSections.Value) :
    ((relabel input).1.2, (relabel input).2) = (input.1.2, input.2) := rfl

theorem domains_ofRuntimeSystem (C : RuntimeSystem) :
    (ofRuntimeSystem C).1.1 =
      (RuntimeStructuralView.indexedDomainOccurrences C.domains).map
        (fun occurrence => (occurrence.1, C.toExplicitSystem.relabelValue occurrence.2)) := by
  simp only [ofRuntimeSystem, relabel, OccurrenceRelabelling.relabel_eq]
  simp only [CountedSymbolSections.rank_symbols_eq_relabelValue]
  rfl

theorem scopes_ofRuntimeSystem (C : RuntimeSystem) : (ofRuntimeSystem C).1.2 = C.scopes := rfl

theorem variableCount_ofRuntimeSystem (C : RuntimeSystem) :
    (ofRuntimeSystem C).2 = C.domains.length := rfl

/-- Repeated occurrences stay repeated; only their values change. -/
theorem recordCount_ofRuntimeSystem (C : RuntimeSystem) :
    CountedSections.recordCount (ofRuntimeSystem C) = C.domainEntryCount + C.scopes.length := by
  simp [CountedSections.recordCount, domains_ofRuntimeSystem, scopes_ofRuntimeSystem,
    RuntimeSystem.domainEntryCount]

theorem rank_bounds (C : RuntimeSystem) (record : ℕ × ℕ)
    (h : record ∈ (ofRuntimeSystem C).1.1) :
    0 < record.2 ∧ record.2 < C.domainEntryPrime := by
  apply OccurrenceIteration.finish_rank_bounds C record
  have wire : (ofRuntimeSystem C).1.1 =
      OccurrenceIteration.finish C.domains.flatten
        (RuntimeStructuralView.indexedDomainOccurrences C.domains) [] := by
    change OccurrenceIteration.finish (CountedSymbolSections.ofRuntimeSystem C).1.1.2 _ [] = _
    rw [CountedSymbolSections.symbols_ofRuntimeSystem]
    rfl
  rw [← wire]
  exact h

example : ofRuntimeSystem ⟨[[100, 7], [], [100, 42, 7]], [[0, 2], [2, 0, 2]]⟩ =
    (([(0, 3), (0, 1), (2, 3), (2, 2), (2, 1)], [[0, 2], [2, 0, 2]]), 3) := by decide
example : ofRuntimeSystem ⟨[[], []], [[]]⟩ = (([], [[]]), 2) := by decide

end CountedRelabelledSections

/-- Lift the complete traversal while retaining every scope cell. -/
noncomputable def relabelledSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime CountedSymbolSections.Sections CountedSections.Sections
      CountedSymbolSections.sectionsFinEncoding CountedSections.sectionsFinEncoding
      (fun input => (OccurrenceRelabelling.relabel input.1, input.2)) :=
  LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    DomainSymbolExtraction.finEncoding DomainFieldRow.outputFinEncoding
    ScopeFieldSection.outputFinEncoding _ occurrenceRelabellingComputableInPolyTime

/-- Retain the variable count, including variables with empty domains. -/
noncomputable def countedRelabelledSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime CountedSymbolSections.Value CountedSections.Value
      CountedSymbolSections.finEncoding CountedSections.finEncoding
      CountedRelabelledSections.relabel :=
  LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    CountedSymbolSections.sectionsFinEncoding CountedSections.sectionsFinEncoding
    finEncodingNatBool _ relabelledSectionsComputableInPolyTime

/-- Complete canonical relabelling starts from the actual Boolean compiler
input. Source preparation, symbol extraction, initialization, every loop cycle
and the two retained-section adapters all belong to the composed polynomial. -/
noncomputable def runtimeCompilerRelabelledSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem CountedSections.Value
      RuntimeCompilerInput.finEncoding CountedSections.finEncoding
      CountedRelabelledSections.ofRuntimeSystem := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerSymbolSectionsComputableInPolyTime countedRelabelledSectionsComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa only [Function.comp_def, CountedRelabelledSections.ofRuntimeSystem] using composed.outputsFun C }

#print axioms OccurrenceRelabelling.relabel_eq
#print axioms OccurrenceRelabelling.relabel_encoded_length_le
#print axioms occurrenceRelabellingComputableInPolyTime
#print axioms CountedRelabelledSections.domains_ofRuntimeSystem
#print axioms CountedRelabelledSections.recordCount_ofRuntimeSystem
#print axioms CountedRelabelledSections.rank_bounds
#print axioms countedRelabelledSectionsComputableInPolyTime
#print axioms runtimeCompilerRelabelledSectionsComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
