import LeanNPHardness.PairExchange
import PhdThesisLean.AllDifferentCSPSourceSections

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-!
# Process both structural sections from the actual compiler input

The dependency now supplies generic pair exchange and right-component
computation. This module specializes those checked APIs to domain/scope
encodings and composes them from the actual compiler input. Generic exchange
uses arbitrary finite component alphabets and takes at most `4s+6` steps;
its implementation and axiom audits are owned by `lean-np-hardness`.
`AllDifferentCSPVariableHeader` separately copies the variable count while
retaining the source. Carrying it through these passes, constructing the record
count, and complete structural assembly remain separate tasks.
-/

/-- Put scopes first using the upstream generic pair exchange. -/
noncomputable def exchangeDomainScopePayloadComputableInPolyTime :
    @TM2ComputableInPolyTime (List (ℕ × ℕ) × List (List ℕ))
      (List (List ℕ) × List (ℕ × ℕ))
      (LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
        ScopeFieldSection.rowPayloadFinEncoding)
      (LeanNPHardness.PairEncoding.finEncoding ScopeFieldSection.rowPayloadFinEncoding
        DomainFieldRow.outputFinEncoding) Prod.swap :=
  LeanNPHardness.PairExchange.computableInPolyTime
    DomainFieldRow.outputFinEncoding ScopeFieldSection.rowPayloadFinEncoding

/-- Restore section order using the upstream generic pair exchange. -/
noncomputable def exchangeScopeDomainOutputComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ) × List (ℕ × ℕ))
      (List (ℕ × ℕ) × List (List ℕ))
      (LeanNPHardness.PairEncoding.finEncoding ScopeFieldSection.outputFinEncoding
        DomainFieldRow.outputFinEncoding)
      (LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
        ScopeFieldSection.outputFinEncoding) Prod.swap :=
  LeanNPHardness.PairExchange.computableInPolyTime
    ScopeFieldSection.outputFinEncoding DomainFieldRow.outputFinEncoding

/-- The complete paired scope pass increases wire length by at most a factor
of four, counting the preserved domain stream as part of both encodings. -/
theorem pairedScopeSection_output_length_le (pair : List (ℕ × ℕ) × List (List ℕ)) :
    ((LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
      ScopeFieldSection.outputFinEncoding).encode pair).length ≤
    4 * ((LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
      ScopeFieldSection.rowPayloadFinEncoding).encode pair).length := by
  have h := ScopeFieldSection.outputEncode_length_le_linear pair.2
  simp only [LeanNPHardness.PairEncoding.finEncoding_encode_length]
  change (DomainFieldRow.outputFinEncoding.encode pair.1).length +
      (ScopeFieldSection.outputEncode pair.2).length ≤ _
  omega

/-- Process all scopes while preserving the exact domain occurrence output.
Only the scope encoding changes; no scope, entry, or repetition is discarded. -/
noncomputable def pairedScopeSectionComputableInPolyTime :
    @TM2ComputableInPolyTime (List (ℕ × ℕ) × List (List ℕ))
      (List (ℕ × ℕ) × List (List ℕ))
      (LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
        ScopeFieldSection.rowPayloadFinEncoding)
      (LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
        ScopeFieldSection.outputFinEncoding) id :=
  LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    DomainFieldRow.outputFinEncoding ScopeFieldSection.rowPayloadFinEncoding
    ScopeFieldSection.outputFinEncoding id scopeSectionComputableInPolyTime

/-- The actual Boolean compiler input constructs both exact tagged structural
sections internally. The variable and record-count headers are not yet emitted. -/
noncomputable def runtimeCompilerProcessedSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem (List (ℕ × ℕ) × List (List ℕ))
      RuntimeCompilerInput.finEncoding
      (LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
        ScopeFieldSection.outputFinEncoding)
      (fun C => (RuntimeStructuralView.indexedDomainOccurrences C.domains, C.scopes)) := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerDomainAndScopesComputableInPolyTime pairedScopeSectionComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa [Function.comp_def] using composed.outputsFun C }

#print axioms exchangeDomainScopePayloadComputableInPolyTime
#print axioms exchangeScopeDomainOutputComputableInPolyTime
#print axioms pairedScopeSection_output_length_le
#print axioms pairedScopeSectionComputableInPolyTime
#print axioms runtimeCompilerProcessedSectionsComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
