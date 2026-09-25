import PhdThesisLean.AllDifferentCSPRowCount
import PhdThesisLean.AllDifferentCSPNegativeRows

/-!
# Retain a unary variable bound through complete domain relabelling

Count original domain rows before expansion, including empty domains, and
carry the unary tally and every scope through the checked relabelling path.
The count is bounded by the wire length for every value of the output type,
so the future bounded pair scan cannot hide exponential work in a binary
header. This module prepares the scan input; it does not implement the scan.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace BoundedRelabelledSections

abbrev Source := (List (List ℕ) × ℕ) × List (List ℕ)
abbrev Value := (List (ℕ × ℕ) × ℕ) × List (List ℕ)

/-- Original domain rows and their unary tally, with untouched raw scopes. -/
def sourceFinEncoding : FinEncoding Source :=
  LeanNPHardness.PairEncoding.finEncoding DomainCountedPayload.finEncoding
    ScopeFieldSection.rowPayloadFinEncoding

def domainsFinEncoding : FinEncoding (List (ℕ × ℕ) × ℕ) :=
  LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding unaryFinEncodingNat

/-- The unary field bounds the numerical variable count by actual wire length. -/
def finEncoding : FinEncoding Value :=
  LeanNPHardness.PairEncoding.finEncoding domainsFinEncoding
    ScopeFieldSection.rowPayloadFinEncoding

def count (sections : List (List ℕ) × List (List ℕ)) : Source :=
  (DomainCountedPayload.retain sections.1, sections.2)

def relabelDomains (domains : List (List ℕ)) : List (ℕ × ℕ) :=
  OccurrenceRelabelling.relabel
    (DomainSymbolExtraction.retain (RuntimeStructuralView.indexedDomainOccurrences domains))

def relabel (source : Source) : Value :=
  ((relabelDomains source.1.1, source.1.2), source.2)

def ofRuntimeSystem (C : RuntimeSystem) : Value :=
  relabel (count (RuntimeSourceSections.split C))

/-- Semantic projection only; no conversion to the old binary wire is claimed. -/
def toCountedSections (value : Value) : CountedSections.Value :=
  ((value.1.1, value.2), value.1.2)

theorem toCountedSections_ofRuntimeSystem (C : RuntimeSystem) :
    toCountedSections (ofRuntimeSystem C) = CountedRelabelledSections.ofRuntimeSystem C := rfl

theorem scopes_and_variableCount (C : RuntimeSystem) :
    ((ofRuntimeSystem C).2, (ofRuntimeSystem C).1.2) = (C.scopes, C.domains.length) := rfl

/-- Source counting, including all retained scopes, at most doubles wire length. -/
theorem count_encode_length_le (sections : List (List ℕ) × List (List ℕ)) :
    (sourceFinEncoding.encode (count sections)).length ≤
      2 * (RuntimeSourceSections.outputFinEncoding.encode sections).length := by
  have tally := DomainCountedPayload.encode_retain_length_le sections.1
  have payload := DomainFieldSection.rowPayloadEncode_length_le_inputEncode_length sections.1
  simp only [sourceFinEncoding, count, RuntimeSourceSections.outputFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length]
  change (DomainCountedPayload.finEncoding.encode (DomainCountedPayload.retain sections.1)).length +
      (ScopeFieldSection.rowPayloadFinEncoding.encode sections.2).length ≤
    2 * ((DomainFieldSection.inputEncode sections.1).length +
      (ScopeFieldSection.rowPayloadFinEncoding.encode sections.2).length)
  omega

/-- Exact output wire length, charging every copied bit, delimiter and tally mark. -/
theorem encode_length (value : Value) :
    (finEncoding.encode value).length =
      (DomainFieldRow.outputEncode value.1.1).length + value.1.2 +
        (DomainFieldSection.rowPayloadEncode value.2).length := by
  simp [finEncoding, domainsFinEncoding,
    DomainFieldRow.outputFinEncoding, DomainFieldSection.rowPayloadFinEncoding,
    unaryFinEncodingNat, unaryEncodeNat_eq_replicate_true, Nat.add_assoc]

theorem variableCount_le_encode_length (value : Value) :
    value.1.2 ≤ (finEncoding.encode value).length := by
  rw [encode_length]
  omega

/-- This holds for every intermediate value, not only those with compiler provenance. -/
theorem candidates_length_le_square (value : Value) :
    (PrimalEdgeEnumeration.candidates value.1.2).length ≤
      (finEncoding.encode value).length ^ 2 := by
  rw [PrimalEdgeEnumeration.candidates_length]
  exact Nat.pow_le_pow_left (variableCount_le_encode_length value) 2

def edges (value : Value) : List (ℕ × ℕ) :=
  PrimalEdgeEnumeration.enumerate value.1.2 value.2

theorem edges_ofRuntimeSystem (C : RuntimeSystem) :
    edges (ofRuntimeSystem C) = PrimalEdgeEnumeration.ofRuntimeSystem C := rfl

/-- Size of the future negative-row output in this intermediate input length.
A size theorem does not supply the still-missing edge-scan runtime. -/
theorem negativeRows_length_le_cubic (value : Value) :
    (NegativeRows.outputEncode (edges value)).length ≤
      9 * ((finEncoding.encode value).length + 1) ^ 3 := by
  exact (NegativeRows.enumerate_output_length_le_cubic value.1.2 value.2).trans
    (Nat.mul_le_mul_left 9 (Nat.pow_le_pow_left
      (Nat.add_le_add_right (variableCount_le_encode_length value) 1) 3))

example : ofRuntimeSystem ⟨[[100, 7], [], [100, 42, 7]], [[0, 2], [2, 0, 2]]⟩ =
    (([(0, 3), (0, 1), (2, 3), (2, 2), (2, 1)], 3), [[0, 2], [2, 0, 2]]) := by decide
example : ofRuntimeSystem ⟨[[], []], [[]]⟩ = (([], 2), [[]]) := by decide
example : ofRuntimeSystem ⟨[], []⟩ = (([], 0), []) := by decide

end BoundedRelabelledSections

/-- Count domain rows while preserving every raw scope cell. -/
noncomputable def boundedSourceSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ) × List (List ℕ)) BoundedRelabelledSections.Source
      RuntimeSourceSections.outputFinEncoding BoundedRelabelledSections.sourceFinEncoding
      BoundedRelabelledSections.count :=
  LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    DomainFieldSection.inputFinEncoding DomainCountedPayload.finEncoding
    ScopeFieldSection.rowPayloadFinEncoding _ completeDomainVariableCountComputableInPolyTime

/-- Source preparation and tally construction both start inside the computation. -/
noncomputable def runtimeCompilerBoundedSourceSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem BoundedRelabelledSections.Source
      RuntimeCompilerInput.finEncoding BoundedRelabelledSections.sourceFinEncoding
      (fun C => BoundedRelabelledSections.count (RuntimeSourceSections.split C)) := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerSectionsComputableInPolyTime boundedSourceSectionsComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by simpa only [Function.comp_def] using composed.outputsFun C }

/-- Reuse expansion, exact symbol extraction and the complete rank traversal
on original domain rows. No generic machine implementation is duplicated. -/
noncomputable def domainPayloadRelabellingComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ)) (List (ℕ × ℕ))
      DomainFieldSection.rowPayloadFinEncoding DomainFieldRow.outputFinEncoding
      BoundedRelabelledSections.relabelDomains := by
  let prepared := compositionComputableInPolyTime _ _ _ _ _
    domainSectionComputableInPolyTime domainSymbolExtractionComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _
    prepared occurrenceRelabellingComputableInPolyTime
  exact { composed with
    outputsFun := fun domains => by
      simpa only [Function.comp_def, BoundedRelabelledSections.relabelDomains]
        using composed.outputsFun domains }

/-- Two existing pair adapters retain the unary count and all scopes across
complete relabelling, including their transfer costs in the polynomial. -/
noncomputable def boundedRelabelledSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime BoundedRelabelledSections.Source BoundedRelabelledSections.Value
      BoundedRelabelledSections.sourceFinEncoding BoundedRelabelledSections.finEncoding
      BoundedRelabelledSections.relabel :=
  LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    DomainCountedPayload.finEncoding BoundedRelabelledSections.domainsFinEncoding
    ScopeFieldSection.rowPayloadFinEncoding _
    (LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
      DomainFieldSection.rowPayloadFinEncoding DomainFieldRow.outputFinEncoding
      unaryFinEncodingNat _ domainPayloadRelabellingComputableInPolyTime)

/-- Actual Boolean compiler input to exact relabelled occurrences, unary
variable count and retained scopes. This closes the pair scan's bounded-input
preparation, not its finite-machine implementation. -/
noncomputable def runtimeCompilerBoundedRelabelledSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem BoundedRelabelledSections.Value
      RuntimeCompilerInput.finEncoding BoundedRelabelledSections.finEncoding
      BoundedRelabelledSections.ofRuntimeSystem := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerBoundedSourceSectionsComputableInPolyTime
    boundedRelabelledSectionsComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa only [Function.comp_def, BoundedRelabelledSections.ofRuntimeSystem]
        using composed.outputsFun C }

#print axioms BoundedRelabelledSections.toCountedSections_ofRuntimeSystem
#print axioms BoundedRelabelledSections.count_encode_length_le
#print axioms BoundedRelabelledSections.encode_length
#print axioms BoundedRelabelledSections.candidates_length_le_square
#print axioms BoundedRelabelledSections.edges_ofRuntimeSystem
#print axioms BoundedRelabelledSections.negativeRows_length_le_cubic
#print axioms runtimeCompilerBoundedSourceSectionsComputableInPolyTime
#print axioms domainPayloadRelabellingComputableInPolyTime
#print axioms boundedRelabelledSectionsComputableInPolyTime
#print axioms runtimeCompilerBoundedRelabelledSectionsComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
