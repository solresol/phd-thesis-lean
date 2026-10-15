import PhdThesisLean.AllDifferentCSPPositiveMembership
import PhdThesisLean.AllDifferentCSPScopeRouting

/-!
# Route one ranked-occurrence query while retaining its continuation

The existing finite scope router already has the required tagged wire layout.
Reuse it to duplicate the candidate, route the exact ordered head record to
comparison, and retain every remaining occurrence. No traversal is assumed.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding

namespace PositivePairQuery

abbrev Input := (ℕ × ℕ) × (ℕ × ℕ)

def finEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding ScopeExtraction.endpointsFinEncoding
    PositiveOccurrenceHead.recordFinEncoding

def equal (input : Input) : Bool :=
  decide (input.1.1 = input.2.1) && decide (input.1.2 = input.2.2)

theorem equal_eq_true (input : Input) : equal input = true ↔ input.1 = input.2 := by
  simp [equal, Prod.ext_iff]

theorem input_length (input : Input) :
    (finEncoding.encode input).length =
      (encodeNat input.1.1).length + (encodeNat input.1.2).length +
        (encodeNat input.2.1).length + (encodeNat input.2.2).length + 3 := by
  have hz : encodeNat 0 = [] := by
    change encodeNum (Num.ofNat' 0) = []
    rw [Num.ofNat'_zero]
    rfl
  simp [finEncoding, ScopeExtraction.endpointsFinEncoding,
    PositiveOccurrenceHead.recordFinEncoding, finEncodingNatBool, encodingNatBool,
    SourceOrderRawFields.encode, hz, Nat.add_assoc]

end PositivePairQuery

namespace PositiveRouting

abbrev Input := PositiveMembershipExtraction.Input
abbrev Output := PositivePairQuery.Input × PositiveMembership.Input
@[simp] abbrev inputFinEncoding := PositiveMembershipExtraction.outputFinEncoding

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding PositivePairQuery.finEncoding
    PositiveMembership.finEncoding

def prepare (input : Input) : Output :=
  ((input.1, input.2.1), PositiveMembershipExtraction.remaining input)

def asScope (input : Input) : ScopeRouting.Input :=
  (input.1, PositiveOccurrenceHead.asScope input.2)

theorem input_encode (input : Input) :
    inputFinEncoding.encode input = ScopeRouting.inputFinEncoding.encode (asScope input) := by
  simp only [PositiveRouting.inputFinEncoding, PositiveMembershipExtraction.outputFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding, PositiveOccurrenceHead.output_encode]
  rfl

theorem output_encode (input : Input) :
    outputFinEncoding.encode (prepare input) =
      ScopeRouting.outputFinEncoding.encode (ScopeRouting.prepare (asScope input)) := by
  simp only [outputFinEncoding, prepare, PositiveMembershipExtraction.remaining,
    PositivePairQuery.finEncoding, PositiveMembership.finEncoding,
    PositiveOccurrenceHead.recordFinEncoding, DomainFieldRow.outputFinEncoding,
    OccurrenceCount.occurrenceWire_eq_rows, ScopeRouting.outputFinEncoding,
    ScopeRouting.prepare, ScopeExtraction.query, ScopeExtraction.remaining,
    ScopeQueries.inputFinEncoding, ScopeExtraction.remainingFinEncoding,
    ScopeExtraction.endpointsFinEncoding, asScope, PositiveOccurrenceHead.asScope,
    DomainFieldSection.rowPayloadFinEncoding, ScopeFieldSection.rowPayloadFinEncoding, SourceOrderRawFields.finEncoding,
    LeanNPHardness.PairEncoding.finEncoding]

/-- Each candidate word is copied once; the head and tail are preserved exactly. -/
theorem output_length (input : Input) :
    (outputFinEncoding.encode (prepare input)).length =
      (inputFinEncoding.encode input).length +
        (ScopeExtraction.endpointsFinEncoding.encode input.1).length := by
  rw [input_encode, output_encode]
  exact ScopeRouting.output_length (asScope input)

theorem output_length_le (input : Input) :
    (outputFinEncoding.encode (prepare input)).length ≤
      2 * (inputFinEncoding.encode input).length := by
  rw [input_encode, output_encode]
  exact ScopeRouting.output_length_le (asScope input)

theorem contains_step (input : Input) :
    PositiveMembership.contains (PositiveMembershipExtraction.source input) =
      (PositivePairQuery.equal (prepare input).1 ||
        PositiveMembership.contains (prepare input).2) :=
  PositiveMembershipExtraction.contains_step input

end PositiveRouting

/-- The previously checked finite router constructs the ordered query and
continuation in `3s+3` steps, including both candidate copies and cleanup. -/
def positiveRouting_outputsInTime (input : PositiveRouting.Input) :
    TM2OutputsInTime ScopeRoutingMachine.computer
      (PositiveRouting.inputFinEncoding.encode input)
      (some (PositiveRouting.outputFinEncoding.encode (PositiveRouting.prepare input)))
      (3 * (PositiveRouting.inputFinEncoding.encode input).length + 3) := by
  simpa only [PositiveRouting.input_encode, PositiveRouting.output_encode] using
    scopeRouting_outputsInTime (PositiveRouting.asScope input)

noncomputable def positiveRoutingComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveRouting.Input PositiveRouting.Output
      PositiveRouting.inputFinEncoding PositiveRouting.outputFinEncoding PositiveRouting.prepare where
  tm := scopeRoutingComputableInPolyTime.tm
  inputAlphabet := scopeRoutingComputableInPolyTime.inputAlphabet
  outputAlphabet := scopeRoutingComputableInPolyTime.outputAlphabet
  time := scopeRoutingComputableInPolyTime.time
  outputsFun input := by
    simpa only [PositiveRouting.input_encode, PositiveRouting.output_encode] using
      scopeRoutingComputableInPolyTime.outputsFun (PositiveRouting.asScope input)

#print axioms PositivePairQuery.equal_eq_true
#print axioms PositivePairQuery.input_length
#print axioms PositiveRouting.output_encode
#print axioms PositiveRouting.output_length
#print axioms PositiveRouting.contains_step
#print axioms positiveRouting_outputsInTime
#print axioms positiveRoutingComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
