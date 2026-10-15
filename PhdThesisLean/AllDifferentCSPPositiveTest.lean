import PhdThesisLean.AllDifferentCSPPositiveComparison

/-!
# Extract and compare one exact ranked occurrence

Compose counted-record extraction, candidate copying, both binary equalities,
and conjunction. The candidate and exact tail survive the complete call.
This is one checked step; the repeated membership dispatcher is still separate.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PositiveTest

abbrev Input := PositiveMembershipExtraction.Input
abbrev Output := Bool × PositiveMembership.Input
@[simp] abbrev inputFinEncoding := PositiveMembershipExtraction.inputFinEncoding

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingBoolBool PositiveMembership.finEncoding

def evaluate (input : Input) : Output :=
  (PositivePairQuery.equal (input.1, input.2.1), PositiveMembershipExtraction.remaining input)

/-- The answer requires both coordinates of this one occurrence to match. -/
theorem result_eq_true (input : Input) :
    (evaluate input).1 = true ↔ input.1 = input.2.1 :=
  PositivePairQuery.equal_eq_true _

theorem remaining_eq (input : Input) : (evaluate input).2 = (input.1, input.2.2) := rfl

/-- One result cell replaces the head's two binary words and six structural cells. -/
theorem output_length_balance (input : Input) :
    (outputFinEncoding.encode (evaluate input)).length +
        (encodeNat input.2.1.1).length + (encodeNat input.2.1.2).length + 5 =
      (inputFinEncoding.encode input).length := by
  have h := PositiveMembershipExtraction.remaining_length_balance input
  simp only [outputFinEncoding, evaluate,
    LeanNPHardness.PairEncoding.finEncoding_encode_length]
  have bit : (finEncodingBoolBool.encode (PositivePairQuery.equal (input.1, input.2.1))).length = 1 := by
    simp [finEncodingBoolBool, encodeBool]
  rw [bit]
  dsimp only [inputFinEncoding]
  omega

theorem output_length_lt (input : Input) :
    (outputFinEncoding.encode (evaluate input)).length <
      (inputFinEncoding.encode input).length := by
  have h := output_length_balance input
  omega

theorem contains_step (input : Input) :
    PositiveMembership.contains (PositiveMembershipExtraction.source input) =
      ((evaluate input).1 || PositiveMembership.contains (evaluate input).2) :=
  PositiveMembershipExtraction.contains_step input

example : evaluate ((0, 1), ((0, 2), [(1, 1)])) =
    (false, (0, 1), [(1, 1)]) := by decide
example : evaluate ((0, 0), ((0, 0), [])) = (true, (0, 0), []) := by decide
example : evaluate ((7, 1000000), ((7, 1000000), [(7, 1000000)])) =
    (true, (7, 1000000), [(7, 1000000)]) := by decide

end PositiveTest

/-- Starting from the contiguous counted source, compute the exact head match
and retain the candidate and tail. All intermediate layouts are constructed
by finite machines, with every transfer included in the composed polynomial. -/
noncomputable def positiveTestComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveTest.Input PositiveTest.Output
      PositiveTest.inputFinEncoding PositiveTest.outputFinEncoding PositiveTest.evaluate := by
  let routed := compositionComputableInPolyTime _ _ _ _ _
    positiveMembershipExtractionComputableInPolyTime positiveRoutingComputableInPolyTime
  let tested := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    PositivePairQuery.finEncoding finEncodingBoolBool PositiveMembership.finEncoding
    PositivePairQuery.equal positivePairMatchComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _ routed tested
  exact composed

#print axioms PositiveTest.result_eq_true
#print axioms PositiveTest.remaining_eq
#print axioms PositiveTest.output_length_balance
#print axioms PositiveTest.output_length_lt
#print axioms PositiveTest.contains_step
#print axioms positiveTestComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
