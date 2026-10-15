import PhdThesisLean.AllDifferentCSPPositiveTest
import PhdThesisLean.AllDifferentCSPScopeAccumulator

/-!
# One complete occurrence-membership iteration

Reuse the checked Boolean accumulator, then compose it with extraction and
same-record comparison. The exact tail and both candidate fields survive.
The executable finish recurrence is verified here. The repeated finite
dispatcher and its total runtime are checked in `AllDifferentCSPPositiveLoop`.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PositiveAccumulator

abbrev Input := Bool × PositiveTest.Output
abbrev Output := PositiveTest.Output

def inputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingBoolBool PositiveTest.outputFinEncoding
@[simp] abbrev outputFinEncoding := PositiveTest.outputFinEncoding

def update (input : Input) : Output := (input.1 || input.2.1, input.2.2)

def asScopeOutput (input : Output) : ScopeTest.Output :=
  (input.1, input.2.1, input.2.2.map fun pair => [0, pair.1, pair.2])

def asScope (input : Input) : ScopeAccumulator.Input := (input.1, asScopeOutput input.2)

theorem output_encode (input : Output) :
    outputFinEncoding.encode input = ScopeAccumulator.outputFinEncoding.encode (asScopeOutput input) := by
  simp only [outputFinEncoding, ScopeAccumulator.outputFinEncoding, PositiveTest.outputFinEncoding,
    PositiveMembership.finEncoding, DomainFieldRow.outputFinEncoding,
    OccurrenceCount.occurrenceWire_eq_rows,
    ScopeTest.outputFinEncoding, ScopeExtraction.remainingFinEncoding,
    DomainFieldSection.rowPayloadFinEncoding, ScopeFieldSection.rowPayloadFinEncoding, asScopeOutput,
    LeanNPHardness.PairEncoding.finEncoding]

theorem input_encode (input : Input) :
    inputFinEncoding.encode input = ScopeAccumulator.inputFinEncoding.encode (asScope input) := by
  simp only [inputFinEncoding, ScopeAccumulator.inputFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding, output_encode, asScope]

theorem update_encode (input : Input) :
    outputFinEncoding.encode (update input) =
      ScopeAccumulator.outputFinEncoding.encode (ScopeAccumulator.update (asScope input)) := by
  rw [output_encode]
  rfl

/-- Exactly two result bits become one; no query or occurrence cell changes. -/
theorem output_length_balance (input : Input) :
    (outputFinEncoding.encode (update input)).length + 1 =
      (inputFinEncoding.encode input).length := by
  simp [inputFinEncoding, PositiveTest.outputFinEncoding,
    update, finEncodingBoolBool, encodeBool]

end PositiveAccumulator

/-- The existing finite OR machine works on the identical continuation alphabet. -/
def positiveAccumulator_outputsInTime (input : PositiveAccumulator.Input) :
    TM2OutputsInTime ScopeAccumulatorMachine.computer
      (PositiveAccumulator.inputFinEncoding.encode input)
      (some (PositiveAccumulator.outputFinEncoding.encode (PositiveAccumulator.update input)))
      (2 * (PositiveAccumulator.inputFinEncoding.encode input).length + 3) := by
  simpa only [PositiveAccumulator.input_encode, PositiveAccumulator.update_encode] using
    scopeAccumulator_outputsInTime (PositiveAccumulator.asScope input)

noncomputable def positiveAccumulatorComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveAccumulator.Input PositiveAccumulator.Output
      PositiveAccumulator.inputFinEncoding PositiveAccumulator.outputFinEncoding
      PositiveAccumulator.update where
  tm := scopeAccumulatorComputableInPolyTime.tm
  inputAlphabet := scopeAccumulatorComputableInPolyTime.inputAlphabet
  outputAlphabet := scopeAccumulatorComputableInPolyTime.outputAlphabet
  time := scopeAccumulatorComputableInPolyTime.time
  outputsFun input := by
    simpa only [PositiveAccumulator.input_encode, PositiveAccumulator.update_encode] using
      scopeAccumulatorComputableInPolyTime.outputsFun (PositiveAccumulator.asScope input)

namespace PositiveIteration

abbrev Input := Bool × PositiveTest.Input
abbrev Output := PositiveAccumulator.Output

def inputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingBoolBool PositiveTest.inputFinEncoding
@[simp] abbrev outputFinEncoding := PositiveAccumulator.outputFinEncoding

theorem nonempty_encode (answer : Bool) (query head : ℕ × ℕ) (tail : List (ℕ × ℕ)) :
    outputFinEncoding.encode (answer, query, head :: tail) =
      inputFinEncoding.encode (answer, query, head, tail) := rfl

def step (input : Input) : Output :=
  PositiveAccumulator.update (input.1, PositiveTest.evaluate input.2)

theorem query_preserved (input : Input) : (step input).2.1 = input.2.1 := rfl
theorem remaining_occurrences (input : Input) : (step input).2.2 = input.2.2.2 := rfl

/-- The accumulated answer OR the remaining membership question is invariant. -/
theorem contains_invariant (input : Input) :
    ((step input).1 || PositiveMembership.contains (step input).2) =
      (input.1 || PositiveMembership.contains (PositiveMembershipExtraction.source input.2)) := by
  rw [PositiveTest.contains_step input.2]
  simp only [step, PositiveAccumulator.update, Bool.or_assoc]

/-- One whole counted occurrence is removed, including both binary fields. -/
theorem output_length_balance (input : Input) :
    (outputFinEncoding.encode (step input)).length +
        (encodeNat input.2.2.1.1).length + (encodeNat input.2.2.1.2).length + 6 =
      (inputFinEncoding.encode input).length := by
  have test := PositiveTest.output_length_balance input.2
  have accumulated := PositiveAccumulator.output_length_balance
    (input.1, PositiveTest.evaluate input.2)
  simp only [PositiveAccumulator.inputFinEncoding, inputFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length] at accumulated ⊢
  have bit : (finEncodingBoolBool.encode input.1).length = 1 := by
    simp [finEncodingBoolBool, encodeBool]
  dsimp only [outputFinEncoding, PositiveAccumulator.outputFinEncoding, step] at accumulated ⊢
  omega

theorem output_length_lt (input : Input) :
    (outputFinEncoding.encode (step input)).length <
      (inputFinEncoding.encode input).length := by
  have h := output_length_balance input
  omega

/-- Executable specification only; the repeated finite-machine proof is separate. -/
def finish (query : ℕ × ℕ) : List (ℕ × ℕ) → Bool → Bool
  | [], answer => answer
  | head :: tail, answer => finish query tail (step (answer, query, head, tail)).1

theorem finish_eq (query : ℕ × ℕ) (occurrences : List (ℕ × ℕ)) (answer : Bool) :
    finish query occurrences answer =
      (answer || PositiveMembership.contains (query, occurrences)) := by
  induction occurrences generalizing answer with
  | nil => simp [finish, PositiveMembership.contains]
  | cons head tail ih =>
      rw [finish, ih]
      exact contains_invariant (answer, query, head, tail)

theorem finish_false_eq_contains (query : ℕ × ℕ) (occurrences : List (ℕ × ℕ)) :
    finish query occurrences false = PositiveMembership.contains (query, occurrences) := by
  simpa using finish_eq query occurrences false

example : finish (0, 1) [(0, 2), (1, 1)] false = false := by decide
example : finish (0, 1) [(0, 2), (0, 1), (0, 1)] false = true := by decide
example : finish (0, 0) [(0, 0)] false = true := by decide
example : finish (0, 0) [] false = false := rfl
example : finish (0, 1) [(0, 2)] true = true := by decide

end PositiveIteration

/-- Execute one complete occurrence iteration, including all extraction,
comparison, preservation, OR accumulation and transfer costs. -/
noncomputable def positiveIterationComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveIteration.Input PositiveIteration.Output
      PositiveIteration.inputFinEncoding PositiveIteration.outputFinEncoding PositiveIteration.step := by
  let tested := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    finEncodingBoolBool PositiveTest.inputFinEncoding PositiveTest.outputFinEncoding
    PositiveTest.evaluate positiveTestComputableInPolyTime
  exact compositionComputableInPolyTime _ _ _ _ _ tested positiveAccumulatorComputableInPolyTime

#print axioms PositiveAccumulator.output_encode
#print axioms PositiveAccumulator.output_length_balance
#print axioms positiveAccumulator_outputsInTime
#print axioms positiveAccumulatorComputableInPolyTime
#print axioms PositiveIteration.nonempty_encode
#print axioms PositiveIteration.contains_invariant
#print axioms PositiveIteration.output_length_balance
#print axioms PositiveIteration.output_length_lt
#print axioms PositiveIteration.finish_false_eq_contains
#print axioms positiveIterationComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
