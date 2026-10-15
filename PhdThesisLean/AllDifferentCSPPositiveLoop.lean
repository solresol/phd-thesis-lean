import PhdThesisLean.AllDifferentCSPPositiveLoopMachine

/-!
# Polynomial-time traversal of every counted occurrence

The finite dispatcher consumes one whole occurrence per cycle. Its full encoded
state strictly shrinks, so every body call and transfer has a uniform bound
in the original wire length. Every occurrence has a count delimiter, including
a zero/zero pair; the number of iterations is therefore at most that length.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PositiveLoop

def result (input : PositiveIteration.Output) : Bool :=
  PositiveIteration.finish input.2.1 input.2.2 input.1

theorem result_eq (input : PositiveIteration.Output) :
    result input = (input.1 || PositiveMembership.contains input.2) := PositiveIteration.finish_eq _ _ _

/-- Every occurrence occupies at least one cell, including a zero/zero pair. -/
theorem occurrences_length_le_state (input : PositiveIteration.Output) :
    input.2.2.length ≤ (PositiveIteration.outputFinEncoding.encode input).length := by
  rcases input with ⟨answer, query, occurrences⟩
  induction occurrences generalizing answer with
  | nil => simp
  | cons occurrence occurrences ih =>
      have tail := ih (PositiveIteration.step (answer, query, occurrence, occurrences)).1
      have smaller := PositiveIteration.output_length_lt (answer, query, occurrence, occurrences)
      change (PositiveIteration.outputFinEncoding.encode
        ((PositiveIteration.step (answer, query, occurrence, occurrences)).1, query, occurrences)).length <
        (PositiveIteration.outputFinEncoding.encode (answer, query, occurrence :: occurrences)).length at smaller
      dsimp only at tail ⊢
      simp only [List.length_cons]
      omega

noncomputable section

/-- Uniform cost of one complete cycle at a bound on the full state length.
It also bounds the final empty-state scan and output. -/
def passTime : Polynomial ℕ := PositiveLoopMachine.body.time + 4 * Polynomial.X + 4

theorem passTime_eval (s : ℕ) :
    passTime.eval s = PositiveLoopMachine.body.time.eval s + 4 * s + 4 := by
  simp [passTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]

/-- Structural induction and strict wire shrinkage bound every complete cycle. -/
def run_bounded (query : ℕ × ℕ) (occurrences : List (ℕ × ℕ)) (answer : Bool) (bound : ℕ)
    (size : (PositiveIteration.outputFinEncoding.encode (answer, query, occurrences)).length ≤ bound) :
    PositiveLoopMachine.Run (PositiveLoopMachine.ready (answer, query, occurrences))
      (PositiveLoopMachine.done (PositiveIteration.finish query occurrences answer))
      ((occurrences.length + 1) * passTime.eval bound) := by
  induction occurrences generalizing answer with
  | nil =>
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (PositiveLoopMachine.exit_run answer query)
      simp only [List.length_nil, zero_add, one_mul, passTime_eval]
      omega
  | cons occurrence occurrences ih =>
      let input : PositiveIteration.Input := (answer, query, occurrence, occurrences)
      have input_size : (PositiveIteration.inputFinEncoding.encode input).length ≤ bound := size
      have output_size := (Nat.le_of_lt (PositiveIteration.output_length_lt input)).trans input_size
      have tail_size : (PositiveIteration.outputFinEncoding.encode
          ((PositiveIteration.step input).1, query, occurrences)).length ≤ bound := output_size
      have tail_run := ih (PositiveIteration.step input).1 tail_size
      have cycle := PositiveLoopMachine.iteration_cycle answer query occurrence occurrences
      have body_cost := LeanNPHardness.MachineRuntime.polynomial_eval_mono
        PositiveLoopMachine.body.time input_size
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (PositiveLoopMachine.seq cycle tail_run)
      simp only [List.length_cons, passTime_eval]
      change PositiveLoopMachine.body.time.eval (PositiveIteration.inputFinEncoding.encode input).length +
        2 * (PositiveIteration.inputFinEncoding.encode input).length +
        2 * (PositiveIteration.outputFinEncoding.encode (PositiveIteration.step input)).length + 4 +
        (occurrences.length + 1) * (PositiveLoopMachine.body.time.eval bound + 4 * bound + 4) ≤
        (occurrences.length + 1 + 1) * (PositiveLoopMachine.body.time.eval bound + 4 * bound + 4)
      nlinarith

/-- A polynomial in the original complete wire length, including all cycles,
their control/transfers, and the final empty-state exit. -/
def time : Polynomial ℕ := (Polynomial.X + 1) * passTime

theorem time_eval (s : ℕ) :
    time.eval s = (s + 1) * (PositiveLoopMachine.body.time.eval s + 4 * s + 4) := by
  simp [time, passTime_eval, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]

def outputsInTime (input : PositiveIteration.Output) :
    TM2OutputsInTime PositiveLoopMachine.computer (PositiveIteration.outputFinEncoding.encode input)
      (some (finEncodingBoolBool.encode (result input)))
      (time.eval (PositiveIteration.outputFinEncoding.encode input).length) := by
  have h := run_bounded input.2.1 input.2.2 input.1
    (PositiveIteration.outputFinEncoding.encode input).length (by rfl)
  have h' := LeanNPHardness.MachinePrimitives.evalsToInTimeMono h
    (Nat.mul_le_mul_right (passTime.eval (PositiveIteration.outputFinEncoding.encode input).length)
      (Nat.add_le_add_right (occurrences_length_le_state input) 1))
  simpa only [PositiveLoopMachine.ready_eq_initList, PositiveLoopMachine.done_eq_haltList,
    result, time, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one] using! h'

end

end PositiveLoop

/-- Complete repeated occurrence testing, including dispatch, transfer and cleanup,
from an arbitrary checked Boolean/endpoint/counted-occurrence state. -/
noncomputable def positiveLoopComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveIteration.Output Bool
      PositiveIteration.outputFinEncoding finEncodingBoolBool PositiveLoop.result where
  tm := PositiveLoopMachine.computer
  inputAlphabet := Equiv.refl PositiveLoopMachine.Wire
  outputAlphabet := Equiv.refl Bool
  time := PositiveLoop.time
  outputsFun input := by simpa [Equiv.refl] using PositiveLoop.outputsInTime input

/-- With an initially false accumulator, the actual machine returns exactly
whether the ordered query occurs in the retained ranked occurrence list. -/
noncomputable def positiveLoop_contains_outputsInTime (query : ℕ × ℕ) (occurrences : List (ℕ × ℕ)) :
    TM2OutputsInTime PositiveLoopMachine.computer
      (PositiveIteration.outputFinEncoding.encode (false, query, occurrences))
      (some (finEncodingBoolBool.encode (PositiveMembership.contains (query, occurrences))))
      (PositiveLoop.time.eval (PositiveIteration.outputFinEncoding.encode (false, query, occurrences)).length) := by
  simpa only [PositiveLoop.result, PositiveIteration.finish_false_eq_contains] using
    PositiveLoop.outputsInTime (false, query, occurrences)

#print axioms PositiveLoop.result_eq
#print axioms PositiveLoop.occurrences_length_le_state
#print axioms PositiveLoop.run_bounded
#print axioms PositiveLoop.outputsInTime
#print axioms positiveLoopComputableInPolyTime
#print axioms positiveLoop_contains_outputsInTime

end PhdThesisLean.AllDifferentCSPMachine
