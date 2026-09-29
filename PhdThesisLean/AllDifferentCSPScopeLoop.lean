import PhdThesisLean.AllDifferentCSPScopeLoopMachine

/-!
# Polynomial-time traversal of every counted scope

The finite dispatcher consumes one whole scope per cycle. Its full encoded
state strictly shrinks, so every body call and transfer has a uniform bound
in the original wire length. Every scope has a count delimiter, including
empty scopes; the number of iterations is therefore at most that length.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace ScopeLoop

def result (input : ScopeIteration.Output) : Bool :=
  ScopeIteration.finish input.2.1 input.2.2 input.1

theorem result_eq (input : ScopeIteration.Output) :
    result input = (input.1 || PrimalEdgeEnumeration.adjacent input.2.2
      input.2.1.1 input.2.1.2) := ScopeIteration.finish_eq _ _ _

/-- Every counted scope, including an empty one, occupies at least one cell. -/
theorem scopes_length_le_state (input : ScopeIteration.Output) :
    input.2.2.length ≤ (ScopeIteration.outputFinEncoding.encode input).length := by
  rcases input with ⟨answer, endpoints, scopes⟩
  induction scopes generalizing answer with
  | nil => simp
  | cons scope scopes ih =>
      have tail := ih (ScopeIteration.step (answer, endpoints, scope, scopes)).1
      have smaller := ScopeIteration.output_length_lt (answer, endpoints, scope, scopes)
      change (ScopeIteration.outputFinEncoding.encode
        ((ScopeIteration.step (answer, endpoints, scope, scopes)).1, endpoints, scopes)).length <
        (ScopeIteration.outputFinEncoding.encode (answer, endpoints, scope :: scopes)).length at smaller
      dsimp only at tail ⊢
      simp only [List.length_cons]
      omega

noncomputable section

/-- Uniform cost of one complete cycle at a bound on the full state length.
It also bounds the final empty-state scan and output. -/
def passTime : Polynomial ℕ := ScopeLoopMachine.body.time + 4 * Polynomial.X + 4

theorem passTime_eval (s : ℕ) :
    passTime.eval s = ScopeLoopMachine.body.time.eval s + 4 * s + 4 := by
  simp [passTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]

/-- Structural induction and strict wire shrinkage bound every complete cycle. -/
def run_bounded (endpoints : ℕ × ℕ) (scopes : List (List ℕ)) (answer : Bool) (bound : ℕ)
    (size : (ScopeIteration.outputFinEncoding.encode (answer, endpoints, scopes)).length ≤ bound) :
    ScopeLoopMachine.Run (ScopeLoopMachine.ready (answer, endpoints, scopes))
      (ScopeLoopMachine.done (ScopeIteration.finish endpoints scopes answer))
      ((scopes.length + 1) * passTime.eval bound) := by
  induction scopes generalizing answer with
  | nil =>
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (ScopeLoopMachine.exit_run answer endpoints)
      simp only [List.length_nil, zero_add, one_mul, passTime_eval]
      omega
  | cons scope scopes ih =>
      let input : ScopeIteration.Input := (answer, endpoints, scope, scopes)
      have input_size : (ScopeIteration.inputFinEncoding.encode input).length ≤ bound := size
      have output_size := (Nat.le_of_lt (ScopeIteration.output_length_lt input)).trans input_size
      have tail_size : (ScopeIteration.outputFinEncoding.encode
          ((ScopeIteration.step input).1, endpoints, scopes)).length ≤ bound := output_size
      have tail_run := ih (ScopeIteration.step input).1 tail_size
      have cycle := ScopeLoopMachine.iteration_cycle answer endpoints scope scopes
      have body_cost := LeanNPHardness.MachineRuntime.polynomial_eval_mono
        ScopeLoopMachine.body.time input_size
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (ScopeLoopMachine.seq cycle tail_run)
      simp only [List.length_cons, passTime_eval]
      change ScopeLoopMachine.body.time.eval (ScopeIteration.inputFinEncoding.encode input).length +
        2 * (ScopeIteration.inputFinEncoding.encode input).length +
        2 * (ScopeIteration.outputFinEncoding.encode (ScopeIteration.step input)).length + 4 +
        (scopes.length + 1) * (ScopeLoopMachine.body.time.eval bound + 4 * bound + 4) ≤
        (scopes.length + 1 + 1) * (ScopeLoopMachine.body.time.eval bound + 4 * bound + 4)
      nlinarith

/-- A polynomial in the original complete wire length, including all cycles,
their control/transfers, and the final empty-state exit. -/
def time : Polynomial ℕ := (Polynomial.X + 1) * passTime

theorem time_eval (s : ℕ) :
    time.eval s = (s + 1) * (ScopeLoopMachine.body.time.eval s + 4 * s + 4) := by
  simp [time, passTime_eval, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]

def outputsInTime (input : ScopeIteration.Output) :
    TM2OutputsInTime ScopeLoopMachine.computer (ScopeIteration.outputFinEncoding.encode input)
      (some (finEncodingBoolBool.encode (result input)))
      (time.eval (ScopeIteration.outputFinEncoding.encode input).length) := by
  have h := run_bounded input.2.1 input.2.2 input.1
    (ScopeIteration.outputFinEncoding.encode input).length (by rfl)
  have h' := LeanNPHardness.MachinePrimitives.evalsToInTimeMono h
    (Nat.mul_le_mul_right (passTime.eval (ScopeIteration.outputFinEncoding.encode input).length)
      (Nat.add_le_add_right (scopes_length_le_state input) 1))
  simpa only [ScopeLoopMachine.ready_eq_initList, ScopeLoopMachine.done_eq_haltList,
    result, time, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one] using h'

end

end ScopeLoop

/-- Complete repeated scope testing, including dispatch, transfer and cleanup,
from an arbitrary checked Boolean/endpoint/counted-scope state. -/
noncomputable def scopeLoopComputableInPolyTime :
    @TM2ComputableInPolyTime ScopeIteration.Output Bool
      ScopeIteration.outputFinEncoding finEncodingBoolBool ScopeLoop.result where
  tm := ScopeLoopMachine.computer
  inputAlphabet := Equiv.refl ScopeLoopMachine.Wire
  outputAlphabet := Equiv.refl Bool
  time := ScopeLoop.time
  outputsFun input := by simpa [Equiv.refl] using ScopeLoop.outputsInTime input

/-- With an initially false accumulator, the actual machine returns exactly
whether the two endpoints occur together in at least one whole scope. -/
noncomputable def scopeLoop_adjacent_outputsInTime (endpoints : ℕ × ℕ) (scopes : List (List ℕ)) :
    TM2OutputsInTime ScopeLoopMachine.computer
      (ScopeIteration.outputFinEncoding.encode (false, endpoints, scopes))
      (some (finEncodingBoolBool.encode (PrimalEdgeEnumeration.adjacent scopes endpoints.1 endpoints.2)))
      (ScopeLoop.time.eval (ScopeIteration.outputFinEncoding.encode (false, endpoints, scopes)).length) := by
  simpa only [ScopeLoop.result, ScopeIteration.finish_false_eq_adjacent] using
    ScopeLoop.outputsInTime (false, endpoints, scopes)

#print axioms ScopeLoop.result_eq
#print axioms ScopeLoop.scopes_length_le_state
#print axioms ScopeLoop.run_bounded
#print axioms ScopeLoop.outputsInTime
#print axioms scopeLoopComputableInPolyTime
#print axioms scopeLoop_adjacent_outputsInTime

end PhdThesisLean.AllDifferentCSPMachine
