import PhdThesisLean.AllDifferentCSPOccurrenceLoopMachine

/-!
# Polynomial-time traversal of all domain occurrences

Each finite cycle removes one occurrence and appends its canonical binary
rank record. The decreasing budget pays for rank growth, so every intermediate
wire fits a fixed quadratic bound in the original wire length. Charging the
body, scans, transfers and final exit at that bound proves a genuine
finite-machine polynomial-time theorem for the complete traversal.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace OccurrenceLoop

def result (input : OccurrenceIteration.State) : List (ℕ × ℕ) :=
  OccurrenceIteration.finish input.1.2 input.1.1 input.2

theorem result_eq (input : OccurrenceIteration.State) :
    result input = input.2 ++ input.1.1.map
      (fun occurrence => (occurrence.1, DomainSymbols.rank input.1.2 occurrence.2)) :=
  OccurrenceIteration.finish_eq_append_map _ _ _

theorem occurrences_length_le_state (input : OccurrenceIteration.State) :
    input.1.1.length ≤ (OccurrenceIteration.stateFinEncoding.encode input).length := by
  have h := OccurrenceIteration.occurrences_length_le_wire input.1.1
  rw [OccurrenceIteration.state_length]
  omega

noncomputable section

/-- One complete cycle, including dispatch and return transfers, at a bound
on the complete serialized state. This also pays for the final empty exit. -/
def passTime : Polynomial ℕ := OccurrenceLoopMachine.body.time + 4 * Polynomial.X + 4

theorem passTime_eval (s : ℕ) :
    passTime.eval s = OccurrenceLoopMachine.body.time.eval s + 4 * s + 4 := by
  simp [passTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]

/-- Induction uses a bound on the decreasing budget, rather than assuming
that serialized states shrink when binary ranks replace small source values. -/
def run_bounded (occurrences : List (ℕ × ℕ)) (symbols : List ℕ)
    (accum : List (ℕ × ℕ)) (bound : ℕ)
    (size : OccurrenceIteration.budget ((occurrences, symbols), accum) ≤ bound) :
    OccurrenceLoopMachine.Run (OccurrenceLoopMachine.ready ((occurrences, symbols), accum))
      (OccurrenceLoopMachine.done (OccurrenceIteration.finish symbols occurrences accum))
      ((occurrences.length + 1) * passTime.eval bound) := by
  induction occurrences generalizing accum with
  | nil =>
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono
        (OccurrenceLoopMachine.exit_run symbols accum)
      simp only [List.length_nil, zero_add, one_mul, passTime_eval]
      unfold OccurrenceIteration.budget at size
      omega
  | cons occurrence occurrences ih =>
      let input : OccurrenceIteration.Input := ((occurrence, occurrences, symbols), accum)
      have source_budget : OccurrenceIteration.budget (OccurrenceIteration.source input) ≤ bound := size
      have next_budget := (OccurrenceIteration.step_budget_le input).trans source_budget
      have input_size : (OccurrenceIteration.inputFinEncoding.encode input).length ≤ bound := by
        unfold OccurrenceIteration.budget at source_budget
        rw [OccurrenceIteration.source_encode] at source_budget
        omega
      have output_size : (OccurrenceIteration.stateFinEncoding.encode
          (OccurrenceIteration.step input)).length ≤ bound := by
        unfold OccurrenceIteration.budget at next_budget
        omega
      have tail_run := ih (OccurrenceIteration.step input).2 next_budget
      have cycle := OccurrenceLoopMachine.iteration_cycle occurrence occurrences symbols accum
      have body_cost := LeanNPHardness.MachineRuntime.polynomial_eval_mono
        OccurrenceLoopMachine.body.time input_size
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono
        (OccurrenceLoopMachine.seq cycle tail_run)
      simp only [List.length_cons, passTime_eval]
      change OccurrenceLoopMachine.body.time.eval (OccurrenceIteration.inputFinEncoding.encode input).length +
        2 * (OccurrenceIteration.inputFinEncoding.encode input).length +
        2 * (OccurrenceIteration.stateFinEncoding.encode (OccurrenceIteration.step input)).length + 4 +
        (occurrences.length + 1) * (OccurrenceLoopMachine.body.time.eval bound + 4 * bound + 4) ≤
        (occurrences.length + 1 + 1) * (OccurrenceLoopMachine.body.time.eval bound + 4 * bound + 4)
      nlinarith

/-- Uniform wire-size bound for every stage, as a polynomial in initial bits. -/
def sizeBound : Polynomial ℕ := 2 * (Polynomial.X + 1) ^ 2

theorem sizeBound_eval (s : ℕ) : sizeBound.eval s = 2 * (s + 1) ^ 2 := by
  simp [sizeBound, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow]

/-- Number of cycles times their uniform cost, including the final exit. -/
def time : Polynomial ℕ := (Polynomial.X + 1) * passTime.comp sizeBound

theorem time_eval (s : ℕ) :
    time.eval s = (s + 1) * (OccurrenceLoopMachine.body.time.eval (2 * (s + 1) ^ 2) +
      4 * (2 * (s + 1) ^ 2) + 4) := by
  simp [time, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_comp,
    sizeBound_eval, passTime_eval]

def outputsInTime (input : OccurrenceIteration.State) :
    TM2OutputsInTime OccurrenceLoopMachine.computer
      (OccurrenceIteration.stateFinEncoding.encode input)
      (some (DomainFieldRow.outputEncode (result input)))
      (time.eval (OccurrenceIteration.stateFinEncoding.encode input).length) := by
  have h := run_bounded input.1.1 input.1.2 input.2
    (2 * ((OccurrenceIteration.stateFinEncoding.encode input).length + 1) ^ 2)
    (OccurrenceIteration.budget_le_quadratic input)
  have h' := LeanNPHardness.MachinePrimitives.evalsToInTimeMono h
    (Nat.mul_le_mul_right
      (passTime.eval (2 * ((OccurrenceIteration.stateFinEncoding.encode input).length + 1) ^ 2))
      (Nat.add_le_add_right (occurrences_length_le_state input) 1))
  simpa only [OccurrenceLoopMachine.ready_eq_initList, OccurrenceLoopMachine.done_eq_haltList,
    result, time, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_comp, sizeBound_eval] using h'

end

end OccurrenceLoop

/-- Complete repeated canonical relabelling, including the finite dispatcher,
ordered output, every transfer, and cleanup, polynomial in actual input bits. -/
noncomputable def occurrenceLoopComputableInPolyTime :
    @TM2ComputableInPolyTime OccurrenceIteration.State (List (ℕ × ℕ))
      OccurrenceIteration.stateFinEncoding DomainFieldRow.outputFinEncoding
      OccurrenceLoop.result where
  tm := OccurrenceLoopMachine.computer
  inputAlphabet := Equiv.refl OccurrenceLoopMachine.Wire
  outputAlphabet := Equiv.refl (Option Bool)
  time := OccurrenceLoop.time
  outputsFun input := by
    simpa [Equiv.refl, DomainFieldRow.outputFinEncoding] using OccurrenceLoop.outputsInTime input

#print axioms OccurrenceLoop.result_eq
#print axioms OccurrenceLoop.occurrences_length_le_state
#print axioms OccurrenceLoop.run_bounded
#print axioms OccurrenceLoop.outputsInTime
#print axioms occurrenceLoopComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
