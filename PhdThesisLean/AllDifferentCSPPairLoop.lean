import PhdThesisLean.AllDifferentCSPPairLoopMachine

/-!
# Polynomial-time construction of the complete pair-scan state

The controller visits the `n²` candidate cells with a computed active answer.
Every reached wire is bounded cubically in the original retained section size;
all body calls and transfers therefore share one polynomial bound. The entry
machine constructs the seed and active answer from the actual input, including
zero variables. No loop count or control answer is supplied by the caller.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PairLoop

def entry (value : BoundedRelabelledSections.Value) : PairTest.Output :=
  PairControl.evaluate false (PairInitialization.seed value)

-- Cache the nested section instance: expanding the whole product at once
-- exceeds Lean's default instance-result size bound (160 >= 128).
local instance : DecidableEq BoundedRelabelledSections.Value := inferInstance
local instance : DecidableEq PairTest.Output := inferInstance

/-- An internal interface whose decoder checks the exact initialized state. -/
def inputDecode (wire : List PairLoopMachine.Wire) : Option BoundedRelabelledSections.Value := do
  let state ← PairTest.outputFinEncoding.decode wire
  let value := state.2.2.1
  if state = entry value then some value else none

def inputFinEncoding : FinEncoding BoundedRelabelledSections.Value where
  Γ := PairLoopMachine.Wire
  encode value := PairTest.outputFinEncoding.encode (entry value)
  decode := inputDecode
  decode_encode value := by
    simp [inputDecode, PairTest.outputFinEncoding.decode_encode, entry, PairControl.evaluate,
      PairInitialization.seed]
  ΓFin := inferInstance

theorem input_length (value : BoundedRelabelledSections.Value) :
    (inputFinEncoding.encode value).length =
      (BoundedRelabelledSections.finEncoding.encode value).length + 1 := by
  exact (PairControl.output_length false _).trans
    (congrArg (· + 1) (PairInitialization.output_length value))

/-- The complete final state retains sections and the exact ordered edge list. -/
def result (value : BoundedRelabelledSections.Value) : PairQueries.Input :=
  ((value.1.2, 0), value, BoundedRelabelledSections.edges value)

theorem run_eq_result (value : BoundedRelabelledSections.Value) :
    PairAdvance.run value (value.1.2 ^ 2) = result value := by
  apply Prod.ext (PairAdvance.run_exhausted value)
  exact Prod.ext (PairAdvance.run_retained value _) (PairAdvance.run_edges_eq value)

def flagged (value : BoundedRelabelledSections.Value) (k : ℕ) : PairTest.Output :=
  PairControl.evaluate false (PairAdvance.run value k)

theorem flagged_zero (value : BoundedRelabelledSections.Value) : flagged value 0 = entry value := rfl

theorem flagged_step (value : BoundedRelabelledSections.Value) (k : ℕ) :
    PairLoopMachine.step (flagged value k) = flagged value (k + 1) := by
  simp only [PairLoopMachine.step, flagged, PairControl.retained_eq, PairAdvance.run_succ]

theorem flagged_length_le (value : BoundedRelabelledSections.Value) (k : ℕ) :
    (PairTest.outputFinEncoding.encode (flagged value k)).length ≤
      12 * ((BoundedRelabelledSections.finEncoding.encode value).length + 1) ^ 3 + 1 := by
  exact (PairControl.output_length false _).le.trans
    (Nat.add_le_add_right (PairAdvance.iterate_length_le_cubic value k) 1)

noncomputable section

/-- A single polynomial bounds complete cycles and the final false-answer exit. -/
def passTime : Polynomial ℕ := PairLoopMachine.body.time + 4 * Polynomial.X + 4

theorem passTime_eval (s : ℕ) :
    passTime.eval s = PairLoopMachine.body.time.eval s + 4 * s + 4 := by
  simp [passTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]

/-- Induction on the remaining grid budget includes every inter-call transfer
and the final computed false-answer scan. -/
def run_bounded (value : BoundedRelabelledSections.Value) (remaining k bound : ℕ)
    (remaining_eq : k + remaining = value.1.2 ^ 2)
    (size : ∀ j, (PairTest.outputFinEncoding.encode (flagged value j)).length ≤ bound) :
    PairLoopMachine.Run (PairLoopMachine.ready (flagged value k))
      (PairLoopMachine.done (result value)) ((remaining + 1) * passTime.eval bound) := by
  induction remaining generalizing k with
  | zero =>
      have hk : k = value.1.2 ^ 2 := by omega
      subst k
      have hf : flagged value (value.1.2 ^ 2) = (false, result value) := by
        rw [flagged, run_eq_result]
        exact PairControl.exhausted value _
      have hs := size (value.1.2 ^ 2)
      rw [hf] at hs ⊢
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (PairLoopMachine.exit_run (result value))
      simp only [zero_add, one_mul, passTime_eval]
      omega
  | succ remaining ih =>
      have hk : k < value.1.2 ^ 2 := by omega
      have ht : flagged value k = (true, PairAdvance.run value k) := by
        apply Prod.ext
        · exact (PairControl.run_active_iff value k).mpr hk
        · rfl
      have cycle := PairLoopMachine.iteration_cycle (PairAdvance.run value k)
      rw [← ht, flagged_step] at cycle
      have tail := ih (k + 1) (by omega)
      have body_cost := LeanNPHardness.MachineRuntime.polynomial_eval_mono
        PairLoopMachine.body.time (size k)
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (PairLoopMachine.seq cycle tail)
      simp only [passTime_eval]
      have hi := size k
      have ho := size (k + 1)
      nlinarith

/-- Polynomial substitution charges the growing state in original input bits. -/
def wireBound : Polynomial ℕ := 12 * (Polynomial.X + 1) ^ 3 + 1

def time : Polynomial ℕ := (Polynomial.X ^ 2 + 1) * passTime.comp wireBound

theorem wireBound_eval (s : ℕ) : wireBound.eval s = 12 * (s + 1) ^ 3 + 1 := by
  simp [wireBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_X]

theorem time_eval (s : ℕ) :
    time.eval s = (s ^ 2 + 1) * passTime.eval (12 * (s + 1) ^ 3 + 1) := by
  simp [time, wireBound_eval, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_comp]

def outputsInTime (value : BoundedRelabelledSections.Value) :
    TM2OutputsInTime PairLoopMachine.computer (inputFinEncoding.encode value)
      (some (PairQueries.inputFinEncoding.encode (result value)))
      (time.eval (inputFinEncoding.encode value).length) := by
  let s := (BoundedRelabelledSections.finEncoding.encode value).length
  have run := run_bounded value (value.1.2 ^ 2) 0 (12 * (s + 1) ^ 3 + 1)
    (by omega) (flagged_length_le value)
  have count := PairAdvance.iterations_le_wire_square value
  have h := LeanNPHardness.MachinePrimitives.evalsToInTimeMono run
    (Nat.mul_le_mul_right (passTime.eval (12 * (s + 1) ^ 3 + 1))
      (Nat.add_le_add_right count 1))
  have bounded : PairLoopMachine.Run (PairLoopMachine.ready (flagged value 0))
      (PairLoopMachine.done (result value)) (time.eval (inputFinEncoding.encode value).length) :=
    LeanNPHardness.MachinePrimitives.evalsToInTimeMono h
    (by rw [← time_eval]; exact LeanNPHardness.MachineRuntime.polynomial_eval_mono time
          (by rw [input_length]; omega))
  simpa only [flagged_zero, PairLoopMachine.ready_eq_initList,
    PairLoopMachine.done_eq_haltList, inputFinEncoding] using bounded

/-- Checked loop interface; the entry machine below constructs its control bit. -/
def computableInPolyTime :
    @TM2ComputableInPolyTime BoundedRelabelledSections.Value PairQueries.Input
      inputFinEncoding PairQueries.inputFinEncoding result where
  tm := PairLoopMachine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := time
  outputsFun value := by simpa [Equiv.refl] using outputsInTime value

/-- Construct both zero endpoints, empty edges and the active bit internally. -/
def entryComputableInPolyTime :
    @TM2ComputableInPolyTime BoundedRelabelledSections.Value BoundedRelabelledSections.Value
      BoundedRelabelledSections.finEncoding inputFinEncoding id := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    pairInitializationComputableInPolyTime pairActiveComputableInPolyTime
  exact { composed with
    outputsFun := fun value => by
      simpa only [Function.comp_def, inputFinEncoding, entry, id_eq] using composed.outputsFun value }

end

end PairLoop

/-- The complete finite grid scan from retained sections, with no supplied
counters, control answers, accumulator invariants or iteration budget. -/
noncomputable def pairEnumerationComputableInPolyTime :
    @TM2ComputableInPolyTime BoundedRelabelledSections.Value PairQueries.Input
      BoundedRelabelledSections.finEncoding PairQueries.inputFinEncoding PairLoop.result := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    PairLoop.entryComputableInPolyTime PairLoop.computableInPolyTime
  exact { composed with
    outputsFun := fun value => by simpa only [Function.comp_def, id_eq] using composed.outputsFun value }

/-- Actual Boolean compiler input to the terminal counters, retained ranked
sections and exact deduplicated primal-edge list. -/
noncomputable def runtimeCompilerPairEnumerationComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem PairQueries.Input
      RuntimeCompilerInput.finEncoding PairQueries.inputFinEncoding
      (fun C => PairLoop.result (BoundedRelabelledSections.ofRuntimeSystem C)) := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerBoundedRelabelledSectionsComputableInPolyTime pairEnumerationComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by simpa only [Function.comp_def] using composed.outputsFun C }

#print axioms PairLoop.inputFinEncoding
#print axioms PairLoop.run_eq_result
#print axioms PairLoop.flagged_length_le
#print axioms PairLoop.run_bounded
#print axioms PairLoop.outputsInTime
#print axioms PairLoop.computableInPolyTime
#print axioms PairLoop.entryComputableInPolyTime
#print axioms pairEnumerationComputableInPolyTime
#print axioms runtimeCompilerPairEnumerationComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
