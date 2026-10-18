import PhdThesisLean.AllDifferentCSPPositiveScanLoopMachine
import PhdThesisLean.AllDifferentCSPPositiveScanInitialization

/-!
# Polynomial-time construction of the complete positive-scan state

The controller visits the `n(q+1)` candidate cells with a computed active answer.
Every reached wire is bounded cubically in the original retained section size;
all body calls and transfers therefore share one polynomial bound. The entry
machine constructs the seed and active answer from the actual input, including
zero variables. No loop count or control answer is supplied by the caller.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PositiveScanLoop

def entry (value : CountedPositiveSections.Value) : PositiveCandidateTest.Output :=
  PositiveControl.evaluate false (PositiveScanInitialization.seed value)

-- Cache the nested section instance: expanding the whole product at once
-- can exceed Lean's default instance-result size bound.
local instance : DecidableEq CountedPositiveSections.Domains := inferInstance
local instance : DecidableEq CountedPositiveSections.Sections := inferInstance
local instance : DecidableEq CountedPositiveSections.Value := inferInstance
local instance : DecidableEq PositiveCandidateQueries.Input := inferInstance
local instance : DecidableEq PositiveCandidateTest.Output := inferInstance

/-- An internal interface whose decoder checks the exact initialized state. -/
def inputDecode (wire : List PositiveScanLoopMachine.Wire) : Option CountedPositiveSections.Value := do
  let state ← PositiveCandidateTest.outputFinEncoding.decode wire
  let value := state.2.2.1
  if state = entry value then some value else none

def inputFinEncoding : FinEncoding CountedPositiveSections.Value where
  Γ := PositiveScanLoopMachine.Wire
  encode value := PositiveCandidateTest.outputFinEncoding.encode (entry value)
  decode := inputDecode
  decode_encode value := by
    simp [inputDecode, PositiveCandidateTest.outputFinEncoding.decode_encode, entry, PositiveControl.evaluate,
      PositiveScanInitialization.seed, PositiveAdvance.seed]
  ΓFin := inferInstance

theorem input_length (value : CountedPositiveSections.Value) :
    (inputFinEncoding.encode value).length =
      (CountedPositiveSections.finEncoding.encode value).length + 1 := by
  exact (PositiveControl.output_length false _).trans
    (congrArg (· + 1) (PositiveScanInitialization.output_length value))

/-- The complete final state retains sections and the exact ordered positive rows. -/
def result (value : CountedPositiveSections.Value) : PositiveCandidateQueries.Input :=
  ((value.1.1.2, 0), value, (PositiveAdvance.run value (PositiveAdvance.gridSize value)).2.2)

theorem run_eq_result (value : CountedPositiveSections.Value) :
    PositiveAdvance.run value (PositiveAdvance.gridSize value) = result value := by
  apply Prod.ext (PositiveAdvance.run_exhausted value)
  exact Prod.ext (PositiveAdvance.run_retained value _) rfl

/-- The result contains exactly the specified ordered positive rows when the
stored occurrence count is consistent. The compiler constructs this count. -/
theorem result_rows (value : CountedPositiveSections.Value)
    (counted : value.1.1.1.2 = value.1.1.1.1.length) :
    (result value).2.2 = (PositiveEnumeration.enumerate value.1.1.2 value.1.1.1.1).map
      (fun candidate => (candidate, value.2.2)) := PositiveAdvance.run_rows_eq value counted

theorem result_ofRuntimeSystem (C : RuntimeSystem) :
    ((result (CountedPositiveSections.ofRuntimeSystem C)).2.2.map PositiveRows.row) =
      C.toExplicitSystem.pinningRows.map RuntimeResidualRow.ofResidualRow :=
  PositiveAdvance.run_ofRuntimeSystem C

theorem result_outputEncode_ofRuntimeSystem (C : RuntimeSystem) :
    PositiveRows.outputEncode (result (CountedPositiveSections.ofRuntimeSystem C)).2.2 =
      DomainFieldSection.rowPayloadEncode
        ((C.toExplicitSystem.pinningRows.map RuntimeResidualRow.ofResidualRow).map
          RuntimeResidualRow.toNatList) := PositiveAdvance.run_outputEncode_ofRuntimeSystem C

theorem result_retained (value : CountedPositiveSections.Value) :
    (result value).2.1 = value := rfl

theorem result_exhausted (value : CountedPositiveSections.Value) :
    (result value).1 = (value.1.1.2, 0) := rfl

theorem result_nodup (value : CountedPositiveSections.Value) :
    (result value).2.2.Nodup := PositiveAdvance.run_nodup value _

theorem result_length_le_cubic (value : CountedPositiveSections.Value) :
    (PositiveCandidateQueries.inputFinEncoding.encode (result value)).length ≤
      16 * ((CountedPositiveSections.finEncoding.encode value).length + 1) ^ 3 := by
  rw [← run_eq_result]
  exact PositiveAdvance.run_length_le_cubic value _

example : result (((([], 0), 0), []), ([], 1)) =
    ((0, 0), (((([], 0), 0), []), ([], 1)), []) := rfl
example : result (((([], 0), 3), []), ([], 1)) =
    ((3, 0), (((([], 0), 3), []), ([], 1)), []) := rfl
example : (result (((([(0, 2), (0, 2), (2, 1)], 3), 4), [[]]), ([(0, 2)], 7))).2.2 =
    [((0, 2), 7), ((2, 1), 7)] := rfl
example : (result (CountedPositiveSections.ofRuntimeSystem
    ⟨[[100, 7, 100], [], [42, 7]], [[0, 2], [2, 0, 2]]⟩)).2.2 =
    [((0, 1), 2), ((0, 3), 2), ((2, 1), 2), ((2, 2), 2)] := by decide

def flagged (value : CountedPositiveSections.Value) (k : ℕ) : PositiveCandidateTest.Output :=
  PositiveControl.evaluate false (PositiveAdvance.run value k)

theorem flagged_zero (value : CountedPositiveSections.Value) : flagged value 0 = entry value := rfl

theorem flagged_step (value : CountedPositiveSections.Value) (k : ℕ) :
    PositiveScanLoopMachine.step (flagged value k) = flagged value (k + 1) := by
  simp only [PositiveScanLoopMachine.step, flagged, PositiveControl.retained_eq, PositiveAdvance.run_succ]

theorem flagged_length_le (value : CountedPositiveSections.Value) (k : ℕ) :
    (PositiveCandidateTest.outputFinEncoding.encode (flagged value k)).length ≤
      16 * ((CountedPositiveSections.finEncoding.encode value).length + 1) ^ 3 + 1 := by
  exact (PositiveControl.output_length false _).le.trans
    (Nat.add_le_add_right (PositiveAdvance.run_length_le_cubic value k) 1)

noncomputable section

/-- A single polynomial bounds complete cycles and the final false-answer exit. -/
def passTime : Polynomial ℕ := PositiveScanLoopMachine.body.time + 4 * Polynomial.X + 4

theorem passTime_eval (s : ℕ) :
    passTime.eval s = PositiveScanLoopMachine.body.time.eval s + 4 * s + 4 := by
  simp [passTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]

/-- Induction on the remaining grid budget includes every inter-call transfer
and the final computed false-answer scan. -/
def run_bounded (value : CountedPositiveSections.Value) (remaining k bound : ℕ)
    (remaining_eq : k + remaining = PositiveAdvance.gridSize value)
    (size : ∀ j, (PositiveCandidateTest.outputFinEncoding.encode (flagged value j)).length ≤ bound) :
    PositiveScanLoopMachine.Run (PositiveScanLoopMachine.ready (flagged value k))
      (PositiveScanLoopMachine.done (result value)) ((remaining + 1) * passTime.eval bound) := by
  induction remaining generalizing k with
  | zero =>
      have hk : k = PositiveAdvance.gridSize value := by omega
      subst k
      have hf : flagged value (PositiveAdvance.gridSize value) = (false, result value) := by
        rw [flagged, run_eq_result]
        exact PositiveControl.exhausted value _
      have hs := size (PositiveAdvance.gridSize value)
      rw [hf] at hs ⊢
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (PositiveScanLoopMachine.exit_run (result value))
      simp only [zero_add, one_mul, passTime_eval]
      omega
  | succ remaining ih =>
      have hk : k < PositiveAdvance.gridSize value := by omega
      have ht : flagged value k = (true, PositiveAdvance.run value k) := by
        apply Prod.ext
        · exact (PositiveControl.run_active_iff value k).mpr hk
        · rfl
      have cycle := PositiveScanLoopMachine.iteration_cycle (PositiveAdvance.run value k)
      rw [← ht, flagged_step] at cycle
      have tail := ih (k + 1) (by omega)
      have body_cost := LeanNPHardness.MachineRuntime.polynomial_eval_mono
        PositiveScanLoopMachine.body.time (size k)
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (PositiveScanLoopMachine.seq cycle tail)
      simp only [passTime_eval]
      have hi := size k
      have ho := size (k + 1)
      nlinarith

/-- Polynomial substitution charges the growing state in original input bits. -/
def wireBound : Polynomial ℕ := 16 * (Polynomial.X + 1) ^ 3 + 1

def time : Polynomial ℕ := (Polynomial.X * (Polynomial.X + 1) + 1) * passTime.comp wireBound

theorem wireBound_eval (s : ℕ) : wireBound.eval s = 16 * (s + 1) ^ 3 + 1 := by
  simp [wireBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_X]

theorem time_eval (s : ℕ) :
    time.eval s = (s * (s + 1) + 1) * passTime.eval (16 * (s + 1) ^ 3 + 1) := by
  simp [time, wireBound_eval, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_comp]

def outputsInTime (value : CountedPositiveSections.Value) :
    TM2OutputsInTime PositiveScanLoopMachine.computer (inputFinEncoding.encode value)
      (some (PositiveCandidateQueries.inputFinEncoding.encode (result value)))
      (time.eval (inputFinEncoding.encode value).length) := by
  let s := (CountedPositiveSections.finEncoding.encode value).length
  have run := run_bounded value (PositiveAdvance.gridSize value) 0 (16 * (s + 1) ^ 3 + 1)
    (by omega) (flagged_length_le value)
  have count := PositiveAdvance.iterations_le_wire_quadratic value
  have h := LeanNPHardness.MachinePrimitives.evalsToInTimeMono run
    (Nat.mul_le_mul_right (passTime.eval (16 * (s + 1) ^ 3 + 1))
      (Nat.add_le_add_right count 1))
  have bounded : PositiveScanLoopMachine.Run (PositiveScanLoopMachine.ready (flagged value 0))
      (PositiveScanLoopMachine.done (result value)) (time.eval (inputFinEncoding.encode value).length) :=
    LeanNPHardness.MachinePrimitives.evalsToInTimeMono h
    (by rw [← time_eval]; exact LeanNPHardness.MachineRuntime.polynomial_eval_mono time
          (by rw [input_length]; omega))
  simpa only [flagged_zero, PositiveScanLoopMachine.ready_eq_initList,
    PositiveScanLoopMachine.done_eq_haltList, inputFinEncoding] using! bounded

/-- Checked loop interface; the entry machine below constructs its control bit. -/
def computableInPolyTime :
    @TM2ComputableInPolyTime CountedPositiveSections.Value PositiveCandidateQueries.Input
      inputFinEncoding PositiveCandidateQueries.inputFinEncoding result where
  tm := PositiveScanLoopMachine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := time
  outputsFun value := by simpa [Equiv.refl] using outputsInTime value

/-- Construct both zero counters, empty positive rows and the active bit internally. -/
def entryComputableInPolyTime :
    @TM2ComputableInPolyTime CountedPositiveSections.Value CountedPositiveSections.Value
      CountedPositiveSections.finEncoding inputFinEncoding id := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    positiveScanInitializationComputableInPolyTime positiveActiveComputableInPolyTime
  exact { composed with
    outputsFun := fun value => by
      simpa only [Function.comp_def, inputFinEncoding, entry, id_eq] using composed.outputsFun value }

end

end PositiveScanLoop

/-- The complete finite grid scan from retained sections, with no supplied
counters, control answers, accumulator invariants or iteration budget. -/
noncomputable def positiveEnumerationComputableInPolyTime :
    @TM2ComputableInPolyTime CountedPositiveSections.Value PositiveCandidateQueries.Input
      CountedPositiveSections.finEncoding PositiveCandidateQueries.inputFinEncoding PositiveScanLoop.result := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    PositiveScanLoop.entryComputableInPolyTime PositiveScanLoop.computableInPolyTime
  exact { composed with
    outputsFun := fun value => by simpa only [Function.comp_def, id_eq] using composed.outputsFun value }

/-- Actual Boolean compiler input to the terminal counters, retained ranked
sections and exact ordered positive rows. -/
noncomputable def runtimeCompilerPositiveEnumerationComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem PositiveCandidateQueries.Input
      RuntimeCompilerInput.finEncoding PositiveCandidateQueries.inputFinEncoding
      (fun C => PositiveScanLoop.result (CountedPositiveSections.ofRuntimeSystem C)) := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerCountedPositiveSectionsComputableInPolyTime positiveEnumerationComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by simpa only [Function.comp_def] using composed.outputsFun C }

#print axioms PositiveScanLoop.inputFinEncoding
#print axioms PositiveScanLoop.result_retained
#print axioms PositiveScanLoop.result_exhausted
#print axioms PositiveScanLoop.result_nodup
#print axioms PositiveScanLoop.result_length_le_cubic
#print axioms PositiveScanLoop.result_rows
#print axioms PositiveScanLoop.result_ofRuntimeSystem
#print axioms PositiveScanLoop.result_outputEncode_ofRuntimeSystem
#print axioms PositiveScanLoop.run_eq_result
#print axioms PositiveScanLoop.flagged_length_le
#print axioms PositiveScanLoop.run_bounded
#print axioms PositiveScanLoop.outputsInTime
#print axioms PositiveScanLoop.computableInPolyTime
#print axioms PositiveScanLoop.entryComputableInPolyTime
#print axioms positiveEnumerationComputableInPolyTime
#print axioms runtimeCompilerPositiveEnumerationComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
