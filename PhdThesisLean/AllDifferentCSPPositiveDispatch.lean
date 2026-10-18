import PhdThesisLean.AllDifferentCSPPairDispatch
import PhdThesisLean.AllDifferentCSPPositiveControl

/-!
# Complete finite rectangular positive-scan dispatch

Reuse the conditional-call and Boolean-erasure machines with the positive
scan's retained encoding. Each active step performs exact domain membership,
conditional emission and the selected binary counter action. Exhausted states
are returned unchanged. Every decision and transfer is computed by the machine.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-- Reuse decision erasure for the full positive state, in at most `2s+2` steps. -/
noncomputable def positiveDecisionEraseComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveCandidateTest.Output PositiveCandidateQueries.Input
      PositiveCandidateTest.outputFinEncoding PositiveCandidateQueries.inputFinEncoding Prod.snd :=
  @decisionEraseComputableInPolyTime _ PositiveCandidateQueries.inputFinEncoding ⟨.inl (.inl false)⟩

namespace PositiveDispatch

def selectedStep (state : PositiveCandidateQueries.Input) : PositiveCandidateQueries.Input :=
  if PositiveControl.continues state then PositiveCounters.inner (PositiveCandidateFilter.filter state)
  else PositiveCounters.outer (PositiveCandidateFilter.filter state)

/-- Both gates retain the original choice, so exactly one branch is invoked. -/
noncomputable def selectedComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveCandidateQueries.Input PositiveCandidateQueries.Input
      PositiveCandidateQueries.inputFinEncoding PositiveCandidateQueries.inputFinEncoding selectedStep := by
  let inner := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    finEncodingBoolBool PositiveCandidateQueries.inputFinEncoding PositiveCandidateQueries.inputFinEncoding
    (fun state => PositiveCounters.inner (PositiveCandidateFilter.filter state)) positiveInnerStepComputableInPolyTime
  let outer := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    finEncodingBoolBool PositiveCandidateQueries.inputFinEncoding PositiveCandidateQueries.inputFinEncoding
    (fun state => PositiveCounters.outer (PositiveCandidateFilter.filter state)) positiveOuterStepComputableInPolyTime
  let first := compositionComputableInPolyTime _ _ _ _ _ positiveContinuesComputableInPolyTime
    (PairGateMachine.computableInPolyTime inner true)
  let branches := compositionComputableInPolyTime _ _ _ _ _ first
    (PairGateMachine.computableInPolyTime outer false)
  let composed := compositionComputableInPolyTime _ _ _ _ _ branches positiveDecisionEraseComputableInPolyTime
  exact { composed with
    outputsFun := fun state => by
      cases h : PositiveControl.continues state <;>
        simpa [Function.comp_def, PositiveControl.evaluate, selectedStep, h] using composed.outputsFun state }

/-- Exhaustion skips the complete active step; no predicate is supplied by the caller. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime PositiveCandidateQueries.Input PositiveCandidateQueries.Input
      PositiveCandidateQueries.inputFinEncoding PositiveCandidateQueries.inputFinEncoding PositiveAdvance.advance := by
  let active := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    finEncodingBoolBool PositiveCandidateQueries.inputFinEncoding PositiveCandidateQueries.inputFinEncoding
    selectedStep selectedComputableInPolyTime
  let gated := compositionComputableInPolyTime _ _ _ _ _ positiveActiveComputableInPolyTime
    (PairGateMachine.computableInPolyTime active true)
  let composed := compositionComputableInPolyTime _ _ _ _ _ gated positiveDecisionEraseComputableInPolyTime
  exact { composed with
    outputsFun := fun state => by
      rw [PositiveControl.advance_eq]
      cases h : PositiveControl.active state <;>
        simpa [Function.comp_def, PositiveControl.evaluate, selectedStep, h] using composed.outputsFun state }

/-- Complete dispatched calls have a uniform bound in the original retained input. -/
theorem iterate_steps_le (value : CountedPositiveSections.Value) (k : ℕ) :
    (computableInPolyTime.outputsFun (PositiveAdvance.run value k)).steps ≤
      computableInPolyTime.time.eval
        (16 * ((CountedPositiveSections.finEncoding.encode value).length + 1) ^ 3) :=
  (computableInPolyTime.outputsFun _).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
      (PositiveAdvance.run_length_le_cubic value k))

/-- Exact next-state output with every dispatch cost bounded in the original
retained-section length. `AllDifferentCSPPositiveScanLoop` checks repeated execution. -/
noncomputable def run_step_outputsInTime
    (value : CountedPositiveSections.Value) (k : ℕ) :
    TM2OutputsInTime computableInPolyTime.tm
      ((PositiveCandidateQueries.inputFinEncoding.encode (PositiveAdvance.run value k)).map
        computableInPolyTime.inputAlphabet.symm)
      (some ((PositiveCandidateQueries.inputFinEncoding.encode (PositiveAdvance.run value (k + 1))).map
        computableInPolyTime.outputAlphabet.symm))
      (computableInPolyTime.time.eval
        (16 * ((CountedPositiveSections.finEncoding.encode value).length + 1) ^ 3)) := by
  rw [PositiveAdvance.run_succ]
  exact LeanNPHardness.MachinePrimitives.evalsToInTimeMono
    (computableInPolyTime.outputsFun (PositiveAdvance.run value k))
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
      (PositiveAdvance.run_length_le_cubic value k))

-- Distinct dimensions, final rank, duplicate occurrences, carry, retained rows,
-- and an exhausted state that would otherwise pass the membership test.
example : selectedStep ((0, 1), (((([(0, 1), (0, 1)], 2), 1), []), ([], 3)), []) =
    ((0, 2), (((([(0, 1), (0, 1)], 2), 1), []), ([], 3)), [((0, 1), 3)]) := rfl
example : selectedStep ((1, 2), (((([(1, 2)], 2), 3), [[]]), ([], 0)), [((0, 0), 0)]) =
    ((2, 0), (((([(1, 2)], 2), 3), [[]]), ([], 0)), [((0, 0), 0), ((1, 2), 0)]) := rfl
example : selectedStep ((2, 7), (((([], 8), 3), []), ([], 1000000)), []) =
    ((2, 8), (((([], 8), 3), []), ([], 1000000)), []) := rfl
example : PositiveAdvance.advance ((3, 1), (((([(3, 1)], 2), 3), []), ([], 9)), []) =
    ((3, 1), (((([(3, 1)], 2), 3), []), ([], 9)), []) := rfl
example : PositiveAdvance.advance ((0, 0), (((([], 0), 0), []), ([], 0)), []) =
    ((0, 0), (((([], 0), 0), []), ([], 0)), []) := rfl
example : selectedStep ((0, 0), (((([], 0), 1), []), ([], 1)), []) =
    ((1, 0), (((([], 0), 1), []), ([], 1)), []) := rfl

end PositiveDispatch

#print axioms positiveDecisionEraseComputableInPolyTime
#print axioms PositiveDispatch.selectedComputableInPolyTime
#print axioms PositiveDispatch.computableInPolyTime
#print axioms PositiveDispatch.iterate_steps_le
#print axioms PositiveDispatch.run_step_outputsInTime

end PhdThesisLean.AllDifferentCSPMachine
