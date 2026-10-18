import PhdThesisLean.AllDifferentCSPPositiveDispatch
import PhdThesisLean.AllDifferentCSPFlaggedLoopMachine

/-!
# Finite repeated rectangular positive-scan controller

A tagged, machine-computed active bit selects each complete dispatch. The body
advances one candidate and computes the next active bit. On exhaustion the
controller removes that bit and returns the complete terminal state. All body
calls, ordered transfers, final scans and scratch cleanup are charged.
-/

namespace PhdThesisLean.AllDifferentCSPMachine.PositiveScanLoopMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

noncomputable section

def step (input : PositiveCandidateTest.Output) : PositiveCandidateTest.Output :=
  PositiveControl.evaluate false (PositiveAdvance.advance input.2)

/-- Erasure, the complete dispatcher, and the next computed exhaustion test. -/
def body : @TM2ComputableInPolyTime PositiveCandidateTest.Output PositiveCandidateTest.Output
    PositiveCandidateTest.outputFinEncoding PositiveCandidateTest.outputFinEncoding step := by
  let advance := compositionComputableInPolyTime _ _ _ _ _
    positiveDecisionEraseComputableInPolyTime PositiveDispatch.computableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _ advance positiveActiveComputableInPolyTime
  exact { composed with
    outputsFun := fun input => by
      simpa only [Function.comp_def, step] using composed.outputsFun input }

abbrev Wire := Sum Bool PositiveCandidateQueriesMachine.Input
abbrev Output := PositiveCandidateQueriesMachine.Input

local instance : Inhabited PositiveCandidateQueries.inputFinEncoding.Γ := ⟨.inl (.inl false)⟩

abbrev computer := @FlaggedLoopMachine.computer _ PositiveCandidateQueries.inputFinEncoding _ step body
abbrev ready := @FlaggedLoopMachine.ready _ PositiveCandidateQueries.inputFinEncoding _ step body
abbrev done := @FlaggedLoopMachine.done _ PositiveCandidateQueries.inputFinEncoding _ step body
abbrev Run := @FlaggedLoopMachine.Run _ PositiveCandidateQueries.inputFinEncoding _ step body
abbrev seq := @FlaggedLoopMachine.seq _ PositiveCandidateQueries.inputFinEncoding _ step body
def iteration_cycle (state : PositiveCandidateQueries.Input) :
    Run (ready (true, state)) (ready (step (true, state)))
      (body.time.eval (PositiveCandidateTest.outputFinEncoding.encode (true, state)).length +
        2 * (PositiveCandidateTest.outputFinEncoding.encode (true, state)).length +
        2 * (PositiveCandidateTest.outputFinEncoding.encode (step (true, state))).length + 4) :=
  FlaggedLoopMachine.iteration_cycle (body := body) state
def exit_run (state : PositiveCandidateQueries.Input) :
    Run (ready (false, state)) (done state)
      (2 * (PositiveCandidateTest.outputFinEncoding.encode (false, state)).length + 2) :=
  FlaggedLoopMachine.exit_run (body := body) state
def ready_eq_initList (input : PositiveCandidateTest.Output) :
    ready input = initList computer (PositiveCandidateTest.outputFinEncoding.encode input) :=
  FlaggedLoopMachine.ready_eq_initList (body := body) input
def done_eq_haltList (state : PositiveCandidateQueries.Input) : done state = haltList computer (PositiveCandidateQueries.inputFinEncoding.encode state) :=
  FlaggedLoopMachine.done_eq_haltList (body := body) state

#print axioms body
#print axioms iteration_cycle
#print axioms exit_run

end

end PhdThesisLean.AllDifferentCSPMachine.PositiveScanLoopMachine
