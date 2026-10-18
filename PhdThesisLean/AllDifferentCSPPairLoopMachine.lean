import PhdThesisLean.AllDifferentCSPPairDispatch
import PhdThesisLean.AllDifferentCSPFlaggedLoopMachine

/-!
# Finite repeated pair-scan controller

A tagged, machine-computed active bit selects each complete dispatch. The body
advances one candidate and computes the next active bit. On exhaustion the
controller removes that bit and returns the complete terminal state. All body
calls, ordered transfers, final scans and scratch cleanup are charged.
-/

namespace PhdThesisLean.AllDifferentCSPMachine.PairLoopMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

noncomputable section

def step (input : PairTest.Output) : PairTest.Output :=
  PairControl.evaluate false (PairAdvance.advance input.2)

/-- Erasure, the complete dispatcher, and the next computed exhaustion test. -/
def body : @TM2ComputableInPolyTime PairTest.Output PairTest.Output
    PairTest.outputFinEncoding PairTest.outputFinEncoding step := by
  let advance := compositionComputableInPolyTime _ _ _ _ _
    pairDecisionEraseComputableInPolyTime PairDispatch.computableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _ advance pairActiveComputableInPolyTime
  exact { composed with
    outputsFun := fun input => by
      simpa only [Function.comp_def, step] using composed.outputsFun input }

abbrev Wire := Sum Bool PairQueriesMachine.Input
abbrev Output := PairQueriesMachine.Input

local instance : Inhabited PairQueries.inputFinEncoding.Γ := ⟨.inl (.inl false)⟩

abbrev computer := @FlaggedLoopMachine.computer _ PairQueries.inputFinEncoding _ step body
abbrev ready := @FlaggedLoopMachine.ready _ PairQueries.inputFinEncoding _ step body
abbrev done := @FlaggedLoopMachine.done _ PairQueries.inputFinEncoding _ step body
abbrev Run := @FlaggedLoopMachine.Run _ PairQueries.inputFinEncoding _ step body
abbrev seq := @FlaggedLoopMachine.seq _ PairQueries.inputFinEncoding _ step body
def iteration_cycle (state : PairQueries.Input) :
    Run (ready (true, state)) (ready (step (true, state)))
      (body.time.eval (PairTest.outputFinEncoding.encode (true, state)).length +
        2 * (PairTest.outputFinEncoding.encode (true, state)).length +
        2 * (PairTest.outputFinEncoding.encode (step (true, state))).length + 4) :=
  FlaggedLoopMachine.iteration_cycle (body := body) state
def exit_run (state : PairQueries.Input) :
    Run (ready (false, state)) (done state)
      (2 * (PairTest.outputFinEncoding.encode (false, state)).length + 2) :=
  FlaggedLoopMachine.exit_run (body := body) state
def ready_eq_initList (input : PairTest.Output) :
    ready input = initList computer (PairTest.outputFinEncoding.encode input) :=
  FlaggedLoopMachine.ready_eq_initList (body := body) input
def done_eq_haltList (state : PairQueries.Input) : done state = haltList computer (PairQueries.inputFinEncoding.encode state) :=
  FlaggedLoopMachine.done_eq_haltList (body := body) state

#print axioms body
#print axioms iteration_cycle
#print axioms exit_run

end

end PhdThesisLean.AllDifferentCSPMachine.PairLoopMachine
