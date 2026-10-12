import PhdThesisLean.AllDifferentCSPScopeIteration
import PhdThesisLean.AllDifferentCSPRecordLoopMachine

/-!
# Finite control for repeated same-scope endpoint tests

Instantiate the shared counted-record controller with the complete checked
scope iteration. Its exact scan/call/return costs and cleanup are retained.
-/

namespace PhdThesisLean.AllDifferentCSPMachine.ScopeLoopMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

noncomputable section

def body := scopeIterationComputableInPolyTime
abbrev Wire := RecordLoopMachine.Wire
abbrev sourceCell := RecordLoopMachine.sourceCell

/-- Every scope contributes a count delimiter, even an empty scope. -/
theorem source_present (input : ScopeIteration.Output) :
    (ScopeIteration.outputFinEncoding.encode input).any sourceCell = !input.2.2.isEmpty := by
  rcases input with ⟨answer, endpoints, scopes⟩
  cases scopes <;>
    simp [ScopeTest.outputFinEncoding, ScopeExtraction.remainingFinEncoding,
      ScopeExtraction.endpointsFinEncoding, finEncodingBoolBool, encodeBool,
      finEncodingNatBool, encodingNatBool, DomainFieldSection.rowPayloadFinEncoding,
      DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
      SourceOrderRawFields.encode, List.any_map, List.map_map, Function.comp_def, sourceCell, RecordLoopMachine.sourceCell]

def loopBody : RecordLoopMachine.Body :=
  ⟨body.tm, body.inputAlphabet, body.outputAlphabet⟩

abbrev computer := RecordLoopMachine.computer (body := loopBody)

def ready (input : ScopeIteration.Output) : computer.Cfg :=
  RecordLoopMachine.ready (body := loopBody) (ScopeIteration.outputFinEncoding.encode input)

abbrev done := RecordLoopMachine.done (body := loopBody)
abbrev Run := RecordLoopMachine.Run (body := loopBody)

def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := RecordLoopMachine.seq h h'

/-- A whole cycle includes detection, loading, the checked body and restoration. -/
def iteration_cycle (answer : Bool) (endpoints : ℕ × ℕ) (scope : List ℕ) (scopes : List (List ℕ)) :
    Run (ready (answer, endpoints, scope :: scopes))
      (ready (ScopeIteration.step (answer, endpoints, scope, scopes)))
      (body.time.eval (ScopeIteration.inputFinEncoding.encode (answer, endpoints, scope, scopes)).length +
        2 * (ScopeIteration.inputFinEncoding.encode (answer, endpoints, scope, scopes)).length +
        2 * (ScopeIteration.outputFinEncoding.encode (ScopeIteration.step (answer, endpoints, scope, scopes))).length + 4) := by
  apply RecordLoopMachine.iteration_cycle (body := loopBody)
  · rw [source_present]
    rfl
  · exact body.outputsFun (answer, endpoints, scope, scopes)

/-- Exhaustion returns exactly the accumulated Boolean and clears every other stack. -/
def exit_run (answer : Bool) (endpoints : ℕ × ℕ) :
    Run (ready (answer, endpoints, [])) (done answer)
      (2 * (ScopeIteration.outputFinEncoding.encode (answer, endpoints, [])).length + 2) := by
  apply RecordLoopMachine.exit_run
  · rw [source_present]
    rfl
  · simp [ScopeTest.outputFinEncoding, List.filterMap_map, Function.comp_def]

theorem ready_eq_initList (input : ScopeIteration.Output) :
    ready input = initList computer (ScopeIteration.outputFinEncoding.encode input) :=
  RecordLoopMachine.ready_eq_initList _

theorem done_eq_haltList (answer : Bool) :
    done answer = haltList computer (finEncodingBoolBool.encode answer) :=
  RecordLoopMachine.done_eq_haltList _

#print axioms source_present
#print axioms iteration_cycle
#print axioms exit_run

end

end PhdThesisLean.AllDifferentCSPMachine.ScopeLoopMachine
