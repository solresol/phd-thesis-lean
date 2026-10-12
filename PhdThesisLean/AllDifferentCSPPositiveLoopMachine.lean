import PhdThesisLean.AllDifferentCSPScopeLoopMachine
import PhdThesisLean.AllDifferentCSPPositiveIteration
import PhdThesisLean.AllDifferentCSPRecordLoopMachine

/-!
# Finite control for repeated ordered-pair occurrence tests

Instantiate the shared counted-record controller with the complete checked
positive iteration. Its exact scan/call/return costs and cleanup are retained.
-/

namespace PhdThesisLean.AllDifferentCSPMachine.PositiveLoopMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

noncomputable section

def body := positiveIterationComputableInPolyTime
abbrev Wire := RecordLoopMachine.Wire
abbrev sourceCell := RecordLoopMachine.sourceCell

/-- Even a zero/zero occurrence has a counted record delimiter. -/
theorem source_present (input : PositiveIteration.Output) :
    (PositiveIteration.outputFinEncoding.encode input).any sourceCell = !input.2.2.isEmpty := by
  rw [PositiveAccumulator.output_encode]
  simpa [PositiveAccumulator.asScopeOutput] using
    ScopeLoopMachine.source_present (PositiveAccumulator.asScopeOutput input)

def loopBody : RecordLoopMachine.Body :=
  ⟨body.tm, body.inputAlphabet, body.outputAlphabet⟩

abbrev computer := RecordLoopMachine.computer (body := loopBody)

def ready (input : PositiveIteration.Output) : computer.Cfg :=
  RecordLoopMachine.ready (body := loopBody) (PositiveIteration.outputFinEncoding.encode input)

abbrev done := RecordLoopMachine.done (body := loopBody)
abbrev Run := RecordLoopMachine.Run (body := loopBody)

def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := RecordLoopMachine.seq h h'

/-- A whole cycle includes detection, loading, the checked body and restoration. -/
def iteration_cycle (answer : Bool) (query : ℕ × ℕ) (head : ℕ × ℕ) (tail : List (ℕ × ℕ)) :
    Run (ready (answer, query, head :: tail))
      (ready (PositiveIteration.step (answer, query, head, tail)))
      (body.time.eval (PositiveIteration.inputFinEncoding.encode (answer, query, head, tail)).length +
        2 * (PositiveIteration.inputFinEncoding.encode (answer, query, head, tail)).length +
        2 * (PositiveIteration.outputFinEncoding.encode (PositiveIteration.step (answer, query, head, tail))).length + 4) := by
  apply RecordLoopMachine.iteration_cycle (body := loopBody)
  · rw [source_present]
    rfl
  · exact body.outputsFun (answer, query, head, tail)

/-- Exhaustion returns exactly the accumulated Boolean and clears every other stack. -/
def exit_run (answer : Bool) (query : ℕ × ℕ) :
    Run (ready (answer, query, [])) (done answer)
      (2 * (PositiveIteration.outputFinEncoding.encode (answer, query, [])).length + 2) := by
  apply RecordLoopMachine.exit_run
  · rw [source_present]
    rfl
  · simp [PositiveTest.outputFinEncoding, List.filterMap_map, Function.comp_def]

theorem ready_eq_initList (input : PositiveIteration.Output) :
    ready input = initList computer (PositiveIteration.outputFinEncoding.encode input) :=
  RecordLoopMachine.ready_eq_initList _

theorem done_eq_haltList (answer : Bool) :
    done answer = haltList computer (finEncodingBoolBool.encode answer) :=
  RecordLoopMachine.done_eq_haltList _

#print axioms source_present
#print axioms iteration_cycle
#print axioms exit_run

end

end PhdThesisLean.AllDifferentCSPMachine.PositiveLoopMachine
