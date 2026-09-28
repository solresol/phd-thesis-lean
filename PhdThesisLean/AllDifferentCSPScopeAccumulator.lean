import PhdThesisLean.AllDifferentCSPScopeTest

/-!
# Accumulate the next same-scope result

Combine the previous answer and the tested head's answer with Boolean OR,
retaining both endpoints and every remaining counted scope. The finite machine
consumes both Boolean cells, restores the retained data in order, and emits
one Boolean cell. Its linear bound includes all copying and final cleanup.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace ScopeAccumulator

abbrev Input := Bool × ScopeTest.Output
abbrev Output := ScopeTest.Output

def inputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingBoolBool ScopeTest.outputFinEncoding

abbrev outputFinEncoding := ScopeTest.outputFinEncoding

def update (input : Input) : Output := (input.1 || input.2.1, input.2.2)

theorem input_length (input : Input) :
    (inputFinEncoding.encode input).length =
      (ScopeExtraction.remainingFinEncoding.encode input.2.2).length + 2 := by
  simp [inputFinEncoding, ScopeTest.outputFinEncoding, finEncodingBoolBool,
    encodeBool]

/-- The two Boolean cells become one; the continuation is unchanged. -/
theorem output_length_balance (input : Input) :
    (outputFinEncoding.encode (update input)).length + 1 =
      (inputFinEncoding.encode input).length := by
  simp [ScopeTest.outputFinEncoding, update, input_length, finEncodingBoolBool,
    encodeBool]

end ScopeAccumulator

namespace ScopeAccumulatorMachine

abbrev Remaining := Sum (Sum Bool Bool) (Option Bool)
abbrev Input := Sum Bool (Sum Bool Remaining)
abbrev Output := Sum Bool Remaining
abbrev State := Bool × Option Remaining

inductive Stack
  | input | saved | output
  deriving DecidableEq, Fintype

inductive Label
  | start | copy (answer : Bool) | emit (answer : Bool)
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input | .saved => Remaining | .output => Output

private def tailCell (s : State) : Remaining := s.2.getD (.inr none)

def program : Label → TM2.Stmt Alphabet Label State
  | .start =>
      .pop .input (fun _ cell => ((cell.bind Sum.getLeft?).getD false, none)) <|
        .pop .input (fun s cell =>
          (s.1 || ((cell.bind Sum.getRight?).bind Sum.getLeft?).getD false, none)) <|
            .goto fun s => .copy s.1
  | .copy answer =>
      .pop .input (fun _ cell => (false, (cell.bind Sum.getRight?).bind Sum.getRight?)) <|
        .branch (fun s => s.2.isSome)
          (.push .saved tailCell <| .goto fun _ => .copy answer)
          (.goto fun _ => .emit answer)
  | .emit answer =>
      .pop .saved (fun _ cell => (false, cell)) <|
        .branch (fun s => s.2.isSome)
          (.push .output (fun s => .inr (tailCell s)) <| .goto fun _ => .emit answer)
          (.push .output (fun _ => .inl answer) <| .load (fun _ => (false, none)) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .start
  σ := State
  initialState := (false, none)
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input : List Input) (saved : List Remaining) (output : List Output) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .saved => saved | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (saved : List Remaining) (output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input saved output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "scope_accumulator_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, tailCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def copy_run (answer : Bool) (tail saved : List Remaining) (state : State) :
    Run (cfg (some (.copy answer)) state (tail.map (fun cell => .inr (.inr cell))) saved [])
      (cfg (some (.emit answer)) (false, none) [] (tail.reverse ++ saved) [])
      (tail.length + 1) := by
  induction tail generalizing saved state with
  | nil => exact one (by scope_accumulator_step)
  | cons cell tail ih =>
      have h : Run
          (cfg (some (.copy answer)) state
            ((cell :: tail).map (fun cell => .inr (.inr cell))) saved [])
          (cfg (some (.copy answer)) (false, some cell)
            (tail.map (fun cell => .inr (.inr cell))) (cell :: saved) []) 1 :=
        one (by scope_accumulator_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih _ _)

private def emit_run (answer : Bool) (saved : List Remaining) (output : List Output)
    (state : State) :
    Run (cfg (some (.emit answer)) state [] saved output)
      (cfg none (false, none) [] [] (.inl answer :: (saved.reverse.map Sum.inr ++ output)))
      (saved.length + 1) := by
  induction saved generalizing output state with
  | nil => exact one (by scope_accumulator_step)
  | cons cell saved ih =>
      have h : Run (cfg (some (.emit answer)) state [] (cell :: saved) output)
          (cfg (some (.emit answer)) (false, some cell) [] saved (.inr cell :: output)) 1 :=
        one (by scope_accumulator_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih _ _)

private def run (old seen : Bool) (tail : List Remaining) :
    Run (cfg (some .start) (false, none)
        (.inl old :: .inr (.inl seen) :: tail.map (fun cell => .inr (.inr cell))) [] [])
      (cfg none (false, none) [] [] (.inl (old || seen) :: tail.map Sum.inr))
      (2 * tail.length + 3) := by
  have start : Run (cfg (some .start) (false, none)
      (.inl old :: .inr (.inl seen) :: tail.map (fun cell => .inr (.inr cell))) [] [])
      (cfg (some (.copy (old || seen))) (old || seen, none)
        (tail.map (fun cell => .inr (.inr cell))) [] []) 1 := one (by scope_accumulator_step)
  have copy := copy_run (old || seen) tail [] (old || seen, none)
  have emit := emit_run (old || seen) tail.reverse [] (false, none)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at copy emit
  convert seq (seq start copy) emit using 1
  omega

private theorem init_eq (input : List Input) :
    initList computer input = cfg (some .start) (false, none) input [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none (false, none) [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

end ScopeAccumulatorMachine

def scopeAccumulator_outputsInTime (input : ScopeAccumulator.Input) :
    TM2OutputsInTime ScopeAccumulatorMachine.computer
      (ScopeAccumulator.inputFinEncoding.encode input)
      (some (ScopeAccumulator.outputFinEncoding.encode (ScopeAccumulator.update input)))
      (2 * (ScopeAccumulator.inputFinEncoding.encode input).length + 3) := by
  have run := ScopeAccumulatorMachine.run input.1 input.2.1
    (ScopeExtraction.remainingFinEncoding.encode input.2.2)
  rw [TM2OutputsInTime, ScopeAccumulatorMachine.init_eq]
  simp only [Option.map_some]
  rw [ScopeAccumulatorMachine.halt_eq]
  apply evalsToInTimeMono (by
    simpa [ScopeAccumulator.inputFinEncoding, ScopeTest.outputFinEncoding,
      ScopeAccumulator.update, LeanNPHardness.PairEncoding.finEncoding,
      finEncodingBoolBool, encodeBool, List.map_map, Function.comp_def] using run)
  rw [ScopeAccumulator.input_length]
  omega

noncomputable def scopeAccumulatorComputableInPolyTime :
    @TM2ComputableInPolyTime ScopeAccumulator.Input ScopeAccumulator.Output
      ScopeAccumulator.inputFinEncoding ScopeAccumulator.outputFinEncoding ScopeAccumulator.update where
  tm := ScopeAccumulatorMachine.computer
  inputAlphabet := Equiv.refl ScopeAccumulatorMachine.Input
  outputAlphabet := Equiv.refl ScopeAccumulatorMachine.Output
  time := 2 * Polynomial.X + 3
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_X] using scopeAccumulator_outputsInTime input

#print axioms ScopeAccumulator.output_length_balance
#print axioms scopeAccumulator_outputsInTime
#print axioms scopeAccumulatorComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
