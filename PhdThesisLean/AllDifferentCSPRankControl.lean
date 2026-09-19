import PhdThesisLean.AllDifferentCSPRankInitialization

/-!
# Test the remaining rank symbols while retaining the complete state

The machine emits a nonempty-list bit followed by the unchanged target,
source-order symbol fields, and unary tally. A zero symbol still has its field
delimiter and is therefore distinguished from an empty list. This supplies a
checked control pass; `AllDifferentCSPRankLoopMachine` reuses its source-field
criterion in the scan that loads each repeated rank iteration.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace RankControl

abbrev Input := RankAccumulator.Output
abbrev Output := Bool × Input
abbrev inputFinEncoding := RankAccumulator.outputFinEncoding

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingBoolBool inputFinEncoding

def inspect (input : Input) : Output := (!input.1.2.isEmpty, input)

theorem output_length (input : Input) :
    (outputFinEncoding.encode (inspect input)).length = (inputFinEncoding.encode input).length + 1 := by
  simp [outputFinEncoding, inspect, finEncodingBoolBool, encodeBool, Nat.add_comm]

/-- The true branch has exactly the already checked nonempty iteration wire;
no decoding or reconstruction of the head is supplied as an assumption. -/
theorem nonempty_encode (target symbol : ℕ) (symbols : List ℕ) (count : ℕ) :
    inputFinEncoding.encode ((target, symbol :: symbols), count) =
      RankIteration.inputFinEncoding.encode ((target, symbol, symbols), count) := rfl

theorem inspect_nil (target count : ℕ) : inspect ((target, []), count) = (false, ((target, []), count)) := rfl

theorem inspect_cons (target symbol : ℕ) (symbols : List ℕ) (count : ℕ) :
    inspect ((target, symbol :: symbols), count) = (true, ((target, symbol :: symbols), count)) := rfl

end RankControl

namespace RankControlMachine

abbrev Wire := Sum (Sum Bool (Option Bool)) Bool
abbrev Output := Sum Bool Wire

inductive Stack
  | input | saved | output
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input | .saved => Wire | .output => Output

inductive Label
  | scan | emit
  deriving DecidableEq, Fintype

abbrev State := Bool × Option Wire

def initialState : State := (false, none)

def sourceCell : Wire → Bool
  | .inl (.inr _) => true
  | _ => false

private def observe (s : State) (cell : Option Wire) : State := (s.1, cell)

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <|
      .branch (fun s => s.2.isSome)
        (.push .saved (fun s => s.2.getD (.inr false)) <|
          .load (fun s => (s.1 || sourceCell (s.2.getD (.inr false)), s.2)) <|
          .goto fun _ => .scan)
        (.goto fun _ => .emit)
  | .emit => .pop .saved observe <|
      .branch (fun s => s.2.isSome)
        (.push .output (fun s => .inr (s.2.getD (.inr false))) <| .goto fun _ => .emit)
        (.push .output (fun s => .inl s.1) <| .load (fun _ => initialState) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := initialState
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input saved : List Wire) (output : List Output) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .saved => saved | .output => output

private def cfg (label : Option Label) (state : State) (input saved : List Wire)
    (output : List Output) : computer.Cfg := ⟨label, state, stackContents input saved output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "control_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, initialState,
    observe, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input saved : List Wire) (seen : Bool) (cell : Option Wire) :
    Run (cfg (some .scan) (seen, cell) input saved [])
      (cfg (some .emit) (seen || input.any sourceCell, none) [] (input.reverse ++ saved) [])
      (input.length + 1) := by
  induction input generalizing saved seen cell with
  | nil => exact one (by control_step)
  | cons bit input ih =>
      have h : Run (cfg (some .scan) (seen, cell) (bit :: input) saved [])
          (cfg (some .scan) (seen || sourceCell bit, some bit) input (bit :: saved) []) 1 :=
        one (by control_step)
      simpa [List.reverse_cons, List.append_assoc, Bool.or_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
          seq h (ih (bit :: saved) (seen || sourceCell bit) (some bit))

private def emit_run (saved : List Wire) (output : List Output) (seen : Bool) (cell : Option Wire) :
    Run (cfg (some .emit) (seen, cell) [] saved output)
      (cfg none initialState [] [] (.inl seen :: (saved.reverse.map Sum.inr ++ output)))
      (saved.length + 1) := by
  induction saved generalizing output cell with
  | nil => exact one (by control_step)
  | cons bit saved ih =>
      have h : Run (cfg (some .emit) (seen, cell) [] (bit :: saved) output)
          (cfg (some .emit) (seen, some bit) [] saved (.inr bit :: output)) 1 := one (by control_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (.inr bit :: output) (some bit))

private def run (input : List Wire) :
    Run (cfg (some .scan) initialState input [] [])
      (cfg none initialState [] [] (.inl (input.any sourceCell) :: input.map Sum.inr))
      (2 * input.length + 2) := by
  have hs := scan_run input [] false none
  have he := emit_run input.reverse [] (input.any sourceCell) none
  simp only [Bool.false_or, List.append_nil, List.reverse_reverse, List.length_reverse] at hs he
  convert seq hs he using 1
  omega

theorem source_present (input : RankControl.Input) :
    (RankControl.inputFinEncoding.encode input).any sourceCell = !input.1.2.isEmpty := by
  rcases input with ⟨⟨target, symbols⟩, count⟩
  cases symbols <;>
    simp [RankAccumulator.outputFinEncoding,
      DomainSymbolMembership.finEncoding, finEncodingNatBool, encodingNatBool,
      SourceOrderRawFields.finEncoding, SourceOrderRawFields.encode, unaryFinEncodingNat,
      List.any_map, List.map_map, Function.comp_def, sourceCell]

private theorem init_eq (input : List Wire) :
    initList computer input = cfg (some .scan) initialState input [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none initialState [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

end RankControlMachine

/-- Test whether the symbol list is nonempty, preserve the complete state,
and clear the work stacks in at most `2s+2` steps in the full encoded length. -/
def rankControl_outputsInTime (input : RankControl.Input) :
    TM2OutputsInTime RankControlMachine.computer (RankControl.inputFinEncoding.encode input)
      (some (RankControl.outputFinEncoding.encode (RankControl.inspect input)))
      (2 * (RankControl.inputFinEncoding.encode input).length + 2) := by
  rw [TM2OutputsInTime, RankControlMachine.init_eq]
  simp only [Option.map_some]
  rw [RankControlMachine.halt_eq]
  have h := RankControlMachine.run (RankControl.inputFinEncoding.encode input)
  rw [RankControlMachine.source_present] at h
  simpa [RankControl.outputFinEncoding, RankControl.inspect, finEncodingBoolBool, encodeBool] using h

noncomputable def rankControlComputableInPolyTime :
    @TM2ComputableInPolyTime RankControl.Input RankControl.Output
      RankControl.inputFinEncoding RankControl.outputFinEncoding RankControl.inspect where
  tm := RankControlMachine.computer
  inputAlphabet := Equiv.refl RankControlMachine.Wire
  outputAlphabet := Equiv.refl RankControlMachine.Output
  time := 2 * Polynomial.X + 2
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using rankControl_outputsInTime input

/-- Construct the initial one-based state and its first branch bit from the
original target/symbol query, including all intermediate transfers. -/
noncomputable def rankEntryComputableInPolyTime :
    @TM2ComputableInPolyTime DomainSymbolMembership.Input RankControl.Output
      DomainSymbolMembership.finEncoding RankControl.outputFinEncoding
      (RankControl.inspect ∘ RankInitialization.seed) :=
  compositionComputableInPolyTime _ _ _ _ _
    rankInitializationComputableInPolyTime rankControlComputableInPolyTime

#print axioms RankControl.output_length
#print axioms RankControl.nonempty_encode
#print axioms RankControlMachine.source_present
#print axioms rankControl_outputsInTime
#print axioms rankControlComputableInPolyTime
#print axioms rankEntryComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
