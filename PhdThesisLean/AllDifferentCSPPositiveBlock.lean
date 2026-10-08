import PhdThesisLean.AllDifferentCSPMachine

/-!
# Checked emission of one positive pinning row

The finite machine preserves the binary index, rank and weight fields and
prefixes the exact length and positive-row tag. The input decoder checks
three fields; the output decoder checks `[4,0,index,rank,weight]`. This local
emitter neither selects distinct pairs nor supplies their shared weight.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding

namespace PositiveBlock

abbrev Value := (ℕ × ℕ) × ℕ

def inputEncode (value : Value) : List (Option Bool) :=
  SourceOrderRawFields.encode [value.1.1, value.1.2, value.2]

def inputDecode (wire : List (Option Bool)) : Option Value := do
  match ← SourceOrderRawFields.decode wire with
  | [index, target, weight] => some ((index, target), weight)
  | _ => none

@[simp]
theorem inputDecode_encode (value : Value) : inputDecode (inputEncode value) = some value := by
  simp [inputDecode, inputEncode]

def inputFinEncoding : FinEncoding Value where
  Γ := Option Bool
  encode := inputEncode
  decode := inputDecode
  decode_encode := inputDecode_encode
  ΓFin := inferInstance

def outputEncode (value : Value) : List (Option Bool) :=
  SourceOrderRawFields.encode [4, 0, value.1.1, value.1.2, value.2]

def outputDecode (wire : List (Option Bool)) : Option Value := do
  match ← SourceOrderRawFields.decode wire with
  | [4, 0, index, target, weight] => some ((index, target), weight)
  | _ => none

@[simp]
theorem outputDecode_encode (value : Value) : outputDecode (outputEncode value) = some value := by
  simp [outputDecode, outputEncode]

def outputFinEncoding : FinEncoding Value where
  Γ := Option Bool
  encode := outputEncode
  decode := outputDecode
  decode_encode := outputDecode_encode
  ΓFin := inferInstance

def headerPrefix : List (Option Bool) := [none, some false, some false, some true, none]

private theorem encodeNat_four : encodeNat 4 = [false, false, true] := by
  unfold encodeNat
  change encodeNum (Num.ofNat' 4) = [false, false, true]
  rw [show (4 : ℕ) = Nat.bit false (Nat.bit false 1) by norm_num [Nat.bit],
    Num.ofNat'_bit, Num.ofNat'_bit, Num.ofNat'_one]
  rfl

private theorem encodeNat_zero : encodeNat 0 = [] := by
  unfold encodeNat
  change encodeNum (Num.ofNat' 0) = []
  rw [Num.ofNat'_zero]
  rfl

theorem outputEncode_eq_prefix (value : Value) :
    outputEncode value = headerPrefix ++ inputEncode value := by
  simp [inputEncode, outputEncode, headerPrefix, SourceOrderRawFields.encode,
    encodeNat_four, encodeNat_zero]

theorem outputEncode_length (value : Value) :
    (outputEncode value).length = (inputEncode value).length + 5 := by
  rw [outputEncode_eq_prefix, List.length_append]
  simp [headerPrefix, Nat.add_comm]

/-- Exact complete counted row in the objective's existing raw row encoding. -/
theorem outputEncode_eq_row (value : Value) :
    outputEncode value = DomainFieldSection.rowPayloadEncode
      [(RuntimeResidualRow.pin value.1.1 value.1.2 value.2).toNatList] := by
  simp [outputEncode, DomainFieldSection.rowPayloadEncode,
    DomainFieldSection.rowFields, RuntimeResidualRow.toNatList]

example : outputDecode (SourceOrderRawFields.encode [3, 0, 1, 2, 4]) = none := by
  simp [outputDecode]
example : outputDecode (SourceOrderRawFields.encode [4, 1, 1, 2, 4]) = none := by
  simp [outputDecode]
example : inputDecode (SourceOrderRawFields.encode [1, 2]) = none := by
  simp [inputDecode]

end PositiveBlock

namespace PositiveBlockMachine

inductive Stack
  | input | saved | output
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : Stack) := Option Bool

inductive Label
  | copy | emit
  deriving DecidableEq, Fintype

abbrev State := Option (Option Bool)

def program : Label → TM2.Stmt Alphabet Label State
  | .copy => .pop .input (fun _ cell => cell) <|
      .branch Option.isSome
        (.push .saved (fun cell => cell.getD none) <| .goto fun _ => .copy)
        (.goto fun _ => .emit)
  | .emit => .pop .saved (fun _ cell => cell) <|
      .branch Option.isSome
        (.push .output (fun cell => cell.getD none) <| .goto fun _ => .emit)
        (.push .output (fun _ => none) <|
          .push .output (fun _ => some true) <|
          .push .output (fun _ => some false) <|
          .push .output (fun _ => some false) <|
          .push .output (fun _ => none) <| .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .copy
  σ := State
  initialState := none
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input saved output : List (Option Bool)) : (k : Stack) → List (Alphabet k)
  | .input => input | .saved => saved | .output => output

private def cfg (label : Option Label) (state : State)
    (input saved output : List (Option Bool)) : computer.Cfg :=
  ⟨label, state, stackContents input saved output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "positive_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, Function.update,
    PositiveBlock.headerPrefix]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def copy_run (input saved : List (Option Bool)) (state : State) :
    Run (cfg (some .copy) state input saved [])
      (cfg (some .emit) none [] (input.reverse ++ saved) []) (input.length + 1) := by
  induction input generalizing saved state with
  | nil => exact one (by positive_step)
  | cons cell input ih =>
    have h : Run (cfg (some .copy) state (cell :: input) saved [])
        (cfg (some .copy) (some cell) input (cell :: saved) []) 1 := one (by positive_step)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using seq h (ih (cell :: saved) (some cell))

private def emit_run (saved output : List (Option Bool)) (state : State) :
    Run (cfg (some .emit) state [] saved output)
      (cfg none none [] [] (PositiveBlock.headerPrefix ++ saved.reverse ++ output))
      (saved.length + 1) := by
  induction saved generalizing output state with
  | nil => exact one (by positive_step)
  | cons cell saved ih =>
    have h : Run (cfg (some .emit) state [] (cell :: saved) output)
        (cfg (some .emit) (some cell) [] saved (cell :: output)) 1 := one (by positive_step)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using seq h (ih (cell :: output) (some cell))

private def run (input : List (Option Bool)) :
    Run (cfg (some .copy) none input [] [])
      (cfg none none [] [] (PositiveBlock.headerPrefix ++ input)) (2 * input.length + 2) := by
  have hc := copy_run input [] none
  have he := emit_run input.reverse [] none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hc he
  convert seq hc he using 1
  omega

private theorem init_eq (input : List (Option Bool)) :
    initList computer input = cfg (some .copy) none input [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List (Option Bool)) :
    haltList computer output = cfg none none [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

end PositiveBlockMachine

/-- All binary field copies, tag cells, and cleanup are included in `2s+2`. -/
def positiveBlock_outputsInTime (value : PositiveBlock.Value) :
    TM2OutputsInTime PositiveBlockMachine.computer (PositiveBlock.inputEncode value)
      (some (PositiveBlock.outputEncode value)) (2 * (PositiveBlock.inputEncode value).length + 2) := by
  rw [TM2OutputsInTime, PositiveBlockMachine.init_eq]
  simp only [Option.map_some, PositiveBlockMachine.halt_eq, PositiveBlock.outputEncode_eq_prefix]
  exact PositiveBlockMachine.run _

noncomputable def positiveBlockComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveBlock.Value PositiveBlock.Value
      PositiveBlock.inputFinEncoding PositiveBlock.outputFinEncoding id where
  tm := PositiveBlockMachine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun value := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using positiveBlock_outputsInTime value

#print axioms PositiveBlock.outputDecode_encode
#print axioms PositiveBlock.outputEncode_length
#print axioms PositiveBlock.outputEncode_eq_row
#print axioms positiveBlock_outputsInTime
#print axioms positiveBlockComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
