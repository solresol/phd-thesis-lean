import PhdThesisLean.SignedMultiplicationRouting
import LeanNPHardness.BooleanListMachine

/-! Canonical signed/framed serialization of a magnitude and sign. -/
namespace PhdThesisLean.SignedIntegerMultiplication

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool TM2ComputableInPolyTime)

set_option backward.isDefEq.respectTransparency false

abbrev ProductFields := ℕ × Bool
abbrev ProductSymbol := Sum Bool Bool

def productEncoding : FinEncoding ProductFields :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingNatBool finEncodingBoolBool

def productWire (a : List Bool) (negative : Bool) : List ProductSymbol :=
  a.map Sum.inl ++ [Sum.inr negative]

@[simp] theorem product_encode (x : ProductFields) :
    productEncoding.encode x = productWire (encodeNat x.1) x.2 := by
  simp [productEncoding, productWire, LeanNPHardness.PairEncoding.finEncoding,
    finEncodingNatBool, finEncodingBoolBool]

/-- An empty magnitude always has positive sign. -/
def assemble (x : ProductFields) : List Bool :=
  (x.2 && decide (x.1 ≠ 0)) :: LeanNPHardness.BinaryNatLists.encodeNat x.1

namespace Assemble

inductive Stack
  | input | magnitude | count | output
  deriving DecidableEq, Fintype
inductive Label
  | scan | restore | prefix
  deriving DecidableEq, Fintype
structure State where
  symbol : Option ProductSymbol
  bit : Option Bool
  negative : Bool
  deriving DecidableEq, Fintype

def state (negative : Bool) : State := ⟨none, none, negative⟩
def observe (s : State) (b : Option Bool) : State := {s with bit := b}
def clear (s : State) : State := state s.negative

def Alphabet : Stack → Type
  | .input => ProductSymbol
  | _ => Bool

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input (fun s b => {s with symbol := b}) <|
      .branch (fun s => s.symbol.isSome)
        (.branch (fun s => match s.symbol with | some (.inl _) => true | _ => false)
          (.push .magnitude (fun s => match s.symbol with | some (.inl b) => b | _ => false) <|
            .push .count (fun _ => true) <| .load clear (.goto fun _ => .scan))
          (.peek .magnitude observe <|
            .load (fun s => state ((match s.symbol with | some (.inr b) => b | _ => false) &&
              s.bit.isSome)) (.goto fun _ => .scan)))
        (.load clear (.goto fun _ => .restore))
  | .restore => .pop .magnitude observe <|
      .branch (fun s => s.bit.isSome)
        (.push .output (fun s => s.bit.getD false) <| .load clear (.goto fun _ => .restore))
        (.push .output (fun _ => false) <| .load clear (.goto fun _ => .prefix))
  | .prefix => .pop .count observe <|
      .branch (fun s => s.bit.isSome)
        (.push .output (fun _ => true) <| .load clear (.goto fun _ => .prefix))
        (.push .output State.negative <| .load (fun _ => state false) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := state false
  Γk₀Fin := inferInstanceAs (Fintype ProductSymbol)
  m := program

def contents (input : List ProductSymbol) (magnitude count output : List Bool) :
    (k : Stack) → List (Alphabet k)
  | .input => input
  | .magnitude => magnitude
  | .count => count
  | .output => output

def cfg (l : Option Label) (z : Bool) (input : List ProductSymbol)
    (magnitude count output : List Bool) : computer.Cfg :=
  ⟨l, state z, contents input magnitude count output⟩

private theorem scan_cons (b z : Bool) (input : List ProductSymbol) (mag count output : List Bool) :
    computer.step (cfg (some .scan) z (Sum.inl b :: input) mag count output) =
    some (cfg (some .scan) z input (b :: mag) (true :: count) output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, clear, state, Function.update]
  funext k; cases k <;> rfl

theorem scan_magnitude (bits : List Bool) (z : Bool) (input : List ProductSymbol)
    (mag count output : List Bool) :
    (fun q => q.bind computer.step)^[bits.length]
      (some (cfg (some .scan) z (bits.map Sum.inl ++ input) mag count output)) =
    some (cfg (some .scan) z input (bits.reverse ++ mag)
      (List.replicate bits.length true ++ count) output) := by
  induction bits generalizing mag count with
  | nil => simp
  | cons b bits ih =>
      simp only [List.length_cons, List.map_cons, List.cons_append]
      rw [Function.iterate_succ_apply, Option.bind_some, scan_cons, ih]
      simp [List.reverse_cons, List.append_assoc, List.replicate_succ,
        LeanNPHardness.MachinePrimitives.replicate_true_append_cons]

private theorem scan_sign (sign z : Bool) (input : List ProductSymbol) (mag count output : List Bool) :
    computer.step (cfg (some .scan) z (Sum.inr sign :: input) mag count output) =
    some (cfg (some .scan) (sign && !mag.isEmpty) input mag count output) := by
  cases mag <;>
    simp [computer, FinTM2.step, cfg, program, contents, Alphabet, clear, state, observe]
  all_goals funext k; cases k <;> rfl

private theorem scan_nil (z : Bool) (mag count output : List Bool) :
    computer.step (cfg (some .scan) z [] mag count output) =
    some (cfg (some .restore) z [] mag count output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, clear, state]

private theorem restore_cons (b z : Bool) (bits count output : List Bool) :
    computer.step (cfg (some .restore) z [] (b :: bits) count output) =
    some (cfg (some .restore) z [] bits count (b :: output)) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, clear, observe, Function.update]
  funext k; cases k <;> rfl

private theorem restore_nil (z : Bool) (count output : List Bool) :
    computer.step (cfg (some .restore) z [] [] count output) =
    some (cfg (some .prefix) z [] [] count (false :: output)) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, clear, observe, Function.update]
  funext k; cases k <;> rfl

theorem restore_run (bits count output : List Bool) (z : Bool) :
    (fun q => q.bind computer.step)^[bits.length + 1]
      (some (cfg (some .restore) z [] bits count output)) =
    some (cfg (some .prefix) z [] [] count (false :: (bits.reverse ++ output))) := by
  induction bits generalizing output with
  | nil => simpa using restore_nil z count output
  | cons b bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, restore_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem prefix_cons (z : Bool) (count output : List Bool) :
    computer.step (cfg (some .prefix) z [] [] (true :: count) output) =
    some (cfg (some .prefix) z [] [] count (true :: output)) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, clear, observe, Function.update]
  funext k; cases k <;> rfl

private theorem prefix_nil (z : Bool) (output : List Bool) :
    computer.step (cfg (some .prefix) z [] [] [] output) =
    some (cfg none false [] [] [] (z :: output)) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, observe, Function.update]
  funext k; cases k <;> rfl

theorem prefix_run (n : ℕ) (output : List Bool) (z : Bool) :
    (fun q => q.bind computer.step)^[n + 1]
      (some (cfg (some .prefix) z [] [] (List.replicate n true) output)) =
    some (cfg none false [] [] [] (z :: (List.replicate n true ++ output))) := by
  induction n generalizing output with
  | zero => simpa using prefix_nil z output
  | succ n ih =>
      rw [List.replicate_succ, Function.iterate_succ_apply, Option.bind_some, prefix_cons, ih]
      simp [LeanNPHardness.MachinePrimitives.replicate_true_append_cons]

/-- Exact serialization cost; the zero sign correction and reset are included. -/
theorem run (a : List Bool) (sign : Bool) :
    (fun q => q.bind computer.step)^[3 * a.length + 4]
      (some (cfg (some .scan) false (productWire a sign) [] [] [])) =
    some (cfg none false [] [] []
      ((sign && !a.isEmpty) :: LeanNPHardness.BinaryNatLists.frame a)) := by
  rw [show 3 * a.length + 4 = ((a.length + 1) + (a.reverse.length + 1) + 1 + 1) + a.length by
      simp; omega, Function.iterate_add_apply]
  rw [productWire, scan_magnitude]
  simp only [List.append_nil]
  rw [Function.iterate_succ_apply, Option.bind_some, scan_sign,
    Function.iterate_succ_apply, Option.bind_some, scan_nil,
    Function.iterate_add_apply, restore_run, prefix_run]
  simp [LeanNPHardness.BinaryNatLists.frame]

private theorem init_eq (bits : List ProductSymbol) :
    initList computer bits = cfg (some .scan) false bits [] [] [] := by
  unfold initList cfg; congr; funext k; cases k <;> rfl
private theorem halt_eq (bits : List Bool) :
    haltList computer bits = cfg none false [] [] [] bits := by
  unfold haltList cfg; congr; funext k; cases k <;> rfl

def outputsInTime (x : ProductFields) :
    TM2OutputsInTime computer (productEncoding.encode x) (some (assemble x))
      (3 * (productEncoding.encode x).length + 1) where
  steps := 3 * (encodeNat x.1).length + 4
  evals_in_steps := by
    change (fun q => q.bind computer.step)^[_] (some (initList computer _)) =
      some (haltList computer _)
    rw [init_eq, halt_eq, product_encode]
    have hz : (encodeNat x.1).isEmpty = decide (x.1 = 0) := by
      apply Bool.eq_iff_iff.mpr
      rw [List.isEmpty_iff_length_eq_zero, decide_eq_true_eq,
        LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size, Nat.size_eq_zero]
    simpa [assemble, LeanNPHardness.BinaryNatLists.encodeNat, hz] using run (encodeNat x.1) x.2
  steps_le_m := by simp [product_encode, productWire]; omega

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime productEncoding
      LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding assemble where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 1
  outputsFun x := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding] using outputsInTime x

end Assemble
end PhdThesisLean.SignedIntegerMultiplication
