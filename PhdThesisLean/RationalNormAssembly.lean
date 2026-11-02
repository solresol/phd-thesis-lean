import PhdThesisLean.RationalNormRouting
import LeanNPHardness.BooleanListMachine

/-! Finite binary assembly of the two norm powers, including zero and cleanup. -/
namespace PhdThesisLean.RationalNorm

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool TM2ComputableInPolyTime)
open RationalVerifierBounds

set_option backward.isDefEq.respectTransparency false

/-- Output fields are reversed: denominator valuation supplies the numerator.
The flag handles the norm of zero independently of the valuation convention. -/
def assemble (x : Fields) : List Bool :=
  if x.2 then Fraction.zero.encode else
    false :: (LeanNPHardness.BinaryNatLists.encodeNat x.1.2 ++
      LeanNPHardness.BinaryNatLists.encodeNat x.1.1)

namespace Assemble

inductive Stack
  | input | den | denCount | num | numCount | output
  deriving DecidableEq, Fintype
inductive Label
  | scan | denRestore | denPrefix | numRestore | numPrefix | drain
  deriving DecidableEq, Fintype
structure State where
  symbol : Option Symbol
  bit : Option Bool
  zero : Bool
  deriving DecidableEq, Fintype

def state (z : Bool) : State := ⟨none, none, z⟩
def observe (s : State) (b : Option Bool) : State := {s with bit := b}
def clear (s : State) : State := state s.zero
def Alphabet : Stack → Type
  | .input => Symbol
  | _ => Bool

def program : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop .input (fun s b => {s with symbol := b}) <|
        .branch (fun s => s.symbol.isSome)
          (.branch (fun s => match s.symbol with | some (.inl (.inl _)) => true | _ => false)
            (.push .den (fun s => match s.symbol with | some (.inl (.inl b)) => b | _ => false) <|
              .push .denCount (fun _ => true) <| .load clear (.goto fun _ => .scan))
            (.branch (fun s => match s.symbol with | some (.inl (.inr _)) => true | _ => false)
              (.push .num (fun s => match s.symbol with | some (.inl (.inr b)) => b | _ => false) <|
                .push .numCount (fun _ => true) <| .load clear (.goto fun _ => .scan))
              (.load (fun s => state (match s.symbol with | some (.inr b) => b | _ => false))
                (.goto fun _ => .scan))))
          (.load clear (.goto fun _ => .denRestore))
  | .denRestore =>
      .pop .den observe <|
        .branch (fun s => s.bit.isSome)
          (.push .output (fun s => s.bit.getD false) <| .load clear (.goto fun _ => .denRestore))
          (.push .output (fun _ => false) <| .load clear (.goto fun _ => .denPrefix))
  | .denPrefix =>
      .pop .denCount observe <|
        .branch (fun s => s.bit.isSome)
          (.push .output (fun _ => true) <| .load clear (.goto fun _ => .denPrefix))
          (.load clear (.goto fun _ => .numRestore))
  | .numRestore =>
      .pop .num observe <|
        .branch (fun s => s.bit.isSome)
          (.push .output (fun s => s.bit.getD false) <| .load clear (.goto fun _ => .numRestore))
          (.push .output (fun _ => false) <| .load clear (.goto fun _ => .numPrefix))
  | .numPrefix =>
      .pop .numCount observe <|
        .branch (fun s => s.bit.isSome)
          (.push .output (fun _ => true) <| .load clear (.goto fun _ => .numPrefix))
          (.push .output (fun _ => false) <|
            .branch (fun s => s.zero)
              (.load clear (.goto fun _ => .drain))
              (.load (fun _ => state false) .halt))
  | .drain =>
      .pop .output observe <|
        .branch (fun s => s.bit.isSome)
          (.load clear (.goto fun _ => .drain))
          (.push .output (fun _ => true) <| .push .output (fun _ => false) <|
            .push .output (fun _ => true) <| .push .output (fun _ => false) <|
              .push .output (fun _ => false) <| .load (fun _ => state false) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := state false
  Γk₀Fin := inferInstanceAs (Fintype Symbol)
  m := program

def contents (input : List Symbol) (den dc num nc output : List Bool) :
    (k : Stack) → List (Alphabet k)
  | .input => input
  | .den => den
  | .denCount => dc
  | .num => num
  | .numCount => nc
  | .output => output

def cfg (l : Option Label) (s : State) (input : List Symbol) (den dc num nc output : List Bool) :
    computer.Cfg := ⟨l, s, contents input den dc num nc output⟩

private theorem scan_den_step (b z : Bool) (input : List Symbol) (den dc num nc output : List Bool) :
    computer.step (cfg (some .scan) (state z) (Sum.inl (Sum.inl b) :: input) den dc num nc output) =
    some (cfg (some .scan) (state z) input (b :: den) (true :: dc) num nc output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, clear, state, Function.update]
  funext k; cases k <;> rfl

theorem scan_den_run (bits : List Bool) (z : Bool) (input : List Symbol)
    (den dc num nc output : List Bool) :
    (fun q => q.bind computer.step)^[bits.length]
      (some (cfg (some .scan) (state z)
        (bits.map (fun b => Sum.inl (Sum.inl b)) ++ input) den dc num nc output)) =
    some (cfg (some .scan) (state z) input (bits.reverse ++ den) (List.replicate bits.length true ++ dc) num nc output) := by
  induction bits generalizing den dc num nc with
  | nil => simp
  | cons b bits ih =>
      simp only [List.length_cons, List.map_cons, List.cons_append]
      rw [Function.iterate_succ_apply, Option.bind_some, scan_den_step, ih]
      simp [List.reverse_cons, List.append_assoc, List.replicate_succ,
        LeanNPHardness.MachinePrimitives.replicate_true_append_cons]

private theorem scan_num_step (b z : Bool) (input : List Symbol) (den dc num nc output : List Bool) :
    computer.step (cfg (some .scan) (state z) (Sum.inl (Sum.inr b) :: input) den dc num nc output) =
    some (cfg (some .scan) (state z) input den dc (b :: num) (true :: nc) output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, clear, state, Function.update]
  funext k; cases k <;> rfl

theorem scan_num_run (bits : List Bool) (z : Bool) (input : List Symbol)
    (den dc num nc output : List Bool) :
    (fun q => q.bind computer.step)^[bits.length]
      (some (cfg (some .scan) (state z)
        (bits.map (fun b => Sum.inl (Sum.inr b)) ++ input) den dc num nc output)) =
    some (cfg (some .scan) (state z) input den dc (bits.reverse ++ num) (List.replicate bits.length true ++ nc) output) := by
  induction bits generalizing den dc num nc with
  | nil => simp
  | cons b bits ih =>
      simp only [List.length_cons, List.map_cons, List.cons_append]
      rw [Function.iterate_succ_apply, Option.bind_some, scan_num_step, ih]
      simp [List.reverse_cons, List.append_assoc, List.replicate_succ,
        LeanNPHardness.MachinePrimitives.replicate_true_append_cons]

private theorem scan_flag_step (z old : Bool) (den dc num nc : List Bool) :
    computer.step (cfg (some .scan) (state old) [Sum.inr z] den dc num nc []) =
    some (cfg (some .scan) (state z) [] den dc num nc []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, Function.update]
  funext k; cases k <;> rfl

private theorem scan_nil_step (z : Bool) (den dc num nc : List Bool) :
    computer.step (cfg (some .scan) (state z) [] den dc num nc []) =
    some (cfg (some .denRestore) (state z) [] den dc num nc []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, clear]

/-- Both binary powers are stored in reverse and their output frames counted. -/
theorem scan_run (a b : List Bool) (z : Bool) :
    (fun q => q.bind computer.step)^[a.length + b.length + 2]
      (some (cfg (some .scan) (state false) (wire a b z) [] [] [] [] [])) =
    some (cfg (some .denRestore) (state z) [] a.reverse (List.replicate a.length true)
      b.reverse (List.replicate b.length true) []) := by
  rw [show a.length + b.length + 2 = 2 + b.length + a.length by omega,
    Function.iterate_add_apply]
  simp only [wire, List.append_assoc]
  rw [scan_den_run]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply, scan_num_run]
  simp only [List.append_nil]
  rw [show 2 = 1 + 1 from rfl, Function.iterate_succ_apply, Option.bind_some, scan_flag_step]
  exact scan_nil_step z _ _ _ _

private theorem den_restore_cons (b z : Bool) (bits output : List Bool) (dc num nc : List Bool) :
    computer.step (cfg (some .denRestore) (state z) [] (b :: bits) dc num nc output) =
    some (cfg (some .denRestore) (state z) [] bits dc num nc (b :: output)) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, clear, observe, Function.update]
  funext k; cases k <;> rfl

private theorem den_restore_nil (z : Bool) (output : List Bool) (dc num nc : List Bool) :
    computer.step (cfg (some .denRestore) (state z) [] [] dc num nc output) =
    some (cfg (some .denPrefix) (state z) [] [] dc num nc (false :: output)) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, clear, observe, Function.update]
  funext k; cases k <;> rfl

/-- Restore one field and add its binary-frame delimiter. -/
theorem den_restore_run (bits output : List Bool) (z : Bool) (dc num nc : List Bool) :
    (fun q => q.bind computer.step)^[bits.length + 1]
      (some (cfg (some .denRestore) (state z) [] bits dc num nc output)) =
    some (cfg (some .denPrefix) (state z) [] [] dc num nc (false :: (bits.reverse ++ output))) := by
  induction bits generalizing output with
  | nil => simpa using den_restore_nil z output dc num nc
  | cons b bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, den_restore_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem den_prefix_cons (z : Bool) (count output : List Bool) (num nc : List Bool) :
    computer.step (cfg (some .denPrefix) (state z) [] [] (true :: count) num nc output) =
    some (cfg (some .denPrefix) (state z) [] [] count num nc (true :: output)) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, clear, observe, Function.update]
  funext k; cases k <;> rfl

private theorem den_prefix_nil (z : Bool) (output : List Bool) (num nc : List Bool) :
    computer.step (cfg (some .denPrefix) (state z) [] [] [] num nc output) =
    some (cfg (some .numRestore) (state z) [] [] [] num nc output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, clear, observe]

theorem den_prefix_run (n : ℕ) (output : List Bool) (z : Bool) (num nc : List Bool) :
    (fun q => q.bind computer.step)^[n + 1]
      (some (cfg (some .denPrefix) (state z) [] [] (List.replicate n true) num nc output)) =
    some (cfg (some .numRestore) (state z) [] [] [] num nc (List.replicate n true ++ output)) := by
  induction n generalizing output with
  | zero => simpa using den_prefix_nil z output num nc
  | succ n ih =>
      rw [List.replicate_succ, Function.iterate_succ_apply, Option.bind_some, den_prefix_cons, ih]
      simp [LeanNPHardness.MachinePrimitives.replicate_true_append_cons]

private theorem num_restore_cons (b z : Bool) (bits output : List Bool) (nc : List Bool) :
    computer.step (cfg (some .numRestore) (state z) [] [] [] (b :: bits) nc output) =
    some (cfg (some .numRestore) (state z) [] [] [] bits nc (b :: output)) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, clear, observe, Function.update]
  funext k; cases k <;> rfl

private theorem num_restore_nil (z : Bool) (output : List Bool) (nc : List Bool) :
    computer.step (cfg (some .numRestore) (state z) [] [] [] [] nc output) =
    some (cfg (some .numPrefix) (state z) [] [] [] [] nc (false :: output)) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, clear, observe, Function.update]
  funext k; cases k <;> rfl

/-- Restore one field and add its binary-frame delimiter. -/
theorem num_restore_run (bits output : List Bool) (z : Bool) (nc : List Bool) :
    (fun q => q.bind computer.step)^[bits.length + 1]
      (some (cfg (some .numRestore) (state z) [] [] [] bits nc output)) =
    some (cfg (some .numPrefix) (state z) [] [] [] [] nc (false :: (bits.reverse ++ output))) := by
  induction bits generalizing output with
  | nil => simpa using num_restore_nil z output nc
  | cons b bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, num_restore_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem num_prefix_cons (z : Bool) (count output : List Bool)  :
    computer.step (cfg (some .numPrefix) (state z) [] [] [] [] (true :: count) output) =
    some (cfg (some .numPrefix) (state z) [] [] [] [] count (true :: output)) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, clear, observe, Function.update]
  funext k; cases k <;> rfl

private theorem num_prefix_nil (z : Bool) (output : List Bool)  :
    computer.step (cfg (some .numPrefix) (state z) [] [] [] [] [] output) =
    some (cfg (if z then some .drain else none) (state z) [] [] [] [] [] (false :: output)) := by
  cases z <;> simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, clear, observe, Function.update]
  all_goals funext k; cases k <;> rfl

theorem num_prefix_run (n : ℕ) (output : List Bool) (z : Bool)  :
    (fun q => q.bind computer.step)^[n + 1]
      (some (cfg (some .numPrefix) (state z) [] [] [] [] (List.replicate n true) output)) =
    some (cfg (if z then some .drain else none) (state z) [] [] [] [] [] (false :: (List.replicate n true ++ output))) := by
  induction n generalizing output with
  | zero => simpa using num_prefix_nil z output
  | succ n ih =>
      rw [List.replicate_succ, Function.iterate_succ_apply, Option.bind_some, num_prefix_cons, ih]
      simp [LeanNPHardness.MachinePrimitives.replicate_true_append_cons]

/-- The binary fields are swapped into positive signed fraction storage. -/
theorem frame_run (a b : List Bool) (z : Bool) :
    (fun q => q.bind computer.step)^[2 * (a.length + b.length) + 4]
      (some (cfg (some .denRestore) (state z) [] a.reverse (List.replicate a.length true)
        b.reverse (List.replicate b.length true) [])) =
    some (cfg (if z then some .drain else none) (state z) [] [] [] [] []
      (false :: (LeanNPHardness.BinaryNatLists.frame b ++ LeanNPHardness.BinaryNatLists.frame a))) := by
  rw [show 2 * (a.length + b.length) + 4 =
      (b.length + 1) + (b.reverse.length + 1) + (a.length + 1) + (a.reverse.length + 1) by simp; omega,
    Function.iterate_add_apply, den_restore_run]
  simp only [List.reverse_reverse, List.append_nil]
  rw [Function.iterate_add_apply, den_prefix_run,
    Function.iterate_add_apply, num_restore_run, num_prefix_run]
  simp [LeanNPHardness.BinaryNatLists.frame, List.append_assoc]

private theorem drain_cons (b : Bool) (output : List Bool) :
    computer.step (cfg (some .drain) (state true) [] [] [] [] [] (b :: output)) =
    some (cfg (some .drain) (state true) [] [] [] [] [] output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, clear, observe, Function.update]
  funext k; cases k <;> rfl

private theorem drain_nil :
    computer.step (cfg (some .drain) (state true) [] [] [] [] [] []) =
    some (cfg none (state false) [] [] [] [] [] Fraction.zero.encode) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, clear, observe, Function.update]
  funext k; cases k <;> rfl

/-- Even zero fractions clear every computed power and scratch count. -/
theorem drain_run (output : List Bool) :
    (fun q => q.bind computer.step)^[output.length + 1]
      (some (cfg (some .drain) (state true) [] [] [] [] [] output)) =
    some (cfg none (state false) [] [] [] [] [] Fraction.zero.encode) := by
  induction output with
  | nil => exact drain_nil
  | cons b output ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, drain_cons, ih]

private theorem init_eq (bits : List Symbol) :
    initList computer bits = cfg (some .scan) (state false) bits [] [] [] [] [] := by
  unfold initList cfg; congr; funext k; cases k <;> rfl
private theorem halt_eq (bits : List Bool) :
    haltList computer bits = cfg none (state false) [] [] [] [] [] bits := by
  unfold haltList cfg; congr; funext k; cases k <;> rfl

/-- A linear-time finite binary serializer, including the zero branch. -/
def outputsInTime (x : Fields) :
    TM2OutputsInTime computer (fieldsEncoding.encode x) (some (assemble x))
      (5 * (fieldsEncoding.encode x).length + 5) := by
  let a := encodeNat x.1.1
  let b := encodeNat x.1.2
  have base : (fun q => q.bind computer.step)^[3 * (a.length + b.length) + 6]
      (some (initList computer (fieldsEncoding.encode x))) =
      some (cfg (if x.2 then some .drain else none) (state x.2) [] [] [] [] []
        (false :: (LeanNPHardness.BinaryNatLists.frame b ++ LeanNPHardness.BinaryNatLists.frame a))) := by
    rw [init_eq, fields_encode, show 3 * (a.length + b.length) + 6 =
      (2 * (a.length + b.length) + 4) + (a.length + b.length + 2) by omega,
      Function.iterate_add_apply, scan_run, frame_run]
  cases hz : x.2 with
  | false =>
      refine { steps := 3 * (a.length + b.length) + 6, evals_in_steps := ?_, steps_le_m := ?_ }
      · change (fun q => q.bind computer.step)^[_] (some (initList computer _)) = some (haltList computer _)
        simpa [halt_eq, assemble, hz, LeanNPHardness.BinaryNatLists.encodeNat, a, b] using base
      · simp [fields_encode, wire, a, b]; omega
  | true =>
      refine { steps := (2 * (a.length + b.length) + 4) + (3 * (a.length + b.length) + 6), evals_in_steps := ?_, steps_le_m := ?_ }
      · change (fun q => q.bind computer.step)^[_] (some (initList computer _)) = some (haltList computer _)
        rw [Function.iterate_add_apply, base]
        simp only [hz, ↓reduceIte]
        have h := drain_run (false :: (LeanNPHardness.BinaryNatLists.frame b ++ LeanNPHardness.BinaryNatLists.frame a))
        simpa [halt_eq, assemble, hz, LeanNPHardness.BinaryNatLists.frame, Nat.mul_add, Nat.two_mul,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simp [fields_encode, wire, a, b]; omega

/-- This output is a binary list, to be identified with the existing Fraction
encoding after the two valuation-power calls. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime fieldsEncoding LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding assemble where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 5 * Polynomial.X + 5
  outputsFun x := by
    simpa [LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using outputsInTime x

end Assemble
end PhdThesisLean.RationalNorm
