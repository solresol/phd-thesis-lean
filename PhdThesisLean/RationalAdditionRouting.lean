import PhdThesisLean.RationalArithmeticMachine
import PhdThesisLean.SignedIntegerAddition

/-!
# Input copying and denominator projection for fraction addition

Both finite machines consume and clear their complete source, reset finite
control and charge all exhaustion transitions. Copying produces a tagged pair
of complete original words; projection removes the left tagged component.
-/
namespace PhdThesisLean.RationalAddition

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)
open RationalVerifierBounds RationalArithmetic

set_option backward.isDefEq.respectTransparency false

namespace Copy

inductive Stack | input | work (right : Bool) | output deriving DecidableEq, Fintype
inductive Label | scan | reverse (right : Bool) deriving DecidableEq, Fintype

def Alphabet : Stack → Type | .output => Sum Bool Bool | _ => Bool

def program : Label → TM2.Stmt Alphabet Label (Option Bool)
  | .scan => .pop .input (fun _ b => b)
      (.branch Option.isSome
        (.push (.work false) (fun b => b.getD false)
          (.push (.work true) (fun b => b.getD false)
            (.load (fun _ => none) (.goto fun _ => .scan))))
        (.load (fun _ => none) (.goto fun _ => .reverse true)))
  | .reverse d => .pop (.work d) (fun _ b => b)
      (.branch Option.isSome
        (.push .output (fun b => if d then Sum.inr (b.getD false) else Sum.inl (b.getD false))
          (.load (fun _ => none) (.goto fun _ => .reverse d)))
        (.load (fun _ => none) (if d then .goto (fun _ => .reverse false) else .halt)))

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program

def contents (input left right : List Bool) (output : List (Sum Bool Bool)) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .work false => left | .work true => right | .output => output

def cfg (l : Option Label) (input left right : List Bool) (output : List (Sum Bool Bool)) :
    computer.Cfg := ⟨l, none, contents input left right output⟩

private theorem scan_cons (b : Bool) (input left right : List Bool) (output : List (Sum Bool Bool)) :
    computer.step (cfg (some .scan) (b :: input) left right output) =
      some (cfg (some .scan) input (b :: left) (b :: right) output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, Function.update]
  funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem scan_nil (left right : List Bool) (output : List (Sum Bool Bool)) :
    computer.step (cfg (some .scan) [] left right output) =
      some (cfg (some (.reverse true)) [] left right output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet]

theorem scan_run (input left right : List Bool) (output : List (Sum Bool Bool)) :
    (fun q => q.bind computer.step)^[input.length + 1]
      (some (cfg (some .scan) input left right output)) =
    some (cfg (some (.reverse true)) [] (input.reverse ++ left) (input.reverse ++ right) output) := by
  induction input generalizing left right with
  | nil => simpa using scan_nil left right output
  | cons b input ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, scan_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem right_run (right left : List Bool) (output : List (Sum Bool Bool)) :
    (fun q => q.bind computer.step)^[right.length + 1]
      (some (cfg (some (.reverse true)) [] left right output)) =
    some (cfg (some (.reverse false)) [] left [] (right.reverse.map Sum.inr ++ output)) := by
  induction right generalizing output with
  | nil => simp [computer, FinTM2.step, cfg, program, contents, Alphabet]
  | cons b right ih =>
      have hs : computer.step (cfg (some (.reverse true)) [] left (b :: right) output) =
          some (cfg (some (.reverse true)) [] left right (Sum.inr b :: output)) := by
        simp [computer, FinTM2.step, cfg, program, contents, Alphabet, Function.update]
        funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, hs, ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem left_run (left : List Bool) (output : List (Sum Bool Bool)) :
    (fun q => q.bind computer.step)^[left.length + 1]
      (some (cfg (some (.reverse false)) [] left [] output)) =
    some (cfg none [] [] [] (left.reverse.map Sum.inl ++ output)) := by
  induction left generalizing output with
  | nil => simp [computer, FinTM2.step, cfg, program, contents, Alphabet]
  | cons b left ih =>
      have hs : computer.step (cfg (some (.reverse false)) [] (b :: left) [] output) =
          some (cfg (some (.reverse false)) [] left [] (Sum.inl b :: output)) := by
        simp [computer, FinTM2.step, cfg, program, contents, Alphabet, Function.update]
        funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, hs, ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem run (input : List Bool) :
    (fun q => q.bind computer.step)^[3 * input.length + 3]
      (some (cfg (some .scan) input [] [] [])) =
    some (cfg none [] [] [] (input.map Sum.inl ++ input.map Sum.inr)) := by
  rw [show 3 * input.length + 3 =
    ((input.length + 1) + (input.length + 1)) + (input.length + 1) by omega,
    Function.iterate_add_apply, scan_run]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply]
  have hr := right_run input.reverse input.reverse []
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  rw [hr]
  simpa using left_run input.reverse (input.map Sum.inr)

def outputsInTime (input : List Bool) :
    TM2OutputsInTime computer input (some (input.map Sum.inl ++ input.map Sum.inr))
      (3 * input.length + 3) where
  steps := 3 * input.length + 3
  evals_in_steps := by
    have hi : initList computer input = cfg (some .scan) input [] [] [] := by
      unfold initList cfg; congr; funext k
      cases k <;> first | rfl | (rename_i d; cases d <;> rfl)
    have ho : haltList computer (input.map Sum.inl ++ input.map Sum.inr) =
        cfg none [] [] [] (input.map Sum.inl ++ input.map Sum.inr) := by
      unfold haltList cfg; congr; funext k
      cases k <;> first | rfl | (rename_i d; cases d <;> rfl)
    change (fun q => q.bind computer.step)^[_] (some (initList computer input)) = _
    simpa only [hi, Option.map_some, ho] using run input
  steps_le_m := le_rfl

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encoding (LeanNPHardness.PairEncoding.finEncoding encoding encoding)
      (fun x => (x, x)) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 3
  outputsFun x := by
    simpa [LeanNPHardness.PairEncoding.finEncoding, encoding, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using outputsInTime (encode x)

end Copy

namespace Right

inductive Stack | input | work | output deriving DecidableEq, Fintype
inductive Label | scan | reverse deriving DecidableEq, Fintype
structure State where
  symbol : Option (Sum Bool Bool)
  bit : Option Bool
  deriving DecidableEq, Fintype

def initial : State := ⟨none, none⟩
def Alphabet : Stack → Type | .input => Sum Bool Bool | _ => Bool

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input (fun s b => {s with symbol := b})
      (.branch (fun s => s.symbol.isSome)
        (.branch (fun s => Assemble.isRight (s.symbol.getD (.inl false)))
          (.push .work (fun s => Assemble.bit (s.symbol.getD (.inl false)))
            (.load (fun _ => initial) (.goto fun _ => .scan)))
          (.load (fun _ => initial) (.goto fun _ => .scan)))
        (.load (fun _ => initial) (.goto fun _ => .reverse)))
  | .reverse => .pop .work (fun s b => {s with bit := b})
      (.branch (fun s => s.bit.isSome)
        (.push .output (fun s => s.bit.getD false)
          (.load (fun _ => initial) (.goto fun _ => .reverse)))
        (.load (fun _ => initial) .halt))

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype (Sum Bool Bool))
  m := program

def contents (input : List (Sum Bool Bool)) (work output : List Bool) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .work => work | .output => output

def cfg (l : Option Label) (input : List (Sum Bool Bool)) (work output : List Bool) :
    computer.Cfg := ⟨l, initial, contents input work output⟩

theorem scan_run (input : List (Sum Bool Bool)) (work output : List Bool) :
    (fun q => q.bind computer.step)^[input.length + 1]
      (some (cfg (some .scan) input work output)) =
    some (cfg (some .reverse) [] ((LeanNPHardness.PairEncoding.rightSymbols input).reverse ++ work) output) := by
  induction input generalizing work with
  | nil => simp [computer, FinTM2.step, cfg, program, contents, Alphabet, initial,
      LeanNPHardness.PairEncoding.rightSymbols]
  | cons s input ih =>
      cases s with
      | inl b =>
          have hs : computer.step (cfg (some .scan) (.inl b :: input) work output) =
              some (cfg (some .scan) input work output) := by
            simp [computer, FinTM2.step, cfg, program, contents, Alphabet, initial,
              Assemble.isRight, Function.update]
            funext k; cases k <;> rfl
          rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, hs, ih]
          rfl
      | inr b =>
          have hs : computer.step (cfg (some .scan) (.inr b :: input) work output) =
              some (cfg (some .scan) input (b :: work) output) := by
            simp [computer, FinTM2.step, cfg, program, contents, Alphabet, initial,
              Assemble.isRight, Assemble.bit, Function.update]
            funext k; cases k <;> rfl
          rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, hs, ih]
          simp [LeanNPHardness.PairEncoding.rightSymbols, List.reverse_cons, List.append_assoc]

theorem reverse_run (work output : List Bool) :
    (fun q => q.bind computer.step)^[work.length + 1]
      (some (cfg (some .reverse) [] work output)) =
    some (cfg none [] [] (work.reverse ++ output)) := by
  induction work generalizing output with
  | nil => simp [computer, FinTM2.step, cfg, program, contents, Alphabet, initial]
  | cons b work ih =>
      have hs : computer.step (cfg (some .reverse) [] (b :: work) output) =
          some (cfg (some .reverse) [] work (b :: output)) := by
        simp [computer, FinTM2.step, cfg, program, contents, Alphabet, initial, Function.update]
        funext k; cases k <;> rfl
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, hs, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem run (left right : List Bool) :
    (fun q => q.bind computer.step)^[left.length + 2 * right.length + 2]
      (some (cfg (some .scan) (left.map Sum.inl ++ right.map Sum.inr) [] [])) =
    some (cfg none [] [] right) := by
  rw [show left.length + 2 * right.length + 2 =
    (right.length + 1) + ((left.map (Sum.inl (β := Bool)) ++ right.map Sum.inr).length + 1) by simp; omega,
    Function.iterate_add_apply, scan_run]
  simp only [LeanNPHardness.PairEncoding.rightSymbols_append,
    LeanNPHardness.PairEncoding.rightSymbols_map_inl,
    LeanNPHardness.PairEncoding.rightSymbols_map_inr, List.nil_append, List.append_nil]
  simpa using reverse_run right.reverse []

def outputsInTime (left right : List Bool) :
    TM2OutputsInTime computer (left.map Sum.inl ++ right.map Sum.inr) (some right)
      (2 * (left.length + right.length) + 2) where
  steps := left.length + 2 * right.length + 2
  evals_in_steps := by
    have hi : initList computer (left.map Sum.inl ++ right.map Sum.inr) =
        cfg (some .scan) (left.map Sum.inl ++ right.map Sum.inr) [] [] := by
      unfold initList cfg; congr; funext k; cases k <;> rfl
    have ho : haltList computer right = cfg none [] [] right := by
      unfold haltList cfg; congr; funext k; cases k <;> rfl
    change (fun q => q.bind computer.step)^[_] (some (initList computer _)) = _
    simpa only [hi, Option.map_some, ho] using run left right
  steps_le_m := by omega

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime fieldsEncoding SignedIntegerComparison.encoding Prod.snd where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun x := by
    simpa [fieldsEncoding, LeanNPHardness.PairEncoding.finEncoding, SignedIntegerComparison.encoding, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using
      outputsInTime (SignedIntegerComparison.encode x.1) (SignedIntegerComparison.encode x.2)

end Right
end PhdThesisLean.RationalAddition
