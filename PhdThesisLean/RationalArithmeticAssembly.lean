import PhdThesisLean.RationalArithmeticRouting

/-! Remove pair tags, optionally removing the positive denominator sign.
The finite machine preserves all other bits and empties its temporary stack. -/
namespace PhdThesisLean.RationalArithmetic

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)

set_option backward.isDefEq.respectTransparency false

def productEncoding : FinEncoding (ℤ × ℤ) := LeanNPHardness.PairEncoding.finEncoding
  SignedIntegerMultiplication.integerEncoding SignedIntegerMultiplication.integerEncoding

/-- `dropSign` is used only when the second integer is a positive denominator. -/
def assemble (dropSign : Bool) (x : ℤ × ℤ) : List Bool :=
  SmithEncoding.encodeInt x.1 ++
    if dropSign then (SmithEncoding.encodeInt x.2).tail else SmithEncoding.encodeInt x.2

namespace Assemble

def isRight : Symbol → Bool | .inl _ => false | .inr _ => true
def bit : Symbol → Bool | .inl b => b | .inr b => b
def skip (dropSign seen : Bool) (s : Symbol) : Bool := dropSign && !seen && isRight s

def flatten (dropSign : Bool) : Bool → List Symbol → List Bool
  | _, [] => []
  | seen, s :: rest =>
      let tail := flatten dropSign (seen || isRight s) rest
      if skip dropSign seen s then tail else bit s :: tail

theorem flatten_length_le (d seen : Bool) (input : List Symbol) :
    (flatten d seen input).length ≤ input.length := by
  induction input generalizing seen with
  | nil => simp [flatten]
  | cons s rest ih =>
      simp only [flatten, List.length_cons]
      have h := ih (seen || isRight s)
      split
      · exact h.trans (Nat.le_succ _)
      · exact Nat.succ_le_succ h

theorem flatten_left (d seen : Bool) (left : List Bool) (rest : List Symbol) :
    flatten d seen (left.map Sum.inl ++ rest) = left ++ flatten d seen rest := by
  induction left with
  | nil => rfl
  | cons b left ih => simp [flatten, skip, isRight, bit, ih]

theorem flatten_right_seen (d : Bool) (right : List Bool) :
    flatten d true (right.map Sum.inr) = right := by
  induction right with
  | nil => rfl
  | cons b right ih => simp [flatten, skip, isRight, bit, ih]

theorem flatten_pair (d b : Bool) (left right : List Bool) :
    flatten d false (left.map Sum.inl ++ (b :: right).map Sum.inr) =
      left ++ if d then right else b :: right := by
  rw [flatten_left]
  simp [flatten, skip, isRight, bit, flatten_right_seen]

inductive Stack | input | scratch | output deriving DecidableEq, Fintype
inductive Label | scan | reverse deriving DecidableEq, Fintype
structure State where
  symbol : Option Symbol
  bit : Option Bool
  seen : Bool
  deriving DecidableEq, Fintype

def state (seen : Bool) : State := ⟨none, none, seen⟩
def Alphabet : Stack → Type | .input => Symbol | _ => Bool

def program (d : Bool) : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input (fun s b => {s with symbol := b})
      (.branch (fun s => s.symbol.isSome)
        (.branch (fun s => skip d s.seen (s.symbol.getD (Sum.inl false)))
          (.load (fun s => state (s.seen || isRight (s.symbol.getD (Sum.inl false))))
            (.goto fun _ => .scan))
          (.push .scratch (fun s => bit (s.symbol.getD (Sum.inl false)))
            (.load (fun s => state (s.seen || isRight (s.symbol.getD (Sum.inl false))))
              (.goto fun _ => .scan))))
        (.load (fun _ => state false) (.goto fun _ => .reverse)))
  | .reverse => .pop .scratch (fun s b => {s with bit := b})
      (.branch (fun s => s.bit.isSome)
        (.push .output (fun s => s.bit.getD false)
          (.load (fun _ => state false) (.goto fun _ => .reverse)))
        (.load (fun _ => state false) .halt))

def computer (d : Bool) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := state false
  Γk₀Fin := inferInstanceAs (Fintype Symbol)
  m := program d

def contents (input : List Symbol) (scratch output : List Bool) :
    (k : Stack) → List (Alphabet k)
  | .input => input
  | .scratch => scratch
  | .output => output

def cfg (d : Bool) (l : Option Label) (seen : Bool) (input : List Symbol)
    (scratch output : List Bool) : (computer d).Cfg := ⟨l, state seen, contents input scratch output⟩

private theorem scan_cons (d seen : Bool) (s : Symbol) (input : List Symbol)
    (scratch output : List Bool) :
    (computer d).step (cfg d (some .scan) seen (s :: input) scratch output) =
    some (cfg d (some .scan) (seen || isRight s) input
      (if skip d seen s then scratch else bit s :: scratch) output) := by
  cases s <;> cases d <;> cases seen <;>
    simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, skip, isRight, bit,
      Function.update]
  all_goals funext k; cases k <;> rfl

private theorem scan_nil (d seen : Bool) (scratch output : List Bool) :
    (computer d).step (cfg d (some .scan) seen [] scratch output) =
    some (cfg d (some .reverse) false [] scratch output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state]

theorem scan_run (d seen : Bool) (input : List Symbol) (scratch output : List Bool) :
    (fun q => q.bind (computer d).step)^[input.length + 1]
      (some (cfg d (some .scan) seen input scratch output)) =
    some (cfg d (some .reverse) false [] ((flatten d seen input).reverse ++ scratch) output) := by
  induction input generalizing seen scratch with
  | nil => simpa [flatten] using scan_nil d seen scratch output
  | cons s input ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, scan_cons, ih]
      by_cases hs : skip d seen s = true <;>
        simp [flatten, hs, List.reverse_cons, List.append_assoc]

private theorem reverse_cons (d b : Bool) (scratch output : List Bool) :
    (computer d).step (cfg d (some .reverse) false [] (b :: scratch) output) =
    some (cfg d (some .reverse) false [] scratch (b :: output)) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, Function.update]
  funext k; cases k <;> rfl
private theorem reverse_nil (d : Bool) (output : List Bool) :
    (computer d).step (cfg d (some .reverse) false [] [] output) =
    some (cfg d none false [] [] output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state]

theorem reverse_run (d : Bool) (scratch output : List Bool) :
    (fun q => q.bind (computer d).step)^[scratch.length + 1]
      (some (cfg d (some .reverse) false [] scratch output)) =
    some (cfg d none false [] [] (scratch.reverse ++ output)) := by
  induction scratch generalizing output with
  | nil => simpa using reverse_nil d output
  | cons b scratch ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, reverse_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Exact count: scan every source symbol, then reverse every retained bit. -/
theorem run (d : Bool) (input : List Symbol) :
    (fun q => q.bind (computer d).step)^[input.length + (flatten d false input).length + 2]
      (some (cfg d (some .scan) false input [] [])) =
    some (cfg d none false [] [] (flatten d false input)) := by
  rw [show input.length + (flatten d false input).length + 2 =
    ((flatten d false input).reverse.length + 1) + (input.length + 1) by simp; omega,
    Function.iterate_add_apply, scan_run]
  simp only [List.append_nil]
  rw [reverse_run]
  simp

private theorem init_eq (d : Bool) (bits : List Symbol) :
    initList (computer d) bits = cfg d (some .scan) false bits [] [] := by
  unfold initList cfg; congr; funext k; cases k <;> rfl
private theorem halt_eq (d : Bool) (bits : List Bool) :
    haltList (computer d) bits = cfg d none false [] [] bits := by
  unfold haltList cfg; congr; funext k; cases k <;> rfl

theorem flatten_encode (d : Bool) (x : ℤ × ℤ) :
    flatten d false (productEncoding.encode x) = assemble d x := by
  simp only [productEncoding, LeanNPHardness.PairEncoding.finEncoding,
    SignedIntegerMultiplication.integerEncoding, assemble]
  have h := flatten_pair d (decide (x.2 < 0)) (SmithEncoding.encodeInt x.1)
    (LeanNPHardness.BinaryNatLists.encodeNat x.2.natAbs)
  simpa only [SmithEncoding.encodeInt, List.tail_cons] using h

def outputsInTime (d : Bool) (x : ℤ × ℤ) :
    TM2OutputsInTime (computer d) (productEncoding.encode x) (some (assemble d x))
      (2 * (productEncoding.encode x).length + 2) where
  steps := (productEncoding.encode x).length + (flatten d false (productEncoding.encode x)).length + 2
  evals_in_steps := by
    change (fun q => q.bind (computer d).step)^[_]
      (some (initList (computer d) (productEncoding.encode x))) =
      some (haltList (computer d) (assemble d x))
    rw [init_eq, halt_eq, ← flatten_encode]
    exact run d (productEncoding.encode x)
  steps_le_m := by have := flatten_length_le d false (productEncoding.encode x); omega

noncomputable def computableInPolyTime (d : Bool) :
    TM2ComputableInPolyTime productEncoding LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding
      (assemble d) where
  tm := computer d
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun x := by
    simpa [LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using outputsInTime d x

end Assemble
end PhdThesisLean.RationalArithmetic
