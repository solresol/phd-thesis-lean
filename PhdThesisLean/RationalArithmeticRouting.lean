import PhdThesisLean.SignedIntegerMultiplication
import PhdThesisLean.RationalNormMachine

/-!
# Routing fraction products and comparison cross-products

Four original Boolean fraction fields are read with stack-based frame counters.
The finite parameter selects ordinary products or comparison cross-products.
Denominators acquire a positive sign for the existing signed multiplier. All
frame bits are retained and every transfer is charged. The input contract is
an encoded pair of positive-denominator fractions, which need not be reduced.
-/
namespace PhdThesisLean.RationalArithmetic

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)
open RationalVerifierBounds

set_option backward.isDefEq.respectTransparency false

/-- Concatenated original fraction words, with no added pair tags. -/
def encode (x : Fraction × Fraction) : List Bool := x.1.encode ++ x.2.encode

def decodePrefix (bits : List Bool) : Option (Fraction × List Bool) := do
  let (z, tail) ← SmithEncoding.decodeIntPrefix bits
  let (d, rest) ← LeanNPHardness.BinaryNatLists.decodeNatPrefix tail
  if hd : 0 < d then some (⟨z, d, hd⟩, rest) else none

@[simp] theorem decodePrefix_encode_append (x : Fraction) (rest : List Bool) :
    decodePrefix (x.encode ++ rest) = some (x, rest) := by
  cases x
  simp [decodePrefix, Fraction.encode, List.append_assoc, *]

def decode (bits : List Bool) : Option (Fraction × Fraction) := do
  let (a, tail) ← decodePrefix bits
  let (b, rest) ← decodePrefix tail
  if rest.isEmpty then some (a, b) else none

@[simp] theorem decode_encode (x : Fraction × Fraction) : decode (encode x) = some x := by
  have h := decodePrefix_encode_append x.2 []
  simp only [List.append_nil] at h
  simp [decode, encode, h]

def encoding : FinEncoding (Fraction × Fraction) where
  Γ := Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

abbrev Fields := (ℤ × ℤ) × (ℤ × ℤ)
abbrev Symbol := Sum Bool Bool

def fieldsEncoding : FinEncoding Fields := LeanNPHardness.PairEncoding.finEncoding
  SignedIntegerComparison.encoding SignedIntegerComparison.encoding

def prepare (cross : Bool) (x : Fraction × Fraction) : Fields :=
  if cross then ((x.1.num, x.2.den), (x.1.den, x.2.num))
  else ((x.1.num, x.2.num), (x.1.den, x.2.den))

namespace Prepare

inductive Stack
  | input | count | work (right : Bool) | output
  deriving DecidableEq, Fintype
inductive Label
  | field (second denominator : Bool) | prefix (second denominator : Bool)
  | payload (second denominator : Bool) | reverse (right : Bool)
  deriving DecidableEq, Fintype

def target (cross second denominator : Bool) : Bool := xor denominator (cross && second)
def next (second denominator : Bool) : Label :=
  if denominator then (if second then .reverse true else .field true false)
  else .field second true

def Alphabet : Stack → Type
  | .output => Symbol
  | _ => Bool

def program (cross : Bool) : Label → TM2.Stmt Alphabet Label (Option Bool)
  | .field s d =>
      if d then .push (.work (target cross s d)) (fun _ => false)
        (.load (fun _ => none) (.goto fun _ => .prefix s d))
      else .pop .input (fun _ b => b)
        (.push (.work (target cross s d)) (fun b => b.getD false)
          (.load (fun _ => none) (.goto fun _ => .prefix s d)))
  | .prefix s d => .pop .input (fun _ b => b)
      (.push (.work (target cross s d)) (fun b => b.getD false)
        (.branch (fun b => b.getD false)
          (.push .count (fun _ => true) (.load (fun _ => none) (.goto fun _ => .prefix s d)))
          (.load (fun _ => none) (.goto fun _ => .payload s d))))
  | .payload s d => .pop .count (fun _ b => b)
      (.branch Option.isSome
        (.pop .input (fun _ b => b)
          (.push (.work (target cross s d)) (fun b => b.getD false)
            (.load (fun _ => none) (.goto fun _ => .payload s d))))
        (.load (fun _ => none) (.goto fun _ => next s d)))
  | .reverse d => .pop (.work d) (fun _ b => b)
      (.branch Option.isSome
        (.push .output (fun b => if d then Sum.inr (b.getD false) else Sum.inl (b.getD false))
          (.load (fun _ => none) (.goto fun _ => .reverse d)))
        (.load (fun _ => none) (if d then .goto (fun _ => .reverse false) else .halt)))

def computer (cross : Bool) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .field false false
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program cross

def contents (input count : List Bool) (work : Bool → List Bool) (output : List Symbol) :
    (k : Stack) → List (Alphabet k)
  | .input => input
  | .count => count
  | .work d => work d
  | .output => output

def cfg (cross : Bool) (l : Option Label) (input count : List Bool)
    (work : Bool → List Bool) (output : List Symbol) : (computer cross).Cfg :=
  ⟨l, none, contents input count work output⟩

def put (w : Bool → List Bool) (d : Bool) (bits : List Bool) : Bool → List Bool :=
  Function.update w d (bits ++ w d)

@[simp] theorem put_nil (w : Bool → List Bool) (d : Bool) : put w d [] = w := by
  simp [put]
@[simp] theorem put_put (w : Bool → List Bool) (d : Bool) (a b : List Bool) :
    put (put w d a) d b = put w d (b ++ a) := by
  simp [put, List.append_assoc]

private theorem prefix_true (c s d : Bool) (input count : List Bool)
    (work : Bool → List Bool) (output : List Symbol) :
    (computer c).step (cfg c (some (.prefix s d)) (true :: input) count work output) =
    some (cfg c (some (.prefix s d)) input (true :: count)
      (put work (target c s d) [true]) output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, put, Function.update]
  funext k; cases k <;> simp [contents, Function.update]
  all_goals split <;> subst_vars <;> rfl

private theorem prefix_false (c s d : Bool) (input count : List Bool)
    (work : Bool → List Bool) (output : List Symbol) :
    (computer c).step (cfg c (some (.prefix s d)) (false :: input) count work output) =
    some (cfg c (some (.payload s d)) input count
      (put work (target c s d) [false]) output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, put, Function.update]
  funext k; cases k <;> simp [contents, Function.update]
  all_goals split <;> subst_vars <;> rfl

theorem prefix_run (c s d : Bool) (n : ℕ) (input count : List Bool)
    (work : Bool → List Bool) (output : List Symbol) :
    (fun q => q.bind (computer c).step)^[n + 1]
      (some (cfg c (some (.prefix s d)) (List.replicate n true ++ false :: input)
        count work output)) =
    some (cfg c (some (.payload s d)) input (List.replicate n true ++ count)
      (put work (target c s d) (false :: List.replicate n true)) output) := by
  induction n generalizing count work with
  | zero => simpa using prefix_false c s d input count work output
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [Function.iterate_succ_apply, Option.bind_some, prefix_true, ih]
      simp [LeanNPHardness.MachinePrimitives.replicate_true_append_cons]

private theorem payload_cons (c s d b : Bool) (input count : List Bool)
    (work : Bool → List Bool) (output : List Symbol) :
    (computer c).step (cfg c (some (.payload s d)) (b :: input) (true :: count) work output) =
    some (cfg c (some (.payload s d)) input count (put work (target c s d) [b]) output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, put, Function.update]
  funext k; cases k <;> simp [contents, Function.update]
  all_goals split <;> subst_vars <;> rfl

private theorem payload_nil (c s d : Bool) (input : List Bool)
    (work : Bool → List Bool) (output : List Symbol) :
    (computer c).step (cfg c (some (.payload s d)) input [] work output) =
    some (cfg c (some (next s d)) input [] work output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet]

theorem payload_run (c s d : Bool) (bits input : List Bool)
    (work : Bool → List Bool) (output : List Symbol) :
    (fun q => q.bind (computer c).step)^[bits.length + 1]
      (some (cfg c (some (.payload s d)) (bits ++ input) (List.replicate bits.length true)
        work output)) =
    some (cfg c (some (next s d)) input []
      (put work (target c s d) bits.reverse) output) := by
  induction bits generalizing work with
  | nil => simpa using payload_nil c s d input work output
  | cons b bits ih =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append]
      rw [Function.iterate_succ_apply, Option.bind_some, payload_cons, ih]
      simp [List.reverse_cons]

private theorem field_step (c s d sign : Bool) (input : List Bool)
    (work : Bool → List Bool) (output : List Symbol) :
    (computer c).step (cfg c (some (.field s d)) (if d then input else sign :: input)
      [] work output) =
    some (cfg c (some (.prefix s d)) input []
      (put work (target c s d) [if d then false else sign]) output) := by
  cases d <;>
    simp [computer, FinTM2.step, cfg, program, contents, Alphabet, put, Function.update]
  all_goals funext k; cases k <;> simp [contents, Function.update]
  all_goals split <;> subst_vars <;> rfl

/-- One field retains its frame and adds a positive sign for a denominator. -/
theorem field_run (c s d sign : Bool) (bits input : List Bool)
    (work : Bool → List Bool) (output : List Symbol) :
    (fun q => q.bind (computer c).step)^[2 * bits.length + 3]
      (some (cfg c (some (.field s d))
        ((if d then LeanNPHardness.BinaryNatLists.frame bits
          else sign :: LeanNPHardness.BinaryNatLists.frame bits) ++ input) [] work output)) =
    some (cfg c (some (next s d)) input []
      (put work (target c s d)
        ((if d then false else sign) :: LeanNPHardness.BinaryNatLists.frame bits).reverse) output) := by
  rw [show 2 * bits.length + 3 = (bits.length + 1 + (bits.length + 1)) + 1 by omega,
    Function.iterate_succ_apply, Option.bind_some]
  have h := field_step c s d sign (LeanNPHardness.BinaryNatLists.frame bits ++ input) work output
  have he : (if d then LeanNPHardness.BinaryNatLists.frame bits else sign ::
      LeanNPHardness.BinaryNatLists.frame bits) ++ input =
      if d then LeanNPHardness.BinaryNatLists.frame bits ++ input else
        sign :: (LeanNPHardness.BinaryNatLists.frame bits ++ input) := by cases d <;> rfl
  rw [he, h]
  simp only [LeanNPHardness.BinaryNatLists.frame, List.append_assoc, List.cons_append]
  rw [Function.iterate_add_apply, prefix_run]
  simp only [List.append_nil]
  rw [payload_run]
  simp [List.reverse_cons, List.reverse_append, List.append_assoc]

private theorem reverse_cons (c d b : Bool) (rest : List Bool)
    (work : Bool → List Bool) (output : List Symbol) :
    (computer c).step (cfg c (some (.reverse d)) [] []
      (Function.update work d (b :: rest)) output) =
    some (cfg c (some (.reverse d)) [] [] (Function.update work d rest)
      ((if d then Sum.inr b else Sum.inl b) :: output)) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, Function.update]
  funext k; cases k <;> simp [contents, Function.update]
  all_goals split <;> subst_vars <;> rfl

private theorem reverse_nil (c d : Bool) (work : Bool → List Bool) (output : List Symbol) :
    (computer c).step (cfg c (some (.reverse d)) [] [] (Function.update work d []) output) =
    some (cfg c (if d then some (.reverse false) else none) [] []
      (Function.update work d []) output) := by
  cases d <;> simp [computer, FinTM2.step, cfg, program, contents, Alphabet, Function.update]

theorem reverse_run (c d : Bool) (bits : List Bool)
    (work : Bool → List Bool) (output : List Symbol) :
    (fun q => q.bind (computer c).step)^[bits.length + 1]
      (some (cfg c (some (.reverse d)) [] [] (Function.update work d bits) output)) =
    some (cfg c (if d then some (.reverse false) else none) [] []
      (Function.update work d [])
      ((bits.reverse.map (fun b => if d then Sum.inr b else Sum.inl b)) ++ output)) := by
  induction bits generalizing output with
  | nil => simpa using reverse_nil c d work output
  | cons b bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, reverse_cons, ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

def buffers (left right : List Bool) : Bool → List Bool := fun d => if d then right else left

@[simp] theorem put_buffers_false (left right bits : List Bool) :
    put (buffers left right) false bits = buffers (bits ++ left) right := by
  funext d; cases d <;> simp [put, buffers]
@[simp] theorem put_buffers_true (left right bits : List Bool) :
    put (buffers left right) true bits = buffers left (bits ++ right) := by
  funext d; cases d <;> simp [put, buffers]
@[simp] theorem update_buffers_false (left right bits : List Bool) :
    Function.update (buffers left right) false bits = buffers bits right := by
  funext d; cases d <;> simp [buffers]
@[simp] theorem update_buffers_true (left right bits : List Bool) :
    Function.update (buffers left right) true bits = buffers left bits := by
  funext d; cases d <;> simp [buffers]

theorem finish_run (c : Bool) (left right : List Bool) :
    (fun q => q.bind (computer c).step)^[left.length + right.length + 2]
      (some (cfg c (some (.reverse true)) [] [] (buffers left.reverse right.reverse) [])) =
    some (cfg c none [] [] (buffers [] [])
      (left.map Sum.inl ++ right.map Sum.inr)) := by
  have hr := reverse_run c true right.reverse (buffers left.reverse []) []
  have hl := reverse_run c false left.reverse (buffers [] []) (right.map Sum.inr)
  simp only [update_buffers_true, List.length_reverse, List.reverse_reverse,
    ↓reduceIte, List.append_nil] at hr
  simp only [update_buffers_false, List.length_reverse, List.reverse_reverse,
    Bool.false_eq_true, ↓reduceIte] at hl
  rw [show left.length + right.length + 2 = (left.length + 1) + (right.length + 1) by omega,
    Function.iterate_add_apply, hr, hl]

def fieldWord (sign : Bool) (bits : List Bool) : List Bool :=
  sign :: LeanNPHardness.BinaryNatLists.frame bits

def sourceWord (sa sb : Bool) (a b d e : List Bool) : List Bool :=
  fieldWord sa a ++ LeanNPHardness.BinaryNatLists.frame b ++
    fieldWord sb d ++ LeanNPHardness.BinaryNatLists.frame e

def leftWord (c sa sb : Bool) (a d e : List Bool) : List Bool :=
  fieldWord sa a ++ if c then fieldWord false e else fieldWord sb d

def rightWord (c sb : Bool) (b d e : List Bool) : List Bool :=
  fieldWord false b ++ if c then fieldWord sb d else fieldWord false e

theorem scan_run (c sa sb : Bool) (a b d e : List Bool) :
    (fun q => q.bind (computer c).step)^[2 * (a.length + b.length + d.length + e.length) + 12]
      (some (cfg c (some (.field false false)) (sourceWord sa sb a b d e) [] (buffers [] []) [])) =
    some (cfg c (some (.reverse true)) [] []
      (buffers (leftWord c sa sb a d e).reverse (rightWord c sb b d e).reverse) []) := by
  rw [show 2 * (a.length + b.length + d.length + e.length) + 12 =
      ((2 * e.length + 3 + (2 * d.length + 3)) + (2 * b.length + 3)) +
        (2 * a.length + 3) by omega, Function.iterate_add_apply]
  unfold sourceWord
  simp only [List.append_assoc]
  change (fun q => q.bind (computer c).step)^[_]
    ((fun q => q.bind (computer c).step)^[2 * a.length + 3]
      (some (cfg c (some (.field false false))
        ((if false then LeanNPHardness.BinaryNatLists.frame a else sa ::
          LeanNPHardness.BinaryNatLists.frame a) ++ _ ) [] (buffers [] []) []))) = _
  rw [field_run]
  simp only [next, target, Bool.and_false, Bool.xor_false, Bool.false_eq_true, ↓reduceIte,
    put_buffers_false, List.append_nil]
  rw [Function.iterate_add_apply]
  have hb := field_run c false true false b
    (fieldWord sb d ++ LeanNPHardness.BinaryNatLists.frame e)
    (buffers (fieldWord sa a).reverse []) []
  simp only [↓reduceIte, Bool.false_eq_true, next, target, Bool.and_false, Bool.xor_false,
    put_buffers_true, List.append_nil] at hb
  simp only [fieldWord] at hb ⊢
  rw [hb, Function.iterate_add_apply]
  have hd := field_run c true false sb d (LeanNPHardness.BinaryNatLists.frame e)
    (buffers (fieldWord sa a).reverse (fieldWord false b).reverse) []
  simp only [↓reduceIte, Bool.false_eq_true, next] at hd
  simp only [fieldWord] at hd ⊢
  rw [hd]
  have he := field_run c true true false e []
    (put (buffers (fieldWord sa a).reverse (fieldWord false b).reverse)
      (target c true false) (fieldWord sb d).reverse) []
  simp only [↓reduceIte, List.append_nil, next] at he
  simp only [fieldWord] at he ⊢
  rw [he]
  cases c <;> simp [target, leftWord, rightWord, List.reverse_append, fieldWord]

/-- Exact routing cost in the original Boolean input, including both reversals. -/
theorem run (c sa sb : Bool) (a b d e : List Bool) :
    (fun q => q.bind (computer c).step)^[2 * (sourceWord sa sb a b d e).length + 10]
      (some (cfg c (some (.field false false)) (sourceWord sa sb a b d e) [] (buffers [] []) [])) =
    some (cfg c none [] [] (buffers [] [])
      ((leftWord c sa sb a d e).map Sum.inl ++ (rightWord c sb b d e).map Sum.inr)) := by
  have ht : 2 * (sourceWord sa sb a b d e).length + 10 =
      ((leftWord c sa sb a d e).length + (rightWord c sb b d e).length + 2) +
        (2 * (a.length + b.length + d.length + e.length) + 12) := by
    cases c <;> simp [sourceWord, fieldWord, leftWord, rightWord,
      LeanNPHardness.BinaryNatLists.frame] <;> omega
  rw [ht, Function.iterate_add_apply, scan_run, finish_run]

private theorem init_eq (c : Bool) (bits : List Bool) :
    initList (computer c) bits = cfg c (some (.field false false)) bits [] (buffers [] []) [] := by
  unfold initList cfg; congr; funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)
private theorem halt_eq (c : Bool) (bits : List Symbol) :
    haltList (computer c) bits = cfg c none [] [] (buffers [] []) bits := by
  unfold haltList cfg; congr; funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

def outputsInTime (c : Bool) (x : Fraction × Fraction) :
    TM2OutputsInTime (computer c) (encode x) (some (fieldsEncoding.encode (prepare c x)))
      (2 * (encode x).length + 10) where
  steps := 2 * (encode x).length + 10
  steps_le_m := le_rfl
  evals_in_steps := by
    change (fun q => q.bind (computer c).step)^[_]
      (some (initList (computer c) (encode x))) =
      some (haltList (computer c) (fieldsEncoding.encode (prepare c x)))
    rw [init_eq, halt_eq]
    have h := run c (decide (x.1.num < 0)) (decide (x.2.num < 0))
      (encodeNat x.1.num.natAbs) (encodeNat x.1.den)
      (encodeNat x.2.num.natAbs) (encodeNat x.2.den)
    have hn₁ : ¬(x.1.den : ℤ) < 0 := by omega
    have hn₂ : ¬(x.2.den : ℤ) < 0 := by omega
    cases c <;> simpa [hn₁, hn₂, encode, Fraction.encode, sourceWord, fieldWord, leftWord, rightWord,
      prepare, fieldsEncoding, LeanNPHardness.PairEncoding.finEncoding,
      SignedIntegerComparison.encoding, SignedIntegerComparison.encode, SmithEncoding.encodeInt,
      LeanNPHardness.BinaryNatLists.encodeNat, List.append_assoc] using h

noncomputable def computableInPolyTime (c : Bool) :
    TM2ComputableInPolyTime encoding fieldsEncoding (prepare c) where
  tm := computer c
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 10
  outputsFun x := by
    simpa [encoding, Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      using outputsInTime c x

end Prepare
end PhdThesisLean.RationalArithmetic
