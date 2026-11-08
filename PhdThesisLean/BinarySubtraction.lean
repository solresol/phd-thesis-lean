import PhdThesisLean.FixedBasePowerMachine
import LeanNPHardness.BinaryArithmetic

/-!
# Binary subtraction with a finite borrow

This module proves the bit arithmetic used by `BinarySubtractionMachine`.
The input is the library's aligned pair of canonical binary naturals. An
underflow returns zero, as required by natural subtraction. Otherwise the
reverse pass removes high zero bits and returns the canonical difference.
-/
namespace PhdThesisLean.BinarySubtraction

open Computability
open LeanNPHardness.MachinePrimitives

abbrev Symbol := Option Bool × Option Bool
abbrev encoding := BinaryNatPair.finEncoding

/-- Numeric value of a possibly noncanonical little-endian bit word. -/
def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

theorem value_encode (n : ℕ) : value (encodeNat n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n; rfl
      rw [FixedBasePowerMachine.encodeNat_cons n hn, value, ih (n / 2) (by omega)]
      have hb : (decide (n % 2 = 1)).toNat = n % 2 := by
        have := Nat.mod_lt n (by decide : 0 < 2)
        by_cases h : n % 2 = 1
        · simp [h]
        · have h0 : n % 2 = 0 := by omega
          simp [h0]
      rw [hb]; omega

theorem value_lt (bs : List Bool) : value bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih => cases b <;> simp only [value, List.length_cons, pow_succ, Bool.toNat_false,
      Bool.toNat_true] <;> omega

def leftValue : List Symbol → ℕ
  | [] => 0
  | p :: ps => (p.1.getD false).toNat + 2 * leftValue ps

def rightValue : List Symbol → ℕ
  | [] => 0
  | p :: ps => (p.2.getD false).toNat + 2 * rightValue ps

theorem zip_values (a b : List Bool) :
    leftValue (BinaryNatPair.zipBits a b) = value a ∧
    rightValue (BinaryNatPair.zipBits a b) = value b := by
  induction a generalizing b with
  | nil =>
      induction b with
      | nil => simp [BinaryNatPair.zipBits, leftValue, rightValue, value]
      | cons b bs ih => simpa [BinaryNatPair.zipBits, leftValue, rightValue, value] using ih
  | cons a as ih =>
      cases b with
      | nil => simpa [BinaryNatPair.zipBits, leftValue, rightValue, value] using ih []
      | cons b bs => simpa [BinaryNatPair.zipBits, leftValue, rightValue, value] using ih bs

theorem zip_length (a b : List Bool) :
    (BinaryNatPair.zipBits a b).length = max a.length b.length := by
  induction a generalizing b with
  | nil =>
      induction b with
      | nil => simp [BinaryNatPair.zipBits]
      | cons b bs ih => simpa [BinaryNatPair.zipBits] using congrArg Nat.succ ih
  | cons a as ih =>
      cases b with
      | nil => simpa [BinaryNatPair.zipBits] using congrArg Nat.succ (ih [])
      | cons b bs => simp [BinaryNatPair.zipBits, ih, Nat.succ_max_succ]

@[simp] theorem encode_length (m n : ℕ) :
    (encoding.encode (m, n)).length = max m.size n.size := by
  simp [encoding, BinaryNatPair.finEncoding, BinaryNatPair.encode, zip_length,
    LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size]

/-- Canonical subtraction never increases the input width. -/
theorem output_length_le (m n : ℕ) :
    (encodeNat (m - n)).length ≤ (encoding.encode (m, n)).length := by
  rw [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size, encode_length]
  exact (Nat.size_le_size (Nat.sub_le m n)).trans (Nat.le_max_left _ _)

/-- Emitted bit and next borrow; all arguments and results are finite. -/
def subStep (borrow a b : Bool) : Bool × Bool :=
  (xor (xor a b) borrow, (!a && (b || borrow)) || (b && borrow))

theorem subStep_identity (borrow a b : Bool) :
    a.toNat + 2 * (subStep borrow a b).2.toNat =
      b.toNat + borrow.toNat + (subStep borrow a b).1.toNat := by
  cases borrow <;> cases a <;> cases b <;> decide

/-- Raw low-to-high result bits and the final underflow bit. -/
def subtract : Bool → List Symbol → List Bool × Bool
  | borrow, [] => ([], borrow)
  | borrow, p :: ps =>
      let s := subStep borrow (p.1.getD false) (p.2.getD false)
      let r := subtract s.2 ps
      (s.1 :: r.1, r.2)

@[simp] theorem subtract_length (borrow : Bool) (ps : List Symbol) :
    (subtract borrow ps).1.length = ps.length := by
  induction ps generalizing borrow with
  | nil => rfl
  | cons p ps ih => simp [subtract, ih]

/-- Exact borrow invariant, including underflow and noncanonical padding. -/
theorem subtract_identity (borrow : Bool) (ps : List Symbol) :
    leftValue ps + 2 ^ ps.length * (subtract borrow ps).2.toNat =
      rightValue ps + borrow.toNat + value (subtract borrow ps).1 := by
  induction ps generalizing borrow with
  | nil => simp [subtract, leftValue, rightValue, value]
  | cons p ps ih =>
      have h := ih (subStep borrow (p.1.getD false) (p.2.getD false)).2
      have hs := subStep_identity borrow (p.1.getD false) (p.2.getD false)
      simp only [subtract, List.length_cons, leftValue, rightValue, value, pow_succ]
      nlinarith

theorem subtract_correct (borrow : Bool) (ps : List Symbol) :
    (if (subtract borrow ps).2 then 0 else value (subtract borrow ps).1) =
      leftValue ps - (rightValue ps + borrow.toNat) := by
  have hi := subtract_identity borrow ps
  have hb := value_lt (subtract borrow ps).1
  rw [subtract_length] at hb
  cases h : (subtract borrow ps).2 <;> simp [h] at hi ⊢ <;> omega

/-- The final finite-control bit is exactly the arithmetic underflow test. -/
theorem subtract_borrow (borrow : Bool) (ps : List Symbol) :
    (subtract borrow ps).2 = decide (leftValue ps < rightValue ps + borrow.toNat) := by
  have hi := subtract_identity borrow ps
  have hb := value_lt (subtract borrow ps).1
  rw [subtract_length] at hb
  cases h : (subtract borrow ps).2 <;> simp [h] at hi ⊢ <;> omega

theorem subtract_encode (m n : ℕ) :
    (if (subtract false (encoding.encode (m, n))).2 then 0
      else value (subtract false (encoding.encode (m, n))).1) = m - n := by
  have h := subtract_correct false (encoding.encode (m, n))
  have hz := zip_values (encodeNat m) (encodeNat n)
  simpa only [encoding, BinaryNatPair.finEncoding, BinaryNatPair.encode, hz.1, hz.2,
    value_encode, Bool.toNat_false, Nat.add_zero] using h

/-- Push a low bit while keeping zero's canonical empty encoding. -/
def pushBit (b : Bool) (bs : List Bool) : List Bool :=
  if b || !bs.isEmpty then b :: bs else []

theorem encode_isEmpty (n : ℕ) : (encodeNat n).isEmpty = decide (n = 0) := by
  by_cases hn : n = 0
  · subst n; rfl
  · rw [FixedBasePowerMachine.encodeNat_cons n hn]
    simp [hn]

theorem pushBit_encode (b : Bool) (n : ℕ) :
    pushBit b (encodeNat n) = encodeNat (b.toNat + 2 * n) := by
  by_cases hn : n = 0
  · subst n; cases b <;> rfl
  · have h : b.toNat + 2 * n ≠ 0 := by omega
    rw [FixedBasePowerMachine.encodeNat_cons _ h]
    cases b <;> simp [pushBit, encode_isEmpty, hn]
    congr 1; omega

def restoreValue (bs : List Bool) (n : ℕ) : ℕ :=
  bs.foldl (fun n b => b.toNat + 2 * n) n

theorem restoreValue_append (a b : List Bool) (n : ℕ) :
    restoreValue (a ++ b) n = restoreValue b (restoreValue a n) := by
  simp [restoreValue, List.foldl_append]

theorem restoreValue_reverse (bs : List Bool) : restoreValue bs.reverse 0 = value bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      rw [List.reverse_cons, restoreValue_append, ih]
      rfl

#print axioms subtract_identity
#print axioms subtract_encode
#print axioms pushBit_encode

end PhdThesisLean.BinarySubtraction
