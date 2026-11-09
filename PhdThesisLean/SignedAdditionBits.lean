import PhdThesisLean.BinarySubtractionMachine
import PhdThesisLean.SignedIntegerMultiplication

/-! Bit arithmetic for signed addition and subtraction on framed binary inputs. -/
namespace PhdThesisLean.SignedIntegerAddition

open Computability
open LeanNPHardness.MachinePrimitives
open BinarySubtraction (value)

/-- Addition or subtraction at one aligned position. -/
def bitStep (add carry : Bool) (a b : Option Bool) : Bool × Bool :=
  if add then binaryAddStep carry a b
  else BinarySubtraction.subStep carry (a.getD false) (b.getD false)

/-- Low-to-high arithmetic, allowing high zero padding on subtraction. -/
def rawBits (add : Bool) : Bool → List Bool → List Bool → List Bool
  | c, [], [] => if add && c then [true] else []
  | c, a :: as, [] =>
      let s := bitStep add c (some a) none
      s.1 :: rawBits add s.2 as []
  | c, [], b :: bs =>
      let s := bitStep add c none (some b)
      s.1 :: rawBits add s.2 [] bs
  | c, a :: as, b :: bs =>
      let s := bitStep add c (some a) (some b)
      s.1 :: rawBits add s.2 as bs

theorem rawBits_add (c : Bool) (a b : List Bool) :
    rawBits true c a b = binaryAddBitsAux c a b := by
  induction a generalizing c b with
  | nil =>
      induction b generalizing c with
      | nil => simp [rawBits, binaryAddBitsAux]
      | cons b bs ih => simp [rawBits, binaryAddBitsAux, bitStep, ih]
  | cons a as ih => cases b <;> simp [rawBits, binaryAddBitsAux, bitStep, ih]

theorem rawBits_sub (c : Bool) (a b : List Bool) :
    rawBits false c a b = (BinarySubtraction.subtract c (BinaryNatPair.zipBits a b)).1 := by
  induction a generalizing c b with
  | nil =>
      induction b generalizing c with
      | nil => simp [rawBits, BinaryNatPair.zipBits, BinarySubtraction.subtract]
      | cons b bs ih => simp [rawBits, BinaryNatPair.zipBits, BinarySubtraction.subtract, bitStep, ih]
  | cons a as ih => cases b <;>
      simp [rawBits, BinaryNatPair.zipBits, BinarySubtraction.subtract, bitStep, ih]

theorem rawBits_length (add c : Bool) (a b : List Bool) :
    (rawBits add c a b).length ≤ max a.length b.length + 1 := by
  induction a generalizing c b with
  | nil =>
      induction b generalizing c with
      | nil => simp [rawBits]; split <;> simp
      | cons b bs ih => simpa [rawBits] using Nat.succ_le_succ (ih (bitStep add c none (some b)).2)
  | cons a as ih =>
      cases b with
      | nil => simpa [rawBits] using Nat.succ_le_succ (ih (bitStep add c (some a) none).2 [])
      | cons b bs => simpa [rawBits, Nat.succ_max_succ] using
          Nat.succ_le_succ (ih (bitStep add c (some a) (some b)).2 bs)

/-- Canonical interpretation of the actual arithmetic bits; subtraction requires
that its routed first magnitude is the larger one. -/
theorem rawBits_value (add : Bool) (m n : ℕ) (h : add = false → n ≤ m) :
    value (rawBits add false (encodeNat m) (encodeNat n)) =
      if add then m + n else m - n := by
  cases add with
  | true => simp [rawBits_add, binaryAddBitsAux_encodeNat, BinarySubtraction.value_encode]
  | false =>
      rw [rawBits_sub]
      have hb := BinarySubtraction.subtract_borrow false (BinaryNatPair.zipBits (encodeNat m) (encodeNat n))
      have hz := BinarySubtraction.zip_values (encodeNat m) (encodeNat n)
      simp only [BinarySubtraction.value_encode] at hz
      simp only [hz.1, hz.2, Bool.toNat_false, Nat.add_zero] at hb
      have hle := h rfl
      have hh := BinarySubtraction.subtract_correct false (BinaryNatPair.zipBits (encodeNat m) (encodeNat n))
      simpa [hb, hz.1, hz.2, not_lt.mpr hle] using hh

/-- Sign-magnitude interpretation, permitting negative zero internally. -/
def signed (negative : Bool) (n : ℕ) : ℤ := if negative then -(n : ℤ) else n

theorem signed_natAbs (a : ℤ) : signed (decide (a < 0)) a.natAbs = a := by
  by_cases h : a < 0
  · simp [signed, h, abs_of_neg h]
  · simp [signed, h, abs_of_nonneg (le_of_not_gt h)]

theorem signed_xor (s t : Bool) (n : ℕ) :
    signed (xor s t) n = if t then -signed s n else signed s n := by
  cases s <;> cases t <;> simp [signed]

def magnitude (sa sb : Bool) (m n : ℕ) : ℕ :=
  if sa == sb then m + n else if m ≤ n then n - m else m - n

def resultSign (sa sb : Bool) (m n : ℕ) : Bool := if m ≤ n then sb else sa

/-- Selecting the larger magnitude's sign handles both mixed-sign orders. -/
theorem signed_magnitude (sa sb : Bool) (m n : ℕ) :
    signed (resultSign sa sb m n) (magnitude sa sb m n) = signed sa m + signed sb n := by
  by_cases h : m ≤ n
  · cases sa <;> cases sb <;> simp [signed, resultSign, magnitude, h, Int.ofNat_sub h] <;> omega
  · have hn : n ≤ m := by omega
    cases sa <;> cases sb <;> simp [signed, resultSign, magnitude, h, Int.ofNat_sub hn] <;> omega

theorem encode_signed (negative : Bool) (n : ℕ) :
    SmithEncoding.encodeInt (signed negative n) =
      (negative && decide (n ≠ 0)) :: LeanNPHardness.BinaryNatLists.encodeNat n := by
  cases negative <;> simp [signed, SmithEncoding.encodeInt, Nat.pos_iff_ne_zero]

/-- The same finite machine handles addition and subtraction by flipping only
its second sign at input; the bit payload and its frame are unchanged. -/
def operation (subtract : Bool) (a b : ℤ) : ℤ := if subtract then a - b else a + b

theorem operation_eq_signed (subtract : Bool) (a b : ℤ) :
    operation subtract a b =
      signed (resultSign (decide (a < 0)) (xor (decide (b < 0)) subtract) a.natAbs b.natAbs)
        (magnitude (decide (a < 0)) (xor (decide (b < 0)) subtract) a.natAbs b.natAbs) := by
  rw [signed_magnitude, signed_xor, signed_natAbs, signed_natAbs]
  cases subtract <;> simp [operation, sub_eq_add_neg]

end PhdThesisLean.SignedIntegerAddition
