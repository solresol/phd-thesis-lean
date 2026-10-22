import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic

/-!
# Integer row-addition invariants for a future Smith algorithm

This is one arithmetic primitive, not a Smith algorithm or a runtime theorem.
The power-of-two bound controls coefficient magnitude after one row addition;
bounding the number of operations and every intermediate coefficient remains open.
-/

namespace PhdThesisLean.SmithRowOperations

variable {m n : ℕ}

/-- Add `c` times source row `s` to destination row `r`. -/
def rowAdd (A : Matrix (Fin m) (Fin n) ℤ) (r s : Fin m) (c : ℤ) :
    Matrix (Fin m) (Fin n) ℤ :=
  fun i j => if i = r then A i j + c * A s j else A i j

/-- The executable update is precisely multiplication by mathlib's elementary matrix. -/
theorem rowAdd_eq_transvection_mul (A : Matrix (Fin m) (Fin n) ℤ) (r s : Fin m) (c : ℤ) :
    rowAdd A r s c = Matrix.transvection r s c * A := by
  ext i j
  by_cases hi : i = r
  · subst i
    simp [rowAdd]
  · simp [rowAdd, hi, Matrix.transvection_mul_apply_of_ne]

/-- Distinct source and destination make integer row addition reversible. -/
theorem rowAdd_inverse (A : Matrix (Fin m) (Fin n) ℤ) (r s : Fin m)
    (h : r ≠ s) (c : ℤ) : rowAdd (rowAdd A r s c) r s (-c) = A := by
  funext i j
  by_cases hi : i = r
  · subst i
    simp [rowAdd, h.symm]
  · simp [rowAdd, hi]

/-- A uniform entry bound includes the multiplier's size, rather than treating
integer arithmetic as a constant-cost operation. -/
theorem rowAdd_natAbs_le (A : Matrix (Fin m) (Fin n) ℤ) (r s : Fin m)
    (c : ℤ) (H C : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ H) (hc : c.natAbs ≤ C) :
    ∀ i j, (rowAdd A r s c i j).natAbs ≤ (C + 1) * H := by
  intro i j
  by_cases hi : i = r
  · simp only [rowAdd, ite_eq_left hi]
    calc
      (A i j + c * A s j).natAbs ≤ (A i j).natAbs + (c * A s j).natAbs :=
        Int.natAbs_add_le _ _
      _ = (A i j).natAbs + c.natAbs * (A s j).natAbs := by rw [Int.natAbs_mul]
      _ ≤ H + C * H := Nat.add_le_add (hA i j) (Nat.mul_le_mul hc (hA s j))
      _ = (C + 1) * H := by ring
  · simp only [rowAdd, ite_eq_right hi]
    have := hA i j
    nlinarith

/-- Binary-height form: one row addition increases the magnitude exponent by
at most the multiplier exponent plus one. No machine-time claim is made. -/
theorem rowAdd_pow_bound (A : Matrix (Fin m) (Fin n) ℤ) (r s : Fin m)
    (c : ℤ) (a b : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ a)
    (hc : c.natAbs ≤ 2 ^ b) :
    ∀ i j, (rowAdd A r s c i j).natAbs ≤ 2 ^ (a + b + 1) := by
  intro i j
  have h := rowAdd_natAbs_le A r s c (2 ^ a) (2 ^ b) hA hc i j
  have hb : 0 < (2 : ℕ) ^ b := by positivity
  have heq : (2 : ℕ) ^ (a + b + 1) = 2 ^ a * 2 ^ b * 2 := by
    rw [pow_add, pow_add]
    norm_num
  have hcoef : (2 : ℕ) ^ b + 1 ≤ 2 ^ b + 2 ^ b := by omega
  calc
    _ ≤ (2 ^ b + 1) * 2 ^ a := h
    _ ≤ (2 ^ b + 2 ^ b) * 2 ^ a := Nat.mul_le_mul_right _ hcoef
    _ = 2 ^ (a + b + 1) := by rw [heq]; ring

end PhdThesisLean.SmithRowOperations

#print axioms PhdThesisLean.SmithRowOperations.rowAdd_inverse
#print axioms PhdThesisLean.SmithRowOperations.rowAdd_eq_transvection_mul
#print axioms PhdThesisLean.SmithRowOperations.rowAdd_natAbs_le
#print axioms PhdThesisLean.SmithRowOperations.rowAdd_pow_bound
