import PhdThesisLean.RationalWitnesses
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Data.Nat.Size

/-!
# Bit bounds for rational contact witnesses

Source: `complexity-regimes/eth-addendum.tex`, `prop:regression-np-complete`.
The size measure below counts binary numerator magnitudes and denominators.
These are coefficient-size theorems, not a verifier runtime theorem.
-/

namespace PhdThesisLean.RationalWitnessBounds

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Matrix
open RationalWitnesses

/-- Binary payload of a reduced rational, excluding sign and framing. -/
def ratBits (q : ℚ) : ℕ := q.num.natAbs.size + q.den.size

section Clearing

variable {ι : Type*} [Fintype ι]

def dataBits (v : ι → ℚ) : ℕ := ∑ i, ratBits (v i)

/-- A product, rather than a computed least common multiple, suffices. -/
def commonDen (v : ι → ℚ) : ℕ := ∏ i, (v i).den

theorem commonDen_pos (v : ι → ℚ) : 0 < commonDen v :=
  Finset.prod_pos fun i _ => (v i).den_pos

theorem den_dvd_commonDen (v : ι → ℚ) (i : ι) : (v i).den ∣ commonDen v := by
  classical
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem ratBits_le_dataBits (v : ι → ℚ) (i : ι) : ratBits (v i) ≤ dataBits v :=
  Finset.single_le_sum (fun j _ => Nat.zero_le (ratBits (v j))) (Finset.mem_univ i)

/-- The denominator product is bounded by the sum of the original binary
payloads, even for an empty family. -/
theorem commonDen_le_pow (v : ι → ℚ) : commonDen v ≤ 2 ^ dataBits v := by
  calc
    commonDen v ≤ ∏ i, 2 ^ ratBits (v i) := by
      apply Finset.prod_le_prod
      intro i _
      exact (Nat.lt_size_self _).le.trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
    _ = 2 ^ dataBits v := by rw [Finset.prod_pow_eq_pow_sum]; rfl

/-- Integral entry obtained by clearing all denominators at once. -/
def cleared (v : ι → ℚ) (i : ι) : ℤ :=
  (v i).num * Int.ofNat (commonDen v / (v i).den)

theorem cleared_cast (v : ι → ℚ) (i : ι) :
    (cleared v i : ℚ) = commonDen v * v i := by
  have hd : ((v i).den : ℚ) ≠ 0 := by exact_mod_cast (v i).den_ne_zero
  have he : ((commonDen v / (v i).den : ℕ) : ℚ) * (v i).den = commonDen v := by
    exact_mod_cast Nat.div_mul_cancel (den_dvd_commonDen v i)
  simp only [cleared, Int.cast_mul, Int.ofNat_eq_natCast, Int.cast_natCast]
  conv_rhs => rw [← (v i).num_div_den]
  rw [← mul_div_assoc]
  apply (eq_div_iff hd).mpr
  calc
    _ = (v i).num * (((commonDen v / (v i).den : ℕ) : ℚ) * (v i).den) := by ring
    _ = _ := by rw [he]; ring

theorem cleared_natAbs_le (v : ι → ℚ) (i : ι) :
    (cleared v i).natAbs ≤ 2 ^ (2 * dataBits v) := by
  have hn : (v i).num.natAbs ≤ 2 ^ dataBits v := by
    apply (Nat.lt_size_self _).le.trans
    exact Nat.pow_le_pow_right (by decide)
      ((Nat.le_add_right _ _).trans (ratBits_le_dataBits v i))
  calc
    (cleared v i).natAbs = (v i).num.natAbs * (commonDen v / (v i).den) := by
      simp only [cleared, Int.natAbs_mul, Int.ofNat_eq_natCast, Int.natAbs_natCast]
    _ ≤ 2 ^ dataBits v * 2 ^ dataBits v :=
      Nat.mul_le_mul hn ((Nat.div_le_self _ _).trans (commonDen_le_pow v))
    _ = 2 ^ (2 * dataBits v) := by rw [← pow_add]; congr 1; omega

end Clearing

/-- The elementary Leibniz bound, retaining the `s log s` term. -/
theorem det_natAbs_le_pow {s h : ℕ} (M : Matrix (Fin s) (Fin s) ℤ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ h) :
    M.det.natAbs ≤ 2 ^ (s * (h + s.size)) := by
  have hb : |M.det| ≤ (s.factorial : ℤ) * (2 ^ h : ℤ) ^ s := by
    simpa using Matrix.det_le (abv := AbsoluteValue.abs)
      (fun i j => (by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hM i j : |M i j| ≤ (2 ^ h : ℤ)))
  have hn : M.det.natAbs ≤ s.factorial * (2 ^ h) ^ s := by
    rw [← Int.natCast_natAbs] at hb
    exact_mod_cast hb
  calc
    M.det.natAbs ≤ s.factorial * (2 ^ h) ^ s := hn
    _ ≤ (2 ^ s.size) ^ s * (2 ^ h) ^ s := by
      apply Nat.mul_le_mul_right
      exact s.factorial_le_pow.trans (Nat.pow_le_pow_left (Nat.lt_size_self s).le s)
    _ = 2 ^ (s * (h + s.size)) := by
      rw [← mul_pow, ← pow_add, ← pow_mul]
      congr 1
      ring

theorem det_size_le {s h : ℕ} (M : Matrix (Fin s) (Fin s) ℤ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ h) :
    M.det.natAbs.size ≤ s * (h + s.size) + 1 := by
  simpa only [Nat.size_pow] using Nat.size_le_size (det_natAbs_le_pow M hM)

/-- Reducing an integer fraction can only reduce its numerator and denominator
magnitudes. The zero numerator is included. -/
theorem ratio_sizes_le (a b : ℤ) (hb : b ≠ 0) :
    ((a : ℚ) / b).num.natAbs.size ≤ a.natAbs.size ∧
    ((a : ℚ) / b).den.size ≤ b.natAbs.size := by
  have he : (a : ℚ) / b = Rat.divInt a b := by simp [Rat.divInt_eq_div]
  rw [he]
  constructor
  · by_cases ha : a = 0
    · simp [ha]
    · exact Nat.size_le_size (Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd a hb) ha)
  · apply Nat.size_le_size
    simpa using Int.natAbs_le_of_dvd_ne_zero (Rat.den_dvd a b) hb

section Samples

variable {ι : Type*} [Fintype ι] {s : ℕ}

theorem sampled_det_cast (v : ι → ℚ) (u : Fin s → Fin s → ι) :
    ((Matrix.det (fun i j => cleared v (u i j)) : ℤ) : ℚ) =
      (commonDen v : ℚ) ^ s * Matrix.det (fun i j => v (u i j)) := by
  rw [Int.cast_det]
  have he : (Matrix.map (fun i j => cleared v (u i j)) (fun z : ℤ => (z : ℚ))) =
      (commonDen v : ℚ) • (fun i j => v (u i j) : Matrix (Fin s) (Fin s) ℚ) := by
    ext i j
    exact cleared_cast v (u i j)
  rw [he, Matrix.det_smul]
  simp

/-- Both determinants use the same clearing factor, which cancels from their
ratio. Reduction then gives a bound on the actual canonical rational fields. -/
theorem det_ratio_sizes_le (v : ι → ℚ) (u w : Fin s → Fin s → ι)
    (hd : Matrix.det (fun i j => v (u i j)) ≠ 0) :
    let q := Matrix.det (fun i j => v (w i j)) / Matrix.det (fun i j => v (u i j))
    q.num.natAbs.size ≤ s * (2 * dataBits v + s.size) + 1 ∧
    q.den.size ≤ s * (2 * dataBits v + s.size) + 1 := by
  let a : ℤ := Matrix.det (fun i j => cleared v (w i j))
  let b : ℤ := Matrix.det (fun i j => cleared v (u i j))
  have hD : (commonDen v : ℚ) ≠ 0 := by exact_mod_cast (commonDen_pos v).ne'
  have hbq : (b : ℚ) ≠ 0 := by
    rw [show (b : ℚ) = _ from sampled_det_cast v u]
    exact mul_ne_zero (pow_ne_zero _ hD) hd
  have hb : b ≠ 0 := fun h => hbq (by rw [h]; simp)
  have he : (a : ℚ) / b =
      Matrix.det (fun i j => v (w i j)) / Matrix.det (fun i j => v (u i j)) := by
    rw [show (a : ℚ) = _ from sampled_det_cast v w,
      show (b : ℚ) = _ from sampled_det_cast v u]
    exact mul_div_mul_left _ _ (pow_ne_zero _ hD)
  dsimp only
  rw [← he]
  exact ⟨(ratio_sizes_le a b hb).1.trans
      (det_size_le _ (fun i j => cleared_natAbs_le v (w i j))),
    (ratio_sizes_le a b hb).2.trans
      (det_size_le _ (fun i j => cleared_natAbs_le v (u i j)))⟩

end Samples

/-- The indexed entries of the design and target; no deduplication occurs. -/
def inputData {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) :
    Fin r × Option (Fin d) → ℚ
  | (i, none) => y i
  | (i, some j) => A i j

/-- The bit-size conclusion for a genuine global minimizer, without full-rank,
nonempty-dimension, or distinct-row assumptions. -/
theorem exists_global_minimizer_bits (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) :
    ∃ β : Fin d → ℚ,
      (∀ β', loss p A y β ≤ loss p A y β') ∧
      ∀ j, (β j).num.natAbs.size ≤ A.rank * (2 * dataBits (inputData A y) + A.rank.size) + 1 ∧
        (β j).den.size ≤ A.rank * (2 * dataBits (inputData A y) + A.rank.size) + 1 := by
  classical
  obtain ⟨s, e, f, γ, hs, hd, hγ, hz, hmin⟩ := exists_global_minimizer_cramer p A y
  refine ⟨extend e γ, hmin, fun j => ?_⟩
  by_cases hj : j ∈ Set.range e
  · obtain ⟨k, rfl⟩ := hj
    rw [extend_apply, hγ k, ← hs]
    let u : Fin s → Fin s → Fin r × Option (Fin d) := fun i j => (f i, some (e j))
    let w : Fin s → Fin s → Fin r × Option (Fin d) :=
      fun i j => if j = k then (f i, none) else (f i, some (e j))
    have hw : (fun i j => inputData A y (w i j)) =
        (A.submatrix f e).updateCol k (y ∘ f) := by
      ext i j
      simp only [w, Matrix.updateCol_apply]
      split_ifs <;> rfl
    have h := det_ratio_sizes_le (inputData A y) u w hd
    have hu : (fun i j => inputData A y (u i j)) = A.submatrix f e := rfl
    simpa only [hw, hu] using h
  · rw [hz j hj]
    simp only [Rat.num_zero, Int.natAbs_zero, Nat.size_zero, Rat.den_zero, Nat.size_one]
    omega

#print axioms commonDen_le_pow
#print axioms cleared_cast
#print axioms cleared_natAbs_le
#print axioms det_natAbs_le_pow
#print axioms det_size_le
#print axioms ratio_sizes_le
#print axioms det_ratio_sizes_le
#print axioms exists_global_minimizer_bits

end PhdThesisLean.RationalWitnessBounds
