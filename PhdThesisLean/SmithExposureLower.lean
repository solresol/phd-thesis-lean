import PhdThesisLean.SmithSweep

/-! A single Euclidean quotient can be copied into every exposed target. -/

namespace PhdThesisLean.SmithExposureLower

open SmithSweep SmithTrace SmithReduction SmithPivot

/-- The first column is (2K+1,2), and every remaining column is (0,1). -/
def family (K n : ℕ) : Matrix (Fin 2) (Fin (n+1)) ℤ :=
  fun i j => if j = 0 then (if i = 0 then 2 * (K : ℤ) + 1 else 2)
             else (if i = 0 then 0 else 1)

/-- Clearing the first column simultaneously puts K in each remaining
position of the pivot row. The number of copied entries is arbitrary. -/
theorem turn_entry (K n : ℕ) (hK : 0 < K) (j : Fin (n+1)) (hj : j ≠ 0) :
    (clearActiveColumn (initial (family K n)) 0).S 0 j = K := by
  let Q := initial (family K n)
  have hd : ¬ (2 * (K : ℤ) + 1) ∣ 2 := by
    intro h
    have := Int.le_of_dvd (by decide : (0:ℤ) < 2) h
    omega
  have hq : (2 * (K : ℤ) + 1).tdiv 2 = K := by
    rw [Int.tdiv_eq_ediv_of_nonneg] <;> omega
  have hm : (2 * (K : ℤ) + 1).tmod 2 = 1 := by
    rw [Int.tmod_def, hq]
    ring
  have hr : (0 : Fin 2) ≠ 1 := by decide
  change (reduceRows Q 0 1 hr 0).S 0 j = _
  simp only [reduceRows, Q, initial, family, ite_true, ite_eq_right (by decide : (1 : Fin 2) ≠ 0),
    hd, ite_false, pivot]
  rw [gcdTrace, dite_eq_right (by decide), hq, hm, gcdTrace, dite_eq_right (by decide)]
  have hz : -(2 : ℤ).tmod (-1) = 0 := by decide
  rw [hz, gcdTrace, dite_eq_left rfl, List.append_nil, run_append,
      (pairStep_rows _ _ _ hr _).1 j, (pairStep_rows _ _ _ hr _).2.1 j]
  simp [family, hj]

/-- With K = 2^n, the n actual targets expose n(n+1) magnitude bits. -/
theorem turn_width (n : ℕ) :
    (∑ j : Fin n, ((clearActiveColumn (initial (family (2^n) n)) 0).S 0 j.succ).natAbs.size) =
      n * (n+1) := by
  simp [turn_entry _ _ (by positivity : 0 < 2^n) _ (Fin.succ_ne_zero _), Nat.size_pow]

/-- Exact cost of the same input, including both dimension headers and every
signed field. Only the first field has width growing with n. -/
theorem input_length (n : ℕ) :
    (SmithEncoding.encode (pack (family (2^n) n)).val).length = 9*n+17 := by
  let cost (z : ℤ) := 2 * z.natAbs.size + 2
  rw [SmithEncoding.encode_length]
  simp only [pack, List.map_ofFn, Function.comp_def,
    LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size, List.sum_ofFn]
  change 2 + (n+1) + 2 + (∑ k, cost (family (2^n) n (finProdFinEquiv.symm k).1
    (finProdFinEquiv.symm k).2)) = _
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, Fin.sum_univ_two]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hcast : (2 * (2 : ℤ)^n + 1).natAbs = Nat.bit true (2^n) := by
    change (2 * (2 : ℤ)^n + 1).natAbs = 2 * (2 : ℕ)^n + 1
    exact_mod_cast (Int.natAbs_natCast (2 * (2 : ℕ)^n + 1))
  have hsize : (2 * (2 : ℤ)^n + 1).natAbs.size = n + 2 := by
    rw [hcast, Nat.size_bit (by simp [Nat.bit]), Nat.size_pow]
  simp [family, cost, hsize]
  have : Nat.size 2 = 2 := rfl
  omega

/-- No constant multiple of the original wire length pays for even the
first perpendicular arm on all rectangular inputs. -/
theorem no_linear_turn_bound (C : ℕ) :
    ∃ n : ℕ, C * (SmithEncoding.encode (pack (family (2^n) n)).val).length <
      ∑ j : Fin n, ((clearActiveColumn (initial (family (2^n) n)) 0).S 0 j.succ).natAbs.size := by
  refine ⟨26 * (C+1), ?_⟩
  rw [input_length, turn_width]
  nlinarith

#print axioms no_linear_turn_bound
#print axioms turn_width
#print axioms input_length
#print axioms turn_entry

end PhdThesisLean.SmithExposureLower
