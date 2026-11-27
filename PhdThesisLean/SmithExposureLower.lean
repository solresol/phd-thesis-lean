import PhdThesisLean.SmithMultiplierBudget

/-! A single Euclidean quotient can be copied into every exposed target. -/

namespace PhdThesisLean.SmithExposureLower

open SmithSweep SmithTrace SmithReduction SmithPivot SmithSweepBounds SmithPivotBounds
open SmithColumn SmithMultiplierBudget

/-- The first column is (2K+1,2), and every remaining column is (0,1). -/
def family (K n : ℕ) : Matrix (Fin 2) (Fin (n+1)) ℤ :=
  fun i j => if j = 0 then (if i = 0 then 2 * (K : ℤ) + 1 else 2)
             else (if i = 0 then 0 else 1)

private theorem first_trace (K n : ℕ) (hK : 0 < K) :
    columnTrace (initial (family K n)) 0 =
      pairStep 0 1 (by decide) (K : ℤ) ++ pairStep 0 1 (by decide) (-2) := by
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
  change reduceRowsTrace (initial (family K n)) 0 1 hr 0 ++ [] = _
  rw [List.append_nil]
  simp only [reduceRowsTrace, initial, family, ite_true,
    ite_eq_right (by decide : (1 : Fin 2) ≠ 0), hd, ite_false]
  rw [gcdTrace, dite_eq_right (by decide), hq, hm, gcdTrace, dite_eq_right (by decide)]
  have hz : -(2 : ℤ).tmod (-1) = 0 := by decide
  rw [hz, gcdTrace, dite_eq_left rfl, List.append_nil]
  rfl

/-- The first column sweep leaves pivot -1 and copies K into each target. -/
theorem turn_row (K n : ℕ) (hK : 0 < K) (j : Fin (n+1)) :
    (clearActiveColumn (initial (family K n)) 0).S 0 j =
      (if j = 0 then (-1 : ℤ) else K) := by
  rw [← columnTrace_run, first_trace K n hK, SmithPivot.run_append,
    (pairStep_rows _ _ _ (by decide : (0 : Fin 2) ≠ 1) _).1 j,
    (pairStep_rows _ _ _ (by decide : (0 : Fin 2) ≠ 1) _).2.1 j]
  by_cases hj : j = 0 <;> simp [initial, family, hj]
  ring

theorem turn_entry (K n : ℕ) (hK : 0 < K) (j : Fin (n+1)) (hj : j ≠ 0) :
    (clearActiveColumn (initial (family K n)) 0).S 0 j = K := by
  simp [turn_row _ _ hK, hj]

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

/-- The first perpendicular arm pays for n actual multipliers of size n+1. -/
theorem perpendicular_budget (n : ℕ) :
    budget (columnTrace (transposeState (clearActiveColumn
      (initial (family (2^n) n)) 0)) 0) = n * (n+2) := by
  let T := transposeState (clearActiveColumn (initial (family (2^n) n)) 0)
  have entry (i : Fin (n+1)) : T.S i 0 = if i = 0 then (-1 : ℤ) else ↑(2^n : ℕ) :=
    turn_row _ _ (by positivity) i
  have active : activeRows (n+1) 0 = (List.finRange n).map Fin.succ := by
    simp [activeRows, List.finRange_succ, List.filter_map, Function.comp_def]
  change budget (sweepRowsTrace T 0 0 (activeRows (n+1) 0)) = _
  rw [active, divisible_sweep_budget]
  · simp [List.map_map, Function.comp_def, entry, Nat.size_pow, List.map_const']
  · exact (List.nodup_finRange n).map (Fin.succ_injective n)
  · simp
  · intro s hs
    simp [entry]

/-- Exact multiplier budget of the first computed column/row pair. -/
theorem first_cross_budget (n : ℕ) :
    budget (crossTrace (initial (family (2^n) n)) 0) = n^2 + 3*n + 17 := by
  rw [crossTrace, budget_append, transpose_budget, perpendicular_budget, first_trace _ _ (by positivity),
    budget_append]
  have htwo : Nat.size 2 = 2 := rfl
  simp [pairStep, budget, coefficient, Nat.size_pow, htwo]
  ring

#print axioms perpendicular_budget
#print axioms first_cross_budget
#print axioms turn_row
#print axioms no_linear_turn_bound
#print axioms turn_width
#print axioms input_length
#print axioms turn_entry

end PhdThesisLean.SmithExposureLower
