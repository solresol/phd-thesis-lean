import PhdThesisLean.SmithCrossMinorFamily

/-! A fixed pivot decrease can accompany unbounded entry amplification at
the second sweep pair of a single diagonal stage. -/

namespace PhdThesisLean.SmithRepeatedPairGrowth

open Matrix SmithTrace SmithReduction SmithSweep

private def family (z : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![4, 2, 0; 0, 1, z; 0, 2*z, 0]

private def middle (z : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2, 0, 0; 1, 2, z; 2*z, 4*z, 0]

private theorem first_pair (z : ℤ) :
    (cross (initial (family z)) 0).S = middle z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cross, clearActiveRow, clearActiveColumn, sweepRows, SmithColumn.activeRows,
      List.finRange_succ, List.finRange_zero, reduceRows, SmithPivot.pivot, transposeState,
      initial, family, middle, SmithPivot.gcdTrace, SmithPivot.pairStep, run, step,
      SmithRowOperations.rowAdd, colAdd, Matrix.cons_val, Nat.reduceLT]
  ring

private theorem second_pair (z : ℤ) (Q : State 3 3) (h : Q.S = middle z) :
    (cross Q 0).S 0 0 = 1 ∧ (cross Q 0).S 2 2 = -2*z^2 := by
  obtain ⟨u, ui, v, vi, s⟩ := Q
  change s = _ at h
  subst s
  constructor <;>
    norm_num [cross, clearActiveRow, clearActiveColumn, sweepRows, SmithColumn.activeRows,
      List.finRange_succ, List.finRange_zero, reduceRows, SmithPivot.pivot, transposeState,
      middle, SmithPivot.gcdTrace, SmithPivot.pairStep, run, step, SmithRowOperations.rowAdd,
      colAdd, Matrix.cons_val, Nat.reduceLT]
  ring

/-- After the first pair the pivot is 2 and its column still needs clearing.
For any proposed height multiplier K, the next pair takes the pivot to 1 and
produces an entry larger in magnitude than K times every incoming entry. -/
theorem second_pair_unbounded_amplification (K : ℕ) :
    ∃ A : Matrix (Fin 3) (Fin 3) ℤ,
      let Q := cross (initial A) 0
      Q.S 0 0 = 2 ∧ Q.S 1 0 = 1 ∧ (cross Q 0).S 0 0 = 1 ∧
        ∀ i j, (K : ℤ) * |Q.S i j| < |(cross Q 0).S 2 2| := by
  let z : ℤ := 2 * (K : ℤ) + 1
  have hz : 1 ≤ z := by dsimp [z]; omega
  refine ⟨family z, ?_⟩
  dsimp only
  obtain ⟨hp, he⟩ := second_pair z _ (first_pair z)
  refine ⟨?_, ?_, hp, ?_⟩
  · rw [first_pair]; rfl
  · rw [first_pair]; rfl
  intro i j
  rw [he, first_pair]
  have hentry : |middle z i j| ≤ 4*z := by
    apply abs_le.mpr
    fin_cases i <;> fin_cases j <;> norm_num [middle, Matrix.cons_val] <;> omega
  have hk : 0 ≤ (K : ℤ) := by positivity
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hentry hk)
  rw [abs_mul, abs_of_nonneg (sq_nonneg z)]
  norm_num
  dsimp [z]
  nlinarith [sq_nonneg (K : ℤ)]

#print axioms second_pair_unbounded_amplification

end PhdThesisLean.SmithRepeatedPairGrowth
