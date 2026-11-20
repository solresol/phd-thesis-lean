import PhdThesisLean.SmithCrossMinorFamily

/-! Original minors alone need not dominate entries at completed pair boundaries. -/

namespace PhdThesisLean.SmithOriginalMinorObstruction

open Matrix SmithTrace SmithReduction SmithSweep SmithMinorFamily

private def exampleInput : Matrix (Fin 2) (Fin 3) ℤ := !![2, 5, 5; 0, 5, 5]

private theorem minors (q : ℕ) : MinorBound exampleInput q 10 := by
  intro f g
  by_cases hf : Function.Injective f
  · have hq : q ≤ 2 := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
    interval_cases q
    · simp
    · rw [Matrix.det_fin_one]
      change (exampleInput (f 0) (g 0)).natAbs ≤ 10
      generalize f 0 = a
      generalize g 0 = b
      fin_cases a <;> fin_cases b <;> decide
    · rw [Matrix.det_fin_two]
      simp only [Matrix.submatrix_apply]
      generalize f 0 = a
      generalize f 1 = b
      generalize g 0 = c
      generalize g 1 = d
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide
  · obtain ⟨a,b,hab,hne⟩ := Function.not_injective_iff.mp hf
    rw [Matrix.det_zero_of_row_eq hne (by
      ext j
      exact congrArg (fun i => exampleInput i (g j)) hab)]
    decide

/-- Every original minor has magnitude at most ten, while a reached entry
at the end of the first complete pair has magnitude twenty. -/
theorem pair_boundary_exceeds_all_original_minors :
    ∃ A : Matrix (Fin 2) (Fin 3) ℤ, (∀ q, MinorBound A q 10) ∧
      ((cross (initial A) 0).S 1 2).natAbs = 20 := by
  refine ⟨exampleInput, minors, ?_⟩
  norm_num [cross, clearActiveRow, clearActiveColumn, sweepRows, SmithColumn.activeRows,
    List.finRange_succ, List.finRange_zero, reduceRows, SmithPivot.pivot, transposeState,
    initial, exampleInput, SmithPivot.gcdTrace, SmithPivot.pairStep, run, step,
    SmithRowOperations.rowAdd, colAdd, Matrix.cons_val, Nat.reduceLT]

#print axioms pair_boundary_exceeds_all_original_minors

end PhdThesisLean.SmithOriginalMinorObstruction
