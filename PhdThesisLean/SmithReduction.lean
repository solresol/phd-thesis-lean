import PhdThesisLean.SmithColumn

/-!
# Divisibility-aware integer pivot reduction

Clear a divisible entry by changing only its target row. Otherwise use the
existing Euclidean pivot: a nonzero pivot then strictly decreases in magnitude.
The transposed operation gives the same alternative for columns, so a row
reduction that disturbs a cleared pivot column must strictly decrease the pivot.
These are local controller invariants, not a complete diagonalizer or a global
coefficient-growth, operation-count or encoded-machine bound.
-/

namespace PhdThesisLean.SmithReduction

open Matrix SmithTrace SmithPivot SmithRowOperations SmithDecomposition SmithEncoding

variable {m n : ℕ}

/-- Exchange the two integral transformations, reversing products by transpose.
Both inverse matrices are retained; this works for every rectangular shape. -/
def transposeState (Q : State m n) : State n m :=
  ⟨Q.V.transpose, Q.Vinv.transpose, Q.U.transpose, Q.Uinv.transpose, Q.S.transpose⟩

@[simp]
theorem transposeState_twice (Q : State m n) :
    transposeState (transposeState Q) = Q := by cases Q; rfl

theorem transposeState_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) : Invariant A.transpose (transposeState Q) := by
  constructor
  · simpa only [transposeState, transpose_mul, transpose_one] using
      congrArg Matrix.transpose hQ.V_Vinv
  · simpa only [transposeState, transpose_mul, transpose_one] using
      congrArg Matrix.transpose hQ.Vinv_V
  · simpa only [transposeState, transpose_mul, transpose_one] using
      congrArg Matrix.transpose hQ.Uinv_U
  · simpa only [transposeState, transpose_mul, transpose_one] using
      congrArg Matrix.transpose hQ.U_Uinv
  · simpa only [transposeState, transpose_mul, Matrix.mul_assoc] using
      congrArg Matrix.transpose hQ.transformed

/-- Clear row `s` at column `j`. Exact division changes only the target row;
the nondivisible case reuses the checked terminating Euclidean pivot.
The divisible branch includes `(0,0)` and uses truncation toward zero. -/
def reduceRows (Q : State m n) (r s : Fin m) (h : r ≠ s) (j : Fin n) : State m n :=
  if Q.S r j ∣ Q.S s j then
    step Q (.row s r h.symm (-(Q.S s j).tdiv (Q.S r j)))
  else pivot Q r s h j

theorem reduceRows_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (r s : Fin m) (h : r ≠ s) (j : Fin n) :
    Invariant A (reduceRows Q r s h j) := by
  unfold reduceRows
  split_ifs
  · exact step_invariant hQ _
  · exact pivot_invariant hQ r s h j

/-- Clearing and gcd magnitude hold without a nonzero pivot hypothesis.
Every row outside the selected pair is fixed. -/
theorem reduceRows_correct (Q : State m n) (r s : Fin m) (h : r ≠ s) (j : Fin n) :
    (reduceRows Q r s h j).S s j = 0 ∧
      ((reduceRows Q r s h j).S r j).natAbs = Int.gcd (Q.S r j) (Q.S s j) ∧
      ∀ i l, i ≠ r → i ≠ s → (reduceRows Q r s h j).S i l = Q.S i l := by
  unfold reduceRows
  split_ifs with hd
  · refine ⟨?_, ?_, ?_⟩
    · simp [step, rowAdd, neg_mul, Int.tdiv_mul_cancel hd]
    · simp only [step, rowAdd, ite_eq_right h]
      exact (Int.gcd_eq_natAbs_left_iff_dvd.mpr hd).symm
    · intro i l _ his
      simp only [step, rowAdd, ite_eq_right his]
  · exact pivot_correct Q r s h j

/-- In the divisible case the entire pivot row stays fixed, including its sign.
An unconditional gcd pivot need not have this property. -/
theorem reduceRows_pivot_of_dvd (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j : Fin n) (hd : Q.S r j ∣ Q.S s j) :
    ∀ l, (reduceRows Q r s h j).S r l = Q.S r l := by
  intro l
  simp [reduceRows, hd, step, rowAdd, h]

/-- Common zeros survive in both selected rows. -/
theorem reduceRows_preserves_zero (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j l : Fin n) (hr : Q.S r l = 0) (hs : Q.S s l = 0) :
    (reduceRows Q r s h j).S r l = 0 ∧ (reduceRows Q r s h j).S s l = 0 := by
  unfold reduceRows
  split_ifs
  · simp [step, rowAdd, h, hr, hs]
  · exact gcdTrace_preserves_zero r s h _ _ Q l hr hs

/-- A nonzero pivot strictly decreases exactly in the nondivisible branch. -/
theorem reduceRows_strict (Q : State m n) (r s : Fin m) (h : r ≠ s) (j : Fin n)
    (ha : Q.S r j ≠ 0) (hd : ¬ Q.S r j ∣ Q.S s j) :
    ((reduceRows Q r s h j).S r j).natAbs < (Q.S r j).natAbs := by
  rw [(reduceRows_correct Q r s h j).2.1]
  exact lt_of_le_of_ne (Int.gcd_le_natAbs_left _ ha)
    (fun heq => hd (Int.gcd_eq_natAbs_left_iff_dvd.mp heq))

/-- Local progress alternative for an alternating controller. This is magnitude
descent, not a logarithmic step bound or a bound on the other matrix entries. -/
theorem reduceRows_progress (Q : State m n) (r s : Fin m) (h : r ≠ s) (j : Fin n)
    (ha : Q.S r j ≠ 0) :
    (∀ l, (reduceRows Q r s h j).S r l = Q.S r l) ∨
      ((reduceRows Q r s h j).S r j).natAbs < (Q.S r j).natAbs := by
  by_cases hd : Q.S r j ∣ Q.S s j
  · exact Or.inl (reduceRows_pivot_of_dvd Q r s h j hd)
  · exact Or.inr (reduceRows_strict Q r s h j ha hd)

/-- Column reduction is the same checked integer operation on the transpose.
Here `r` is the pivot column, `s` the target column and `i` the selected row. -/
def reduceCols (Q : State m n) (r s : Fin n) (h : r ≠ s) (i : Fin m) : State m n :=
  transposeState (reduceRows (transposeState Q) r s h i)

theorem reduceCols_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (r s : Fin n) (h : r ≠ s) (i : Fin m) :
    Invariant A (reduceCols Q r s h i) := by
  exact transposeState_invariant (reduceRows_invariant (transposeState_invariant hQ) r s h i)

theorem reduceCols_correct (Q : State m n) (r s : Fin n) (h : r ≠ s) (i : Fin m) :
    (reduceCols Q r s h i).S i s = 0 ∧
      ((reduceCols Q r s h i).S i r).natAbs = Int.gcd (Q.S i r) (Q.S i s) ∧
      ∀ l j, j ≠ r → j ≠ s → (reduceCols Q r s h i).S l j = Q.S l j := by
  obtain ⟨hc, hg, ho⟩ := reduceRows_correct (transposeState Q) r s h i
  exact ⟨hc, hg, fun l j => ho j l⟩

theorem reduceCols_preserves_zero (Q : State m n) (r s : Fin n) (h : r ≠ s)
    (i l : Fin m) (hr : Q.S l r = 0) (hs : Q.S l s = 0) :
    (reduceCols Q r s h i).S l r = 0 ∧ (reduceCols Q r s h i).S l s = 0 :=
  reduceRows_preserves_zero (transposeState Q) r s h i l hr hs

/-- If a column reduction can disturb an already cleared pivot column, its
nonzero pivot must decrease. This rules out constant-pivot alternating cycles
locally; a complete active-block controller and its global bounds remain open. -/
theorem reduceCols_clear_or_descend (Q : State m n) (r s : Fin n) (h : r ≠ s)
    (i : Fin m) (ha : Q.S i r ≠ 0)
    (hclear : ∀ l, l ≠ i → Q.S l r = 0) :
    (∀ l, l ≠ i → (reduceCols Q r s h i).S l r = 0) ∨
      ((reduceCols Q r s h i).S i r).natAbs < (Q.S i r).natAbs := by
  rcases reduceRows_progress (transposeState Q) r s h i ha with hfixed | hstrict
  · left
    intro l hl
    change (reduceRows (transposeState Q) r s h i).S r l = 0
    rw [hfixed l]
    exact hclear l hl
  · exact Or.inr hstrict

/-- Total runtime-indexed reduction of one column entry. Missing indices and
the pivot itself are no-ops, including both empty orientations. -/
def reduceAtColumn (Q : State m n) (k target : ℕ) : State m n :=
  if hr : k < m then
    if hc : k < n then
      if hs : target < m then
        if h : k ≠ target then
          reduceRows Q ⟨k, hr⟩ ⟨target, hs⟩ (Fin.ne_of_val_ne h) ⟨k, hc⟩
        else Q
      else Q
    else Q
  else Q

theorem reduceAtColumn_of_missing (Q : State m n) (k target : ℕ)
    (h : m ≤ k ∨ n ≤ k ∨ m ≤ target ∨ k = target) :
    reduceAtColumn Q k target = Q := by
  unfold reduceAtColumn
  split_ifs with hr hc hs hne
  · omega
  all_goals rfl

theorem reduceAtColumn_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (k target : ℕ) : Invariant A (reduceAtColumn Q k target) := by
  unfold reduceAtColumn
  split_ifs
  · exact reduceRows_invariant hQ _ _ _ _
  all_goals exact hQ

theorem reduceAtColumn_clears (Q : State m n) (k target : ℕ)
    (hr : k < m) (hc : k < n) (hs : target < m) (h : k ≠ target) :
    (reduceAtColumn Q k target).S ⟨target, hs⟩ ⟨k, hc⟩ = 0 := by
  simp only [reduceAtColumn, dite_eq_left hr, dite_eq_left hc, dite_eq_left hs, dite_eq_left h]
  exact (reduceRows_correct Q _ _ _ _).1

/-- Total row-entry reduction, using the same guards on the transposed shape. -/
def reduceAtRow (Q : State m n) (k target : ℕ) : State m n :=
  transposeState (reduceAtColumn (transposeState Q) k target)

theorem reduceAtRow_of_missing (Q : State m n) (k target : ℕ)
    (h : n ≤ k ∨ m ≤ k ∨ n ≤ target ∨ k = target) :
    reduceAtRow Q k target = Q := by
  unfold reduceAtRow
  rw [reduceAtColumn_of_missing _ k target h, transposeState_twice]

theorem reduceAtRow_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (k target : ℕ) : Invariant A (reduceAtRow Q k target) :=
  transposeState_invariant (reduceAtColumn_invariant (transposeState_invariant hQ) k target)

theorem reduceAtRow_clears (Q : State m n) (k target : ℕ)
    (hr : k < m) (hc : k < n) (hs : target < n) (h : k ≠ target) :
    (reduceAtRow Q k target).S ⟨k, hr⟩ ⟨target, hs⟩ = 0 :=
  reduceAtColumn_clears (transposeState Q) k target hc hr hs h

/-- Stored input/output in the existing unary-dimension, signed-binary format.
`acrossRow = true` selects a row-entry (column-operation) reduction. Control
indices are additional data with no claimed codec, size or machine-time bound. -/
def reduceDense (A : Dense) (acrossRow : Bool) (k target : ℕ) : Result A.rows A.cols :=
  (if acrossRow then reduceAtRow (initial A.toMatrix) k target
    else reduceAtColumn (initial A.toMatrix) k target).result

theorem reduceDense_equivalence (A : Dense) (acrossRow : Bool) (k target : ℕ) :
    let R := reduceDense A acrossRow k target
    R.Uinv.matrix * R.U.matrix = 1 ∧ R.U.matrix * R.Uinv.matrix = 1 ∧
      R.V.matrix * R.Vinv.matrix = 1 ∧ R.Vinv.matrix * R.V.matrix = 1 ∧
      R.U.matrix * A.toMatrix * R.V.matrix = R.S.matrix := by
  have h : Invariant A.toMatrix
      (if acrossRow then reduceAtRow (initial A.toMatrix) k target
        else reduceAtColumn (initial A.toMatrix) k target) := by
    split_ifs
    · exact reduceAtRow_invariant (initial_invariant A.toMatrix) k target
    · exact reduceAtColumn_invariant (initial_invariant A.toMatrix) k target
  simpa only [reduceDense, State.result, pack_matrix] using
    And.intro h.Uinv_U ⟨h.U_Uinv, h.V_Vinv, h.Vinv_V, h.transformed⟩

-- Kernel-checked counterexample to unmodified alternating gcd sweeps: the
-- transformed matrix returns after two passes, while off-diagonal zeros move.
private abbrev cycleInput : Dense := ⟨2, 2, [2, 2, 0, 2], rfl⟩
private def naiveRow (Q : State 2 2) : State 2 2 :=
  transposeState (pivot (transposeState Q) 0 1 (by decide) 0)
example : (pack (naiveRow (initial cycleInput.toMatrix)).S).val.entries =
    [2, 0, 2, 2] := by
  norm_num [naiveRow, pivot, transposeState, initial, cycleInput, Dense.toMatrix,
    gcdTrace, pairStep, run, step, rowAdd, colAdd]
  decide
example : (pack (pivot (naiveRow (initial cycleInput.toMatrix))
    0 1 (by decide) 0).S).val.entries = [2, 2, 0, 2] := by
  norm_num [naiveRow, pivot, transposeState, initial, cycleInput, Dense.toMatrix,
    gcdTrace, pairStep, run, step, rowAdd, colAdd]
  decide

-- The exact-division branch clears that same example without reintroducing
-- its lower-left entry. These finite specializations do not replace the proofs.
example : check cycleInput.toMatrix (reduceDense cycleInput true 0 1) = true := by
  decide
private abbrev signedInput : Dense := ⟨1, 2, [-2, 6], rfl⟩
example : (reduceDense signedInput true 0 1).S.val.entries = [-2, 0] := by decide
private abbrev nondivisibleInput : Dense := ⟨1, 2, [6, 4], rfl⟩
example : (reduceDense nondivisibleInput true 0 1).S.val.entries = [-2, 0] := by
  norm_num [reduceDense, reduceAtRow, reduceAtColumn, reduceRows, transposeState,
    initial, nondivisibleInput, Dense.toMatrix, pivot, gcdTrace, pairStep]
  decide
private abbrev zeroPivotInput : Dense := ⟨1, 2, [0, 6], rfl⟩
example : (reduceDense zeroPivotInput true 0 1).S.val.entries = [6, 0] := by
  norm_num [reduceDense, reduceAtRow, reduceAtColumn, reduceRows, transposeState,
    initial, zeroPivotInput, Dense.toMatrix, pivot, gcdTrace, pairStep]
  decide
example : check (⟨0, 3, [], rfl⟩ : Dense).toMatrix
    (reduceDense ⟨0, 3, [], rfl⟩ true 0 1) = true := by decide
example : check (⟨3, 0, [], rfl⟩ : Dense).toMatrix
    (reduceDense ⟨3, 0, [], rfl⟩ false 0 1) = true := by decide
example : check (⟨0, 0, [], rfl⟩ : Dense).toMatrix
    (reduceDense ⟨0, 0, [], rfl⟩ true 0 1) = true := by decide
example : reduceAtRow (initial cycleInput.toMatrix) 4 1 =
    initial cycleInput.toMatrix := reduceAtRow_of_missing _ _ _ (Or.inl (by decide))
example : reduceAtColumn (initial cycleInput.toMatrix) 0 0 =
    initial cycleInput.toMatrix := reduceAtColumn_of_missing _ _ _ (by omega)

#print axioms transposeState_invariant
#print axioms reduceRows
#print axioms reduceRows_invariant
#print axioms reduceRows_correct
#print axioms reduceRows_pivot_of_dvd
#print axioms reduceRows_preserves_zero
#print axioms reduceRows_strict
#print axioms reduceRows_progress
#print axioms reduceCols_invariant
#print axioms reduceCols_correct
#print axioms reduceCols_preserves_zero
#print axioms reduceCols_clear_or_descend
#print axioms reduceAtColumn_of_missing
#print axioms reduceAtColumn_invariant
#print axioms reduceAtColumn_clears
#print axioms reduceAtRow_of_missing
#print axioms reduceAtRow_invariant
#print axioms reduceAtRow_clears
#print axioms reduceDense
#print axioms reduceDense_equivalence

end PhdThesisLean.SmithReduction
