import PhdThesisLean.SmithTrace

/-!
# A terminating integer Euclidean row pivot

Compute an addition trace from two entries, rather than accepting a supplied
trace. A quotient reduction and a determinant-one signed swap replace `(a,b)`
by `(b,-(a.tmod b))`, using division truncated toward zero. Strict remainder
descent proves termination. The output
pivot has magnitude `gcd a b`; its sign is not normalized. This is a local
pivot primitive, not a diagonalization algorithm or a bit-complexity theorem.
-/

namespace PhdThesisLean.SmithPivot

open Matrix SmithTrace SmithRowOperations SmithDecomposition SmithEncoding

variable {m n : ℕ}

/-- Quotient subtraction followed by `(x,y) ↦ (y,-x)`, using only additions. -/
def pairStep (r s : Fin m) (h : r ≠ s) (q : ℤ) : List (Op m n) :=
  [.row r s h (-q), .row r s h 1, .row s r h.symm (-1), .row r s h 1]

theorem pairStep_rows (Q : State m n) (r s : Fin m) (h : r ≠ s) (q : ℤ) :
    (∀ j, (run Q (pairStep r s h q)).S r j = Q.S s j) ∧
      (∀ j, (run Q (pairStep r s h q)).S s j = -(Q.S r j - q * Q.S s j)) ∧
      (∀ i j, i ≠ r → i ≠ s → (run Q (pairStep r s h q)).S i j = Q.S i j) := by
  constructor
  · intro j
    simp [pairStep, run, step, rowAdd, h, h.symm]
    ring
  · constructor
    · intro j
      simp [pairStep, run, step, rowAdd, h.symm]
      ring
    · intro i j hir his
      simp [pairStep, run, step, rowAdd, hir, his]

theorem remainder_descent (a b : ℤ) (hb : b ≠ 0) :
    (-(a.tmod b)).natAbs < b.natAbs := by
  simpa only [Int.natAbs_neg, Int.natAbs_tmod] using
    Nat.mod_lt a.natAbs (Int.natAbs_pos.mpr hb)

/-- Executable trace selection for one pair of rows and one pivot column.
The scalar parameters are the two current entries, not an assumed result. -/
def gcdTrace (r s : Fin m) (h : r ≠ s) (a b : ℤ) : List (Op m n) :=
  if hb : b = 0 then []
  else pairStep r s h (a.tdiv b) ++ gcdTrace r s h b (-(a.tmod b))
termination_by b.natAbs
decreasing_by exact remainder_descent a b hb

theorem run_append (Q : State m n) (xs ys : List (Op m n)) :
    run Q (xs ++ ys) = run (run Q xs) ys := by
  induction xs generalizing Q with
  | nil => rfl
  | cons op xs ih => exact ih (step Q op)

/-- The generated trace clears the second entry and preserves the gcd magnitude.
All other rows are fixed, regardless of rectangular shape or rank. -/
theorem gcdTrace_correct (r s : Fin m) (h : r ≠ s) (a b : ℤ)
    (Q : State m n) (j : Fin n) (ha : Q.S r j = a) (hb : Q.S s j = b) :
    let B := (run Q (gcdTrace r s h a b)).S
    B s j = 0 ∧ (B r j).natAbs = Int.gcd a b ∧
      ∀ i k, i ≠ r → i ≠ s → B i k = Q.S i k := by
  rw [gcdTrace]
  split_ifs with hzero
  · simp [run, ha, hb, hzero]
  · rw [run_append]
    have hp := pairStep_rows Q r s h (a.tdiv b)
    have hfirst : (run Q (pairStep r s h (a.tdiv b))).S r j = b := by
      simpa [hb] using hp.1 j
    have hsecond : (run Q (pairStep r s h (a.tdiv b))).S s j = -(a.tmod b) := by
      rw [hp.2.1 j, ha, hb, Int.tmod_def, mul_comm b]
    obtain ⟨hclear, hgcd, hrest⟩ :=
      gcdTrace_correct r s h b (-(a.tmod b)) _ j hfirst hsecond
    refine ⟨hclear, ?_, ?_⟩
    · rw [hgcd, Int.gcd_neg, Int.gcd_comm b, Int.tmod_def,
        Int.gcd_sub_mul_left_left]
    · intro i k hir his
      rw [hrest i k hir his, hp.2.2 i k hir his]
termination_by b.natAbs
decreasing_by exact remainder_descent a b hzero

/-- Common zero columns of the selected rows remain zero after this pivot.
This is needed before using the primitive inside a recursive active block. -/
theorem gcdTrace_preserves_zero (r s : Fin m) (h : r ≠ s) (a b : ℤ)
    (Q : State m n) (k : Fin n) (hr : Q.S r k = 0) (hs : Q.S s k = 0) :
    (run Q (gcdTrace r s h a b)).S r k = 0 ∧
      (run Q (gcdTrace r s h a b)).S s k = 0 := by
  rw [gcdTrace]
  split_ifs with hb
  · exact ⟨hr, hs⟩
  · rw [run_append]
    have hp := pairStep_rows Q r s h (a.tdiv b)
    apply gcdTrace_preserves_zero r s h b (-(a.tmod b)) _ k
    · rw [hp.1 k, hs]
    · rw [hp.2.1 k, hr, hs]
      ring
termination_by b.natAbs
decreasing_by exact remainder_descent a b hb

/-- Compute one pair pivot from the current matrix entries. -/
def pivot (Q : State m n) (r s : Fin m) (h : r ≠ s) (j : Fin n) : State m n :=
  run Q (gcdTrace r s h (Q.S r j) (Q.S s j))

theorem pivot_correct (Q : State m n) (r s : Fin m) (h : r ≠ s) (j : Fin n) :
    (pivot Q r s h j).S s j = 0 ∧
      ((pivot Q r s h j).S r j).natAbs = Int.gcd (Q.S r j) (Q.S s j) ∧
      ∀ i k, i ≠ r → i ≠ s → (pivot Q r s h j).S i k = Q.S i k :=
  gcdTrace_correct r s h _ _ Q j rfl rfl

theorem pivot_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (r s : Fin m) (h : r ≠ s) (j : Fin n) :
    Invariant A (pivot Q r s h j) :=
  run_invariant hQ _

/-- Materialize the pivot's five matrices in the existing finite dense format.
The row/column indices are supplied; selecting a whole diagonalization is open. -/
def pivotDense (A : Dense) (r s : Fin A.rows) (h : r ≠ s) (j : Fin A.cols) :
    Result A.rows A.cols :=
  executeDense A (gcdTrace r s h (A.toMatrix r j) (A.toMatrix s j))

theorem pivotDense_correct (A : Dense) (r s : Fin A.rows) (h : r ≠ s)
    (j : Fin A.cols) :
    let B := (pivotDense A r s h j).S.matrix
    B s j = 0 ∧ (B r j).natAbs = Int.gcd (A.toMatrix r j) (A.toMatrix s j) ∧
      ∀ i k, i ≠ r → i ≠ s → B i k = A.toMatrix i k := by
  simpa only [pivotDense, executeDense, execute, State.result, pack_matrix, pivot, initial]
    using pivot_correct (initial A.toMatrix) r s h j

theorem pivotDense_equivalence (A : Dense) (r s : Fin A.rows) (h : r ≠ s)
    (j : Fin A.cols) :
    let R := pivotDense A r s h j
    R.Uinv.matrix * R.U.matrix = 1 ∧ R.U.matrix * R.Uinv.matrix = 1 ∧
      R.V.matrix * R.Vinv.matrix = 1 ∧ R.Vinv.matrix * R.V.matrix = 1 ∧
      R.U.matrix * A.toMatrix * R.V.matrix = R.S.matrix :=
  execute_equivalence A.toMatrix _

theorem pivotDense_preserves_zero (A : Dense) (r s : Fin A.rows) (h : r ≠ s)
    (j k : Fin A.cols) (hr : A.toMatrix r k = 0) (hs : A.toMatrix s k = 0) :
    (pivotDense A r s h j).S.matrix r k = 0 ∧
      (pivotDense A r s h j).S.matrix s k = 0 := by
  simpa only [pivotDense, executeDense, execute, State.result, pack_matrix] using
    gcdTrace_preserves_zero r s h (A.toMatrix r j) (A.toMatrix s j)
      (initial A.toMatrix) k hr hs

-- Kernel-checked cases: signed inputs, rectangular/rank-deficient input,
-- common zero columns, a nonselected row, and both zero/nonzero base cases.
private abbrev rectangularInput : Dense := ⟨3, 2, [30, 0, 21, 0, 7, 5], rfl⟩
example : (pivotDense rectangularInput (0 : Fin 3) (1 : Fin 3) (by decide)
    (0 : Fin 2)).S.val.entries = [-3, 0, 0, 0, 7, 5] := by
  simp only [pivotDense, executeDense]
  norm_num [rectangularInput, Dense.toMatrix, gcdTrace, pairStep]
  decide
private abbrev negativeInput : Dense := ⟨2, 1, [-100, -99], rfl⟩
example : (pivotDense negativeInput (0 : Fin 2) (1 : Fin 2) (by decide)
    (0 : Fin 1)).S.val.entries = [1, 0] := by
  simp only [pivotDense, executeDense]
  norm_num [negativeInput, Dense.toMatrix, gcdTrace, pairStep]
  decide
example : (gcdTrace (n := 1) (0 : Fin 2) 1 (by decide) (-100) (-99)).length = 8 := by
  norm_num [gcdTrace, pairStep]
example : check negativeInput.toMatrix
    (pivotDense negativeInput (0 : Fin 2) (1 : Fin 2) (by decide) (0 : Fin 1)) = true := by
  simp only [pivotDense, executeDense]
  norm_num [negativeInput, Dense.toMatrix, gcdTrace, pairStep]
  decide
example : (gcdTrace (n := 1) (0 : Fin 2) 1 (by decide) (-7) 0).length = 0 := by
  norm_num [gcdTrace]
private abbrev zeroInput : Dense := ⟨2, 1, [0, 0], rfl⟩
example : check zeroInput.toMatrix
    (pivotDense zeroInput (0 : Fin 2) (1 : Fin 2) (by decide) (0 : Fin 1)) = true := by
  simp only [pivotDense, executeDense]
  norm_num [zeroInput, Dense.toMatrix, gcdTrace]
  decide
private abbrev zeroPivotInput : Dense := ⟨2, 1, [0, 6], rfl⟩
example : (pivotDense zeroPivotInput (0 : Fin 2) (1 : Fin 2) (by decide)
    (0 : Fin 1)).S.val.entries = [6, 0] := by
  simp only [pivotDense, executeDense]
  norm_num [zeroPivotInput, Dense.toMatrix, gcdTrace, pairStep]
  decide

#print axioms pairStep_rows
#print axioms remainder_descent
#print axioms gcdTrace
#print axioms gcdTrace_correct
#print axioms gcdTrace_preserves_zero
#print axioms pivot_correct
#print axioms pivot_invariant
#print axioms pivotDense
#print axioms pivotDense_correct
#print axioms pivotDense_equivalence
#print axioms pivotDense_preserves_zero

end PhdThesisLean.SmithPivot
