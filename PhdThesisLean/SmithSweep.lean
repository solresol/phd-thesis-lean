import PhdThesisLean.SmithReduction

/-!
# Divisibility-aware active sweeps and progress across a complete pass

Each pair is reduced from the current entries, using exact division whenever
possible. A whole sweep either fixes the pivot row or strictly decreases a
nonzero pivot. After an active-column sweep followed by an active-row sweep,
both arms of the pivot are clear or its nonzero magnitude has decreased.
All integral maps and inverses are retained, including for empty rectangles.
This is one finite pass, not a recursive diagonalizer or a bit-cost theorem.
-/

namespace PhdThesisLean.SmithSweep

open Matrix SmithTrace SmithPivot SmithReduction SmithColumn SmithDecomposition SmithEncoding

variable {m n : ℕ}

/-- Visit the supplied rows, selecting every quotient from the updated matrix.
Occurrences of the pivot itself are skipped; repeated targets are permitted. -/
def sweepRows (Q : State m n) (r : Fin m) (j : Fin n) : List (Fin m) → State m n
  | [] => Q
  | s :: rows =>
      if h : r = s then sweepRows Q r j rows
      else sweepRows (reduceRows Q r s h j) r j rows

theorem sweepRows_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (r : Fin m) (j : Fin n) (rows : List (Fin m)) :
    Invariant A (sweepRows Q r j rows) := by
  induction rows generalizing Q with
  | nil => exact hQ
  | cons s rows ih =>
      simp only [sweepRows]
      split_ifs with h
      · exact ih hQ
      · exact ih (reduceRows_invariant hQ r s h j)

/-- Clearing is persistent even if the same target is visited again. -/
theorem sweepRows_clears (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (i : Fin m) (hir : i ≠ r)
    (hi : i ∈ rows ∨ Q.S i j = 0) :
    (sweepRows Q r j rows).S i j = 0 := by
  induction rows generalizing Q with
  | nil => exact hi.resolve_left (by simp)
  | cons s rows ih =>
      simp only [sweepRows]
      split_ifs with h
      · apply ih Q
        rcases hi with hmem | hzero
        · rcases List.mem_cons.mp hmem with heq | hmem
          · exact False.elim (hir (heq.trans h.symm))
          · exact Or.inl hmem
        · exact Or.inr hzero
      · apply ih (reduceRows Q r s h j)
        rcases hi with hmem | hzero
        · rcases List.mem_cons.mp hmem with heq | hmem
          · subst i
            exact Or.inr (reduceRows_correct Q r s h j).1
          · exact Or.inl hmem
        · right
          by_cases his : i = s
          · subst i
            exact (reduceRows_correct Q r s h j).1
          · rw [(reduceRows_correct Q r s h j).2.2 i j hir his, hzero]

theorem sweepRows_outside (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (i : Fin m) (hir : i ≠ r) (hi : i ∉ rows) :
    ∀ l, (sweepRows Q r j rows).S i l = Q.S i l := by
  induction rows generalizing Q with
  | nil => intro l; rfl
  | cons s rows ih =>
      have his : i ≠ s := fun h => hi (List.mem_cons.mpr (Or.inl h))
      have htail : i ∉ rows := fun h => hi (List.mem_cons_of_mem s h)
      simp only [sweepRows]
      split_ifs with h
      · exact ih Q htail
      · intro l
        rw [ih (reduceRows Q r s h j) htail l,
          (reduceRows_correct Q r s h j).2.2 i l hir his]

/-- A protected zero column is preserved on all the selected rows. -/
theorem sweepRows_preserves_zero (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (l : Fin n) (hr : Q.S r l = 0)
    (hrows : ∀ i ∈ rows, Q.S i l = 0) :
    (sweepRows Q r j rows).S r l = 0 ∧
      ∀ i ∈ rows, (sweepRows Q r j rows).S i l = 0 := by
  induction rows generalizing Q with
  | nil => exact ⟨hr, by simp⟩
  | cons s rows ih =>
      simp only [sweepRows]
      split_ifs with h
      · obtain ⟨hfirst, hrest⟩ := ih Q hr (fun i hi => hrows i (by simp [hi]))
        refine ⟨hfirst, ?_⟩
        intro i hi
        rcases List.mem_cons.mp hi with heq | hmem
        · simpa [heq, ← h] using hfirst
        · exact hrest i hmem
      · have hp := reduceRows_preserves_zero Q r s h j l hr (hrows s (by simp))
        have htail : ∀ i ∈ rows, (reduceRows Q r s h j).S i l = 0 := by
          intro i hi
          by_cases hir : i = r
          · simpa [hir] using hp.1
          · by_cases his : i = s
            · simpa [his] using hp.2
            · rw [(reduceRows_correct Q r s h j).2.2 i l hir his]
              exact hrows i (by simp [hi])
        obtain ⟨hfirst, hrest⟩ := ih (reduceRows Q r s h j) hp.1 htail
        refine ⟨hfirst, ?_⟩
        intro i hi
        rcases List.mem_cons.mp hi with heq | hmem
        · subst i
          by_cases hs : s ∈ rows
          · exact hrest s hs
          · rw [sweepRows_outside (reduceRows Q r s h j) r j rows s (Ne.symm h) hs l]
            exact hp.2
        · exact hrest i hmem

private theorem reduceRows_nonzero_le (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j : Fin n) (ha : Q.S r j ≠ 0) :
    (reduceRows Q r s h j).S r j ≠ 0 ∧
      ((reduceRows Q r s h j).S r j).natAbs ≤ (Q.S r j).natAbs := by
  have hg := (reduceRows_correct Q r s h j).2.1
  constructor
  · apply Int.natAbs_pos.mp
    rw [hg]
    exact Int.gcd_pos_of_ne_zero_left _ ha
  · rw [hg]
    exact Int.gcd_le_natAbs_left _ ha

/-- A nonzero pivot stays nonzero and its magnitude cannot increase. The
nonzero hypothesis is essential: a zero pivot may acquire a nonzero target. -/
theorem sweepRows_nonzero_le (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (ha : Q.S r j ≠ 0) :
    (sweepRows Q r j rows).S r j ≠ 0 ∧
      ((sweepRows Q r j rows).S r j).natAbs ≤ (Q.S r j).natAbs := by
  induction rows generalizing Q with
  | nil => exact ⟨ha, le_rfl⟩
  | cons s rows ih =>
      simp only [sweepRows]
      split_ifs with h
      · exact ih Q ha
      · obtain ⟨hn, hle⟩ := reduceRows_nonzero_le Q r s h j ha
        obtain ⟨hn', hle'⟩ := ih (reduceRows Q r s h j) hn
        exact ⟨hn', hle'.trans hle⟩

/-- Lift the local progress alternative across the entire finite sweep.
After a strict decrease, subsequent nonincreases cannot undo that progress. -/
theorem sweepRows_progress (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (ha : Q.S r j ≠ 0) :
    (∀ l, (sweepRows Q r j rows).S r l = Q.S r l) ∨
      ((sweepRows Q r j rows).S r j).natAbs < (Q.S r j).natAbs := by
  induction rows generalizing Q with
  | nil => exact Or.inl (fun _ => rfl)
  | cons s rows ih =>
      simp only [sweepRows]
      split_ifs with h
      · exact ih Q ha
      · have hn := (reduceRows_nonzero_le Q r s h j ha).1
        rcases reduceRows_progress Q r s h j ha with hfixed | hstrict
        · rcases ih (reduceRows Q r s h j) hn with htail | htail
          · exact Or.inl (fun l => (htail l).trans (hfixed l))
          · exact Or.inr (by simpa only [hfixed j] using htail)
        · exact Or.inr (lt_of_le_of_lt
            (sweepRows_nonzero_le (reduceRows Q r s h j) r j rows hn).2 hstrict)

/-- A total active-column pass, using the existing runtime row enumeration. -/
def clearActiveColumn (Q : State m n) (k : ℕ) : State m n :=
  if hr : k < m then
    if hc : k < n then sweepRows Q ⟨k, hr⟩ ⟨k, hc⟩ (activeRows m k)
    else Q
  else Q

theorem clearActiveColumn_of_missing (Q : State m n) (k : ℕ)
    (h : m ≤ k ∨ n ≤ k) : clearActiveColumn Q k = Q := by
  unfold clearActiveColumn
  split_ifs with hr hc
  · omega
  all_goals rfl

theorem clearActiveColumn_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (k : ℕ) : Invariant A (clearActiveColumn Q k) := by
  unfold clearActiveColumn
  split_ifs
  · exact sweepRows_invariant hQ _ _ _
  all_goals exact hQ

theorem clearActiveColumn_clears (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (i : Fin m) (hi : k < i.val) :
    (clearActiveColumn Q k).S i ⟨k, hc⟩ = 0 := by
  simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc]
  apply sweepRows_clears Q _ _ _ i
  · intro heq
    have := congrArg Fin.val heq
    simp only at this
    omega
  · exact Or.inl ((mem_activeRows i k).mpr hi)

theorem clearActiveColumn_nonzero_le (Q : State m n) (k : ℕ) (hr : k < m)
    (hc : k < n) (ha : Q.S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0) :
    (clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0 ∧
      ((clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs ≤
        (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs := by
  simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc]
  exact sweepRows_nonzero_le Q _ _ _ ha

/-- Earlier rows and columns stay fixed under the lower-left zero invariant. -/
theorem clearActiveColumn_prefix (Q : State m n) (k : ℕ)
    (hzero : ∀ (i : Fin m) (l : Fin n), k ≤ i.val → l.val < k → Q.S i l = 0)
    (i : Fin m) (l : Fin n) (hprefix : i.val < k ∨ l.val < k) :
    (clearActiveColumn Q k).S i l = Q.S i l := by
  unfold clearActiveColumn
  split_ifs with hr hc
  · by_cases hi : i.val < k
    · apply sweepRows_outside Q _ _ _ i
      · intro heq
        have := congrArg Fin.val heq
        simp only at this
        omega
      · simp only [mem_activeRows]
        omega
    · have hl : l.val < k := hprefix.resolve_left hi
      have hp := sweepRows_preserves_zero Q (⟨k, hr⟩ : Fin m) (⟨k, hc⟩ : Fin n)
        (activeRows m k) l (hzero _ l (by simp) hl)
        (fun a ha => hzero a l (Nat.le_of_lt ((mem_activeRows a k).mp ha)) hl)
      rw [hzero i l (by omega) hl]
      by_cases hik : i.val = k
      · have heq : i = (⟨k, hr⟩ : Fin m) := Fin.ext hik
        simpa [heq] using hp.1
      · exact hp.2 i ((mem_activeRows i k).mpr (by omega))
  all_goals rfl

/-- The column-operation pass is the very same row sweep on the transpose. -/
def clearActiveRow (Q : State m n) (k : ℕ) : State m n :=
  transposeState (clearActiveColumn (transposeState Q) k)

theorem clearActiveRow_of_missing (Q : State m n) (k : ℕ)
    (h : m ≤ k ∨ n ≤ k) : clearActiveRow Q k = Q := by
  unfold clearActiveRow
  rw [clearActiveColumn_of_missing _ k h.symm, transposeState_twice]

theorem clearActiveRow_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (k : ℕ) : Invariant A (clearActiveRow Q k) :=
  transposeState_invariant (clearActiveColumn_invariant (transposeState_invariant hQ) k)

theorem clearActiveRow_clears (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (j : Fin n) (hj : k < j.val) :
    (clearActiveRow Q k).S ⟨k, hr⟩ j = 0 :=
  clearActiveColumn_clears (transposeState Q) k hc hr j hj

theorem clearActiveRow_nonzero_le (Q : State m n) (k : ℕ) (hr : k < m)
    (hc : k < n) (ha : Q.S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0) :
    (clearActiveRow Q k).S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0 ∧
      ((clearActiveRow Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs ≤
        (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs :=
  clearActiveColumn_nonzero_le (transposeState Q) k hc hr ha

theorem clearActiveRow_progress (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (ha : Q.S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0) :
    (∀ i, (clearActiveRow Q k).S i ⟨k, hc⟩ = Q.S i ⟨k, hc⟩) ∨
      ((clearActiveRow Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs <
        (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs := by
  simpa only [clearActiveRow, clearActiveColumn, dite_eq_left hc, dite_eq_left hr,
    transposeState, Matrix.transpose_apply] using
    sweepRows_progress (transposeState Q) ⟨k, hc⟩ ⟨k, hr⟩ (activeRows n k) ha

theorem clearActiveRow_prefix (Q : State m n) (k : ℕ)
    (hzero : ∀ (i : Fin m) (l : Fin n), i.val < k → k ≤ l.val → Q.S i l = 0)
    (i : Fin m) (l : Fin n) (hprefix : i.val < k ∨ l.val < k) :
    (clearActiveRow Q k).S i l = Q.S i l :=
  clearActiveColumn_prefix (transposeState Q) k
    (fun j a hj ha => hzero a j ha hj) l i hprefix.symm

/-- One complete pair of active sweeps, with no externally supplied trace. -/
def cross (Q : State m n) (k : ℕ) : State m n :=
  clearActiveRow (clearActiveColumn Q k) k

theorem cross_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (k : ℕ) : Invariant A (cross Q k) :=
  clearActiveRow_invariant (clearActiveColumn_invariant hQ k) k

theorem cross_of_missing (Q : State m n) (k : ℕ) (h : m ≤ k ∨ n ≤ k) :
    cross Q k = Q := by
  rw [cross, clearActiveColumn_of_missing Q k h, clearActiveRow_of_missing Q k h]

theorem cross_nonzero_le (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (ha : Q.S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0) :
    (cross Q k).S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0 ∧
      ((cross Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs ≤
        (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs := by
  obtain ⟨hn, hle⟩ := clearActiveColumn_nonzero_le Q k hr hc ha
  obtain ⟨hn', hle'⟩ := clearActiveRow_nonzero_le (clearActiveColumn Q k) k hr hc hn
  exact ⟨hn', hle'.trans hle⟩

/-- A completed diagonal prefix is protected on both sides of the active block.
No nonzero pivot is required for this preservation result. -/
theorem cross_prefix (Q : State m n) (k : ℕ)
    (hlower : ∀ (i : Fin m) (j : Fin n), k ≤ i.val → j.val < k → Q.S i j = 0)
    (hupper : ∀ (i : Fin m) (j : Fin n), i.val < k → k ≤ j.val → Q.S i j = 0)
    (i : Fin m) (j : Fin n) (hprefix : i.val < k ∨ j.val < k) :
    (cross Q k).S i j = Q.S i j := by
  have hupper' : ∀ (a : Fin m) (b : Fin n), a.val < k → k ≤ b.val →
      (clearActiveColumn Q k).S a b = 0 := by
    intro a b ha hb
    rw [clearActiveColumn_prefix Q k hlower a b (Or.inl ha)]
    exact hupper a b ha hb
  rw [cross, clearActiveRow_prefix (clearActiveColumn Q k) k hupper' i j hprefix]
  exact clearActiveColumn_prefix Q k hlower i j hprefix

/-- The complete pass either isolates both active arms or strictly decreases
the original nonzero pivot. This is numeric descent, without a bit-step bound. -/
theorem cross_isolated_or_descend (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (ha : Q.S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0) :
    ((∀ i : Fin m, k < i.val → (cross Q k).S i ⟨k, hc⟩ = 0) ∧
      (∀ j : Fin n, k < j.val → (cross Q k).S ⟨k, hr⟩ j = 0)) ∨
      ((cross Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs <
        (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs := by
  obtain ⟨hn, hle⟩ := clearActiveColumn_nonzero_le Q k hr hc ha
  rcases clearActiveRow_progress (clearActiveColumn Q k) k hr hc hn with hfixed | hstrict
  · left
    constructor
    · intro i hi
      rw [cross, hfixed i]
      exact clearActiveColumn_clears Q k hr hc i hi
    · exact fun j hj => clearActiveRow_clears (clearActiveColumn Q k) k hr hc j hj
  · exact Or.inr (lt_of_lt_of_le hstrict hle)

/-- Store all five outputs in the existing dense binary-encoding contract.
The runtime control index has no new codec or machine-cost claim. -/
def crossDense (A : Dense) (k : ℕ) : Result A.rows A.cols :=
  (cross (initial A.toMatrix) k).result

theorem crossDense_equivalence (A : Dense) (k : ℕ) :
    let R := crossDense A k
    R.Uinv.matrix * R.U.matrix = 1 ∧ R.U.matrix * R.Uinv.matrix = 1 ∧
      R.V.matrix * R.Vinv.matrix = 1 ∧ R.Vinv.matrix * R.V.matrix = 1 ∧
      R.U.matrix * A.toMatrix * R.V.matrix = R.S.matrix := by
  have h := cross_invariant (initial_invariant A.toMatrix) k
  simpa only [crossDense, State.result, pack_matrix] using
    And.intro h.Uinv_U ⟨h.U_Uinv, h.V_Vinv, h.Vinv_V, h.transformed⟩

theorem crossDense_isolated_or_descend (A : Dense) (k : ℕ) (hr : k < A.rows)
    (hc : k < A.cols) (ha : A.toMatrix ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0) :
    ((∀ i : Fin A.rows, k < i.val → (crossDense A k).S.matrix i ⟨k, hc⟩ = 0) ∧
      (∀ j : Fin A.cols, k < j.val → (crossDense A k).S.matrix ⟨k, hr⟩ j = 0)) ∨
      ((crossDense A k).S.matrix ⟨k, hr⟩ ⟨k, hc⟩).natAbs <
        (A.toMatrix ⟨k, hr⟩ ⟨k, hc⟩).natAbs := by
  simpa only [crossDense, State.result, pack_matrix, initial] using
    cross_isolated_or_descend (initial A.toMatrix) k hr hc ha

theorem crossDense_prefix (A : Dense) (k : ℕ)
    (hlower : ∀ (i : Fin A.rows) (j : Fin A.cols),
      k ≤ i.val → j.val < k → A.toMatrix i j = 0)
    (hupper : ∀ (i : Fin A.rows) (j : Fin A.cols),
      i.val < k → k ≤ j.val → A.toMatrix i j = 0)
    (i : Fin A.rows) (j : Fin A.cols) (hprefix : i.val < k ∨ j.val < k) :
    (crossDense A k).S.matrix i j = A.toMatrix i j := by
  simpa only [crossDense, State.result, pack_matrix, initial] using
    cross_prefix (initial A.toMatrix) k hlower hupper i j hprefix

-- Exact division fixes the pivot row across a repeated-target sweep.
private abbrev divisibleInput : Dense := ⟨3, 2, [-2, 4, 6, 9, -4, 7], rfl⟩
example : (pack (sweepRows (initial divisibleInput.toMatrix) 0 0 [0, 1, 2, 1]).S).val.entries =
    [-2, 4, 0, 21, 0, -1] := by decide

-- Evaluator regression evidence, separate from the universal progress proof:
-- the first pass shrinks the pivot but needs a second pass to clear both arms.
private abbrev descentInput : Dense := ⟨2, 3, [6, 4, 0, 0, 6, 0], rfl⟩
/-- info: [-2, 0, 0, 6, -18, 0] -/
#guard_msgs in
#eval (crossDense descentInput 0).S.val.entries
/-- info: [-2, 0, 0, 0, -18, 0] -/
#guard_msgs in
#eval (cross (cross (initial descentInput.toMatrix) 0) 0).result.S.val.entries

-- A nondivisible rectangular case, including a nonempty protected prefix.
private abbrev prefixInput : Dense :=
  ⟨4, 3, [7, 0, 0, 0, 6, 4, 0, 0, 6, 0, 0, 0], rfl⟩
example : ∀ (i : Fin 4) (j : Fin 3), i.val < 1 ∨ j.val < 1 →
    (crossDense prefixInput 1).S.matrix i j = prefixInput.toMatrix i j := by
  have hlower : ∀ (i : Fin 4) (j : Fin 3),
      1 ≤ i.val → j.val < 1 → prefixInput.toMatrix i j = 0 := by decide
  have hupper : ∀ (i : Fin 4) (j : Fin 3),
      i.val < 1 → 1 ≤ j.val → prefixInput.toMatrix i j = 0 := by decide
  exact fun i j hp => crossDense_prefix prefixInput 1 hlower hupper i j hp

-- A zero pivot is processed but is deliberately outside nonzero descent.
private abbrev zeroPivotInput : Dense := ⟨1, 2, [0, 6], rfl⟩
example : (crossDense zeroPivotInput 0).S.val.entries = [6, 0] := by
  norm_num [crossDense, cross, clearActiveRow, clearActiveColumn, sweepRows,
    reduceRows, transposeState, initial, zeroPivotInput, Dense.toMatrix,
    activeRows, List.finRange_succ, pivot, gcdTrace, pairStep]
  decide

-- Totality and all inverse identities retain both empty orientations.
example : check (⟨0, 3, [], rfl⟩ : Dense).toMatrix
    (crossDense ⟨0, 3, [], rfl⟩ 0) = true := by decide
example : check (⟨3, 0, [], rfl⟩ : Dense).toMatrix
    (crossDense ⟨3, 0, [], rfl⟩ 0) = true := by decide
example : check (⟨0, 0, [], rfl⟩ : Dense).toMatrix
    (crossDense ⟨0, 0, [], rfl⟩ 0) = true := by decide
example : cross (initial prefixInput.toMatrix) 3 = initial prefixInput.toMatrix :=
  cross_of_missing _ 3 (Or.inr (by decide))

end PhdThesisLean.SmithSweep

#print axioms PhdThesisLean.SmithSweep.sweepRows
#print axioms PhdThesisLean.SmithSweep.sweepRows_invariant
#print axioms PhdThesisLean.SmithSweep.sweepRows_clears
#print axioms PhdThesisLean.SmithSweep.sweepRows_outside
#print axioms PhdThesisLean.SmithSweep.sweepRows_preserves_zero
#print axioms PhdThesisLean.SmithSweep.sweepRows_nonzero_le
#print axioms PhdThesisLean.SmithSweep.sweepRows_progress
#print axioms PhdThesisLean.SmithSweep.clearActiveColumn
#print axioms PhdThesisLean.SmithSweep.clearActiveColumn_of_missing
#print axioms PhdThesisLean.SmithSweep.clearActiveColumn_invariant
#print axioms PhdThesisLean.SmithSweep.clearActiveColumn_clears
#print axioms PhdThesisLean.SmithSweep.clearActiveColumn_nonzero_le
#print axioms PhdThesisLean.SmithSweep.clearActiveColumn_prefix
#print axioms PhdThesisLean.SmithSweep.clearActiveRow
#print axioms PhdThesisLean.SmithSweep.clearActiveRow_of_missing
#print axioms PhdThesisLean.SmithSweep.clearActiveRow_invariant
#print axioms PhdThesisLean.SmithSweep.clearActiveRow_clears
#print axioms PhdThesisLean.SmithSweep.clearActiveRow_nonzero_le
#print axioms PhdThesisLean.SmithSweep.clearActiveRow_progress
#print axioms PhdThesisLean.SmithSweep.clearActiveRow_prefix
#print axioms PhdThesisLean.SmithSweep.cross
#print axioms PhdThesisLean.SmithSweep.cross_invariant
#print axioms PhdThesisLean.SmithSweep.cross_of_missing
#print axioms PhdThesisLean.SmithSweep.cross_nonzero_le
#print axioms PhdThesisLean.SmithSweep.cross_prefix
#print axioms PhdThesisLean.SmithSweep.cross_isolated_or_descend
#print axioms PhdThesisLean.SmithSweep.crossDense
#print axioms PhdThesisLean.SmithSweep.crossDense_equivalence
#print axioms PhdThesisLean.SmithSweep.crossDense_isolated_or_descend
#print axioms PhdThesisLean.SmithSweep.crossDense_prefix
