import PhdThesisLean.SmithPivot

/-!
# An executable active-column sweep

Choose pair pivots from the current entries to clear an entire active column.
Earlier rows are fixed, and common zero columns of the active rows are
preserved. All transformations and inverses stay integral. The total stored
entry point also handles absent rows/columns. This is one controller pass;
it does not diagonalize a matrix or bound coefficient growth or machine time.
-/

namespace PhdThesisLean.SmithColumn

open Matrix SmithTrace SmithPivot SmithDecomposition SmithEncoding

variable {m n : ℕ}

/-- Visit a finite list of rows, computing each pivot from the updated state.
An occurrence of the pivot row is skipped; repeated target rows are harmless.
The active-column entry point below supplies its own list of eligible rows. -/
def sweep (Q : State m n) (r : Fin m) (j : Fin n) : List (Fin m) → State m n
  | [] => Q
  | s :: rows =>
      if h : r = s then sweep Q r j rows
      else sweep (pivot Q r s h j) r j rows

theorem sweep_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (r : Fin m) (j : Fin n) (rows : List (Fin m)) :
    Invariant A (sweep Q r j rows) := by
  induction rows generalizing Q with
  | nil => exact hQ
  | cons s rows ih =>
      simp only [sweep]
      split_ifs with h
      · exact ih hQ
      · exact ih (pivot_invariant hQ r s h j)

/-- A cleared nonpivot row stays cleared even if it is visited again. -/
private theorem pivot_preserves_clear (Q : State m n) (r s : Fin m)
    (h : r ≠ s) (j : Fin n) (i : Fin m) (hir : i ≠ r) (hi : Q.S i j = 0) :
    (pivot Q r s h j).S i j = 0 := by
  by_cases his : i = s
  · subst i
    exact (pivot_correct Q r s h j).1
  · rw [(pivot_correct Q r s h j).2.2 i j hir his, hi]

/-- Every visited nonpivot row is cleared; zeros present before the sweep
also remain zero. No distinctness or nonzero-entry assumption is needed. -/
theorem sweep_clears (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (i : Fin m) (hir : i ≠ r)
    (hi : i ∈ rows ∨ Q.S i j = 0) :
    (sweep Q r j rows).S i j = 0 := by
  induction rows generalizing Q with
  | nil => exact hi.resolve_left (by simp)
  | cons s rows ih =>
      simp only [sweep]
      split_ifs with h
      · apply ih Q
        rcases hi with hmem | hzero
        · left
          rcases List.mem_cons.mp hmem with heq | hmem
          · exact False.elim (hir (heq.trans h.symm))
          · exact hmem
        · exact Or.inr hzero
      · apply ih (pivot Q r s h j)
        rcases hi with hmem | hzero
        · rcases List.mem_cons.mp hmem with heq | hmem
          · right
            subst i
            exact (pivot_correct Q r s h j).1
          · exact Or.inl hmem
        · exact Or.inr (pivot_preserves_clear Q r s h j i hir hzero)

/-- Every row other than the pivot and listed targets is unchanged. -/
theorem sweep_outside (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (i : Fin m) (hir : i ≠ r) (hi : i ∉ rows) :
    ∀ l, (sweep Q r j rows).S i l = Q.S i l := by
  induction rows generalizing Q with
  | nil => intro l; rfl
  | cons s rows ih =>
      have his : i ≠ s := fun h => hi (List.mem_cons.mpr (Or.inl h))
      have htail : i ∉ rows := fun h => hi (List.mem_cons_of_mem s h)
      simp only [sweep]
      split_ifs with h
      · exact ih Q htail
      · intro l
        rw [ih (pivot Q r s h j) htail l,
          (pivot_correct Q r s h j).2.2 i l hir his]

/-- A protected column stays zero on the pivot and every eligible target.
Unlike outside-row preservation, this covers the pivot row itself. -/
theorem sweep_preserves_zero (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (l : Fin n) (hr : Q.S r l = 0)
    (hrows : ∀ i ∈ rows, Q.S i l = 0) :
    (sweep Q r j rows).S r l = 0 ∧
      ∀ i ∈ rows, (sweep Q r j rows).S i l = 0 := by
  induction rows generalizing Q with
  | nil => exact ⟨hr, by simp⟩
  | cons s rows ih =>
      simp only [sweep]
      split_ifs with h
      · obtain ⟨hfirst, hrest⟩ := ih Q hr (fun i hi => hrows i (by simp [hi]))
        refine ⟨hfirst, ?_⟩
        intro i hi
        rcases List.mem_cons.mp hi with heq | hmem
        · simpa [heq, ← h] using hfirst
        · exact hrest i hmem
      · have hp := gcdTrace_preserves_zero r s h (Q.S r j) (Q.S s j) Q l
          hr (hrows s (by simp))
        change (pivot Q r s h j).S r l = 0 ∧
          (pivot Q r s h j).S s l = 0 at hp
        have htail : ∀ i ∈ rows, (pivot Q r s h j).S i l = 0 := by
          intro i hi
          by_cases hir : i = r
          · simpa [hir] using hp.1
          · by_cases his : i = s
            · simpa [his] using hp.2
            · rw [(pivot_correct Q r s h j).2.2 i l hir his]
              exact hrows i (by simp [hi])
        obtain ⟨hfirst, hrest⟩ := ih (pivot Q r s h j) hp.1 htail
        refine ⟨hfirst, ?_⟩
        intro i hi
        rcases List.mem_cons.mp hi with heq | hmem
        · subst i
          by_cases hs : s ∈ rows
          · exact hrest s hs
          · rw [sweep_outside (pivot Q r s h j) r j rows s (Ne.symm h) hs l]
            exact hp.2
        · exact hrest i hmem

/-- Runtime row selection: visit exactly the rows strictly below `k`. -/
def activeRows (m k : ℕ) : List (Fin m) :=
  (List.finRange m).filter (fun i => k < i.val)

@[simp]
theorem mem_activeRows (i : Fin m) (k : ℕ) :
    i ∈ activeRows m k ↔ k < i.val := by
  simp [activeRows]

/-- One total controller pass, including rectangular and empty base cases. -/
def clearColumn (Q : State m n) (k : ℕ) : State m n :=
  if hr : k < m then
    if hc : k < n then sweep Q ⟨k, hr⟩ ⟨k, hc⟩ (activeRows m k)
    else Q
  else Q

theorem clearColumn_of_missing (Q : State m n) (k : ℕ)
    (h : m ≤ k ∨ n ≤ k) : clearColumn Q k = Q := by
  unfold clearColumn
  split_ifs with hr hc
  · omega
  all_goals rfl

theorem clearColumn_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (k : ℕ) : Invariant A (clearColumn Q k) := by
  unfold clearColumn
  split_ifs
  · exact sweep_invariant hQ _ _ _
  all_goals exact hQ

/-- Every entry strictly below an existing diagonal position is cleared. -/
theorem clearColumn_clears (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (i : Fin m) (hi : k < i.val) :
    (clearColumn Q k).S i ⟨k, hc⟩ = 0 := by
  simp only [clearColumn, dite_eq_left hr, dite_eq_left hc]
  apply sweep_clears Q _ _ _ i
  · intro heq
    have := congrArg Fin.val heq
    simp only at this
    omega
  · exact Or.inl ((mem_activeRows i k).mpr hi)

/-- Earlier rows and columns are fixed, provided active rows already vanish
in the earlier columns. This is the protected-prefix controller invariant. -/
theorem clearColumn_prefix (Q : State m n) (k : ℕ)
    (hzero : ∀ (i : Fin m) (l : Fin n), k ≤ i.val → l.val < k → Q.S i l = 0)
    (i : Fin m) (l : Fin n) (hprefix : i.val < k ∨ l.val < k) :
    (clearColumn Q k).S i l = Q.S i l := by
  unfold clearColumn
  split_ifs with hr hc
  · by_cases hi : i.val < k
    · apply sweep_outside Q _ _ _ i
      · intro heq
        have := congrArg Fin.val heq
        simp only at this
        omega
      · simp only [mem_activeRows]
        omega
    · have hl : l.val < k := hprefix.resolve_left hi
      have hp := sweep_preserves_zero Q (⟨k, hr⟩ : Fin m) (⟨k, hc⟩ : Fin n)
        (activeRows m k) l (hzero _ l (by simp) hl)
        (fun a ha => hzero a l (Nat.le_of_lt ((mem_activeRows a k).mp ha)) hl)
      rw [hzero i l (by omega) hl]
      by_cases hik : i.val = k
      · have heq : i = (⟨k, hr⟩ : Fin m) := Fin.ext hik
        simpa [heq] using hp.1
      · exact hp.2 i ((mem_activeRows i k).mpr (by omega))
  all_goals rfl

/-- Advance the zero lower-left active-block boundary by one position.
This is a column-elimination invariant; entries above the diagonal may remain. -/
theorem clearColumn_next_zero (Q : State m n) (k : ℕ)
    (hzero : ∀ (i : Fin m) (l : Fin n), k ≤ i.val → l.val < k → Q.S i l = 0) :
    ∀ (i : Fin m) (l : Fin n), k + 1 ≤ i.val → l.val < k + 1 →
      (clearColumn Q k).S i l = 0 := by
  intro i l hi hl
  by_cases hlt : l.val < k
  · rw [clearColumn_prefix Q k hzero i l (Or.inr hlt)]
    exact hzero i l (by omega) hlt
  · have heq : l.val = k := by omega
    have hr : k < m := by omega
    have hc : k < n := by omega
    have hindex : l = (⟨k, hc⟩ : Fin n) := Fin.ext heq
    rw [hindex]
    exact clearColumn_clears Q k hr hc i (by omega)

/-- Materialize all five computed matrices using the existing dense format.
Only the active position is supplied; eligible rows and quotients are computed. -/
def clearColumnDense (A : Dense) (k : ℕ) : Result A.rows A.cols :=
  (clearColumn (initial A.toMatrix) k).result

theorem clearColumnDense_equivalence (A : Dense) (k : ℕ) :
    let R := clearColumnDense A k
    R.Uinv.matrix * R.U.matrix = 1 ∧ R.U.matrix * R.Uinv.matrix = 1 ∧
      R.V.matrix * R.Vinv.matrix = 1 ∧ R.Vinv.matrix * R.V.matrix = 1 ∧
      R.U.matrix * A.toMatrix * R.V.matrix = R.S.matrix := by
  have h := clearColumn_invariant (initial_invariant A.toMatrix) k
  simpa only [clearColumnDense, State.result, pack_matrix] using
    And.intro h.Uinv_U ⟨h.U_Uinv, h.V_Vinv, h.Vinv_V, h.transformed⟩

theorem clearColumnDense_clears (A : Dense) (k : ℕ) (hr : k < A.rows)
    (hc : k < A.cols) (i : Fin A.rows) (hi : k < i.val) :
    (clearColumnDense A k).S.matrix i ⟨k, hc⟩ = 0 := by
  simpa only [clearColumnDense, State.result, pack_matrix] using
    clearColumn_clears (initial A.toMatrix) k hr hc i hi

theorem clearColumnDense_prefix (A : Dense) (k : ℕ)
    (hzero : ∀ (i : Fin A.rows) (l : Fin A.cols),
      k ≤ i.val → l.val < k → A.toMatrix i l = 0)
    (i : Fin A.rows) (l : Fin A.cols) (hprefix : i.val < k ∨ l.val < k) :
    (clearColumnDense A k).S.matrix i l = A.toMatrix i l := by
  simpa only [clearColumnDense, State.result, pack_matrix, initial] using
    clearColumn_prefix (initial A.toMatrix) k hzero i l hprefix

/-- For at most one column this single pass already satisfies the weak
decomposition contract, including every zero-column input and `0 × 1`. -/
theorem clearColumnDense_valid_of_cols_le_one (A : Dense) (hc : A.cols ≤ 1) :
    Valid A.toMatrix (clearColumnDense A 0) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := clearColumnDense_equivalence A 0
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  intro i j hij
  have hj : j.val = 0 := by omega
  have hrow : 0 < A.rows := by omega
  have hcol : 0 < A.cols := by omega
  have hi : 0 < i.val := by omega
  have heq : j = (⟨0, hcol⟩ : Fin A.cols) := Fin.ext hj
  rw [heq]
  exact clearColumnDense_clears A 0 hrow hcol i hi

-- Kernel-checked specialization of the protected-prefix and clearing theorems.
private abbrev activeInput : Dense :=
  ⟨4, 3, [7, 11, -2, 0, 30, 5, 0, 21, 4, 0, 7, 2], rfl⟩
example :
    (∀ l : Fin 3, (clearColumnDense activeInput 1).S.matrix 0 l =
      activeInput.toMatrix 0 l) ∧
    ((clearColumnDense activeInput 1).S.matrix 2 1 = 0) ∧
    ((clearColumnDense activeInput 1).S.matrix 3 1 = 0) ∧
    (∀ i : Fin 4, (clearColumnDense activeInput 1).S.matrix i 0 =
      activeInput.toMatrix i 0) := by
  have hz : ∀ (i : Fin 4) (l : Fin 3),
      1 ≤ i.val → l.val < 1 → activeInput.toMatrix i l = 0 := by decide
  refine ⟨?_, clearColumnDense_clears activeInput 1 (by decide) (by decide) 2 (by decide),
    clearColumnDense_clears activeInput 1 (by decide) (by decide) 3 (by decide), ?_⟩
  · intro l
    exact clearColumnDense_prefix activeInput 1 hz 0 l (Or.inl (by decide))
  · intro i
    exact clearColumnDense_prefix activeInput 1 hz i 0 (Or.inr (by decide))

private abbrev tallInput : Dense := ⟨3, 1, [0, -30, 21], rfl⟩
example : check tallInput.toMatrix (clearColumnDense tallInput 0) = true :=
  (check_eq_true_iff _ _).mpr (clearColumnDense_valid_of_cols_le_one _ (by decide))

-- These evaluator outputs are regression evidence, separate from the theorems.
-- They do not construct proofs or establish coefficient/runtime bounds.
/-- info: [-3, 0, 0] -/
#guard_msgs in
#eval (clearColumnDense tallInput 0).S.val.entries

private abbrev zeroColumnInput : Dense := ⟨3, 2, [0, 4, 0, -5, 0, 6], rfl⟩
/-- info: [0, 4, 0, -5, 0, 6] -/
#guard_msgs in
#eval (clearColumnDense zeroColumnInput 0).S.val.entries

example : check (⟨0, 3, [], rfl⟩ : Dense).toMatrix
    (clearColumnDense ⟨0, 3, [], rfl⟩ 0) = true := by decide
example : check (⟨3, 0, [], rfl⟩ : Dense).toMatrix
    (clearColumnDense ⟨3, 0, [], rfl⟩ 0) = true := by decide
example : check (⟨0, 0, [], rfl⟩ : Dense).toMatrix
    (clearColumnDense ⟨0, 0, [], rfl⟩ 0) = true := by decide
example : clearColumn (initial activeInput.toMatrix) 3 =
    initial activeInput.toMatrix := clearColumn_of_missing _ _ (Or.inr (by decide))

#print axioms sweep
#print axioms sweep_invariant
#print axioms sweep_clears
#print axioms sweep_outside
#print axioms sweep_preserves_zero
#print axioms clearColumn
#print axioms clearColumn_of_missing
#print axioms clearColumn_invariant
#print axioms clearColumn_clears
#print axioms clearColumn_prefix
#print axioms clearColumn_next_zero
#print axioms clearColumnDense
#print axioms clearColumnDense_equivalence
#print axioms clearColumnDense_clears
#print axioms clearColumnDense_prefix
#print axioms clearColumnDense_valid_of_cols_le_one

end PhdThesisLean.SmithColumn
