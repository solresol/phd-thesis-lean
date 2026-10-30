import PhdThesisLean.SmithSweep

/-!
# Terminating isolation of one active diagonal position

One unmeasured sweep pair seeds a possibly zero pivot. A zero result already
has both active arms clear; a nonzero result supports recursion by strict
natural-magnitude descent. Every operation retains integral transformations
and both inverses. Completed prefixes are protected under the two zero-block
invariants. This isolates one position, without a full diagonalizer, global
coefficient-growth bound, polynomial operation count or encoded machine.
-/

namespace PhdThesisLean.SmithIsolation

open Matrix SmithTrace SmithReduction SmithColumn SmithSweep SmithDecomposition SmithEncoding

variable {m n : ℕ}

/-- A sweep whose resulting pivot is zero was entirely idle. This is stronger
than clearing: all five matrices are unchanged, including both inverses. -/
theorem sweepRows_eq_of_zero (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (hz : (sweepRows Q r j rows).S r j = 0) :
    sweepRows Q r j rows = Q := by
  induction rows generalizing Q with
  | nil => rfl
  | cons s rows ih =>
      simp only [sweepRows] at hz ⊢
      split_ifs at hz ⊢ with h
      · exact ih Q hz
      · have htail := ih (reduceRows Q r s h j) hz
        have hp : (reduceRows Q r s h j).S r j = 0 := by rw [← htail]; exact hz
        have hg := (reduceRows_correct Q r s h j).2.1
        rw [hp, Int.natAbs_zero] at hg
        have ha : Q.S r j = 0 := by
          by_contra ha
          have := Int.gcd_pos_of_ne_zero_left (Q.S s j) ha
          omega
        have hb : Q.S s j = 0 := by
          simpa [ha] using hg.symm
        rw [htail]
        simp only [reduceRows, ha, hb, dvd_zero, ite_true, Int.zero_tdiv, neg_zero, step]
        have hu : SmithRowOperations.rowAdd Q.U s r 0 = Q.U := by
          funext i l
          simp [SmithRowOperations.rowAdd]
        have hui : colAdd Q.Uinv r s 0 = Q.Uinv := by
          funext i l
          simp [colAdd]
        have hs : SmithRowOperations.rowAdd Q.S s r 0 = Q.S := by
          funext i l
          simp [SmithRowOperations.rowAdd]
        rw [hu, hui, hs]

theorem clearActiveRow_eq_of_zero (Q : State m n) (k : ℕ) (hr : k < m)
    (hc : k < n) (hz : (clearActiveRow Q k).S ⟨k, hr⟩ ⟨k, hc⟩ = 0) :
    clearActiveRow Q k = Q := by
  have hz' : (sweepRows (transposeState Q) ⟨k, hc⟩ ⟨k, hr⟩
      (activeRows n k)).S ⟨k, hc⟩ ⟨k, hr⟩ = 0 := by
    simpa only [clearActiveRow, clearActiveColumn, dite_eq_left hc,
      dite_eq_left hr, transposeState, Matrix.transpose_apply] using hz
  simp only [clearActiveRow, clearActiveColumn, dite_eq_left hc, dite_eq_left hr,
    sweepRows_eq_of_zero _ _ _ _ hz', transposeState_twice]

/-- A seeding pass either produces a nonzero pivot or has already isolated a
zero pivot. No nonzero initial entry or active-block selection is assumed. -/
theorem cross_isolated_of_zero (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (hz : (cross Q k).S ⟨k, hr⟩ ⟨k, hc⟩ = 0) :
    (∀ i : Fin m, k < i.val → (cross Q k).S i ⟨k, hc⟩ = 0) ∧
      (∀ j : Fin n, k < j.val → (cross Q k).S ⟨k, hr⟩ j = 0) := by
  have hfixed := clearActiveRow_eq_of_zero (clearActiveColumn Q k) k hr hc hz
  constructor
  · intro i hi
    rw [cross, hfixed]
    exact clearActiveColumn_clears Q k hr hc i hi
  · exact fun j hj => clearActiveRow_clears (clearActiveColumn Q k) k hr hc j hj

/-- Both arms strictly beyond the active diagonal position are zero. This is
the weak diagonalization condition, without signs or a divisibility chain. -/
def Isolated (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n) : Prop :=
  (∀ i : Fin m, k < i.val → Q.S i ⟨k, hc⟩ = 0) ∧
    (∀ j : Fin n, k < j.val → Q.S ⟨k, hr⟩ j = 0)

instance (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n) :
    Decidable (Isolated Q k hr hc) := inferInstanceAs (Decidable (_ ∧ _))

/-- Iterate complete passes only after a nonzero pivot is available. The
measure is its numeric magnitude; no polynomial bound in binary bits follows. -/
def isolateNonzero (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (ha : Q.S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0) : State m n :=
  if _h : Isolated (cross Q k) k hr hc then cross Q k
  else isolateNonzero (cross Q k) k hr hc (cross_nonzero_le Q k hr hc ha).1
termination_by (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs
decreasing_by exact (cross_isolated_or_descend Q k hr hc ha).resolve_left _h

theorem isolateNonzero_isolated (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (ha : Q.S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0) :
    Isolated (isolateNonzero Q k hr hc ha) k hr hc := by
  rw [isolateNonzero]
  split_ifs with h
  · exact h
  · exact isolateNonzero_isolated (cross Q k) k hr hc (cross_nonzero_le Q k hr hc ha).1
termination_by (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs
decreasing_by exact (cross_isolated_or_descend Q k hr hc ha).resolve_left h

theorem isolateNonzero_invariant {A : Matrix (Fin m) (Fin n) ℤ} (Q : State m n)
    (hQ : Invariant A Q) (k : ℕ) (hr : k < m) (hc : k < n)
    (ha : Q.S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0) :
    Invariant A (isolateNonzero Q k hr hc ha) := by
  rw [isolateNonzero]
  split_ifs with h
  · exact cross_invariant hQ k
  · exact isolateNonzero_invariant (cross Q k) (cross_invariant hQ k) k hr hc
      (cross_nonzero_le Q k hr hc ha).1
termination_by (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs
decreasing_by exact (cross_isolated_or_descend Q k hr hc ha).resolve_left h

theorem isolateNonzero_prefix (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (ha : Q.S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0)
    (hlower : ∀ (i : Fin m) (j : Fin n), k ≤ i.val → j.val < k → Q.S i j = 0)
    (hupper : ∀ (i : Fin m) (j : Fin n), i.val < k → k ≤ j.val → Q.S i j = 0)
    (i : Fin m) (j : Fin n) (hprefix : i.val < k ∨ j.val < k) :
    (isolateNonzero Q k hr hc ha).S i j = Q.S i j := by
  rw [isolateNonzero]
  split_ifs with h
  · exact cross_prefix Q k hlower hupper i j hprefix
  · have hlower' : ∀ (a : Fin m) (b : Fin n), k ≤ a.val → b.val < k →
        (cross Q k).S a b = 0 := by
      intro a b ha hb
      rw [cross_prefix Q k hlower hupper a b (Or.inr hb)]
      exact hlower a b ha hb
    have hupper' : ∀ (a : Fin m) (b : Fin n), a.val < k → k ≤ b.val →
        (cross Q k).S a b = 0 := by
      intro a b ha hb
      rw [cross_prefix Q k hlower hupper a b (Or.inl ha)]
      exact hupper a b ha hb
    rw [isolateNonzero_prefix (cross Q k) k hr hc (cross_nonzero_le Q k hr hc ha).1
      hlower' hupper' i j hprefix]
    exact cross_prefix Q k hlower hupper i j hprefix
termination_by (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs
decreasing_by exact (cross_isolated_or_descend Q k hr hc ha).resolve_left h

/-- Total pivot isolation. One pass seeds zero pivots; a zero outcome is already
isolated, while a nonzero outcome enters the descending controller. Missing
positions, including empty rectangles, return the original five matrices. -/
def isolate (Q : State m n) (k : ℕ) : State m n :=
  if hr : k < m then
    if hc : k < n then
      if hz : (cross Q k).S ⟨k, hr⟩ ⟨k, hc⟩ = 0 then cross Q k
      else isolateNonzero (cross Q k) k hr hc hz
    else Q
  else Q

theorem isolate_of_missing (Q : State m n) (k : ℕ) (h : m ≤ k ∨ n ≤ k) :
    isolate Q k = Q := by
  unfold isolate
  split_ifs with hr hc hz
  all_goals first | omega | rfl

theorem isolate_isolated (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n) :
    Isolated (isolate Q k) k hr hc := by
  simp only [isolate, dite_eq_left hr, dite_eq_left hc]
  split_ifs with hz
  · exact cross_isolated_of_zero Q k hr hc hz
  · exact isolateNonzero_isolated (cross Q k) k hr hc hz

theorem isolate_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (k : ℕ) : Invariant A (isolate Q k) := by
  unfold isolate
  split_ifs
  · exact cross_invariant hQ k
  · exact isolateNonzero_invariant _ (cross_invariant hQ k) _ _ _ _
  all_goals exact hQ

theorem isolate_prefix (Q : State m n) (k : ℕ)
    (hlower : ∀ (i : Fin m) (j : Fin n), k ≤ i.val → j.val < k → Q.S i j = 0)
    (hupper : ∀ (i : Fin m) (j : Fin n), i.val < k → k ≤ j.val → Q.S i j = 0)
    (i : Fin m) (j : Fin n) (hprefix : i.val < k ∨ j.val < k) :
    (isolate Q k).S i j = Q.S i j := by
  unfold isolate
  split_ifs with hr hc hz
  · exact cross_prefix Q k hlower hupper i j hprefix
  · have hlower' : ∀ (a : Fin m) (b : Fin n), k ≤ a.val → b.val < k →
        (cross Q k).S a b = 0 := by
      intro a b ha hb
      rw [cross_prefix Q k hlower hupper a b (Or.inr hb)]
      exact hlower a b ha hb
    have hupper' : ∀ (a : Fin m) (b : Fin n), a.val < k → k ≤ b.val →
        (cross Q k).S a b = 0 := by
      intro a b ha hb
      rw [cross_prefix Q k hlower hupper a b (Or.inl ha)]
      exact hupper a b ha hb
    rw [isolateNonzero_prefix _ k hr hc hz hlower' hupper' i j hprefix]
    exact cross_prefix Q k hlower hupper i j hprefix
  all_goals rfl

/-- Isolation advances both zero-block boundaries. This is the invariant needed
by a later recursion over diagonal positions, including a zero isolated pivot. -/
theorem isolate_next_zero (Q : State m n) (k : ℕ)
    (hlower : ∀ (i : Fin m) (j : Fin n), k ≤ i.val → j.val < k → Q.S i j = 0)
    (hupper : ∀ (i : Fin m) (j : Fin n), i.val < k → k ≤ j.val → Q.S i j = 0) :
    (∀ (i : Fin m) (j : Fin n), k + 1 ≤ i.val → j.val < k + 1 →
      (isolate Q k).S i j = 0) ∧
    (∀ (i : Fin m) (j : Fin n), i.val < k + 1 → k + 1 ≤ j.val →
      (isolate Q k).S i j = 0) := by
  constructor
  · intro i j hi hj
    by_cases hj' : j.val < k
    · rw [isolate_prefix Q k hlower hupper i j (Or.inr hj')]
      exact hlower i j (by omega) hj'
    · have hr : k < m := by omega
      have hc : k < n := by omega
      have heq : j = (⟨k, hc⟩ : Fin n) := Fin.ext (show j.val = k by omega)
      rw [heq]
      exact (isolate_isolated Q k hr hc).1 i (by omega)
  · intro i j hi hj
    by_cases hi' : i.val < k
    · rw [isolate_prefix Q k hlower hupper i j (Or.inl hi')]
      exact hupper i j hi' (by omega)
    · have hr : k < m := by omega
      have hc : k < n := by omega
      have heq : i = (⟨k, hr⟩ : Fin m) := Fin.ext (show i.val = k by omega)
      rw [heq]
      exact (isolate_isolated Q k hr hc).2 j (by omega)

/-- Materialize all five matrices in the existing complete-output encoding. -/
def isolateDense (A : Dense) (k : ℕ) : Result A.rows A.cols :=
  (isolate (initial A.toMatrix) k).result

theorem isolateDense_equivalence (A : Dense) (k : ℕ) :
    let R := isolateDense A k
    R.Uinv.matrix * R.U.matrix = 1 ∧ R.U.matrix * R.Uinv.matrix = 1 ∧
      R.V.matrix * R.Vinv.matrix = 1 ∧ R.Vinv.matrix * R.V.matrix = 1 ∧
      R.U.matrix * A.toMatrix * R.V.matrix = R.S.matrix := by
  have h := isolate_invariant (initial_invariant A.toMatrix) k
  simpa only [isolateDense, State.result, pack_matrix] using
    And.intro h.Uinv_U ⟨h.U_Uinv, h.V_Vinv, h.Vinv_V, h.transformed⟩

theorem isolateDense_isolated (A : Dense) (k : ℕ) (hr : k < A.rows) (hc : k < A.cols) :
    (∀ i : Fin A.rows, k < i.val → (isolateDense A k).S.matrix i ⟨k, hc⟩ = 0) ∧
      (∀ j : Fin A.cols, k < j.val → (isolateDense A k).S.matrix ⟨k, hr⟩ j = 0) := by
  simpa only [Isolated, isolateDense, State.result, pack_matrix] using
    isolate_isolated (initial A.toMatrix) k hr hc

theorem isolateDense_prefix (A : Dense) (k : ℕ)
    (hlower : ∀ (i : Fin A.rows) (j : Fin A.cols),
      k ≤ i.val → j.val < k → A.toMatrix i j = 0)
    (hupper : ∀ (i : Fin A.rows) (j : Fin A.cols),
      i.val < k → k ≤ j.val → A.toMatrix i j = 0)
    (i : Fin A.rows) (j : Fin A.cols) (hprefix : i.val < k ∨ j.val < k) :
    (isolateDense A k).S.matrix i j = A.toMatrix i j := by
  simpa only [isolateDense, State.result, pack_matrix, initial] using
    isolate_prefix (initial A.toMatrix) k hlower hupper i j hprefix

-- The general correctness theorems apply to an initially zero pivot and to
-- a protected prefix, without a supplied nonzero-entry witness.
private abbrev prefixInput : Dense :=
  ⟨4, 3, [7, 0, 0, 0, 0, 4, 0, 6, 6, 0, 0, 0], rfl⟩
example : ∀ (i : Fin 4) (j : Fin 3), i.val < 1 ∨ j.val < 1 →
    (isolateDense prefixInput 1).S.matrix i j = prefixInput.toMatrix i j := by
  exact isolateDense_prefix prefixInput 1 (by decide) (by decide)

example : (∀ i : Fin 4, 1 < i.val → (isolateDense prefixInput 1).S.matrix i 1 = 0) ∧
    (∀ j : Fin 3, 1 < j.val → (isolateDense prefixInput 1).S.matrix 1 j = 0) :=
  isolateDense_isolated prefixInput 1 (by decide) (by decide)

-- Missing positions fix all five matrices in each empty orientation and a
-- nonempty rectangle. These are kernel-checked uses of the universal guard.
example : isolate (initial (⟨0, 3, [], rfl⟩ : Dense).toMatrix) 0 =
    initial (⟨0, 3, [], rfl⟩ : Dense).toMatrix :=
  isolate_of_missing _ 0 (Or.inl (by decide))
example : isolate (initial (⟨3, 0, [], rfl⟩ : Dense).toMatrix) 0 =
    initial (⟨3, 0, [], rfl⟩ : Dense).toMatrix :=
  isolate_of_missing _ 0 (Or.inr (by decide))
example : isolate (initial (⟨0, 0, [], rfl⟩ : Dense).toMatrix) 0 =
    initial (⟨0, 0, [], rfl⟩ : Dense).toMatrix :=
  isolate_of_missing _ 0 (Or.inl (by decide))
example : isolate (initial prefixInput.toMatrix) 3 = initial prefixInput.toMatrix :=
  isolate_of_missing _ 3 (Or.inr (by decide))

-- Evaluator regressions are evidence about these runs, separate from the
-- universal isolation, termination and integer-equivalence proofs above.
private abbrev descentInput : Dense := ⟨2, 3, [6, 4, 0, 0, 6, 0], rfl⟩
/-- info: [-2, 0, 0, 0, -18, 0] -/
#guard_msgs in
#eval (isolateDense descentInput 0).S.val.entries

private abbrev zeroRowInput : Dense := ⟨1, 2, [0, -6], rfl⟩
/-- info: [-6, 0] -/
#guard_msgs in
#eval (isolateDense zeroRowInput 0).S.val.entries

private abbrev zeroColumnInput : Dense := ⟨2, 1, [0, 6], rfl⟩
/-- info: [6, 0] -/
#guard_msgs in
#eval (isolateDense zeroColumnInput 0).S.val.entries

-- A zero isolated pivot need not mean the remaining block is zero. Keeping
-- such a pivot is permitted by the weak contract, which has no zero ordering.
private abbrev zeroArmsInput : Dense := ⟨2, 2, [0, 0, 0, 5], rfl⟩
/-- info: [0, 0, 0, 5] -/
#guard_msgs in
#eval (isolateDense zeroArmsInput 0).S.val.entries

end PhdThesisLean.SmithIsolation

#print axioms PhdThesisLean.SmithIsolation.sweepRows_eq_of_zero
#print axioms PhdThesisLean.SmithIsolation.clearActiveRow_eq_of_zero
#print axioms PhdThesisLean.SmithIsolation.cross_isolated_of_zero
#print axioms PhdThesisLean.SmithIsolation.Isolated
#print axioms PhdThesisLean.SmithIsolation.isolateNonzero
#print axioms PhdThesisLean.SmithIsolation.isolateNonzero_isolated
#print axioms PhdThesisLean.SmithIsolation.isolateNonzero_invariant
#print axioms PhdThesisLean.SmithIsolation.isolateNonzero_prefix
#print axioms PhdThesisLean.SmithIsolation.isolate
#print axioms PhdThesisLean.SmithIsolation.isolate_of_missing
#print axioms PhdThesisLean.SmithIsolation.isolate_isolated
#print axioms PhdThesisLean.SmithIsolation.isolate_invariant
#print axioms PhdThesisLean.SmithIsolation.isolate_prefix
#print axioms PhdThesisLean.SmithIsolation.isolate_next_zero
#print axioms PhdThesisLean.SmithIsolation.isolateDense
#print axioms PhdThesisLean.SmithIsolation.isolateDense_equivalence
#print axioms PhdThesisLean.SmithIsolation.isolateDense_isolated
#print axioms PhdThesisLean.SmithIsolation.isolateDense_prefix
