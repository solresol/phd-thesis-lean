import PhdThesisLean.SmithExactMinors

/-!
# Selected minors through arbitrarily many exact stages

Exact stages preserve a selected minor whenever its rows and columns contain
the nonzero pivots. Zero exact stages are idle, so their indices can be omitted.
One original minor then controls every transformed-entry prefix through any
finite exact run, including singular rectangles and empty shapes. The
divisibility hypotheses are not invariants of the full diagonalizer.
-/

namespace PhdThesisLean.SmithExactStages

open Matrix SmithTrace SmithReduction SmithSweep SmithColumn SmithSweepBounds
  SmithTraceCount SmithEncoding SmithDecomposition SmithExactDivision SmithExactMinors

variable {m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

/-- A row addition preserves a selected minor containing its source row.
The destination may be selected or outside the minor. -/
theorem rowAdd_minor (A : Matrix (Fin m) (Fin n) ℤ)
    (f : α → Fin m) (g : α → Fin n) (hf : Function.Injective f)
    (r s : Fin m) (hrs : r ≠ s) (c : ℤ) (a : α) (ha : f a = r) :
    ((SmithRowOperations.rowAdd A s r c).submatrix f g).det = (A.submatrix f g).det := by
  classical
  by_cases hs : ∃ b, f b = s
  · obtain ⟨b, hb⟩ := hs
    have hba : b ≠ a := by intro h; subst b; exact hrs (ha.symm.trans hb)
    have heq : (SmithRowOperations.rowAdd A s r c).submatrix f g =
        (A.submatrix f g).updateRow b ((A.submatrix f g) b + c • (A.submatrix f g) a) := by
      ext i j
      by_cases hi : i = b
      · subst i
        simp [SmithRowOperations.rowAdd, Matrix.submatrix_apply, Matrix.updateRow, Function.update,
          hb, ha, Pi.add_apply]
      · have hfi : f i ≠ s := fun h => hi (hf (h.trans hb.symm))
        simp [SmithRowOperations.rowAdd, Matrix.submatrix_apply, Matrix.updateRow, Function.update,
          hi, hfi]
    rw [heq, Matrix.det_updateRow_add_smul_self _ hba]
  · congr 1
    ext i j
    have hfi : f i ≠ s := fun h => hs ⟨i, h⟩
    simp [SmithRowOperations.rowAdd, hfi]

private theorem sweep_minor (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (hd : ∀ i, Q.S r j ∣ Q.S i j)
    (f : α → Fin m) (g : α → Fin n) (hf : Function.Injective f)
    (a : α) (ha : f a = r) :
    ((sweepRows Q r j rows).S.submatrix f g).det = (Q.S.submatrix f g).det := by
  induction rows generalizing Q with
  | nil => rfl
  | cons s rows ih =>
      by_cases hrs : r = s
      · simp only [sweepRows, dite_eq_left hrs]
        exact ih Q hd
      · have hd' : ∀ i, (reduceRows Q r s hrs j).S r j ∣
            (reduceRows Q r s hrs j).S i j := by
          intro i
          rw [reduceRows_pivot_of_dvd Q r s hrs j (hd s)]
          by_cases hi : i = s
          · subst i
            rw [(reduceRows_correct Q r s hrs j).1]
            exact dvd_zero _
          · simpa only [reduceRows, ite_eq_left (hd s), step,
              SmithRowOperations.rowAdd, ite_eq_right hi] using hd i
        rw [sweepRows, dite_eq_right hrs, ih _ hd']
        simp only [reduceRows, ite_eq_left (hd s), step]
        exact rowAdd_minor Q.S f g hf r s hrs _ a ha

/-- A complete exact pair preserves every minor containing its pivot row and
column. Other selected rows/columns may lie anywhere, including above the pivot.
Neither nonzero pivots nor a nonzero determinant are needed. -/
theorem cross_minor (Q : State m n) (k : ℕ) (hd : ExactArms Q k)
    (hr : k < m) (hc : k < n)
    (f : α → Fin m) (g : α → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (a b : α) (ha : f a = ⟨k, hr⟩) (hb : g b = ⟨k, hc⟩) :
    ((cross Q k).S.submatrix f g).det = (Q.S.submatrix f g).det := by
  have hp (l : Fin n) : (clearActiveColumn Q k).S ⟨k, hr⟩ l = Q.S ⟨k, hr⟩ l := by
    simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc]
    exact sweepRows_pivot_of_dvd Q _ _ _ (hd hr hc).1 l
  have hrow : ∀ l, (clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩ ∣
      (clearActiveColumn Q k).S ⟨k, hr⟩ l := by
    intro l
    rw [hp _, hp _]
    exact (hd hr hc).2.1 l
  have hcol : ((clearActiveColumn Q k).S.submatrix f g).det =
      (Q.S.submatrix f g).det := by
    simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc]
    exact sweep_minor Q _ _ _ (hd hr hc).1 f g hf a ha
  have htrans := sweep_minor (transposeState (clearActiveColumn Q k))
    ⟨k, hc⟩ ⟨k, hr⟩ (activeRows n k) hrow g f hg b hb
  change ((clearActiveColumn (transposeState (clearActiveColumn Q k)) k).S.transpose.submatrix f g).det = _
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  rw [clearActiveColumn, dite_eq_left hc, dite_eq_left hr, htrans]
  simpa only [transposeState, ← Matrix.transpose_submatrix, Matrix.det_transpose] using hcol

/-- The existing pair controller at successive diagonal positions. This is
auxiliary trace bookkeeping, not a replacement controlled-growth algorithm. -/
def stages (Q : State m n) : ℕ → State m n
  | 0 => Q
  | k + 1 => cross (stages Q k) k

def stagesTrace (Q : State m n) : ℕ → List (Op m n)
  | 0 => []
  | k + 1 => stagesTrace Q k ++ crossTrace (stages Q k) k

theorem stagesTrace_run (Q : State m n) (k : ℕ) :
    run Q (stagesTrace Q k) = stages Q k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [stagesTrace, run_append, ih, crossTrace_run, stages]

theorem stages_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (k : ℕ) : Invariant A (stages Q k) := by
  rw [← stagesTrace_run]
  exact run_invariant hQ _

/-- Missing positions contribute no additions, preserving the complete state. -/
theorem stagesTrace_succ_of_missing (Q : State m n) (k : ℕ) (h : m ≤ k ∨ n ≤ k) :
    stagesTrace Q (k + 1) = stagesTrace Q k := by
  have hz : crossTrace (stages Q k) k = [] := by
    rcases h with h | h <;> simp [crossTrace, columnTrace, not_lt_of_ge h]
  rw [stagesTrace, hz, List.append_nil]

theorem stagesTrace_of_empty (Q : State m n) (k : ℕ) (h : m = 0 ∨ n = 0) :
    stagesTrace Q k = [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [stagesTrace_succ_of_missing Q k (by omega), ih]

/-- Every selected minor containing all completed pivot rows and columns is
unchanged through any finite run of exact stages, including zero pivots. -/
theorem stages_minor (Q : State m n) (k : ℕ)
    (hd : ∀ t < k, ExactArms (stages Q t) t)
    (f : α → Fin m) (g : α → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hrows : ∀ t < k, ∃ a, (f a).val = t)
    (hcols : ∀ t < k, ∃ b, (g b).val = t) :
    ((stages Q k).S.submatrix f g).det = (Q.S.submatrix f g).det := by
  induction k with
  | zero => rfl
  | succ k ih =>
      obtain ⟨a, ha⟩ := hrows k (by omega)
      obtain ⟨b, hb⟩ := hcols k (by omega)
      have hr : k < m := ha ▸ (f a).isLt
      have hc : k < n := hb ▸ (g b).isLt
      rw [stages, cross_minor _ k (hd k (by omega)) hr hc f g hf hg a b
        (Fin.ext ha) (Fin.ext hb)]
      exact ih (fun t ht => hd t (by omega))
        (fun t ht => hrows t (by omega)) (fun t ht => hcols t (by omega))

private theorem cross_isolated (Q : State m n) (k : ℕ) (hd : ExactArms Q k)
    (hr : k < m) (hc : k < n) :
    SmithIsolation.Isolated (cross Q k) k hr hc := by
  constructor
  · intro i hi
    have hir : i ≠ ⟨k, hr⟩ := by intro h; subst i; simp at hi
    rw [cross_nonpivot_entry_of_dvd Q k hd hr hc i hir]
    exact clearActiveColumn_clears Q k hr hc i hi
  · exact fun j hj => clearActiveRow_clears (clearActiveColumn Q k) k hr hc j hj

private theorem cross_prefix_succ (Q : State m n) (k : ℕ) (hd : ExactArms Q k)
    (hQ : SmithDiagonalization.Prefix Q k) :
    SmithDiagonalization.Prefix (cross Q k) (k + 1) := by
  intro i j hij hpos
  by_cases hold : i.val < k ∨ j.val < k
  · rw [cross_prefix Q k (fun a b ha hb => hQ a b (by omega) (Or.inr hb))
      (fun a b ha hb => hQ a b (by omega) (Or.inl ha)) i j hold]
    exact hQ i j hij hold
  · have hi : k ≤ i.val := by omega
    have hj : k ≤ j.val := by omega
    have hr : k < m := lt_of_le_of_lt hi i.isLt
    have hc : k < n := lt_of_le_of_lt hj j.isLt
    rcases hpos with hi' | hj'
    · have hie : i = ⟨k, hr⟩ := Fin.ext (by simpa using (show i.val = k by omega))
      subst i
      exact (cross_isolated Q k hd hr hc).2 j (by omega)
    · have hje : j = ⟨k, hc⟩ := Fin.ext (by simpa using (show j.val = k by omega))
      subst j
      exact (cross_isolated Q k hd hr hc).1 i (by omega)

theorem stages_prefix (Q : State m n) (k : ℕ)
    (hd : ∀ t < k, ExactArms (stages Q t) t) :
    SmithDiagonalization.Prefix (stages Q k) k := by
  induction k with
  | zero => exact SmithDiagonalization.prefix_zero Q
  | succ k ih =>
      exact cross_prefix_succ _ k (hd k (by omega))
        (ih (fun t ht => hd t (by omega)))

private theorem stages_retains (Q : State m n) (k t : ℕ) (ht : t ≤ k)
    (hd : ∀ a < k, ExactArms (stages Q a) a)
    (i : Fin m) (j : Fin n) (hpos : i.val < t ∨ j.val < t) :
    (stages Q k).S i j = (stages Q t).S i j := by
  induction k with
  | zero =>
      have heq : t = 0 := by omega
      subst t
      rfl
  | succ k ih =>
      by_cases htk : t ≤ k
      · have hp := stages_prefix Q k (fun a ha => hd a (by omega))
        rw [stages, cross_prefix _ k
          (fun a b ha hb => hp a b (by omega) (Or.inr hb))
          (fun a b ha hb => hp a b (by omega) (Or.inl ha)) i j (by omega)]
        exact ih htk (fun a ha => hd a (by omega))
      · have : t = k + 1 := by omega
        subst t
        rfl

private theorem cross_pivot_eq (Q : State m n) (k : ℕ) (hd : ExactArms Q k)
    (hr : k < m) (hc : k < n) :
    (cross Q k).S ⟨k, hr⟩ ⟨k, hc⟩ = Q.S ⟨k, hr⟩ ⟨k, hc⟩ := by
  have hp (l : Fin n) : (clearActiveColumn Q k).S ⟨k, hr⟩ l = Q.S ⟨k, hr⟩ l := by
    simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc]
    exact sweepRows_pivot_of_dvd Q _ _ _ (hd hr hc).1 l
  have hrow : ∀ l, (clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩ ∣
      (clearActiveColumn Q k).S ⟨k, hr⟩ l := by
    intro l
    rw [hp _, hp _]
    exact (hd hr hc).2.1 l
  change (clearActiveColumn (transposeState (clearActiveColumn Q k)) k).S
    ⟨k, hc⟩ ⟨k, hr⟩ = _
  rw [clearActiveColumn, dite_eq_left hc, dite_eq_left hr,
    sweepRows_pivot_of_dvd _ _ _ _ hrow]
  exact hp _

private theorem completed_pivot_eq (Q : State m n) (k t : ℕ) (ht : t < k)
    (hd : ∀ a < k, ExactArms (stages Q a) a) (hr : t < m) (hc : t < n) :
    (stages Q k).S ⟨t, hr⟩ ⟨t, hc⟩ = (stages Q t).S ⟨t, hr⟩ ⟨t, hc⟩ := by
  rw [stages_retains Q k (t + 1) (by omega) hd _ _ (Or.inl (by simp)), stages,
    cross_pivot_eq _ t (hd t ht)]

/-- Zero exact stages are idle on all five matrices. Consequently selected
minors need contain only the nonzero completed pivots, avoiding cancellation
at zero even for rank-deficient matrices. -/
theorem stages_minor_of_nonzero (Q : State m n) (k : ℕ) (hk : k ≤ min m n)
    (hd : ∀ t < k, ExactArms (stages Q t) t)
    (f : α → Fin m) (g : α → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hrows : ∀ t < k, ∀ (hr : t < m) (hc : t < n),
      (stages Q t).S ⟨t, hr⟩ ⟨t, hc⟩ ≠ 0 → ∃ a, (f a).val = t)
    (hcols : ∀ t < k, ∀ (hr : t < m) (hc : t < n),
      (stages Q t).S ⟨t, hr⟩ ⟨t, hc⟩ ≠ 0 → ∃ b, (g b).val = t) :
    ((stages Q k).S.submatrix f g).det = (Q.S.submatrix f g).det := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hr : k < m := lt_of_lt_of_le (Nat.lt_succ_self k) (hk.trans (min_le_left _ _))
      have hc : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) (hk.trans (min_le_right _ _))
      have hprev := ih (by omega) (fun t ht => hd t (by omega))
        (fun t ht => hrows t (by omega)) (fun t ht => hcols t (by omega))
      rw [stages]
      by_cases hz : (stages Q k).S ⟨k, hr⟩ ⟨k, hc⟩ = 0
      · rw [cross_eq_of_zero _ k (hd k (by omega)) hr hc hz]
        exact hprev
      · obtain ⟨a, ha⟩ := hrows k (by omega) hr hc hz
        obtain ⟨b, hb⟩ := hcols k (by omega) hr hc hz
        rw [cross_minor _ k (hd k (by omega)) hr hc f g hf hg a b
          (Fin.ext ha) (Fin.ext hb)]
        exact hprev

/-- One original minor bounds each trailing entry after arbitrarily many
exact stages. Zero completed pivots are omitted from the selected minor; no
nonsingularity, square shape or nonzero-pivot premise is imposed. -/
theorem stages_trailing_height (Q : State m n) (k H : ℕ) (hH : 1 ≤ H)
    (hd : ∀ t < k, ExactArms (stages Q t) t)
    (hQ : ∀ i j, (Q.S i j).natAbs ≤ H)
    (i : Fin m) (j : Fin n) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    ((stages Q k).S i j).natAbs ≤ (k + 1).factorial * H ^ (k + 1) := by
  classical
  have hm : k ≤ m := hi.trans i.isLt.le
  have hn : k ≤ n := hj.trans j.isLt.le
  let p (a : Fin k) := (stages Q k).S
    ⟨a.val, lt_of_lt_of_le a.isLt hm⟩ ⟨a.val, lt_of_lt_of_le a.isLt hn⟩
  let β := {a : Fin k // p a ≠ 0}
  let f : Option β → Fin m := fun a => match a with
    | none => i
    | some a => ⟨a.val.val, lt_of_lt_of_le a.val.isLt hm⟩
  let g : Option β → Fin n := fun a => match a with
    | none => j
    | some a => ⟨a.val.val, lt_of_lt_of_le a.val.isLt hn⟩
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b => have hv := congrArg Fin.val hab; dsimp [f] at hv; have := b.val.isLt; omega
    | some a =>
        cases b with
        | none => have hv := congrArg Fin.val hab; dsimp [f] at hv; have := a.val.isLt; omega
        | some b =>
            congr 1
            apply Subtype.ext
            apply Fin.ext
            exact congrArg (fun x : Fin m => x.val) hab
  have hg : Function.Injective g := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b => have hv := congrArg Fin.val hab; dsimp [g] at hv; have := b.val.isLt; omega
    | some a =>
        cases b with
        | none => have hv := congrArg Fin.val hab; dsimp [g] at hv; have := a.val.isLt; omega
        | some b =>
            congr 1
            apply Subtype.ext
            apply Fin.ext
            exact congrArg (fun x : Fin n => x.val) hab
  have hmem (t : ℕ) (ht : t < k) (hr : t < m) (hc : t < n)
      (hz : (stages Q t).S ⟨t, hr⟩ ⟨t, hc⟩ ≠ 0) : p ⟨t, ht⟩ ≠ 0 := by
    dsimp [p]
    rwa [completed_pivot_eq Q k t ht hd hr hc]
  have hminor := stages_minor_of_nonzero Q k (le_min hm hn) hd f g hf hg
    (fun t ht hr hc hz => ⟨some ⟨⟨t, ht⟩, hmem t ht hr hc hz⟩, rfl⟩)
    (fun t ht hr hc hz => ⟨some ⟨⟨t, ht⟩, hmem t ht hr hc hz⟩, rfl⟩)
  let B := (stages Q k).S.submatrix f g
  have hp := stages_prefix Q k hd
  have hdiag : B = Matrix.diagonal (fun a => B a a) := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp
    · rw [Matrix.diagonal_apply_ne _ hab]
      cases a with
      | none =>
          cases b with
          | none => exact False.elim (hab rfl)
          | some b =>
              apply hp _ _ (by dsimp [f, g]; have := b.val.isLt; omega)
              exact Or.inr b.val.isLt
      | some a =>
          cases b with
          | none =>
              apply hp _ _ (by dsimp [f, g]; have := a.val.isLt; omega)
              exact Or.inl a.val.isLt
          | some b =>
              apply hp _ _ ?_ (Or.inl a.val.isLt)
              intro heq
              apply hab
              congr 1
              apply Subtype.ext
              exact Fin.ext heq
  have hdet : B.det = (stages Q k).S i j * ∏ a : β, p a.val := by
    rw [hdiag, Matrix.det_diagonal, Fintype.prod_option]
    rfl
  have hprod : (∏ a : β, p a.val) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    exact fun a _ => a.property
  have hle : ((stages Q k).S i j).natAbs ≤ B.det.natAbs := by
    rw [hdet, Int.natAbs_mul]
    exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hprod)
  have hcard : Fintype.card (Option β) ≤ k + 1 := by
    rw [Fintype.card_option]
    have hc := Fintype.card_subtype_le (fun a : Fin k => p a ≠ 0)
    simpa only [Fintype.card_fin] using Nat.add_le_add_right hc 1
  have hD : ∀ a b, |(Q.S.submatrix f g) a b| ≤ (H : ℤ) := by
    intro a b
    rw [← Int.natCast_natAbs]
    exact_mod_cast hQ (f a) (g b)
  have hdetZ := Matrix.det_le (abv := AbsoluteValue.abs) hD
  have hdetN : (Q.S.submatrix f g).det.natAbs ≤
      (Fintype.card (Option β)).factorial * H ^ Fintype.card (Option β) := by
    change |(Q.S.submatrix f g).det| ≤
      (Fintype.card (Option β)).factorial • (H : ℤ) ^ Fintype.card (Option β) at hdetZ
    rw [nsmul_eq_mul, ← Int.natCast_natAbs] at hdetZ
    exact_mod_cast hdetZ
  calc
    _ ≤ B.det.natAbs := hle
    _ = (Q.S.submatrix f g).det.natAbs := congrArg Int.natAbs hminor
    _ ≤ (Fintype.card (Option β)).factorial * H ^ Fintype.card (Option β) := hdetN
    _ ≤ (k + 1).factorial * H ^ (k + 1) :=
      Nat.mul_le_mul (Nat.factorial_le hcard) (Nat.pow_le_pow_right hH hcard)

/-- All transformed entries, including completed diagonal entries, share the
same original-input minor bound after any finite exact run. -/
theorem stages_height (Q : State m n) (k H : ℕ) (hH : 1 ≤ H)
    (hd : ∀ t < k, ExactArms (stages Q t) t)
    (hQ : ∀ i j, (Q.S i j).natAbs ≤ H) :
    ∀ i j, ((stages Q k).S i j).natAbs ≤ (k + 1).factorial * H ^ (k + 1) := by
  induction k with
  | zero => simpa [stages] using hQ
  | succ k ih =>
      have hprev := ih (fun t ht => hd t (by omega))
      have hmono : (k + 1).factorial * H ^ (k + 1) ≤
          (k + 1 + 1).factorial * H ^ (k + 1 + 1) :=
        Nat.mul_le_mul (Nat.factorial_le (by omega)) (Nat.pow_le_pow_right hH (by omega))
      intro i j
      by_cases hold : i.val < k ∨ j.val < k
      · have hp := stages_prefix Q k (fun t ht => hd t (by omega))
        rw [stages, cross_prefix _ k
          (fun a b ha hb => hp a b (by omega) (Or.inr hb))
          (fun a b ha hb => hp a b (by omega) (Or.inl ha)) i j hold]
        exact (hprev i j).trans hmono
      · by_cases hnew : i.val < k + 1 ∨ j.val < k + 1
        · by_cases heq : i.val = j.val
          · have hi : i.val = k := by omega
            have hj : j.val = k := by omega
            have hr : k < m := hi ▸ i.isLt
            have hc : k < n := hj ▸ j.isLt
            have hie : i = ⟨k, hr⟩ := Fin.ext hi
            have hje : j = ⟨k, hc⟩ := Fin.ext hj
            rw [hie, hje, stages, cross_pivot_eq _ k (hd k (by omega))]
            exact (hprev _ _).trans hmono
          · rw [stages_prefix Q (k + 1) hd i j heq hnew, Int.natAbs_zero]
            exact Nat.zero_le _
        · exact stages_trailing_height Q (k + 1) H hH hd hQ i j (by omega) (by omega)

/-- Every actual addition prefix is controlled by one original minor bound,
without compounding the local quadratic estimate at successive stages. -/
theorem stagesTrace_prefix_height (Q : State m n) (k H : ℕ) (hH : 1 ≤ H)
    (hd : ∀ t < k, ExactArms (stages Q t) t)
    (hQ : ∀ i j, (Q.S i j).natAbs ≤ H) :
    ∀ t i j, ((run Q ((stagesTrace Q k).take t)).S i j).natAbs ≤
      (k + 1).factorial * H ^ (k + 1) := by
  induction k with
  | zero => simpa [stagesTrace, run] using fun (_ : ℕ) => hQ
  | succ k ih =>
      have hd' : ∀ t < k, ExactArms (stages Q t) t :=
        fun t ht => hd t (by omega)
      have hmono : (k + 1).factorial * H ^ (k + 1) ≤
          (k + 1 + 1).factorial * H ^ (k + 1 + 1) :=
        Nat.mul_le_mul (Nat.factorial_le (by omega)) (Nat.pow_le_pow_right hH (by omega))
      intro t i j
      rw [stagesTrace, List.take_append]
      by_cases ht : t ≤ (stagesTrace Q k).length
      · rw [Nat.sub_eq_zero_of_le ht, List.take_zero, List.append_nil]
        exact (ih hd' t i j).trans hmono
      · rw [List.take_of_length_le (by omega), run_append, stagesTrace_run]
        apply crossTrace_prefix_height_of_endpoints _ k _ (hd k (by omega))
        · exact fun i j => (stages_height Q k H hH hd' hQ i j).trans hmono
        · exact stages_height Q (k + 1) H hH hd hQ

/-- Factorials and powers yield a polynomial bit width in the number of
stages and incoming width. This includes zero pivots and all prefix additions. -/
theorem stagesTrace_prefix_width (Q : State m n) (k c : ℕ)
    (hd : ∀ t < k, ExactArms (stages Q t) t)
    (hQ : ∀ i j, (Q.S i j).natAbs < 2 ^ c) :
    PrefixWidth Q (stagesTrace Q k) ((k + 1) * (c + k + 1) + 1) := by
  have hfactor : (k + 1).factorial ≤ 2 ^ ((k + 1) * (k + 1)) := by
    calc
      _ ≤ (k + 1) ^ (k + 1) := Nat.factorial_le_pow _
      _ ≤ (2 ^ (k + 1)) ^ (k + 1) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = _ := by rw [← pow_mul]
  intro t i j
  have hh := stagesTrace_prefix_height Q k (2 ^ c) (Nat.one_le_pow _ _ (by decide)) hd
    (fun i j => (hQ i j).le) t i j
  have hpow : 2 ^ ((k + 1) * (k + 1)) * (2 ^ c) ^ (k + 1) =
      (2 : ℕ) ^ ((k + 1) * (c + k + 1)) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have hle := hh.trans (Nat.mul_le_mul_right ((2 ^ c) ^ (k + 1)) hfactor)
  rw [hpow] at hle
  exact hle.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

/-- This is the length of the row/column-addition trace, not machine time. -/
theorem stagesTrace_length (Q : State m n) (k : ℕ)
    (hd : ∀ t < k, ExactArms (stages Q t) t) :
    (stagesTrace Q k).length ≤ k * (m + n) := by
  induction k with
  | zero => simp [stagesTrace]
  | succ k ih =>
      rw [stagesTrace, List.length_append]
      have hprev := ih (fun t ht => hd t (by omega))
      have hnext := crossTrace_length_of_dvd (stages Q k) k (hd k (by omega))
      nlinarith

private theorem stagesTrace_coefficient_le (Q : State m n) (k b : ℕ) (hb : 0 < b)
    (hw : PrefixWidth Q (stagesTrace Q k) b) :
    ∀ op ∈ stagesTrace Q k, (SmithPivotBounds.coefficient op).natAbs ≤ 2 ^ b := by
  induction k with
  | zero => simp [stagesTrace]
  | succ k ih =>
      have hleft := ih hw.left
      have hright : PrefixWidth (stages Q k) (crossTrace (stages Q k) k) b := by
        simpa only [stagesTrace_run] using hw.right
      have hnext := SmithComputedBounds.crossTrace_coefficient_le _ k b hb hright
      exact fun op hop => (List.mem_append.mp hop).elim (hleft op) (hnext op)

/-- Common bit width in original dense input length, for at most `min m n`
exact stages. The separate all-five bound below also pays for inverse maps. -/
def width (s : ℕ) : ℕ := (s + 1) * (2 * s + 1) + 1

def exponent (s : ℕ) : ℕ := s + s ^ 2 * (width s + 1)

/-- Polynomial all-five, every-prefix size under explicit exact-stage premises.
The input length includes signed entries and unary dimensions, so identity
maps in the two empty orientations are charged too. No machine is claimed. -/
theorem stagesTrace_input_prefix_bound (A : Dense) (k t : ℕ)
    (hk : k ≤ min A.rows A.cols)
    (hd : ∀ a < k, ExactArms (stages (initial A.toMatrix) a) a) :
    SmithPivotBounds.Bounded
      (run (initial A.toMatrix) ((stagesTrace (initial A.toMatrix) k).take t))
      (2 ^ exponent (SmithEncoding.encode A).length) := by
  let s := (SmithEncoding.encode A).length
  have hdim := dimensions_le_length A
  have hks : k ≤ s := by have := hk.trans (min_le_left _ _); dsimp [s]; omega
  have hsum : A.rows + A.cols ≤ s := by dsimp [s]; omega
  have hS : ∀ i j, (A.toMatrix i j).natAbs < 2 ^ s :=
    fun i j => Nat.size_le.mp (SmithIsolationCount.entry_size_le_input_length A i j)
  have hw : PrefixWidth (initial A.toMatrix) (stagesTrace (initial A.toMatrix) k) (width s) := by
    intro t i j
    apply (stagesTrace_prefix_width (initial A.toMatrix) k s hd hS t i j).trans_le
    apply Nat.pow_le_pow_right (by decide)
    dsimp [width]
    nlinarith
  have hcoeff := stagesTrace_coefficient_le _ k (width s) (by dsimp [width]; omega) hw
  have hinit := SmithPivotBounds.initial_pow_bound A.toMatrix s (fun i j => (hS i j).le)
  have hout := SmithPivotBounds.run_pow_bound _ ((stagesTrace (initial A.toMatrix) k).take t)
    s (width s) hinit (fun op hop => hcoeff op (List.mem_of_mem_take hop))
  have hlen := (List.length_take_le' t (stagesTrace (initial A.toMatrix) k)).trans
    (stagesTrace_length _ k hd)
  have hcount : ((stagesTrace (initial A.toMatrix) k).take t).length ≤ s ^ 2 := by
    calc
      _ ≤ k * (A.rows + A.cols) := hlen
      _ ≤ s * s := Nat.mul_le_mul hks hsum
      _ = s ^ 2 := by ring
  apply hout.mono
  apply Nat.pow_le_pow_right (by decide)
  dsimp [exponent]
  nlinarith

/-- Complete five-matrix output size; signs, dimensions, both inverse maps
and outer frames are included. This is conditional on exactness at each stage. -/
theorem stages_output_length (A : Dense) (k : ℕ)
    (hk : k ≤ min A.rows A.cols)
    (hd : ∀ a < k, ExactArms (stages (initial A.toMatrix) a) a) :
    let s := (SmithEncoding.encode A).length
    (SmithDecomposition.encode (stages (initial A.toMatrix) k).result).length ≤
      16 * s ^ 6 + 24 * s ^ 5 + 24 * s ^ 4 + 8 * s ^ 3 +
        16 * s ^ 2 + 10 * s + 25 := by
  have hb := stagesTrace_input_prefix_bound A k
    (stagesTrace (initial A.toMatrix) k).length hk hd
  rw [List.take_length, stagesTrace_run] at hb
  calc
    _ ≤ 2 * (5 * (SmithEncoding.encode A).length + 10 +
        2 * (SmithEncoding.encode A).length * (SmithEncoding.encode A).length *
          (2 * (exponent (SmithEncoding.encode A).length + 1) + 2)) + 5 :=
      encode_length_le_of_input_bits A _ _ hb.result_entry_bits
    _ = _ := by simp only [exponent, width]; ring

/-- At the last rectangular position an exact run satisfies the existing weak
integer decomposition contract. This does not establish its premises globally
or identify its trace with the full `finishTrace` controller. -/
theorem stages_valid (A : Dense)
    (hd : ∀ a < min A.rows A.cols, ExactArms (stages (initial A.toMatrix) a) a) :
    Valid A.toMatrix (stages (initial A.toMatrix) (min A.rows A.cols)).result := by
  have h := stages_invariant (initial_invariant A.toMatrix) (min A.rows A.cols)
  have hp := stages_prefix (initial A.toMatrix) (min A.rows A.cols) hd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [State.result, pack_matrix] using h.Uinv_U
  · simpa only [State.result, pack_matrix] using h.U_Uinv
  · simpa only [State.result, pack_matrix] using h.V_Vinv
  · simpa only [State.result, pack_matrix] using h.Vinv_V
  · simpa only [State.result, pack_matrix] using h.transformed
  · intro i j hij
    simp only [State.result, pack_matrix]
    apply hp i j hij
    omega

-- Kernel specializations exercise a zero first pivot, a negative nonunit
-- second pivot, a rectangular singular input, and both empty orientations.
-- Universal proofs above establish the bounds; these check their scope.
private abbrev rectangle : Dense :=
  ⟨3, 4, [0, 0, 0, 0, 0, -2, 4, 2, 0, 6, -10, -4], rfl⟩

private theorem rectangle_exact : ∀ a < 3,
    ExactArms (stages (initial rectangle.toMatrix) a) a := by
  intro a ha
  have hcases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;> intro hr hc <;> decide +revert

example (t : ℕ) : SmithPivotBounds.Bounded
    (run (initial rectangle.toMatrix) ((stagesTrace (initial rectangle.toMatrix) 3).take t))
    (2 ^ exponent (SmithEncoding.encode rectangle).length) :=
  stagesTrace_input_prefix_bound rectangle 3 t (by decide) rectangle_exact

example : Valid rectangle.toMatrix (stages (initial rectangle.toMatrix) 3).result :=
  stages_valid rectangle rectangle_exact

example (t : ℕ) : SmithPivotBounds.Bounded
    (run (initial (⟨0, 3, [], rfl⟩ : Dense).toMatrix)
      ((stagesTrace (initial (⟨0, 3, [], rfl⟩ : Dense).toMatrix) 0).take t))
    (2 ^ exponent (SmithEncoding.encode (⟨0, 3, [], rfl⟩ : Dense)).length) :=
  stagesTrace_input_prefix_bound _ 0 t (by decide) (by intro a ha; omega)

example (t : ℕ) : SmithPivotBounds.Bounded
    (run (initial (⟨3, 0, [], rfl⟩ : Dense).toMatrix)
      ((stagesTrace (initial (⟨3, 0, [], rfl⟩ : Dense).toMatrix) 0).take t))
    (2 ^ exponent (SmithEncoding.encode (⟨3, 0, [], rfl⟩ : Dense)).length) :=
  stagesTrace_input_prefix_bound _ 0 t (by decide) (by intro a ha; omega)

example : stagesTrace (initial rectangle.toMatrix) 4 =
    stagesTrace (initial rectangle.toMatrix) 3 :=
  stagesTrace_succ_of_missing _ 3 (Or.inl (by decide))

end PhdThesisLean.SmithExactStages

#print axioms PhdThesisLean.SmithExactStages.rowAdd_minor
#print axioms PhdThesisLean.SmithExactStages.cross_minor
#print axioms PhdThesisLean.SmithExactStages.stages
#print axioms PhdThesisLean.SmithExactStages.stagesTrace
#print axioms PhdThesisLean.SmithExactStages.stagesTrace_run
#print axioms PhdThesisLean.SmithExactStages.stages_invariant
#print axioms PhdThesisLean.SmithExactStages.stagesTrace_succ_of_missing
#print axioms PhdThesisLean.SmithExactStages.stagesTrace_of_empty
#print axioms PhdThesisLean.SmithExactStages.stages_minor
#print axioms PhdThesisLean.SmithExactStages.stages_prefix
#print axioms PhdThesisLean.SmithExactStages.stages_minor_of_nonzero
#print axioms PhdThesisLean.SmithExactStages.stages_trailing_height
#print axioms PhdThesisLean.SmithExactStages.stages_height
#print axioms PhdThesisLean.SmithExactStages.stagesTrace_prefix_height
#print axioms PhdThesisLean.SmithExactStages.stagesTrace_prefix_width
#print axioms PhdThesisLean.SmithExactStages.stagesTrace_length
#print axioms PhdThesisLean.SmithExactStages.width
#print axioms PhdThesisLean.SmithExactStages.exponent
#print axioms PhdThesisLean.SmithExactStages.stagesTrace_input_prefix_bound
#print axioms PhdThesisLean.SmithExactStages.stages_output_length
#print axioms PhdThesisLean.SmithExactStages.stages_valid
