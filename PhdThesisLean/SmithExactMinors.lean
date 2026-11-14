import PhdThesisLean.SmithExactDivision

/-!
# Minors across two exact-division stages

Two successive exact stages have a cubic transformed-height bound in their
common incoming matrix, rather than two compounding quadratic estimates.
The premise is checked separately at each stage; it is not a global invariant
of the computed diagonalizer. No encoded-machine runtime is claimed.
-/

namespace PhdThesisLean.SmithExactMinors

open Matrix SmithTrace SmithReduction SmithSweep SmithColumn SmithSweepBounds
  SmithTraceCount SmithEncoding SmithDecomposition SmithExactDivision

variable {m n : ℕ}

private theorem midpoint (Q : State m n) (k : ℕ) (hd : ExactArms Q k)
    (hr : k < m) (hc : k < n) :
    (∀ l, (clearActiveColumn Q k).S ⟨k, hr⟩ l = Q.S ⟨k, hr⟩ l) ∧
    (∀ i, i ≠ ⟨k, hr⟩ → (clearActiveColumn Q k).S i ⟨k, hc⟩ = 0) := by
  constructor
  · simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc]
    exact sweepRows_pivot_of_dvd Q _ _ _ (hd hr hc).1
  · intro i hir
    simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc]
    apply sweepRows_clears Q _ _ _ i hir
    by_cases hi : k < i.val
    · exact Or.inl ((mem_activeRows i k).mpr hi)
    · exact Or.inr ((hd hr hc).2.2 i (by
        have hne : i.val ≠ k := fun h => hir (Fin.ext h)
        omega))

/-- Earlier rows and the pivot row are retained or zeroed by an exact pair.
Only rows strictly below the pivot can acquire a new nonzero value. -/
theorem cross_entry_eq_or_zero_of_le (Q : State m n) (k : ℕ)
    (hd : ExactArms Q k) (i : Fin m) (hi : i.val ≤ k) (l : Fin n) :
    (cross Q k).S i l = Q.S i l ∨ (cross Q k).S i l = 0 := by
  by_cases hr : k < m
  · by_cases hc : k < n
    · have hp := (midpoint Q k hd hr hc).1
      by_cases hir : i = ⟨k, hr⟩
      · subst i
        have hd' : ∀ l, (clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩ ∣
            (clearActiveColumn Q k).S ⟨k, hr⟩ l := by
          intro l
          rw [hp _, hp _]
          exact (hd hr hc).2.1 l
        change (clearActiveColumn (transposeState (clearActiveColumn Q k)) k).S l ⟨k, hr⟩ =
          Q.S ⟨k, hr⟩ l ∨
          (clearActiveColumn (transposeState (clearActiveColumn Q k)) k).S l ⟨k, hr⟩ = 0
        rw [clearActiveColumn, dite_eq_left hc, dite_eq_left hr]
        have heq := sweepRows_entry_eq_or_zero (transposeState (clearActiveColumn Q k))
          ⟨k, hc⟩ ⟨k, hr⟩ (activeRows n k) hd' (midpoint Q k hd hr hc).2 l ⟨k, hr⟩
        simpa only [transposeState, Matrix.transpose_apply, hp] using heq
      · left
        rw [cross_nonpivot_entry_of_dvd Q k hd hr hc i hir l]
        simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc]
        rw [sweepRows_entry_of_dvd Q _ _ _ (hd hr hc).1]
        simp only [mem_activeRows]
        simp [show ¬ k < i.val by omega]
    · simp [cross, clearActiveRow, clearActiveColumn, hc]
  · simp [cross, clearActiveRow, clearActiveColumn, hr]

/-- A zero pivot with exact arms makes the pair idle on all five matrices.
This is not an inference from a zero determinant or a rank assumption. -/
theorem cross_eq_of_zero (Q : State m n) (k : ℕ) (hd : ExactArms Q k)
    (hr : k < m) (hc : k < n) (hz : Q.S ⟨k, hr⟩ ⟨k, hc⟩ = 0) :
    cross Q k = Q := by
  have hcol : clearActiveColumn Q k = Q := by
    simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc]
    apply SmithIsolation.sweepRows_eq_of_zero
    rw [sweepRows_pivot_of_dvd Q _ _ _ (hd hr hc).1, hz]
  rw [cross, hcol]
  change transposeState (clearActiveColumn (transposeState Q) k) = Q
  rw [clearActiveColumn, dite_eq_left hc, dite_eq_left hr]
  have hrow : sweepRows (transposeState Q) ⟨k, hc⟩ ⟨k, hr⟩ (activeRows n k) =
      transposeState Q := by
    apply SmithIsolation.sweepRows_eq_of_zero
    rw [sweepRows_pivot_of_dvd _ _ _ _ (hd hr hc).2.1]
    exact hz
  rw [hrow, transposeState_twice]

/-- Prefixes of an exact pair are bounded by its two endpoints. This avoids
charging a new local estimate at each visited target. -/
theorem crossTrace_prefix_height_of_endpoints (Q : State m n) (k H : ℕ)
    (hd : ExactArms Q k) (hQ : ∀ i l, (Q.S i l).natAbs ≤ H)
    (hR : ∀ i l, ((cross Q k).S i l).natAbs ≤ H) :
    ∀ t i l, ((run Q ((crossTrace Q k).take t)).S i l).natAbs ≤ H := by
  have hcol : ∀ t i l, ((run Q ((columnTrace Q k).take t)).S i l).natAbs ≤ H := by
    intro t i l
    unfold columnTrace
    split_ifs with hr hc
    · rw [sweepRowsTrace_take_of_dvd _ _ _ _ (hd hr hc).1 (by simp) t,
        sweepRows_entry_of_dvd Q _ _ _ (hd hr hc).1]
      split_ifs with h
      · have hfull := cross_nonpivot_entry_of_dvd Q k hd hr hc i h.1 l
        simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc] at hfull
        rw [sweepRows_entry_of_dvd Q _ _ _ (hd hr hc).1,
          ite_eq_left ⟨h.1, List.mem_of_mem_take h.2⟩] at hfull
        rw [← hfull]
        exact hR i l
      · exact hQ i l
    all_goals simpa only [List.take_nil, run] using hQ i l
  have hmid : ∀ i l, ((clearActiveColumn Q k).S i l).natAbs ≤ H := by
    simpa only [List.take_length, columnTrace_run] using hcol (columnTrace Q k).length
  have hrow : ∀ t i l, ((run (transposeState (clearActiveColumn Q k))
      ((columnTrace (transposeState (clearActiveColumn Q k)) k).take t)).S i l).natAbs ≤ H := by
    unfold columnTrace
    split_ifs with hc hr
    · have hp := (midpoint Q k hd hr hc).1
      have hd' : ∀ l, (clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩ ∣
          (clearActiveColumn Q k).S ⟨k, hr⟩ l := by
        intro l
        rw [hp _, hp _]
        exact (hd hr hc).2.1 l
      intro t i l
      rw [sweepRowsTrace_take_of_dvd _ _ _ _ hd' (by simp) t]
      rcases sweepRows_entry_eq_or_zero (transposeState (clearActiveColumn Q k))
        ⟨k, hc⟩ ⟨k, hr⟩ ((activeRows n k).take t) hd'
        (midpoint Q k hd hr hc).2 i l with heq | heq
      · rw [heq]
        exact hmid l i
      · rw [heq, Int.natAbs_zero]
        exact Nat.zero_le _
    all_goals
      intro t i l
      simpa only [List.take_nil, run, transposeState, Matrix.transpose_apply] using hmid l i
  intro t i l
  unfold crossTrace
  rw [List.take_append]
  by_cases ht : t ≤ (columnTrace Q k).length
  · rw [Nat.sub_eq_zero_of_le ht, List.take_zero, List.append_nil]
    exact hcol t i l
  · rw [List.take_of_length_le (by omega), run_append, columnTrace_run, ← List.map_take]
    have heq := run_transpose (transposeState (clearActiveColumn Q k))
      ((columnTrace (transposeState (clearActiveColumn Q k)) k).take
        (t - (columnTrace Q k).length))
    rw [transposeState_twice] at heq
    rw [heq]
    exact hrow _ l i

/-- The product of the two signed pivots times a trailing output entry is
its incoming 3-by-3 minor. Neither pivot is assumed to be a unit or nonzero. -/
theorem two_cross_target_numerator (Q : State m n) (k : ℕ)
    (h0 : ExactArms Q k) (h1 : ExactArms (cross Q k) (k + 1))
    (hr : k + 1 < m) (hc : k + 1 < n) (i : Fin m) (hi : k + 1 < i.val) (l : Fin n) :
    Q.S ⟨k, by omega⟩ ⟨k, by omega⟩ * (cross Q k).S ⟨k + 1, hr⟩ ⟨k + 1, hc⟩ *
      (cross (cross Q k) (k + 1)).S i l =
    Matrix.det !![Q.S ⟨k, by omega⟩ ⟨k, by omega⟩,
      Q.S ⟨k, by omega⟩ ⟨k + 1, hc⟩, Q.S ⟨k, by omega⟩ l;
      Q.S ⟨k + 1, hr⟩ ⟨k, by omega⟩,
      Q.S ⟨k + 1, hr⟩ ⟨k + 1, hc⟩, Q.S ⟨k + 1, hr⟩ l;
      Q.S i ⟨k, by omega⟩, Q.S i ⟨k + 1, hc⟩, Q.S i l] := by
  have hq := cross_target_numerator Q k h0 (by omega) (by omega)
    ⟨k + 1, hr⟩ (by simp) ⟨k + 1, hc⟩
  have hf := cross_target_numerator Q k h0 (by omega) (by omega)
    ⟨k + 1, hr⟩ (by simp) l
  have hh := cross_target_numerator Q k h0 (by omega) (by omega)
    i (by omega) ⟨k + 1, hc⟩
  have hz := cross_target_numerator Q k h0 (by omega) (by omega) i (by omega) l
  have hw := cross_target_numerator (cross Q k) (k + 1) h1 hr hc i hi l
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  by_cases hp : Q.S ⟨k, by omega⟩ ⟨k, by omega⟩ = 0
  · have hrow (j : Fin n) : Q.S ⟨k, by omega⟩ j = 0 := by
      have hd := (h0 (by omega) (by omega)).2.1 j
      simpa only [hp, zero_dvd_iff] using hd
    simp only [hp, hrow, zero_mul, add_zero, sub_zero]
  · apply mul_left_cancel₀ hp
    linear_combination (Q.S ⟨k, by omega⟩ ⟨k, by omega⟩) ^ 2 * hw +
      (Q.S ⟨k, by omega⟩ ⟨k, by omega⟩ * (cross Q k).S i l) * hq +
      (Q.S ⟨k, by omega⟩ ⟨k, by omega⟩ * Q.S ⟨k + 1, hr⟩ ⟨k + 1, hc⟩ -
        Q.S ⟨k + 1, hr⟩ ⟨k, by omega⟩ * Q.S ⟨k, by omega⟩ ⟨k + 1, hc⟩) * hz -
      (Q.S ⟨k, by omega⟩ ⟨k, by omega⟩ * (cross Q k).S ⟨k + 1, hr⟩ l) * hh -
      (Q.S ⟨k, by omega⟩ ⟨k, by omega⟩ * Q.S i ⟨k + 1, hc⟩ -
        Q.S i ⟨k, by omega⟩ * Q.S ⟨k, by omega⟩ ⟨k + 1, hc⟩) * hf


/-- The complete exact pair has a quadratic height bound, including missing
positions. The next theorem uses minors to avoid composing this bound twice. -/
theorem cross_height_of_dvd (Q : State m n) (k H : ℕ)
    (hd : ExactArms Q k) (hQ : ∀ i l, (Q.S i l).natAbs ≤ H) :
    ∀ i l, ((cross Q k).S i l).natAbs ≤ H + H * H := by
  intro i l
  by_cases hr : k < m
  · by_cases hc : k < n
    · by_cases hi : i.val ≤ k
      · rcases cross_entry_eq_or_zero_of_le Q k hd i hi l with heq | heq
        · rw [heq]
          exact (hQ i l).trans (Nat.le_add_right _ _)
        · rw [heq, Int.natAbs_zero]
          exact Nat.zero_le _
      · have hir : i ≠ ⟨k, hr⟩ := by intro h; subst i; simp at hi
        rw [cross_nonpivot_entry_of_dvd Q k hd hr hc i hir l]
        simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc]
        exact sweepRows_height_of_dvd Q _ _ _ (hd hr hc).1 H hQ i l
    · rw [cross_of_missing Q k (Or.inr (by omega))]
      exact (hQ i l).trans (Nat.le_add_right H (H * H))
  · rw [cross_of_missing Q k (Or.inl (by omega))]
    exact (hQ i l).trans (Nat.le_add_right H (H * H))

private theorem quadratic_le_cubic (H : ℕ) (hH : 1 ≤ H) :
    H + H * H ≤ 6 * H ^ 3 := by
  have hsq : H ≤ H * H := by nlinarith
  have hcube : H * H ≤ H ^ 3 := by nlinarith
  omega

/-- A common incoming height bounds both exact stages cubically. Zero pivots
use the idle-pair theorem rather than cancelling zero. Rectangles, singular
inputs and missing positions need no determinant-nonvanishing premise. -/
theorem two_cross_height (Q : State m n) (k H : ℕ) (hH : 1 ≤ H)
    (h0 : ExactArms Q k) (h1 : ExactArms (cross Q k) (k + 1))
    (hQ : ∀ i l, (Q.S i l).natAbs ≤ H) :
    ∀ i l, ((cross (cross Q k) (k + 1)).S i l).natAbs ≤ 6 * H ^ 3 := by
  have hR : ∀ i l, ((cross Q k).S i l).natAbs ≤ 6 * H ^ 3 :=
    fun i l => (cross_height_of_dvd Q k H h0 hQ i l).trans (quadratic_le_cubic H hH)
  by_cases hr : k + 1 < m
  · by_cases hc : k + 1 < n
    · by_cases hp : Q.S ⟨k, by omega⟩ ⟨k, by omega⟩ = 0
      · have heq := cross_eq_of_zero Q k h0 (by omega) (by omega) hp
        rw [heq] at h1 ⊢
        exact fun i l => (cross_height_of_dvd Q (k + 1) H h1 hQ i l).trans
          (quadratic_le_cubic H hH)
      · by_cases hq : (cross Q k).S ⟨k + 1, hr⟩ ⟨k + 1, hc⟩ = 0
        · rw [cross_eq_of_zero (cross Q k) (k + 1) h1 hr hc hq]
          exact hR
        · intro i l
          by_cases hi : i.val ≤ k + 1
          · rcases cross_entry_eq_or_zero_of_le (cross Q k) (k + 1) h1 i hi l with heq | heq
            · rw [heq]
              exact hR i l
            · rw [heq, Int.natAbs_zero]
              exact Nat.zero_le _
          · let D : Matrix (Fin 3) (Fin 3) ℤ :=
              !![Q.S ⟨k, by omega⟩ ⟨k, by omega⟩,
                Q.S ⟨k, by omega⟩ ⟨k + 1, hc⟩, Q.S ⟨k, by omega⟩ l;
                Q.S ⟨k + 1, hr⟩ ⟨k, by omega⟩,
                Q.S ⟨k + 1, hr⟩ ⟨k + 1, hc⟩, Q.S ⟨k + 1, hr⟩ l;
                Q.S i ⟨k, by omega⟩, Q.S i ⟨k + 1, hc⟩, Q.S i l]
            have hD : ∀ a b, |D a b| ≤ (H : ℤ) := by
              intro a b
              fin_cases a <;> fin_cases b <;>
                change |Q.S _ _| ≤ (H : ℤ) <;>
                rw [← Int.natCast_natAbs] <;> exact_mod_cast hQ _ _
            have hdetZ : |D.det| ≤ (6 : ℤ) * (H : ℤ) ^ 3 := by
              have hb := Matrix.det_le (abv := AbsoluteValue.abs) hD
              norm_num at hb
              exact hb
            have hdet : D.det.natAbs ≤ 6 * H ^ 3 := by
              rw [← Int.natCast_natAbs] at hdetZ
              exact_mod_cast hdetZ
            have hnum := two_cross_target_numerator Q k h0 h1 hr hc i (by omega) l
            have hmul : Q.S ⟨k, by omega⟩ ⟨k, by omega⟩ *
                (cross Q k).S ⟨k + 1, hr⟩ ⟨k + 1, hc⟩ ≠ 0 := mul_ne_zero hp hq
            calc
              _ ≤ (Q.S ⟨k, by omega⟩ ⟨k, by omega⟩ *
                    (cross Q k).S ⟨k + 1, hr⟩ ⟨k + 1, hc⟩ *
                    (cross (cross Q k) (k + 1)).S i l).natAbs := by
                  rw [Int.natAbs_mul]
                  exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr hmul)
              _ = D.det.natAbs := congrArg Int.natAbs hnum
              _ ≤ 6 * H ^ 3 := hdet
    · rw [cross_of_missing (cross Q k) (k + 1) (Or.inr (by omega))]
      exact hR
  · rw [cross_of_missing (cross Q k) (k + 1) (Or.inl (by omega))]
    exact hR

/-- Actual row/column additions at two successive runtime positions. This
trace uses the existing pair controller; it does not change the diagonalizer. -/
def twoCrossTrace (Q : State m n) (k : ℕ) : List (Op m n) :=
  crossTrace Q k ++ crossTrace (cross Q k) (k + 1)

theorem twoCrossTrace_run (Q : State m n) (k : ℕ) :
    run Q (twoCrossTrace Q k) = cross (cross Q k) (k + 1) := by
  rw [twoCrossTrace, run_append, crossTrace_run, crossTrace_run]

/-- Every addition prefix has the same cubic incoming-height bound. A bound
only on the final entries would not suffice for binary-complexity work. -/
theorem twoCrossTrace_prefix_height (Q : State m n) (k H : ℕ) (hH : 1 ≤ H)
    (h0 : ExactArms Q k) (h1 : ExactArms (cross Q k) (k + 1))
    (hQ : ∀ i l, (Q.S i l).natAbs ≤ H) :
    ∀ t i l, ((run Q ((twoCrossTrace Q k).take t)).S i l).natAbs ≤ 6 * H ^ 3 := by
  have hQ' : ∀ i l, (Q.S i l).natAbs ≤ 6 * H ^ 3 :=
    fun i l => (hQ i l).trans ((Nat.le_add_right H (H * H)).trans (quadratic_le_cubic H hH))
  have hR : ∀ i l, ((cross Q k).S i l).natAbs ≤ 6 * H ^ 3 :=
    fun i l => (cross_height_of_dvd Q k H h0 hQ i l).trans (quadratic_le_cubic H hH)
  have hT := two_cross_height Q k H hH h0 h1 hQ
  intro t i l
  rw [twoCrossTrace, List.take_append]
  by_cases ht : t ≤ (crossTrace Q k).length
  · rw [Nat.sub_eq_zero_of_le ht, List.take_zero, List.append_nil]
    exact crossTrace_prefix_height_of_endpoints Q k _ h0 hQ' hR t i l
  · rw [List.take_of_length_le (by omega), run_append, crossTrace_run]
    exact crossTrace_prefix_height_of_endpoints (cross Q k) (k + 1) _ h1 hR hT _ i l

/-- Two successive exact stages need at most three incoming width units and
three extra bits, including every prefix and all zero/missing cases. -/
theorem twoCrossTrace_prefix_width (Q : State m n) (k c : ℕ)
    (h0 : ExactArms Q k) (h1 : ExactArms (cross Q k) (k + 1))
    (hQ : ∀ i l, (Q.S i l).natAbs < 2 ^ c) :
    PrefixWidth Q (twoCrossTrace Q k) (3 * c + 3) := by
  intro t i l
  have hb := twoCrossTrace_prefix_height Q k (2 ^ c) (by
    have : 0 < (2 : ℕ) ^ c := by positivity
    omega) h0 h1
    (fun i l => (hQ i l).le) t i l
  have heq : (2 : ℕ) ^ (3 * c + 3) = 8 * (2 ^ c) ^ 3 := by
    rw [pow_add, show 3 * c = c * 3 by omega, pow_mul]
    norm_num
    ring
  rw [heq]
  have : 0 < ((2 : ℕ) ^ c) ^ 3 := by positivity
  omega

/-- This counts additions only. It excludes computing quotients, branch tests,
traversal and encoding, so it is not a machine-time claim. -/
theorem twoCrossTrace_length (Q : State m n) (k : ℕ)
    (h0 : ExactArms Q k) (h1 : ExactArms (cross Q k) (k + 1)) :
    (twoCrossTrace Q k).length ≤ 2 * (m + n) := by
  rw [twoCrossTrace, List.length_append]
  have ha := crossTrace_length_of_dvd Q k h0
  have hb := crossTrace_length_of_dvd (cross Q k) (k + 1) h1
  omega


/-- All five integer matrices at every prefix, measured in the existing dense
input's actual bits. Both inverse maps and empty-dimension identities are paid
for. This is a size theorem, without an arithmetic or structural machine. -/
theorem twoCrossTrace_input_prefix_bound (A : Dense) (k t : ℕ)
    (h0 : ExactArms (initial A.toMatrix) k)
    (h1 : ExactArms (cross (initial A.toMatrix) k) (k + 1)) :
    SmithPivotBounds.Bounded (run (initial A.toMatrix)
      ((twoCrossTrace (initial A.toMatrix) k).take t))
      (2 ^ (6 * (SmithEncoding.encode A).length ^ 2 +
        9 * (SmithEncoding.encode A).length)) := by
  let s := (SmithEncoding.encode A).length
  let b := 3 * s + 3
  have hS : ∀ i l, (A.toMatrix i l).natAbs < 2 ^ s :=
    fun i l => Nat.size_le.mp (SmithIsolationCount.entry_size_le_input_length A i l)
  have hw := twoCrossTrace_prefix_width (initial A.toMatrix) k s h0 h1 hS
  have hcoeff : ∀ op ∈ twoCrossTrace (initial A.toMatrix) k,
      (SmithPivotBounds.coefficient op).natAbs ≤ 2 ^ b := by
    have hleft := SmithComputedBounds.crossTrace_coefficient_le _ k b (by omega) hw.left
    have hright : PrefixWidth (cross (initial A.toMatrix) k)
        (crossTrace (cross (initial A.toMatrix) k) (k + 1)) b := by
      simpa only [crossTrace_run] using hw.right
    have hnext := SmithComputedBounds.crossTrace_coefficient_le _ (k + 1) b (by omega) hright
    intro op hop
    exact (List.mem_append.mp hop).elim (hleft op) (hnext op)
  have hQ := SmithPivotBounds.initial_pow_bound A.toMatrix s (fun i l => (hS i l).le)
  have hout := SmithPivotBounds.run_pow_bound _
    ((twoCrossTrace (initial A.toMatrix) k).take t) s b hQ
    (fun op hop => hcoeff op (List.mem_of_mem_take hop))
  have hlen := (List.length_take_le' t (twoCrossTrace (initial A.toMatrix) k)).trans
    (twoCrossTrace_length _ k h0 h1)
  have hdim := dimensions_le_length A
  apply hout.mono
  apply Nat.pow_le_pow_right (by decide)
  dsimp [s, b] at *
  nlinarith

/-- Quartic complete five-matrix output size after two exact positions. The
bound includes signs, dimension headers, both inverse maps and every frame. -/
theorem two_cross_output_length (A : Dense) (k : ℕ)
    (h0 : ExactArms (initial A.toMatrix) k)
    (h1 : ExactArms (cross (initial A.toMatrix) k) (k + 1)) :
    let s := (SmithEncoding.encode A).length
    (SmithDecomposition.encode
      (cross (cross (initial A.toMatrix) k) (k + 1)).result).length ≤
      48 * s ^ 4 + 72 * s ^ 3 + 16 * s ^ 2 + 10 * s + 25 := by
  have hb := twoCrossTrace_input_prefix_bound A k
    (twoCrossTrace (initial A.toMatrix) k).length h0 h1
  rw [List.take_length, twoCrossTrace_run] at hb
  calc
    _ ≤ 2 * (5 * (SmithEncoding.encode A).length + 10 +
        2 * (SmithEncoding.encode A).length * (SmithEncoding.encode A).length *
          (2 * (6 * (SmithEncoding.encode A).length ^ 2 +
            9 * (SmithEncoding.encode A).length + 1) + 2)) + 5 :=
      encode_length_le_of_input_bits A _ _ hb.result_entry_bits
    _ = _ := by ring

/-- Exact incoming arms need not be exact at the next position. This checked
counterexample prevents using the two-stage hypotheses as a global invariant. -/
theorem exactArms_not_preserved : ∃ A : Dense,
    ExactArms (initial A.toMatrix) 0 ∧
      ¬ ExactArms (cross (initial A.toMatrix) 0) 1 := by
  refine ⟨⟨3, 3, [2, 2, 2, 2, 4, 5, 2, 5, 2], rfl⟩, ?_, ?_⟩
  · intro hr hc
    decide +revert
  · intro h
    have hd := (h (by decide) (by decide)).1 (2 : Fin 3)
    change (2 : ℤ) ∣ 3 at hd
    exact (by decide : ¬ (2 : ℤ) ∣ 3) hd

-- Kernel specializations include a negative nonunit pivot, rectangular data,
-- singular zero arms, missing positions and both empty orientations. They are
-- applications of the universal proofs, not empirical complexity estimates.
private abbrev rectangle : Dense :=
  ⟨3, 4, [-2, 4, 2, 0, 6, -10, -4, 2, -4, 10, 8, 4], rfl⟩

private theorem rectangle_exact : ExactArms (initial rectangle.toMatrix) 0 := by
  intro hr hc
  decide +revert

private theorem rectangle_next_exact : ExactArms (cross (initial rectangle.toMatrix) 0) 1 := by
  intro hr hc
  decide +revert

example (t : ℕ) : SmithPivotBounds.Bounded
    (run (initial rectangle.toMatrix) ((twoCrossTrace (initial rectangle.toMatrix) 0).take t))
    (2 ^ (6 * (SmithEncoding.encode rectangle).length ^ 2 +
      9 * (SmithEncoding.encode rectangle).length)) :=
  twoCrossTrace_input_prefix_bound rectangle 0 t rectangle_exact rectangle_next_exact

example :
    (cross (cross (initial (⟨3, 3, [0, 0, 0, 0, 0, 0, 0, 0, 5], rfl⟩ : Dense).toMatrix) 0) 1) =
      initial (⟨3, 3, [0, 0, 0, 0, 0, 0, 0, 0, 5], rfl⟩ : Dense).toMatrix := by
  rw [cross_eq_of_zero _ 0 (by intro hr hc; decide +revert) (by decide) (by decide) rfl,
    cross_eq_of_zero _ 1 (by intro hr hc; decide +revert) (by decide) (by decide) rfl]

example (t : ℕ) : SmithPivotBounds.Bounded
    (run (initial (⟨0, 3, [], rfl⟩ : Dense).toMatrix)
      ((twoCrossTrace (initial (⟨0, 3, [], rfl⟩ : Dense).toMatrix) 0).take t))
    (2 ^ (6 * (SmithEncoding.encode (⟨0, 3, [], rfl⟩ : Dense)).length ^ 2 +
      9 * (SmithEncoding.encode (⟨0, 3, [], rfl⟩ : Dense)).length)) :=
  twoCrossTrace_input_prefix_bound _ 0 t (by intro hr; change 0 < 0 at hr; omega)
    (by intro hr; change 1 < 0 at hr; omega)

example (t : ℕ) : SmithPivotBounds.Bounded
    (run (initial (⟨3, 0, [], rfl⟩ : Dense).toMatrix)
      ((twoCrossTrace (initial (⟨3, 0, [], rfl⟩ : Dense).toMatrix) 0).take t))
    (2 ^ (6 * (SmithEncoding.encode (⟨3, 0, [], rfl⟩ : Dense)).length ^ 2 +
      9 * (SmithEncoding.encode (⟨3, 0, [], rfl⟩ : Dense)).length)) :=
  twoCrossTrace_input_prefix_bound _ 0 t (by intro hr hc; change 0 < 0 at hc; omega)
    (by intro hr hc; change 1 < 0 at hc; omega)

example : twoCrossTrace (initial rectangle.toMatrix) 42 = [] := by
  simp [twoCrossTrace, crossTrace, columnTrace]

end PhdThesisLean.SmithExactMinors

#print axioms PhdThesisLean.SmithExactMinors.cross_entry_eq_or_zero_of_le
#print axioms PhdThesisLean.SmithExactMinors.cross_eq_of_zero
#print axioms PhdThesisLean.SmithExactMinors.crossTrace_prefix_height_of_endpoints
#print axioms PhdThesisLean.SmithExactMinors.two_cross_target_numerator
#print axioms PhdThesisLean.SmithExactMinors.cross_height_of_dvd
#print axioms PhdThesisLean.SmithExactMinors.two_cross_height
#print axioms PhdThesisLean.SmithExactMinors.twoCrossTrace
#print axioms PhdThesisLean.SmithExactMinors.twoCrossTrace_run
#print axioms PhdThesisLean.SmithExactMinors.twoCrossTrace_prefix_height
#print axioms PhdThesisLean.SmithExactMinors.twoCrossTrace_prefix_width
#print axioms PhdThesisLean.SmithExactMinors.twoCrossTrace_length
#print axioms PhdThesisLean.SmithExactMinors.twoCrossTrace_input_prefix_bound
#print axioms PhdThesisLean.SmithExactMinors.two_cross_output_length
#print axioms PhdThesisLean.SmithExactMinors.exactArms_not_preserved
