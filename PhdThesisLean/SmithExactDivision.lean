import PhdThesisLean.SmithComputedBounds

/-!
# Exact-division phases of the computed Smith controller

If the pivot divides its selected column, a complete sweep has the same
Schur-complement formula as one elimination, independently of the number of
targets or repeated visits. Bounds here concern this checkable divisibility
case. They do not establish the global transformed-prefix growth invariant.
-/

namespace PhdThesisLean.SmithExactDivision

open Matrix SmithTrace SmithReduction SmithSweep SmithColumn SmithSweepBounds
  SmithTraceCount SmithEncoding SmithDecomposition SmithRowOperations

variable {m n : ℕ}

private theorem reduce_dvd (Q : State m n) (r s : Fin m) (hrs : r ≠ s)
    (j : Fin n) (hd : ∀ i, Q.S r j ∣ Q.S i j) :
    ∀ i, (reduceRows Q r s hrs j).S r j ∣ (reduceRows Q r s hrs j).S i j := by
  intro i
  rw [reduceRows_pivot_of_dvd Q r s hrs j (hd s)]
  by_cases his : i = s
  · subst i
    rw [(reduceRows_correct Q r s hrs j).1]
    exact dvd_zero _
  · simp only [reduceRows, ite_eq_left (hd s), step, rowAdd, ite_eq_right his]
    exact hd i

/-- The pivot row stays fixed throughout an exact-division sweep. -/
theorem sweepRows_pivot_of_dvd (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (hd : ∀ i, Q.S r j ∣ Q.S i j) (l : Fin n) :
    (sweepRows Q r j rows).S r l = Q.S r l := by
  induction rows generalizing Q with
  | nil => rfl
  | cons s rows ih =>
      simp only [sweepRows]
      split_ifs with h
      · exact ih Q hd
      · rw [ih _ (reduce_dvd Q r s h j hd),
          reduceRows_pivot_of_dvd Q r s h j (hd s)]

/-- Exact Schur-complement entries for the existing sweep. It also covers a
zero pivot and repeated targets; it assumes no rank or square condition. -/
theorem sweepRows_entry_of_dvd (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (hd : ∀ i, Q.S r j ∣ Q.S i j) (i : Fin m) (l : Fin n) :
    (sweepRows Q r j rows).S i l =
      if i ≠ r ∧ i ∈ rows then
        Q.S i l - (Q.S i j).tdiv (Q.S r j) * Q.S r l else Q.S i l := by
  induction rows generalizing Q with
  | nil => simp [sweepRows]
  | cons s rows ih =>
      by_cases hir : i = r
      · subst i
        simp only [ne_eq, not_true_eq_false, false_and, ite_false]
        exact sweepRows_pivot_of_dvd Q r j (s :: rows) hd l
      · by_cases hrs : r = s
        · subst s
          simpa [sweepRows, hir] using ih Q hd
        · rw [sweepRows, dite_eq_right hrs, ih _ (reduce_dvd Q r s hrs j hd)]
          by_cases his : i = s
          · subst i
            have hz := (reduceRows_correct Q r s hrs j).1
            simp only [hz, Int.zero_tdiv, zero_mul, sub_zero, ite_self]
            rw [ite_eq_left ⟨hir, List.mem_cons_self⟩]
            simp only [reduceRows, ite_eq_left (hd s), step, rowAdd, ite_true]
            ring
          · have hrow (c : Fin n) :
                (reduceRows Q r s hrs j).S i c = Q.S i c :=
              (reduceRows_correct Q r s hrs j).2.2 i c hir his
            rw [hrow l, hrow j, reduceRows_pivot_of_dvd Q r s hrs j (hd s) j,
              reduceRows_pivot_of_dvd Q r s hrs j (hd s) l]
            simp [his]

/-- Multiplying a changed row by the signed pivot recovers the incoming
minor. There is no denominator inversion over the rationals. -/
theorem sweepRows_target_numerator (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (hd : ∀ i, Q.S r j ∣ Q.S i j)
    (i : Fin m) (hir : i ≠ r) (hi : i ∈ rows) (l : Fin n) :
    Q.S r j * (sweepRows Q r j rows).S i l =
      Q.S r j * Q.S i l - Q.S i j * Q.S r l := by
  rw [sweepRows_entry_of_dvd Q r j rows hd, ite_eq_left ⟨hir, hi⟩]
  have hdiv := Int.tdiv_mul_cancel (hd i)
  linear_combination -(Q.S r l) * hdiv

/-- In an exact-division phase every nonpivot target contributes one addition.
This identifies all five matrices at each prefix, not just the final `S`. -/
theorem sweepRowsTrace_take_of_dvd (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (hd : ∀ i, Q.S r j ∣ Q.S i j) (hr : r ∉ rows) (t : ℕ) :
    run Q ((sweepRowsTrace Q r j rows).take t) = sweepRows Q r j (rows.take t) := by
  induction rows generalizing Q t with
  | nil => simp [sweepRowsTrace, sweepRows, run]
  | cons s rows ih =>
      have hrs : r ≠ s := fun h => hr (by simp [h])
      have hrt : r ∉ rows := fun h => hr (by simp [h])
      cases t with
      | zero => simp [run, sweepRows]
      | succ t =>
          simp only [sweepRowsTrace, dite_eq_right hrs, reduceRowsTrace, ite_eq_left (hd s),
            List.singleton_append, List.take_succ_cons, run, sweepRows]
          simpa only [reduceRows, ite_eq_left (hd s)] using
            ih (reduceRows Q r s hrs j) (reduce_dvd Q r s hrs j hd) hrt t

/-- A complete exact-division sweep costs only one quadratic magnitude bound
on `S`, regardless of the number of targets. This is an arithmetic size bound. -/
theorem sweepRows_height_of_dvd (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (hd : ∀ i, Q.S r j ∣ Q.S i j)
    (H : ℕ) (hS : ∀ i l, (Q.S i l).natAbs ≤ H) (i : Fin m) (l : Fin n) :
    ((sweepRows Q r j rows).S i l).natAbs ≤ H + H * H := by
  rw [sweepRows_entry_of_dvd Q r j rows hd]
  split_ifs
  · calc
      _ ≤ (Q.S i l).natAbs + ((Q.S i j).tdiv (Q.S r j) * Q.S r l).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ H + H * H := by
        rw [Int.natAbs_mul]
        exact Nat.add_le_add (hS i l) (Nat.mul_le_mul
          ((Int.natAbs_tdiv_le_natAbs _ _).trans (hS i j)) (hS r l))
  · exact (hS i l).trans (Nat.le_add_right _ _)

/-- The size bound holds at every actual addition prefix, with no assumption
of a pre-existing prefix width. Missing dimensions cannot supply these indices. -/
theorem sweepRowsTrace_prefix_width_of_dvd (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (hd : ∀ i, Q.S r j ∣ Q.S i j) (hr : r ∉ rows)
    (c : ℕ) (hS : ∀ i l, (Q.S i l).natAbs < 2 ^ c) :
    PrefixWidth Q (sweepRowsTrace Q r j rows) (2 * c + 2) := by
  intro t i l
  rw [sweepRowsTrace_take_of_dvd Q r j rows hd hr t]
  have hb := sweepRows_height_of_dvd Q r j (rows.take t) hd (2 ^ c)
    (fun i l => (hS i l).le) i l
  have hp : 0 < (2 : ℕ) ^ c := by positivity
  have hpow : (2 : ℕ) ^ (2 * c + 2) = 4 * 2 ^ c * 2 ^ c := by
    rw [show 2 * c + 2 = c + c + 2 by omega, pow_add, pow_add]
    norm_num
    ring
  rw [hpow]
  nlinarith

/-- With a pivot row supported only at the selected column, exact elimination
can only retain or zero each entry. Applied on the transpose, this controls the
row sweep after the pivot column has been cleared. -/
theorem sweepRows_entry_eq_or_zero (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (hd : ∀ i, Q.S r j ∣ Q.S i j)
    (hz : ∀ l, l ≠ j → Q.S r l = 0) (i : Fin m) (l : Fin n) :
    (sweepRows Q r j rows).S i l = Q.S i l ∨
      (sweepRows Q r j rows).S i l = 0 := by
  rw [sweepRows_entry_of_dvd Q r j rows hd]
  split_ifs
  · by_cases hlj : l = j
    · subst l
      right
      rw [Int.tdiv_mul_cancel (hd i), sub_self]
    · left
      rw [hz l hlj, mul_zero, sub_zero]
  · exact Or.inl rfl

/-- Exact divisions contribute one addition per nonpivot target, including
repeated zero targets. This counts instructions, not quotient computation. -/
theorem sweepRowsTrace_length_of_dvd (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (hd : ∀ i, Q.S r j ∣ Q.S i j) (hr : r ∉ rows) :
    (sweepRowsTrace Q r j rows).length = rows.length := by
  induction rows generalizing Q with
  | nil => rfl
  | cons s rows ih =>
      have hrs : r ≠ s := fun h => hr (by simp [h])
      have hrt : r ∉ rows := fun h => hr (by simp [h])
      simp only [sweepRowsTrace, dite_eq_right hrs, reduceRowsTrace,
        ite_eq_left (hd s), List.length_append,
        ih _ (reduce_dvd Q r s hrs j hd) hrt, List.length_cons, List.length_nil]
      omega

/-- The column prefix bound is total in the runtime position and both empty
orientations. Its premise is divisibility in the incoming column, not a width
invariant about the computed trace. -/
theorem columnTrace_prefix_width_of_dvd (Q : State m n) (k c : ℕ)
    (hd : ∀ (hr : k < m) (hc : k < n), ∀ i,
      Q.S ⟨k, hr⟩ ⟨k, hc⟩ ∣ Q.S i ⟨k, hc⟩)
    (hS : ∀ i l, (Q.S i l).natAbs < 2 ^ c) :
    PrefixWidth Q (columnTrace Q k) (2 * c + 2) := by
  unfold columnTrace
  split_ifs with hr hc
  · apply sweepRowsTrace_prefix_width_of_dvd Q _ _ _ (hd hr hc)
      (by simp) c hS
  all_goals
    intro t i l
    simp only [List.take_nil, run]
    exact (hS i l).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

/-- Checkable incoming arms for an exact-division sweep pair. Earlier entries
of the pivot column are zero, as in the completed-prefix invariant. Missing
positions impose no condition. This is not a global algorithm assumption. -/
def ExactArms (Q : State m n) (k : ℕ) : Prop :=
  ∀ (hr : k < m) (hc : k < n),
    (∀ i, Q.S ⟨k, hr⟩ ⟨k, hc⟩ ∣ Q.S i ⟨k, hc⟩) ∧
    (∀ l, Q.S ⟨k, hr⟩ ⟨k, hc⟩ ∣ Q.S ⟨k, hr⟩ l) ∧
    (∀ i, i.val < k → Q.S i ⟨k, hc⟩ = 0)

private theorem exact_midpoint (Q : State m n) (k : ℕ)
    (hd : ExactArms Q k) (hr : k < m) (hc : k < n) :
    (∀ l, (clearActiveColumn Q k).S ⟨k, hr⟩ l = Q.S ⟨k, hr⟩ l) ∧
    (∀ i, i ≠ ⟨k, hr⟩ → (clearActiveColumn Q k).S i ⟨k, hc⟩ = 0) := by
  obtain ⟨hcol, hrow, hprior⟩ := hd hr hc
  simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc]
  constructor
  · exact sweepRows_pivot_of_dvd Q _ _ _ hcol
  · intro i hir
    apply sweepRows_clears Q _ _ _ i hir
    by_cases hi : k < i.val
    · exact Or.inl ((mem_activeRows i k).mpr hi)
    · right
      apply hprior i
      have hne : i.val ≠ k := fun h => hir (Fin.ext h)
      omega

/-- Once the column is clear, the following exact row sweep preserves every
nonpivot row entry. This gives the actual sweep pair a Schur-complement formula. -/
theorem cross_nonpivot_entry_of_dvd (Q : State m n) (k : ℕ)
    (hd : ExactArms Q k) (hr : k < m) (hc : k < n)
    (i : Fin m) (hi : i ≠ ⟨k, hr⟩) (l : Fin n) :
    (cross Q k).S i l = (clearActiveColumn Q k).S i l := by
  have hp := (exact_midpoint Q k hd hr hc).1
  have hz := (exact_midpoint Q k hd hr hc).2
  have hd' : ∀ l, (clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩ ∣
      (clearActiveColumn Q k).S ⟨k, hr⟩ l := by
    intro l
    rw [hp _, hp _]
    exact (hd hr hc).2.1 l
  change (clearActiveColumn (transposeState (clearActiveColumn Q k)) k).S l i = _
  rw [clearActiveColumn, dite_eq_left hc, dite_eq_left hr]
  rw [sweepRows_entry_of_dvd _ _ _ _ hd']
  simp only [transposeState, Matrix.transpose_apply, hz i hi, mul_zero, sub_zero, ite_self]

/-- The signed pivot times each trailing entry is exactly its incoming
2-by-2 minor. The zero-pivot case is included without cancellation. -/
theorem cross_target_numerator (Q : State m n) (k : ℕ)
    (hd : ExactArms Q k) (hr : k < m) (hc : k < n)
    (i : Fin m) (hi : k < i.val) (l : Fin n) :
    Q.S ⟨k, hr⟩ ⟨k, hc⟩ * (cross Q k).S i l =
      Q.S ⟨k, hr⟩ ⟨k, hc⟩ * Q.S i l - Q.S i ⟨k, hc⟩ * Q.S ⟨k, hr⟩ l := by
  have hir : i ≠ ⟨k, hr⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
  rw [cross_nonpivot_entry_of_dvd Q k hd hr hc i hir l]
  simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc]
  exact sweepRows_target_numerator Q _ _ _ (hd hr hc).1 i hir
    ((mem_activeRows i k).mpr hi) l

/-- Every addition prefix of both sweeps has at most twice the incoming
transformed bit width plus two. The second sweep cannot grow `S`; no dimension,
rank, determinant or nonzero-pivot restriction is imposed. -/
theorem crossTrace_prefix_width_of_dvd (Q : State m n) (k c : ℕ)
    (hd : ExactArms Q k) (hS : ∀ i l, (Q.S i l).natAbs < 2 ^ c) :
    PrefixWidth Q (crossTrace Q k) (2 * c + 2) := by
  have hcol := columnTrace_prefix_width_of_dvd Q k c
    (fun hr hc => (hd hr hc).1) hS
  have hmid : ∀ i l, ((clearActiveColumn Q k).S i l).natAbs < 2 ^ (2 * c + 2) := by
    simpa only [List.take_length, columnTrace_run] using hcol (columnTrace Q k).length
  have hrow : PrefixWidth (transposeState (clearActiveColumn Q k))
      (columnTrace (transposeState (clearActiveColumn Q k)) k) (2 * c + 2) := by
    unfold columnTrace
    split_ifs with hc hr
    · have hp := (exact_midpoint Q k hd hr hc).1
      have hz := (exact_midpoint Q k hd hr hc).2
      have hd' : ∀ l, (clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩ ∣
          (clearActiveColumn Q k).S ⟨k, hr⟩ l := by
        intro l
        rw [hp _, hp _]
        exact (hd hr hc).2.1 l
      intro t i l
      rw [sweepRowsTrace_take_of_dvd _ _ _ _ hd' (by simp) t]
      rcases sweepRows_entry_eq_or_zero (transposeState (clearActiveColumn Q k))
        ⟨k, hc⟩ ⟨k, hr⟩ ((activeRows n k).take t) hd' hz i l with heq | heq
      · rw [heq]
        exact hmid l i
      · rw [heq, Int.natAbs_zero]
        positivity
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

/-- Only one row/column addition per active target in this phase. Arithmetic,
branch tests, traversal and output serialization are not machine-costed here. -/
theorem crossTrace_length_of_dvd (Q : State m n) (k : ℕ) (hd : ExactArms Q k) :
    (crossTrace Q k).length ≤ m + n := by
  unfold crossTrace
  rw [List.length_append, List.length_map]
  by_cases hr : k < m
  · by_cases hc : k < n
    · have hp := (exact_midpoint Q k hd hr hc).1
      have hd' : ∀ l, (clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩ ∣
          (clearActiveColumn Q k).S ⟨k, hr⟩ l := by
        intro l
        rw [hp _, hp _]
        exact (hd hr hc).2.1 l
      simp only [columnTrace, dite_eq_left hr, dite_eq_left hc]
      rw [sweepRowsTrace_length_of_dvd _ _ _ _ (hd hr hc).1 (by simp),
        sweepRowsTrace_length_of_dvd _ _ _ _ hd' (by simp)]
      exact Nat.add_le_add (activeRows_length_le m k) (activeRows_length_le n k)
    · simp [columnTrace, hc]
  · simp [columnTrace, hr]

/-- All five integral matrices at every prefix of an exact sweep pair, in
actual dense input bits. The exponent is quadratic, including empty cases. -/
theorem crossTrace_input_prefix_bound (A : Dense) (k t : ℕ)
    (hd : ExactArms (initial A.toMatrix) k) :
    SmithPivotBounds.Bounded (run (initial A.toMatrix)
      ((crossTrace (initial A.toMatrix) k).take t))
      (2 ^ (2 * (SmithEncoding.encode A).length ^ 2 +
        4 * (SmithEncoding.encode A).length)) := by
  let s := (SmithEncoding.encode A).length
  let b := 2 * s + 2
  have hS : ∀ i l, (A.toMatrix i l).natAbs < 2 ^ s :=
    fun i l => Nat.size_le.mp (SmithIsolationCount.entry_size_le_input_length A i l)
  have hw := crossTrace_prefix_width_of_dvd (initial A.toMatrix) k s hd hS
  have hcoeff := SmithComputedBounds.crossTrace_coefficient_le _ k b (by omega) hw
  have hQ := SmithPivotBounds.initial_pow_bound A.toMatrix s (fun i l => (hS i l).le)
  have hout := SmithPivotBounds.run_pow_bound _
    ((crossTrace (initial A.toMatrix) k).take t) s b hQ
    (fun op hop => hcoeff op (List.mem_of_mem_take hop))
  have hlen := (List.length_take_le' t (crossTrace (initial A.toMatrix) k)).trans
    (crossTrace_length_of_dvd _ k hd)
  have hdim := dimensions_le_length A
  apply hout.mono
  apply Nat.pow_le_pow_right (by decide)
  dsimp [s, b] at *
  nlinarith

/-- Quartic complete output size for the same exact-division sweep pair.
Both inverse maps, unary dimensions, signs and framing are included. -/
theorem crossDense_output_length_of_dvd (A : Dense) (k : ℕ)
    (hd : ExactArms (initial A.toMatrix) k) :
    let s := (SmithEncoding.encode A).length
    (SmithDecomposition.encode (crossDense A k)).length ≤
      16 * s ^ 4 + 32 * s ^ 3 + 16 * s ^ 2 + 10 * s + 25 := by
  have hb := crossTrace_input_prefix_bound A k
    (crossTrace (initial A.toMatrix) k).length hd
  rw [List.take_length, crossTrace_run] at hb
  calc
    _ ≤ 2 * (5 * (SmithEncoding.encode A).length + 10 +
        2 * (SmithEncoding.encode A).length * (SmithEncoding.encode A).length *
          (2 * (2 * (SmithEncoding.encode A).length ^ 2 +
            4 * (SmithEncoding.encode A).length + 1) + 2)) + 5 :=
      encode_length_le_of_input_bits A _ _ hb.result_entry_bits
    _ = _ := by ring

-- Kernel specializations exercise negative/nonunit and zero pivots,
-- repeated targets, rectangular/singular matrices and both empty orientations.
private abbrev rectangle : Dense := ⟨3, 2, [-2, 4, 6, 9, -4, 7], rfl⟩
private theorem rectangle_exact : ExactArms (initial rectangle.toMatrix) 0 := by
  intro hr hc
  decide +revert

example (t : ℕ) :
    SmithPivotBounds.Bounded (run (initial rectangle.toMatrix)
      ((crossTrace (initial rectangle.toMatrix) 0).take t))
      (2 ^ (2 * (SmithEncoding.encode rectangle).length ^ 2 +
        4 * (SmithEncoding.encode rectangle).length)) :=
  crossTrace_input_prefix_bound rectangle 0 t rectangle_exact

example : (crossDense rectangle 0).S.val.entries = [-2, 0, 0, 21, 0, -1] := by decide

example : (sweepRows (initial rectangle.toMatrix) 0 0 [1, 2, 1]).S 1 1 = 21 :=
  by decide

example : ExactArms (initial
    (⟨3, 2, [0, 0, 0, 7, 0, -9], rfl⟩ : Dense).toMatrix) 0 := by
  intro hr hc
  decide +revert

example : (crossDense (⟨3, 2, [-2, 4, 6, -12, -4, 8], rfl⟩ : Dense) 0).S.val.entries =
    [-2, 0, 0, 0, 0, 0] := by decide

example : (SmithDecomposition.encode (crossDense ⟨0, 3, [], rfl⟩ 0)).length ≤
    16 * (SmithEncoding.encode (⟨0, 3, [], rfl⟩ : Dense)).length ^ 4 +
      32 * (SmithEncoding.encode (⟨0, 3, [], rfl⟩ : Dense)).length ^ 3 +
      16 * (SmithEncoding.encode (⟨0, 3, [], rfl⟩ : Dense)).length ^ 2 +
      10 * (SmithEncoding.encode (⟨0, 3, [], rfl⟩ : Dense)).length + 25 :=
  crossDense_output_length_of_dvd _ 0 (by intro hr; exact (Nat.not_lt_zero 0 hr).elim)

example : (SmithDecomposition.encode (crossDense ⟨3, 0, [], rfl⟩ 0)).length ≤
    16 * (SmithEncoding.encode (⟨3, 0, [], rfl⟩ : Dense)).length ^ 4 +
      32 * (SmithEncoding.encode (⟨3, 0, [], rfl⟩ : Dense)).length ^ 3 +
      16 * (SmithEncoding.encode (⟨3, 0, [], rfl⟩ : Dense)).length ^ 2 +
      10 * (SmithEncoding.encode (⟨3, 0, [], rfl⟩ : Dense)).length + 25 :=
  crossDense_output_length_of_dvd _ 0 (by intro hr hc; exact (Nat.not_lt_zero 0 hc).elim)

example : ExactArms (initial rectangle.toMatrix) 42 := by intro hr; norm_num [rectangle] at hr

#print axioms sweepRows_pivot_of_dvd
#print axioms sweepRows_entry_of_dvd
#print axioms sweepRows_target_numerator
#print axioms sweepRowsTrace_take_of_dvd
#print axioms sweepRows_height_of_dvd
#print axioms sweepRowsTrace_prefix_width_of_dvd
#print axioms sweepRows_entry_eq_or_zero
#print axioms sweepRowsTrace_length_of_dvd
#print axioms columnTrace_prefix_width_of_dvd
#print axioms ExactArms
#print axioms cross_nonpivot_entry_of_dvd
#print axioms cross_target_numerator
#print axioms crossTrace_prefix_width_of_dvd
#print axioms crossTrace_length_of_dvd
#print axioms crossTrace_input_prefix_bound
#print axioms crossDense_output_length_of_dvd

end PhdThesisLean.SmithExactDivision
