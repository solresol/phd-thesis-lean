import PhdThesisLean.SmithIsolation

/-!
# Binary descent and sweep counts for the existing integer isolator

The pivot magnitude after a sweep divides the incoming magnitude. A failed
nonzero sweep pair therefore at least halves it. Count the state transitions
in the existing isolator's recurrence and replay its exact five-matrix result.
This semantic count does not measure Lean evaluation, the arithmetic inside a
pair reduction, coefficient growth or encoded-machine time.
-/

namespace PhdThesisLean.SmithIsolationCount

open SmithTrace SmithReduction SmithColumn SmithSweep SmithIsolation SmithEncoding

variable {m n : ℕ}

/-- Every pair reduction replaces the pivot magnitude by a divisor, including
zero pivots. This concerns the actual selected reduction, not a supplied gcd. -/
theorem reduceRows_pivot_dvd (Q : State m n) (r s : Fin m) (h : r ≠ s) (j : Fin n) :
    ((reduceRows Q r s h j).S r j).natAbs ∣ (Q.S r j).natAbs := by
  rw [(reduceRows_correct Q r s h j).2.1]
  exact Nat.gcd_dvd_left _ _

theorem sweepRows_pivot_dvd (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) :
    ((sweepRows Q r j rows).S r j).natAbs ∣ (Q.S r j).natAbs := by
  induction rows generalizing Q with
  | nil => exact dvd_refl _
  | cons s rows ih =>
      simp only [sweepRows]
      split_ifs with h
      · exact ih Q
      · exact (ih (reduceRows Q r s h j)).trans (reduceRows_pivot_dvd Q r s h j)

theorem clearActiveColumn_pivot_dvd (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n) :
    ((clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs ∣
      (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs := by
  simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc]
  exact sweepRows_pivot_dvd Q _ _ _

theorem clearActiveRow_pivot_dvd (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n) :
    ((clearActiveRow Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs ∣
      (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs :=
  clearActiveColumn_pivot_dvd (transposeState Q) k hc hr

theorem cross_pivot_dvd (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n) :
    ((cross Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs ∣
      (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs :=
  (clearActiveRow_pivot_dvd (clearActiveColumn Q k) k hr hc).trans
    (clearActiveColumn_pivot_dvd Q k hr hc)

/-- A proper natural divisor is at most half its positive multiple. -/
theorem two_mul_le_of_dvd_of_lt {a b : ℕ} (hd : a ∣ b) (hlt : a < b) :
    2 * a ≤ b := by
  obtain ⟨c, rfl⟩ := hd
  have hc : 2 ≤ c := by
    by_contra h
    have : c = 0 ∨ c = 1 := by omega
    rcases this with rfl | rfl <;> simp_all
  nlinarith

/-- Failure of the actual sweep pair forces a factor-two decrease, without
rank, square or sign hypotheses. Zero is handled by the separate seeding pass. -/
theorem cross_failure_halves (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (ha : Q.S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0)
    (hf : ¬ Isolated (cross Q k) k hr hc) :
    2 * ((cross Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs ≤
      (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs :=
  two_mul_le_of_dvd_of_lt (cross_pivot_dvd Q k hr hc)
    ((cross_isolated_or_descend Q k hr hc ha).resolve_left hf)

theorem size_lt_of_halves {a b : ℕ} (ha : 0 < a) (h : 2 * a ≤ b) :
    a.size < b.size := by
  have hs : (2 * a).size = a.size + 1 := by
    simpa [Nat.bit, Nat.two_mul] using
      (Nat.size_bit (b := false) (n := a) (by simpa [Nat.bit] using ha.ne'))
  have := Nat.size_le_size h
  omega

theorem cross_failure_size (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (ha : Q.S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0)
    (hf : ¬ Isolated (cross Q k) k hr hc) :
    ((cross Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs.size <
      (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs.size :=
  size_lt_of_halves (Int.natAbs_pos.mpr (cross_nonzero_le Q k hr hc ha).1)
    (cross_failure_halves Q k hr hc ha hf)

/-- Semantic sweep-pair count for `isolateNonzero`, including the successful
pair. Its recursive branches follow that code; this is not an evaluator cost. -/
def nonzeroPasses (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (ha : Q.S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0) : ℕ :=
  if _h : Isolated (cross Q k) k hr hc then 1
  else 1 + nonzeroPasses (cross Q k) k hr hc (cross_nonzero_le Q k hr hc ha).1
termination_by (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs
decreasing_by exact (cross_isolated_or_descend Q k hr hc ha).resolve_left _h

/-- Replay an explicit number of complete sweep pairs on all five matrices. -/
def crosses (Q : State m n) (k : ℕ) : ℕ → State m n
  | 0 => Q
  | count + 1 => crosses (cross Q k) k count

theorem nonzeroPasses_replay (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (ha : Q.S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0) :
    crosses Q k (nonzeroPasses Q k hr hc ha) = isolateNonzero Q k hr hc ha := by
  rw [nonzeroPasses, isolateNonzero]
  split_ifs with h
  · rfl
  · rw [Nat.add_comm 1, crosses]
    exact nonzeroPasses_replay (cross Q k) k hr hc (cross_nonzero_le Q k hr hc ha).1
termination_by (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs
decreasing_by exact (cross_isolated_or_descend Q k hr hc ha).resolve_left h

/-- At most one sweep pair per binary magnitude bit after seeding. -/
theorem nonzeroPasses_le_size (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (ha : Q.S ⟨k, hr⟩ ⟨k, hc⟩ ≠ 0) :
    nonzeroPasses Q k hr hc ha ≤ (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs.size := by
  rw [nonzeroPasses]
  split_ifs with h
  · exact Nat.size_pos.mpr (Int.natAbs_pos.mpr ha)
  · have hi := nonzeroPasses_le_size (cross Q k) k hr hc
      (cross_nonzero_le Q k hr hc ha).1
    have hd := cross_failure_size Q k hr hc ha h
    omega
termination_by (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs
decreasing_by exact (cross_isolated_or_descend Q k hr hc ha).resolve_left h

/-- Include the seeding pair; missing positions perform no sweep at all. -/
def isolationPasses (Q : State m n) (k : ℕ) : ℕ :=
  if hr : k < m then
    if hc : k < n then
      if hz : (cross Q k).S ⟨k, hr⟩ ⟨k, hc⟩ = 0 then 1
      else 1 + nonzeroPasses (cross Q k) k hr hc hz
    else 0
  else 0

theorem isolationPasses_replay (Q : State m n) (k : ℕ) :
    crosses Q k (isolationPasses Q k) = isolate Q k := by
  unfold isolationPasses isolate
  split_ifs with hr hc hz
  · rfl
  · rw [Nat.add_comm 1, crosses, nonzeroPasses_replay]
  all_goals rfl

theorem isolationPasses_of_missing (Q : State m n) (k : ℕ)
    (h : m ≤ k ∨ n ≤ k) : isolationPasses Q k = 0 := by
  unfold isolationPasses
  split_ifs with hr hc hz
  all_goals omega

theorem isolationPasses_le_seed_size (Q : State m n) (k : ℕ)
    (hr : k < m) (hc : k < n) :
    isolationPasses Q k ≤ 1 + ((cross Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs.size := by
  simp only [isolationPasses, dite_eq_left hr, dite_eq_left hc]
  split_ifs with hz
  · omega
  · exact Nat.add_le_add_left (nonzeroPasses_le_size (cross Q k) k hr hc hz) 1

/-- A pair reduction cannot increase any magnitude in the selected column
past a common bound on that column. Other columns are not covered. -/
theorem reduceRows_column_bound (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j : Fin n) (H : ℕ) (hQ : ∀ i, (Q.S i j).natAbs ≤ H) :
    ∀ i, ((reduceRows Q r s h j).S i j).natAbs ≤ H := by
  intro i
  by_cases hir : i = r
  · subst i
    rw [(reduceRows_correct Q r s h j).2.1]
    by_cases ha : Q.S r j = 0
    · simpa [ha] using hQ s
    · exact (Int.gcd_le_natAbs_left _ ha).trans (hQ r)
  · by_cases his : i = s
    · subst i
      rw [(reduceRows_correct Q r s h j).1]
      exact Nat.zero_le H
    · rw [(reduceRows_correct Q r s h j).2.2 i j hir his]
      exact hQ i

theorem sweepRows_column_bound (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (H : ℕ) (hQ : ∀ i, (Q.S i j).natAbs ≤ H) :
    ∀ i, ((sweepRows Q r j rows).S i j).natAbs ≤ H := by
  induction rows generalizing Q with
  | nil => exact hQ
  | cons s rows ih =>
      simp only [sweepRows]
      split_ifs with h
      · exact ih Q hQ
      · exact ih (reduceRows Q r s h j) (reduceRows_column_bound Q r s h j H hQ)

theorem clearActiveColumn_pivot_le (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (H : ℕ) (hQ : ∀ i, (Q.S i ⟨k, hc⟩).natAbs ≤ H) :
    ((clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs ≤ H := by
  simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc]
  exact sweepRows_column_bound Q _ _ _ H hQ _

theorem clearActiveColumn_eq_of_zero (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (hz : (clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩ = 0) :
    clearActiveColumn Q k = Q := by
  simp only [clearActiveColumn, dite_eq_left hr, dite_eq_left hc] at hz ⊢
  exact sweepRows_eq_of_zero Q _ _ _ hz

/-- Even a zero-pivot seeding pass has pivot magnitude at most the incoming
matrix height. This is a bound on one pivot, not on the other output entries. -/
theorem cross_pivot_le (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n)
    (H : ℕ) (hQ : ∀ i j, (Q.S i j).natAbs ≤ H) :
    ((cross Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs ≤ H := by
  by_cases hz : (clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩ = 0
  · rw [cross, clearActiveColumn_eq_of_zero Q k hr hc hz]
    exact clearActiveColumn_pivot_le (transposeState Q) k hc hr H (fun j => hQ _ j)
  · exact (clearActiveRow_nonzero_le (clearActiveColumn Q k) k hr hc hz).2.trans
      (clearActiveColumn_pivot_le Q k hr hc H (fun i => hQ i _))

/-- The existing library's binary-size bridge charges each stored entry to
the actual signed, framed dense matrix encoding, including dimension costs. -/
theorem entry_size_le_input_length (A : Dense) (i : Fin A.rows) (j : Fin A.cols) :
    (A.toMatrix i j).natAbs.size ≤ (encode A).length := by
  have hm : A.toMatrix i j ∈ A.entries := List.getElem_mem _
  have hs := List.single_le_sum (M := ℕ)
    (l := A.entries.map (fun z => 2 * (Computability.encodeNat z.natAbs).length + 2))
    (fun _ _ => Nat.zero_le _) (2 * (Computability.encodeNat (A.toMatrix i j).natAbs).length + 2)
    (List.mem_map.mpr ⟨A.toMatrix i j, hm, rfl⟩)
  rw [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size] at hs
  rw [encode_length]
  omega

theorem crossDense_pivot_size_le_input_length (A : Dense) (k : ℕ) (hr : k < A.rows)
    (hc : k < A.cols) :
    ((cross (initial A.toMatrix) k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs.size ≤
      (encode A).length := by
  have hQ : ∀ i j, (A.toMatrix i j).natAbs ≤ 2 ^ (encode A).length - 1 := by
    intro i j
    have := Nat.size_le.mp (entry_size_le_input_length A i j)
    omega
  have h := cross_pivot_le (initial A.toMatrix) k hr hc _ hQ
  apply Nat.size_le.mpr
  have hp : 0 < 2 ^ (encode A).length := by positivity
  omega

/-- A single isolation from a densely encoded matrix uses at most `s+1`
sweep pairs, where `s` is its complete input bit length. This includes zero
pivots, arbitrary runtime positions, singular rectangles and empty inputs. -/
theorem isolationPasses_le_input_length (A : Dense) (k : ℕ) :
    isolationPasses (initial A.toMatrix) k ≤ (encode A).length + 1 := by
  by_cases hr : k < A.rows
  · by_cases hc : k < A.cols
    · have hs := isolationPasses_le_seed_size (initial A.toMatrix) k hr hc
      have hb := crossDense_pivot_size_le_input_length A k hr hc
      omega
    · rw [isolationPasses_of_missing _ k (Or.inr (by omega))]
      omega
  · rw [isolationPasses_of_missing _ k (Or.inl (by omega))]
    omega

/-- The existing isolator's exact output is reached within `s+1` semantic
transitions of `cross`. No cost is assigned to a transition or its test. -/
theorem isolate_eq_bounded_crosses (A : Dense) (k : ℕ) :
    ∃ count ≤ (encode A).length + 1,
      crosses (initial A.toMatrix) k count = isolate (initial A.toMatrix) k :=
  ⟨isolationPasses (initial A.toMatrix) k, isolationPasses_le_input_length A k,
    isolationPasses_replay _ _⟩

-- Evaluator regression evidence for nonzero/multipass traces, separate from
-- the universal theorems above and the kernel-checked zero/missing cases below.
private abbrev descentInput : Dense := ⟨2, 3, [6, 4, 0, 0, 6, 0], rfl⟩
/-- info: 2 -/
#guard_msgs in
#eval isolationPasses (initial descentInput.toMatrix) 0
private abbrev zeroSeedInput : Dense := ⟨1, 2, [0, -6], rfl⟩
/-- info: 2 -/
#guard_msgs in
#eval isolationPasses (initial zeroSeedInput.toMatrix) 0
example : isolationPasses (initial (⟨2, 3, [0, 0, 0, 0, 0, 0], rfl⟩ : Dense).toMatrix) 0 =
    1 := by decide
example : isolationPasses (initial (⟨0, 3, [], rfl⟩ : Dense).toMatrix) 0 = 0 := by decide
example : isolationPasses (initial (⟨3, 0, [], rfl⟩ : Dense).toMatrix) 0 = 0 := by decide
example : isolationPasses (initial (⟨0, 0, [], rfl⟩ : Dense).toMatrix) 0 = 0 := by decide
example : isolationPasses (initial descentInput.toMatrix) 3 = 0 := by decide

end PhdThesisLean.SmithIsolationCount
