import PhdThesisLean.SmithPivotBounds

/-!
# Binary widths through a complete divisibility-aware sweep pair

The selected column remains bounded at reduction boundaries, so a single
sweep pays the same quotient-bit budget at every target. The trace below
replays the existing controller; every prefix includes the temporary signed
swap additions and all five matrices. Transposition handles the second sweep.
These are local width and semantic addition-count bounds, not global bounds
for repeated isolation or an encoded-machine runtime theorem.
-/

namespace PhdThesisLean.SmithSweepBounds

open SmithTrace SmithPivot SmithReduction SmithColumn SmithSweep
  SmithPivotBounds SmithIsolationCount SmithEncoding SmithDecomposition

variable {m n : ℕ}

theorem run_append (Q : State m n) (xs ys : List (Op m n)) :
    run Q (xs ++ ys) = run (run Q xs) ys := by
  induction xs generalizing Q with
  | nil => rfl
  | cons op xs ih => exact ih (step Q op)

/-- Expose exactly the additions selected by the existing pair reducer. -/
def reduceRowsTrace (Q : State m n) (r s : Fin m) (h : r ≠ s) (j : Fin n) :
    List (Op m n) :=
  if Q.S r j ∣ Q.S s j then [.row s r h.symm (-(Q.S s j).tdiv (Q.S r j))]
  else gcdTrace r s h (Q.S r j) (Q.S s j)

theorem reduceRowsTrace_run (Q : State m n) (r s : Fin m) (h : r ≠ s) (j : Fin n) :
    run Q (reduceRowsTrace Q r s h j) = reduceRows Q r s h j := by
  unfold reduceRowsTrace reduceRows
  split_ifs <;> rfl

theorem reduceRowsTrace_bounds (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j : Fin n) (c : ℕ) (hc : 0 < c)
    (ha : (Q.S r j).natAbs < 2 ^ c) (hb : (Q.S s j).natAbs < 2 ^ c) :
    (reduceRowsTrace Q r s h j).length ≤ 8 * c ∧
      ∀ op ∈ reduceRowsTrace Q r s h j, (coefficient op).natAbs ≤ 2 ^ c := by
  unfold reduceRowsTrace
  split_ifs
  · constructor
    · simp only [List.length_singleton]
      omega
    · intro op hop
      simp only [List.mem_singleton] at hop
      subst op
      simpa only [coefficient, Int.natAbs_neg] using
        (Int.natAbs_tdiv_le_natAbs (Q.S s j) (Q.S r j)).trans hb.le
  · exact ⟨(gcdTrace_length_le r s h _ _).trans
      (Nat.mul_le_mul_left 8 (Nat.size_le.mpr hb)),
      gcdTrace_coefficient_le r s h _ _ (2 ^ c)
        (Nat.one_le_pow c 2 (by decide)) ha.le hb.le⟩

/-- Only the selected column is constrained; the other columns may grow. -/
theorem reduceRows_column_lt (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j : Fin n) (c : ℕ) (hQ : ∀ i, (Q.S i j).natAbs < 2 ^ c) :
    ∀ i, ((reduceRows Q r s h j).S i j).natAbs < 2 ^ c := by
  have hp : 0 < (2 : ℕ) ^ c := by positivity
  have hb := reduceRows_column_bound Q r s h j (2 ^ c - 1) (fun i => by
    have := hQ i
    omega)
  intro i
  have := hb i
  omega

/-- The trace is computed from successive updated states, with repeated targets
and occurrences of the pivot handled exactly as in `sweepRows`. -/
def sweepRowsTrace (Q : State m n) (r : Fin m) (j : Fin n) :
    List (Fin m) → List (Op m n)
  | [] => []
  | s :: rows =>
      if h : r = s then sweepRowsTrace Q r j rows
      else reduceRowsTrace Q r s h j ++ sweepRowsTrace (reduceRows Q r s h j) r j rows

theorem sweepRowsTrace_run (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) : run Q (sweepRowsTrace Q r j rows) = sweepRows Q r j rows := by
  induction rows generalizing Q with
  | nil => rfl
  | cons s rows ih =>
      simp only [sweepRowsTrace, sweepRows]
      split_ifs with h
      · exact ih Q
      · rw [run_append, reduceRowsTrace_run, ih]

/-- A fixed selected-column bound controls every quotient throughout the sweep.
It need not be replaced by the growing height of the other four matrices. -/
theorem sweepRowsTrace_bounds (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (c : ℕ) (hc : 0 < c)
    (hS : ∀ i, (Q.S i j).natAbs < 2 ^ c) :
    (sweepRowsTrace Q r j rows).length ≤ rows.length * (8 * c) ∧
      ∀ op ∈ sweepRowsTrace Q r j rows, (coefficient op).natAbs ≤ 2 ^ c := by
  induction rows generalizing Q with
  | nil => simp [sweepRowsTrace]
  | cons s rows ih =>
      simp only [sweepRowsTrace]
      split_ifs with h
      · obtain ⟨hlen, hcoeff⟩ := ih Q hS
        exact ⟨hlen.trans (Nat.mul_le_mul_right _ (by simp)), hcoeff⟩
      · obtain ⟨hp, hpc⟩ := reduceRowsTrace_bounds Q r s h j c hc (hS r) (hS s)
        obtain ⟨ht, htc⟩ := ih (reduceRows Q r s h j)
          (reduceRows_column_lt Q r s h j c hS)
        constructor
        · rw [List.length_append, List.length_cons]
          nlinarith
        · intro op hop
          exact (List.mem_append.mp hop).elim (hpc op) (htc op)

/-- Every addition prefix, including an unfinished signed swap, bounds all five
matrices by the proposed exponent `d + length(rows) * 8c(c+1)`. -/
theorem sweepRows_prefix_pow_bound (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (d c t : ℕ) (hc : 0 < c) (hQ : Bounded Q (2 ^ d))
    (hS : ∀ i, (Q.S i j).natAbs < 2 ^ c) :
    Bounded (run Q ((sweepRowsTrace Q r j rows).take t))
      (2 ^ (d + rows.length * (8 * c * (c + 1)))) := by
  obtain ⟨hlen, hcoeff⟩ := sweepRowsTrace_bounds Q r j rows c hc hS
  have hb := run_pow_bound Q ((sweepRowsTrace Q r j rows).take t) d c hQ
    (fun op hop => hcoeff op (List.mem_of_mem_take hop))
  apply hb.mono
  apply Nat.pow_le_pow_right (by decide)
  have ht := (List.length_take_le' t (sweepRowsTrace Q r j rows)).trans hlen
  have := Nat.mul_le_mul_right (c + 1) ht
  nlinarith

theorem sweepRows_pow_bound (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (d c : ℕ) (hc : 0 < c) (hQ : Bounded Q (2 ^ d))
    (hS : ∀ i, (Q.S i j).natAbs < 2 ^ c) :
    Bounded (sweepRows Q r j rows) (2 ^ (d + rows.length * (8 * c * (c + 1)))) := by
  simpa only [List.take_length, sweepRowsTrace_run] using
    sweepRows_prefix_pow_bound Q r j rows d c (sweepRowsTrace Q r j rows).length hc hQ hS

/-- Total trace of the existing active-column controller, including missing
positions and both empty orientations. -/
def columnTrace (Q : State m n) (k : ℕ) : List (Op m n) :=
  if hr : k < m then
    if hc : k < n then sweepRowsTrace Q ⟨k, hr⟩ ⟨k, hc⟩ (activeRows m k)
    else []
  else []

theorem columnTrace_run (Q : State m n) (k : ℕ) :
    run Q (columnTrace Q k) = clearActiveColumn Q k := by
  unfold columnTrace clearActiveColumn
  split_ifs
  · exact sweepRowsTrace_run _ _ _ _
  all_goals rfl

theorem activeRows_length_le (m k : ℕ) : (activeRows m k).length ≤ m := by
  simpa only [activeRows, List.length_finRange] using
    List.length_filter_le (fun i : Fin m => decide (k < i.val)) (List.finRange m)

theorem columnTrace_length_le (Q : State m n) (k c : ℕ) (hc : 0 < c)
    (hS : ∀ i j, (Q.S i j).natAbs < 2 ^ c) :
    (columnTrace Q k).length ≤ m * (8 * c) := by
  unfold columnTrace
  split_ifs
  · exact (sweepRowsTrace_bounds _ _ _ _ c hc (fun i => hS i _)).1.trans
      (Nat.mul_le_mul_right _ (activeRows_length_le m k))
  all_goals simp

theorem columnTrace_prefix_pow_bound (Q : State m n) (k d c t : ℕ) (hc : 0 < c)
    (hQ : Bounded Q (2 ^ d)) (hS : ∀ i j, (Q.S i j).natAbs < 2 ^ c) :
    Bounded (run Q ((columnTrace Q k).take t)) (2 ^ (d + m * (8 * c * (c + 1)))) := by
  unfold columnTrace
  split_ifs
  · exact (sweepRows_prefix_pow_bound _ _ _ _ d c t hc hQ (fun i => hS i _)).mono
      (Nat.pow_le_pow_right (by decide)
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ (activeRows_length_le m k)) d))
  all_goals
    simpa only [List.take_nil, run] using
      (hQ.mono (Nat.pow_le_pow_right (by decide)
        (Nat.le_add_right d (m * (8 * c * (c + 1))))))

theorem clearActiveColumn_pow_bound (Q : State m n) (k d c : ℕ) (hc : 0 < c)
    (hQ : Bounded Q (2 ^ d)) (hS : ∀ i j, (Q.S i j).natAbs < 2 ^ c) :
    Bounded (clearActiveColumn Q k) (2 ^ (d + m * (8 * c * (c + 1)))) := by
  simpa only [List.take_length, columnTrace_run] using
    columnTrace_prefix_pow_bound Q k d c (columnTrace Q k).length hc hQ hS

theorem clearActiveRow_pow_bound (Q : State m n) (k d c : ℕ) (hc : 0 < c)
    (hQ : Bounded Q (2 ^ d)) (hS : ∀ i j, (Q.S i j).natAbs < 2 ^ c) :
    Bounded (clearActiveRow Q k) (2 ^ (d + n * (8 * c * (c + 1)))) :=
  (clearActiveColumn_pow_bound (transposeState Q) k d c hc hQ.transposeState
    (fun i j => hS j i)).transposeState

/-- Cubic bit-width budget for one active sweep from a densely encoded input. -/
def sweepWidth (s : ℕ) : ℕ := s + s * (8 * s * (s + 1))

/-- Degree-seven bit-width budget for one column/row sweep pair. It is not
iterated over the isolator or over diagonal positions. -/
def crossWidth (s : ℕ) : ℕ :=
  sweepWidth s + s * (8 * (sweepWidth s + 1) * (sweepWidth s + 2))

private theorem input_length_pos (A : Dense) : 0 < (SmithEncoding.encode A).length := by
  have := dimensions_le_length A
  omega

private theorem input_entry_lt (A : Dense) :
    ∀ i j, (A.toMatrix i j).natAbs < 2 ^ (SmithEncoding.encode A).length :=
  fun i j => Nat.size_le.mp (entry_size_le_input_length A i j)

/-- Bound each actual first-sweep prefix in the original complete input bits. -/
theorem columnTrace_input_prefix_bound (A : Dense) (k t : ℕ) :
    Bounded (run (initial A.toMatrix) ((columnTrace (initial A.toMatrix) k).take t))
      (2 ^ sweepWidth (SmithEncoding.encode A).length) := by
  have hS := input_entry_lt A
  have hb := columnTrace_prefix_pow_bound (initial A.toMatrix) k _ _ t
    (input_length_pos A) (initial_pow_bound A.toMatrix _ (fun i j => (hS i j).le)) hS
  apply hb.mono
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (by have := dimensions_le_length A; omega)) _

theorem clearActiveColumn_input_bound (A : Dense) (k : ℕ) :
    Bounded (clearActiveColumn (initial A.toMatrix) k)
      (2 ^ sweepWidth (SmithEncoding.encode A).length) := by
  simpa only [List.take_length, columnTrace_run] using
    columnTrace_input_prefix_bound A k (columnTrace (initial A.toMatrix) k).length

private theorem column_entry_lt (A : Dense) (k : ℕ) :
    ∀ i j, ((clearActiveColumn (initial A.toMatrix) k).S i j).natAbs <
      2 ^ (sweepWidth (SmithEncoding.encode A).length + 1) := by
  intro i j
  have hb := (clearActiveColumn_input_bound A k).S i j
  have hp : 0 < (2 : ℕ) ^ sweepWidth (SmithEncoding.encode A).length := by positivity
  rw [pow_succ]
  omega

/-- First-phase prefixes fit the common budget for the whole pair. -/
theorem cross_column_prefix_bound (A : Dense) (k t : ℕ) :
    Bounded (run (initial A.toMatrix) ((columnTrace (initial A.toMatrix) k).take t))
      (2 ^ crossWidth (SmithEncoding.encode A).length) :=
  (columnTrace_input_prefix_bound A k t).mono
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))

/-- Every second-phase prefix is the transpose of an actual column trace on
the updated state. Both integral inverses and unfinished swaps are included. -/
theorem cross_row_prefix_bound (A : Dense) (k t : ℕ) :
    let P := clearActiveColumn (initial A.toMatrix) k
    Bounded (transposeState (run (transposeState P)
      ((columnTrace (transposeState P) k).take t)))
      (2 ^ crossWidth (SmithEncoding.encode A).length) := by
  dsimp only
  have hb := (columnTrace_prefix_pow_bound
    (transposeState (clearActiveColumn (initial A.toMatrix) k)) k
    (sweepWidth (SmithEncoding.encode A).length)
    (sweepWidth (SmithEncoding.encode A).length + 1) t (by omega)
    (clearActiveColumn_input_bound A k).transposeState
    (fun i j => column_entry_lt A k j i)).transposeState
  apply hb.mono
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (by have := dimensions_le_length A; omega)) _

/-- The final state is exactly the already checked controller, not a supplied
replacement decomposition. No square, rank or nonzero hypothesis is used. -/
theorem cross_input_bound (A : Dense) (k : ℕ) :
    Bounded (cross (initial A.toMatrix) k)
      (2 ^ crossWidth (SmithEncoding.encode A).length) := by
  simpa only [List.take_length, columnTrace_run, cross, clearActiveRow] using
    cross_row_prefix_bound A k
      (columnTrace (transposeState (clearActiveColumn (initial A.toMatrix) k)) k).length

/-- Exchange actual row and column instructions when transposing a state. -/
def transposeOp : Op m n → Op n m
  | .row r s h c => .col r s h c
  | .col r s h c => .row r s h c

theorem transposeState_step (Q : State m n) (op : Op m n) :
    transposeState (step Q op) = step (transposeState Q) (transposeOp op) := by
  cases op <;> rfl

theorem run_transpose (Q : State m n) (ops : List (Op m n)) :
    run (transposeState Q) (ops.map transposeOp) = transposeState (run Q ops) := by
  induction ops generalizing Q with
  | nil => rfl
  | cons op ops ih =>
      simp only [List.map_cons, run, ← transposeState_step]
      exact ih (step Q op)

/-- The full computed addition trace of the existing sweep pair. -/
def crossTrace (Q : State m n) (k : ℕ) : List (Op m n) :=
  columnTrace Q k ++
    (columnTrace (transposeState (clearActiveColumn Q k)) k).map transposeOp

theorem crossTrace_run (Q : State m n) (k : ℕ) :
    run Q (crossTrace Q k) = cross Q k := by
  unfold crossTrace
  rw [run_append, columnTrace_run]
  simpa only [transposeState_twice, columnTrace_run, cross, clearActiveRow] using
    run_transpose (transposeState (clearActiveColumn Q k))
      (columnTrace (transposeState (clearActiveColumn Q k)) k)

/-- A single prefix theorem for the concatenated row/column trace. This covers
every actual intermediate addition in either phase, not just pair endpoints. -/
theorem crossTrace_input_prefix_bound (A : Dense) (k t : ℕ) :
    Bounded (run (initial A.toMatrix) ((crossTrace (initial A.toMatrix) k).take t))
      (2 ^ crossWidth (SmithEncoding.encode A).length) := by
  unfold crossTrace
  rw [List.take_append]
  by_cases ht : t ≤ (columnTrace (initial A.toMatrix) k).length
  · rw [Nat.sub_eq_zero_of_le ht, List.take_zero, List.append_nil]
    exact cross_column_prefix_bound A k t
  · rw [List.take_of_length_le (by omega), run_append, columnTrace_run, ← List.map_take]
    have heq := run_transpose (transposeState (clearActiveColumn (initial A.toMatrix) k))
      ((columnTrace (transposeState (clearActiveColumn (initial A.toMatrix) k)) k).take
        (t - (columnTrace (initial A.toMatrix) k).length))
    rw [transposeState_twice] at heq
    rw [heq]
    exact cross_row_prefix_bound A k _

/-- Count row additions in the first trace and column additions in its
transposed successor. This assigns no cost to computing a quotient or list. -/
def crossAdditions (A : Dense) (k : ℕ) : ℕ :=
  (columnTrace (initial A.toMatrix) k).length +
    (columnTrace (transposeState (clearActiveColumn (initial A.toMatrix) k)) k).length

theorem crossTrace_length (A : Dense) (k : ℕ) :
    (crossTrace (initial A.toMatrix) k).length = crossAdditions A k := by
  simp only [crossTrace, List.length_append, List.length_map, crossAdditions]

theorem crossAdditions_le_input_length (A : Dense) (k : ℕ) :
    crossAdditions A k ≤
      (SmithEncoding.encode A).length * (8 * (SmithEncoding.encode A).length) +
      (SmithEncoding.encode A).length * (8 * (sweepWidth (SmithEncoding.encode A).length + 1)) := by
  have hcol := columnTrace_length_le (initial A.toMatrix) k _
    (input_length_pos A) (input_entry_lt A)
  have hrow := columnTrace_length_le
    (transposeState (clearActiveColumn (initial A.toMatrix) k)) k _
    (by omega : 0 < sweepWidth (SmithEncoding.encode A).length + 1)
    (fun i j => column_entry_lt A k j i)
  have hd := dimensions_le_length A
  exact Nat.add_le_add
    (hcol.trans (Nat.mul_le_mul_right _ (by omega)))
    (hrow.trans (Nat.mul_le_mul_right _ (by omega)))

/-- Degree-nine bound on all five framed dense output matrices of one complete
sweep pair. Signs, dimensions, canonical zero and inverse fields are charged.
The control index is supplied separately; this is size, not machine time. -/
theorem crossDense_output_length_le (A : Dense) (k : ℕ) :
    (SmithDecomposition.encode (crossDense A k)).length ≤
      2 * (5 * (SmithEncoding.encode A).length + 10 +
        2 * (SmithEncoding.encode A).length * (SmithEncoding.encode A).length *
          (2 * (crossWidth (SmithEncoding.encode A).length + 1) + 2)) + 5 :=
  encode_length_le_of_input_bits A _ _ (cross_input_bound A k).result_entry_bits

-- Kernel computations exercise the trace's exact-division, repeated-target,
-- zero and missing-index branches. Universal bounds are proved above.
private abbrev divisibleInput : Dense := ⟨3, 2, [-2, 4, 6, 9, -4, 7], rfl⟩
example : (sweepRowsTrace (initial divisibleInput.toMatrix) 0 0 [0, 1, 2, 1]).map
    coefficient = [3, -2, 0] := by decide
example : (sweepRowsTrace (initial (0 : Matrix (Fin 2) (Fin 3) ℤ)) 0 0 [0, 1, 1]).map
    coefficient = [0, 0] := by decide
example : columnTrace (initial divisibleInput.toMatrix) 42 = [] := by decide
example : crossAdditions (⟨0, 3, [], rfl⟩ : Dense) 0 = 0 := by decide
example : crossAdditions (⟨3, 0, [], rfl⟩ : Dense) 0 = 0 := by decide
example : crossAdditions (⟨0, 0, [], rfl⟩ : Dense) 0 = 0 := by decide

-- Evaluator regressions for nonzero Euclidean recursion are separate from
-- kernel proofs. The rectangle needs another pair; one pair is not a diagonalizer.
private abbrev tallInput : Dense := ⟨3, 1, [0, -30, 21], rfl⟩
/-- info: (16, [-3, 0, 0], true) -/
#guard_msgs in
#eval (crossAdditions tallInput 0, (crossDense tallInput 0).S.val.entries,
  check tallInput.toMatrix (crossDense tallInput 0))

private abbrev prefixInput : Dense :=
  ⟨4, 3, [7, 0, 0, 0, 6, 4, 0, 0, 6, 0, 0, 0], rfl⟩
/-- info: (10, [7, 0, 0, 0, -2, 0, 0, 6, -18, 0, 0, 0], false) -/
#guard_msgs in
#eval (crossAdditions prefixInput 1, (crossDense prefixInput 1).S.val.entries,
  check prefixInput.toMatrix (crossDense prefixInput 1))

#print axioms run_append
#print axioms reduceRowsTrace
#print axioms reduceRowsTrace_run
#print axioms reduceRowsTrace_bounds
#print axioms reduceRows_column_lt
#print axioms sweepRowsTrace
#print axioms sweepRowsTrace_run
#print axioms sweepRowsTrace_bounds
#print axioms sweepRows_prefix_pow_bound
#print axioms sweepRows_pow_bound
#print axioms columnTrace
#print axioms columnTrace_run
#print axioms activeRows_length_le
#print axioms columnTrace_length_le
#print axioms columnTrace_prefix_pow_bound
#print axioms clearActiveColumn_pow_bound
#print axioms clearActiveRow_pow_bound
#print axioms sweepWidth
#print axioms crossWidth
#print axioms columnTrace_input_prefix_bound
#print axioms clearActiveColumn_input_bound
#print axioms cross_column_prefix_bound
#print axioms cross_row_prefix_bound
#print axioms cross_input_bound
#print axioms transposeOp
#print axioms transposeState_step
#print axioms run_transpose
#print axioms crossTrace
#print axioms crossTrace_run
#print axioms crossTrace_input_prefix_bound
#print axioms crossAdditions
#print axioms crossTrace_length
#print axioms crossAdditions_le_input_length
#print axioms crossDense_output_length_le

end PhdThesisLean.SmithSweepBounds
