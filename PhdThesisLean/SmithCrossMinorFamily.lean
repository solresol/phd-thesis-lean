import PhdThesisLean.SmithMinorFamily

/-!
# All-minor transport across one complete alternating pair

The column phase supplies its own order-one minor bound for the row phase.
Thus every fixed-order minor, at every actual addition prefix of one computed
column/row pair, has a cubic bit bound in the original dense input length.
Repeated pairs and diagonal stages still require an amortized growth invariant;
this module does not supply a global polynomial bound or a machine runtime.
-/

namespace PhdThesisLean.SmithCrossMinorFamily

open Matrix SmithTrace SmithReduction SmithSweep SmithSweepBounds
  SmithMinorFamily SmithEncoding

variable {m n q : ℕ}

/-- Order-one minor control is exactly entry control, including empty shapes. -/
theorem minorBound_one_iff (A : Matrix (Fin m) (Fin n) ℤ) (H : ℕ) :
    MinorBound A 1 H ↔ ∀ i j, (A i j).natAbs ≤ H := by
  constructor
  · intro h i j
    simpa only [Matrix.det_fin_one, Matrix.submatrix_apply] using
      h (fun _ => i) (fun _ => j)
  · intro h f g
    simpa only [Matrix.det_fin_one, Matrix.submatrix_apply] using h (f 0) (g 0)

/-- A strict width at the actual column/row midpoint. This uses order-one
minor transport, rather than a five-matrix bound or a fresh determinant bound. -/
theorem columnTrace_prefix_entries_lt (Q : State m n) (k c t : ℕ) (hc : 0 < c)
    (hS : ∀ i j, (Q.S i j).natAbs < 2 ^ c) :
    ∀ i j, ((run Q ((columnTrace Q k).take t)).S i j).natAbs <
      2 ^ (c + m * (9 * c) + 1) := by
  have hb := columnTrace_prefix_minorBound Q k c c t hc hS
    ((minorBound_one_iff Q.S (2 ^ c)).mpr (fun i j => (hS i j).le))
  intro i j
  have he := (minorBound_one_iff _ _).mp hb i j
  exact he.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

/-- All minors through both phases of the actual trace. The second width is
proved at the updated midpoint; it is not assumed to equal the incoming width.
The extra bit converts the non-strict minor bound to a strict selected width. -/
theorem crossTrace_prefix_minorBound (Q : State m n) (k d c t : ℕ) (hc : 0 < c)
    (hS : ∀ i j, (Q.S i j).natAbs < 2 ^ c) (hM : MinorBound Q.S q (2 ^ d)) :
    MinorBound (run Q ((crossTrace Q k).take t)).S q
      (2 ^ (d + m * (9 * c) + n * (9 * (c + m * (9 * c) + 1)))) := by
  unfold crossTrace
  by_cases ht : t ≤ (columnTrace Q k).length
  · simpa only [List.take_append, Nat.sub_eq_zero_of_le ht, List.take_zero,
      List.append_nil] using (columnTrace_prefix_minorBound Q k d c t hc hS hM).mono
        (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  · have hmid : MinorBound (clearActiveColumn Q k).S q
        (2 ^ (d + m * (9 * c))) := by
      simpa only [List.take_length, columnTrace_run] using
        columnTrace_prefix_minorBound Q k d c (columnTrace Q k).length hc hS hM
    have hwidth : ∀ i j, ((clearActiveColumn Q k).S i j).natAbs <
        2 ^ (c + m * (9 * c) + 1) := by
      simpa only [List.take_length, columnTrace_run] using
        columnTrace_prefix_entries_lt Q k c (columnTrace Q k).length hc hS
    simpa only [List.take_append, List.take_of_length_le (by omega :
        (columnTrace Q k).length ≤ t), run_append, columnTrace_run] using
      rowTrace_prefix_minorBound (clearActiveColumn Q k) k (d + m * (9 * c))
        (c + m * (9 * c) + 1) (t - (columnTrace Q k).length) (by omega) hwidth hmid

private theorem dense_cross_budget (A : Dense) (q : ℕ) (hq : q ≤ A.rows) :
    let s := (SmithEncoding.encode A).length
    q * (s + q) + A.rows * (9 * s) +
      A.cols * (9 * (s + A.rows * (9 * s) + 1)) ≤
        81 * s ^ 3 + 20 * s ^ 2 + 9 * s := by
  dsimp
  let s := (SmithEncoding.encode A).length
  have hd := SmithEncoding.dimensions_le_length A
  have hm : A.rows ≤ s := by omega
  have hn : A.cols ≤ s := by omega
  have hq' : q ≤ s := hq.trans hm
  have hfirst := Nat.mul_le_mul hq' (Nat.add_le_add_left hq' s)
  have hcol := Nat.mul_le_mul_right (9 * s) hm
  have hrow := Nat.mul_le_mul hn
    (Nat.mul_le_mul_left 9 (Nat.add_le_add_right (Nat.add_le_add_left hcol s) 1))
  change q * (s + q) + A.rows * (9 * s) +
    A.cols * (9 * (s + A.rows * (9 * s) + 1)) ≤ _
  nlinarith

/-- Every minor, at every addition prefix of a full computed column/row pair,
has a cubic magnitude-bit bound in the original signed/framed dense input.
Repeated selections, order zero, zero pivots and empty rectangles are included. -/
theorem dense_crossTrace_prefix_minor_bits (A : Dense) (k t : ℕ)
    (f : Fin q → Fin A.rows) (g : Fin q → Fin A.cols) :
    (((run (initial A.toMatrix)
      ((crossTrace (initial A.toMatrix) k).take t)).S.submatrix f g).det).natAbs.size ≤
      81 * (SmithEncoding.encode A).length ^ 3 +
        20 * (SmithEncoding.encode A).length ^ 2 + 9 * (SmithEncoding.encode A).length + 1 := by
  classical
  by_cases hf : Function.Injective f
  · let s := (SmithEncoding.encode A).length
    have hS : ∀ i j, (A.toMatrix i j).natAbs < 2 ^ s :=
      fun i j => Nat.size_le.mp (SmithIsolationCount.entry_size_le_input_length A i j)
    have hs : 0 < s := by have := SmithEncoding.dimensions_le_length A; omega
    have hb := crossTrace_prefix_minorBound (initial A.toMatrix) k (q * (s + q)) s t hs
      hS (minorBound_of_entries A.toMatrix s (fun i j => (hS i j).le)) f g
    have horder : q ≤ A.rows := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
    have hb' := hb.trans (Nat.pow_le_pow_right (by decide) (dense_cross_budget A q horder))
    simpa only [Nat.size_pow] using Nat.size_le_size hb'
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hf
    rw [Matrix.det_zero_of_row_eq hne (by
      ext j
      exact congrArg (fun i => (run (initial A.toMatrix)
        ((crossTrace (initial A.toMatrix) k).take t)).S i (g j)) hab)]
    simp

/-- Order one specializes the minor theorem to a common transformed-entry
prefix width. This is one pair, not the full recursive diagonalizer. -/
theorem dense_crossTrace_prefixWidth (A : Dense) (k : ℕ) :
    SmithTraceCount.PrefixWidth (initial A.toMatrix) (crossTrace (initial A.toMatrix) k)
      (81 * (SmithEncoding.encode A).length ^ 3 +
        20 * (SmithEncoding.encode A).length ^ 2 + 9 * (SmithEncoding.encode A).length + 1) := by
  intro t i j
  have hb := dense_crossTrace_prefix_minor_bits A k t
    (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)
  simp only [Matrix.det_fin_one, Matrix.submatrix_apply] at hb
  exact Nat.size_le.mp hb

private abbrev growthInput : Dense := ⟨2, 2, [2, 1, 1, 7], rfl⟩

/-- A computed pair can shrink its pivot while increasing another entry.
Consequently pivot descent does not imply a nonincreasing entry-height budget.
This does not disprove a different global polynomial invariant. -/
theorem cross_entries_can_grow :
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
      (∀ i j, (A i j).natAbs ≤ 7) ∧ A 0 0 = 2 ∧
        (cross (initial A) 0).S 0 0 = 1 ∧ (cross (initial A) 0).S 1 1 = 13 := by
  refine ⟨growthInput.toMatrix, ?_, rfl, ?_, ?_⟩
  · decide +revert
  all_goals
    norm_num [cross, clearActiveRow, clearActiveColumn, SmithSweep.sweepRows,
      SmithColumn.activeRows, List.finRange_succ, List.finRange_zero, reduceRows,
      SmithPivot.pivot, transposeState, initial, growthInput, Dense.toMatrix,
      SmithPivot.gcdTrace, SmithPivot.pairStep, run, step, SmithRowOperations.rowAdd, colAdd]

#print axioms minorBound_one_iff
#print axioms columnTrace_prefix_entries_lt
#print axioms crossTrace_prefix_minorBound
#print axioms dense_crossTrace_prefix_minor_bits
#print axioms dense_crossTrace_prefixWidth
#print axioms cross_entries_can_grow

end PhdThesisLean.SmithCrossMinorFamily
