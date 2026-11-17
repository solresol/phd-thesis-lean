import PhdThesisLean.SmithPivotMinorTransport
import PhdThesisLean.SmithExactStages

/-!
# A closed family of minors through a complete computed sweep

All minors of a fixed order form a family closed under changing the selected
rows. A reducer charges its selected-entry width once, independently of minor
order. The selected-column invariant then gives an additive width charge over
every target of a complete column sweep. Transposition covers row sweeps.

This local closure does not bound alternating sweeps or later diagonal stages
in the original input, and supplies no encoded-machine runtime theorem.
-/

namespace PhdThesisLean.SmithMinorFamily

open Matrix SmithTrace SmithPivot SmithReduction SmithRowOperations
  SmithPivotMinors SmithPivotMinorTransport SmithSweepBounds SmithColumn
  SmithEncoding

variable {m n q : ℕ}

/-- A common magnitude bound for every minor of order `q`. Repeated row or
column selections are allowed and have zero determinant. Order zero costs one. -/
def MinorBound (A : Matrix (Fin m) (Fin n) ℤ) (q H : ℕ) : Prop :=
  ∀ (f : Fin q → Fin m) (g : Fin q → Fin n), (A.submatrix f g).det.natAbs ≤ H

theorem MinorBound.mono {A : Matrix (Fin m) (Fin n) ℤ} {H K : ℕ}
    (h : MinorBound A q H) (hHK : H ≤ K) : MinorBound A q K :=
  fun f g => (h f g).trans hHK

private theorem det_zero_of_not_injective (A : Matrix (Fin m) (Fin n) ℤ)
    (f : Fin q → Fin m) (g : Fin q → Fin n) (hf : ¬ Function.Injective f) :
    (A.submatrix f g).det = 0 := by
  classical
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hf
  exact Matrix.det_zero_of_row_eq hne (by ext j; exact congrArg (fun i => A i (g j)) hab)

/-- Replacing one row selects another member of the same minor family.
In particular the replacement is allowed to repeat an existing row. -/
theorem MinorBound.rowMinor {A : Matrix (Fin m) (Fin n) ℤ} {H : ℕ}
    (h : MinorBound A q H) (f : Fin q → Fin m) (g : Fin q → Fin n)
    (a : Fin q) (i : Fin m) : (rowMinor A f g a i).natAbs ≤ H := by
  have he : (A.submatrix f g).updateRow a (fun j => A i (g j)) =
      A.submatrix (Function.update f a i) g := by
    ext b j
    by_cases hb : b = a <;> simp [Matrix.updateRow, Function.update, hb]
  change ((A.submatrix f g).updateRow a (fun j => A i (g j))).det.natAbs ≤ H
  rw [he]
  exact h (Function.update f a i) g

private theorem run_minor_closed (Q : State m n) (r s : Fin m) (hrs : r ≠ s)
    (ops : List (Op m n)) (hops : ∀ op ∈ ops, RowPair r s op)
    (f : Fin q → Fin m) (g : Fin q → Fin n) (hf : Function.Injective f)
    (hclosed : (∃ a, f a = r) ↔ ∃ a, f a = s) :
    ((run Q ops).S.submatrix f g).det = (Q.S.submatrix f g).det := by
  induction ops generalizing Q with
  | nil => rfl
  | cons op ops ih =>
      rw [run, ih (step Q op) (fun x hx => hops x (by simp [hx]))]
      have hop := hops op (by simp)
      cases op with
      | col u v huv c => exact False.elim hop
      | row u v huv c =>
          have hsame : (∃ a, f a = u) ↔ ∃ a, f a = v := by
            rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hclosed
            · exact hclosed.symm
          by_cases hv : ∃ a, f a = v
          · obtain ⟨a, ha⟩ := hv
            exact SmithExactStages.rowAdd_minor Q.S f g hf v u huv.symm c a ha
          · have hu : ¬ ∃ a, f a = u := fun h => hv (hsame.mp h)
            congr 1
            ext a j
            simp [step, rowAdd, show f a ≠ u from fun he => hu ⟨a, he⟩]

private theorem reducer_rowPair (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j : Fin n) : ∀ op ∈ reduceRowsTrace Q r s h j, RowPair r s op := by
  unfold reduceRowsTrace
  split_ifs
  · intro op hop
    simp only [List.mem_singleton] at hop
    subst op
    exact Or.inr ⟨rfl, rfl⟩
  · exact gcdTrace_rowPair r s h _ _

/-- One actual reducer transports the entire minor family, including minors
containing neither or both mixed rows, at every unfinished addition prefix. -/
theorem reduceRowsTrace_prefix_minorBound (Q : State m n)
    (r s : Fin m) (hrs : r ≠ s) (j : Fin n) (d c t : ℕ) (hc : 0 < c)
    (hx : (Q.S r j).natAbs < 2 ^ c) (hy : (Q.S s j).natAbs < 2 ^ c)
    (hM : MinorBound Q.S q (2 ^ d)) :
    MinorBound (run Q ((reduceRowsTrace Q r s hrs j).take t)).S q (2 ^ (d + 9 * c)) := by
  classical
  intro f g
  by_cases hf : Function.Injective f
  · by_cases hclosed : (∃ a, f a = r) ↔ ∃ a, f a = s
    · rw [run_minor_closed Q r s hrs _ (fun op hop =>
        reducer_rowPair Q r s hrs j op (List.mem_of_mem_take hop)) f g hf hclosed]
      exact (hM f g).trans (Nat.pow_le_pow_right (by decide) (by omega))
    · have hone : (∃ a, f a = r) ∧ (¬ ∃ a, f a = s) ∨
          (∃ a, f a = s) ∧ (¬ ∃ a, f a = r) := by tauto
      rcases hone with ⟨⟨a, ha⟩, hs⟩ | ⟨⟨a, ha⟩, hr⟩
      · rw [← rowMinor_self _ f g a]
        exact reduceRowsTrace_prefix_minor_pow_bound Q r s hrs j d c t hc hx hy
          f g a (fun b hb => ⟨fun he => hb (hf (he.trans ha.symm)),
            fun he => hs ⟨b, he⟩⟩) (hM.rowMinor f g a) (f a)
      · rw [← rowMinor_self _ f g a]
        exact reduceRowsTrace_prefix_minor_pow_bound Q r s hrs j d c t hc hx hy
          f g a (fun b hb => ⟨fun he => hr ⟨b, he⟩,
            fun he => hb (hf (he.trans ha.symm))⟩) (hM.rowMinor f g a) (f a)
  · rw [det_zero_of_not_injective _ f g hf]
    exact Nat.zero_le _

/-- A complete sweep charges `9c` per target, with the same selected-column
width `c` at every boundary. The minor family is reselected after each reducer. -/
theorem sweepRowsTrace_prefix_minorBound (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (d c t : ℕ) (hc : 0 < c)
    (hS : ∀ i, (Q.S i j).natAbs < 2 ^ c) (hM : MinorBound Q.S q (2 ^ d)) :
    MinorBound (run Q ((sweepRowsTrace Q r j rows).take t)).S q
      (2 ^ (d + rows.length * (9 * c))) := by
  induction rows generalizing Q d t with
  | nil => simpa only [sweepRowsTrace, List.take_nil, run, List.length_nil,
      Nat.zero_mul, Nat.add_zero] using hM
  | cons s rows ih =>
      simp only [sweepRowsTrace]
      split_ifs with hrs
      · exact (ih Q d t hS hM).mono (Nat.pow_le_pow_right (by decide)
          (by simp only [List.length_cons]; nlinarith))
      · have hfirst := reduceRowsTrace_prefix_minorBound Q r s hrs j d c t hc
          (hS r) (hS s) hM
        by_cases ht : t ≤ (reduceRowsTrace Q r s hrs j).length
        · simpa only [List.take_append, Nat.sub_eq_zero_of_le ht, List.take_zero,
            List.append_nil] using hfirst.mono (Nat.pow_le_pow_right (by decide)
              (by simp only [List.length_cons]; nlinarith))
        · have hnext : MinorBound (reduceRows Q r s hrs j).S q (2 ^ (d + 9 * c)) := by
            simpa only [List.take_length, reduceRowsTrace_run] using
              reduceRowsTrace_prefix_minorBound Q r s hrs j d c
                (reduceRowsTrace Q r s hrs j).length hc (hS r) (hS s) hM
          have htail := ih (reduceRows Q r s hrs j) (d + 9 * c)
            (t - (reduceRowsTrace Q r s hrs j).length)
            (reduceRows_column_lt Q r s hrs j c hS) hnext
          simpa only [List.take_append, List.take_of_length_le (by omega :
              (reduceRowsTrace Q r s hrs j).length ≤ t), SmithSweepBounds.run_append,
            reduceRowsTrace_run] using (show
              MinorBound (run (reduceRows Q r s hrs j)
                ((sweepRowsTrace (reduceRows Q r s hrs j) r j rows).take
                  (t - (reduceRowsTrace Q r s hrs j).length))).S q
                (2 ^ (d + (s :: rows).length * (9 * c))) from by
              convert htail using 1
              congr 1
              simp only [List.length_cons]
              ring)

/-- Total active-column wrapper. Missing positions and empty rectangles are
idle, and no rank, nonzero-pivot or divisibility hypothesis is imposed. -/
theorem columnTrace_prefix_minorBound (Q : State m n) (k d c t : ℕ) (hc : 0 < c)
    (hS : ∀ i j, (Q.S i j).natAbs < 2 ^ c) (hM : MinorBound Q.S q (2 ^ d)) :
    MinorBound (run Q ((columnTrace Q k).take t)).S q (2 ^ (d + m * (9 * c))) := by
  unfold columnTrace
  split_ifs
  · exact (sweepRowsTrace_prefix_minorBound _ _ _ _ d c t hc (fun i => hS i _) hM).mono
      (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (activeRows_length_le m k)) d))
  all_goals
    simpa only [List.take_nil, run] using
      (hM.mono (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)))

/-- Transposition exchanges the two selections without changing magnitude. -/
theorem MinorBound.transpose {A : Matrix (Fin m) (Fin n) ℤ} {H : ℕ}
    (h : MinorBound A q H) : MinorBound A.transpose q H := by
  intro f g
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  exact h g f

/-- The same entire-family bound at each actual column-addition prefix of a
row sweep. This is the trace used in the second half of `crossTrace`. -/
theorem rowTrace_prefix_minorBound (Q : State m n) (k d c t : ℕ) (hc : 0 < c)
    (hS : ∀ i j, (Q.S i j).natAbs < 2 ^ c) (hM : MinorBound Q.S q (2 ^ d)) :
    MinorBound (run Q (((columnTrace (transposeState Q) k).map transposeOp).take t)).S q
      (2 ^ (d + n * (9 * c))) := by
  have hb := (columnTrace_prefix_minorBound (transposeState Q) k d c t hc
    (fun i j => hS j i) hM.transpose).transpose
  have he := run_transpose (transposeState Q) ((columnTrace (transposeState Q) k).take t)
  rw [transposeState_twice] at he
  rw [← List.map_take, he]
  exact hb

/-- Reuse the existing determinant estimate for the incoming family, paying
for its order. This estimate is not reapplied at every row reducer. -/
theorem minorBound_of_entries (A : Matrix (Fin m) (Fin n) ℤ) (w : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ w) : MinorBound A q (2 ^ (q * (w + q))) := by
  intro f g
  exact (RationalWitnessBounds.det_natAbs_le_pow (A.submatrix f g)
    (fun i j => hA (f i) (g j))).trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_left q (Nat.add_le_add_left
        (Nat.size_le.mpr Nat.lt_two_pow_self) w)))

private theorem dense_sweep_budget (A : Dense) (q : ℕ) (hq : q ≤ A.rows) :
    q * ((SmithEncoding.encode A).length + q) +
      A.rows * (9 * (SmithEncoding.encode A).length) ≤
        11 * (SmithEncoding.encode A).length ^ 2 := by
  have hd := SmithEncoding.dimensions_le_length A
  have hr : A.rows ≤ (SmithEncoding.encode A).length := by omega
  have horder := hq.trans hr
  have hfirst := Nat.mul_le_mul horder
    (Nat.add_le_add_left horder (SmithEncoding.encode A).length)
  have hnext := Nat.mul_le_mul_right (9 * (SmithEncoding.encode A).length) hr
  nlinarith

/-- In the actual binary input length `s`, all minors at all prefixes of one
total active-column sweep have at most `11s²+1` magnitude bits. Injectivity
pays the order from the dimension header; repeated selections give zero. -/
theorem dense_columnTrace_prefix_minor_bits (A : Dense) (k t : ℕ)
    (f : Fin q → Fin A.rows) (g : Fin q → Fin A.cols) :
    (((run (initial A.toMatrix)
      ((columnTrace (initial A.toMatrix) k).take t)).S.submatrix f g).det).natAbs.size ≤
        11 * (SmithEncoding.encode A).length ^ 2 + 1 := by
  classical
  by_cases hf : Function.Injective f
  · let L := (SmithEncoding.encode A).length
    have hA : ∀ i j, (A.toMatrix i j).natAbs < 2 ^ L :=
      fun i j => Nat.size_le.mp (SmithIsolationCount.entry_size_le_input_length A i j)
    have hL : 0 < L := by have := SmithEncoding.dimensions_le_length A; omega
    have hb := columnTrace_prefix_minorBound (initial A.toMatrix) k (q * (L + q)) L t hL
      hA (minorBound_of_entries A.toMatrix L (fun i j => (hA i j).le)) f g
    have horder : q ≤ A.rows := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
    have hbudget := dense_sweep_budget A q horder
    have hs := Nat.size_le_size (hb.trans (Nat.pow_le_pow_right (by decide) hbudget))
    simpa only [Nat.size_pow] using hs
  · rw [det_zero_of_not_injective _ f g hf]
    simp

/-- The transposed dense-input result pays for column orders from the original
column header and covers the actual mapped row-sweep trace. -/
theorem dense_rowTrace_prefix_minor_bits (A : Dense) (k t : ℕ)
    (f : Fin q → Fin A.rows) (g : Fin q → Fin A.cols) :
    (((run (initial A.toMatrix)
      (((columnTrace (transposeState (initial A.toMatrix)) k).map transposeOp).take t)).S.submatrix
        f g).det).natAbs.size ≤ 11 * (SmithEncoding.encode A).length ^ 2 + 1 := by
  classical
  by_cases hg : Function.Injective g
  · let L := (SmithEncoding.encode A).length
    have hA : ∀ i j, (A.toMatrix i j).natAbs < 2 ^ L :=
      fun i j => Nat.size_le.mp (SmithIsolationCount.entry_size_le_input_length A i j)
    have hd := SmithEncoding.dimensions_le_length A
    have hL : 0 < L := by omega
    have hb := rowTrace_prefix_minorBound (initial A.toMatrix) k (q * (L + q)) L t hL
      hA (minorBound_of_entries A.toMatrix L (fun i j => (hA i j).le)) f g
    have horder : q ≤ A.cols := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective g hg
    have hcol : A.cols ≤ L := by omega
    have hq := horder.trans hcol
    have hfirst := Nat.mul_le_mul hq (Nat.add_le_add_left hq L)
    have hnext := Nat.mul_le_mul_right (9 * L) hcol
    have hbudget : q * (L + q) + A.cols * (9 * L) ≤ 11 * L ^ 2 := by nlinarith
    have hs := Nat.size_le_size (hb.trans (Nat.pow_le_pow_right (by decide) hbudget))
    simpa only [Nat.size_pow] using hs
  · rw [← Matrix.det_transpose, Matrix.transpose_submatrix,
      det_zero_of_not_injective _ g f hg]
    simp

#print axioms MinorBound
#print axioms MinorBound.mono
#print axioms MinorBound.rowMinor
#print axioms reduceRowsTrace_prefix_minorBound
#print axioms sweepRowsTrace_prefix_minorBound
#print axioms columnTrace_prefix_minorBound
#print axioms MinorBound.transpose
#print axioms rowTrace_prefix_minorBound
#print axioms minorBound_of_entries
#print axioms dense_columnTrace_prefix_minor_bits
#print axioms dense_rowTrace_prefix_minor_bits

end PhdThesisLean.SmithMinorFamily
