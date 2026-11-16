import PhdThesisLean.SmithPivotMinors
import PhdThesisLean.SmithPivotLinearBounds
import PhdThesisLean.SmithSweepBounds
import PhdThesisLean.RationalWitnessBounds

/-!
# Transport of selected minors through Euclidean pivot mixing

When just one of a pivot's two rows belongs to a selected minor, that minor
is not preserved. Minors with one variable row instead undergo the same
two-row additions as the original entries. Replaying those minors as virtual
entries lets the existing quotient-height bound control every actual prefix,
without multiplying the width charge by the order of the minor.

This is a local transport estimate. It supplies neither a common original-input
minor bound through successive pivots nor a polynomial-time decomposition.
-/

namespace PhdThesisLean.SmithPivotMinorTransport

open Matrix SmithTrace SmithPivot SmithRowOperations SmithPivotMinors SmithPivotBounds
  SmithEncoding SmithSweepBounds SmithReduction

variable {m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

/-- Replace one selected row by row `i`, retaining its slot and orientation.
No injectivity or nonzero determinant is required. -/
def rowMinor (A : Matrix (Fin m) (Fin n) ℤ) (f : α → Fin m) (g : α → Fin n)
    (a : α) (i : Fin m) : ℤ :=
  ((A.submatrix f g).updateRow a (fun j => A i (g j))).det

/-- At the original row, the variable-row determinant is the selected minor. -/
theorem rowMinor_self (A : Matrix (Fin m) (Fin n) ℤ)
    (f : α → Fin m) (g : α → Fin n) (a : α) :
    rowMinor A f g a (f a) = (A.submatrix f g).det := by
  unfold rowMinor
  have he : (fun j => A (f a) (g j)) = (A.submatrix f g) a := rfl
  rw [he, Matrix.updateRow_eq_self]

/-- A variable-row minor changes by exactly the corresponding row addition
provided the fixed rows avoid the destination. The source may lie outside
the selected minor. -/
theorem rowMinor_rowAdd (A : Matrix (Fin m) (Fin n) ℤ)
    (f : α → Fin m) (g : α → Fin n) (a : α)
    (r s : Fin m) (c : ℤ) (hf : ∀ b, b ≠ a → f b ≠ r) (i : Fin m) :
    rowMinor (rowAdd A r s c) f g a i =
      if i = r then rowMinor A f g a i + c * rowMinor A f g a s
      else rowMinor A f g a i := by
  classical
  have hbase (v : α → ℤ) :
      (((rowAdd A r s c).submatrix f g).updateRow a v) =
        (A.submatrix f g).updateRow a v := by
    ext b j
    by_cases hb : b = a
    · simp [Matrix.updateRow, Function.update, hb]
    · simp [Matrix.updateRow, Function.update, hb, rowAdd, hf b hb]
  unfold rowMinor
  rw [hbase]
  by_cases hi : i = r
  · subst i
    simp only [rowAdd, ite_eq_left]
    change ((A.submatrix f g).updateRow a
      ((fun j => A r (g j)) + c • (fun j => A s (g j)))).det = _
    rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
  · simp only [rowAdd, ite_eq_right hi]

private theorem run_rowMinor (Q R : State m n) (r s : Fin m)
    (ops : List (Op m n)) (hops : ∀ op ∈ ops, RowPair r s op)
    (f : α → Fin m) (g : α → Fin n) (a : α)
    (hf : ∀ b, b ≠ a → f b ≠ r ∧ f b ≠ s)
    (hR : ∀ i j, R.S i j = rowMinor Q.S f g a i) :
    ∀ i j, (run R ops).S i j = rowMinor (run Q ops).S f g a i := by
  induction ops generalizing Q R with
  | nil => exact hR
  | cons op ops ih =>
      apply ih (step Q op) (step R op) (fun x hx => hops x (by simp [hx]))
      have hop := hops op (by simp)
      cases op with
      | col u v huv c => exact False.elim hop
      | row u v huv c =>
          have hfixed : ∀ b, b ≠ a → f b ≠ u := by
            rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact fun b hb => (hf b hb).1
            · exact fun b hb => (hf b hb).2
          intro i j
          simp only [step, rowMinor_rowAdd Q.S f g a u v c hfixed i]
          by_cases hi : i = u <;> simp only [rowAdd, hi, hR, ↓reduceIte]

/-- Replay all the variable-row minors at every prefix of the actual computed
Euclidean trace. Fixed rows avoid both mixed rows; one mixed row replaces
the distinguished slot. No divisibility premise is imposed. -/
theorem gcdTrace_prefix_rowMinor (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (x y : ℤ) (t : ℕ) (f : α → Fin m) (g : α → Fin n) (a : α)
    (hf : ∀ b, b ≠ a → f b ≠ r ∧ f b ≠ s) (i : Fin m) :
    rowMinor (run Q ((gcdTrace r s h x y).take t)).S f g a i =
      (run (initial (fun i _ => rowMinor Q.S f g a i))
        ((gcdTrace r s h x y).take t)).S i (g a) := by
  symm
  exact run_rowMinor Q _ r s _ (fun op hop =>
    gcdTrace_rowPair r s h x y op (List.mem_of_mem_take hop)) f g a hf
      (fun _ _ => rfl) i (g a)

/-- Every temporary selected minor is bounded by one incoming minor-height
factor and the actual Euclidean trace factor. The charge is independent of
the minor's order. -/
theorem gcdTrace_prefix_minor_height (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (x y : ℤ) (t H : ℕ) (hH : 1 ≤ H)
    (f : α → Fin m) (g : α → Fin n) (a : α)
    (hf : ∀ b, b ≠ a → f b ≠ r ∧ f b ≠ s)
    (hM : ∀ i, (rowMinor Q.S f g a i).natAbs ≤ H) (i : Fin m) :
    (rowMinor (run Q ((gcdTrace r s h x y).take t)).S f g a i).natAbs ≤
      H * max 1 (max x.natAbs y.natAbs) *
        2 ^ (gcdTrace (n := n) r s h x y).length := by
  rw [gcdTrace_prefix_rowMinor Q r s h x y t f g a hf i]
  have hid {k : ℕ} : ∀ i j : Fin k, ((1 : Matrix (Fin k) (Fin k) ℤ) i j).natAbs ≤ H := by
    intro i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, hH]
  have hinit : Bounded (initial (fun i (_ : Fin n) => rowMinor Q.S f g a i)) H :=
    ⟨hid, hid, hid, hid, fun i _ => hM i⟩
  have hb := SmithPivotLinearBounds.gcdTrace_prefix_height_bound
    (initial (fun i _ => rowMinor Q.S f g a i)) r s h x y H t
    hinit
  exact hb.S i (g a)

/-- A common incoming minor exponent `d` grows by at most `9c` during one
computed pivot on a pair of magnitude width `c`, independently of minor order.
Every addition prefix, including unfinished signed swaps, is covered. -/
theorem gcdTrace_prefix_minor_pow_bound (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (x y : ℤ) (d c t : ℕ) (hx : x.natAbs < 2 ^ c) (hy : y.natAbs < 2 ^ c)
    (f : α → Fin m) (g : α → Fin n) (a : α)
    (hf : ∀ b, b ≠ a → f b ≠ r ∧ f b ≠ s)
    (hM : ∀ i, (rowMinor Q.S f g a i).natAbs ≤ 2 ^ d) (i : Fin m) :
    (rowMinor (run Q ((gcdTrace r s h x y).take t)).S f g a i).natAbs ≤
      2 ^ (d + 9 * c) := by
  rw [gcdTrace_prefix_rowMinor Q r s h x y t f g a hf i]
  exact (SmithPivotLinearBounds.gcdTrace_prefix_pow_bound
    (initial (fun i _ => rowMinor Q.S f g a i)) r s h x y d c t
      (initial_pow_bound _ d (fun i _ => hM i)) hx hy).S i (g a)

/-- The bound uses the selected entries of the incoming matrix, rather than
extra scalar parameters. It includes an all-zero selected pair. -/
theorem pivot_minor_pow_bound (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j : Fin n) (d c : ℕ)
    (hx : (Q.S r j).natAbs < 2 ^ c) (hy : (Q.S s j).natAbs < 2 ^ c)
    (f : α → Fin m) (g : α → Fin n) (a : α)
    (hf : ∀ b, b ≠ a → f b ≠ r ∧ f b ≠ s)
    (hM : ∀ i, (rowMinor Q.S f g a i).natAbs ≤ 2 ^ d) (i : Fin m) :
    (rowMinor (pivot Q r s h j).S f g a i).natAbs ≤ 2 ^ (d + 9 * c) := by
  simpa only [List.take_length, pivot] using
    gcdTrace_prefix_minor_pow_bound Q r s h _ _ d c
      (gcdTrace (n := n) r s h (Q.S r j) (Q.S s j)).length hx hy f g a hf hM i

/-- The actual divisibility-aware reducer has the same minor transport.
This includes its exact-division shortcut and all prefixes of either branch. -/
theorem reduceRowsTrace_prefix_rowMinor (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j : Fin n) (t : ℕ) (f : α → Fin m) (g : α → Fin n) (a : α)
    (hf : ∀ b, b ≠ a → f b ≠ r ∧ f b ≠ s) (i : Fin m) :
    rowMinor (run Q ((reduceRowsTrace Q r s h j).take t)).S f g a i =
      (run (initial (fun i _ => rowMinor Q.S f g a i))
        ((reduceRowsTrace Q r s h j).take t)).S i (g a) := by
  have hops : ∀ op ∈ reduceRowsTrace Q r s h j, RowPair r s op := by
    unfold reduceRowsTrace
    split_ifs
    · intro op hop
      simp only [List.mem_singleton] at hop
      subst op
      exact Or.inr ⟨rfl, rfl⟩
    · exact gcdTrace_rowPair r s h _ _
  symm
  exact run_rowMinor Q _ r s _ (fun op hop => hops op (List.mem_of_mem_take hop))
    f g a hf (fun _ _ => rfl) i (g a)

/-- Incoming minor width is charged once for a complete actual reducer,
independently of the order of the selected minors. -/
theorem reduceRowsTrace_prefix_minor_pow_bound (Q : State m n)
    (r s : Fin m) (h : r ≠ s) (j : Fin n) (d c t : ℕ) (hc : 0 < c)
    (hx : (Q.S r j).natAbs < 2 ^ c) (hy : (Q.S s j).natAbs < 2 ^ c)
    (f : α → Fin m) (g : α → Fin n) (a : α)
    (hf : ∀ b, b ≠ a → f b ≠ r ∧ f b ≠ s)
    (hM : ∀ i, (rowMinor Q.S f g a i).natAbs ≤ 2 ^ d) (i : Fin m) :
    (rowMinor (run Q ((reduceRowsTrace Q r s h j).take t)).S f g a i).natAbs ≤
      2 ^ (d + 9 * c) := by
  rw [reduceRowsTrace_prefix_rowMinor Q r s h j t f g a hf i]
  have hinit := initial_pow_bound (fun i (_ : Fin n) => rowMinor Q.S f g a i) d
    (fun i _ => hM i)
  unfold reduceRowsTrace
  split_ifs
  · cases t with
    | zero =>
        exact (hM i).trans (Nat.pow_le_pow_right (by decide) (by omega))
    | succ t =>
        have hs := step_pow_bound _
          (.row s r h.symm (-(Q.S s j).tdiv (Q.S r j))) d c hinit (by
            simpa only [coefficient, Int.natAbs_neg] using
              (Int.natAbs_tdiv_le_natAbs (Q.S s j) (Q.S r j)).trans hy.le)
        have hle : d + c + 1 ≤ d + 9 * c := by omega
        simpa only [List.take_succ_cons, List.take_nil, run] using
          (hs.S i (g a)).trans (Nat.pow_le_pow_right (by decide) hle)
  · exact (SmithPivotLinearBounds.gcdTrace_prefix_pow_bound _ r s h _ _ d c t
      hinit hx hy).S i (g a)

theorem reduceRows_minor_pow_bound (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j : Fin n) (d c : ℕ) (hc : 0 < c)
    (hx : (Q.S r j).natAbs < 2 ^ c) (hy : (Q.S s j).natAbs < 2 ^ c)
    (f : α → Fin m) (g : α → Fin n) (a : α)
    (hf : ∀ b, b ≠ a → f b ≠ r ∧ f b ≠ s)
    (hM : ∀ i, (rowMinor Q.S f g a i).natAbs ≤ 2 ^ d) (i : Fin m) :
    (rowMinor (reduceRows Q r s h j).S f g a i).natAbs ≤ 2 ^ (d + 9 * c) := by
  simpa only [List.take_length, reduceRowsTrace_run] using
    reduceRowsTrace_prefix_minor_pow_bound Q r s h j d c
      (reduceRowsTrace Q r s h j).length hc hx hy f g a hf hM i

/-- The transposed determinant replaces one column, in its original slot. -/
def colMinor (A : Matrix (Fin m) (Fin n) ℤ) (f : α → Fin m) (g : α → Fin n)
    (a : α) (j : Fin n) : ℤ := rowMinor A.transpose g f a j

theorem colMinor_self (A : Matrix (Fin m) (Fin n) ℤ)
    (f : α → Fin m) (g : α → Fin n) (a : α) :
    colMinor A f g a (g a) = (A.submatrix f g).det := by
  rw [colMinor, rowMinor_self, ← Matrix.transpose_submatrix, Matrix.det_transpose]

/-- Column-operation prefixes of the actual reducer obey the same bound,
without a square-shape assumption. -/
theorem reduceColsTrace_prefix_minor_pow_bound (Q : State m n)
    (r s : Fin n) (h : r ≠ s) (j : Fin m) (d c t : ℕ) (hc : 0 < c)
    (hx : (Q.S j r).natAbs < 2 ^ c) (hy : (Q.S j s).natAbs < 2 ^ c)
    (f : α → Fin m) (g : α → Fin n) (a : α)
    (hg : ∀ b, b ≠ a → g b ≠ r ∧ g b ≠ s)
    (hM : ∀ l, (colMinor Q.S f g a l).natAbs ≤ 2 ^ d) (l : Fin n) :
    (colMinor (transposeState
      (run (transposeState Q) ((reduceRowsTrace (transposeState Q) r s h j).take t))).S
        f g a l).natAbs ≤ 2 ^ (d + 9 * c) :=
  reduceRowsTrace_prefix_minor_pow_bound (transposeState Q) r s h j d c t hc hx hy
    g f a hg hM l

/-- Charge incoming minors to the incoming entries by the standard determinant
bound. This statement contains no assumed global minor-growth invariant. -/
theorem rowMinor_entry_pow_bound (A : Matrix (Fin m) (Fin n) ℤ)
    (w : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ w)
    (f : α → Fin m) (g : α → Fin n) (a : α) (i : Fin m) :
    (rowMinor A f g a i).natAbs ≤ 2 ^ (Fintype.card α * (w + Fintype.card α)) := by
  classical
  let B := (A.submatrix f g).updateRow a (fun j => A i (g j))
  have hB : ∀ b j, (B b j).natAbs ≤ 2 ^ w := by
    intro b j
    by_cases hb : b = a
    · subst b
      simpa only [B, Matrix.updateRow_self] using hA i (g j)
    · simpa only [B, Matrix.updateRow_ne hb, Matrix.submatrix_apply] using hA (f b) (g j)
  let e := (Fintype.equivFin α).symm
  have hd := RationalWitnessBounds.det_natAbs_le_pow (B.submatrix e e)
    (fun b j => hB (e b) (e j))
  rw [Matrix.det_submatrix_equiv_self] at hd
  exact hd.trans (Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left
      (Nat.size_le.mpr Nat.lt_two_pow_self) w)))

/-- In the actual complete dense input length `s`, every one-row-replacement
minor of order at most `s` has at most `2s²+9s+1` magnitude bits during one
actual reducer. Unary dimension headers pay for all orders of genuine minors. -/
theorem dense_reduceRowsTrace_prefix_minor_bits (A : Dense)
    (r s : Fin A.rows) (h : r ≠ s) (j : Fin A.cols) (t : ℕ)
    (f : α → Fin A.rows) (g : α → Fin A.cols) (a : α)
    (hf : ∀ b, b ≠ a → f b ≠ r ∧ f b ≠ s)
    (horder : Fintype.card α ≤ (SmithEncoding.encode A).length) (i : Fin A.rows) :
    (rowMinor (run (initial A.toMatrix)
      ((reduceRowsTrace (initial A.toMatrix) r s h j).take t)).S f g a i).natAbs.size ≤
      2 * (SmithEncoding.encode A).length ^ 2 +
        9 * (SmithEncoding.encode A).length + 1 := by
  let L := (SmithEncoding.encode A).length
  have hA : ∀ u v, (A.toMatrix u v).natAbs < 2 ^ L :=
    fun u v => Nat.size_le.mp (SmithIsolationCount.entry_size_le_input_length A u v)
  have hL : 0 < L := by
    have := SmithEncoding.dimensions_le_length A
    omega
  have hb := reduceRowsTrace_prefix_minor_pow_bound (initial A.toMatrix) r s h j
    (Fintype.card α * (L + Fintype.card α)) L t hL (hA r j) (hA s j) f g a hf
      (fun u => rowMinor_entry_pow_bound A.toMatrix L (fun u v => (hA u v).le) f g a u) i
  have he : Fintype.card α * (L + Fintype.card α) + 9 * L ≤ 2 * L ^ 2 + 9 * L := by
    nlinarith [Nat.mul_le_mul horder (Nat.add_le_add_left horder L)]
  have hs := Nat.size_le_size (hb.trans (Nat.pow_le_pow_right (by decide) he))
  simpa only [Nat.size_pow] using hs

/-- A genuine selected minor containing the pivot row and omitting the other
mixed row has the binary bound in complete original dense input length.
Injectivity and the paid dimension header supply the order bound internally. -/
theorem dense_selected_minor_prefix_bits (A : Dense)
    (r s : Fin A.rows) (h : r ≠ s) (j : Fin A.cols) (t : ℕ)
    (f : α → Fin A.rows) (g : α → Fin A.cols) (a : α)
    (hinj : Function.Injective f) (ha : f a = r) (hs : ∀ b, f b ≠ s) :
    (((run (initial A.toMatrix)
      ((reduceRowsTrace (initial A.toMatrix) r s h j).take t)).S.submatrix f g).det).natAbs.size ≤
      2 * (SmithEncoding.encode A).length ^ 2 +
        9 * (SmithEncoding.encode A).length + 1 := by
  rw [← rowMinor_self _ f g a]
  apply dense_reduceRowsTrace_prefix_minor_bits
  · intro b hb
    exact ⟨fun he => hb (hinj (he.trans ha.symm)), hs b⟩
  · have hcard := Fintype.card_le_of_injective f hinj
    have hdim := SmithEncoding.dimensions_le_length A
    simp only [Fintype.card_fin] at hcard
    omega

private def mixingMatrix : Matrix (Fin 3) (Fin 2) ℤ := !![2, 1; 3, 0; 0, 1]

/-- A computed nondivisible pivot really changes a minor omitting the mixed-in
row. Thus preservation of a single original minor cannot replace transport. -/
theorem outside_mix_changes_minor :
    ∃ A : Matrix (Fin 3) (Fin 2) ℤ,
      ¬ A 0 0 ∣ A 1 0 ∧ (A.submatrix ![0, 2] id).det = 2 ∧
        ((reduceRows (initial A) 0 1 (by decide) 0).S.submatrix ![0, 2] id).det = -1 := by
  refine ⟨mixingMatrix, ?_⟩
  norm_num [mixingMatrix, reduceRows, pivot, initial, gcdTrace, pairStep, run, step,
    rowAdd, Matrix.det_fin_two]

-- The bound includes an all-zero selected pair with zero scalar width.
example (Q : State m n) (r s : Fin m) (h : r ≠ s) (d t : ℕ)
    (f : α → Fin m) (g : α → Fin n) (a : α)
    (hf : ∀ b, b ≠ a → f b ≠ r ∧ f b ≠ s)
    (hM : ∀ i, (rowMinor Q.S f g a i).natAbs ≤ 2 ^ d) (i : Fin m) :
    (rowMinor (run Q ((gcdTrace r s h 0 0).take t)).S f g a i).natAbs ≤ 2 ^ d := by
  simpa only [Nat.mul_zero, Nat.add_zero] using
    gcdTrace_prefix_minor_pow_bound Q r s h 0 0 d 0 t (by decide) (by decide)
      f g a hf hM i

-- Universal-prefix specialization: negative, nonunit and rectangular input.
example (t : ℕ) :
    let A : Dense := ⟨3, 2, [-2, 1, -3, 0, 0, 1], rfl⟩
    (rowMinor (run (initial A.toMatrix)
      ((reduceRowsTrace (initial A.toMatrix) 0 1 (by decide) 0).take t)).S
        ![0, 2] id 0 0).natAbs.size ≤
      2 * (SmithEncoding.encode A).length ^ 2 + 9 * (SmithEncoding.encode A).length + 1 := by
  dsimp only
  apply dense_reduceRowsTrace_prefix_minor_bits
  · decide
  · have hd := SmithEncoding.dimensions_le_length
      (⟨3, 2, [-2, 1, -3, 0, 0, 1], rfl⟩ : Dense)
    norm_num only [Fintype.card_fin]
    omega

#print axioms rowMinor
#print axioms rowMinor_self
#print axioms rowMinor_rowAdd
#print axioms gcdTrace_prefix_rowMinor
#print axioms gcdTrace_prefix_minor_height
#print axioms gcdTrace_prefix_minor_pow_bound
#print axioms pivot_minor_pow_bound
#print axioms reduceRowsTrace_prefix_rowMinor
#print axioms reduceRowsTrace_prefix_minor_pow_bound
#print axioms reduceRows_minor_pow_bound
#print axioms colMinor
#print axioms colMinor_self
#print axioms reduceColsTrace_prefix_minor_pow_bound
#print axioms rowMinor_entry_pow_bound
#print axioms dense_reduceRowsTrace_prefix_minor_bits
#print axioms dense_selected_minor_prefix_bits
#print axioms outside_mix_changes_minor

end PhdThesisLean.SmithPivotMinorTransport
