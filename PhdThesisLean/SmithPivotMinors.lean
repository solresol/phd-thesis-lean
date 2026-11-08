import PhdThesisLean.SmithReduction
import PhdThesisLean.SmithIsolationCount

/-!
# Exact determinantal numerators in the existing Smith pair reducer

Every addition prefix of a two-row Euclidean pivot preserves both its selected
two-column minors in `S` and the mixed minors between `S` and `U`. Once the
selected entry is cleared, the signed gcd pivot times each target-row entry is
exactly the incoming minor. The transposed statement covers `S` and `V` for a
column reduction. These are local identities and target-row bounds, not a
global minor invariant for the alternating diagonalizer or machine-time bounds.
-/

namespace PhdThesisLean.SmithPivotMinors

open Matrix SmithTrace SmithPivot SmithReduction SmithRowOperations SmithEncoding

variable {m n : ℕ}

private def rowPair (r s : Fin m) : Op m n → Prop
  | .row u v _ _ => (u = r ∧ v = s) ∨ (u = s ∧ v = r)
  | .col _ _ _ _ => False

private theorem gcdTrace_rowPair (r s : Fin m) (h : r ≠ s) (a b : ℤ) :
    ∀ op ∈ gcdTrace (n := n) r s h a b, rowPair r s op := by
  rw [gcdTrace]
  split_ifs with hb
  · simp
  · intro op hop
    rcases List.mem_append.mp hop with hop | hop
    · simp only [pairStep, List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl | rfl <;> simp [rowPair]
    · exact gcdTrace_rowPair r s h b (-(a.tmod b)) op hop
termination_by b.natAbs
decreasing_by exact remainder_descent a b hb

private theorem step_minors (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (op : Op m n) (hop : rowPair r s op) (j l : Fin n) (c : Fin m) :
    ((step Q op).S r j * (step Q op).S s l -
        (step Q op).S s j * (step Q op).S r l =
      Q.S r j * Q.S s l - Q.S s j * Q.S r l) ∧
    ((step Q op).S r j * (step Q op).U s c -
        (step Q op).S s j * (step Q op).U r c =
      Q.S r j * Q.U s c - Q.S s j * Q.U r c) := by
  cases op with
  | col u v huv k => exact False.elim hop
  | row u v huv k =>
      rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        constructor <;> simp [step, rowAdd, h, h.symm] <;> ring

private theorem run_minors (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (ops : List (Op m n)) (hops : ∀ op ∈ ops, rowPair r s op)
    (j l : Fin n) (c : Fin m) :
    ((run Q ops).S r j * (run Q ops).S s l -
        (run Q ops).S s j * (run Q ops).S r l =
      Q.S r j * Q.S s l - Q.S s j * Q.S r l) ∧
    ((run Q ops).S r j * (run Q ops).U s c -
        (run Q ops).S s j * (run Q ops).U r c =
      Q.S r j * Q.U s c - Q.S s j * Q.U r c) := by
  induction ops generalizing Q with
  | nil => exact ⟨rfl, rfl⟩
  | cons op ops ih =>
      have ht := ih (step Q op) (fun x hx => hops x (by simp [hx]))
      have hs := step_minors Q r s h op (hops op (by simp)) j l c
      exact ⟨ht.1.trans hs.1, ht.2.trans hs.2⟩

/-- Every actual addition prefix, including unfinished signed swaps, preserves
the selected `S` minors and the mixed `S,U` minors. Scalar trace parameters may
be arbitrary here; clearing below uses the actual selected entries. -/
theorem gcdTrace_prefix_minors (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (a b : ℤ) (t : ℕ) (j l : Fin n) (c : Fin m) :
    let R := run Q ((gcdTrace r s h a b).take t)
    (R.S r j * R.S s l - R.S s j * R.S r l =
      Q.S r j * Q.S s l - Q.S s j * Q.S r l) ∧
    (R.S r j * R.U s c - R.S s j * R.U r c =
      Q.S r j * Q.U s c - Q.S s j * Q.U r c) :=
  run_minors Q r s h _ (fun op hop =>
    gcdTrace_rowPair r s h a b op (List.mem_of_mem_take hop)) j l c

/-- Exact target numerators for the complete existing Euclidean pivot, using
its signed output pivot. No nonzero, rank or square premise is needed. -/
theorem pivot_target_numerators (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j l : Fin n) (c : Fin m) :
    let R := pivot Q r s h j
    (R.S r j * R.S s l = Q.S r j * Q.S s l - Q.S s j * Q.S r l) ∧
    (R.S r j * R.U s c = Q.S r j * Q.U s c - Q.S s j * Q.U r c) := by
  have hm := run_minors Q r s h _ (gcdTrace_rowPair r s h (Q.S r j) (Q.S s j)) j l c
  have hz := (pivot_correct Q r s h j).1
  dsimp only [pivot] at hz ⊢
  simpa only [hz, zero_mul, sub_zero] using hm

/-- The exact-division shortcut and Euclidean branch have the same numerator
identity. Thus this describes the reducer actually used by the sweeps. -/
theorem reduceRows_target_numerators (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j l : Fin n) (c : Fin m) :
    let R := reduceRows Q r s h j
    (R.S r j * R.S s l = Q.S r j * Q.S s l - Q.S s j * Q.S r l) ∧
    (R.S r j * R.U s c = Q.S r j * Q.U s c - Q.S s j * Q.U r c) := by
  unfold reduceRows
  split_ifs with hd
  · have hdiv := Int.tdiv_mul_cancel hd
    constructor
    · simp only [step, rowAdd, ite_eq_left, ite_eq_right h]
      linear_combination -(Q.S r l) * hdiv
    · simp only [step, rowAdd, ite_eq_left, ite_eq_right h]
      linear_combination -(Q.U r c) * hdiv
  · exact pivot_target_numerators Q r s h j l c

/-- Column reductions inherit the exact `S,V` numerator formulas by transpose.
The forward column map uses column indices, without square input assumptions. -/
theorem reduceCols_target_numerators (Q : State m n) (r s : Fin n) (h : r ≠ s)
    (i l : Fin m) (c : Fin n) :
    let R := reduceCols Q r s h i
    (R.S i r * R.S l s = Q.S i r * Q.S l s - Q.S i s * Q.S l r) ∧
    (R.S i r * R.V c s = Q.S i r * Q.V c s - Q.S i s * Q.V c r) :=
  reduceRows_target_numerators (transposeState Q) r s h i l c

private theorem numerator_natAbs_le (a b x y g z : ℤ)
    (heq : g * z = a * y - b * x) :
    g.natAbs * z.natAbs ≤ a.natAbs * y.natAbs + b.natAbs * x.natAbs := by
  calc
    g.natAbs * z.natAbs = (a * y - b * x).natAbs := by
      rw [← Int.natAbs_mul, heq]
    _ ≤ (a * y).natAbs + (b * x).natAbs := Int.natAbs_sub_le _ _
    _ = _ := by rw [Int.natAbs_mul, Int.natAbs_mul]

/-- Retain the gcd divisor in both target-row magnitude bounds; do not charge
every Euclidean quotient afresh. Both source entries and map entries appear. -/
theorem reduceRows_target_scaled_bounds (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j l : Fin n) (c : Fin m) :
    let g := Int.gcd (Q.S r j) (Q.S s j)
    let R := reduceRows Q r s h j
    (g * (R.S s l).natAbs ≤
      (Q.S r j).natAbs * (Q.S s l).natAbs + (Q.S s j).natAbs * (Q.S r l).natAbs) ∧
    (g * (R.U s c).natAbs ≤
      (Q.S r j).natAbs * (Q.U s c).natAbs + (Q.S s j).natAbs * (Q.U r c).natAbs) := by
  obtain ⟨hS, hU⟩ := reduceRows_target_numerators Q r s h j l c
  have hg := (reduceRows_correct Q r s h j).2.1
  constructor
  · simpa only [hg] using numerator_natAbs_le _ _ _ _ _ _ hS
  · simpa only [hg] using numerator_natAbs_le _ _ _ _ _ _ hU

/-- For a nonzero selected pair, the target row has height at most `2*H*K`
in `S` and at most `2*H*F` in `U`. These are complete-pair endpoint bounds;
the existing prefix theorem is still needed for temporary arithmetic growth. -/
theorem reduceRows_target_bounds (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j : Fin n) (H K F : ℕ) (hne : Q.S r j ≠ 0 ∨ Q.S s j ≠ 0)
    (ha : (Q.S r j).natAbs ≤ H) (hb : (Q.S s j).natAbs ≤ H)
    (hS : ∀ l, (Q.S r l).natAbs ≤ K ∧ (Q.S s l).natAbs ≤ K)
    (hU : ∀ c, (Q.U r c).natAbs ≤ F ∧ (Q.U s c).natAbs ≤ F) :
    (∀ l, ((reduceRows Q r s h j).S s l).natAbs ≤ 2 * H * K) ∧
    (∀ c, ((reduceRows Q r s h j).U s c).natAbs ≤ 2 * H * F) := by
  have hg : 0 < Int.gcd (Q.S r j) (Q.S s j) := by
    rcases hne with ha | hb
    · exact Int.gcd_pos_of_ne_zero_left _ ha
    · exact Int.gcd_pos_of_ne_zero_right _ hb
  constructor
  · intro l
    have hs := (reduceRows_target_scaled_bounds Q r s h j l r).1
    have hprod : (Q.S r j).natAbs * (Q.S s l).natAbs +
        (Q.S s j).natAbs * (Q.S r l).natAbs ≤ H * K + H * K :=
      Nat.add_le_add (Nat.mul_le_mul ha (hS l).2) (Nat.mul_le_mul hb (hS l).1)
    have hz := Nat.le_mul_of_pos_left ((reduceRows Q r s h j).S s l).natAbs hg
    exact hz.trans ((hs.trans hprod).trans_eq (by ring))
  · intro c
    have hu := (reduceRows_target_scaled_bounds Q r s h j j c).2
    have hprod : (Q.S r j).natAbs * (Q.U s c).natAbs +
        (Q.S s j).natAbs * (Q.U r c).natAbs ≤ H * F + H * F :=
      Nat.add_le_add (Nat.mul_le_mul ha (hU c).2) (Nat.mul_le_mul hb (hU c).1)
    have hz := Nat.le_mul_of_pos_left ((reduceRows Q r s h j).U s c).natAbs hg
    exact hz.trans ((hu.trans hprod).trans_eq (by ring))

/-- Starting from identity maps, the cleared target row's forward coefficients
are bounded by the two selected magnitudes themselves. The gcd factor is kept,
including the all-zero pair, where this scaled statement is vacuous. -/
theorem initial_target_forward_scaled_bound (A : Matrix (Fin m) (Fin n) ℤ)
    (r s : Fin m) (h : r ≠ s) (j : Fin n) (c : Fin m) :
    Int.gcd (A r j) (A s j) * ((reduceRows (initial A) r s h j).U s c).natAbs ≤
      max (A r j).natAbs (A s j).natAbs := by
  have hb := (reduceRows_target_scaled_bounds (initial A) r s h j j c).2
  by_cases hcr : r = c
  · subst c
    simp only [initial, Matrix.one_apply, ite_eq_left, ite_eq_right h.symm,
      Int.natAbs_zero, Int.natAbs_one, mul_zero, mul_one, zero_add] at hb
    exact hb.trans (le_max_right _ _)
  · by_cases hcs : s = c
    · subst c
      simp only [initial, Matrix.one_apply, ite_eq_left, ite_eq_right h,
        Int.natAbs_zero, Int.natAbs_one, mul_zero, mul_one, add_zero] at hb
      exact hb.trans (le_max_left _ _)
    · simp only [initial, Matrix.one_apply, ite_eq_right hcr, ite_eq_right hcs,
        Int.natAbs_zero, mul_zero, add_zero] at hb
      exact hb.trans (Nat.zero_le _)

/-- Charge the cleared forward row to the original dense input bits. This
unconditional endpoint statement includes an all-zero selected pair, which
leaves the identity forward row fixed. It bounds only that target row. -/
theorem dense_target_forward_bound (A : Dense) (r s : Fin A.rows) (h : r ≠ s)
    (j : Fin A.cols) (c : Fin A.rows) :
    ((reduceRows (initial A.toMatrix) r s h j).U s c).natAbs ≤
      2 ^ (SmithEncoding.encode A).length := by
  by_cases hz : A.toMatrix r j = 0 ∧ A.toMatrix s j = 0
  · have hid : (reduceRows (initial A.toMatrix) r s h j).U s c =
        (1 : Matrix (Fin A.rows) (Fin A.rows) ℤ) s c := by
      simp [reduceRows, initial, hz.1, hz.2, step, rowAdd]
    rw [hid]
    by_cases hsc : s = c
    · simpa only [Matrix.one_apply, ite_eq_left hsc, Int.natAbs_one] using
        Nat.one_le_pow (SmithEncoding.encode A).length 2 (by decide)
    · simp [hsc]
  · have hg : 0 < Int.gcd (A.toMatrix r j) (A.toMatrix s j) := by
      by_cases ha : A.toMatrix r j = 0
      · exact Int.gcd_pos_of_ne_zero_right _ (by tauto)
      · exact Int.gcd_pos_of_ne_zero_left _ ha
    have hs := initial_target_forward_scaled_bound A.toMatrix r s h j c
    have hentry (i : Fin A.rows) : (A.toMatrix i j).natAbs ≤
        2 ^ (SmithEncoding.encode A).length :=
      (Nat.size_le.mp (SmithIsolationCount.entry_size_le_input_length A i j)).le
    exact (Nat.le_mul_of_pos_left _ hg).trans
      (hs.trans (max_le (hentry r) (hentry s)))

/-- The cleared target's forward coefficients use at most `s+1` binary
magnitude bits in complete original input length `s`. This is an endpoint
size bound, without a serializer or arithmetic-machine runtime claim. -/
theorem dense_target_forward_bits (A : Dense) (r s : Fin A.rows) (h : r ≠ s)
    (j : Fin A.cols) (c : Fin A.rows) :
    ((reduceRows (initial A.toMatrix) r s h j).U s c).natAbs.size ≤
      (SmithEncoding.encode A).length + 1 := by
  simpa only [Nat.size_pow] using Nat.size_le_size (dense_target_forward_bound A r s h j c)

-- An exact parametric obstruction: controlling only transformed entries and
-- their minors cannot control forward maps for arbitrary valid traces. This
-- trace is not claimed to be generated by the diagonalizer.
/-- A rank-one input is fixed by arbitrarily large determinant-one shears.
The actual controller needs additional invariants beyond minors of `S`. -/
theorem fixed_column_shear (t : ℤ) :
    let A : Matrix (Fin 2) (Fin 1) ℤ := !![1; 0]
    let Q := run (initial A) [.row 0 1 (by decide) t]
    Q.S = A ∧ Q.U 0 1 = t ∧ Invariant A Q := by
  refine ⟨?_, ?_, run_invariant (initial_invariant _) _⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [run, step, initial, rowAdd]
  · simp [run, step, initial, rowAdd]

#print axioms gcdTrace_prefix_minors
#print axioms pivot_target_numerators
#print axioms reduceRows_target_numerators
#print axioms reduceCols_target_numerators
#print axioms reduceRows_target_scaled_bounds
#print axioms reduceRows_target_bounds
#print axioms initial_target_forward_scaled_bound
#print axioms dense_target_forward_bound
#print axioms dense_target_forward_bits
#print axioms fixed_column_shear

end PhdThesisLean.SmithPivotMinors
