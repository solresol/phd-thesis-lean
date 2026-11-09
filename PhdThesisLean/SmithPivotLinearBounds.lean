import PhdThesisLean.SmithPivotBounds

/-!
# Linear local bit widths for the computed Euclidean pivot

The quotient in a completed pair step is paid for by the decrease of the
selected magnitudes, rather than charging its full bit width at every step.
This bounds every addition prefix of the actual trace on all five matrices.
It does not bound repeated sweeps, the complete diagonalizer, or machine time.
-/

namespace PhdThesisLean.SmithPivotLinearBounds

open Matrix SmithTrace SmithPivot SmithPivotBounds SmithRowOperations SmithEncoding
  SmithDecomposition

variable {m n : ℕ}

private theorem step_bound (Q : State m n) (op : Op m n) (H : ℕ)
    (hQ : Bounded Q H) :
    Bounded (step Q op) (((coefficient op).natAbs + 1) * H) := by
  have hw : H ≤ ((coefficient op).natAbs + 1) * H := by
    simpa using Nat.mul_le_mul_right H (Nat.le_add_left 1 (coefficient op).natAbs)
  have hc {u v : ℕ} (A : Matrix (Fin u) (Fin v) ℤ) (r s : Fin v) (c : ℤ)
      (hA : ∀ i j, (A i j).natAbs ≤ H) :
      ∀ i j, (colAdd A r s c i j).natAbs ≤ (c.natAbs + 1) * H :=
    fun i j => rowAdd_natAbs_le A.transpose r s c H c.natAbs
      (fun j i => hA i j) le_rfl j i
  cases op with
  | row r s h c =>
      exact ⟨rowAdd_natAbs_le Q.U r s c H c.natAbs hQ.U le_rfl,
        by simpa [coefficient, step] using hc Q.Uinv s r (-c) hQ.Uinv,
        fun i j => (hQ.V i j).trans hw, fun i j => (hQ.Vinv i j).trans hw,
        rowAdd_natAbs_le Q.S r s c H c.natAbs hQ.S le_rfl⟩
  | col r s h c =>
      exact ⟨fun i j => (hQ.U i j).trans hw, fun i j => (hQ.Uinv i j).trans hw,
        hc Q.V r s c hQ.V,
        by simpa [coefficient, step] using
          rowAdd_natAbs_le Q.Vinv s r (-c) H c.natAbs hQ.Vinv (by simp),
        hc Q.S r s c hQ.S⟩

private theorem linear_bound (x y q : ℤ) (H : ℕ)
    (hx : x.natAbs ≤ H) (hy : y.natAbs ≤ H) :
    (x + q * y).natAbs ≤ (q.natAbs + 1) * H := by
  calc
    _ ≤ x.natAbs + (q * y).natAbs := Int.natAbs_add_le _ _
    _ ≤ H + q.natAbs * H := by rw [Int.natAbs_mul]; gcongr
    _ = _ := by ring

/-- A completed quotient subtraction and signed swap has only linear
dependence on the quotient, for the inverse map as well as the forward map. -/
theorem pairStep_bound (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (q : ℤ) (H : ℕ) (hQ : Bounded Q H) :
    Bounded (run Q (pairStep r s h q)) ((q.natAbs + 1) * H) := by
  have hw : H ≤ (q.natAbs + 1) * H := by
    simpa using Nat.mul_le_mul_right H (Nat.le_add_left 1 q.natAbs)
  have hr {k : ℕ} (A : Matrix (Fin m) (Fin k) ℤ)
      (hA : ∀ i j, (A i j).natAbs ≤ H) (i : Fin m) (j : Fin k) :
      (rowAdd (rowAdd (rowAdd (rowAdd A r s (-q)) r s 1) s r (-1))
        r s 1 i j).natAbs ≤ (q.natAbs + 1) * H := by
    by_cases hir : i = r
    · subst i
      convert (hA s j).trans hw using 1
      congr 1
      simp [rowAdd, h, h.symm]
      ring
    · by_cases his : i = s
      · subst i
        convert linear_bound (-(A r j)) (A s j) q H
          (by simpa using hA r j) (hA s j) using 1
        congr 1
        simp [rowAdd, h.symm]
        ring
      · simpa [rowAdd, hir, his] using (hA i j).trans hw
  have hi (i j : Fin m) :
      ((run Q (pairStep r s h q)).Uinv i j).natAbs ≤ (q.natAbs + 1) * H := by
    by_cases hjr : j = r
    · subst j
      convert linear_bound (Q.Uinv i s) (Q.Uinv i r) q H
        (hQ.Uinv i s) (hQ.Uinv i r) using 1
      congr 1
      simp [pairStep, run, step, colAdd, h]
    · by_cases hjs : j = s
      · subst j
        have he : (run Q (pairStep r s h q)).Uinv i s = -(Q.Uinv i r) := by
          simp [pairStep, run, step, colAdd, h, h.symm]
          ring
        rw [he, Int.natAbs_neg]
        exact (hQ.Uinv i r).trans hw
      · simpa [pairStep, run, step, colAdd, hjr, hjs] using
          (hQ.Uinv i j).trans hw
  exact ⟨hr Q.U hQ.U, hi, fun i j => (hQ.V i j).trans hw,
    fun i j => (hQ.Vinv i j).trans hw, hr Q.S hQ.S⟩

/-- Includes all temporary additions inside the signed swap, not just its
endpoint. The factor eight pays for its three unit-coefficient additions. -/
theorem pairStep_prefix_bound (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (q : ℤ) (H t : ℕ) (hQ : Bounded Q H) :
    Bounded (run Q ((pairStep r s h q).take t)) (8 * (q.natAbs + 1) * H) := by
  have h1 := step_bound Q (.row r s h (-q)) H hQ
  have h2 := step_bound _ (.row r s h 1) _ h1
  have h3 := step_bound _ (.row s r h.symm (-1)) _ h2
  have h4 := step_bound _ (.row r s h 1) _ h3
  simp only [coefficient, Int.natAbs_neg, Int.natAbs_one] at h1 h2 h3 h4
  have hw : H ≤ (q.natAbs + 1) * H := by
    simpa using Nat.mul_le_mul_right H (Nat.le_add_left 1 q.natAbs)
  simp only [Nat.mul_assoc]
  rcases t with _ | t
  · exact hQ.mono (by omega)
  rcases t with _ | t
  · simpa [pairStep, run] using h1.mono (by omega)
  rcases t with _ | t
  · simpa [pairStep, run] using h2.mono (by omega)
  rcases t with _ | t
  · simpa [pairStep, run] using h3.mono (by omega)
  · simpa [pairStep, run] using h4.mono (by omega)

/-- The actual quotient is charged against the next selected magnitude.
This uses truncation toward zero and holds for either sign of each entry. -/
theorem quotient_height_bound (a b : ℤ) :
    ((a.tdiv b).natAbs + 1) * b.natAbs ≤
      2 * max 1 (max a.natAbs b.natAbs) := by
  have hq : (a.tdiv b).natAbs * b.natAbs ≤ a.natAbs := by
    rw [Int.natAbs_tdiv]
    exact Nat.div_mul_le_self _ _
  have ha : a.natAbs ≤ max 1 (max a.natAbs b.natAbs) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hb : b.natAbs ≤ max 1 (max a.natAbs b.natAbs) :=
    (le_max_right _ _).trans (le_max_right _ _)
  nlinarith

/-- Every prefix of the computed trace is bounded by one incoming magnitude
factor and one constant factor per addition. No bound on arbitrary valid
traces, rank, determinant, or nonzero input is assumed. -/
theorem gcdTrace_prefix_height_bound (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (a b : ℤ) (H t : ℕ) (hQ : Bounded Q H) :
    Bounded (run Q ((gcdTrace r s h a b).take t))
      (H * max 1 (max a.natAbs b.natAbs) *
        2 ^ (gcdTrace (n := n) r s h a b).length) := by
  rw [gcdTrace]
  split_ifs with hb
  · simpa [run] using hQ.mono (by
      have : 1 ≤ max 1 (max a.natAbs b.natAbs) := le_max_left _ _
      nlinarith)
  · let M := max 1 (max a.natAbs b.natAbs)
    let q := a.tdiv b
    let tail := gcdTrace (n := n) r s h b (-(a.tmod b))
    have hlen : (pairStep (n := n) r s h q).length = 4 := rfl
    have hM : 1 ≤ M := le_max_left _ _
    have hq : q.natAbs + 1 ≤ 2 * M := by
      have hqa := Int.natAbs_tdiv_le_natAbs a b
      have ha : a.natAbs ≤ M := (le_max_left _ _).trans (le_max_right _ _)
      omega
    have ht : max 1 (max b.natAbs (-(a.tmod b)).natAbs) = b.natAbs := by
      have hr := remainder_descent a b hb
      have hp := Int.natAbs_pos.mpr hb
      omega
    have hpow : 1 ≤ (2 : ℕ) ^ tail.length := Nat.one_le_pow _ _ (by decide)
    change Bounded (run Q (((pairStep r s h q) ++ tail).take t))
      (H * M * 2 ^ ((pairStep (n := n) r s h q ++ tail).length))
    rw [List.length_append, hlen, pow_add]
    norm_num only [Nat.reducePow]
    by_cases hsmall : t ≤ 4
    · rw [List.take_append_of_le_length (by simpa [hlen] using hsmall)]
      apply (pairStep_prefix_bound Q r s h q H t hQ).mono
      calc
        8 * (q.natAbs + 1) * H ≤ H * M * 16 := by nlinarith
        _ ≤ H * M * (16 * 2 ^ tail.length) :=
          Nat.mul_le_mul_left (H * M) (by omega)
    · rw [List.take_append, List.take_of_length_le (by omega), run_append]
      have hi := gcdTrace_prefix_height_bound (run Q (pairStep r s h q)) r s h
        b (-(a.tmod b)) ((q.natAbs + 1) * H) (t - 4)
        (pairStep_bound Q r s h q H hQ)
      rw [ht] at hi
      apply hi.mono
      have htel := quotient_height_bound a b
      change (q.natAbs + 1) * b.natAbs ≤ 2 * M at htel
      change (q.natAbs + 1) * H * b.natAbs * 2 ^ tail.length ≤ _
      calc
        _ = H * ((q.natAbs + 1) * b.natAbs) * 2 ^ tail.length := by ring
        _ ≤ H * (2 * M) * 2 ^ tail.length := by gcongr
        _ ≤ H * M * (16 * 2 ^ tail.length) := by
          rw [show H * (2 * M) * 2 ^ tail.length =
            H * M * (2 * 2 ^ tail.length) by ring]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by decide : 2 ≤ 16))
termination_by b.natAbs
decreasing_by exact remainder_descent a b hb

/-- The exponent is linear in the incoming pair's bit width, rather than
quadratic. All five matrices and every temporary swap prefix are included. -/
theorem gcdTrace_prefix_pow_bound (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (a b : ℤ) (d c t : ℕ) (hQ : Bounded Q (2 ^ d))
    (ha : a.natAbs < 2 ^ c) (hb : b.natAbs < 2 ^ c) :
    Bounded (run Q ((gcdTrace r s h a b).take t)) (2 ^ (d + 9 * c)) := by
  apply (gcdTrace_prefix_height_bound Q r s h a b (2 ^ d) t hQ).mono
  have hM : max 1 (max a.natAbs b.natAbs) ≤ 2 ^ c :=
    max_le (Nat.one_le_pow c 2 (by decide)) (max_le ha.le hb.le)
  have hL : (gcdTrace (n := n) r s h a b).length ≤ 8 * c :=
    (gcdTrace_length_le r s h a b).trans
      (Nat.mul_le_mul_left 8 (Nat.size_le.mpr hb))
  calc
    _ ≤ 2 ^ d * 2 ^ c * 2 ^ (8 * c) := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hM)
        (Nat.pow_le_pow_right (by decide) hL)
    _ = 2 ^ (d + 9 * c) := by simp only [← pow_add]; congr 1; ring

/-- In the complete original dense input length `s`, every intermediate
magnitude of a single computed pivot is at most `2^(10*s)`. -/
theorem pivot_prefix_bound (A : Dense) (r s : Fin A.rows) (h : r ≠ s)
    (j : Fin A.cols) (t : ℕ) :
    Bounded (run (initial A.toMatrix)
      ((gcdTrace r s h (A.toMatrix r j) (A.toMatrix s j)).take t))
      (2 ^ (10 * (SmithEncoding.encode A).length)) := by
  have hA : ∀ i j, (A.toMatrix i j).natAbs < 2 ^ (SmithEncoding.encode A).length :=
    fun i j => Nat.size_le.mp (SmithIsolationCount.entry_size_le_input_length A i j)
  convert gcdTrace_prefix_pow_bound _ r s h _ _ _ _ t
    (initial_pow_bound A.toMatrix _ (fun i j => (hA i j).le)) (hA r j) (hA s j)
    using 1
  congr 1
  ring

theorem pivot_bound (A : Dense) (r s : Fin A.rows) (h : r ≠ s) (j : Fin A.cols) :
    Bounded (pivot (initial A.toMatrix) r s h j)
      (2 ^ (10 * (SmithEncoding.encode A).length)) := by
  simpa only [List.take_length, pivot, initial] using
    pivot_prefix_bound A r s h j (gcdTrace (n := A.cols) r s h
      (A.toMatrix r j) (A.toMatrix s j)).length

/-- Cubic complete output length for one pivot, including all five dense
matrices, signs, field frames and unary dimensions. This is not runtime. -/
theorem pivotDense_output_length_le (A : Dense) (r s : Fin A.rows) (h : r ≠ s)
    (j : Fin A.cols) :
    (SmithDecomposition.encode (pivotDense A r s h j)).length ≤
      80 * (SmithEncoding.encode A).length ^ 3 +
        16 * (SmithEncoding.encode A).length ^ 2 +
        10 * (SmithEncoding.encode A).length + 25 := by
  calc
    _ ≤ 2 * (5 * (SmithEncoding.encode A).length + 10 +
        2 * (SmithEncoding.encode A).length * (SmithEncoding.encode A).length *
          (2 * (10 * (SmithEncoding.encode A).length + 1) + 2)) + 5 :=
      encode_length_le_of_input_bits A _ _ (pivot_bound A r s h j).result_entry_bits
    _ = _ := by ring

/-- The controller's exact-division shortcut and its Euclidean branch both
satisfy the linear local exponent. No nonzero-entry hypothesis is required. -/
theorem reduceRows_pow_bound (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j : Fin n) (d c : ℕ) (hc : 0 < c) (hQ : Bounded Q (2 ^ d))
    (ha : (Q.S r j).natAbs < 2 ^ c) (hb : (Q.S s j).natAbs < 2 ^ c) :
    Bounded (SmithReduction.reduceRows Q r s h j) (2 ^ (d + 9 * c)) := by
  unfold SmithReduction.reduceRows
  split_ifs
  · have hs := step_pow_bound Q (.row s r h.symm (-(Q.S s j).tdiv (Q.S r j)))
      d c hQ (by
        simpa [coefficient] using
          (Int.natAbs_tdiv_le_natAbs (Q.S s j) (Q.S r j)).trans hb.le)
    exact hs.mono (Nat.pow_le_pow_right (by decide) (by omega))
  · simpa only [List.take_length, pivot] using
      gcdTrace_prefix_pow_bound Q r s h _ _ d c
        (gcdTrace (n := n) r s h (Q.S r j) (Q.S s j)).length hQ ha hb

/-- The total runtime-indexed column-entry reduction retains every no-op
branch, including missing positions and empty rectangles. -/
theorem reduceAtColumn_pow_bound (Q : State m n) (k target d c : ℕ)
    (hc : 0 < c) (hQ : Bounded Q (2 ^ d))
    (hS : ∀ i j, (Q.S i j).natAbs < 2 ^ c) :
    Bounded (SmithReduction.reduceAtColumn Q k target) (2 ^ (d + 9 * c)) := by
  unfold SmithReduction.reduceAtColumn
  split_ifs
  · exact reduceRows_pow_bound Q _ _ _ _ d c hc hQ (hS _ _) (hS _ _)
  all_goals exact hQ.mono (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))

theorem reduceAtRow_pow_bound (Q : State m n) (k target d c : ℕ)
    (hc : 0 < c) (hQ : Bounded Q (2 ^ d))
    (hS : ∀ i j, (Q.S i j).natAbs < 2 ^ c) :
    Bounded (SmithReduction.reduceAtRow Q k target) (2 ^ (d + 9 * c)) :=
  (reduceAtColumn_pow_bound (SmithReduction.transposeState Q) k target d c hc
    hQ.transposeState (fun i j => hS j i)).transposeState

/-- Unconditional cubic output length for one stored entry reduction in
either orientation. Includes singular, rectangular, empty and missing cases;
it is not a bound for iterated sweeps or the complete diagonalizer. -/
theorem reduceDense_output_length_le (A : Dense) (acrossRow : Bool) (k target : ℕ) :
    (SmithDecomposition.encode (SmithReduction.reduceDense A acrossRow k target)).length ≤
      80 * (SmithEncoding.encode A).length ^ 3 +
        16 * (SmithEncoding.encode A).length ^ 2 +
        10 * (SmithEncoding.encode A).length + 25 := by
  have hS : ∀ i j, (A.toMatrix i j).natAbs < 2 ^ (SmithEncoding.encode A).length :=
    fun i j => Nat.size_le.mp (SmithIsolationCount.entry_size_le_input_length A i j)
  have hp : 0 < (SmithEncoding.encode A).length := by
    simp only [SmithEncoding.encode, List.length_append, List.length_replicate,
      List.length_cons]
    omega
  have hQ := initial_pow_bound A.toMatrix _ (fun i j => (hS i j).le)
  have hb : Bounded (if acrossRow then
      SmithReduction.reduceAtRow (initial A.toMatrix) k target
    else SmithReduction.reduceAtColumn (initial A.toMatrix) k target)
      (2 ^ (10 * (SmithEncoding.encode A).length)) := by
    split
    · convert reduceAtRow_pow_bound _ k target _ _ hp hQ hS using 1
      congr 1
      ring
    · convert reduceAtColumn_pow_bound _ k target _ _ hp hQ hS using 1
      congr 1
      ring
  calc
    _ ≤ 2 * (5 * (SmithEncoding.encode A).length + 10 +
        2 * (SmithEncoding.encode A).length * (SmithEncoding.encode A).length *
          (2 * (10 * (SmithEncoding.encode A).length + 1) + 2)) + 5 :=
      encode_length_le_of_input_bits A _ _ hb.result_entry_bits
    _ = _ := by ring

-- Kernel specializations keep zero scalar width, singular/rectangular input,
-- both empty orientations and missing positions in the new bounds' scope.
example (Q : State m n) (r s : Fin m) (h : r ≠ s) (t : ℕ)
    (hQ : Bounded Q 1) :
    Bounded (run Q ((gcdTrace r s h 0 0).take t)) 1 := by
  simpa using gcdTrace_prefix_pow_bound Q r s h 0 0 0 0 t hQ (by decide) (by decide)

example (t : ℕ) :
    Bounded (run (initial (⟨3, 2, [-100, 0, -99, 0, 0, 0], rfl⟩ : Dense).toMatrix)
      ((gcdTrace (n := 2) (0 : Fin 3) 1 (by decide) (-100) (-99)).take t))
      (2 ^ (10 * (SmithEncoding.encode
        (⟨3, 2, [-100, 0, -99, 0, 0, 0], rfl⟩ : Dense)).length)) :=
  pivot_prefix_bound _ 0 1 (by decide) 0 t

example : (SmithDecomposition.encode
    (SmithReduction.reduceDense ⟨0, 3, [], rfl⟩ true 0 1)).length ≤
    80 * (SmithEncoding.encode (⟨0, 3, [], rfl⟩ : Dense)).length ^ 3 +
      16 * (SmithEncoding.encode (⟨0, 3, [], rfl⟩ : Dense)).length ^ 2 +
      10 * (SmithEncoding.encode (⟨0, 3, [], rfl⟩ : Dense)).length + 25 :=
  reduceDense_output_length_le _ true 0 1

example : (SmithDecomposition.encode
    (SmithReduction.reduceDense ⟨3, 0, [], rfl⟩ false 0 1)).length ≤
    80 * (SmithEncoding.encode (⟨3, 0, [], rfl⟩ : Dense)).length ^ 3 +
      16 * (SmithEncoding.encode (⟨3, 0, [], rfl⟩ : Dense)).length ^ 2 +
      10 * (SmithEncoding.encode (⟨3, 0, [], rfl⟩ : Dense)).length + 25 :=
  reduceDense_output_length_le _ false 0 1

example : Bounded (SmithReduction.reduceAtColumn (initial
    (⟨2, 3, [0, 0, 0, 0, 0, 0], rfl⟩ : Dense).toMatrix) 8 12) (2 ^ 9) :=
  reduceAtColumn_pow_bound _ 8 12 0 1 (by decide) (initial_pow_bound _ 0 (by decide))
    (by decide)

#print axioms pairStep_bound
#print axioms pairStep_prefix_bound
#print axioms quotient_height_bound
#print axioms gcdTrace_prefix_height_bound
#print axioms gcdTrace_prefix_pow_bound
#print axioms pivot_prefix_bound
#print axioms pivot_bound
#print axioms pivotDense_output_length_le
#print axioms reduceRows_pow_bound
#print axioms reduceAtColumn_pow_bound
#print axioms reduceAtRow_pow_bound
#print axioms reduceDense_output_length_le

end PhdThesisLean.SmithPivotLinearBounds
