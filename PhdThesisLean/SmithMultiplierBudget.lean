import PhdThesisLean.SmithComputedBounds

/-! # Additive multiplier widths along the computed Smith trace -/

namespace PhdThesisLean.SmithMultiplierBudget

open SmithEncoding SmithTrace SmithTraceCount SmithPivotBounds SmithComputedBounds

variable {m n : ℕ}

/-- One bit per operation plus the binary magnitude length of its multiplier. -/
def budget (ops : List (Op m n)) : ℕ :=
  (ops.map fun op => (coefficient op).natAbs.size + 1).sum

theorem budget_append (xs ys : List (Op m n)) :
    budget (xs ++ ys) = budget xs + budget ys := by simp [budget]

/-- Each addition costs its own width, including when updating inverse maps. -/
theorem run_budget_bound (Q : State m n) (ops : List (Op m n)) (a : ℕ)
    (hQ : Bounded Q (2 ^ a)) : Bounded (run Q ops) (2 ^ (a + budget ops)) := by
  induction ops generalizing Q a with
  | nil => simpa [run, budget] using hQ
  | cons op ops ih =>
    have hs := step_pow_bound Q op a _ hQ (Nat.lt_size_self _).le
    simpa [run, budget, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih _ _ hs

private theorem budget_le (ops : List (Op m n)) (b : ℕ)
    (h : ∀ op ∈ ops, (coefficient op).natAbs ≤ 2 ^ b) :
    budget ops ≤ ops.length * (b + 2) := by
  induction ops with
  | nil => simp [budget]
  | cons op ops ih =>
    have hc := Nat.size_le_size (h op (by simp))
    rw [Nat.size_pow] at hc
    have ht := ih (fun x hx => h x (by simp [hx]))
    change (coefficient op).natAbs.size + 1 + budget ops ≤ _
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A polynomial total multiplier width is equivalent to the still-open
original-input prefix bound for this controller. -/
theorem polynomial_budget_iff :
    (∃ P : Polynomial ℕ, ∀ A : Dense, budget (decomposeTrace A) ≤
      P.eval (SmithEncoding.encode A).length) ↔
    (∃ P : Polynomial ℕ, ∀ A : Dense, PrefixWidth (initial A.toMatrix)
      (decomposeTrace A) (P.eval (SmithEncoding.encode A).length + 1)) := by
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨Polynomial.X + P, ?_⟩
    intro A t i j
    let s := (SmithEncoding.encode A).length
    have hA := initial_pow_bound A.toMatrix s (fun i j =>
      (Nat.size_le.mp (SmithIsolationCount.entry_size_le_input_length A i j)).le)
    have h := (run_budget_bound _ ((decomposeTrace A).take t) s hA).S i j
    have hsplit := budget_append ((decomposeTrace A).take t) ((decomposeTrace A).drop t)
    rw [List.take_append_drop] at hsplit
    have hfull := hP A
    change _ < 2 ^ ((Polynomial.X + P).eval s + 1)
    simp only [Polynomial.eval_add, Polynomial.eval_X]
    apply h.trans_lt (Nat.pow_lt_pow_right (by decide) ?_)
    dsimp [s] at *
    omega
  · rintro ⟨P, hP⟩
    refine ⟨8 * Polynomial.X * Polynomial.X * (P + 1) * (P + 2) * (P + 3), ?_⟩
    intro A
    let b := P.eval (SmithEncoding.encode A).length + 1
    have hc := decomposeTrace_coefficient_le A b (by dsimp [b]; omega) (hP A)
    have hl := decomposeTrace_length_le_of_width A b (by dsimp [b]; omega) (hP A)
    apply (budget_le _ b hc).trans
    simpa [b, Polynomial.eval_add, Polynomial.eval_mul, Nat.add_assoc] using
      Nat.mul_le_mul_right (b + 2) hl

private theorem quotient_width (a b : ℕ) (hb : 0 < b) :
    (a / b).size + b.size ≤ max a.size b.size + 1 := by
  by_cases hq : a / b = 0
  · simp [hq]
    omega
  have hx := Nat.size_pos.mpr (Nat.pos_of_ne_zero hq)
  have hy := Nat.size_pos.mpr hb
  have h₁ := Nat.lt_size.mp (show (a / b).size - 1 < (a / b).size by omega)
  have h₂ := Nat.lt_size.mp (show b.size - 1 < b.size by omega)
  have hpow := (Nat.mul_le_mul h₁ h₂).trans (Nat.div_mul_le_self a b)
  rw [← pow_add] at hpow
  have := Nat.lt_size.mpr hpow
  omega

/-- The gcd keeps its remaining width as credit. Each group of four actual
additions consumes at most eight further bits beyond the width decrease. -/
theorem gcdTrace_budget_credit (r s : Fin m) (h : r ≠ s) (a b : ℤ) :
    let ops := SmithPivot.gcdTrace (n := n) r s h a b
    budget ops + (a.natAbs.gcd b.natAbs).size ≤
      max a.natAbs.size b.natAbs.size + 2 * ops.length := by
  dsimp only
  rw [SmithPivot.gcdTrace]
  split_ifs with hb
  · subst b
    simp [budget]
  · have hi := gcdTrace_budget_credit r s h b (-(a.tmod b))
    simp only [Int.natAbs_neg, Int.natAbs_tmod] at hi
    have hm := Nat.size_le_size (Nat.mod_lt a.natAbs (Int.natAbs_pos.mpr hb)).le
    rw [max_eq_left hm, Nat.gcd_comm b.natAbs, ← Nat.gcd_rec b.natAbs a.natAbs,
      Nat.gcd_comm b.natAbs] at hi
    have hw := quotient_width a.natAbs b.natAbs (Int.natAbs_pos.mpr hb)
    rw [budget_append, List.length_append]
    have hc : budget (SmithPivot.pairStep (n := n) r s h (a.tdiv b)) =
        (a.natAbs / b.natAbs).size + 7 := by
      simp [SmithPivot.pairStep, budget, coefficient, Int.natAbs_tdiv]
      have he : a.natAbs.div b.natAbs = a.natAbs / b.natAbs := rfl
      rw [he]
    rw [hc]
    change _ ≤ _ + 2 * (4 + _)
    omega
termination_by b.natAbs
decreasing_by exact SmithPivot.remainder_descent a b hb

theorem gcdTrace_budget_le (r s : Fin m) (h : r ≠ s) (a b : ℤ) :
    budget (SmithPivot.gcdTrace (n := n) r s h a b) + (a.natAbs.gcd b.natAbs).size ≤
      max a.natAbs.size b.natAbs.size + 16 * b.natAbs.size := by
  have := gcdTrace_budget_credit (n := n) r s h a b
  have := gcdTrace_length_le (n := n) r s h a b
  dsimp only at *
  omega

open SmithSweepBounds SmithReduction SmithSweep

private theorem reduceRows_budget (Q : State m n) (r s : Fin m) (h : r ≠ s) (j : Fin n) :
    budget (reduceRowsTrace Q r s h j) + ((reduceRows Q r s h j).S r j).natAbs.size ≤
      (Q.S r j).natAbs.size + 17 * (Q.S s j).natAbs.size + 1 := by
  rw [(reduceRows_correct Q r s h j).2.1]
  unfold reduceRowsTrace
  split_ifs with hd
  · rw [Int.gcd_eq_natAbs_left_iff_dvd.mpr hd]
    have hw := Nat.size_le_size (Int.natAbs_tdiv_le_natAbs (Q.S s j) (Q.S r j))
    simp only [budget, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, coefficient, Int.natAbs_neg]
    omega
  · have ht := gcdTrace_budget_le (n := n) r s h (Q.S r j) (Q.S s j)
    change _ + ((Q.S r j).natAbs.gcd (Q.S s j).natAbs).size ≤ _
    omega

/-- Charge a sweep to its incoming pivot once and to the incoming widths
of its listed targets. Repeated targets have already been cleared. -/
theorem sweepRows_budget (Q : State m n) (r : Fin m) (j : Fin n) (rows : List (Fin m))
    (hr : r ∉ rows) :
    budget (sweepRowsTrace Q r j rows) + ((sweepRows Q r j rows).S r j).natAbs.size ≤
      (Q.S r j).natAbs.size +
        (rows.map fun s => 17 * (Q.S s j).natAbs.size + 1).sum := by
  induction rows generalizing Q with
  | nil => simp [sweepRowsTrace, sweepRows, budget]
  | cons s rows ih =>
    simp only [sweepRowsTrace, sweepRows, List.map_cons, List.sum_cons]
    split_ifs with heq
    · exact False.elim (hr (List.mem_cons.mpr (Or.inl heq)))
    · let T := reduceRows Q r s heq j
      have hs := reduceRows_correct Q r s heq j
      have htail : r ∉ rows := fun hx => hr (List.mem_cons_of_mem s hx)
      have hmono (i : Fin m) (hi : i ∈ rows) :
          (T.S i j).natAbs.size ≤ (Q.S i j).natAbs.size := by
        have hir : i ≠ r := fun e => htail (e ▸ hi)
        by_cases his : i = s
        · subst i
          simp [T, hs.1]
        · simp [T, hs.2.2 i j hir his]
      have hsum : (rows.map fun i => 17 * (T.S i j).natAbs.size + 1).sum ≤
          (rows.map fun i => 17 * (Q.S i j).natAbs.size + 1).sum := by
        apply List.sum_le_sum
        intro i hi
        have := hmono i hi
        omega
      have ht := ih T htail
      have hp := reduceRows_budget Q r s heq j
      rw [budget_append]
      dsimp [T] at *
      omega

#print axioms sweepRows_budget
#print axioms gcdTrace_budget_credit
#print axioms gcdTrace_budget_le
#print axioms budget_append
#print axioms run_budget_bound
#print axioms polynomial_budget_iff

end PhdThesisLean.SmithMultiplierBudget
