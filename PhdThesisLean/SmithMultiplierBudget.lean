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

/-- For distinct nonpivot targets divisible by the pivot, the budget is
exactly the sum of the incoming quotient widths plus one per target. -/
theorem divisible_sweep_budget {m n : ℕ} (Q : State m n) (r : Fin m) (j : Fin n)
    (rows : List (Fin m)) (hn : rows.Nodup) (hr : r ∉ rows)
    (hd : ∀ s ∈ rows, Q.S r j ∣ Q.S s j) :
    budget (sweepRowsTrace Q r j rows) =
      (rows.map fun s => ((Q.S s j).tdiv (Q.S r j)).natAbs.size + 1).sum := by
  induction rows generalizing Q with
  | nil => rfl
  | cons s rows ih =>
    obtain ⟨hs, hn⟩ := List.nodup_cons.mp hn
    have hrs : r ≠ s := fun h => hr (by simp [h])
    have htail : r ∉ rows := fun h => hr (List.mem_cons_of_mem _ h)
    have hdiv := hd s (by simp)
    let T := reduceRows Q r s hrs j
    have keep (i : Fin m) (hi : i ≠ s) : T.S i j = Q.S i j := by
      simp [T, reduceRows, hdiv, step, SmithRowOperations.rowAdd, hi]
    have ht (i) (hi : i ∈ rows) : i ≠ s := fun h => hs (h ▸ hi)
    have hrec := ih T hn htail (fun i hi => by
      rw [keep r hrs, keep i (ht i hi)]
      exact hd i (List.mem_cons_of_mem _ hi))
    rw [sweepRowsTrace, dite_eq_right hrs, budget_append]
    change _ + budget (sweepRowsTrace T r j rows) = _
    rw [hrec, List.map_cons, List.sum_cons]
    congr 1
    · simp [reduceRowsTrace, hdiv, budget, coefficient]
    · congr 1
      apply List.map_congr_left
      intro i hi
      rw [keep r hrs, keep i (ht i hi)]

open SmithColumn

private theorem active_charge (A : Dense) (j : Fin A.cols) (k : ℕ) :
    ((activeRows A.rows k).map fun i => 17 * (A.toMatrix i j).natAbs.size + 1).sum ≤
      17 * (SmithEncoding.encode A).length := by
  let charge (i : Fin A.rows) := 17 * (A.toMatrix i j).natAbs.size + 1
  let wire (z : ℤ) := 2 * (Computability.encodeNat z.natAbs).length + 2
  let pos (i : Fin A.rows) : Fin A.entries.length :=
    ⟨i.val * A.cols + j.val, by
      rw [A.entryCount]
      calc
        _ < i.val * A.cols + A.cols := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * A.cols := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ _ := Nat.mul_le_mul_right _ i.isLt⟩
  have hinj : Function.Injective pos := by
    intro x y he
    have heq := congrArg Fin.val he
    change x.val * A.cols + j.val = y.val * A.cols + j.val at heq
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega : 0 < A.cols)
      (Nat.add_right_cancel heq))
  have hs : (∑ i, charge i) ≤ ∑ t : Fin A.entries.length, 17 * wire A.entries[t.val] := by
    apply Finset.sum_le_sum_of_injOn pos hinj.injOn (Finset.subset_univ _)
    · intro i _
      dsimp [charge, pos, wire, Dense.toMatrix]
      rw [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size]
      omega
    · intros
      omega
  rw [← Finset.mul_sum, ← List.sum_ofFn (f := fun t : Fin A.entries.length => wire A.entries[t.val]), List.ofFn_getElem_eq_map] at hs
  have hsub := ((List.filter_sublist (l := List.finRange A.rows)
    (p := fun i => decide (k < i.val))).map charge).sum_le_sum (fun _ _ => Nat.zero_le _)
  rw [← Fin.sum_univ_def] at hsub
  change _ ≤ 17 * (SmithEncoding.encode A).length
  rw [encode_length]
  dsimp [wire] at hs
  exact (hsub.trans hs).trans (Nat.mul_le_mul_left _ (by omega))

/-- The first column sweep reads distinct fields in the original dense wire format. -/
theorem initial_column_budget (A : Dense) (k : ℕ) :
    budget (columnTrace (initial A.toMatrix) k) ≤ 18 * (SmithEncoding.encode A).length := by
  unfold columnTrace
  split_ifs with hr hc
  · let r : Fin A.rows := ⟨k, hr⟩
    let j : Fin A.cols := ⟨k, hc⟩
    have h := sweepRows_budget (initial A.toMatrix) r j (activeRows A.rows k)
      (by simp [mem_activeRows, r])
    have ha := active_charge A j k
    have hp := SmithIsolationCount.entry_size_le_input_length A r j
    change _ + _ ≤ (A.toMatrix r j).natAbs.size +
      ((activeRows A.rows k).map fun i => 17 * (A.toMatrix i j).natAbs.size + 1).sum at h
    change budget (sweepRowsTrace _ r j _) ≤ _
    omega
  all_goals simp [budget]

/-- Total binary magnitude width exposed to the perpendicular sweep at the first turn. -/
theorem initial_turn_width (A : Dense) (k : ℕ) (r : Fin A.rows) :
    let L := (SmithEncoding.encode A).length
    ((activeRows A.cols k).map fun j =>
      ((clearActiveColumn (initial A.toMatrix) k).S r j).natAbs.size).sum ≤
        (activeRows A.cols k).length * (19 * L + 1) := by
  dsimp only
  let L := (SmithEncoding.encode A).length
  have hA := initial_pow_bound A.toMatrix L (fun i j =>
    (Nat.size_le.mp (SmithIsolationCount.entry_size_le_input_length A i j)).le)
  have h := run_budget_bound _ (columnTrace (initial A.toMatrix) k) L hA
  rw [columnTrace_run] at h
  have hb := initial_column_budget A k
  apply (List.sum_le_length_nsmul _ (19 * L + 1) ?_).trans_eq
  · simp [L]
  · intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    have hw := Nat.size_le_size (h.S r j)
    rw [Nat.size_pow] at hw
    dsimp [L] at *
    omega

/-- Target charges at their actual time of exposure in one column sweep. -/
def columnCharge (Q : State m n) (k : ℕ) (j : Fin n) : ℕ :=
  ((activeRows m k).map fun i => 17 * (Q.S i j).natAbs.size + 1).sum

private theorem column_credit (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n) :
    budget (columnTrace Q k) + ((clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs.size ≤
      (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs.size + columnCharge Q k ⟨k, hc⟩ := by
  simpa [columnTrace, clearActiveColumn, hr, hc, columnCharge] using
    sweepRows_budget Q ⟨k, hr⟩ ⟨k, hc⟩ (activeRows m k) (by simp [mem_activeRows])

theorem transpose_budget (ops : List (Op m n)) :
    budget (ops.map transposeOp) = budget ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih => cases op <;> simpa [budget, transposeOp, coefficient] using ih

/-- Sum both actual arms at each successive pass, excluding the pivot. -/
def exposedCharge (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n) : ℕ → ℕ
  | 0 => 0
  | t + 1 => columnCharge Q k ⟨k, hc⟩ +
      columnCharge (transposeState (clearActiveColumn Q k)) k ⟨k, hr⟩ +
      exposedCharge (cross Q k) k hr hc t

open SmithIsolationCount in
/-- The initial pivot is charged once over any number of turns. -/
theorem crosses_budget_credit (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n) (t : ℕ) :
    budget (crossesTrace Q k t) + ((crosses Q k t).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs.size ≤
      (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs.size + exposedCharge Q k hr hc t := by
  induction t generalizing Q with
  | zero => simp [crossesTrace, crosses, budget, exposedCharge]
  | succ t ih =>
    have hcol := column_credit Q k hr hc
    have hrow := column_credit (transposeState (clearActiveColumn Q k)) k hc hr
    change _ + ((cross Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs.size ≤
      ((clearActiveColumn Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs.size + _ at hrow
    have htail := ih (cross Q k)
    simp only [crossesTrace, crossTrace, budget_append, transpose_budget, crosses, exposedCharge]
    omega

open SmithIsolation SmithIsolationCount in
/-- Specialize the pivot credit to the controller's computed stopping time. -/
theorem isolate_budget_credit (Q : State m n) (k : ℕ) (hr : k < m) (hc : k < n) :
    budget (isolateTrace Q k) + ((isolate Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs.size ≤
      (Q.S ⟨k, hr⟩ ⟨k, hc⟩).natAbs.size + exposedCharge Q k hr hc (isolationPasses Q k) := by
  simpa only [isolateTrace, isolationPasses_replay] using
    crosses_budget_credit Q k hr hc (isolationPasses Q k)

#print axioms isolate_budget_credit
#print axioms crosses_budget_credit
#print axioms initial_column_budget
#print axioms initial_turn_width
#print axioms sweepRows_budget
#print axioms gcdTrace_budget_credit
#print axioms gcdTrace_budget_le
#print axioms budget_append
#print axioms run_budget_bound
#print axioms divisible_sweep_budget
#print axioms polynomial_budget_iff

end PhdThesisLean.SmithMultiplierBudget
