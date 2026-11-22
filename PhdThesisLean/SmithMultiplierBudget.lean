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

#print axioms budget_append
#print axioms run_budget_bound
#print axioms polynomial_budget_iff

end PhdThesisLean.SmithMultiplierBudget
