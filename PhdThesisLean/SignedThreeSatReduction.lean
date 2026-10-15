import PhdThesisLean.FixedPrimeMaxCutReduction

/-!
# The signed clause-reward reduction as a map of encoded instances

This module gives the semantic half of the NP-hardness transfer for thesis Corollary
`cor:signed-nphard` (`sudoku-via-padic-regression/body.tex`): the threshold decision
problem for signed affine `p`-adic residual objectives is NP-hard at `p = 5`.

## The construction

Truth values are encoded by `x_v = 0` for true and `x_v = 1` for false, and variable
`v` is the coefficient `β v` (literal index `v + 1`). Each clause `C` gives one negative
observation `clauseRow C` with residual `u_C ⬝ x - t_C`: a positive literal on `v`
contributes `x_v - 1` and a negative literal contributes `-x_v`, so at Boolean points
the residual is minus the number of true literal occurrences (`residual_bool`). For
`p > 3` and clauses of width three its norm is the satisfaction indicator.

Each literal occurrence also contributes a positive Boolean forcing pair
`(e_v, 0), (e_v, 1)` (`forcingRows`). This is the thesis's well
`α (|x_v|_p + |x_v - 1|_p)` with the weight `α` split into one unit per occurrence, so
that the rows can be emitted while streaming: weak domination suffices for the decision
problem. One extra negative zero row is harmless.

`signedReduce F` lists the clause rows, the zero row, and the forcing rows (in the order
the machine of `SignedThreeSatMachine.lean` emits them), with bound `2m` for `m`
clauses.

## Correctness

`clauseValue_snap_le` shows that snapping all coordinates (with
`FixedPrimeMaxCutReduction.snap`) does not increase the contribution of any clause,
and at Boolean points a width-three clause contributes `3` minus its satisfaction
indicator (`clauseValue_bool`). Hence `signed_iff`: for a formula of exact width three
and every prime `p > 3`, the formula is satisfiable iff the signed objective of
`signedReduce F` has a point of value at most `2m`, which is the thesis's threshold
`α n - m` statement in the per-occurrence normalisation.
-/

namespace PhdThesisLean.SignedThreeSatReduction

open LeanNPHardness LeanNPHardness.CNF
open PhdThesisLean.PadicRegressionLanguage
open PhdThesisLean.FixedPrimeMaxCutReduction (U snap snap_le snap_bool bval U_zero U_one
  bval_of_bool)

/-! ### The construction -/

/-- The variable of a literal. -/
def litVar : Literal ℕ → ℕ
  | .positive v => v
  | .negative v => v

/-- The residual terms of a literal in its clause row. -/
def litTerms : Literal ℕ → Row
  | .positive v => [.positive 0, .positive (v + 1)]
  | .negative v => [.negative (v + 1)]

/-- The row `(u_C, t_C)` of a clause. -/
def clauseRow (c : Clause ℕ) : Row := c.flatMap litTerms

/-- The positive Boolean forcing pair on literal index `i`. -/
def forcingRows (i : ℕ) : List SignedRow :=
  [(true, [.positive i]), (true, [.positive i, .positive 0])]

/-- The negative clause rows, followed by one negative zero row. -/
def clauseRows (F : Formula ℕ) : List SignedRow :=
  F.map (fun c => (false, clauseRow c)) ++ [(false, [])]

/-- One forcing pair per literal occurrence, in reverse order of occurrence. -/
def occurrenceRows (F : Formula ℕ) : List SignedRow :=
  F.reverse.flatMap fun c => c.reverse.flatMap fun l => forcingRows (litVar l + 1)

/-- The reduction from CNF formulas to signed threshold instances. -/
def signedReduce (F : Formula ℕ) : List SignedRow × ℕ :=
  (clauseRows F ++ occurrenceRows F, 2 * F.length)

/-! ### Values -/

variable {p : ℕ}

/-- The contribution of one literal to its clause residual. -/
def litValue (β : ℕ → ℚ) : Literal ℕ → ℚ
  | .positive v => β v - 1
  | .negative v => -β v

theorem residual_clauseRow (β : ℕ → ℚ) (c : Clause ℕ) :
    residual β (clauseRow c) = (c.map (litValue β)).sum := by
  induction c with
  | nil => rfl
  | cons l c ih =>
      simp only [clauseRow, List.flatMap_cons, residual, List.map_append, List.sum_append] at ih ⊢
      rw [ih, List.map_cons, List.sum_cons]
      cases l with
      | positive v => simp [litTerms, term, litValue]; ring
      | negative v => simp [litTerms, term, litValue]

/-- The contribution of a clause: its occurrence wells minus its reward. -/
def clauseValue (p : ℕ) (β : ℕ → ℚ) (c : Clause ℕ) : ℚ :=
  (c.map fun l => U p (β (litVar l))).sum - padicNorm p (residual β (clauseRow c))

theorem signedLoss_forcingRows (β : ℕ → ℚ) (v : ℕ) :
    signedLoss p β (forcingRows (v + 1)) = U p (β v) := by
  simp [forcingRows, signedLoss, residual, term, U]
  ring_nf

theorem signedLoss_clauseRows (β : ℕ → ℚ) (F : Formula ℕ) :
    signedLoss p β (clauseRows F) =
      -(F.map fun c => padicNorm p (residual β (clauseRow c))).sum := by
  rw [clauseRows, signedLoss_append]
  have h0 : signedLoss p β [(false, [])] = 0 := by simp [signedLoss, residual]
  rw [h0, add_zero]
  induction F with
  | nil => rfl
  | cons c F ih =>
      rw [List.map_cons, signedLoss_cons, ih, List.map_cons, List.sum_cons]
      simp only [Bool.false_eq_true, if_false]
      ring

theorem signedLoss_occurrenceRows (β : ℕ → ℚ) (F : Formula ℕ) :
    signedLoss p β (occurrenceRows F) =
      (F.map fun c => (c.map fun l => U p (β (litVar l))).sum).sum := by
  have hc : ∀ c : Clause ℕ, signedLoss p β (c.reverse.flatMap fun l => forcingRows (litVar l + 1))
      = (c.map fun l => U p (β (litVar l))).sum := by
    intro c
    rw [signedLoss_flatMap]
    simp only [signedLoss_forcingRows, List.map_reverse, List.sum_reverse]
  rw [occurrenceRows, signedLoss_flatMap]
  simp only [hc, List.map_reverse, List.sum_reverse]

/-- The signed objective of the instance, written per clause. -/
theorem signedLoss_signedReduce (β : ℕ → ℚ) (F : Formula ℕ) :
    signedLoss p β (signedReduce F).1 = (F.map (clauseValue p β)).sum := by
  rw [signedReduce, signedLoss_append, signedLoss_clauseRows, signedLoss_occurrenceRows]
  induction F with
  | nil => simp
  | cons c F ih =>
      simp only [List.map_cons, List.sum_cons, clauseValue] at ih ⊢
      linarith

/-! ### Snapping -/

theorem padicNorm_sum_le [Fact p.Prime] (L : List ℚ) :
    padicNorm p L.sum ≤ (L.map (padicNorm p)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      rw [List.sum_cons, List.map_cons, List.sum_cons]
      exact le_trans (padicNorm.triangle_ineq a L.sum) (by linarith)

/-- Snapping all coordinates does not increase the contribution of a clause. -/
theorem clauseValue_snap_le [Fact p.Prime] (β : ℕ → ℚ) (c : Clause ℕ) :
    clauseValue p (fun i => snap p (β i)) c ≤ clauseValue p β c := by
  set d : Literal ℕ → ℚ := fun l => padicNorm p (β (litVar l) - snap p (β (litVar l)))
  have hres : padicNorm p (residual β (clauseRow c)) ≤
      padicNorm p (residual (fun i => snap p (β i)) (clauseRow c)) + (c.map d).sum := by
    rw [residual_clauseRow, residual_clauseRow]
    have hsplit : (c.map (litValue β)).sum = (c.map (litValue fun i => snap p (β i))).sum +
        (c.map fun l => litValue β l - litValue (fun i => snap p (β i)) l).sum := by
      rw [← List.sum_map_add]
      congr 1
      apply List.map_congr_left
      intro l _
      ring
    rw [hsplit]
    refine le_trans (padicNorm.triangle_ineq _ _) (add_le_add le_rfl ?_)
    refine le_trans (padicNorm_sum_le _) (le_of_eq ?_)
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro l _
    cases l with
    | positive v =>
        simp only [Function.comp_apply, litValue, d, litVar]
        congr 1
        ring
    | negative v =>
        simp only [Function.comp_apply, litValue, d, litVar]
        rw [show -β v - -snap p (β v) = -(β v - snap p (β v)) by ring, padicNorm.neg]
  have hU : (c.map fun l => U p (snap p (β (litVar l)))).sum + (c.map d).sum ≤
      (c.map fun l => U p (β (litVar l))).sum := by
    rw [← List.sum_map_add]
    apply List.sum_le_sum
    intro l _
    exact snap_le (β (litVar l))
  unfold clauseValue
  linarith

/-! ### Boolean points -/

/-- The point encoding an assignment: `x_v = 0` for true and `1` for false. -/
def point (a : ℕ → Bool) : ℕ → ℚ := fun v => bval (!a v)

theorem litValue_point (a : ℕ → Bool) (l : Literal ℕ) :
    litValue (point a) l = -(if l.eval a then 1 else 0) := by
  cases l with
  | positive v => cases h : a v <;> simp [litValue, point, bval, Literal.eval, h]
  | negative v => cases h : a v <;> simp [litValue, point, bval, Literal.eval, h]

/-- At a Boolean point the clause residual is minus the number of true literal
occurrences. -/
theorem residual_bool (a : ℕ → Bool) (c : Clause ℕ) :
    residual (point a) (clauseRow c) = -((c.filter (·.eval a)).length : ℚ) := by
  rw [residual_clauseRow]
  induction c with
  | nil => simp
  | cons l c ih =>
      rw [List.map_cons, List.sum_cons, ih, litValue_point, List.filter_cons]
      split <;> simp_all

theorem clauseValue_bool [hp : Fact p.Prime] (hp3 : 3 < p) (a : ℕ → Bool) (c : Clause ℕ)
    (hc : c.length = 3) :
    clauseValue p (point a) c = 3 - (if c.eval a then 1 else 0) := by
  have hU : (c.map fun l => U p (point a (litVar l))).sum = c.length := by
    have : ∀ l ∈ c, U p (point a (litVar l)) = 1 := by
      intro l _
      cases h : a (litVar l) <;> simp [point, bval, h, U_zero, U_one]
    rw [List.map_congr_left this]
    simp
  have hk : (c.filter (·.eval a)).length ≤ 3 := by
    rw [← hc]; exact List.length_filter_le _ _
  have hnorm : padicNorm p (residual (point a) (clauseRow c)) = if c.eval a then 1 else 0 := by
    rw [residual_bool, padicNorm.neg]
    by_cases he : c.eval a = true
    · have hpos : 0 < (c.filter (·.eval a)).length := by
        rw [List.length_pos_iff_exists_mem]
        simp only [Clause.eval, List.any_eq_true] at he
        obtain ⟨l, hl, hl'⟩ := he
        exact ⟨l, List.mem_filter.mpr ⟨hl, hl'⟩⟩
      rw [if_pos he]
      exact_mod_cast (padicNorm.nat_eq_one_iff _).mpr
        (Nat.not_dvd_of_pos_of_lt hpos (by omega))
    · have hzero : (c.filter (·.eval a)).length = 0 := by
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro l hl hl'
        apply he
        simp only [Clause.eval, List.any_eq_true]
        exact ⟨l, hl, hl'⟩
      rw [if_neg he, hzero]
      simp
  rw [clauseValue, hU, hnorm, hc]
  norm_num

/-! ### Correctness -/

theorem two_mul_length_le {α : Type} (g : α → ℚ) (L : List α) (h : ∀ c ∈ L, 2 ≤ g c) :
    (2 * L.length : ℚ) ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons c L ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons]
      have := h c (List.mem_cons_self ..)
      have := ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
      push_cast
      linarith

/-- **The signed clause-reward reduction preserves membership.** For every prime
`p > 3` and every formula of exact width three, the formula is satisfiable iff the
signed objective of `signedReduce F` takes a value at most `2m`. -/
theorem signed_iff [Fact p.Prime] (hp3 : 3 < p) (F : Formula ℕ) (hF : F.ExactWidth 3) :
    F.Satisfiable ↔ SignedRegressionLang p (signedReduce F) := by
  have hvalue : ∀ a : ℕ → Bool, signedLoss p (point a) (signedReduce F).1 =
      (F.map fun c => 3 - (if c.eval a then (1 : ℚ) else 0)).sum := by
    intro a
    rw [signedLoss_signedReduce]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact clauseValue_bool hp3 a c (hF c hc)
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨point a, ?_⟩
    rw [hvalue]
    have : ∀ c ∈ F, (3 - (if c.eval a then (1 : ℚ) else 0)) = 2 := by
      intro c hc
      have : c.eval a = true := (Clause.eval_eq_true a c).mpr (ha c hc)
      simp [this]; norm_num
    rw [List.map_congr_left this]
    simp [signedReduce, mul_comm]
  · rintro ⟨β, hβ⟩
    have hsnap : signedLoss p (fun i => snap p (β i)) (signedReduce F).1 ≤
        signedLoss p β (signedReduce F).1 := by
      rw [signedLoss_signedReduce, signedLoss_signedReduce]
      apply List.sum_le_sum
      intro c _
      exact clauseValue_snap_le β c
    set a : ℕ → Bool := fun v => decide (snap p (β v) = 0) with ha
    have hpt : (fun i => snap p (β i)) = point a := by
      funext v
      rcases snap_bool (p := p) (β v) with h | h <;> simp [point, bval, ha, h]
    rw [hpt, hvalue] at hsnap
    refine ⟨a, fun c hc => (Clause.eval_eq_true a c).mp ?_⟩
    by_contra hne
    have hlt : ∀ c' ∈ F, (2 : ℚ) ≤ 3 - (if c'.eval a then (1 : ℚ) else 0) := by
      intro c' _; split <;> norm_num
    have hsum : (2 * F.length : ℚ) + 1 ≤
        (F.map fun c => 3 - (if c.eval a then (1 : ℚ) else 0)).sum := by
      obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hc
      have h1 := two_mul_length_le (fun c => 3 - (if c.eval a then (1 : ℚ) else 0)) L₁
        (fun c' hc' => hlt c' (List.mem_append_left _ hc'))
      have h2 := two_mul_length_le (fun c => 3 - (if c.eval a then (1 : ℚ) else 0)) L₂
        (fun c' hc' => hlt c' (List.mem_append_right _ (List.mem_cons_of_mem _ hc')))
      simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons,
        List.length_append, List.length_cons]
      simp only [Bool.not_eq_true] at hne
      rw [hne]
      push_cast
      norm_num
      linarith
    have : signedLoss p β (signedReduce F).1 ≤ (2 * F.length : ℚ) := by
      have := hβ
      simp only [signedReduce] at this ⊢
      exact_mod_cast this
    linarith

end PhdThesisLean.SignedThreeSatReduction

#print axioms PhdThesisLean.SignedThreeSatReduction.signed_iff
