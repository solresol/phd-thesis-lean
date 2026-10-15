import PhdThesisLean.FixedPrimeHardness
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees

namespace PhdThesisLean.PolynomialResidualHardness

open scoped BigOperators
open PhdThesisLean.FiniteDomainCompiler
open PhdThesisLean.ClauseCompiler
open PhdThesisLean.FixedPrimeHardness

/-!
# Positive polynomial-residual hardness (no dyadic tractability transfer)

This module formalises thesis Corollary `cor:sudoku-polynomial-dyadic-hardness`
("No dyadic tractability transfer") together with the construction that
precedes it in Section `sec:sudoku-polynomial-labels` (the positive
polynomial-residual objective `L_poly`, its digit-snapping argument and its
value on Boolean assignments), from
`sudoku-via-padic-regression/body.tex` of the thesis repository.

## Correspondence with the thesis

* Literals, clauses (three literals with pairwise distinct variables), the
  convention `x_i = 0 ⇔ z_i = true`, the literal-failure value `δ(λ; x)` and the
  3-CNF syntax `ThreeCNF` are reused from `ClauseCompiler` and
  `FixedPrimeHardness`.
* `clauseProduct C x = ∏_{λ ∈ C} δ(λ; x)` is the thesis's `V_C(x)`;
  `clauseProduct_embeddedBoolean` is the claim that it is `0` on Boolean points
  satisfying `C` and `1` otherwise.
* `polyLoss Φ ω α` is `L_poly` with arbitrary clause weights `ω` and pinning
  weight `α`. The thesis minimises over `x ∈ ℤ_p^n`; here parameters range over
  `ℚ_p^n` and the unit ball is the explicit predicate `InUnitBall`, with
  `IsGlobalMinOnBall` the corresponding notion of global minimiser.
* `norm_clauseProduct_update_sub_le` is the `1`-Lipschitz claim ("every literal
  factor lies in `ℤ_p`, so each incident product is `1`-Lipschitz in `x_i`"); it
  needs only `x` in the unit ball, not the new value.
* `polyLoss_snap_lt` and `globalMinOnBall_boolean` are the snapping argument:
  under `α > max_i ∑_{C ∋ z_i} ω_C` (stated coordinatewise as
  `∀ i, incidentClauseWeight Φ ω i < α`, with `ω ≥ 0`) every global minimiser on
  the ball is Boolean. `polyLoss_embeddedBoolean` is
  `L_poly(x) = α n + ∑_{C false under x} ω_C`.
* The corollary's proof is `polynomial_residual_hardness`, proved for every
  prime `p` (the thesis remarks that "the snapping proof is independent of the
  prime"), and `dyadic_no_tractability_transfer` is its specialisation to
  `p = 2`. With unit clause weights and `α = F.pinWeight = 1 + max_i #{C ∋ z_i}`
  a global minimiser on `ℤ_2^n` exists, every such minimiser is Boolean, the
  minimum equals `α n` iff the formula is satisfiable, and any exact optimiser
  decides satisfiability through `boolReadout`.
* "Multilinear of degree at most three" is checked literally:
  `clausePolynomial C : MvPolynomial (Fin n) ℚ_[p]` evaluates to `clauseProduct`
  (`eval_clausePolynomial`), has `totalDegree ≤ 3`
  (`clausePolynomial_totalDegree_le`) and `degreeOf i ≤ 1` for every variable
  (`clausePolynomial_degreeOf_le`).
* Size accounting mirrors `FixedPrimeHardness`: `compilePolynomial F` has
  `observationCount = 2 n + m` (two unary rows per variable, one clause residual
  per clause), linear in the unit-cell size of the formula.

## What is stronger

The construction is proved for every prime, for arbitrary finite clause index
types and arbitrary nonnegative clause weights; the Lipschitz bound does not
need the perturbed value to lie in the unit ball.

## What is external

NP-hardness transfer is external: Mathlib has no P/NP framework, so "3-SAT is
NP-hard" and polynomial-time computability of `compilePolynomial` are not Lean
premises. What is checked is the semantic many-one reduction
(`compilePolynomial_correct`: `F.Satisfiable ↔ (compilePolynomial F).Accepts p`),
the Boolean snapping, the decision-by-optimiser statement
(`global_optimizer_decides_three_sat`), the degree bounds and the row count.
-/

/-- The closed unit ball `ℤ_p^n` inside `ℚ_p^n`. -/
def InUnitBall {p n : ℕ} [Fact p.Prime] (x : Parameter p n) : Prop :=
  ∀ i, ‖x i‖ ≤ 1

/-- Global minimiser of `f` among the points of the unit ball. -/
def IsGlobalMinOnBall {p n : ℕ} [Fact p.Prime]
    (f : Parameter p n → ℝ) (x : Parameter p n) : Prop :=
  InUnitBall x ∧ ∀ y, InUnitBall y → f x ≤ f y

theorem inUnitBall_update
    {p n : ℕ} [Fact p.Prime] {x : Parameter p n} (hx : InUnitBall x)
    (i : Fin n) {b : ℚ_[p]} (hb : ‖b‖ ≤ 1) :
    InUnitBall (Function.update x i b) := by
  intro j
  by_cases hji : j = i
  · subst hji
    simpa using hb
  · simpa [Function.update, hji] using hx j

theorem embeddedBoolean_inUnitBall
    {p n : ℕ} [Fact p.Prime] (s : Fin n → Bool) :
    InUnitBall (embeddedBoolean (p := p) s) := by
  intro i
  cases hs : s i <;> simp [embeddedBoolean, boolValue, hs]

/-- The clause residual `V_C(x) = ∏_{λ ∈ C} δ(λ; x)`: the product of the three
literal-failure values. Because the three literals of a `Clause` have distinct
variables, this is a multilinear polynomial of total degree at most three. -/
noncomputable def clauseProduct
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (x : Parameter p n) : ℚ_[p] :=
  ∏ k : Fin 3, literalFailureValue (C.literal k) x

/-- On Boolean points the clause residual is `0` when the clause is satisfied
and `1` when it is false. -/
theorem clauseProduct_embeddedBoolean
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (s : Fin n → Bool) :
    clauseProduct C (embeddedBoolean (p := p) s) =
      if clauseSatisfied C s then 0 else 1 := by
  rw [clauseProduct, Fin.prod_univ_three]
  simp_rw [literalFailureValue_embeddedBoolean]
  cases h₀ : literalFailureBit (C.literal 0) s <;>
    cases h₁ : literalFailureBit (C.literal 1) s <;>
    cases h₂ : literalFailureBit (C.literal 2) s <;>
    simp [clauseSatisfied, boolValue, h₀, h₁, h₂]

theorem norm_literalFailureValue_le
    {p n : ℕ} [Fact p.Prime] (l : Literal n) {x : Parameter p n}
    (hx : InUnitBall x) :
    ‖literalFailureValue l x‖ ≤ 1 := by
  rw [literalFailureValue]
  split_ifs
  · calc
      ‖1 - x l.var‖ = ‖(1 : ℚ_[p]) + (-(x l.var))‖ := by rw [sub_eq_add_neg]
      _ ≤ max ‖(1 : ℚ_[p])‖ ‖-(x l.var)‖ := Padic.nonarchimedean _ _
      _ ≤ 1 := by
        rw [norm_neg, norm_one]
        exact max_le le_rfl (hx _)
  · exact hx _

theorem norm_clauseProduct_le
    {p n : ℕ} [Fact p.Prime] (C : Clause n) {x : Parameter p n}
    (hx : InUnitBall x) :
    ‖clauseProduct C x‖ ≤ 1 := by
  rw [clauseProduct, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun k _ => norm_literalFailureValue_le _ hx)

theorem literalFailureValue_update_of_ne
    {p n : ℕ} [Fact p.Prime] (l : Literal n) (x : Parameter p n)
    (i : Fin n) (b : ℚ_[p]) (h : l.var ≠ i) :
    literalFailureValue l (Function.update x i b) =
      literalFailureValue l x := by
  simp [literalFailureValue, Function.update, h]

theorem norm_literalFailureValue_update_sub
    {p n : ℕ} [Fact p.Prime] (l : Literal n) (x : Parameter p n)
    (b : ℚ_[p]) :
    ‖literalFailureValue l (Function.update x l.var b) -
        literalFailureValue l x‖ = ‖b - x l.var‖ := by
  rw [literalFailureValue, literalFailureValue]
  split_ifs
  · simp only [Function.update_self]
    rw [show (1 - b) - (1 - x l.var) = -(b - x l.var) by ring, norm_neg]
  · simp only [Function.update_self]

/-- A clause whose variables avoid coordinate `i` has a residual that does not
depend on `x i`. -/
theorem clauseProduct_update_of_not_occurs
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (x : Parameter p n)
    (i : Fin n) (b : ℚ_[p]) (h : ¬ ∃ k, (C.literal k).var = i) :
    clauseProduct C (Function.update x i b) = clauseProduct C x := by
  rw [clauseProduct, clauseProduct]
  refine Finset.prod_congr rfl fun k _ => ?_
  exact literalFailureValue_update_of_ne _ _ _ _ (fun hk => h ⟨k, hk⟩)

theorem clauseProduct_update_sub
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (x : Parameter p n)
    (i : Fin n) (b : ℚ_[p]) (k₀ : Fin 3) (hk₀ : (C.literal k₀).var = i) :
    clauseProduct C (Function.update x i b) - clauseProduct C x =
      (∏ k ∈ Finset.univ.erase k₀, literalFailureValue (C.literal k) x) *
        (literalFailureValue (C.literal k₀) (Function.update x i b) -
          literalFailureValue (C.literal k₀) x) := by
  classical
  rw [clauseProduct, clauseProduct,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ k₀),
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ k₀)]
  have hrest :
      (∏ k ∈ Finset.univ.erase k₀,
          literalFailureValue (C.literal k) (Function.update x i b)) =
        ∏ k ∈ Finset.univ.erase k₀, literalFailureValue (C.literal k) x := by
    apply Finset.prod_congr rfl
    intro k hk
    apply literalFailureValue_update_of_ne
    intro hki
    exact Finset.ne_of_mem_erase hk
      (C.variables_injective (hki.trans hk₀.symm))
  rw [hrest]
  ring

/-- Each clause residual is `1`-Lipschitz in every coordinate on the unit ball:
changing `x i` to `b` moves `V_C` by at most `‖b - x i‖`. Only `x` needs to lie
in the unit ball; no bound on `b` is required. -/
theorem norm_clauseProduct_update_sub_le
    {p n : ℕ} [Fact p.Prime] (C : Clause n) {x : Parameter p n}
    (hx : InUnitBall x) (i : Fin n) (b : ℚ_[p])
    (hocc : ∃ k, (C.literal k).var = i) :
    ‖clauseProduct C (Function.update x i b) - clauseProduct C x‖ ≤
      ‖b - x i‖ := by
  classical
  obtain ⟨k₀, hk₀⟩ := hocc
  rw [clauseProduct_update_sub C x i b k₀ hk₀, norm_mul]
  have hrest :
      ‖∏ k ∈ Finset.univ.erase k₀, literalFailureValue (C.literal k) x‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun k _ => norm_literalFailureValue_le _ hx)
  have hdiff :
      ‖literalFailureValue (C.literal k₀) (Function.update x i b) -
          literalFailureValue (C.literal k₀) x‖ = ‖b - x i‖ := by
    subst hk₀
    exact norm_literalFailureValue_update_sub _ _ _
  rw [hdiff]
  calc
    ‖∏ k ∈ Finset.univ.erase k₀, literalFailureValue (C.literal k) x‖ *
        ‖b - x i‖ ≤ 1 * ‖b - x i‖ :=
      mul_le_mul_of_nonneg_right hrest (norm_nonneg _)
    _ = ‖b - x i‖ := one_mul _

/-! ## The positive polynomial-residual objective `L_poly` -/

/-- The positive polynomial-residual objective
`L_poly(x) = α ∑ᵢ (‖xᵢ‖ + ‖xᵢ - 1‖) + ∑_C ω_C ‖V_C(x)‖`
for a clause family `Φ`, clause weights `ω` and pinning weight `α`. -/
noncomputable def polyLoss
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (ω : κ → ℝ) (α : ℝ) (x : Parameter p n) : ℝ :=
  α * ∑ i, (‖x i‖ + ‖x i - 1‖) + ∑ r, ω r * ‖clauseProduct (Φ r) x‖

/-- `∑_{C ∋ z_i} ω_C`: the total clause weight incident to variable `i`. -/
noncomputable def incidentClauseWeight
    {n : ℕ} {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (ω : κ → ℝ) (i : Fin n) : ℝ :=
  ∑ r, if ∃ k, ((Φ r).literal k).var = i then ω r else 0

theorem incidentClauseWeight_nonneg
    {n : ℕ} {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) {ω : κ → ℝ} (hω : ∀ r, 0 ≤ ω r) (i : Fin n) :
    0 ≤ incidentClauseWeight Φ ω i := by
  rw [incidentClauseWeight]
  apply Finset.sum_nonneg
  intro r _
  split_ifs
  · exact hω r
  · exact le_rfl

/-- With unit clause weights the incident weight is the variable degree
(the number of clauses containing the variable). -/
theorem incidentClauseWeight_unit
    {n : ℕ} {κ : Type*} [Fintype κ] (Φ : κ → Clause n) (i : Fin n) :
    incidentClauseWeight Φ (fun _ => (1 : ℝ)) i = variableDegree Φ i := by
  rw [incidentClauseWeight, variableDegree]

theorem unaryCost_booleanDomain
    {p n : ℕ} [Fact p.Prime] (i : Fin n) (t : ℚ_[p]) :
    unaryCost (booleanDomain (p := p) i) t = ‖t‖ + ‖t - 1‖ := by
  simp [unaryCost, booleanDomain]

theorem unarySum_update
    {p n : ℕ} [Fact p.Prime] (x : Parameter p n) (i : Fin n) (b : ℚ_[p]) :
    (∑ j, (‖Function.update x i b j‖ + ‖Function.update x i b j - 1‖)) -
        ∑ j, (‖x j‖ + ‖x j - 1‖) =
      (‖b‖ + ‖b - 1‖) - (‖x i‖ + ‖x i - 1‖) := by
  classical
  have hsum :
      (∑ j ∈ Finset.univ \ {i},
          (‖Function.update x i b j‖ + ‖Function.update x i b j - 1‖)) =
        ∑ j ∈ Finset.univ \ {i}, (‖x j‖ + ‖x j - 1‖) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [Function.update, hji]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
  rw [show Function.update x i b i = b by simp, hsum]
  ring

/-- Changing coordinate `i` of a point of the unit ball to `b` increases the
weighted clause penalties by at most `(∑_{C ∋ z_i} ω_C) ‖b - x i‖`. -/
theorem clauseSum_update_sub_le
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) {ω : κ → ℝ} (hω : ∀ r, 0 ≤ ω r)
    {x : Parameter p n} (hx : InUnitBall x) (i : Fin n) (b : ℚ_[p]) :
    (∑ r, ω r * ‖clauseProduct (Φ r) (Function.update x i b)‖) -
        ∑ r, ω r * ‖clauseProduct (Φ r) x‖ ≤
      incidentClauseWeight Φ ω i * ‖b - x i‖ := by
  rw [← Finset.sum_sub_distrib, incidentClauseWeight, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r _
  by_cases hocc : ∃ k, ((Φ r).literal k).var = i
  · rw [if_pos hocc, ← mul_sub]
    apply mul_le_mul_of_nonneg_left _ (hω r)
    exact (norm_sub_norm_le _ _).trans
      (norm_clauseProduct_update_sub_le (Φ r) hx i b hocc)
  · rw [if_neg hocc, zero_mul,
      clauseProduct_update_of_not_occurs (Φ r) x i b hocc]
    simp

/-- Digit snapping for `L_poly`: if `α` exceeds the incident clause weight of
every variable and `x i` is not Boolean, snapping `x i` to a suitable
`b ∈ {0, 1}` strictly decreases the objective. -/
theorem polyLoss_snap_lt
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) {ω : κ → ℝ} {α : ℝ} (hω : ∀ r, 0 ≤ ω r)
    (hα : ∀ i, incidentClauseWeight Φ ω i < α)
    {x : Parameter p n} (hx : InUnitBall x) (i : Fin n)
    (hxi : x i ≠ 0 ∧ x i ≠ 1) :
    ∃ b : ℚ_[p], (b = 0 ∨ b = 1) ∧
      polyLoss Φ ω α (Function.update x i b) < polyLoss Φ ω α x := by
  obtain ⟨b, hb, hsnap⟩ :=
    exists_unaryCost_snap (booleanDomain_nonempty (p := p) i)
      (booleanDomain_unitSeparated i) (x := x i)
  have hb' : b = 0 ∨ b = 1 := by simpa [booleanDomain] using hb
  refine ⟨b, hb', ?_⟩
  rw [unaryCost_booleanDomain, unaryCost_booleanDomain] at hsnap
  have hunary := unarySum_update x i b
  have hclause := clauseSum_update_sub_le Φ hω hx i b
  have hpos : 0 < ‖x i - b‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    rcases hb' with rfl | rfl
    · exact hxi.1
    · exact hxi.2
  have hW : 0 ≤ incidentClauseWeight Φ ω i :=
    incidentClauseWeight_nonneg Φ hω i
  have hαpos : 0 < α := lt_of_le_of_lt hW (hα i)
  have hrev : ‖b - x i‖ = ‖x i - b‖ := norm_sub_rev _ _
  rw [hrev] at hclause
  have hneg : (incidentClauseWeight Φ ω i - α) * ‖x i - b‖ < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr (hα i)) hpos
  have hunary' :
      α * ((∑ j, (‖Function.update x i b j‖ + ‖Function.update x i b j - 1‖)) -
        ∑ j, (‖x j‖ + ‖x j - 1‖)) ≤ α * (-‖x i - b‖) := by
    apply mul_le_mul_of_nonneg_left _ hαpos.le
    linarith
  rw [polyLoss, polyLoss]
  nlinarith [hunary', hclause, hneg]

/-- Every global minimiser of `L_poly` on the unit ball is Boolean. -/
theorem globalMinOnBall_boolean
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) {ω : κ → ℝ} {α : ℝ} (hω : ∀ r, 0 ≤ ω r)
    (hα : ∀ i, incidentClauseWeight Φ ω i < α)
    {x : Parameter p n} (hmin : IsGlobalMinOnBall (polyLoss Φ ω α) x) :
    ∀ i, x i = 0 ∨ x i = 1 := by
  intro i
  by_contra hne
  push_neg at hne
  obtain ⟨b, hb, hlt⟩ := polyLoss_snap_lt Φ hω hα hmin.1 i hne
  have hball : InUnitBall (Function.update x i b) :=
    inUnitBall_update hmin.1 i (by rcases hb with rfl | rfl <;> simp)
  exact absurd (hmin.2 _ hball) (not_le.mpr hlt)

/-- On Boolean assignments `L_poly = α n + ∑_{C false under s} ω_C`. -/
theorem polyLoss_embeddedBoolean
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (ω : κ → ℝ) (α : ℝ) (s : Fin n → Bool) :
    polyLoss Φ ω α (embeddedBoolean (p := p) s) =
      α * n + ∑ r ∈ Finset.univ.filter (fun r => ¬ clauseSatisfied (Φ r) s),
        ω r := by
  classical
  rw [polyLoss, Finset.sum_filter]
  have hunary : ∀ i,
      ‖embeddedBoolean (p := p) s i‖ + ‖embeddedBoolean (p := p) s i - 1‖ = 1 := by
    intro i
    cases hs : s i <;> simp [embeddedBoolean, boolValue, hs]
  simp_rw [hunary, clauseProduct_embeddedBoolean]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp

theorem le_polyLoss_embeddedBoolean
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) {ω : κ → ℝ} (hω : ∀ r, 0 ≤ ω r) (α : ℝ)
    (s : Fin n → Bool) :
    α * n ≤ polyLoss Φ ω α (embeddedBoolean (p := p) s) := by
  rw [polyLoss_embeddedBoolean]
  have hnonneg :
      0 ≤ ∑ r ∈ Finset.univ.filter (fun r => ¬ clauseSatisfied (Φ r) s), ω r :=
    Finset.sum_nonneg fun r _ => hω r
  linarith

/-! ## Global minimisers on the unit ball -/

/-- Repeated snapping: every point of the unit ball is dominated by a Boolean
point. -/
theorem exists_boolean_not_greater
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) {ω : κ → ℝ} {α : ℝ} (hω : ∀ r, 0 ≤ ω r)
    (hα : ∀ i, incidentClauseWeight Φ ω i < α)
    (x : Parameter p n) (hx : InUnitBall x) :
    ∃ s : Fin n → Bool,
      polyLoss Φ ω α (embeddedBoolean (p := p) s) ≤ polyLoss Φ ω α x := by
  classical
  generalize hk : (outsideDomain (booleanDomain (p := p)) x).card = k
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
      by_cases hxD : InDomain (booleanDomain (p := p)) x
      · obtain ⟨s, rfl⟩ := inBooleanDomain_exists_embedded x hxD
        exact ⟨s, le_rfl⟩
      · have hbad : (outsideDomain (booleanDomain (p := p)) x).Nonempty := by
          exact Finset.nonempty_iff_ne_empty.mpr fun hempty =>
            hxD ((outsideDomain_eq_empty_iff _ x).mp hempty)
        obtain ⟨i, hi⟩ := hbad
        have hxi : x i ≠ 0 ∧ x i ≠ 1 := by
          have hnot : x i ∉ booleanDomain (p := p) i := by
            simpa [outsideDomain] using hi
          simpa [booleanDomain, not_or] using hnot
        obtain ⟨b, hb, hlt⟩ := polyLoss_snap_lt Φ hω hα hx i hxi
        have hbD : b ∈ booleanDomain (p := p) i := by
          simp [booleanDomain, hb]
        have hball : InUnitBall (Function.update x i b) :=
          inUnitBall_update hx i (by rcases hb with rfl | rfl <;> simp)
        have hcardlt :
            (outsideDomain (booleanDomain (p := p))
              (Function.update x i b)).card < k := by
          have hpos : 0 < (outsideDomain (booleanDomain (p := p)) x).card :=
            Finset.card_pos.mpr ⟨i, hi⟩
          rw [outsideDomain_update _ x i b hbD, Finset.card_erase_of_mem hi, hk]
          omega
        obtain ⟨s, hs⟩ := ih _ hcardlt (Function.update x i b) hball rfl
        exact ⟨s, hs.trans hlt.le⟩

/-- The lower bound `α n ≤ L_poly` on the whole unit ball. -/
theorem le_polyLoss_of_inUnitBall
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) {ω : κ → ℝ} {α : ℝ} (hω : ∀ r, 0 ≤ ω r)
    (hα : ∀ i, incidentClauseWeight Φ ω i < α)
    {x : Parameter p n} (hx : InUnitBall x) :
    α * n ≤ polyLoss Φ ω α x := by
  obtain ⟨s, hs⟩ := exists_boolean_not_greater Φ hω hα x hx
  exact (le_polyLoss_embeddedBoolean Φ hω α s).trans hs

/-- A global minimiser of `L_poly` on the unit ball exists. -/
theorem exists_globalMinOnBall
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) {ω : κ → ℝ} {α : ℝ} (hω : ∀ r, 0 ≤ ω r)
    (hα : ∀ i, incidentClauseWeight Φ ω i < α) :
    ∃ x : Parameter p n, IsGlobalMinOnBall (polyLoss Φ ω α) x := by
  classical
  have huniv : (Finset.univ : Finset (Fin n → Bool)).Nonempty :=
    ⟨fun _ => false, Finset.mem_univ _⟩
  obtain ⟨s, _, hs⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin n → Bool))
      (fun t => polyLoss Φ ω α (embeddedBoolean (p := p) t)) huniv
  refine ⟨embeddedBoolean (p := p) s, embeddedBoolean_inUnitBall s, ?_⟩
  intro y hy
  obtain ⟨t, ht⟩ := exists_boolean_not_greater Φ hω hα y hy
  exact (hs t (Finset.mem_univ _)).trans ht

/-! ## Reading a Boolean assignment off an optimiser -/

/-- The Boolean assignment read off a parameter vector: `true` exactly where
the coordinate equals `1`. -/
noncomputable def boolReadout
    {p n : ℕ} [Fact p.Prime] (x : Parameter p n) : Fin n → Bool := by
  classical
  exact fun i => decide (x i = 1)

theorem embeddedBoolean_boolReadout
    {p n : ℕ} [Fact p.Prime] {x : Parameter p n}
    (hx : ∀ i, x i = 0 ∨ x i = 1) :
    embeddedBoolean (p := p) (boolReadout x) = x := by
  funext i
  rcases hx i with h | h <;> simp [embeddedBoolean, boolReadout, boolValue, h]

/-- Number of clauses falsified by a Boolean assignment. -/
noncomputable def falseCount
    {n : ℕ} {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (s : Fin n → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter fun r => ¬ clauseSatisfied (Φ r) s).card

theorem falseCount_eq_zero_iff
    {n : ℕ} {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (s : Fin n → Bool) :
    falseCount Φ s = 0 ↔ FormulaSatisfied Φ s := by
  classical
  rw [falseCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp [FormulaSatisfied]

/-- With unit clause weights, `L_poly = α n + #(false clauses)` on Boolean
assignments. -/
theorem polyLoss_unit_embeddedBoolean
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (α : ℝ) (s : Fin n → Bool) :
    polyLoss Φ (fun _ => (1 : ℝ)) α (embeddedBoolean (p := p) s) =
      α * n + falseCount Φ s := by
  classical
  rw [polyLoss_embeddedBoolean, falseCount]
  simp

/-! ## Unit-weight satisfiability criteria (any prime) -/

theorem unit_weights_nonneg {κ : Type*} : ∀ r : κ, (0 : ℝ) ≤ (fun _ => (1 : ℝ)) r :=
  fun _ => zero_le_one

theorem incidentClauseWeight_unit_lt
    {n : ℕ} {κ : Type*} [Fintype κ] (Φ : κ → Clause n) {α : ℝ}
    (hα : ∀ i, variableDegree Φ i < α) (i : Fin n) :
    incidentClauseWeight Φ (fun _ => (1 : ℝ)) i < α := by
  rw [incidentClauseWeight_unit]
  exact hα i

/-- Every global minimiser on the ball has value `α n` iff the formula is
satisfiable (unit clause weights, `α` above every variable degree). -/
theorem globalMinOnBall_value_iff_satisfiable
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) {α : ℝ} (hα : ∀ i, variableDegree Φ i < α)
    {x : Parameter p n}
    (hmin : IsGlobalMinOnBall (polyLoss Φ (fun _ => (1 : ℝ)) α) x) :
    polyLoss Φ (fun _ => (1 : ℝ)) α x = α * n ↔
      ∃ s : Fin n → Bool, FormulaSatisfied Φ s := by
  have hα' := incidentClauseWeight_unit_lt Φ hα
  have hbool := globalMinOnBall_boolean Φ unit_weights_nonneg hα' hmin
  constructor
  · intro hval
    refine ⟨boolReadout x, (falseCount_eq_zero_iff Φ _).mp ?_⟩
    have hx := embeddedBoolean_boolReadout (p := p) hbool
    rw [← hx, polyLoss_unit_embeddedBoolean] at hval
    exact_mod_cast (by linarith : (falseCount Φ (boolReadout x) : ℝ) = 0)
  · rintro ⟨s, hs⟩
    have hval : polyLoss Φ (fun _ => (1 : ℝ)) α (embeddedBoolean (p := p) s) =
        α * n := by
      rw [polyLoss_unit_embeddedBoolean, (falseCount_eq_zero_iff Φ s).mpr hs]
      simp
    have hle := hmin.2 _ (embeddedBoolean_inUnitBall s)
    have hge := le_polyLoss_of_inUnitBall Φ unit_weights_nonneg hα' hmin.1
    linarith

/-- The minimum of `L_poly` over the ball is `α n` iff the formula is
satisfiable. -/
theorem exists_globalMinOnBall_value_iff_satisfiable
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) {α : ℝ} (hα : ∀ i, variableDegree Φ i < α) :
    (∃ x : Parameter p n,
      IsGlobalMinOnBall (polyLoss Φ (fun _ => (1 : ℝ)) α) x ∧
        polyLoss Φ (fun _ => (1 : ℝ)) α x = α * n) ↔
      ∃ s : Fin n → Bool, FormulaSatisfied Φ s := by
  have hα' := incidentClauseWeight_unit_lt Φ hα
  constructor
  · rintro ⟨x, hmin, hval⟩
    exact (globalMinOnBall_value_iff_satisfiable Φ hα hmin).mp hval
  · rintro ⟨s, hs⟩
    have hval : polyLoss Φ (fun _ => (1 : ℝ)) α (embeddedBoolean (p := p) s) =
        α * n := by
      rw [polyLoss_unit_embeddedBoolean, (falseCount_eq_zero_iff Φ s).mpr hs]
      simp
    refine ⟨embeddedBoolean (p := p) s, ⟨embeddedBoolean_inUnitBall s, ?_⟩, hval⟩
    intro y hy
    rw [hval]
    exact le_polyLoss_of_inUnitBall Φ unit_weights_nonneg hα' hy

/-- Any exact global optimiser on the ball decides satisfiability: the formula
is satisfiable iff the Boolean assignment read off the optimiser satisfies
it. -/
theorem globalMinOnBall_readout_decides
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) {α : ℝ} (hα : ∀ i, variableDegree Φ i < α)
    {x : Parameter p n}
    (hmin : IsGlobalMinOnBall (polyLoss Φ (fun _ => (1 : ℝ)) α) x) :
    (∃ s : Fin n → Bool, FormulaSatisfied Φ s) ↔
      FormulaSatisfied Φ (boolReadout x) := by
  constructor
  · intro hsat
    have hα' := incidentClauseWeight_unit_lt Φ hα
    have hbool := globalMinOnBall_boolean Φ unit_weights_nonneg hα' hmin
    have hval := (globalMinOnBall_value_iff_satisfiable Φ hα hmin).mpr hsat
    have hx := embeddedBoolean_boolReadout (p := p) hbool
    rw [← hx, polyLoss_unit_embeddedBoolean] at hval
    exact (falseCount_eq_zero_iff Φ _).mp
      (by exact_mod_cast (by linarith : (falseCount Φ (boolReadout x) : ℝ) = 0))
  · intro h
    exact ⟨_, h⟩

/-! ## Degree accounting: each clause residual is multilinear of degree ≤ 3 -/

/-- The literal-failure polynomial `X_i` (positive literal) or `1 - X_i`
(negated literal). -/
noncomputable def literalPolynomial
    {p n : ℕ} [Fact p.Prime] (l : Literal n) : MvPolynomial (Fin n) ℚ_[p] :=
  if l.negated then 1 - MvPolynomial.X l.var else MvPolynomial.X l.var

/-- The clause residual as a polynomial: the product of its three
literal-failure polynomials. -/
noncomputable def clausePolynomial
    {p n : ℕ} [Fact p.Prime] (C : Clause n) : MvPolynomial (Fin n) ℚ_[p] :=
  ∏ k : Fin 3, literalPolynomial (C.literal k)

theorem eval_literalPolynomial
    {p n : ℕ} [Fact p.Prime] (l : Literal n) (x : Parameter p n) :
    MvPolynomial.eval x (literalPolynomial (p := p) l) =
      literalFailureValue l x := by
  rw [literalPolynomial, literalFailureValue]
  split_ifs <;> simp

/-- The clause residual `V_C` is the evaluation of `clausePolynomial C`. -/
theorem eval_clausePolynomial
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (x : Parameter p n) :
    MvPolynomial.eval x (clausePolynomial (p := p) C) = clauseProduct C x := by
  rw [clausePolynomial, clauseProduct, MvPolynomial.eval_prod]
  exact Finset.prod_congr rfl fun k _ => eval_literalPolynomial _ _

theorem literalPolynomial_totalDegree_le
    {p n : ℕ} [Fact p.Prime] (l : Literal n) :
    (literalPolynomial (p := p) l).totalDegree ≤ 1 := by
  rw [literalPolynomial]
  split_ifs
  · refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X]
    simp
  · rw [MvPolynomial.totalDegree_X]

/-- Each clause residual has total degree at most three. -/
theorem clausePolynomial_totalDegree_le
    {p n : ℕ} [Fact p.Prime] (C : Clause n) :
    (clausePolynomial (p := p) C).totalDegree ≤ 3 := by
  rw [clausePolynomial]
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  calc
    (∑ k : Fin 3, (literalPolynomial (p := p) (C.literal k)).totalDegree) ≤
        ∑ _k : Fin 3, 1 :=
      Finset.sum_le_sum fun k _ => literalPolynomial_totalDegree_le _
    _ = 3 := by simp

theorem literalPolynomial_degreeOf_le
    {p n : ℕ} [Fact p.Prime] (l : Literal n) (i : Fin n) :
    MvPolynomial.degreeOf i (literalPolynomial (p := p) l) ≤
      if l.var = i then 1 else 0 := by
  rw [literalPolynomial]
  have hX : MvPolynomial.degreeOf i (MvPolynomial.X l.var : MvPolynomial (Fin n) ℚ_[p]) =
      if l.var = i then 1 else 0 := by
    rw [MvPolynomial.degreeOf_X]
    simp only [eq_comm]
  have hone : MvPolynomial.degreeOf i (1 : MvPolynomial (Fin n) ℚ_[p]) = 0 := by
    simpa using MvPolynomial.degreeOf_C (1 : ℚ_[p]) i
  by_cases hneg : l.negated
  · rw [if_pos hneg]
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans ?_
    rw [hone, hX]
    split_ifs <;> simp
  · rw [if_neg hneg, hX]

/-- Each clause residual is multilinear: every variable has degree at most one
in it (the three literals have distinct variables). -/
theorem clausePolynomial_degreeOf_le
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (i : Fin n) :
    MvPolynomial.degreeOf i (clausePolynomial (p := p) C) ≤ 1 := by
  classical
  rw [clausePolynomial]
  refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
  refine (Finset.sum_le_sum fun k _ => literalPolynomial_degreeOf_le (p := p)
    (C.literal k) i).trans ?_
  by_cases hocc : ∃ k, (C.literal k).var = i
  · obtain ⟨k₀, hk₀⟩ := hocc
    rw [Finset.sum_eq_single k₀]
    · simp [hk₀]
    · intro k _ hk
      have hne : (C.literal k).var ≠ i := fun h =>
        hk (C.variables_injective (h.trans hk₀.symm))
      simp [hne]
    · simp
  · push_neg at hocc
    simp [hocc]

/-! ## The decision instance and its size -/

/-- A positive polynomial-residual instance: `numVars` Boolean wells of weight
`pinWeight` (two unary rows `‖xᵢ‖`, `‖xᵢ - 1‖` each) and `numResiduals` unit
weight clause residuals, each a product of at most three affine factors. -/
structure PositivePolynomialInstance where
  numVars : ℕ
  numResiduals : ℕ
  residual : Fin numResiduals → Clause numVars
  pinWeight : ℕ

/-- The objective of an instance over `ℚ_p^n` (used on the unit ball). -/
noncomputable def PositivePolynomialInstance.loss
    (p : ℕ) [Fact p.Prime] (I : PositivePolynomialInstance)
    (x : Parameter p I.numVars) : ℝ :=
  (I.pinWeight : ℝ) * ∑ i, (‖x i‖ + ‖x i - 1‖) +
    ∑ r, ‖clauseProduct (I.residual r) x‖

/-- The decision problem: does the objective reach `α n` on the unit ball? -/
def PositivePolynomialInstance.Accepts
    (p : ℕ) [Fact p.Prime] (I : PositivePolynomialInstance) : Prop :=
  ∃ x : Parameter p I.numVars,
    InUnitBall x ∧ I.loss p x ≤ (I.pinWeight : ℝ) * I.numVars

/-- Number of residual rows: two unary rows per variable plus one clause
residual per clause. -/
def PositivePolynomialInstance.observationCount
    (I : PositivePolynomialInstance) : ℕ :=
  2 * I.numVars + I.numResiduals

/-- The compilation of a 3-CNF formula: unit clause weights and pinning weight
`α = 1 + max_i #{C ∋ z_i}`. -/
def compilePolynomial (F : ThreeCNF) : PositivePolynomialInstance where
  numVars := F.numVars
  numResiduals := F.numClauses
  residual := F.clause
  pinWeight := F.pinWeight

theorem compilePolynomial_loss
    (p : ℕ) [Fact p.Prime] (F : ThreeCNF) (x : Parameter p F.numVars) :
    (compilePolynomial F).loss p x =
      polyLoss F.clause (fun _ => (1 : ℝ)) (F.pinWeight : ℝ) x := by
  simp [PositivePolynomialInstance.loss, polyLoss, compilePolynomial]

theorem compilePolynomial_numVars (F : ThreeCNF) :
    (compilePolynomial F).numVars = F.numVars := rfl

theorem compilePolynomial_pinWeight (F : ThreeCNF) :
    (compilePolynomial F).pinWeight = F.pinWeight := rfl

theorem compilePolynomial_observationCount (F : ThreeCNF) :
    (compilePolynomial F).observationCount = 2 * F.numVars + F.numClauses := by
  rfl

theorem compilePolynomial_observationCount_linear (F : ThreeCNF) :
    (compilePolynomial F).observationCount ≤ 2 * F.cellSize := by
  rw [compilePolynomial_observationCount, ThreeCNF.cellSize]
  omega

/-- Semantic correctness of the reduction at every prime: `F` is satisfiable
iff the compiled objective reaches `α n` somewhere on the unit ball. -/
theorem compilePolynomial_correct
    (p : ℕ) [Fact p.Prime] (F : ThreeCNF) :
    F.Satisfiable ↔ (compilePolynomial F).Accepts p := by
  have hα : ∀ i, variableDegree F.clause i < (F.pinWeight : ℝ) :=
    F.variableDegree_lt_pinWeight
  have hα' := incidentClauseWeight_unit_lt F.clause hα
  simp only [PositivePolynomialInstance.Accepts, compilePolynomial_loss,
    compilePolynomial_numVars, compilePolynomial_pinWeight]
  constructor
  · intro hsat
    obtain ⟨x, hmin, hval⟩ :=
      (exists_globalMinOnBall_value_iff_satisfiable (p := p) F.clause hα).mpr hsat
    exact ⟨x, hmin.1, hval.le⟩
  · rintro ⟨x, hx, hle⟩
    obtain ⟨g, hgmin⟩ :=
      exists_globalMinOnBall (p := p) F.clause unit_weights_nonneg hα'
    refine (globalMinOnBall_value_iff_satisfiable F.clause hα hgmin).mp ?_
    have hge := le_polyLoss_of_inUnitBall F.clause unit_weights_nonneg hα' hgmin.1
    have hle' := hgmin.2 x hx
    linarith

/-- Any exact global optimiser for the instance class decides 3-SAT (at every
prime): either through the optimal value or through the Boolean readout. -/
theorem global_optimizer_decides_three_sat
    (p : ℕ) [Fact p.Prime]
    (solve : (I : PositivePolynomialInstance) → Parameter p I.numVars)
    (optimal : ∀ I : PositivePolynomialInstance,
      IsGlobalMinOnBall (I.loss p) (solve I))
    (F : ThreeCNF) :
    (F.Satisfiable ↔
      (compilePolynomial F).loss p (solve (compilePolynomial F)) ≤
        (F.pinWeight : ℝ) * F.numVars) ∧
    (F.Satisfiable ↔
      FormulaSatisfied F.clause (boolReadout (solve (compilePolynomial F)))) := by
  have hα : ∀ i, variableDegree F.clause i < (F.pinWeight : ℝ) :=
    F.variableDegree_lt_pinWeight
  have hmin : IsGlobalMinOnBall
      (polyLoss (p := p) F.clause (fun _ => (1 : ℝ)) (F.pinWeight : ℝ))
      (solve (compilePolynomial F)) := by
    have h := optimal (compilePolynomial F)
    refine ⟨h.1, fun y hy => ?_⟩
    have := h.2 y hy
    simpa [compilePolynomial_loss] using this
  refine ⟨?_, globalMinOnBall_readout_decides F.clause hα hmin⟩
  rw [compilePolynomial_loss]
  constructor
  · intro hsat
    exact ((globalMinOnBall_value_iff_satisfiable F.clause hα hmin).mpr hsat).le
  · intro hle
    refine (globalMinOnBall_value_iff_satisfiable F.clause hα hmin).mp ?_
    have hge := le_polyLoss_of_inUnitBall F.clause unit_weights_nonneg
      (incidentClauseWeight_unit_lt F.clause hα) hmin.1
    linarith

/-! ## Headline statements -/

/-- The unit-weight objective of the thesis construction for a 3-CNF formula,
with pinning weight `α = 1 + max_i #{C ∋ z_i}`. -/
noncomputable def unitPolyLoss
    (p : ℕ) [Fact p.Prime] (F : ThreeCNF) : Parameter p F.numVars → ℝ :=
  polyLoss F.clause (fun _ => (1 : ℝ)) (F.pinWeight : ℝ)

/-- The construction at an arbitrary prime `p`: existence of ball-minimisers,
Booleanity of every ball-minimiser, the value criterion `min = α n ↔ Sat`,
decision by Boolean readout, multilinearity and degree `≤ 3` of every clause
residual, and the `2n + m` row count. -/
theorem polynomial_residual_hardness
    (p : ℕ) [Fact p.Prime] (F : ThreeCNF) :
    (∃ x, IsGlobalMinOnBall (unitPolyLoss p F) x) ∧
    (∀ x, IsGlobalMinOnBall (unitPolyLoss p F) x → ∀ i, x i = 0 ∨ x i = 1) ∧
    (∀ s, unitPolyLoss p F (embeddedBoolean s) =
      (F.pinWeight : ℝ) * F.numVars + falseCount F.clause s) ∧
    (∀ x, IsGlobalMinOnBall (unitPolyLoss p F) x →
      (unitPolyLoss p F x = (F.pinWeight : ℝ) * F.numVars ↔ F.Satisfiable)) ∧
    ((∃ x, IsGlobalMinOnBall (unitPolyLoss p F) x ∧
      unitPolyLoss p F x = (F.pinWeight : ℝ) * F.numVars) ↔ F.Satisfiable) ∧
    (∀ x, IsGlobalMinOnBall (unitPolyLoss p F) x →
      (F.Satisfiable ↔ FormulaSatisfied F.clause (boolReadout x))) ∧
    (∀ r, (clausePolynomial (p := p) (F.clause r)).totalDegree ≤ 3 ∧
      ∀ i, MvPolynomial.degreeOf i (clausePolynomial (p := p) (F.clause r)) ≤ 1) ∧
    (compilePolynomial F).observationCount = 2 * F.numVars + F.numClauses := by
  have hα : ∀ i, variableDegree F.clause i < (F.pinWeight : ℝ) :=
    F.variableDegree_lt_pinWeight
  have hα' := incidentClauseWeight_unit_lt F.clause hα
  refine ⟨exists_globalMinOnBall F.clause unit_weights_nonneg hα',
    fun x hx => globalMinOnBall_boolean F.clause unit_weights_nonneg hα' hx,
    fun s => polyLoss_unit_embeddedBoolean F.clause _ s,
    fun x hx => globalMinOnBall_value_iff_satisfiable F.clause hα hx,
    exists_globalMinOnBall_value_iff_satisfiable F.clause hα,
    fun x hx => globalMinOnBall_readout_decides F.clause hα hx,
    fun r => ⟨clausePolynomial_totalDegree_le _,
      fun i => clausePolynomial_degreeOf_le _ i⟩,
    compilePolynomial_observationCount F⟩

/-- Thesis Corollary `cor:sudoku-polynomial-dyadic-hardness` ("No dyadic
tractability transfer"), semantic part: over `ℤ_2^n` the unit-weight positive
polynomial-residual objective of any 3-CNF formula has Boolean ball-minimisers,
its minimum is `α n` iff the formula is satisfiable, any exact optimiser decides
satisfiability, every non-unary residual is multilinear of degree at most
three, and the instance has `2n + m` rows. -/
theorem dyadic_no_tractability_transfer (F : ThreeCNF) :
    (∃ x, IsGlobalMinOnBall (unitPolyLoss 2 F) x) ∧
    (∀ x, IsGlobalMinOnBall (unitPolyLoss 2 F) x → ∀ i, x i = 0 ∨ x i = 1) ∧
    (∀ s, unitPolyLoss 2 F (embeddedBoolean s) =
      (F.pinWeight : ℝ) * F.numVars + falseCount F.clause s) ∧
    (∀ x, IsGlobalMinOnBall (unitPolyLoss 2 F) x →
      (unitPolyLoss 2 F x = (F.pinWeight : ℝ) * F.numVars ↔ F.Satisfiable)) ∧
    ((∃ x, IsGlobalMinOnBall (unitPolyLoss 2 F) x ∧
      unitPolyLoss 2 F x = (F.pinWeight : ℝ) * F.numVars) ↔ F.Satisfiable) ∧
    (∀ x, IsGlobalMinOnBall (unitPolyLoss 2 F) x →
      (F.Satisfiable ↔ FormulaSatisfied F.clause (boolReadout x))) ∧
    (∀ r, (clausePolynomial (p := 2) (F.clause r)).totalDegree ≤ 3 ∧
      ∀ i, MvPolynomial.degreeOf i (clausePolynomial (p := 2) (F.clause r)) ≤ 1) ∧
    (compilePolynomial F).observationCount = 2 * F.numVars + F.numClauses :=
  polynomial_residual_hardness 2 F

/-- The many-one reduction of the corollary at `p = 2`. -/
theorem dyadic_compilePolynomial_correct (F : ThreeCNF) :
    F.Satisfiable ↔ (compilePolynomial F).Accepts 2 :=
  compilePolynomial_correct 2 F

#print axioms clauseProduct_embeddedBoolean
#print axioms norm_clauseProduct_update_sub_le
#print axioms polyLoss_snap_lt
#print axioms globalMinOnBall_boolean
#print axioms polyLoss_embeddedBoolean
#print axioms exists_globalMinOnBall
#print axioms exists_globalMinOnBall_value_iff_satisfiable
#print axioms globalMinOnBall_readout_decides
#print axioms clausePolynomial_totalDegree_le
#print axioms clausePolynomial_degreeOf_le
#print axioms compilePolynomial_correct
#print axioms global_optimizer_decides_three_sat
#print axioms polynomial_residual_hardness
#print axioms dyadic_no_tractability_transfer
#print axioms dyadic_compilePolynomial_correct

end PhdThesisLean.PolynomialResidualHardness
