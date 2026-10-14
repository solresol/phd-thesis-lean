import PhdThesisLean.ClauseCompiler

namespace PhdThesisLean.ClauseErasure

open scoped BigOperators
open PhdThesisLean.FiniteDomainCompiler
open PhdThesisLean.ClauseCompiler

/-!
# Clause erasure by positive hole-filling, and approximate negation

This module formalises two statements of the thesis.

* **Proposition `prop:3sat-hole-filling`** ("Clause erasure by positive
  hole-filling") from
  `/Users/gregb/Documents/devel/phd-thesis/appendices/complexity-3sat-clausewise.tex`,
  together with the clause row `u_C` (`ClauseCompiler.clauseCoeff`), the
  forbidden value `t_C = 3 - k_C` (`ClauseCompiler.clauseTarget`, see
  `clauseTarget_eq`), and the indicator lemma `lem:3sat-row-indicator`
  (`ClauseCompiler.clause_row_indicator`) that it relies on.
* The unnamed **Lemma of appendix `app:approximate-negation`** from
  `/Users/gregb/Documents/devel/phd-thesis/sudoku-via-padic-regression/body.tex`:
  replacing a negated-literal coefficient `-1` by any integer `c̃ ≡ -1 (mod p)`
  preserves `|u_C^⊤x - t_C|_p` on Boolean-labelled `x`. The thesis's "(R2)"
  (the clause residual is a `p`-adic unit on satisfying Boolean assignments
  for `p > 3`) is `ClauseCompiler.clause_row_indicator`.

## Part (a): hole filling

For a clause `C` with `k_C = negatedCount C` negated literals, the clause row
sum `s_C(x) = u_C^⊤ x` is `clauseSum C x`. On Boolean inputs it takes the
integer value `clauseSumInt C b`, which lies in the four consecutive integers
`valueRange C = {-k_C, …, 3 - k_C}` (`clauseSumInt_mem_valueRange`) and equals
the top `t_C = 3 - k_C` exactly when the clause is falsified
(`clauseSum_embeddedBoolean_eq_target_iff`). The positive encoding uses the
well `well (allowedValues C)` with `allowedValues C = valueRange C \ {t_C}`.

The well `well S t = ∑ a ∈ S, ‖t - a‖` is `FiniteDomainCompiler.unaryCost`
over the integer value set cast into `ℚ_[p]` (`well_eq_unaryCost`). For `p > 3`
and `S ⊆ V_C`, `well S` takes the value `|S| - 1` on `S` and `|S|` on
`V_C \ S` (`well_at_mem`, `well_at_notMem`), so it is minimised exactly on `S`
(`well_minimised_iff`). Adding the missing well at `t_C` gives the erasure
identity `well S_C (s) + ‖s - t_C‖ = well V_C (s)` (`clause_erasure_identity`),
and `well V_C` is the constant `3` on Boolean inputs
(`well_valueRange_embeddedBoolean`, the proposition's "constant on {0,1}^n").

The clause-wise positive objective `positiveLoss` and the erased objective
`erasedLoss` are both instances of the finite-domain compiler template
(`wellLoss_eq_compilerLoss`): each clause term is a family of positive affine
observations `(+1, u_C, a, 1)`, `a ∈ S`. Consequences:

* `positiveLoss_embeddedBoolean`: `L⁺(x) = α n + 3 m - sat(x)` on Boolean `x`,
  so the positive encoding also rewards satisfaction (well value `2` when the
  clause is true, `3` when it is false: `well_allowedValues_embeddedBoolean`).
* `erasedLoss_embeddedBoolean`: the erased objective is the constant
  `α n + 3 m` on Boolean inputs.
* `erasedLoss_globalMin_iff` (the "trivial problem" claim): under the
  domination hypothesis `4 Δ < α` (`Δ = max_i variableDegree Φ i`, each
  erased clause term being a sum of four 1-Lipschitz well terms in every
  incident coordinate), the global minimisers of the erased objective over all
  of `ℚ_[p]^n` are exactly the Boolean assignments. No unit-ball restriction is
  needed: the ultrametric snapping argument of the compiler template is global.
* `positiveLoss_globalMin_iff_maximizesSatisfied` (bonus, the positive-encoding
  analogue of `thm:3sat-clausewise`): under `3 Δ < α`, a Boolean assignment is
  a global minimiser of the positive objective iff it maximises the number of
  satisfied clauses.

The thesis says only that the remaining problem is "trivial"; the domination
hypothesis `∀ i, 4 * variableDegree Φ i < α` is our explicit, documented
sufficient condition for the Booleanity of all global minimisers. The constancy
statements on Boolean inputs need no such hypothesis.

## Part (b): approximate negation

`modifiedCoeff C c` is the clause row with the coefficient of each negated
literal `k` replaced by `c k` (positive literals keep coefficient `1`), and
`modifiedSum C c x` is its dot product with `x`. `approximate_negation` proves
`‖modifiedSum C c x - t_C‖ = ‖clauseSum C x - t_C‖` for every Boolean-labelled
`x` whenever `c k ≡ -1 [ZMOD p]` for every negated position `k` and `p > 3`.
Choosing `c k = -1` at unmodified positions recovers the thesis's "some
coefficients". The two residuals differ by `residualShift`, an integer multiple
of `p`; at the falsifying assignment both vanish, and at a satisfying
assignment the original residual is a unit, so the ultrametric
`Padic.add_eq_max_of_ne` preserves the norm. `pow_sub_one_modEq_neg_one`
records that `p^k - 1` (`k ≥ 1`) is a valid replacement, and
`modifiedClausewiseLoss_embeddedBoolean` shows that the compiled clause-wise
objective with substituted rows agrees with the original on Boolean inputs.

## Correspondence notes

* Formulas are indexed by an arbitrary finite type `κ` (rather than `Fin m`),
  and all statements are over `ℚ_[p]` (stronger than the thesis's `ℤ_p^n`).
* Everything is checked; nothing is external.
-/

/-- Global minimiser of a real-valued function (same shape as
`PhdThesisLean.AllDifferent.IsGlobalMin`). -/
def IsGlobalMin {α : Type*} (f : α → ℝ) (x : α) : Prop :=
  ∀ y, f x ≤ f y

/-! ### The clause row, its target, and its value range -/

/-- `k_C`: the number of negated literals in the clause. -/
def negatedCount {n : ℕ} (C : Clause n) : ℕ :=
  ∑ k, if (C.literal k).negated then 1 else 0

/-- `s_C(x) = u_C^⊤ x`, the clause row sum. -/
noncomputable def clauseSum
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (x : Parameter p n) : ℚ_[p] :=
  ∑ j, (clauseCoeff C j : ℚ_[p]) * x j

theorem clauseSum_sub_target_eq_residual
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (x : Parameter p n) :
    clauseSum C x - (clauseTarget C : ℚ_[p]) =
      affineResidual (clauseObservation (p := p) C) x := rfl

theorem clauseTarget_add_negatedCount {n : ℕ} (C : Clause n) :
    clauseTarget C + (negatedCount C : ℤ) = 3 := by
  rw [clauseTarget, negatedCount]
  push_cast
  rw [← Finset.sum_add_distrib]
  have h : ∀ k : Fin 3,
      ((if (C.literal k).negated then (0 : ℤ) else 1) +
        (if (C.literal k).negated then (1 : ℤ) else 0)) = 1 := by
    intro k
    split_ifs <;> simp
  simp [h]

/-- `t_C = 3 - k_C`. -/
theorem clauseTarget_eq {n : ℕ} (C : Clause n) :
    clauseTarget C = 3 - (negatedCount C : ℤ) := by
  have := clauseTarget_add_negatedCount C
  omega

/-- `V_C = {-k_C, -k_C + 1, …, 3 - k_C}`, four consecutive integers. -/
def valueRange {n : ℕ} (C : Clause n) : Finset ℤ :=
  Finset.Icc (-(negatedCount C : ℤ)) (3 - negatedCount C)

/-- `S_C = V_C \ {t_C}`, the allowed values of the positive encoding. -/
def allowedValues {n : ℕ} (C : Clause n) : Finset ℤ :=
  (valueRange C).erase (3 - negatedCount C)

theorem target_mem_valueRange {n : ℕ} (C : Clause n) :
    clauseTarget C ∈ valueRange C := by
  rw [valueRange, Finset.mem_Icc, clauseTarget_eq]
  constructor <;> omega

theorem allowedValues_eq_erase_target {n : ℕ} (C : Clause n) :
    allowedValues C = (valueRange C).erase (clauseTarget C) := by
  rw [allowedValues, clauseTarget_eq]

theorem allowedValues_subset {n : ℕ} (C : Clause n) :
    allowedValues C ⊆ valueRange C :=
  Finset.erase_subset _ _

theorem target_notMem_allowedValues {n : ℕ} (C : Clause n) :
    clauseTarget C ∉ allowedValues C := by
  rw [allowedValues_eq_erase_target]
  simp

theorem mem_allowedValues_iff {n : ℕ} (C : Clause n) (a : ℤ) :
    a ∈ allowedValues C ↔ a ∈ valueRange C ∧ a ≠ clauseTarget C := by
  rw [allowedValues_eq_erase_target, Finset.mem_erase, and_comm]

theorem card_valueRange {n : ℕ} (C : Clause n) :
    (valueRange C).card = 4 := by
  rw [valueRange, Int.card_Icc]
  have h : (3 - (negatedCount C : ℤ) + 1 - -(negatedCount C : ℤ)) = 4 := by ring
  rw [h]
  rfl

theorem card_allowedValues {n : ℕ} (C : Clause n) :
    (allowedValues C).card = 3 := by
  rw [allowedValues_eq_erase_target,
    Finset.card_erase_of_mem (target_mem_valueRange C), card_valueRange]

/-- Distinct elements of `V_C` differ by at most `3` in absolute value. -/
theorem abs_sub_le_three_of_mem_valueRange
    {n : ℕ} (C : Clause n) {a b : ℤ}
    (ha : a ∈ valueRange C) (hb : b ∈ valueRange C) :
    |a - b| ≤ 3 := by
  rw [valueRange, Finset.mem_Icc] at ha hb
  rw [abs_le]
  constructor <;> omega

/-! ### Wells -/

/-- `W_S(t) = ∑_{a ∈ S} |t - a|_p`, the positive well over an integer value
set `S`. -/
noncomputable def well
    {p : ℕ} [Fact p.Prime] (S : Finset ℤ) (t : ℚ_[p]) : ℝ :=
  ∑ a ∈ S, ‖t - (a : ℚ_[p])‖

open Classical in
/-- The well is exactly `FiniteDomainCompiler.unaryCost` over the value set
cast into `ℚ_[p]`. -/
theorem well_eq_unaryCost
    {p : ℕ} [Fact p.Prime] (S : Finset ℤ) (t : ℚ_[p]) :
    well S t = unaryCost (S.image (Int.cast : ℤ → ℚ_[p])) t := by
  rw [well, unaryCost, Finset.sum_image]
  intro a _ b _ hab
  exact Int.cast_injective hab

/-- Two integers that differ by a nonzero amount of absolute value `< p` are
unit-separated in `ℚ_[p]`. -/
theorem norm_intCast_sub_eq_one
    {p : ℕ} [Fact p.Prime] {a b : ℤ} (hab : a ≠ b) (hlt : |a - b| < p) :
    ‖(a : ℚ_[p]) - (b : ℚ_[p])‖ = 1 := by
  rw [← Int.cast_sub]
  have hndvd : ¬ ((p : ℤ) ∣ a - b) := by
    intro hdvd
    exact (sub_ne_zero.mpr hab) (Int.eq_zero_of_abs_lt_dvd hdvd hlt)
  have hnot : ¬ ‖((a - b : ℤ) : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_intCast_lt_one_iff]
    exact hndvd
  exact le_antisymm (Padic.norm_int_le_one _) (not_lt.mp hnot)

/-- For `p > 3`, distinct elements of `V_C` are unit-separated in `ℚ_[p]`. -/
theorem valueRange_sep
    {p n : ℕ} [Fact p.Prime] (hp : 3 < p) (C : Clause n) :
    ∀ a ∈ valueRange C, ∀ b ∈ valueRange C, a ≠ b →
      ‖(a : ℚ_[p]) - (b : ℚ_[p])‖ = 1 := by
  intro a ha b hb hab
  apply norm_intCast_sub_eq_one hab
  have h3 := abs_sub_le_three_of_mem_valueRange C ha hb
  have hp' : (3 : ℤ) < p := by exact_mod_cast hp
  omega

/-- On a unit-separated value set `V`, the well of `S ⊆ V` evaluated at a
member of `S` is `|S| - 1`. -/
theorem well_at_mem
    {p : ℕ} [Fact p.Prime] {V S : Finset ℤ}
    (hsep : ∀ a ∈ V, ∀ b ∈ V, a ≠ b → ‖(a : ℚ_[p]) - (b : ℚ_[p])‖ = 1)
    (hS : S ⊆ V) {t : ℤ} (ht : t ∈ V) (htS : t ∈ S) :
    well S (t : ℚ_[p]) = S.card - 1 := by
  classical
  rw [well, ← Finset.sum_erase_add _ _ htS, sub_self, norm_zero, add_zero]
  have hsum :
      (∑ a ∈ S.erase t, ‖(t : ℚ_[p]) - (a : ℚ_[p])‖) =
        ∑ _a ∈ S.erase t, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact hsep t ht a (hS (Finset.mem_of_mem_erase ha))
      (Ne.symm (Finset.ne_of_mem_erase ha))
  rw [hsum]
  simp [Finset.card_erase_of_mem htS,
    Nat.cast_sub (Finset.card_pos.mpr ⟨t, htS⟩)]

/-- On a unit-separated value set `V`, the well of `S ⊆ V` evaluated at a
member of `V \ S` is `|S|`. -/
theorem well_at_notMem
    {p : ℕ} [Fact p.Prime] {V S : Finset ℤ}
    (hsep : ∀ a ∈ V, ∀ b ∈ V, a ≠ b → ‖(a : ℚ_[p]) - (b : ℚ_[p])‖ = 1)
    (hS : S ⊆ V) {t : ℤ} (ht : t ∈ V) (htS : t ∉ S) :
    well S (t : ℚ_[p]) = S.card := by
  rw [well]
  have hsum :
      (∑ a ∈ S, ‖(t : ℚ_[p]) - (a : ℚ_[p])‖) = ∑ _a ∈ S, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact hsep t ht a (hS ha) (fun h => htS (h ▸ ha))
  rw [hsum]
  simp

/-- On `V`, the well of a nonempty `S ⊆ V` is minimised exactly on `S`. -/
theorem well_minimised_iff
    {p : ℕ} [Fact p.Prime] {V S : Finset ℤ}
    (hsep : ∀ a ∈ V, ∀ b ∈ V, a ≠ b → ‖(a : ℚ_[p]) - (b : ℚ_[p])‖ = 1)
    (hS : S ⊆ V) (hne : S.Nonempty) {t : ℤ} (ht : t ∈ V) :
    (∀ t' ∈ V, well S (t : ℚ_[p]) ≤ well S (t' : ℚ_[p])) ↔ t ∈ S := by
  constructor
  · intro hmin
    by_contra htS
    obtain ⟨s, hs⟩ := hne
    have h := hmin s (hS hs)
    rw [well_at_notMem hsep hS ht htS, well_at_mem hsep hS (hS hs) hs] at h
    linarith
  · intro htS t' ht'
    rw [well_at_mem hsep hS ht htS]
    by_cases ht'S : t' ∈ S
    · rw [well_at_mem hsep hS ht' ht'S]
    · rw [well_at_notMem hsep hS ht' ht'S]
      linarith

/-- Hole filling: adding the missing well at `a ∈ S` to the well over
`S \ {a}` gives the well over `S`. -/
theorem well_erase_add_norm
    {p : ℕ} [Fact p.Prime] {S : Finset ℤ} {a : ℤ} (ha : a ∈ S) (t : ℚ_[p]) :
    well (S.erase a) t + ‖t - (a : ℚ_[p])‖ = well S t := by
  classical
  rw [well, well]
  exact Finset.sum_erase_add _ _ ha

/-- The erasure identity for a clause:
`W_{S_C}(s_C(x)) + |s_C(x) - t_C|_p = W_{V_C}(s_C(x))` for every `x`. -/
theorem clause_erasure_identity
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (x : Parameter p n) :
    well (allowedValues C) (clauseSum C x) +
        ‖clauseSum C x - (clauseTarget C : ℚ_[p])‖ =
      well (valueRange C) (clauseSum C x) := by
  rw [allowedValues_eq_erase_target]
  exact well_erase_add_norm (target_mem_valueRange C) _

/-! ### The clause row sum on Boolean inputs -/

/-- The Boolean bit as an integer. -/
def boolBit (b : Bool) : ℤ := if b then 1 else 0

theorem boolValue_eq_boolBit {p : ℕ} [Fact p.Prime] (b : Bool) :
    boolValue (p := p) b = (boolBit b : ℚ_[p]) := by
  cases b <;> simp [boolValue, boolBit]

/-- The integer value of `s_C` on a Boolean assignment. -/
def clauseSumInt {n : ℕ} (C : Clause n) (b : Fin n → Bool) : ℤ :=
  ∑ k, literalSign (C.literal k) * boolBit (b (C.literal k).var)

/-- A clause row built from any per-literal integer weights `σ` dots with `x`
as the sum over literals, because the three variables are distinct. -/
theorem sum_coeff_mul
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (σ : Fin 3 → ℤ)
    (x : Parameter p n) :
    (∑ j, ((∑ k, if (C.literal k).var = j then σ k else 0 : ℤ) : ℚ_[p]) * x j) =
      ∑ k, (σ k : ℚ_[p]) * x (C.literal k).var := by
  classical
  simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [ite_mul, zero_mul]
  rw [Fintype.sum_ite_eq]

theorem clauseSum_eq_sum_literals
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (x : Parameter p n) :
    clauseSum C x =
      ∑ k, ((literalSign (C.literal k) : ℤ) : ℚ_[p]) * x (C.literal k).var := by
  rw [clauseSum]
  exact sum_coeff_mul C (fun k => literalSign (C.literal k)) x

theorem clauseSum_embeddedBoolean
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (b : Fin n → Bool) :
    clauseSum C (embeddedBoolean (p := p) b) = (clauseSumInt C b : ℚ_[p]) := by
  rw [clauseSum_eq_sum_literals, clauseSumInt]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  simp [embeddedBoolean, boolValue_eq_boolBit]

/-- `s_C` ranges over `V_C` on Boolean inputs. -/
theorem clauseSumInt_mem_valueRange
    {n : ℕ} (C : Clause n) (b : Fin n → Bool) :
    clauseSumInt C b ∈ valueRange C := by
  rw [valueRange, Finset.mem_Icc]
  have hlow : -(negatedCount C : ℤ) =
      ∑ k, (if (C.literal k).negated then (-1 : ℤ) else 0) := by
    rw [negatedCount]
    push_cast
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  have hhigh : (3 : ℤ) - negatedCount C =
      ∑ k, (if (C.literal k).negated then (0 : ℤ) else 1) := by
    rw [← clauseTarget_eq, clauseTarget]
  rw [hlow, hhigh, clauseSumInt]
  constructor <;> apply Finset.sum_le_sum <;> intro k _ <;>
    cases hneg : (C.literal k).negated <;> cases b (C.literal k).var <;>
    simp [literalSign, boolBit, hneg]

theorem clauseSum_embeddedBoolean_mem_valueRange
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (b : Fin n → Bool) :
    ∃ v ∈ valueRange C, clauseSum C (embeddedBoolean (p := p) b) = (v : ℚ_[p]) :=
  ⟨clauseSumInt C b, clauseSumInt_mem_valueRange C b, clauseSum_embeddedBoolean C b⟩

/-- The residual `s_C - t_C` is the sum of the literal failure bits minus
three (thesis proof of `lem:3sat-row-indicator`, integer form). -/
theorem clauseSumInt_sub_target
    {n : ℕ} (C : Clause n) (b : Fin n → Bool) :
    clauseSumInt C b - clauseTarget C =
      ∑ k, (boolBit (literalFailureBit (C.literal k) b) - 1) := by
  rw [clauseSumInt, clauseTarget, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  cases hneg : (C.literal k).negated <;> cases hb : b (C.literal k).var <;>
    simp [literalSign, literalFailureBit, boolBit, hneg, hb]

theorem forall_fin_three {P : Fin 3 → Prop} :
    (∀ k, P k) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2

/-- A clause is falsified exactly when every literal fails. -/
theorem not_clauseSatisfied_iff
    {n : ℕ} (C : Clause n) (b : Fin n → Bool) :
    ¬ clauseSatisfied C b ↔ ∀ k, literalFailureBit (C.literal k) b = true := by
  rw [forall_fin_three]
  unfold clauseSatisfied
  cases literalFailureBit (C.literal 0) b <;>
    cases literalFailureBit (C.literal 1) b <;>
    cases literalFailureBit (C.literal 2) b <;> simp

/-- `s_C = t_C` exactly at the falsifying assignments (integer form). -/
theorem clauseSumInt_eq_target_iff
    {n : ℕ} (C : Clause n) (b : Fin n → Bool) :
    clauseSumInt C b = clauseTarget C ↔ ¬ clauseSatisfied C b := by
  rw [← sub_eq_zero, clauseSumInt_sub_target, not_clauseSatisfied_iff,
    forall_fin_three, Fin.sum_univ_three]
  cases literalFailureBit (C.literal 0) b <;>
    cases literalFailureBit (C.literal 1) b <;>
    cases literalFailureBit (C.literal 2) b <;> norm_num [boolBit]

/-- `s_C(x) = t_C` exactly at the falsifying Boolean assignments: the clause is
falsified at the top of the range `V_C`. -/
theorem clauseSum_embeddedBoolean_eq_target_iff
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (b : Fin n → Bool) :
    clauseSum C (embeddedBoolean (p := p) b) = (clauseTarget C : ℚ_[p]) ↔
      ¬ clauseSatisfied C b := by
  rw [clauseSum_embeddedBoolean, Int.cast_inj, clauseSumInt_eq_target_iff]

/-! ### The clause terms on Boolean inputs -/

/-- After hole filling, the clause term is the constant `3` on every Boolean
input: the clause is erased. -/
theorem well_valueRange_embeddedBoolean
    {p n : ℕ} [Fact p.Prime] (hp : 3 < p) (C : Clause n) (b : Fin n → Bool) :
    well (valueRange C) (clauseSum C (embeddedBoolean (p := p) b)) = 3 := by
  rw [clauseSum_embeddedBoolean,
    well_at_mem (valueRange_sep hp C) (Finset.Subset.refl _)
      (clauseSumInt_mem_valueRange C b) (clauseSumInt_mem_valueRange C b),
    card_valueRange]
  norm_num

/-- The positive clause term is `2` on satisfying and `3` on falsifying
Boolean inputs. -/
theorem well_allowedValues_embeddedBoolean
    {p n : ℕ} [Fact p.Prime] (hp : 3 < p) (C : Clause n) (b : Fin n → Bool) :
    well (allowedValues C) (clauseSum C (embeddedBoolean (p := p) b)) =
      if clauseSatisfied C b then 2 else 3 := by
  rw [clauseSum_embeddedBoolean]
  have hmem := clauseSumInt_mem_valueRange C b
  by_cases hsat : clauseSatisfied C b
  · have hS : clauseSumInt C b ∈ allowedValues C := by
      rw [mem_allowedValues_iff]
      exact ⟨hmem, fun h => (clauseSumInt_eq_target_iff C b).mp h hsat⟩
    rw [well_at_mem (valueRange_sep hp C) (allowedValues_subset C) hmem hS,
      card_allowedValues, if_pos hsat]
    norm_num
  · have hS : clauseSumInt C b ∉ allowedValues C := by
      rw [mem_allowedValues_iff]
      intro h
      exact h.2 ((clauseSumInt_eq_target_iff C b).mpr hsat)
    rw [well_at_notMem (valueRange_sep hp C) (allowedValues_subset C) hmem hS,
      card_allowedValues, if_neg hsat]
    norm_num

/-! ### The objectives as instances of the compiler template -/

/-- The unary Boolean pinning term `∑ i (|x_i|_p + |x_i - 1|_p)`. -/
noncomputable def pinningTerm
    {p n : ℕ} [Fact p.Prime] (x : Parameter p n) : ℝ :=
  ∑ i, (‖x i‖ + ‖x i - 1‖)

theorem unaryCost_booleanDomain
    {p n : ℕ} [Fact p.Prime] (i : Fin n) (t : ℚ_[p]) :
    unaryCost (booleanDomain (p := p) i) t = ‖t‖ + ‖t - 1‖ := by
  classical
  rw [unaryCost]
  simp [booleanDomain, Finset.sum_pair (zero_ne_one' ℚ_[p])]

theorem pinningLoss_booleanDomain
    {p n : ℕ} [Fact p.Prime] (α : ℝ) (x : Parameter p n) :
    pinningLoss (booleanDomain (p := p)) (fun _ => α) x = α * pinningTerm x := by
  rw [pinningLoss, pinningTerm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [unaryCost_booleanDomain]

theorem pinningTerm_embeddedBoolean
    {p n : ℕ} [Fact p.Prime] (b : Fin n → Bool) :
    pinningTerm (embeddedBoolean (p := p) b) = n := by
  rw [pinningTerm]
  have h : ∀ i, ‖embeddedBoolean (p := p) b i‖ +
      ‖embeddedBoolean (p := p) b i - 1‖ = 1 := by
    intro i
    cases hb : b i <;> simp [embeddedBoolean, boolValue, hb]
  simp [h]

/-- The positive affine observation `(+1, u_C, a, 1)`: one well at value `a`
for the clause row. -/
noncomputable def wellObservation
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (a : ℤ) : AffineObservation p n where
  sign := 1
  weight := 1
  coeff i := (clauseCoeff C i : ℚ_[p])
  target := (a : ℚ_[p])

/-- The family of positive observations: one well at every `a ∈ A r` for every
clause `r`. -/
noncomputable def wellFamily
    {p n : ℕ} [Fact p.Prime] {κ : Type*}
    (Φ : κ → Clause n) (A : κ → Finset ℤ) :
    (Σ r : κ, ↥(A r)) → AffineObservation p n :=
  fun ra => wellObservation (Φ ra.1) (ra.2 : ℤ)

theorem wellFamily_sign
    {p n : ℕ} [Fact p.Prime] {κ : Type*}
    (Φ : κ → Clause n) (A : κ → Finset ℤ) (ra : Σ r : κ, ↥(A r)) :
    |(wellFamily (p := p) Φ A ra).sign| = 1 := by
  simp [wellFamily, wellObservation]

theorem wellFamily_weight
    {p n : ℕ} [Fact p.Prime] {κ : Type*}
    (Φ : κ → Clause n) (A : κ → Finset ℤ) (ra : Σ r : κ, ↥(A r)) :
    0 ≤ (wellFamily (p := p) Φ A ra).weight := by
  simp [wellFamily, wellObservation]

theorem wellFamily_coeff_norm
    {p n : ℕ} [Fact p.Prime] {κ : Type*}
    (Φ : κ → Clause n) (A : κ → Finset ℤ) (ra : Σ r : κ, ↥(A r)) (i : Fin n) :
    ‖(wellFamily (p := p) Φ A ra).coeff i‖ ≤ 1 := by
  simpa [wellFamily, wellObservation] using
    Padic.norm_int_le_one (p := p) (clauseCoeff (Φ ra.1) i)

theorem interactionLoss_wellFamily
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (A : κ → Finset ℤ) (x : Parameter p n) :
    interactionLoss (wellFamily (p := p) Φ A) x =
      ∑ r, well (A r) (clauseSum (Φ r) x) := by
  rw [interactionLoss, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [well, ← Finset.sum_coe_sort (A r)
    (fun a : ℤ => ‖clauseSum (Φ r) x - (a : ℚ_[p])‖)]
  apply Finset.sum_congr rfl
  intro a _
  simp [wellFamily, wellObservation, affineResidual, clauseSum]

theorem incidentWeight_wellFamily
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (A : κ → Finset ℤ) (i : Fin n) :
    incidentWeight (wellFamily (p := p) Φ A) i =
      ∑ r, if ∃ k, ((Φ r).literal k).var = i then ((A r).card : ℝ) else 0 := by
  classical
  rw [incidentWeight, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hocc : ∃ k, ((Φ r).literal k).var = i
  · have hne : clauseCoeff (Φ r) i ≠ 0 :=
      (clauseCoeff_ne_zero_iff (Φ r) i).mpr hocc
    simp [wellFamily, wellObservation, hocc, hne]
  · have hzero : clauseCoeff (Φ r) i = 0 :=
      not_ne_iff.mp ((clauseCoeff_ne_zero_iff (Φ r) i).not.mpr hocc)
    simp [wellFamily, wellObservation, hocc, hzero]

/-- Each clause term with `c` wells contributes `c` to the incident weight of
every variable it contains. -/
theorem incidentWeight_wellFamily_of_card
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (A : κ → Finset ℤ) {c : ℝ}
    (hcard : ∀ r, ((A r).card : ℝ) = c) (i : Fin n) :
    incidentWeight (wellFamily (p := p) Φ A) i = c * variableDegree Φ i := by
  classical
  rw [incidentWeight_wellFamily, variableDegree, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [hcard r]
  split_ifs <;> simp

/-- The general positive well objective
`α ∑ i (|x_i|_p + |x_i - 1|_p) + ∑ r W_{A r}(s_{C_r}(x))`. -/
noncomputable def wellLoss
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (A : κ → Finset ℤ) (α : ℝ) (x : Parameter p n) : ℝ :=
  α * pinningTerm x + ∑ r, well (A r) (clauseSum (Φ r) x)

/-- The positive well objective is a finite-domain compiler loss. -/
theorem wellLoss_eq_compilerLoss
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (A : κ → Finset ℤ) (α : ℝ) (x : Parameter p n) :
    wellLoss Φ A α x =
      compilerLoss (booleanDomain (p := p)) (fun _ => α)
        (wellFamily (p := p) Φ A) x := by
  rw [wellLoss, compilerLoss, pinningLoss_booleanDomain, interactionLoss_wellFamily]

/-- Under domination, every global minimiser of a positive well objective is
Boolean. -/
theorem wellLoss_globalMin_boolean
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (A : κ → Finset ℤ) {c : ℝ}
    (hcard : ∀ r, ((A r).card : ℝ) = c) (α : ℝ)
    (hdom : ∀ i, c * variableDegree Φ i < α)
    (x : Parameter p n) (hmin : IsGlobalMin (wellLoss Φ A α) x) :
    ∃ b : Fin n → Bool, x = embeddedBoolean (p := p) b := by
  have hxD : InDomain (booleanDomain (p := p)) x := by
    apply compiler_global_minimizer_inDomain (booleanDomain (p := p))
      (fun _ => α) (wellFamily (p := p) Φ A)
      booleanDomain_nonempty booleanDomain_unitSeparated
    · intro i
      rw [incidentWeight_wellFamily_of_card Φ A hcard i]
      exact hdom i
    · exact wellFamily_sign Φ A
    · exact wellFamily_weight Φ A
    · exact wellFamily_coeff_norm Φ A
    · intro y
      rw [← wellLoss_eq_compilerLoss, ← wellLoss_eq_compilerLoss]
      exact hmin y
  obtain ⟨b, hb⟩ := inBooleanDomain_exists_embedded x hxD
  exact ⟨b, hb.symm⟩

/-- Under domination, every point is dominated by some Boolean assignment. -/
theorem exists_boolean_wellLoss_le
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (A : κ → Finset ℤ) {c : ℝ}
    (hcard : ∀ r, ((A r).card : ℝ) = c) (α : ℝ)
    (hdom : ∀ i, c * variableDegree Φ i < α) (x : Parameter p n) :
    ∃ b : Fin n → Bool,
      wellLoss Φ A α (embeddedBoolean (p := p) b) ≤ wellLoss Φ A α x := by
  obtain ⟨z, hzD, hzx⟩ :=
    exists_inDomain_not_greater (booleanDomain (p := p)) (fun _ => α)
      (wellFamily (p := p) Φ A) booleanDomain_nonempty booleanDomain_unitSeparated
      (fun i => by
        rw [incidentWeight_wellFamily_of_card Φ A hcard i]
        exact hdom i)
      (wellFamily_sign Φ A) (wellFamily_weight Φ A) (wellFamily_coeff_norm Φ A) x
  obtain ⟨b, rfl⟩ := inBooleanDomain_exists_embedded z hzD
  refine ⟨b, ?_⟩
  rw [wellLoss_eq_compilerLoss, wellLoss_eq_compilerLoss]
  exact hzx

/-! ### The positive clause-wise objective and the erased objective -/

/-- `L⁺_Φ(x) = α ∑ i (|x_i|_p + |x_i - 1|_p) + ∑ r W_{S_{C_r}}(s_{C_r}(x))`,
the positive clause-wise encoding. -/
noncomputable def positiveLoss
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (α : ℝ) (x : Parameter p n) : ℝ :=
  α * pinningTerm x + ∑ r, well (allowedValues (Φ r)) (clauseSum (Φ r) x)

/-- `L^∘_Φ(x) = α ∑ i (|x_i|_p + |x_i - 1|_p) + ∑ r W_{V_{C_r}}(s_{C_r}(x))`,
the objective after hole-filling every clause. -/
noncomputable def erasedLoss
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (α : ℝ) (x : Parameter p n) : ℝ :=
  α * pinningTerm x + ∑ r, well (valueRange (Φ r)) (clauseSum (Φ r) x)

theorem positiveLoss_eq_wellLoss
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (α : ℝ) (x : Parameter p n) :
    positiveLoss Φ α x = wellLoss Φ (fun r => allowedValues (Φ r)) α x := rfl

theorem erasedLoss_eq_wellLoss
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (α : ℝ) (x : Parameter p n) :
    erasedLoss Φ α x = wellLoss Φ (fun r => valueRange (Φ r)) α x := rfl

/-- The erased objective is the positive objective plus the missing wells
`∑ r |s_{C_r}(x) - t_{C_r}|_p`, for every `x`. -/
theorem erasedLoss_eq_positiveLoss_add
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (α : ℝ) (x : Parameter p n) :
    erasedLoss Φ α x =
      positiveLoss Φ α x +
        ∑ r, ‖clauseSum (Φ r) x - (clauseTarget (Φ r) : ℚ_[p])‖ := by
  rw [erasedLoss, positiveLoss, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact (clause_erasure_identity (Φ r) x).symm

/-- `L⁺_Φ(x) = α n + 3 m - sat_Φ(x)` on Boolean `x`: the positive encoding
rewards satisfaction. -/
theorem positiveLoss_embeddedBoolean
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (hp : 3 < p) (Φ : κ → Clause n) (α : ℝ) (b : Fin n → Bool) :
    positiveLoss Φ α (embeddedBoolean (p := p) b) =
      α * n + 3 * Fintype.card κ - satisfiedCount Φ b := by
  classical
  rw [positiveLoss, pinningTerm_embeddedBoolean]
  simp_rw [well_allowedValues_embeddedBoolean hp]
  have hsplit : ∀ r, (if clauseSatisfied (Φ r) b then (2 : ℝ) else 3) =
      3 - (if clauseSatisfied (Φ r) b then (1 : ℝ) else 0) := by
    intro r
    split_ifs <;> norm_num
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hindicator :
      (∑ r : κ, if clauseSatisfied (Φ r) b then (1 : ℝ) else 0) =
        (satisfiedCount Φ b : ℝ) := by
    rw [satisfiedCount]
    simp
  rw [hindicator]
  ring

/-- The erased objective is the constant `α n + 3 m` on Boolean inputs. -/
theorem erasedLoss_embeddedBoolean
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (hp : 3 < p) (Φ : κ → Clause n) (α : ℝ) (b : Fin n → Bool) :
    erasedLoss Φ α (embeddedBoolean (p := p) b) =
      α * n + 3 * Fintype.card κ := by
  rw [erasedLoss, pinningTerm_embeddedBoolean]
  simp_rw [well_valueRange_embeddedBoolean hp]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Every Boolean assignment is a global minimiser of the erased objective
among Boolean assignments (no domination hypothesis needed). -/
theorem erasedLoss_embeddedBoolean_le
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (hp : 3 < p) (Φ : κ → Clause n) (α : ℝ) (b b' : Fin n → Bool) :
    erasedLoss Φ α (embeddedBoolean (p := p) b) ≤
      erasedLoss Φ α (embeddedBoolean (p := p) b') := by
  rw [erasedLoss_embeddedBoolean hp, erasedLoss_embeddedBoolean hp]

/-- The "trivial problem" claim: under the domination hypothesis `4 Δ < α`,
the global minimisers of the erased objective over all of `ℚ_[p]^n` are
exactly the Boolean assignments. -/
theorem erasedLoss_globalMin_iff
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (hp : 3 < p) (Φ : κ → Clause n) (α : ℝ)
    (hdom : ∀ i, 4 * variableDegree Φ i < α) (x : Parameter p n) :
    IsGlobalMin (erasedLoss Φ α) x ↔
      ∃ b : Fin n → Bool, x = embeddedBoolean (p := p) b := by
  have hcard : ∀ r, ((valueRange (Φ r)).card : ℝ) = 4 := by
    intro r
    rw [card_valueRange]
    norm_num
  constructor
  · intro hmin
    exact wellLoss_globalMin_boolean Φ (fun r => valueRange (Φ r)) hcard α hdom x hmin
  · rintro ⟨b, rfl⟩ y
    obtain ⟨b', hb'⟩ :=
      exists_boolean_wellLoss_le Φ (fun r => valueRange (Φ r)) hcard α hdom y
    calc erasedLoss Φ α (embeddedBoolean (p := p) b)
        = erasedLoss Φ α (embeddedBoolean (p := p) b') := by
          rw [erasedLoss_embeddedBoolean hp, erasedLoss_embeddedBoolean hp]
      _ ≤ erasedLoss Φ α y := hb'

/-- **Proposition `prop:3sat-hole-filling`** (clause erasure by positive
hole-filling), for a prime `p > 3`:
1. adding the missing well at `t_C` makes every clause term the constant `3`
   on Boolean inputs;
2. the fully erased objective is the constant `α n + 3 m` on Boolean inputs;
3. under the domination hypothesis `4 Δ < α`, its global minimisers over
   `ℚ_[p]^n` are exactly all Boolean assignments. -/
theorem clause_erasure
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (hp : 3 < p) (Φ : κ → Clause n) (α : ℝ)
    (hdom : ∀ i, 4 * variableDegree Φ i < α) :
    (∀ (C : Clause n) (b : Fin n → Bool),
      well (valueRange C) (clauseSum C (embeddedBoolean (p := p) b)) = 3) ∧
    (∀ b : Fin n → Bool,
      erasedLoss Φ α (embeddedBoolean (p := p) b) = α * n + 3 * Fintype.card κ) ∧
    (∀ x : Parameter p n,
      IsGlobalMin (erasedLoss Φ α) x ↔
        ∃ b : Fin n → Bool, x = embeddedBoolean (p := p) b) :=
  ⟨fun C b => well_valueRange_embeddedBoolean hp C b,
    fun b => erasedLoss_embeddedBoolean hp Φ α b,
    fun x => erasedLoss_globalMin_iff hp Φ α hdom x⟩

/-- Under `3 Δ < α`, every global minimiser of the positive encoding is
Boolean. -/
theorem positiveLoss_globalMin_boolean
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (α : ℝ)
    (hdom : ∀ i, 3 * variableDegree Φ i < α)
    (x : Parameter p n) (hmin : IsGlobalMin (positiveLoss Φ α) x) :
    ∃ b : Fin n → Bool, x = embeddedBoolean (p := p) b := by
  have hcard : ∀ r, ((allowedValues (Φ r)).card : ℝ) = 3 := by
    intro r
    rw [card_allowedValues]
    norm_num
  exact wellLoss_globalMin_boolean Φ (fun r => allowedValues (Φ r)) hcard α hdom x hmin

/-- The positive-encoding analogue of `thm:3sat-clausewise`: under `3 Δ < α`,
a Boolean assignment is a global minimiser of the positive objective iff it
maximises the number of satisfied clauses. -/
theorem positiveLoss_globalMin_iff_maximizesSatisfied
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (hp : 3 < p) (Φ : κ → Clause n) (α : ℝ)
    (hdom : ∀ i, 3 * variableDegree Φ i < α) (b : Fin n → Bool) :
    IsGlobalMin (positiveLoss Φ α) (embeddedBoolean (p := p) b) ↔
      MaximizesSatisfied Φ b := by
  have hcard : ∀ r, ((allowedValues (Φ r)).card : ℝ) = 3 := by
    intro r
    rw [card_allowedValues]
    norm_num
  constructor
  · intro hmin b'
    have h := hmin (embeddedBoolean (p := p) b')
    rw [positiveLoss_embeddedBoolean hp, positiveLoss_embeddedBoolean hp] at h
    exact_mod_cast (by linarith : (satisfiedCount Φ b' : ℝ) ≤ satisfiedCount Φ b)
  · intro hmax y
    obtain ⟨b', hb'⟩ :=
      exists_boolean_wellLoss_le Φ (fun r => allowedValues (Φ r)) hcard α hdom y
    have hcount : (satisfiedCount Φ b' : ℝ) ≤ satisfiedCount Φ b := by
      exact_mod_cast hmax b'
    calc positiveLoss Φ α (embeddedBoolean (p := p) b)
        ≤ positiveLoss Φ α (embeddedBoolean (p := p) b') := by
          rw [positiveLoss_embeddedBoolean hp, positiveLoss_embeddedBoolean hp]
          linarith
      _ ≤ positiveLoss Φ α y := hb'

/-! ### Part (b): approximate negation -/

/-- The per-literal coefficient after substitution: `c k` at a negated
position, `1` at a positive one. -/
def modifiedSign {n : ℕ} (C : Clause n) (c : Fin 3 → ℤ) (k : Fin 3) : ℤ :=
  if (C.literal k).negated then c k else 1

/-- `ũ_C`: the clause row with each negated-literal coefficient `-1` replaced
by `c k`. -/
def modifiedCoeff {n : ℕ} (C : Clause n) (c : Fin 3 → ℤ) (i : Fin n) : ℤ :=
  ∑ k, if (C.literal k).var = i then modifiedSign C c k else 0

/-- `ũ_C^⊤ x`. -/
noncomputable def modifiedSum
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (c : Fin 3 → ℤ)
    (x : Parameter p n) : ℚ_[p] :=
  ∑ j, (modifiedCoeff C c j : ℚ_[p]) * x j

/-- Substituting `-1` everywhere recovers the original clause row. -/
theorem modifiedCoeff_neg_one {n : ℕ} (C : Clause n) :
    modifiedCoeff C (fun _ => -1) = clauseCoeff C := by
  funext i
  rw [modifiedCoeff, clauseCoeff]
  apply Finset.sum_congr rfl
  intro k _
  simp [modifiedSign, literalSign]

theorem modifiedSum_eq_sum_literals
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (c : Fin 3 → ℤ)
    (x : Parameter p n) :
    modifiedSum C c x =
      ∑ k, (modifiedSign C c k : ℚ_[p]) * x (C.literal k).var := by
  rw [modifiedSum]
  exact sum_coeff_mul C (modifiedSign C c) x

/-- The two residuals differ by `∑_{negated k} (c̃_k + 1) x_{var k}`. -/
theorem modifiedSum_sub_clauseSum
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (c : Fin 3 → ℤ)
    (x : Parameter p n) :
    modifiedSum C c x - clauseSum C x =
      ∑ k, (((if (C.literal k).negated then c k + 1 else 0 : ℤ) : ℚ_[p])) *
        x (C.literal k).var := by
  rw [modifiedSum_eq_sum_literals, clauseSum_eq_sum_literals,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← sub_mul]
  congr 1
  cases hneg : (C.literal k).negated
  · simp [modifiedSign, literalSign, hneg]
  · simp [modifiedSign, literalSign, hneg]

/-- The integer by which the two residuals differ on a Boolean assignment. -/
def residualShift {n : ℕ} (C : Clause n) (c : Fin 3 → ℤ) (b : Fin n → Bool) : ℤ :=
  ∑ k, (if (C.literal k).negated then c k + 1 else 0) * boolBit (b (C.literal k).var)

theorem modifiedSum_sub_clauseSum_embeddedBoolean
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (c : Fin 3 → ℤ) (b : Fin n → Bool) :
    modifiedSum C c (embeddedBoolean (p := p) b) -
        clauseSum C (embeddedBoolean (p := p) b) =
      (residualShift C c b : ℚ_[p]) := by
  rw [modifiedSum_sub_clauseSum, residualShift]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  simp [embeddedBoolean, boolValue_eq_boolBit]

/-- The residual shift is a multiple of `p` when every substituted coefficient
is `≡ -1 (mod p)`. -/
theorem dvd_residualShift
    {p n : ℕ} (C : Clause n) (c : Fin 3 → ℤ)
    (hc : ∀ k, (C.literal k).negated = true → c k ≡ -1 [ZMOD p])
    (b : Fin n → Bool) :
    (p : ℤ) ∣ residualShift C c b := by
  rw [residualShift]
  apply Finset.dvd_sum
  intro k _
  apply Dvd.dvd.mul_right
  cases hneg : (C.literal k).negated
  · simp
  · show (p : ℤ) ∣ c k + 1
    have h := Int.modEq_iff_dvd.mp (hc k hneg)
    have h' : (-1 : ℤ) - c k = -(c k + 1) := by ring
    rw [h', dvd_neg] at h
    exact h

/-- At a falsifying assignment every negated variable is `0`, so the residual
shift vanishes. -/
theorem residualShift_eq_zero_of_not_satisfied
    {n : ℕ} (C : Clause n) (c : Fin 3 → ℤ) (b : Fin n → Bool)
    (hsat : ¬ clauseSatisfied C b) :
    residualShift C c b = 0 := by
  rw [not_clauseSatisfied_iff] at hsat
  rw [residualShift]
  apply Finset.sum_eq_zero
  intro k _
  cases hneg : (C.literal k).negated
  · simp
  · have hfail := hsat k
    rw [literalFailureBit, hneg] at hfail
    simp at hfail
    simp [boolBit, hfail]

/-- **Approximate negation** (thesis appendix `app:approximate-negation`,
prime `p > 3`): replacing the negated-literal coefficients by integers
`c k ≡ -1 (mod p)` preserves `|u_C^⊤x - t_C|_p` on every Boolean-labelled `x`. -/
theorem approximate_negation
    {p n : ℕ} [Fact p.Prime] (hp : 3 < p) (C : Clause n) (c : Fin 3 → ℤ)
    (hc : ∀ k, (C.literal k).negated = true → c k ≡ -1 [ZMOD p])
    (b : Fin n → Bool) :
    ‖modifiedSum C c (embeddedBoolean (p := p) b) - (clauseTarget C : ℚ_[p])‖ =
      ‖clauseSum C (embeddedBoolean (p := p) b) - (clauseTarget C : ℚ_[p])‖ := by
  have hdecomp :
      modifiedSum C c (embeddedBoolean (p := p) b) - (clauseTarget C : ℚ_[p]) =
        (clauseSum C (embeddedBoolean (p := p) b) - (clauseTarget C : ℚ_[p])) +
          (residualShift C c b : ℚ_[p]) := by
    rw [← modifiedSum_sub_clauseSum_embeddedBoolean]
    ring
  rw [hdecomp]
  have hres :
      ‖clauseSum C (embeddedBoolean (p := p) b) - (clauseTarget C : ℚ_[p])‖ =
        if clauseSatisfied C b then 1 else 0 := by
    rw [clauseSum_sub_target_eq_residual]
    exact clause_row_indicator hp C b
  by_cases hsat : clauseSatisfied C b
  · have hshift_lt : ‖(residualShift C c b : ℚ_[p])‖ < 1 := by
      rw [Padic.norm_intCast_lt_one_iff]
      exact dvd_residualShift C c hc b
    rw [Padic.add_eq_max_of_ne]
    · rw [hres, if_pos hsat, max_eq_left hshift_lt.le]
    · rw [hres, if_pos hsat]
      exact ne_of_gt hshift_lt
  · rw [residualShift_eq_zero_of_not_satisfied C c b hsat, Int.cast_zero, add_zero]

/-- The substituted row is still the clause-satisfaction indicator. -/
theorem modified_row_indicator
    {p n : ℕ} [Fact p.Prime] (hp : 3 < p) (C : Clause n) (c : Fin 3 → ℤ)
    (hc : ∀ k, (C.literal k).negated = true → c k ≡ -1 [ZMOD p])
    (b : Fin n → Bool) :
    ‖modifiedSum C c (embeddedBoolean (p := p) b) - (clauseTarget C : ℚ_[p])‖ =
      if clauseSatisfied C b then 1 else 0 := by
  rw [approximate_negation hp C c hc b, clauseSum_sub_target_eq_residual]
  exact clause_row_indicator hp C b

/-- `p^k - 1 ≡ -1 (mod p)` for `k ≥ 1`: the thesis's example replacements
`p - 1` and `p^k - 1` are valid. -/
theorem pow_sub_one_modEq_neg_one (p : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ((p : ℤ) ^ k - 1) ≡ -1 [ZMOD p] := by
  rw [Int.modEq_iff_dvd]
  have h : (-1 : ℤ) - ((p : ℤ) ^ k - 1) = -((p : ℤ) ^ k) := by ring
  rw [h, dvd_neg]
  exact dvd_pow_self _ (by omega)

/-- Replacing every negated coefficient by `p^k - 1` (`k ≥ 1`) preserves the
residual norm on Boolean inputs. -/
theorem approximate_negation_pow
    {p n : ℕ} [Fact p.Prime] (hp : 3 < p) (C : Clause n) {k : ℕ} (hk : 1 ≤ k)
    (b : Fin n → Bool) :
    ‖modifiedSum C (fun _ => (p : ℤ) ^ k - 1) (embeddedBoolean (p := p) b) -
        (clauseTarget C : ℚ_[p])‖ =
      ‖clauseSum C (embeddedBoolean (p := p) b) - (clauseTarget C : ℚ_[p])‖ :=
  approximate_negation hp C _ (fun _ _ => pow_sub_one_modEq_neg_one p hk) b

/-- The substituted clause row as a negative affine observation, as in the
clause-wise compiler. -/
noncomputable def modifiedObservation
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (c : Fin 3 → ℤ) :
    AffineObservation p n where
  sign := -1
  weight := 1
  coeff i := (modifiedCoeff C c i : ℚ_[p])
  target := (clauseTarget C : ℚ_[p])

theorem norm_affineResidual_modifiedObservation
    {p n : ℕ} [Fact p.Prime] (hp : 3 < p) (C : Clause n) (c : Fin 3 → ℤ)
    (hc : ∀ k, (C.literal k).negated = true → c k ≡ -1 [ZMOD p])
    (b : Fin n → Bool) :
    ‖affineResidual (modifiedObservation (p := p) C c) (embeddedBoolean (p := p) b)‖ =
      ‖affineResidual (clauseObservation (p := p) C) (embeddedBoolean (p := p) b)‖ :=
  approximate_negation hp C c hc b

/-- The clause-wise objective with substituted rows (`c r` for clause `r`). -/
noncomputable def modifiedClausewiseLoss
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (c : κ → Fin 3 → ℤ) (pinWeight : ℝ)
    (x : Parameter p n) : ℝ :=
  compilerLoss (booleanDomain (p := p)) (fun _ => pinWeight)
    (fun r => modifiedObservation (p := p) (Φ r) (c r)) x

/-- On Boolean inputs, the clause-wise objective with substituted rows agrees
with the original `clausewiseLoss`: the substitution is an identity, not an
approximation. -/
theorem modifiedClausewiseLoss_embeddedBoolean
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (hp : 3 < p) (Φ : κ → Clause n) (c : κ → Fin 3 → ℤ)
    (hc : ∀ r k, ((Φ r).literal k).negated = true → c r k ≡ -1 [ZMOD p])
    (pinWeight : ℝ) (b : Fin n → Bool) :
    modifiedClausewiseLoss Φ c pinWeight (embeddedBoolean (p := p) b) =
      clausewiseLoss Φ pinWeight (embeddedBoolean (p := p) b) := by
  rw [modifiedClausewiseLoss, clausewiseLoss, compilerLoss, compilerLoss]
  congr 1
  rw [interactionLoss, interactionLoss]
  apply Finset.sum_congr rfl
  intro r _
  rw [norm_affineResidual_modifiedObservation hp (Φ r) (c r) (hc r) b]
  rfl

end PhdThesisLean.ClauseErasure

#print axioms PhdThesisLean.ClauseErasure.clause_erasure
#print axioms PhdThesisLean.ClauseErasure.erasedLoss_globalMin_iff
#print axioms PhdThesisLean.ClauseErasure.erasedLoss_embeddedBoolean
#print axioms PhdThesisLean.ClauseErasure.well_valueRange_embeddedBoolean
#print axioms PhdThesisLean.ClauseErasure.positiveLoss_globalMin_iff_maximizesSatisfied
#print axioms PhdThesisLean.ClauseErasure.approximate_negation
#print axioms PhdThesisLean.ClauseErasure.modified_row_indicator
#print axioms PhdThesisLean.ClauseErasure.modifiedClausewiseLoss_embeddedBoolean
