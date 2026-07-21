/-
  Formalisation of the additive contact theorem from Greg Baker's PhD thesis.

  Thesis source: ultrametric-regularisation-and-loss/unification.tex
  Thesis label: thm:additive-contact
  Thesis snapshot: 2c6418bcf9643fc6e039237f0f59ace14b2557fc
-/

import Mathlib.Data.NNReal.Basic
import PhdThesisLean.ContactTheorem

namespace PhdThesisLean.AdditiveContact

open scoped BigOperators NNReal
open ContactTheorem

/-- The rational `p`-adic norm, regarded as a nonnegative real number. -/
noncomputable def padicMagnitude (p : ℕ) (q : ℚ) : ℝ≥0 :=
  ⟨(padicNorm p q : ℝ), by exact_mod_cast padicNorm.nonneg q⟩

@[simp]
theorem padicMagnitude_zero (p : ℕ) : padicMagnitude p 0 = 0 := by
  ext
  simp [padicMagnitude]

theorem padicMagnitude_le_of_padicNorm_le
    {p : ℕ} {q r : ℚ} (h : padicNorm p q ≤ padicNorm p r) :
    padicMagnitude p q ≤ padicMagnitude p r := by
  change (padicNorm p q : ℝ) ≤ (padicNorm p r : ℝ)
  exact_mod_cast h

theorem padicMagnitude_ne_zero
    {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0) :
    padicMagnitude p q ≠ 0 := by
  intro h
  have hreal := congrArg NNReal.toReal h
  change (padicNorm p q : ℝ) = 0 at hreal
  have hrat : padicNorm p q = 0 := by exact_mod_cast hreal
  exact hq (padicNorm.zero_of_padicNorm_eq_zero hrat)

/-- A transformed additive residual loss. The transform is defined on
nonnegative reals, matching the thesis statement. -/
noncomputable def transformedLoss
    (p : ℕ) (φ : ℝ≥0 → ℝ) {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) : ℝ :=
  ∑ i, φ (padicMagnitude p (residual X y β i))

/-- Strong form of the additive contact theorem. A minimiser of any monotone
additive transform that strictly distinguishes zero from every positive
magnitude has `n + 1` contacts, unless the predictors are degenerate. -/
theorem additive_contact_or_degenerate
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ)
    (φ : ℝ≥0 → ℝ) (hmono : Monotone φ)
    (hzero : ∀ t : ℝ≥0, t ≠ 0 → φ 0 < φ t)
    (β : Model n)
    (hmin : ∀ γ : Model n,
      transformedLoss p φ X y β ≤ transformedLoss p φ X y γ) :
    n + 1 ≤ contactCount X y β ∨ Degenerate X := by
  by_cases hcontacts : n + 1 ≤ contactCount X y β
  · exact Or.inl hcontacts
  by_cases hdeg : Degenerate X
  · exact Or.inr hdeg
  exfalso
  obtain ⟨β', hnorm_le, j, hjnew, hjold⟩ :=
    exists_pointwise_norm_improvement p X y β (Nat.lt_of_not_ge hcontacts) hdeg
  have hterm_le : ∀ i,
      φ (padicMagnitude p (residual X y β' i)) ≤
        φ (padicMagnitude p (residual X y β i)) := by
    intro i
    exact hmono (padicMagnitude_le_of_padicNorm_le (hnorm_le i))
  have hjterm_strict :
      φ (padicMagnitude p (residual X y β' j)) <
        φ (padicMagnitude p (residual X y β j)) := by
    rw [hjnew, padicMagnitude_zero]
    exact hzero _ (padicMagnitude_ne_zero hjold)
  have hloss_strict : transformedLoss p φ X y β' < transformedLoss p φ X y β := by
    apply Finset.sum_lt_sum
    · intro i _
      exact hterm_le i
    · exact ⟨j, Finset.mem_univ j, hjterm_strict⟩
  exact (not_lt_of_ge (hmin β')) hloss_strict

/-- Statement-faithful wrapper for thesis Theorem `thm:additive-contact`. -/
theorem additive_contact_theorem
    (p n k : ℕ) [Fact p.Prime]
    (_hn : 0 < n) (_hk : n + 1 ≤ k)
    (X : Fin k → Point n) (y : Fin k → ℚ)
    (_hwell : ∀ i j, y i ≠ y j → X i ≠ X j)
    (φ : ℝ≥0 → ℝ) (hmono : Monotone φ)
    (hzero : ∀ t : ℝ≥0, t ≠ 0 → φ 0 < φ t)
    (β : Model n)
    (hmin : ∀ γ : Model n,
      transformedLoss p φ X y β ≤ transformedLoss p φ X y γ) :
    n + 1 ≤ contactCount X y β ∨ Degenerate X :=
  additive_contact_or_degenerate p X y φ hmono hzero β hmin

end PhdThesisLean.AdditiveContact
