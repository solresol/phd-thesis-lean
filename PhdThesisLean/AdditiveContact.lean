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

@[simp]
theorem padicMagnitude_eq_zero
    {p : ℕ} [Fact p.Prime] {q : ℚ} :
    padicMagnitude p q = 0 ↔ q = 0 := by
  constructor
  · contrapose!
    exact padicMagnitude_ne_zero
  · rintro rfl
    exact padicMagnitude_zero p

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

/-! ## Count-loss special case -/

/-- The step transform underlying count loss. -/
noncomputable def countTransform (t : ℝ≥0) : ℝ := if t = 0 then 0 else 1

theorem countTransform_monotone : Monotone countTransform := by
  intro a b hab
  by_cases ha : a = 0
  · by_cases hb : b = 0 <;> simp [countTransform, ha, hb]
  · have hb : b ≠ 0 := by
      intro hb
      apply ha
      apply le_antisymm
      · simpa [hb] using hab
      · exact bot_le
    simp [countTransform, ha, hb]

theorem countTransform_zero_lt {t : ℝ≥0} (ht : t ≠ 0) :
    countTransform 0 < countTransform t := by
  simp [countTransform, ht]

/-- Number of nonzero residuals, embedded in the reals. -/
noncomputable def countLoss
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) : ℝ :=
  ∑ i, if residual X y β i = 0 then 0 else 1

theorem countLoss_eq_transformedLoss
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) :
    countLoss X y β = transformedLoss p countTransform X y β := by
  apply Finset.sum_congr rfl
  intro i _
  simp [countTransform]

theorem count_contact_or_degenerate
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n)
    (hmin : ∀ γ : Model n, countLoss X y β ≤ countLoss X y γ) :
    n + 1 ≤ contactCount X y β ∨ Degenerate X := by
  apply additive_contact_or_degenerate p X y countTransform countTransform_monotone
    (fun _ ht ↦ countTransform_zero_lt ht) β
  intro γ
  rw [← countLoss_eq_transformedLoss p X y β,
    ← countLoss_eq_transformedLoss p X y γ]
  exact hmin γ

/-! ## Additive q-family special case -/

/-- The generalised `p`-adic magnitude `q⁻ᵛ`, with exact residuals assigned
weight zero. -/
noncomputable def qPadicTerm (p : ℕ) (q : ℝ) (r : ℚ) : ℝ :=
  if r = 0 then 0 else q ^ (-padicValRat p r)

theorem qPadicTerm_le_of_padicNorm_le
    {p : ℕ} [Fact p.Prime] {q : ℝ} (hq : 1 < q) {r s : ℚ}
    (h : padicNorm p r ≤ padicNorm p s) :
    qPadicTerm p q r ≤ qPadicTerm p q s := by
  by_cases hs : s = 0
  · subst s
    have hrnorm : padicNorm p r = 0 :=
      le_antisymm h (padicNorm.nonneg r)
    have hr : r = 0 := padicNorm.zero_of_padicNorm_eq_zero hrnorm
    simp [qPadicTerm, hr]
  by_cases hr : r = 0
  · simp [qPadicTerm, hr, hs, (zpow_pos (lt_trans zero_lt_one hq) _).le]
  simp only [qPadicTerm, if_neg hr, if_neg hs]
  rw [padicNorm.eq_zpow_of_nonzero hr, padicNorm.eq_zpow_of_nonzero hs] at h
  have hp : (1 : ℚ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hv : -padicValRat p r ≤ -padicValRat p s :=
    (zpow_le_zpow_iff_right₀ hp).mp h
  exact (zpow_le_zpow_iff_right₀ hq).mpr hv

theorem qPadicTerm_pos
    {p : ℕ} {q : ℝ} (hq : 1 < q) {r : ℚ} (hr : r ≠ 0) :
    0 < qPadicTerm p q r := by
  rw [qPadicTerm, if_neg hr]
  exact zpow_pos (lt_trans zero_lt_one hq) _

/-- Additive `q`-loss from the thesis, with `q⁻ᵛ_p(0) = 0`. -/
noncomputable def qLoss
    (p : ℕ) (q : ℝ) {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) : ℝ :=
  ∑ i, qPadicTerm p q (residual X y β i)

theorem q_contact_or_degenerate
    (p : ℕ) [Fact p.Prime] {q : ℝ} (hq : 1 < q) {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n)
    (hmin : ∀ γ : Model n, qLoss p q X y β ≤ qLoss p q X y γ) :
    n + 1 ≤ contactCount X y β ∨ Degenerate X := by
  by_cases hcontacts : n + 1 ≤ contactCount X y β
  · exact Or.inl hcontacts
  by_cases hdeg : Degenerate X
  · exact Or.inr hdeg
  exfalso
  obtain ⟨β', hnorm_le, j, hjnew, hjold⟩ :=
    exists_pointwise_norm_improvement p X y β (Nat.lt_of_not_ge hcontacts) hdeg
  have hterm_le : ∀ i,
      qPadicTerm p q (residual X y β' i) ≤
        qPadicTerm p q (residual X y β i) := by
    intro i
    exact qPadicTerm_le_of_padicNorm_le hq (hnorm_le i)
  have hjterm_strict :
      qPadicTerm p q (residual X y β' j) <
        qPadicTerm p q (residual X y β j) := by
    rw [hjnew]
    simpa [qPadicTerm] using qPadicTerm_pos hq hjold
  have hloss_strict : qLoss p q X y β' < qLoss p q X y β := by
    apply Finset.sum_lt_sum
    · intro i _
      exact hterm_le i
    · exact ⟨j, Finset.mem_univ j, hjterm_strict⟩
  exact (not_lt_of_ge (hmin β')) hloss_strict

/-- Statement-faithful wrapper for thesis Corollary
`cor:additive-contact-special-cases`. -/
theorem additive_contact_special_cases
    (p n k : ℕ) [Fact p.Prime]
    (_hn : 0 < n) (_hk : n + 1 ≤ k)
    (X : Fin k → Point n) (y : Fin k → ℚ)
    (_hwell : ∀ i j, y i ≠ y j → X i ≠ X j) :
    (∀ β : Model n,
      (∀ γ : Model n, countLoss X y β ≤ countLoss X y γ) →
        n + 1 ≤ contactCount X y β ∨ Degenerate X) ∧
    ∀ q : ℝ, 1 < q → ∀ β : Model n,
      (∀ γ : Model n, qLoss p q X y β ≤ qLoss p q X y γ) →
        n + 1 ≤ contactCount X y β ∨ Degenerate X := by
  constructor
  · intro β hmin
    exact count_contact_or_degenerate p X y β hmin
  · intro q hq β hmin
    exact q_contact_or_degenerate p hq X y β hmin

end PhdThesisLean.AdditiveContact
