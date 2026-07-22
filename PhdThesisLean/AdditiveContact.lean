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

/-! ## Lexicographic behaviour when `q` exceeds the data count -/

/-- Indices of the nonzero residuals. Exact fits are omitted because their
`p`-adic valuation is infinite rather than an integer. -/
noncomputable def nonzeroResidualIndices
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) : Finset (Fin k) :=
  Finset.univ.filter fun i ↦ residual X y β i ≠ 0

/-- The finite set of integer valuations attained by nonzero residuals. -/
noncomputable def valuationSupport
    (p : ℕ) {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) : Finset ℤ :=
  (nonzeroResidualIndices X y β).image fun i ↦ padicValRat p (residual X y β i)

/-- The residual-valuation histogram. Exact fits do not belong to any finite
valuation bin. -/
noncomputable def valuationHistogram
    (p : ℕ) {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n)
    (t : ℤ) : ℕ :=
  ((nonzeroResidualIndices X y β).filter fun i ↦
    padicValRat p (residual X y β i) = t).card

/-- The additive `q`-loss is the weighted sum of its finite valuation
histogram. -/
theorem qLoss_eq_histogram_sum_on_support
    (p : ℕ) (q : ℝ) {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) :
    qLoss p q X y β =
      ∑ t ∈ valuationSupport p X y β,
        (valuationHistogram p X y β t : ℝ) * q ^ (-t) := by
  classical
  calc
    qLoss p q X y β =
        ∑ i ∈ nonzeroResidualIndices X y β,
          q ^ (-padicValRat p (residual X y β i)) := by
      simp only [qLoss, qPadicTerm]
      rw [nonzeroResidualIndices, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : residual X y β i = 0 <;> simp [hi]
    _ = ∑ t ∈ valuationSupport p X y β,
          ∑ i ∈ nonzeroResidualIndices X y β with
            padicValRat p (residual X y β i) = t,
              q ^ (-padicValRat p (residual X y β i)) := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro i hi
      exact Finset.mem_image_of_mem _ hi
    _ = ∑ t ∈ valuationSupport p X y β,
          (valuationHistogram p X y β t : ℝ) * q ^ (-t) := by
      apply Finset.sum_congr rfl
      intro t _
      calc
        (∑ i ∈ nonzeroResidualIndices X y β with
            padicValRat p (residual X y β i) = t,
              q ^ (-padicValRat p (residual X y β i))) =
            ∑ _i ∈ (nonzeroResidualIndices X y β).filter
                (fun i ↦ padicValRat p (residual X y β i) = t), q ^ (-t) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = (valuationHistogram p X y β t : ℝ) * q ^ (-t) := by
          simp [valuationHistogram]

theorem histogram_eq_zero_of_not_mem_support
    (p : ℕ) {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) {t : ℤ}
    (ht : t ∉ valuationSupport p X y β) :
    valuationHistogram p X y β t = 0 := by
  rw [valuationHistogram, Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  exact ht (Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1,
    (Finset.mem_filter.mp hi).2⟩)

theorem mem_valuationSupport_of_histogram_ne_zero
    (p : ℕ) {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) {t : ℤ}
    (ht : valuationHistogram p X y β t ≠ 0) :
    t ∈ valuationSupport p X y β := by
  contrapose! ht
  exact histogram_eq_zero_of_not_mem_support p X y β ht

theorem qLoss_eq_histogram_sum_of_support_subset
    (p : ℕ) (q : ℝ) {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n)
    {V : Finset ℤ} (hV : valuationSupport p X y β ⊆ V) :
    qLoss p q X y β =
      ∑ t ∈ V, (valuationHistogram p X y β t : ℝ) * q ^ (-t) := by
  rw [qLoss_eq_histogram_sum_on_support]
  apply Finset.sum_subset hV
  intro t _ ht
  rw [histogram_eq_zero_of_not_mem_support p X y β ht]
  simp

theorem valuationHistogram_le_dataCount
    (p : ℕ) {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) (t : ℤ) :
    valuationHistogram p X y β t ≤ k := by
  rw [valuationHistogram]
  calc
    ((nonzeroResidualIndices X y β).filter fun i ↦
        padicValRat p (residual X y β i) = t).card ≤
        (nonzeroResidualIndices X y β).card := Finset.card_filter_le _ _
    _ ≤ Finset.univ.card := by
      rw [nonzeroResidualIndices]
      exact Finset.card_filter_le _ _
    _ = k := by simp

theorem valuationHistogram_sum_le_dataCount
    (p : ℕ) {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n)
    {V : Finset ℤ} (hV : valuationSupport p X y β ⊆ V) :
    ∑ t ∈ V, valuationHistogram p X y β t ≤ k := by
  classical
  have hsupport :
      ∑ t ∈ valuationSupport p X y β, valuationHistogram p X y β t =
        ∑ t ∈ V, valuationHistogram p X y β t := by
    apply Finset.sum_subset hV
    intro t _ ht
    exact histogram_eq_zero_of_not_mem_support p X y β ht
  rw [← hsupport]
  calc
    (∑ t ∈ valuationSupport p X y β, valuationHistogram p X y β t) =
        (nonzeroResidualIndices X y β).card := by
      have hmaps :
          ((nonzeroResidualIndices X y β : Finset (Fin k)) : Set (Fin k)).MapsTo
            (fun i ↦ padicValRat p (residual X y β i))
            (valuationSupport p X y β : Set ℤ) := by
        intro i hi
        change i ∈ nonzeroResidualIndices X y β at hi
        change padicValRat p (residual X y β i) ∈
          (nonzeroResidualIndices X y β).image
            (fun j : Fin k ↦ padicValRat p (residual X y β j))
        exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
      simpa only [valuationHistogram] using
        (Finset.card_eq_sum_card_fiberwise hmaps).symm
    _ ≤ Finset.univ.card := by
      rw [nonzeroResidualIndices]
      exact Finset.card_filter_le _ _
    _ = k := by simp

private lemma sum_eq_below_add_at_add_above
    (V : Finset ℤ) (t0 : ℤ) (ht0 : t0 ∈ V) (f : ℤ → ℝ) :
    ∑ t ∈ V, f t =
      (∑ t ∈ V.filter (fun t ↦ t < t0), f t) + f t0 +
        ∑ t ∈ V.filter (fun t ↦ t0 < t), f t := by
  classical
  have hbelow :
      (V.erase t0).filter (fun t ↦ t < t0) = V.filter (fun t ↦ t < t0) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · exact fun h ↦ ⟨h.1.2, h.2⟩
    · intro h
      exact ⟨⟨by omega, h.1⟩, h.2⟩
  have habove :
      (V.erase t0).filter (fun t ↦ ¬t < t0) = V.filter (fun t ↦ t0 < t) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor <;> intro h
    · exact ⟨h.1.2, by omega⟩
    · exact ⟨⟨by omega, h.1⟩, by omega⟩
  rw [← Finset.sum_erase_add V f ht0]
  rw [← Finset.sum_filter_add_sum_filter_not (V.erase t0) (fun t ↦ t < t0) f]
  rw [hbelow, habove]
  ring

/-- Numerical core: for a base larger than the total mass of the first
histogram, its first smaller bin dominates every possible adverse tail. -/
theorem weighted_histogram_lexicographic
    (q : ℝ) (hq1 : 1 < q) (k : ℕ) (hqk : (k : ℝ) < q)
    (V : Finset ℤ) (h h' : ℤ → ℕ) (t0 : ℤ) (ht0 : t0 ∈ V)
    (hbelow : ∀ t ∈ V, t < t0 → h t = h' t)
    (hlt : h t0 < h' t0)
    (hsum : ∑ t ∈ V, h t ≤ k) :
    (∑ t ∈ V, (h t : ℝ) * q ^ (-t)) <
      ∑ t ∈ V, (h' t : ℝ) * q ^ (-t) := by
  classical
  let B := V.filter fun t ↦ t < t0
  let T := V.filter fun t ↦ t0 < t
  have hqpos : 0 < q := lt_trans zero_lt_one hq1
  have hwpos : ∀ t : ℤ, 0 < q ^ (-t) := fun t ↦ zpow_pos hqpos _
  have hbelow_eq :
      (∑ t ∈ B, (h t : ℝ) * q ^ (-t)) =
        ∑ t ∈ B, (h' t : ℝ) * q ^ (-t) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [hbelow t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2]
  have hTsubset : T ⊆ V := fun _ ht ↦ (Finset.mem_filter.mp ht).1
  have hTsum : ∑ t ∈ T, h t ≤ k := by
    exact le_trans
      (Finset.sum_le_sum_of_subset_of_nonneg hTsubset (fun _ _ _ ↦ Nat.zero_le _)) hsum
  have hweight : ∀ t ∈ T, q ^ (-t) ≤ q ^ (-(t0 + 1)) := by
    intro t ht
    apply zpow_le_zpow_right₀ hq1.le
    have hle : t0 + 1 ≤ t := Int.add_one_le_iff.mpr (Finset.mem_filter.mp ht).2
    omega
  have htail_bound :
      (∑ t ∈ T, (h t : ℝ) * q ^ (-t)) ≤
        (k : ℝ) * q ^ (-(t0 + 1)) := by
    calc
      (∑ t ∈ T, (h t : ℝ) * q ^ (-t)) ≤
          ∑ t ∈ T, (h t : ℝ) * q ^ (-(t0 + 1)) := by
        apply Finset.sum_le_sum
        intro t ht
        exact mul_le_mul_of_nonneg_left (hweight t ht) (Nat.cast_nonneg _)
      _ = (↑(∑ t ∈ T, h t) : ℝ) * q ^ (-(t0 + 1)) := by
        rw [Nat.cast_sum]
        exact (Finset.sum_mul T (fun t ↦ (h t : ℝ)) (q ^ (-(t0 + 1)))).symm
      _ ≤ (k : ℝ) * q ^ (-(t0 + 1)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hTsum) (le_of_lt (hwpos _))
  have hprime_tail_nonneg :
      0 ≤ ∑ t ∈ T, (h' t : ℝ) * q ^ (-t) := by
    apply Finset.sum_nonneg
    intro t _
    positivity
  have h0gap : (h t0 : ℝ) + 1 ≤ (h' t0 : ℝ) := by
    exact_mod_cast hlt
  have hscale :
      (k : ℝ) * q ^ (-(t0 + 1)) < q ^ (-t0) := by
    rw [show -(t0 + 1) = -t0 - 1 by omega, zpow_sub₀ (ne_of_gt hqpos)]
    rw [zpow_one]
    calc
      (k : ℝ) * (q ^ (-t0) / q) = ((k : ℝ) * q ^ (-t0)) / q := by ring
      _ < (q * q ^ (-t0)) / q := by
        exact (div_lt_div_iff_of_pos_right hqpos).2
          (mul_lt_mul_of_pos_right hqk (hwpos t0))
      _ = q ^ (-t0) := by field_simp
  rw [sum_eq_below_add_at_add_above V t0 ht0,
    sum_eq_below_add_at_add_above V t0 ht0]
  change
    (∑ t ∈ B, (h t : ℝ) * q ^ (-t)) + (h t0 : ℝ) * q ^ (-t0) +
        ∑ t ∈ T, (h t : ℝ) * q ^ (-t) <
      (∑ t ∈ B, (h' t : ℝ) * q ^ (-t)) + (h' t0 : ℝ) * q ^ (-t0) +
        ∑ t ∈ T, (h' t : ℝ) * q ^ (-t)
  rw [hbelow_eq]
  have hmain :
      (h t0 : ℝ) * q ^ (-t0) + (k : ℝ) * q ^ (-(t0 + 1)) <
        (h' t0 : ℝ) * q ^ (-t0) := by
    nlinarith [hwpos t0]
  nlinarith

/-- Strong form of thesis Theorem `thm:q-lexicographic`. -/
theorem qLoss_lt_of_first_histogram_lt
    (p : ℕ) (q : ℝ) {n k : ℕ} (hq : (k : ℝ) < q)
    (X : Fin k → Point n) (y : Fin k → ℚ) (β β' : Model n) (t0 : ℤ)
    (hbelow : ∀ t : ℤ, t < t0 →
      valuationHistogram p X y β t = valuationHistogram p X y β' t)
    (hlt : valuationHistogram p X y β t0 < valuationHistogram p X y β' t0) :
    qLoss p q X y β < qLoss p q X y β' := by
  classical
  let V := valuationSupport p X y β ∪ valuationSupport p X y β'
  have hprime_pos : valuationHistogram p X y β' t0 ≠ 0 := by omega
  have ht0 : t0 ∈ V := by
    exact Finset.mem_union_right _
      (mem_valuationSupport_of_histogram_ne_zero p X y β' hprime_pos)
  have hk : 0 < k := by
    have hle := valuationHistogram_le_dataCount p X y β' t0
    omega
  have hq1 : 1 < q := by
    exact lt_of_le_of_lt (by exact_mod_cast hk) hq
  have hβV : valuationSupport p X y β ⊆ V := Finset.subset_union_left
  have hβ'V : valuationSupport p X y β' ⊆ V := Finset.subset_union_right
  rw [qLoss_eq_histogram_sum_of_support_subset p q X y β hβV,
    qLoss_eq_histogram_sum_of_support_subset p q X y β' hβ'V]
  apply weighted_histogram_lexicographic q hq1 k hq V
    (valuationHistogram p X y β) (valuationHistogram p X y β') t0 ht0
  · intro t _ ht
    exact hbelow t ht
  · exact hlt
  · exact valuationHistogram_sum_le_dataCount p X y β hβV

/-- Statement-faithful wrapper for thesis Theorem `thm:q-lexicographic`.
The explicit `hdifferent` hypothesis records the prose assumption; the
strict inequality at `t0` already implies it mathematically. -/
theorem q_lexicographic_theorem
    (p : ℕ) (q : ℝ) {n k : ℕ} (hq : (k : ℝ) < q)
    (X : Fin k → Point n) (y : Fin k → ℚ) (β β' : Model n) (t0 : ℤ)
    (_hdifferent : ∃ t : ℤ,
      valuationHistogram p X y β t ≠ valuationHistogram p X y β' t)
    (hsmallest : ∀ t : ℤ, t < t0 →
      valuationHistogram p X y β t = valuationHistogram p X y β' t)
    (hlt : valuationHistogram p X y β t0 < valuationHistogram p X y β' t0) :
    qLoss p q X y β < qLoss p q X y β' :=
  qLoss_lt_of_first_histogram_lt p q hq X y β β' t0 hsmallest hlt

end PhdThesisLean.AdditiveContact
