/-
  Formalisation of the bounded-information subset-summary lower bound from
  Greg Baker's PhD thesis.

  Thesis source: coreset-obstruction/coreset.tex
  Thesis label: prop:subset-summary-lower-bound
  Thesis snapshot: 2c6418bcf9643fc6e039237f0f59ace14b2557fc
-/

import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

namespace PhdThesisLean.SubsetSummary

open scoped BigOperators

abbrev UnweightedSummary (m s : ℕ) (A : Type*) [Fintype A] :=
  Σ j : Fin (s + 1),
    Σ S : ↥((Finset.univ : Finset (Fin m)).powersetCard j.val),
      S.1 → A

abbrev WeightedSummary (m s : ℕ) (A W : Type*) [Fintype A] [Fintype W] :=
  Σ j : Fin (s + 1),
    Σ S : ↥((Finset.univ : Finset (Fin m)).powersetCard j.val),
      S.1 → (A × W)

theorem card_unweightedSummary
    (m s : ℕ) (A : Type*) [Fintype A] :
    Fintype.card (UnweightedSummary m s A) =
      ∑ j ∈ Finset.range (s + 1),
        Nat.choose m j * Fintype.card A ^ j := by
  classical
  simp only [UnweightedSummary, Fintype.card_sigma, Fintype.card_fun,
    Fintype.card_coe]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.univ_eq_attach]
  calc
    (∑ x ∈ ((Finset.univ : Finset (Fin m)).powersetCard j.val).attach,
        Fintype.card A ^ x.val.card) =
        ∑ x ∈ (Finset.univ : Finset (Fin m)).powersetCard j.val,
          Fintype.card A ^ x.card :=
      by
        simpa only using Finset.sum_attach
          ((Finset.univ : Finset (Fin m)).powersetCard j.val)
          (fun x ↦ Fintype.card A ^ x.card)
    _ = Nat.choose m j.val * Fintype.card A ^ j.val := by
      rw [Finset.sum_powersetCard]
      simp

theorem card_weightedSummary
    (m s : ℕ) (A W : Type*) [Fintype A] [Fintype W] :
    Fintype.card (WeightedSummary m s A W) =
      ∑ j ∈ Finset.range (s + 1),
        Nat.choose m j * (Fintype.card A * Fintype.card W) ^ j := by
  classical
  simp only [WeightedSummary, Fintype.card_sigma, Fintype.card_fun,
    Fintype.card_coe, Fintype.card_prod]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.univ_eq_attach]
  calc
    (∑ x ∈ ((Finset.univ : Finset (Fin m)).powersetCard j.val).attach,
        (Fintype.card A * Fintype.card W) ^ x.val.card) =
        ∑ x ∈ (Finset.univ : Finset (Fin m)).powersetCard j.val,
          (Fintype.card A * Fintype.card W) ^ x.card :=
      by
        simpa only using Finset.sum_attach
          ((Finset.univ : Finset (Fin m)).powersetCard j.val)
          (fun x ↦ (Fintype.card A * Fintype.card W) ^ x.card)
    _ = Nat.choose m j.val *
        (Fintype.card A * Fintype.card W) ^ j.val := by
      rw [Finset.sum_powersetCard]
      simp

def trueParameter
    {p m : ℕ} [Fact p.Prime] {A : Type*}
    (embed : A → ℚ_[p]) (u : Fin m → A) : Fin m → ℚ_[p] :=
  fun i ↦ embed (u i)

def standardBasisVector
    {p m : ℕ} [Fact p.Prime] (i : Fin m) : Fin m → ℚ_[p] :=
  fun j ↦ if j = i then 1 else 0

def standardDataset
    {p m : ℕ} [Fact p.Prime] {A : Type*}
    (embed : A → ℚ_[p]) (u : Fin m → A) :
    Fin m → ((Fin m → ℚ_[p]) × ℚ_[p]) :=
  fun i ↦ (standardBasisVector i, embed (u i))

theorem standardDataset_injective
    {p m : ℕ} [Fact p.Prime] {A : Type*}
    (embed : A → ℚ_[p]) (u : Fin m → A) :
    Function.Injective (standardDataset embed u) := by
  intro i j hij
  by_contra hne
  have hx := congrArg (fun z ↦ z.1 i) hij
  simp [standardDataset, standardBasisVector, hne] at hx

@[simp]
theorem dotProduct_standardBasisVector
    {p m : ℕ} [Fact p.Prime]
    (β : Fin m → ℚ_[p]) (i : Fin m) :
    dotProduct β (standardBasisVector i) = β i := by
  classical
  rw [dotProduct, Finset.sum_eq_single i]
  · simp [standardBasisVector]
  · intro j _hj hji
    simp [standardBasisVector, hji]
  · simp

noncomputable def standardDatasetLoss
    {p m : ℕ} [Fact p.Prime] {A : Type*}
    (embed : A → ℚ_[p]) (u : Fin m → A) (β : Fin m → ℚ_[p]) : ℝ :=
  ∑ i, ‖(standardDataset embed u i).2 -
    dotProduct β (standardDataset embed u i).1‖

noncomputable def standardPadicLoss
    {p m : ℕ} [Fact p.Prime] {A : Type*}
    (embed : A → ℚ_[p]) (u : Fin m → A) (β : Fin m → ℚ_[p]) : ℝ :=
  ∑ i, ‖embed (u i) - β i‖

theorem standardDatasetLoss_eq_standardPadicLoss
    {p m : ℕ} [Fact p.Prime] {A : Type*}
    (embed : A → ℚ_[p]) (u : Fin m → A) (β : Fin m → ℚ_[p]) :
    standardDatasetLoss embed u β = standardPadicLoss embed u β := by
  simp [standardDatasetLoss, standardPadicLoss, standardDataset]

def IsUniqueGlobalMinimizer
    {Θ : Type*} (f : Θ → ℝ) (x : Θ) : Prop :=
  (∀ y, f x ≤ f y) ∧ ∀ y, f y = f x → y = x

theorem standardPadicLoss_eq_zero_iff
    {p m : ℕ} [Fact p.Prime] {A : Type*}
    (embed : A → ℚ_[p]) (u : Fin m → A) (β : Fin m → ℚ_[p]) :
    standardPadicLoss embed u β = 0 ↔ β = trueParameter embed u := by
  constructor
  · intro h
    apply funext
    intro i
    have hi : ‖embed (u i) - β i‖ = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _hj ↦ norm_nonneg (embed (u j) - β j))).mp h i (Finset.mem_univ i)
    exact (sub_eq_zero.mp (norm_eq_zero.mp hi)).symm
  · rintro rfl
    simp [standardPadicLoss, trueParameter]

theorem trueParameter_unique_minimizer
    {p m : ℕ} [Fact p.Prime] {A : Type*}
    (embed : A → ℚ_[p]) (u : Fin m → A) :
    IsUniqueGlobalMinimizer (standardPadicLoss embed u)
      (trueParameter embed u) := by
  constructor
  · intro β
    rw [(standardPadicLoss_eq_zero_iff embed u _).mpr rfl]
    exact Finset.sum_nonneg fun i _hi ↦ norm_nonneg _
  · intro β hβ
    apply (standardPadicLoss_eq_zero_iff embed u β).mp
    rw [hβ]
    exact (standardPadicLoss_eq_zero_iff embed u _).mpr rfl

theorem decoder_failure_of_card_lt
    (p m : ℕ) [Fact p.Prime]
    {A Summary : Type*} [Fintype A] [Fintype Summary]
    (embed : A → ℚ_[p]) (Δ : ℝ)
    (hsep : ∀ a b : A, a ≠ b → 2 * Δ < ‖embed a - embed b‖)
    (C : (Fin m → A) → Summary)
    (g : Summary → Fin m → ℚ_[p])
    (hcard : Fintype.card Summary < Fintype.card A ^ m) :
    ∃ u : Fin m → A,
      Δ < ‖g (C u) - trueParameter embed u‖ := by
  have hcard' :
      Fintype.card Summary < Fintype.card (Fin m → A) := by
    simpa [Fintype.card_fun, Fintype.card_fin] using hcard
  obtain ⟨u, v, huv, hC⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt C hcard'
  obtain ⟨i, hi⟩ := Function.ne_iff.mp huv
  by_contra hfail
  push_neg at hfail
  have huCoord :
      ‖embed (u i) - g (C u) i‖ ≤ Δ := by
    rw [norm_sub_rev]
    have hcoord :
        ‖g (C u) i - embed (u i)‖ ≤
          ‖g (C u) - trueParameter embed u‖ := by
      simpa [trueParameter] using
        norm_le_pi_norm (g (C u) - trueParameter embed u) i
    exact hcoord.trans (hfail u)
  have hvCoord :
      ‖g (C u) i - embed (v i)‖ ≤ Δ := by
    have hv := hfail v
    rw [← hC] at hv
    have hcoord :
        ‖g (C u) i - embed (v i)‖ ≤
          ‖g (C u) - trueParameter embed v‖ := by
      simpa [trueParameter] using
        norm_le_pi_norm (g (C u) - trueParameter embed v) i
    exact hcoord.trans hv
  have hdist :
      ‖embed (u i) - embed (v i)‖ ≤ 2 * Δ := by
    calc
      ‖embed (u i) - embed (v i)‖ =
          ‖(embed (u i) - g (C u) i) +
            (g (C u) i - embed (v i))‖ := by ring_nf
      _ ≤ ‖embed (u i) - g (C u) i‖ +
          ‖g (C u) i - embed (v i)‖ := norm_add_le _ _
      _ ≤ 2 * Δ := by linarith
  exact (not_lt_of_ge hdist) (hsep (u i) (v i) hi)

theorem subset_summary_lower_bound_unweighted
    (p m s : ℕ) [Fact p.Prime] (_hm : 1 ≤ m) (_hs : s < m)
    {A : Type*} [Fintype A]
    (embed : A → ℚ_[p]) (Δ : ℝ) (_hΔ : 0 < Δ)
    (hsep : ∀ a b : A, a ≠ b → 2 * Δ < ‖embed a - embed b‖)
    (C : (Fin m → A) → UnweightedSummary m s A)
    (g : UnweightedSummary m s A → Fin m → ℚ_[p])
    (hcount :
      (∑ j ∈ Finset.range (s + 1),
        Nat.choose m j * Fintype.card A ^ j) <
          Fintype.card A ^ m) :
    (∀ u : Fin m → A,
      IsUniqueGlobalMinimizer (standardPadicLoss embed u)
        (trueParameter embed u)) ∧
    ∃ u : Fin m → A,
      Δ < ‖g (C u) - trueParameter embed u‖ := by
  constructor
  · exact trueParameter_unique_minimizer embed
  · apply decoder_failure_of_card_lt p m embed Δ hsep C g
    rwa [card_unweightedSummary]

theorem subset_summary_lower_bound_weighted
    (p m s : ℕ) [Fact p.Prime] (_hm : 1 ≤ m) (_hs : s < m)
    {A W : Type*} [Fintype A] [Fintype W]
    (embed : A → ℚ_[p]) (Δ : ℝ) (_hΔ : 0 < Δ)
    (hsep : ∀ a b : A, a ≠ b → 2 * Δ < ‖embed a - embed b‖)
    (C : (Fin m → A) → WeightedSummary m s A W)
    (g : WeightedSummary m s A W → Fin m → ℚ_[p])
    (hcount :
      (∑ j ∈ Finset.range (s + 1),
        Nat.choose m j *
          (Fintype.card A * Fintype.card W) ^ j) <
            Fintype.card A ^ m) :
    (∀ u : Fin m → A,
      IsUniqueGlobalMinimizer (standardPadicLoss embed u)
        (trueParameter embed u)) ∧
    ∃ u : Fin m → A,
      Δ < ‖g (C u) - trueParameter embed u‖ := by
  constructor
  · exact trueParameter_unique_minimizer embed
  · apply decoder_failure_of_card_lt p m embed Δ hsep C g
    rwa [card_weightedSummary]

/-- Statement-faithful wrapper for thesis Theorem
`prop:subset-summary-lower-bound`, combining its unweighted and finite-weight
alphabet conclusions. -/
theorem bounded_information_subset_summaries
    (p m s : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hs : s < m)
    {A W : Type*} [Fintype A] [Fintype W]
    (embed : A → ℚ_[p]) (Δ : ℝ) (hΔ : 0 < Δ)
    (hsep : ∀ a b : A, a ≠ b → 2 * Δ < ‖embed a - embed b‖)
    (C : (Fin m → A) → UnweightedSummary m s A)
    (g : UnweightedSummary m s A → Fin m → ℚ_[p])
    (hcount :
      (∑ j ∈ Finset.range (s + 1),
        Nat.choose m j * Fintype.card A ^ j) <
          Fintype.card A ^ m)
    (Cw : (Fin m → A) → WeightedSummary m s A W)
    (gw : WeightedSummary m s A W → Fin m → ℚ_[p])
    (hcountW :
      (∑ j ∈ Finset.range (s + 1),
        Nat.choose m j *
          (Fintype.card A * Fintype.card W) ^ j) <
            Fintype.card A ^ m) :
    (∀ u : Fin m → A,
      IsUniqueGlobalMinimizer (standardDatasetLoss embed u)
        (trueParameter embed u)) ∧
    (∃ u : Fin m → A,
      Δ < ‖g (C u) - trueParameter embed u‖) ∧
    ∃ u : Fin m → A,
      Δ < ‖gw (Cw u) - trueParameter embed u‖ := by
  have hu := subset_summary_lower_bound_unweighted p m s hm hs
    embed Δ hΔ hsep C g hcount
  have hw := subset_summary_lower_bound_weighted p m s hm hs
    embed Δ hΔ hsep Cw gw hcountW
  refine ⟨?_, hu.2, hw.2⟩
  intro u
  have heq : standardDatasetLoss embed u = standardPadicLoss embed u := by
    funext β
    exact standardDatasetLoss_eq_standardPadicLoss embed u β
  rw [heq]
  exact hu.1 u

end PhdThesisLean.SubsetSummary
