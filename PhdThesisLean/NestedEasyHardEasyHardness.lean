import PhdThesisLean.NestedEasyHardEasy
import PhdThesisLean.FixedPrimeMaxCut

namespace PhdThesisLean.NestedEasyHardEasy

open scoped BigOperators
open PhdThesisLean.AllDifferent (IsGlobalMin)

/-!
# Stage 2 of the nested family is the fixed-prime Max-Cut reduction

This module connects Stage 2 of thesis Theorem `thm:nested-easy-hard-easy`
(`complexity-regimes/body.tex`) to the fixed-prime Max-Cut reduction of
Theorem `thm:fixed-prime-hardness` formalised in `FixedPrimeMaxCut.lean`.

`loss_A'_eq_maxCutLoss` shows that the summed `5`-adic loss of the hard dataset
`A'_G` is literally the Max-Cut forcing objective `maxCutLoss` at `p = 5`.
Consequently every result about that objective transfers: `stage2_globalMin_iff`
characterises the global minimisers of `A'_G` as the Boolean embeddings of the
maximum cuts of `G`, `stage2_boolean` shows every global minimiser is Boolean,
and `stage2_optimal_value` gives the optimal value `∑ M_j + |E| - maxcut`.

`nested_easy_hard_easy_with_hardness` bundles the three stages with the Max-Cut
characterisation of Stage 2. As in `FixedPrimeMaxCut.lean`, the complexity
transfer ("Max-Cut is NP-hard", polynomial-time computability of `G ↦ A'_G`) is
external; the semantic reduction is fully checked.
-/

variable {n : ℕ} {ε : Type*} [Fintype ε]

/-- The loss of `A'_G` is the fixed-prime Max-Cut objective at `p = 5`. -/
theorem loss_A'_eq_maxCutLoss (left right : ε → Fin n) (β : Fin n → ℚ_[5]) :
    loss (A'_G left right) β = FixedPrimeMaxCut.maxCutLoss left right β := by
  rw [loss_A']
  rfl

theorem loss_A'_fun_eq (left right : ε → Fin n) :
    loss (A'_G left right) = FixedPrimeMaxCut.maxCutLoss (p := 5) left right := by
  funext β
  exact loss_A'_eq_maxCutLoss left right β

/-- Every global minimiser of the hard dataset is Boolean. -/
theorem stage2_boolean (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    (β : Fin n → ℚ_[5]) (hβ : IsGlobalMin (loss (A'_G left right)) β) :
    ∀ j, β j = 0 ∨ β j = 1 := by
  rw [loss_A'_fun_eq] at hβ
  exact FixedPrimeMaxCut.globalMin_boolean left right hne hβ

/-- The global minimisers of `A'_G` are exactly the Boolean embeddings of the
maximum cuts of `G`: minimising the Stage 2 objective is Max-Cut. -/
theorem stage2_globalMin_iff (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    (β : Fin n → ℚ_[5]) :
    IsGlobalMin (loss (A'_G left right)) β ↔
      ∃ s : Fin n → Bool, β = FixedPrimeMaxCut.embed 5 s ∧
        ∀ s', FixedPrimeMaxCut.cutSize left right s' ≤
          FixedPrimeMaxCut.cutSize left right s := by
  rw [loss_A'_fun_eq]
  exact FixedPrimeMaxCut.isGlobalMin_iff left right hne β

/-- A global minimiser of the hard dataset exists. -/
theorem stage2_exists_globalMin (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e) :
    ∃ β : Fin n → ℚ_[5], IsGlobalMin (loss (A'_G left right)) β := by
  rw [loss_A'_fun_eq]
  exact FixedPrimeMaxCut.exists_globalMin left right hne

/-- The optimal value of the hard dataset is `∑ M_j + |E| - maxcut`. -/
theorem stage2_optimal_value (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    (β : Fin n → ℚ_[5]) (hβ : IsGlobalMin (loss (A'_G left right)) β) :
    loss (A'_G left right) β =
      (∑ j, (M left right j : ℝ)) + Fintype.card ε -
        FixedPrimeMaxCut.maxCut left right := by
  rw [loss_A'_fun_eq] at hβ ⊢
  exact FixedPrimeMaxCut.maxCutLoss_globalMin_eq left right hne hβ

/-- Thesis Theorem `thm:nested-easy-hard-easy` with Stage 2 stated as the
Max-Cut reduction: nesting; Stage 1 unique optimum `0`; Stage 2 global
minimisers are exactly the maximum cuts (with the Max-Cut optimal value and
`5|E| + 2|V|` rows); Stage 3 closed-form optimum and grid characterisation. -/
theorem nested_easy_hard_easy_with_hardness (left right : ε → Fin n)
    (hne : ∀ e, left e ≠ right e) {L : ℕ} (hL : 1 ≤ L) :
    (A_G n ≤ A'_G left right ∧ A'_G left right ≤ A''_G left right L) ∧
    ((∀ β : Fin n → ℚ_[5], IsGlobalMin (loss (A_G n)) β ↔ β = 0) ∧
      loss (A_G n) 0 = 0) ∧
    ((∃ β : Fin n → ℚ_[5], IsGlobalMin (loss (A'_G left right)) β) ∧
      (∀ β : Fin n → ℚ_[5], IsGlobalMin (loss (A'_G left right)) β ↔
        ∃ s : Fin n → Bool, β = FixedPrimeMaxCut.embed 5 s ∧
          ∀ s', FixedPrimeMaxCut.cutSize left right s' ≤
            FixedPrimeMaxCut.cutSize left right s) ∧
      (∀ β : Fin n → ℚ_[5], IsGlobalMin (loss (A'_G left right)) β →
        loss (A'_G left right) β =
          (∑ j, (M left right j : ℝ)) + Fintype.card ε -
            FixedPrimeMaxCut.maxCut left right) ∧
      Multiset.card (A'_G left right) = 5 * Fintype.card ε + 2 * n) ∧
    (IsGlobalMin (loss (A''_G left right L)) (fun _ : Fin n => c L) ∧
      ∀ β : Fin n → ℚ_[5],
        IsGlobalMin (loss (A''_G left right L)) β ↔ ∀ j, ∃ a : Fin 5, β j = t L a) :=
  ⟨⟨A_le_A' left right, A'_le_A'' left right L⟩,
    ⟨stage1_globalMin_iff, loss_A_zero⟩,
    ⟨stage2_exists_globalMin left right hne, stage2_globalMin_iff left right hne,
      stage2_optimal_value left right hne, card_A' left right hne⟩,
    ⟨stage3_optimum left right hne hL, stage3_globalMin_iff left right hne hL⟩⟩

end PhdThesisLean.NestedEasyHardEasy

#print axioms PhdThesisLean.NestedEasyHardEasy.loss_A'_eq_maxCutLoss
#print axioms PhdThesisLean.NestedEasyHardEasy.stage2_globalMin_iff
#print axioms PhdThesisLean.NestedEasyHardEasy.stage2_optimal_value
#print axioms PhdThesisLean.NestedEasyHardEasy.nested_easy_hard_easy_with_hardness
