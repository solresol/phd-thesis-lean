/-
  Formalisation of max-loss contact existence from Greg Baker's PhD thesis.

  Thesis source: ultrametric-regularisation-and-loss/unification.tex
  Thesis label: thm:max-contact-existence
  Thesis snapshot: 2c6418bcf9643fc6e039237f0f59ace14b2557fc
-/

import PhdThesisLean.AdditiveContact

namespace PhdThesisLean.MaxContact

open scoped NNReal
open AdditiveContact ContactTheorem

/-- Supremum of the finitely many rational `p`-adic residual magnitudes. The
empty supremum is zero. -/
noncomputable def maxLoss
    (p : ℕ) {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) : ℝ≥0 :=
  Finset.univ.sup fun i ↦ padicMagnitude p (residual X y β i)

theorem maxLoss_le_of_pointwise_norm_le
    (p : ℕ) {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) {β γ : Model n}
    (h : ∀ i, padicNorm p (residual X y β i) ≤ padicNorm p (residual X y γ i)) :
    maxLoss p X y β ≤ maxLoss p X y γ := by
  apply Finset.sup_le
  intro i hi
  exact (padicMagnitude_le_of_padicNorm_le (h i)).trans
    (Finset.le_sup (s := Finset.univ)
      (f := fun j ↦ padicMagnitude p (residual X y γ j)) hi)

/-- Every model on non-degenerate data is max-loss dominated by an
independent interpolant from the finite candidate family. -/
theorem exists_candidate_with_maxLoss_le
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n)
    (hdeg : ¬Degenerate X) :
    ∃ β' ∈ CandidateModels X y, maxLoss p X y β' ≤ maxLoss p X y β := by
  obtain ⟨A, β', hAcard, hAind, hAfits, hnorm, _hloss⟩ :=
    independent_contact_refinement p X y β hdeg
  exact ⟨β', ⟨A, hAcard, hAind, hAfits⟩,
    maxLoss_le_of_pointwise_norm_le p X y hnorm⟩

/-- A member of the independent-interpolant family has at least `n + 1`
exact contacts. -/
theorem candidate_has_full_contact_count
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) {β : Model n}
    (hβ : β ∈ CandidateModels X y) :
    n + 1 ≤ contactCount X y β := by
  obtain ⟨A, hAcard, _, hAfits⟩ := hβ
  rw [← hAcard]
  apply Finset.card_le_card
  intro i hi
  simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hAfits i hi

/-- Strong max-loss existence theorem. A global minimiser exists in the finite
independent-interpolant family, and therefore has at least `n + 1` contacts. -/
theorem exists_maxLoss_minimizer_with_contacts
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (hdeg : ¬Degenerate X) :
    ∃ β' : Model n,
      (∀ β : Model n, maxLoss p X y β' ≤ maxLoss p X y β) ∧
        n + 1 ≤ contactCount X y β' := by
  classical
  let H := CandidateModels X y
  have hHfinite : H.Finite := finite_candidateModels X y
  have hdominates : ∀ β : Model n, ∃ β' ∈ H,
      maxLoss p X y β' ≤ maxLoss p X y β := by
    intro β
    simpa [H] using exists_candidate_with_maxLoss_le p X y β hdeg
  have hHnonempty : H.Nonempty := by
    obtain ⟨β', hβ'H, _⟩ := hdominates 0
    exact ⟨β', hβ'H⟩
  obtain ⟨β', hβ'H, hβ'min⟩ :=
    Set.exists_min_image H (maxLoss p X y) hHfinite hHnonempty
  refine ⟨β', ?_, candidate_has_full_contact_count X y (by simpa [H] using hβ'H)⟩
  intro β
  obtain ⟨γ, hγH, hγle⟩ := hdominates β
  exact (hβ'min γ hγH).trans hγle

/-- Statement-faithful wrapper for thesis Theorem
`thm:max-contact-existence`. -/
theorem max_contact_existence
    (p n k : ℕ) [Fact p.Prime]
    (_hn : 0 < n) (_hk : n + 1 ≤ k)
    (X : Fin k → Point n) (y : Fin k → ℚ)
    (_hwell : ∀ i j, y i ≠ y j → X i ≠ X j)
    (hdeg : ¬Degenerate X) :
    ∃ β' : Model n,
      (∀ β : Model n, maxLoss p X y β' ≤ maxLoss p X y β) ∧
        n + 1 ≤ contactCount X y β' :=
  exists_maxLoss_minimizer_with_contacts p X y hdeg

end PhdThesisLean.MaxContact
