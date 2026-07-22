/-
  Formalisation of discrete-metric regularised regression from Greg Baker's
  PhD thesis.

  Thesis source: ultrametric-regularisation-and-loss/unification.tex
  Thesis labels: thm:discrete-regularised, cor:discrete-algorithm
  Thesis snapshot: 2c6418bcf9643fc6e039237f0f59ace14b2557fc
-/

import PhdThesisLean.ContactTheorem

namespace PhdThesisLean.DiscreteRegularization

open scoped BigOperators
open ContactTheorem

/-- Number of nonzero slope coefficients. The affine intercept, stored at
coordinate zero of `Model n`, is not regularised. -/
def slopeSupportCount {n : ℕ} (β : Model n) : ℕ :=
  (Finset.univ.filter fun j : Fin n ↦ β j.succ ≠ 0).card

theorem slopeSupportCount_le {n : ℕ} (β : Model n) : slopeSupportCount β ≤ n := by
  unfold slopeSupportCount
  simpa using Finset.card_filter_le Finset.univ (fun j : Fin n ↦ β j.succ ≠ 0)

/-- A model whose nonzero slopes are exactly the chosen coordinates. -/
def modelWithSlopeSupport {n : ℕ} (A : Finset (Fin n)) : Model n :=
  Fin.cases 0 fun j ↦ if j ∈ A then 1 else 0

@[simp]
theorem slopeSupportCount_modelWithSlopeSupport
    {n : ℕ} (A : Finset (Fin n)) :
    slopeSupportCount (modelWithSlopeSupport A) = A.card := by
  simp [slopeSupportCount, modelWithSlopeSupport]

theorem exists_model_with_slopeSupportCount
    {n t : ℕ} (ht : t ≤ n) :
    ∃ β : Model n, slopeSupportCount β = t := by
  have ht' : t ≤ (Finset.univ : Finset (Fin n)).card := by simpa using ht
  obtain ⟨A, _, hAcard⟩ := Finset.exists_subset_card_eq ht'
  exact ⟨modelWithSlopeSupport A, by simp [hAcard]⟩

/-- Discrete residual loss plus an `ℓ₀` penalty on slopes. -/
def discreteLoss
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (r : ℚ) (β : Model n) : ℚ :=
  (k : ℚ) - contactCount X y β + r * slopeSupportCount β

/-- Contact counts attained by models with exactly `t` nonzero slopes. The
ambient range records the elementary bound `contactCount ≤ k`. -/
noncomputable def attainableContactCounts
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) (t : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range (k + 1)).filter fun c ↦
      ∃ β : Model n, slopeSupportCount β = t ∧ contactCount X y β = c

/-- Maximum attainable contact count at exact slope-support size `t`. The
value defaults to zero outside the feasible range, but every `t ≤ n` is proved
feasible below. -/
noncomputable def K
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) (t : ℕ) : ℕ :=
  (attainableContactCounts X y t).sup id

theorem contactCount_le_dataCount
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) :
    contactCount X y β ≤ k := by
  unfold contactCount contacts
  simpa using Finset.card_filter_le Finset.univ (fun i ↦ residual X y β i = 0)

theorem contactCount_mem_attainable
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (β : Model n) :
    contactCount X y β ∈ attainableContactCounts X y (slopeSupportCount β) := by
  classical
  rw [attainableContactCounts, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (contactCount_le_dataCount X y β)),
    β, rfl, rfl⟩

theorem contactCount_le_K
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) :
    contactCount X y β ≤ K X y (slopeSupportCount β) := by
  exact Finset.le_sup (f := id) (contactCount_mem_attainable X y β)

theorem attainableContactCounts_nonempty
    {n k t : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) (ht : t ≤ n) :
    (attainableContactCounts X y t).Nonempty := by
  obtain ⟨β, hβ⟩ := exists_model_with_slopeSupportCount ht
  rw [← hβ]
  exact ⟨contactCount X y β, contactCount_mem_attainable X y β⟩

/-- `K(t)` is attained for every feasible support size, repairing the missing
attainment step in the inherited prototype. -/
theorem exists_model_attaining_K
    {n k t : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) (ht : t ≤ n) :
    ∃ β : Model n, slopeSupportCount β = t ∧ contactCount X y β = K X y t := by
  classical
  let S := attainableContactCounts X y t
  have hS : S.Nonempty := attainableContactCounts_nonempty X y ht
  obtain ⟨c, hcS, hcmax⟩ := Finset.exists_mem_eq_sup S hS id
  have hcS' : c ∈ attainableContactCounts X y t := by simpa [S] using hcS
  rw [attainableContactCounts, Finset.mem_filter] at hcS'
  obtain ⟨_, β, hβsupport, hβcontact⟩ := hcS'
  refine ⟨β, hβsupport, ?_⟩
  rw [hβcontact, K]
  simpa [S] using hcmax.symm

/-- Candidate gain `K(t) - rt`. -/
def supportGain (Kvalues : ℕ → ℕ) (r : ℚ) (t : ℕ) : ℚ :=
  Kvalues t - r * t

/-- A selected support size maximizing candidate gain over `0, ..., n`. -/
noncomputable def bestSupportIndex
    (n : ℕ) (Kvalues : ℕ → ℕ) (r : ℚ) : Fin (n + 1) :=
  (Finset.exists_max_image (Finset.univ : Finset (Fin (n + 1)))
    (fun t ↦ supportGain Kvalues r t) (by simp)).choose

theorem bestSupportIndex_maximizes
    (n : ℕ) (Kvalues : ℕ → ℕ) (r : ℚ) (t : Fin (n + 1)) :
    supportGain Kvalues r t ≤ supportGain Kvalues r (bestSupportIndex n Kvalues r) := by
  exact (Finset.exists_max_image (Finset.univ : Finset (Fin (n + 1)))
    (fun s ↦ supportGain Kvalues r s) (by simp)).choose_spec.2 t (by simp)

theorem model_attaining_best_K_is_optimal
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) (r : ℚ)
    (βstar : Model n)
    (hsupport : slopeSupportCount βstar = bestSupportIndex n (K X y) r)
    (hcontact : contactCount X y βstar = K X y (bestSupportIndex n (K X y) r)) :
    (∀ β : Model n, discreteLoss X y r βstar ≤ discreteLoss X y r β) ∧
      discreteLoss X y r βstar =
        (k : ℚ) - K X y (bestSupportIndex n (K X y) r) +
          r * (bestSupportIndex n (K X y) r : ℕ) := by
  constructor
  · intro β
    let tβ : Fin (n + 1) :=
      ⟨slopeSupportCount β, Nat.lt_succ_of_le (slopeSupportCount_le β)⟩
    have hgain := bestSupportIndex_maximizes n (K X y) r tβ
    have hcontacts : contactCount X y β ≤ K X y (slopeSupportCount β) :=
      contactCount_le_K X y β
    unfold supportGain at hgain
    unfold discreteLoss
    rw [hsupport, hcontact]
    change
      (k : ℚ) - (K X y (bestSupportIndex n (K X y) r) : ℕ) +
          r * (bestSupportIndex n (K X y) r : ℕ) ≤
        (k : ℚ) - contactCount X y β + r * slopeSupportCount β
    have hcontacts' :
        (contactCount X y β : ℚ) ≤ K X y (slopeSupportCount β) := by
      exact_mod_cast hcontacts
    change
      (K X y (slopeSupportCount β) : ℚ) - r * slopeSupportCount β ≤
        (K X y (bestSupportIndex n (K X y) r) : ℚ) -
          r * (bestSupportIndex n (K X y) r : ℕ) at hgain
    linarith
  · simp [discreteLoss, hsupport, hcontact]

/-- Statement-faithful form of thesis Theorem `thm:discrete-regularised`.
The selected support size maximises `K(t) - rt`; an attaining model is a global
minimiser and has the displayed minimum loss. -/
theorem discrete_regularized_regression
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (r : ℚ) (_hr : 0 ≤ r) :
    ∃ tstar : Fin (n + 1), ∃ βstar : Model n,
      slopeSupportCount βstar = tstar ∧
      contactCount X y βstar = K X y tstar ∧
      (∀ t : Fin (n + 1),
        supportGain (K X y) r t ≤ supportGain (K X y) r tstar) ∧
      (∀ β : Model n, discreteLoss X y r βstar ≤ discreteLoss X y r β) ∧
      discreteLoss X y r βstar =
        (k : ℚ) - K X y tstar + r * (tstar : ℕ) := by
  let tstar := bestSupportIndex n (K X y) r
  obtain ⟨βstar, hsupport, hcontact⟩ :=
    exists_model_attaining_K X y (Nat.le_of_lt_succ tstar.isLt)
  obtain ⟨hmin, hloss⟩ :=
    model_attaining_best_K_is_optimal X y r βstar hsupport hcontact
  exact ⟨tstar, βstar, hsupport, hcontact,
    bestSupportIndex_maximizes n (K X y) r, hmin, hloss⟩

/-- Formal algorithmic corollary. Given one model attaining `K(t)` for every
support size, selecting the largest candidate gain and returning its witness
produces a global minimiser. -/
theorem discrete_algorithm
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (r : ℚ) (_hr : 0 ≤ r)
    (witness : Fin (n + 1) → Model n)
    (hwitness : ∀ t : Fin (n + 1),
      slopeSupportCount (witness t) = t ∧ contactCount X y (witness t) = K X y t) :
    let tstar := bestSupportIndex n (K X y) r
    let βstar := witness tstar
    slopeSupportCount βstar = tstar ∧
      contactCount X y βstar = K X y tstar ∧
      (∀ t : Fin (n + 1),
        supportGain (K X y) r t ≤ supportGain (K X y) r tstar) ∧
      (∀ β : Model n, discreteLoss X y r βstar ≤ discreteLoss X y r β) ∧
      discreteLoss X y r βstar =
        (k : ℚ) - K X y tstar + r * (tstar : ℕ) := by
  dsimp only
  let tstar := bestSupportIndex n (K X y) r
  have hsupport := (hwitness tstar).1
  have hcontact := (hwitness tstar).2
  obtain ⟨hmin, hloss⟩ :=
    model_attaining_best_K_is_optimal X y r (witness tstar) hsupport hcontact
  exact ⟨hsupport, hcontact, bestSupportIndex_maximizes n (K X y) r, hmin, hloss⟩

end PhdThesisLean.DiscreteRegularization
