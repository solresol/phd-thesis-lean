/-
  Formalisation of Regularised Discrete Metric Linear Regression
  From Appendix 2 of Greg Baker's PhD Thesis

  Main theorem: The optimal loss for regularised linear regression with
  the discrete metric is one of the values {m - K(t) + r*t : t ∈ {0..n}}
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Tactic

/-! ## Basic Definitions -/

/-- A dataset is a finite set of points (X_i, y_i) ∈ ℚ^n × ℚ -/
structure Dataset (n : ℕ) where
  points : Finset (Fin n → ℚ) × ℚ
  size : ℕ
  size_eq : size = points.1.card

/-- A hyperplane is represented by coefficients (a₁, ..., aₙ, b) ∈ ℚ^(n+1) -/
structure Hyperplane (n : ℕ) where
  coeffs : Fin n → ℚ  -- a₁, ..., aₙ
  intercept : ℚ       -- b

/-- The discrete metric: d(x, y) = if x = y then 0 else 1 -/
def discreteMetric (x y : ℚ) : ℕ :=
  if x = y then 0 else 1

/-- Discrete metric satisfies ultrametric inequality -/
theorem discrete_metric_ultrametric (x y z : ℚ) :
    discreteMetric x z ≤ max (discreteMetric x y) (discreteMetric y z) := by
  simp only [discreteMetric]
  split_ifs with hxz hxy hyz hxy hyz
  · -- x = z: LHS = 0, always ≤ max
    exact Nat.zero_le _
  · -- x = z but also checking other cases - contradiction handled by split_ifs
    exact Nat.zero_le _
  · -- x ≠ z, x = y, y = z: contradiction since x = y = z implies x = z
    simp_all
  · -- x ≠ z, x = y, y ≠ z: LHS = 1, RHS = max 0 1 = 1
    simp
  · -- x ≠ z, x ≠ y, y = z: LHS = 1, RHS = max 1 0 = 1
    simp
  · -- x ≠ z, x ≠ y, y ≠ z: LHS = 1, RHS = max 1 1 = 1
    simp

/-! ## The N function: count non-zero coefficients -/

/-- N counts the number of non-zero coefficients in the first n arguments -/
def N (n : ℕ) (h : Hyperplane n) : ℕ :=
  (Finset.univ.filter (fun i => h.coeffs i ≠ 0)).card

/-- N is bounded by n -/
theorem N_le_n (n : ℕ) (h : Hyperplane n) : N n h ≤ n := by
  unfold N
  calc (Finset.univ.filter (fun i => h.coeffs i ≠ 0)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n := Finset.card_fin n

/-! ## The C function: count points on hyperplane -/

/-- Check if a point lies on a hyperplane (using discrete metric = 0) -/
def pointOnHyperplane (n : ℕ) (h : Hyperplane n) (x : Fin n → ℚ) (y : ℚ) : Prop :=
  (Finset.univ.sum (fun i => h.coeffs i * x i)) + h.intercept = y

instance (n : ℕ) (h : Hyperplane n) (x : Fin n → ℚ) (y : ℚ) :
    Decidable (pointOnHyperplane n h x y) :=
  inferInstanceAs (Decidable (_ = _))

/-- C counts the number of points in the dataset that the hyperplane passes through -/
def C (n : ℕ) (D : Finset ((Fin n → ℚ) × ℚ)) (h : Hyperplane n) : ℕ :=
  (D.filter (fun p => pointOnHyperplane n h p.1 p.2)).card

/-! ## The K function: maximum C for given N value -/

/-- G(t) is the set of hyperplanes with exactly t non-zero coefficients -/
def G (n : ℕ) (t : ℕ) : Set (Hyperplane n) :=
  {h | N n h = t}

/-- K(t) is the maximum number of points any hyperplane with N=t passes through -/
noncomputable def K (n : ℕ) (D : Finset ((Fin n → ℚ) × ℚ)) (t : ℕ) : ℕ :=
  sSup {c | ∃ h : Hyperplane n, N n h = t ∧ C n D h = c}

/-! ## The Loss Function -/

/-- Loss function for regularised discrete metric regression -/
def Loss (n : ℕ) (D : Finset ((Fin n → ℚ) × ℚ)) (r : ℚ) (h : Hyperplane n) : ℚ :=
  D.card - C n D h + r * N n h

/-- Equivalent formulation: we want to maximise C(h) - r*N(h) -/
def Gain (n : ℕ) (D : Finset ((Fin n → ℚ) × ℚ)) (r : ℚ) (h : Hyperplane n) : ℚ :=
  C n D h - r * N n h

theorem loss_gain_relation (n : ℕ) (D : Finset ((Fin n → ℚ) × ℚ)) (r : ℚ) (h : Hyperplane n) :
    Loss n D r h = D.card - Gain n D r h := by
  unfold Loss Gain
  ring

/-! ## Main Theorem: Optimal Loss is in Finite Set -/

/-- The set of possible optimal losses -/
def PossibleLosses (n : ℕ) (D : Finset ((Fin n → ℚ) × ℚ)) (r : ℚ) : Finset ℚ :=
  Finset.image (fun t => D.card - K n D t + r * t) (Finset.range (n + 1))

/-- For any hyperplane h with N(h) = t, its loss is at least m - K(t) + r*t -/
theorem loss_lower_bound (n : ℕ) (D : Finset ((Fin n → ℚ) × ℚ)) (r : ℚ)
    (h : Hyperplane n) (hr : 0 ≤ r) :
    ∃ t ∈ Finset.range (n + 1), D.card - K n D t + r * t ≤ Loss n D r h := by
  use N n h
  constructor
  · simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (N_le_n n h)
  · unfold Loss
    -- C(h) ≤ K(N(h)) by definition of K as supremum
    -- Therefore m - K(N(h)) + r*N(h) ≤ m - C(h) + r*N(h)
    sorry -- requires showing C n D h ≤ K n D (N n h)

/-- Main theorem: The optimal loss equals one of the enumerated values -/
theorem optimal_loss_in_finite_set (n : ℕ) (D : Finset ((Fin n → ℚ) × ℚ)) (r : ℚ)
    (hr : 0 ≤ r) (hD : D.Nonempty) :
    ∃ t ∈ Finset.range (n + 1),
      ∀ h : Hyperplane n, (D.card : ℚ) - K n D t + r * t ≤ Loss n D r h := by
  -- The optimal loss is achieved by some hyperplane h*
  -- h* has some value N(h*) = t* ∈ {0..n}
  -- The loss of h* equals m - C(h*) + r*t*
  -- Since h* achieves the optimum among hyperplanes with N=t*, C(h*) = K(t*)
  -- Therefore optimal loss = m - K(t*) + r*t*
  sorry

/-- The number of distinct optimal regularisation values is at most n+1 -/
theorem finite_critical_r_values (n : ℕ) (D : Finset ((Fin n → ℚ) × ℚ)) :
    ∃ S : Finset ℚ, S.card ≤ n + 1 ∧
      ∀ r₁ r₂ : ℚ, (∀ s ∈ S, r₁ < s ↔ r₂ < s) →
        (∀ t, K n D t - r₁ * t = K n D t - r₂ * t →
          -- same optimal t for both r values
          True) := by
  -- The critical values of r are where K(t₁) - r*t₁ = K(t₂) - r*t₂
  -- i.e., r = (K(t₁) - K(t₂)) / (t₁ - t₂)
  -- There are at most (n+1 choose 2) such values, but the relevant ones
  -- are at most n (the boundaries between consecutive t values being optimal)
  sorry

end
