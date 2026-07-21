/-
  Formalisation of the central contact theorem from Chapter 2 of Greg Baker's
  PhD thesis.

  Thesis source: multivariate-padic-linear-regression/coretheorem.tex
  Thesis label: core-theorem
  Thesis snapshot: 2c6418bcf9643fc6e039237f0f59ace14b2557fc

  Algorithm supplement source: multivariate-padic-linear-regression/algorithm.tex
  Supplement labels: lem:independent-contacts, rem:existence-minimiser
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Tactic

namespace PhdThesisLean.ContactTheorem

open scoped BigOperators

/-- Predictor vectors for an affine model with `n` slope coefficients. -/
abbrev Point (n : ℕ) := Fin n → ℚ

/-- Affine parameters, with the intercept at coordinate zero. -/
abbrev Model (n : ℕ) := Fin (n + 1) → ℚ

/-- Add the affine coordinate `1` in front of a predictor vector. -/
def augment {n : ℕ} (x : Point n) : Fin (n + 1) → ℚ :=
  Fin.cases 1 x

/-- Evaluate an affine model at a predictor vector. -/
def affineEval {n : ℕ} (β : Model n) (x : Point n) : ℚ :=
  dotProduct β (augment x)

/-- Evaluation at a fixed predictor is linear in the model parameters. -/
def evalLinear {n : ℕ} (x : Point n) : Model n →ₗ[ℚ] ℚ where
  toFun β := affineEval β x
  map_add' β γ := by simp [affineEval]
  map_smul' a β := by simp [affineEval]

/-- Dot product with a fixed parameter vector, viewed as a linear functional
on augmented predictor vectors. -/
def dotLinear {n : ℕ} (φ : Model n) : Model n →ₗ[ℚ] ℚ where
  toFun z := dotProduct φ z
  map_add' z w := by simp
  map_smul' a z := by simp

/-- Residual at observation `i`. Indexed data preserve repeated observations. -/
def residual {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (β : Model n) (i : Fin k) : ℚ :=
  affineEval β (X i) - y i

/-- Summed rational `p`-adic residual loss. -/
def loss (p : ℕ) {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (β : Model n) : ℚ :=
  ∑ i, padicNorm p (residual X y β i)

/-- The observation indices contacted exactly by `β`. -/
def contacts {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (β : Model n) : Finset (Fin k) :=
  Finset.univ.filter fun i ↦ residual X y β i = 0

/-- Number of observations contacted exactly by `β`. -/
def contactCount {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (β : Model n) : ℕ :=
  (contacts X y β).card

/-- Degeneracy from the thesis: a nonzero affine function vanishes on every predictor. -/
def Degenerate {n k : ℕ} (X : Fin k → Point n) : Prop :=
  ∃ φ : Model n, φ ≠ 0 ∧ ∀ i, affineEval φ (X i) = 0

/-- A set of observation indices is affinely independent when their augmented
predictor vectors `(Xᵢ, 1)` are linearly independent. -/
def Independent {n k : ℕ} (X : Fin k → Point n) (A : Finset (Fin k)) : Prop :=
  LinearIndepOn ℚ (fun i ↦ augment (X i)) (A : Set (Fin k))

/-- Every index in `A` is contacted by `β`. -/
def FitsOn {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (A : Finset (Fin k)) (β : Model n) : Prop :=
  ∀ i ∈ A, residual X y β i = 0

/-- Evaluate a parameter direction on a selected set of observations. -/
def evalOn {n k : ℕ} (X : Fin k → Point n) (A : Finset (Fin k)) :
    Model n →ₗ[ℚ] ((i : A) → ℚ) where
  toFun φ i := affineEval φ (X i.1)
  map_add' φ ψ := by
    ext i
    simp [affineEval]
  map_smul' a φ := by
    ext i
    simp [affineEval]

/-- Fewer than `n + 1` contact equations have a nonzero parameter direction
that leaves every existing contact fixed. -/
theorem exists_direction_vanishing_on
    {n k : ℕ} (X : Fin k → Point n) (A : Finset (Fin k))
    (hA : A.card < n + 1) :
    ∃ φ : Model n, φ ≠ 0 ∧ ∀ i ∈ A, affineEval φ (X i) = 0 := by
  let T := evalOn X A
  have hdim : Module.finrank ℚ ((i : A) → ℚ) < Module.finrank ℚ (Model n) := by
    simpa [Model] using hA
  have hker : LinearMap.ker T ≠ ⊥ := T.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨φ, hφker, hφne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨φ, hφne, ?_⟩
  rw [LinearMap.mem_ker] at hφker
  intro i hi
  have hi' := congrFun hφker (⟨i, hi⟩ : A)
  simpa [T, evalOn] using hi'

@[simp]
theorem residual_add_smul
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (β φ : Model n) (a : ℚ) (i : Fin k) :
    residual X y (β + a • φ) i =
      residual X y β i + a * affineEval φ (X i) := by
  simp [residual, affineEval]
  ring

/-- The local ultrametric estimate used in the perturbation proof. -/
theorem padicNorm_add_mul_le
    {p : ℕ} [Fact p.Prime] {r a d : ℚ} (hd : d ≠ 0)
    (ha : padicNorm p a ≤ padicNorm p (-r / d)) :
    padicNorm p (r + a * d) ≤ padicNorm p r := by
  have hdnorm : padicNorm p d ≠ 0 := padicNorm.nonzero hd
  have hmul : padicNorm p (a * d) ≤ padicNorm p r := by
    calc
      padicNorm p (a * d) = padicNorm p a * padicNorm p d := padicNorm.mul _ _
      _ ≤ padicNorm p (-r / d) * padicNorm p d :=
        mul_le_mul_of_nonneg_right ha (padicNorm.nonneg d)
      _ = padicNorm p r := by
        rw [padicNorm.div, padicNorm.neg, div_mul_cancel₀ _ hdnorm]
  exact padicNorm.nonarchimedean.trans_eq (max_eq_left hmul)

/-- One independent-contact lifting step. Starting from fewer than `n + 1`
independent contacts, a non-degenerate dataset supplies one more independent
contact without increasing any residual norm, hence without increasing loss. -/
theorem lift_independent_contacts
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n)
    (A : Finset (Fin k)) (hdeg : ¬Degenerate X)
    (hAcard : A.card < n + 1) (hAind : Independent X A)
    (hAfits : FitsOn X y A β) :
    ∃ j : Fin k, ∃ β' : Model n,
      j ∉ A ∧ Independent X (insert j A) ∧ FitsOn X y (insert j A) β' ∧
        loss p X y β' ≤ loss p X y β := by
  obtain ⟨φ, hφne, hφA⟩ := exists_direction_vanishing_on X A hAcard
  have hactive_exists : ∃ i, affineEval φ (X i) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hdeg ⟨φ, hφne, h⟩
  let active : Finset (Fin k) :=
    Finset.univ.filter fun i ↦ affineEval φ (X i) ≠ 0
  have hactive : active.Nonempty := by
    obtain ⟨i, hi⟩ := hactive_exists
    exact ⟨i, by simp [active, hi]⟩
  obtain ⟨j, hjactive, hjmin⟩ := Finset.exists_min_image active
    (fun i ↦ padicNorm p (-residual X y β i / affineEval φ (X i))) hactive
  let a : ℚ := -residual X y β j / affineEval φ (X j)
  let β' : Model n := β + a • φ
  have hjdenom : affineEval φ (X j) ≠ 0 := by
    simpa [active] using hjactive
  have hjnotmem : j ∉ A := by
    intro hjA
    exact hjdenom (hφA j hjA)
  have hnorm_le : ∀ i, padicNorm p (residual X y β' i) ≤
      padicNorm p (residual X y β i) := by
    intro i
    by_cases hi : affineEval φ (X i) = 0
    · simp [β', residual_add_smul, hi]
    · have hamin : padicNorm p a ≤
          padicNorm p (-residual X y β i / affineEval φ (X i)) := by
        exact hjmin i (by simp [active, hi])
      change padicNorm p (residual X y (β + a • φ) i) ≤ _
      rw [residual_add_smul]
      exact padicNorm_add_mul_le hi hamin
  have hjnew : residual X y β' j = 0 := by
    change residual X y (β + a • φ) j = 0
    rw [residual_add_smul]
    dsimp [a]
    field_simp
    ring
  have hspan_le :
      Submodule.span ℚ ((fun i ↦ augment (X i)) '' (A : Set (Fin k))) ≤
        LinearMap.ker (dotLinear φ) := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨i, hiA, rfl⟩ := hz
    change dotLinear φ (augment (X i)) = 0
    simpa [dotLinear, affineEval] using hφA i hiA
  have hjnotspan : augment (X j) ∉
      Submodule.span ℚ ((fun i ↦ augment (X i)) '' (A : Set (Fin k))) := by
    intro hjspan
    have hjker := hspan_le hjspan
    change dotLinear φ (augment (X j)) = 0 at hjker
    exact hjdenom (by simpa [dotLinear, affineEval] using hjker)
  have hinsert_ind : Independent X (insert j A) := by
    simpa [Independent] using hAind.insert hjnotspan
  have hinsert_fits : FitsOn X y (insert j A) β' := by
    intro i hi
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hiA
    · exact hjnew
    · change residual X y (β + a • φ) i = 0
      rw [residual_add_smul, hφA i hiA, hAfits i hiA]
      ring
  refine ⟨j, β', hjnotmem, hinsert_ind, hinsert_fits, ?_⟩
  unfold loss
  exact Finset.sum_le_sum fun i _ ↦ hnorm_le i

/-- Iterate independent-contact lifting a prescribed number of times. -/
theorem extend_independent_contacts_aux
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (hdeg : ¬Degenerate X)
    (remaining : ℕ) (A : Finset (Fin k)) (β : Model n)
    (hcard : A.card + remaining = n + 1)
    (hAind : Independent X A) (hAfits : FitsOn X y A β) :
    ∃ B : Finset (Fin k), ∃ β' : Model n,
      A ⊆ B ∧ B.card = n + 1 ∧ Independent X B ∧ FitsOn X y B β' ∧
        loss p X y β' ≤ loss p X y β := by
  induction remaining generalizing A β with
  | zero =>
      refine ⟨A, β, Finset.Subset.rfl, ?_, hAind, hAfits, le_rfl⟩
      omega
  | succ remaining ih =>
      have hAcard : A.card < n + 1 := by omega
      obtain ⟨j, β₁, hjnotmem, hinsert_ind, hinsert_fits, hlift⟩ :=
        lift_independent_contacts p X y β A hdeg hAcard hAind hAfits
      have hcard_insert : (insert j A).card + remaining = n + 1 := by
        rw [Finset.card_insert_of_notMem hjnotmem]
        omega
      obtain ⟨B, β', hsubset, hBcard, hBind, hBfits, hfinal⟩ :=
        ih (insert j A) β₁ hcard_insert hinsert_ind hinsert_fits
      refine ⟨B, β', ?_, hBcard, hBind, hBfits, hfinal.trans hlift⟩
      exact (Finset.subset_insert j A).trans hsubset

/-- Independent-contact refinement from the thesis algorithm supplement. Every
model on a non-degenerate dataset can be replaced, without increasing loss, by
a model through `n + 1` affinely independent observations. -/
theorem independent_contact_refinement
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n)
    (hdeg : ¬Degenerate X) :
    ∃ A : Finset (Fin k), ∃ β' : Model n,
      A.card = n + 1 ∧ Independent X A ∧ FitsOn X y A β' ∧
        loss p X y β' ≤ loss p X y β := by
  obtain ⟨A, β', _, hAcard, hAind, hAfits, hloss⟩ :=
    extend_independent_contacts_aux p X y hdeg (n + 1) ∅ β
      (by simp) (by simp [Independent]) (by simp [FitsOn])
  exact ⟨A, β', hAcard, hAind, hAfits, hloss⟩

/-- `n + 1` affinely independent interpolation conditions determine a unique
affine model. -/
theorem unique_interpolant
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (A : Finset (Fin k)) (hAcard : A.card = n + 1)
    (hAind : Independent X A) {β γ : Model n}
    (hβfits : FitsOn X y A β) (hγfits : FitsOn X y A γ) :
    β = γ := by
  classical
  let v : A → Model n := fun i ↦ augment (X i.1)
  have hlin : LinearIndependent ℚ v := by
    simpa [v, Independent, LinearIndepOn] using hAind
  have hApos : 0 < Fintype.card A := by
    simp [hAcard]
  letI : Nonempty A := Fintype.card_pos_iff.mp hApos
  have hcard_finrank : Fintype.card A = Module.finrank ℚ (Model n) := by
    simp [Model, hAcard]
  have hspan : Submodule.span ℚ (Set.range v) = ⊤ :=
    hlin.span_eq_top_of_card_eq_finrank hcard_finrank
  let δ : Model n := β - γ
  have hspan_le : Submodule.span ℚ (Set.range v) ≤ LinearMap.ker (dotLinear δ) := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨i, rfl⟩ := hz
    change affineEval δ (X i.1) = 0
    have hβ := hβfits i.1 i.2
    have hγ := hγfits i.1 i.2
    simp only [residual, sub_eq_zero] at hβ hγ
    simp only [δ, affineEval, sub_dotProduct]
    change affineEval β (X i.1) - affineEval γ (X i.1) = 0
    rw [hβ, hγ]
    ring
  have hker : LinearMap.ker (dotLinear δ) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact hspan_le
  have hdot_zero : ∀ z : Model n, dotLinear δ z = 0 := by
    intro z
    apply LinearMap.mem_ker.mp
    rw [hker]
    trivial
  have hδzero : δ = 0 := by
    funext q
    have hq := hdot_zero (fun i ↦ if i = q then 1 else 0)
    simpa [dotLinear, dotProduct] using hq
  exact sub_eq_zero.mp hδzero

/-- Affine models determined by some full-size independent contact set. -/
def CandidateModels {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) :
    Set (Model n) :=
  {β | ∃ A : Finset (Fin k),
    A.card = n + 1 ∧ Independent X A ∧ FitsOn X y A β}

/-- The independent interpolant family is finite. Each possible index set has
at most one interpolating affine model. -/
theorem finite_candidateModels
    {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) :
    (CandidateModels X y).Finite := by
  classical
  let fiber : Finset (Fin k) → Set (Model n) := fun A ↦
    {β | A.card = n + 1 ∧ Independent X A ∧ FitsOn X y A β}
  have hfiber : ∀ A, (fiber A).Finite := by
    intro A
    apply Set.Subsingleton.finite
    intro β hβ γ hγ
    exact unique_interpolant X y A hβ.1 hβ.2.1 hβ.2.2 hγ.2.2
  have hunion : (⋃ A, fiber A).Finite := Set.finite_iUnion hfiber
  rw [show CandidateModels X y = ⋃ A, fiber A by
    ext β
    simp [CandidateModels, fiber]]
  exact hunion

/-- Every model on non-degenerate data is dominated by a member of the finite
independent-interpolant family. -/
theorem exists_candidate_with_loss_le
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n)
    (hdeg : ¬Degenerate X) :
    ∃ β' ∈ CandidateModels X y, loss p X y β' ≤ loss p X y β := by
  obtain ⟨A, β', hAcard, hAind, hAfits, hloss⟩ :=
    independent_contact_refinement p X y β hdeg
  exact ⟨β', ⟨A, hAcard, hAind, hAfits⟩, hloss⟩

/-- Exact finite-search theorem. On non-degenerate data, the global minimum is
attained by a member of `CandidateModels`; each member is the unique interpolant
of its supporting `n + 1` affinely independent observations. -/
theorem exists_global_minimizer_on_independent_contacts
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (hdeg : ¬Degenerate X) :
    ∃ β' ∈ CandidateModels X y,
      ∀ β : Model n, loss p X y β' ≤ loss p X y β := by
  classical
  let H := CandidateModels X y
  have hHfinite : H.Finite := finite_candidateModels X y
  have hdominates : ∀ β : Model n, ∃ β' ∈ H,
      loss p X y β' ≤ loss p X y β := by
    intro β
    simpa [H] using exists_candidate_with_loss_le p X y β hdeg
  have hHnonempty : H.Nonempty := by
    obtain ⟨β', hβ'H, _⟩ := hdominates 0
    exact ⟨β', hβ'H⟩
  obtain ⟨β', hβ'H, hβ'min⟩ :=
    Set.exists_min_image H (loss p X y) hHfinite hHnonempty
  refine ⟨β', by simpa [H] using hβ'H, ?_⟩
  intro β
  obtain ⟨γ, hγH, hγle⟩ := hdominates β
  exact (hβ'min γ hγH).trans hγle

/-- If a model has fewer than `n + 1` contacts on non-degenerate data, there is
another model for which every residual norm is no larger and at least one is
strictly smaller. This is the reusable perturbation core of the contact
theorems. -/
theorem exists_pointwise_norm_improvement
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n)
    (hfew : contactCount X y β < n + 1) (hdeg : ¬Degenerate X) :
    ∃ β' : Model n,
      (∀ i, padicNorm p (residual X y β' i) ≤ padicNorm p (residual X y β i)) ∧
      ∃ j, residual X y β' j = 0 ∧ residual X y β j ≠ 0 := by
  obtain ⟨φ, hφne, hφcontacts⟩ :=
    exists_direction_vanishing_on X (contacts X y β) hfew
  have hactive_exists : ∃ i, affineEval φ (X i) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hdeg ⟨φ, hφne, h⟩
  let active : Finset (Fin k) :=
    Finset.univ.filter fun i ↦ affineEval φ (X i) ≠ 0
  have hactive : active.Nonempty := by
    obtain ⟨i, hi⟩ := hactive_exists
    exact ⟨i, by simp [active, hi]⟩
  obtain ⟨j, hjactive, hjmin⟩ := Finset.exists_min_image active
    (fun i ↦ padicNorm p (-residual X y β i / affineEval φ (X i))) hactive
  let a : ℚ := -residual X y β j / affineEval φ (X j)
  let β' : Model n := β + a • φ
  have hjdenom : affineEval φ (X j) ≠ 0 := by
    simpa [active] using hjactive
  have hnorm_le : ∀ i, padicNorm p (residual X y β' i) ≤
      padicNorm p (residual X y β i) := by
    intro i
    by_cases hi : affineEval φ (X i) = 0
    · simp [β', residual_add_smul, hi]
    · have hamin : padicNorm p a ≤
          padicNorm p (-residual X y β i / affineEval φ (X i)) := by
        exact hjmin i (by simp [active, hi])
      change padicNorm p (residual X y (β + a • φ) i) ≤ _
      rw [residual_add_smul]
      exact padicNorm_add_mul_le hi hamin
  have hjresidual_ne : residual X y β j ≠ 0 := by
    intro hjzero
    have hjcontact : j ∈ contacts X y β := by simp [contacts, hjzero]
    exact hjdenom (hφcontacts j hjcontact)
  have hjnew : residual X y β' j = 0 := by
    change residual X y (β + a • φ) j = 0
    rw [residual_add_smul]
    dsimp [a]
    field_simp
    ring
  exact ⟨β', hnorm_le, j, hjnew, hjresidual_ne⟩

/-- A global minimiser of summed `p`-adic residual loss either has at least
`n + 1` exact contacts or the predictor data are degenerate. This stronger
form does not need the thesis's size or well-posedness hypotheses. -/
theorem contact_or_degenerate_of_minimizes
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n)
    (hmin : ∀ γ : Model n, loss p X y β ≤ loss p X y γ) :
    n + 1 ≤ contactCount X y β ∨ Degenerate X := by
  by_cases hcontacts : n + 1 ≤ contactCount X y β
  · exact Or.inl hcontacts
  by_cases hdeg : Degenerate X
  · exact Or.inr hdeg
  exfalso
  obtain ⟨β', hnorm_le, j, hjnew, hjold⟩ :=
    exists_pointwise_norm_improvement p X y β (Nat.lt_of_not_ge hcontacts) hdeg
  have hjstrict : padicNorm p (residual X y β' j) <
      padicNorm p (residual X y β j) := by
    rw [hjnew, padicNorm.zero]
    exact lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero hjold))
  have hloss_strict : loss p X y β' < loss p X y β := by
    apply Finset.sum_lt_sum
    · intro i _
      exact hnorm_le i
    · exact ⟨j, Finset.mem_univ j, hjstrict⟩
  exact (not_lt_of_ge (hmin β')) hloss_strict

/-- Statement-faithful wrapper for thesis Theorem `core-theorem`.

The positivity, dataset-size, and response-consistency assumptions are retained
for exact correspondence, although the perturbation proof establishes the
dichotomy without using them. -/
theorem contact_theorem
    (p n k : ℕ) [Fact p.Prime]
    (_hn : 0 < n) (_hk : n + 1 ≤ k)
    (X : Fin k → Point n) (y : Fin k → ℚ)
    (_hwell : ∀ i j, y i ≠ y j → X i ≠ X j)
    (β : Model n)
    (hmin : ∀ γ : Model n, loss p X y β ≤ loss p X y γ) :
    n + 1 ≤ contactCount X y β ∨ Degenerate X :=
  contact_or_degenerate_of_minimizes p X y β hmin

end PhdThesisLean.ContactTheorem
