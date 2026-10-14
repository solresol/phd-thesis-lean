/-
  Formalisation of Lemma `lem:reg-finite-candidates` ("Reduction to finitely
  many candidate lines") from Greg Baker's PhD thesis, together with the
  weighted (nonnegative-weight) contact theory that its proof invokes.

  Thesis source: ultrametric-regularisation-and-loss/body.tex
  Thesis labels: lem:reg-finite-candidates (headline),
                 ex:monotonicity-violation (the six-point dataset)
-/

import Mathlib.Data.NNReal.Basic
import PhdThesisLean.ContactTheorem
import PhdThesisLean.AdditiveContact

namespace PhdThesisLean.RegularisedCandidates

/-!
# Reduction to finitely many candidate lines

Thesis source: `ultrametric-regularisation-and-loss/body.tex`
(Example `ex:monotonicity-violation`, Lemma `lem:reg-finite-candidates` and its
proof).

## What is formalised

* The six-point dataset `P₀ = (15, 12)`, `P₁ = (12, −14)`, `P₂ = (3, −4)`,
  `P₃ = (12, 11)`, `P₄ = (−15, 12)`, `P₅ = (7, 12)` (`xs`, `ys`, `dataX`), the
  per-point loss `ℓ(r) = 2^{−v₅(r)}` with `ℓ(0) = 0` (`ell`, which is literally
  `AdditiveContact.qPadicTerm 5 2`), and the regularised objective
  `𝓛(a, b; λ) = ∑ᵢ ℓ(yᵢ − a xᵢ − b) + λ 2^{−v₅(a)}` (`objective`), for the line
  `y = a x + b` encoded as `β : Model 1` with intercept `β 0 = b` and slope
  `β 1 = a` (the `ContactTheorem` convention).
* Headline `reg_finite_candidates`: for every `λ ≥ 0` the objective attains its
  minimum, and some minimiser either passes through two distinct data points or
  is horizontal (`β 1 = 0`) and passes through a data point. This is exactly the
  statement of `lem:reg-finite-candidates`.
* `reg_finite_candidates_zero`: the `λ = 0` refinement used in the thesis proof
  (the plain contact theorem gives alternative (1) outright).
* `reg_minimizer_in_finite_family` / `finite_augmentedCandidates`: the
  "finitely many lines through two of the seven augmented points" step.
* `not_fits_one_three`, `nonvertical_pair_count`, `distinct_horizontal_count`:
  the bookkeeping remarks in the lemma statement (the pair `P₁, P₃` is vertical;
  there are 14 non-vertical pairs; the six horizontals `y = yᵢ` are four lines).

## How the proof is formalised (the "seven-row" lifting)

The thesis folds the slope penalty into a seventh weighted row `(1, 0) ↦ 0`
and applies the Chapter 2 perturbation argument "verbatim to positive weights".
`ContactTheorem` always augments predictors with the affine constant `1`, so the
synthetic row (whose residual must be the bare slope) is not an affine row.
We therefore generalise the Chapter 2 development to a *homogeneous* design:
rows `Z i : Fin m → ℚ`, residual `⟪Z i, θ⟫ − t i`, weights `w i ≥ 0`, and an
arbitrary per-residual loss `g` that is monotone in the `p`-adic norm
(`NormMonotone`). All of `exists_direction_vanishing_on`,
`lift_independent_contacts`, `independent_contact_refinement`,
`unique_interpolant`, `finite_candidateModels` and
`exists_global_minimizer_on_independent_contacts` port line-for-line, because
the original proofs only ever use linearity of `θ ↦ ⟪Z i, θ⟫`
(`hexists_direction_vanishing_on`, `perturb_core`, `hlift_independent_contacts`,
`hindependent_contact_refinement`, `hunique_interpolant`,
`hfinite_candidateModels`, `weighted_exists_global_minimizer`). The affine
theory is recovered by `affineDesign X i := augment (X i)`
(`weighted_exists_global_minimizer_on_independent_contacts`,
`weighted_affine_contact_or_degenerate`), and the seven-row system of the
thesis is `designZ = Fin.snoc (augment ∘ dataX) ![0, 1]` with targets
`Fin.snoc ys 0` and weights `Fin.snoc 1 λ`.

## Correspondence notes

* The thesis per-point loss `2^{−v₅(r)}` is `(2 : ℝ) ^ (−padicValRat 5 r)`
  (`zpow`); no real powers are needed.
* Stronger than the thesis: the weighted contact theory holds for any prime
  `p`, any number of rows and parameters, any nonnegative weights (the thesis
  says "positive weights"), and any norm-monotone per-residual loss; the strict
  contact dichotomy (`weighted_contact_or_degenerate`) needs positive weights
  and `g 0 < g r` for `r ≠ 0`, matching `AdditiveContact`.
* The headline is handled uniformly for all `λ ≥ 0` (the thesis splits off
  `λ = 0`); the `λ = 0` case is additionally recorded in the sharper form
  `reg_finite_candidates_zero`.
* Alternative (1) is stated as "two distinct indices `i ≠ j` with the line
  through `Pᵢ` and `Pⱼ`"; since `P₁, P₃` share the abscissa `12` and no line
  fits both (`not_fits_one_three`), such a pair is automatically one of the 14
  non-vertical pairs counted in `nonvertical_pair_count`.
* Nothing is external: every step, including non-degeneracy of the augmented
  rows, is checked.
-/

open scoped BigOperators NNReal
open ContactTheorem AdditiveContact

/-- Global minimality of a real-valued function (same shape as
`PhdThesisLean.AllDifferent.IsGlobalMin`; that module is not imported here). -/
def IsGlobalMin {α : Type*} (f : α → ℝ) (x : α) : Prop := ∀ y, f x ≤ f y

/-! ## Homogeneous weighted contact theory

Rows `Z i ∈ ℚ^m`, targets `t i`, model `θ ∈ ℚ^m`, residual `⟪Z i, θ⟫ − t i`.
The affine theory of `ContactTheorem` is the special case `Z i = augment (X i)`.
-/

/-- Parameter vectors of a homogeneous linear model with `m` coefficients. -/
abbrev Param (m : ℕ) := Fin m → ℚ

/-- Residual of row `i`: the row `Z i` paired with `θ`, minus the target `t i`. -/
def hres {m k : ℕ} (Z : Fin k → Param m) (t : Fin k → ℚ) (θ : Param m) (i : Fin k) : ℚ :=
  dotProduct (Z i) θ - t i

/-- A per-residual loss that depends monotonically on the `p`-adic norm of the
residual. -/
def NormMonotone (p : ℕ) (g : ℚ → ℝ) : Prop :=
  ∀ r s : ℚ, padicNorm p r ≤ padicNorm p s → g r ≤ g s

/-- Weighted additive loss `∑ᵢ wᵢ g(rᵢ(θ))`. -/
noncomputable def weightedLoss {m k : ℕ} (g : ℚ → ℝ) (w : Fin k → ℝ)
    (Z : Fin k → Param m) (t : Fin k → ℚ) (θ : Param m) : ℝ :=
  ∑ i, w i * g (hres Z t θ i)

/-- Degeneracy: a nonzero parameter direction is orthogonal to every row. -/
def HDegenerate {m k : ℕ} (Z : Fin k → Param m) : Prop :=
  ∃ φ : Param m, φ ≠ 0 ∧ ∀ i, dotProduct (Z i) φ = 0

/-- The rows indexed by `A` are linearly independent. -/
def HIndependent {m k : ℕ} (Z : Fin k → Param m) (A : Finset (Fin k)) : Prop :=
  LinearIndepOn ℚ Z (A : Set (Fin k))

/-- Every row in `A` is contacted exactly by `θ`. -/
def HFitsOn {m k : ℕ} (Z : Fin k → Param m) (t : Fin k → ℚ) (A : Finset (Fin k))
    (θ : Param m) : Prop :=
  ∀ i ∈ A, hres Z t θ i = 0

/-- Rows contacted exactly by `θ`. -/
def hcontacts {m k : ℕ} (Z : Fin k → Param m) (t : Fin k → ℚ) (θ : Param m) :
    Finset (Fin k) :=
  Finset.univ.filter fun i ↦ hres Z t θ i = 0

/-- Number of rows contacted exactly by `θ`. -/
def hcontactCount {m k : ℕ} (Z : Fin k → Param m) (t : Fin k → ℚ) (θ : Param m) : ℕ :=
  (hcontacts Z t θ).card

/-- Dot product with a fixed vector, as a linear functional. -/
def dotFunctional {m : ℕ} (φ : Param m) : Param m →ₗ[ℚ] ℚ where
  toFun z := dotProduct φ z
  map_add' z w := by simp
  map_smul' a z := by simp

/-- Evaluate a parameter direction on the rows indexed by `A`. -/
def hevalOn {m k : ℕ} (Z : Fin k → Param m) (A : Finset (Fin k)) :
    Param m →ₗ[ℚ] ((i : A) → ℚ) where
  toFun θ i := dotProduct (Z i.1) θ
  map_add' θ ψ := by
    ext i
    simp [dotProduct_add]
  map_smul' a θ := by
    ext i
    simp [dotProduct_smul]

/-- Fewer than `m` row equations leave a nonzero parameter direction free. -/
theorem hexists_direction_vanishing_on
    {m k : ℕ} (Z : Fin k → Param m) (A : Finset (Fin k)) (hA : A.card < m) :
    ∃ φ : Param m, φ ≠ 0 ∧ ∀ i ∈ A, dotProduct (Z i) φ = 0 := by
  let T := hevalOn Z A
  have hdim : Module.finrank ℚ ((i : A) → ℚ) < Module.finrank ℚ (Param m) := by
    simpa [Param] using hA
  have hker : LinearMap.ker T ≠ ⊥ := T.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨φ, hφker, hφne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨φ, hφne, ?_⟩
  rw [LinearMap.mem_ker] at hφker
  intro i hi
  have hi' := congrFun hφker (⟨i, hi⟩ : A)
  simpa [T, hevalOn] using hi'

@[simp]
theorem hres_add_smul
    {m k : ℕ} (Z : Fin k → Param m) (t : Fin k → ℚ)
    (θ φ : Param m) (a : ℚ) (i : Fin k) :
    hres Z t (θ + a • φ) i = hres Z t θ i + a * dotProduct (Z i) φ := by
  simp only [hres, dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

/-- The perturbation core. Given a direction `φ` that is not orthogonal to
every row, a scaling of `φ` creates a new exact contact at a row not orthogonal
to `φ` while no residual norm increases. -/
theorem perturb_core
    (p : ℕ) [Fact p.Prime] {m k : ℕ}
    (Z : Fin k → Param m) (t : Fin k → ℚ) (θ φ : Param m)
    (hφ : ∃ i, dotProduct (Z i) φ ≠ 0) :
    ∃ j : Fin k, ∃ a : ℚ,
      dotProduct (Z j) φ ≠ 0 ∧ hres Z t (θ + a • φ) j = 0 ∧
        ∀ i, padicNorm p (hres Z t (θ + a • φ) i) ≤ padicNorm p (hres Z t θ i) := by
  let active : Finset (Fin k) := Finset.univ.filter fun i ↦ dotProduct (Z i) φ ≠ 0
  have hactive : active.Nonempty := by
    obtain ⟨i, hi⟩ := hφ
    exact ⟨i, by simp [active, hi]⟩
  obtain ⟨j, hjactive, hjmin⟩ := Finset.exists_min_image active
    (fun i ↦ padicNorm p (-hres Z t θ i / dotProduct (Z i) φ)) hactive
  have hjdenom : dotProduct (Z j) φ ≠ 0 := by
    simpa [active] using hjactive
  refine ⟨j, -hres Z t θ j / dotProduct (Z j) φ, hjdenom, ?_, ?_⟩
  · rw [hres_add_smul, div_mul_cancel₀ _ hjdenom]
    ring
  · intro i
    by_cases hi : dotProduct (Z i) φ = 0
    · simp [hres_add_smul, hi]
    · rw [hres_add_smul]
      exact padicNorm_add_mul_le hi (hjmin i (by simp [active, hi]))

/-- Homogeneous version of `ContactTheorem.exists_pointwise_norm_improvement`. -/
theorem hexists_pointwise_norm_improvement
    (p : ℕ) [Fact p.Prime] {m k : ℕ}
    (Z : Fin k → Param m) (t : Fin k → ℚ) (θ : Param m)
    (hfew : hcontactCount Z t θ < m) (hdeg : ¬HDegenerate Z) :
    ∃ θ' : Param m,
      (∀ i, padicNorm p (hres Z t θ' i) ≤ padicNorm p (hres Z t θ i)) ∧
      ∃ j, hres Z t θ' j = 0 ∧ hres Z t θ j ≠ 0 := by
  obtain ⟨φ, hφne, hφcontacts⟩ :=
    hexists_direction_vanishing_on Z (hcontacts Z t θ) hfew
  have hactive : ∃ i, dotProduct (Z i) φ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hdeg ⟨φ, hφne, h⟩
  obtain ⟨j, a, hjdenom, hjnew, hnorm⟩ := perturb_core p Z t θ φ hactive
  refine ⟨θ + a • φ, hnorm, j, hjnew, ?_⟩
  intro hjzero
  exact hjdenom (hφcontacts j (by simp [hcontacts, hjzero]))

/-- Weighted contact dichotomy, homogeneous form: a minimiser of a positively
weighted norm-monotone loss that strictly distinguishes `0` has at least `m`
exact contacts unless the rows are degenerate. -/
theorem weighted_contact_or_degenerate
    (p : ℕ) [Fact p.Prime] {m k : ℕ}
    (g : ℚ → ℝ) (hg : NormMonotone p g) (hg0 : ∀ r : ℚ, r ≠ 0 → g 0 < g r)
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i)
    (Z : Fin k → Param m) (t : Fin k → ℚ) (θ : Param m)
    (hmin : ∀ γ : Param m, weightedLoss g w Z t θ ≤ weightedLoss g w Z t γ) :
    m ≤ hcontactCount Z t θ ∨ HDegenerate Z := by
  by_cases hmany : m ≤ hcontactCount Z t θ
  · exact Or.inl hmany
  by_cases hdeg : HDegenerate Z
  · exact Or.inr hdeg
  exfalso
  obtain ⟨θ', hnorm_le, j, hjnew, hjold⟩ :=
    hexists_pointwise_norm_improvement p Z t θ (Nat.lt_of_not_ge hmany) hdeg
  have hterm_le : ∀ i, w i * g (hres Z t θ' i) ≤ w i * g (hres Z t θ i) := fun i ↦
    mul_le_mul_of_nonneg_left (hg _ _ (hnorm_le i)) (hw i).le
  have hjstrict : w j * g (hres Z t θ' j) < w j * g (hres Z t θ j) := by
    rw [hjnew]
    exact mul_lt_mul_of_pos_left (hg0 _ hjold) (hw j)
  have hloss_strict : weightedLoss g w Z t θ' < weightedLoss g w Z t θ := by
    apply Finset.sum_lt_sum
    · intro i _
      exact hterm_le i
    · exact ⟨j, Finset.mem_univ j, hjstrict⟩
  exact (not_lt_of_ge (hmin θ')) hloss_strict

/-- One independent-contact lifting step (homogeneous form of
`ContactTheorem.lift_independent_contacts`). -/
theorem hlift_independent_contacts
    (p : ℕ) [Fact p.Prime] {m k : ℕ}
    (Z : Fin k → Param m) (t : Fin k → ℚ) (θ : Param m)
    (A : Finset (Fin k)) (hdeg : ¬HDegenerate Z)
    (hAcard : A.card < m) (hAind : HIndependent Z A) (hAfits : HFitsOn Z t A θ) :
    ∃ j : Fin k, ∃ θ' : Param m,
      j ∉ A ∧ HIndependent Z (insert j A) ∧ HFitsOn Z t (insert j A) θ' ∧
        ∀ i, padicNorm p (hres Z t θ' i) ≤ padicNorm p (hres Z t θ i) := by
  obtain ⟨φ, hφne, hφA⟩ := hexists_direction_vanishing_on Z A hAcard
  have hactive : ∃ i, dotProduct (Z i) φ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hdeg ⟨φ, hφne, h⟩
  obtain ⟨j, a, hjdenom, hjnew, hnorm⟩ := perturb_core p Z t θ φ hactive
  have hjnotmem : j ∉ A := fun hjA ↦ hjdenom (hφA j hjA)
  have hspan_le :
      Submodule.span ℚ (Z '' (A : Set (Fin k))) ≤ LinearMap.ker (dotFunctional φ) := by
    rw [Submodule.span_le]
    rintro z ⟨i, hiA, rfl⟩
    change dotProduct φ (Z i) = 0
    rw [dotProduct_comm]
    exact hφA i hiA
  have hjnotspan : Z j ∉ Submodule.span ℚ (Z '' (A : Set (Fin k))) := by
    intro hjspan
    have hjker : dotProduct φ (Z j) = 0 := hspan_le hjspan
    rw [dotProduct_comm] at hjker
    exact hjdenom hjker
  refine ⟨j, θ + a • φ, hjnotmem, ?_, ?_, hnorm⟩
  · simpa [HIndependent] using hAind.insert hjnotspan
  · intro i hi
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hiA
    · exact hjnew
    · rw [hres_add_smul, hφA i hiA, hAfits i hiA]
      ring

/-- Iterate independent-contact lifting a prescribed number of times. -/
theorem hextend_independent_contacts_aux
    (p : ℕ) [Fact p.Prime] {m k : ℕ}
    (Z : Fin k → Param m) (t : Fin k → ℚ) (hdeg : ¬HDegenerate Z)
    (remaining : ℕ) (A : Finset (Fin k)) (θ : Param m)
    (hcard : A.card + remaining = m)
    (hAind : HIndependent Z A) (hAfits : HFitsOn Z t A θ) :
    ∃ B : Finset (Fin k), ∃ θ' : Param m,
      A ⊆ B ∧ B.card = m ∧ HIndependent Z B ∧ HFitsOn Z t B θ' ∧
        ∀ i, padicNorm p (hres Z t θ' i) ≤ padicNorm p (hres Z t θ i) := by
  induction remaining generalizing A θ with
  | zero =>
      refine ⟨A, θ, Finset.Subset.rfl, ?_, hAind, hAfits, fun _ ↦ le_rfl⟩
      omega
  | succ remaining ih =>
      have hAcard : A.card < m := by omega
      obtain ⟨j, θ₁, hjnotmem, hinsert_ind, hinsert_fits, hnorm_lift⟩ :=
        hlift_independent_contacts p Z t θ A hdeg hAcard hAind hAfits
      have hcard_insert : (insert j A).card + remaining = m := by
        rw [Finset.card_insert_of_notMem hjnotmem]
        omega
      obtain ⟨B, θ', hsubset, hBcard, hBind, hBfits, hnorm_final⟩ :=
        ih (insert j A) θ₁ hcard_insert hinsert_ind hinsert_fits
      exact ⟨B, θ', (Finset.subset_insert j A).trans hsubset, hBcard, hBind, hBfits,
        fun i ↦ (hnorm_final i).trans (hnorm_lift i)⟩

/-- Independent-contact refinement, homogeneous form: on non-degenerate rows
every `θ` is dominated (every residual norm no larger) by a `θ'` contacting `m`
linearly independent rows. -/
theorem hindependent_contact_refinement
    (p : ℕ) [Fact p.Prime] {m k : ℕ}
    (Z : Fin k → Param m) (t : Fin k → ℚ) (θ : Param m) (hdeg : ¬HDegenerate Z) :
    ∃ A : Finset (Fin k), ∃ θ' : Param m,
      A.card = m ∧ HIndependent Z A ∧ HFitsOn Z t A θ' ∧
        ∀ i, padicNorm p (hres Z t θ' i) ≤ padicNorm p (hres Z t θ i) := by
  obtain ⟨A, θ', _, hAcard, hAind, hAfits, hnorm⟩ :=
    hextend_independent_contacts_aux p Z t hdeg m ∅ θ
      (by simp) (by simp [HIndependent]) (by simp [HFitsOn])
  exact ⟨A, θ', hAcard, hAind, hAfits, hnorm⟩

/-- `m` linearly independent interpolation conditions determine `θ`. -/
theorem hunique_interpolant
    {m k : ℕ} (Z : Fin k → Param m) (t : Fin k → ℚ)
    (A : Finset (Fin k)) (hAcard : A.card = m)
    (hAind : HIndependent Z A) {θ γ : Param m}
    (hθ : HFitsOn Z t A θ) (hγ : HFitsOn Z t A γ) :
    θ = γ := by
  classical
  let v : A → Param m := fun i ↦ Z i.1
  have hlin : LinearIndependent ℚ v := by
    simpa [v, HIndependent, LinearIndepOn] using hAind
  have hcard_finrank : Fintype.card A = Module.finrank ℚ (Param m) := by
    simp [Param, hAcard]
  have hspan : Submodule.span ℚ (Set.range v) = ⊤ :=
    hlin.span_eq_top_of_card_eq_finrank' hcard_finrank
  let δ : Param m := θ - γ
  have hspan_le : Submodule.span ℚ (Set.range v) ≤ LinearMap.ker (dotFunctional δ) := by
    rw [Submodule.span_le]
    rintro z ⟨i, rfl⟩
    change dotProduct δ (Z i.1) = 0
    have hθi := hθ i.1 i.2
    have hγi := hγ i.1 i.2
    simp only [hres, sub_eq_zero] at hθi hγi
    rw [dotProduct_comm, dotProduct_sub, hθi, hγi, sub_self]
  have hker : LinearMap.ker (dotFunctional δ) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact hspan_le
  have hdot_zero : ∀ z : Param m, dotFunctional δ z = 0 := by
    intro z
    apply LinearMap.mem_ker.mp
    rw [hker]
    trivial
  have hδzero : δ = 0 := by
    funext q
    have hq := hdot_zero (fun i ↦ if i = q then 1 else 0)
    simpa [dotFunctional, dotProduct] using hq
  exact sub_eq_zero.mp hδzero

/-- Models determined by some full-size independent contact set. -/
def HCandidateModels {m k : ℕ} (Z : Fin k → Param m) (t : Fin k → ℚ) : Set (Param m) :=
  {θ | ∃ A : Finset (Fin k), A.card = m ∧ HIndependent Z A ∧ HFitsOn Z t A θ}

/-- The independent-interpolant family is finite. -/
theorem hfinite_candidateModels
    {m k : ℕ} (Z : Fin k → Param m) (t : Fin k → ℚ) :
    (HCandidateModels Z t).Finite := by
  classical
  let fiber : Finset (Fin k) → Set (Param m) := fun A ↦
    {θ | A.card = m ∧ HIndependent Z A ∧ HFitsOn Z t A θ}
  have hfiber : ∀ A, (fiber A).Finite := by
    intro A
    apply Set.Subsingleton.finite
    intro θ hθ γ hγ
    exact hunique_interpolant Z t A hθ.1 hθ.2.1 hθ.2.2 hγ.2.2
  have hunion : (⋃ A, fiber A).Finite := Set.finite_iUnion hfiber
  rw [show HCandidateModels Z t = ⋃ A, fiber A by
    ext θ
    simp [HCandidateModels, fiber]]
  exact hunion

/-- Every `θ` is dominated in weighted norm-monotone loss by a member of the
finite independent-interpolant family. Only nonnegative weights are needed. -/
theorem weighted_exists_candidate_le
    (p : ℕ) [Fact p.Prime] {m k : ℕ}
    (g : ℚ → ℝ) (hg : NormMonotone p g) (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (Z : Fin k → Param m) (t : Fin k → ℚ) (θ : Param m) (hdeg : ¬HDegenerate Z) :
    ∃ θ' ∈ HCandidateModels Z t, weightedLoss g w Z t θ' ≤ weightedLoss g w Z t θ := by
  obtain ⟨A, θ', hAcard, hAind, hAfits, hnorm⟩ :=
    hindependent_contact_refinement p Z t θ hdeg
  refine ⟨θ', ⟨A, hAcard, hAind, hAfits⟩, ?_⟩
  unfold weightedLoss
  exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hg _ _ (hnorm i)) (hw i)

/-- Weighted finite-search theorem, homogeneous form: on non-degenerate rows a
nonnegatively weighted norm-monotone loss attains its global minimum at a
member of the finite family `HCandidateModels`. -/
theorem weighted_exists_global_minimizer
    (p : ℕ) [Fact p.Prime] {m k : ℕ}
    (g : ℚ → ℝ) (hg : NormMonotone p g) (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (Z : Fin k → Param m) (t : Fin k → ℚ) (hdeg : ¬HDegenerate Z) :
    ∃ θ ∈ HCandidateModels Z t,
      ∀ γ : Param m, weightedLoss g w Z t θ ≤ weightedLoss g w Z t γ := by
  classical
  have hfin := hfinite_candidateModels Z t
  have hdom : ∀ γ : Param m, ∃ θ ∈ HCandidateModels Z t,
      weightedLoss g w Z t θ ≤ weightedLoss g w Z t γ :=
    fun γ ↦ weighted_exists_candidate_le p g hg w hw Z t γ hdeg
  have hne : (HCandidateModels Z t).Nonempty := by
    obtain ⟨θ, hθ, _⟩ := hdom 0
    exact ⟨θ, hθ⟩
  obtain ⟨θ, hθ, hθmin⟩ := Set.exists_min_image _ (weightedLoss g w Z t) hfin hne
  refine ⟨θ, hθ, fun γ ↦ ?_⟩
  obtain ⟨θ', hθ', hle⟩ := hdom γ
  exact (hθmin θ' hθ').trans hle

/-- A monotone transform of the `p`-adic magnitude is norm-monotone. -/
theorem normMonotone_of_monotone (p : ℕ) {φ : ℝ≥0 → ℝ} (hφ : Monotone φ) :
    NormMonotone p fun r ↦ φ (padicMagnitude p r) :=
  fun _ _ h ↦ hφ (padicMagnitude_le_of_padicNorm_le h)

/-! ## The affine (Chapter 2) data as a homogeneous design -/

/-- The augmented design `(1, Xᵢ)` of affine data. -/
def affineDesign {n k : ℕ} (X : Fin k → Point n) : Fin k → Param (n + 1) :=
  fun i ↦ augment (X i)

theorem dot_affineDesign {n k : ℕ} (X : Fin k → Point n) (φ : Model n) (i : Fin k) :
    dotProduct (affineDesign X i) φ = affineEval φ (X i) := by
  unfold affineDesign affineEval
  exact dotProduct_comm _ _

theorem hres_affineDesign {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (β : Model n) (i : Fin k) :
    hres (affineDesign X) y β i = residual X y β i := by
  rw [hres, dot_affineDesign, ContactTheorem.residual]

theorem hdegenerate_affineDesign_iff {n k : ℕ} (X : Fin k → Point n) :
    HDegenerate (affineDesign X) ↔ Degenerate X := by
  simp only [HDegenerate, Degenerate, dot_affineDesign]

theorem hindependent_affineDesign_iff {n k : ℕ} (X : Fin k → Point n)
    (A : Finset (Fin k)) :
    HIndependent (affineDesign X) A ↔ Independent X A :=
  Iff.rfl

theorem hfitsOn_affineDesign_iff {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (A : Finset (Fin k)) (β : Model n) :
    HFitsOn (affineDesign X) y A β ↔ FitsOn X y A β := by
  simp only [HFitsOn, FitsOn, hres_affineDesign]

theorem hcandidateModels_affineDesign {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) :
    HCandidateModels (affineDesign X) y = CandidateModels X y := by
  ext β
  simp only [HCandidateModels, CandidateModels, Set.mem_setOf_eq,
    hindependent_affineDesign_iff, hfitsOn_affineDesign_iff]

/-- Weighted additive loss on affine data: `∑ᵢ wᵢ g(residualᵢ)`. -/
noncomputable def weightedAffineLoss {n k : ℕ} (g : ℚ → ℝ) (w : Fin k → ℝ)
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) : ℝ :=
  ∑ i, w i * g (residual X y β i)

theorem weightedAffineLoss_eq {n k : ℕ} (g : ℚ → ℝ) (w : Fin k → ℝ)
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) :
    weightedAffineLoss g w X y β = weightedLoss g w (affineDesign X) y β := by
  simp only [weightedAffineLoss, weightedLoss, hres_affineDesign]

/-- Weighted finite-search theorem on affine data: the global minimum of a
nonnegatively weighted norm-monotone loss is attained on
`ContactTheorem.CandidateModels`. -/
theorem weighted_exists_global_minimizer_on_independent_contacts
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (g : ℚ → ℝ) (hg : NormMonotone p g) (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (X : Fin k → Point n) (y : Fin k → ℚ) (hdeg : ¬Degenerate X) :
    ∃ β ∈ CandidateModels X y,
      ∀ γ : Model n, weightedAffineLoss g w X y β ≤ weightedAffineLoss g w X y γ := by
  have hdeg' : ¬HDegenerate (affineDesign X) := by
    rwa [hdegenerate_affineDesign_iff]
  obtain ⟨β, hβ, hmin⟩ := weighted_exists_global_minimizer p g hg w hw (affineDesign X) y hdeg'
  refine ⟨β, by rwa [← hcandidateModels_affineDesign], fun γ ↦ ?_⟩
  rw [weightedAffineLoss_eq, weightedAffineLoss_eq]
  exact hmin γ

/-- Weighted contact dichotomy on affine data (positive weights, loss strictly
distinguishing `0`). -/
theorem weighted_affine_contact_or_degenerate
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (g : ℚ → ℝ) (hg : NormMonotone p g) (hg0 : ∀ r : ℚ, r ≠ 0 → g 0 < g r)
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i)
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n)
    (hmin : ∀ γ : Model n, weightedAffineLoss g w X y β ≤ weightedAffineLoss g w X y γ) :
    n + 1 ≤ contactCount X y β ∨ Degenerate X := by
  by_cases hmany : n + 1 ≤ contactCount X y β
  · exact Or.inl hmany
  by_cases hdeg : Degenerate X
  · exact Or.inr hdeg
  exfalso
  obtain ⟨β', hnorm_le, j, hjnew, hjold⟩ :=
    exists_pointwise_norm_improvement p X y β (Nat.lt_of_not_ge hmany) hdeg
  have hterm_le : ∀ i, w i * g (residual X y β' i) ≤ w i * g (residual X y β i) := fun i ↦
    mul_le_mul_of_nonneg_left (hg _ _ (hnorm_le i)) (hw i).le
  have hjstrict : w j * g (residual X y β' j) < w j * g (residual X y β j) := by
    rw [hjnew]
    exact mul_lt_mul_of_pos_left (hg0 _ hjold) (hw j)
  have hloss_strict : weightedAffineLoss g w X y β' < weightedAffineLoss g w X y β := by
    apply Finset.sum_lt_sum
    · intro i _
      exact hterm_le i
    · exact ⟨j, Finset.mem_univ j, hjstrict⟩
  exact (not_lt_of_ge (hmin β')) hloss_strict

/-- Weighted transformed loss `∑ᵢ wᵢ φ(‖residualᵢ‖ₚ)` with a monotone
`φ : ℝ≥0 → ℝ`, as in `AdditiveContact.transformedLoss`. -/
noncomputable def weightedTransformedLoss
    (p : ℕ) (φ : ℝ≥0 → ℝ) {n k : ℕ} (w : Fin k → ℝ)
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) : ℝ :=
  ∑ i, w i * φ (padicMagnitude p (residual X y β i))

theorem weightedTransformedLoss_eq
    (p : ℕ) (φ : ℝ≥0 → ℝ) {n k : ℕ} (w : Fin k → ℝ)
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) :
    weightedTransformedLoss p φ w X y β =
      weightedAffineLoss (fun r ↦ φ (padicMagnitude p r)) w X y β :=
  rfl

theorem weightedTransformed_exists_global_minimizer
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (φ : ℝ≥0 → ℝ) (hφ : Monotone φ) (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (X : Fin k → Point n) (y : Fin k → ℚ) (hdeg : ¬Degenerate X) :
    ∃ β ∈ CandidateModels X y,
      ∀ γ : Model n, weightedTransformedLoss p φ w X y β ≤
        weightedTransformedLoss p φ w X y γ := by
  simp only [weightedTransformedLoss_eq]
  exact weighted_exists_global_minimizer_on_independent_contacts p _
    (normMonotone_of_monotone p hφ) w hw X y hdeg

/-! ## The six-point dataset of Example `ex:monotonicity-violation` -/

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Abscissae of `P₀, …, P₅`. -/
def xs : Fin 6 → ℚ := ![15, 12, 3, 12, -15, 7]

/-- Ordinates of `P₀, …, P₅`. -/
def ys : Fin 6 → ℚ := ![12, -14, -4, 11, 12, 12]

/-- The predictors as one-dimensional points. -/
def dataX : Fin 6 → Point 1 := fun i _ ↦ xs i

/-- The per-point loss `ℓ(r) = 2^{−v₅(r)}`, with `ℓ(0) = 0`. -/
noncomputable def ell (r : ℚ) : ℝ := qPadicTerm 5 2 r

theorem ell_def (r : ℚ) :
    ell r = if r = 0 then 0 else (2 : ℝ) ^ (-padicValRat 5 r) :=
  rfl

theorem ell_zero : ell 0 = 0 := by
  simp [ell, qPadicTerm]

theorem ell_neg (r : ℚ) : ell (-r) = ell r := by
  simp [ell, qPadicTerm, padicValRat.neg]

theorem ell_pos {r : ℚ} (hr : r ≠ 0) : 0 < ell r :=
  qPadicTerm_pos (by norm_num) hr

theorem ell_normMonotone : NormMonotone 5 ell :=
  fun _ _ h ↦ qPadicTerm_le_of_padicNorm_le (by norm_num) h

theorem ell_zero_lt {r : ℚ} (hr : r ≠ 0) : ell 0 < ell r := by
  rw [ell_zero]
  exact ell_pos hr

/-- In the `ContactTheorem` convention a line is `β : Model 1` with intercept
`β 0 = b` and slope `β 1 = a`; its value at `x` is `b + a x`. -/
theorem augment_eq (x : Point 1) : augment x = ![1, x 0] := by
  ext j
  fin_cases j <;> rfl

theorem affineEval_dataX (β : Model 1) (i : Fin 6) :
    affineEval β (dataX i) = β 0 + β 1 * xs i := by
  rw [affineEval, augment_eq]
  simp [dotProduct, Fin.sum_univ_two, dataX]

/-- The line `β` passes through the data point `Pᵢ`. -/
def fits (β : Model 1) (i : Fin 6) : Prop := affineEval β (dataX i) = ys i

/-- The regularised objective `𝓛(a, b; λ) = ∑ᵢ ℓ(yᵢ − a xᵢ − b) + λ ℓ(a)`. -/
noncomputable def objective (lam : ℝ) (β : Model 1) : ℝ :=
  ∑ i, ell (ys i - affineEval β (dataX i)) + lam * ell (β 1)

/-! ### The seven-row augmented system

The thesis adjoins the row `(1, 0)` (in its `(a, b)` ordering) with response
`0` and weight `λ`. In the `(intercept, slope)` ordering of `Model 1` that row is
`![0, 1]`, and its residual is the slope `β 1`. -/

/-- The synthetic penalty row. -/
def slopeRow : Param 2 := ![0, 1]

/-- The seven augmented rows: `(1, xᵢ)` for `i < 6`, then the penalty row. -/
def designZ : Fin 7 → Param 2 :=
  Fin.snoc (α := fun _ ↦ Param 2) (fun i : Fin 6 ↦ augment (dataX i)) slopeRow

/-- Targets: `yᵢ` for the data rows, `0` for the penalty row. -/
def targetT : Fin 7 → ℚ := Fin.snoc (α := fun _ ↦ ℚ) ys 0

/-- Weights: `1` for the data rows, `λ` for the penalty row. -/
noncomputable def weightW (lam : ℝ) : Fin 7 → ℝ :=
  Fin.snoc (α := fun _ ↦ ℝ) (fun _ : Fin 6 ↦ (1 : ℝ)) lam

@[simp] theorem designZ_castSucc (i : Fin 6) :
    designZ (Fin.castSucc i) = augment (dataX i) := by
  simp [designZ]

@[simp] theorem designZ_last : designZ (Fin.last 6) = slopeRow := by
  simp only [designZ, Fin.snoc_last]

@[simp] theorem targetT_castSucc (i : Fin 6) : targetT (Fin.castSucc i) = ys i := by
  simp [targetT]

@[simp] theorem targetT_last : targetT (Fin.last 6) = 0 := by
  simp only [targetT, Fin.snoc_last]

@[simp] theorem weightW_castSucc (lam : ℝ) (i : Fin 6) :
    weightW lam (Fin.castSucc i) = 1 := by
  simp [weightW]

@[simp] theorem weightW_last (lam : ℝ) : weightW lam (Fin.last 6) = lam := by
  simp only [weightW, Fin.snoc_last]

theorem hres_castSucc (θ : Param 2) (i : Fin 6) :
    hres designZ targetT θ (Fin.castSucc i) = affineEval θ (dataX i) - ys i := by
  rw [hres, designZ_castSucc, targetT_castSucc, affineEval, dotProduct_comm]

theorem hres_last (θ : Param 2) : hres designZ targetT θ (Fin.last 6) = θ 1 := by
  rw [hres, designZ_last, targetT_last]
  simp [slopeRow, dotProduct, Fin.sum_univ_two]

/-- The regularised objective is the weighted loss of the seven-row system. -/
theorem objective_eq_weightedLoss (lam : ℝ) (β : Model 1) :
    objective lam β = weightedLoss ell (weightW lam) designZ targetT β := by
  unfold objective weightedLoss
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [hres_castSucc, hres_last, weightW_castSucc, weightW_last, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h := ell_neg (affineEval β (dataX i) - ys i)
  rwa [neg_sub] at h

theorem dot_designZ_castSucc (φ : Param 2) (i : Fin 6) :
    dotProduct (designZ (Fin.castSucc i)) φ = φ 0 + xs i * φ 1 := by
  rw [designZ_castSucc, augment_eq]
  simp [dotProduct, Fin.sum_univ_two, dataX]

/-- The augmented rows span `ℚ²` (`(1, 15)` and `(0, 1)` are independent). -/
theorem designZ_nondegenerate : ¬HDegenerate designZ := by
  rintro ⟨φ, hne, h⟩
  have h6 := h (Fin.last 6)
  rw [designZ_last] at h6
  simp [slopeRow, dotProduct, Fin.sum_univ_two] at h6
  have h0 := h (Fin.castSucc 0)
  rw [dot_designZ_castSucc] at h0
  simp only [xs, Matrix.cons_val_zero] at h0
  have hφ0 : φ 0 = 0 := by linarith
  apply hne
  funext j
  fin_cases j <;> simp [hφ0, h6]

theorem weightW_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (i : Fin 7) : 0 ≤ weightW lam i := by
  by_cases hi : i = Fin.last 6
  · subst hi
    rw [weightW_last]
    exact hlam
  · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    rw [weightW_castSucc]
    exact zero_le_one

/-- A contact at a data row of the augmented system is a fit of the line
through the corresponding data point. -/
theorem fits_of_hres_castSucc {θ : Param 2} {i : Fin 6}
    (h : hres designZ targetT θ (Fin.castSucc i) = 0) : fits θ i := by
  rw [hres_castSucc, sub_eq_zero] at h
  exact h

/-- The seven-row candidate family is finite ("there are only finitely many
lines through two of the seven augmented points"). -/
theorem finite_augmentedCandidates : (HCandidateModels designZ targetT).Finite :=
  hfinite_candidateModels designZ targetT

/-- The minimum of the regularised objective is attained within the finite
family of lines through two independent augmented contacts. -/
theorem reg_minimizer_in_finite_family (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ β ∈ HCandidateModels designZ targetT, IsGlobalMin (objective lam) β := by
  obtain ⟨θ, hθ, hmin⟩ :=
    weighted_exists_global_minimizer 5 ell ell_normMonotone (weightW lam)
      (weightW_nonneg hlam) designZ targetT designZ_nondegenerate
  refine ⟨θ, hθ, fun γ ↦ ?_⟩
  rw [objective_eq_weightedLoss, objective_eq_weightedLoss]
  exact hmin γ

/-- Thesis Lemma `lem:reg-finite-candidates`. For every `λ ≥ 0` the regularised
objective attains its minimum, and the minimum is attained by a line that
either (1) passes through two distinct data points, or (2) is horizontal
(`β 1 = 0`, so the penalty vanishes) and passes through a data point. -/
theorem reg_finite_candidates (lam : ℝ) (hlam : 0 ≤ lam) :
    (∃ β : Model 1, IsGlobalMin (objective lam) β) ∧
    ∃ β : Model 1, IsGlobalMin (objective lam) β ∧
      ((∃ i j : Fin 6, i ≠ j ∧ fits β i ∧ fits β j) ∨
        (β 1 = 0 ∧ ∃ i : Fin 6, fits β i)) := by
  obtain ⟨θ, ⟨A, hAcard, -, hAfits⟩, hglob⟩ := reg_minimizer_in_finite_family lam hlam
  refine ⟨⟨θ, hglob⟩, θ, hglob, ?_⟩
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hAcard
  have hi : hres designZ targetT θ i = 0 := hAfits i (by simp)
  have hj : hres designZ targetT θ j = 0 := hAfits j (by simp)
  by_cases hi6 : i = Fin.last 6
  · subst hi6
    obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr (Ne.symm hij)
    right
    exact ⟨by rwa [hres_last] at hi, j', fits_of_hres_castSucc hj⟩
  · obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr hi6
    by_cases hj6 : j = Fin.last 6
    · subst hj6
      right
      exact ⟨by rwa [hres_last] at hj, i', fits_of_hres_castSucc hi⟩
    · obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj6
      left
      exact ⟨i', j', fun h ↦ hij (by rw [h]),
        fits_of_hres_castSucc hi, fits_of_hres_castSucc hj⟩

/-! ### The unpenalised case `λ = 0` -/

/-- The six data predictors are non-degenerate (`(1, 15)` and `(1, 12)` are
independent). -/
theorem dataX_nondegenerate : ¬Degenerate dataX := by
  rintro ⟨φ, hne, h⟩
  have h0 := h 0
  have h1 := h 1
  rw [affineEval_dataX] at h0 h1
  simp only [xs, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hφ1 : φ 1 = 0 := by linarith
  have hφ0 : φ 0 = 0 := by linarith
  apply hne
  funext j
  fin_cases j <;> simp [hφ0, hφ1]

theorem objective_zero_eq (β : Model 1) :
    objective 0 β = weightedAffineLoss ell (fun _ ↦ 1) dataX ys β := by
  unfold objective weightedAffineLoss
  simp only [zero_mul, add_zero, one_mul, ContactTheorem.residual]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h := ell_neg (affineEval β (dataX i) - ys i)
  rwa [neg_sub] at h

/-- The `λ = 0` case of the thesis proof: the plain (unweighted) contact theorem
yields a minimiser through two distinct data points, i.e. alternative (1). -/
theorem reg_finite_candidates_zero :
    ∃ β : Model 1, IsGlobalMin (objective 0) β ∧
      ∃ i j : Fin 6, i ≠ j ∧ fits β i ∧ fits β j := by
  obtain ⟨β, ⟨A, hAcard, -, hAfits⟩, hmin⟩ :=
    weighted_exists_global_minimizer_on_independent_contacts 5 ell ell_normMonotone
      (fun _ ↦ (1 : ℝ)) (fun _ ↦ zero_le_one) dataX ys dataX_nondegenerate
  refine ⟨β, fun γ ↦ ?_, ?_⟩
  · rw [objective_zero_eq, objective_zero_eq]
    exact hmin γ
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hAcard
    refine ⟨i, j, hij, ?_, ?_⟩
    · have h := hAfits i (by simp)
      rwa [ContactTheorem.residual, sub_eq_zero] at h
    · have h := hAfits j (by simp)
      rwa [ContactTheorem.residual, sub_eq_zero] at h

/-! ### Bookkeeping remarks from the lemma statement -/

/-- `P₁` and `P₃` share the abscissa `12`: no line passes through both. -/
theorem not_fits_one_three (β : Model 1) (h1 : fits β 1) : ¬fits β 3 := by
  intro h3
  unfold fits at h1 h3
  rw [affineEval_dataX] at h1 h3
  simp only [xs, ys, Matrix.cons_val_one, Matrix.cons_val] at h1 h3
  linarith

/-- Exactly `14` of the `15` pairs of data points are non-vertical. -/
theorem nonvertical_pair_count :
    (Finset.univ.filter fun ij : Fin 6 × Fin 6 ↦ ij.1 < ij.2 ∧ xs ij.1 ≠ xs ij.2).card = 14 := by
  decide

/-- The six horizontals `y = yᵢ` are four distinct lines. -/
theorem distinct_horizontal_count : (Finset.univ.image ys).card = 4 := by
  decide

#print axioms reg_finite_candidates
#print axioms reg_finite_candidates_zero
#print axioms reg_minimizer_in_finite_family
#print axioms weighted_exists_global_minimizer
#print axioms weighted_exists_global_minimizer_on_independent_contacts
#print axioms weighted_contact_or_degenerate
#print axioms weighted_affine_contact_or_degenerate

end PhdThesisLean.RegularisedCandidates
