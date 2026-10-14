/-
  Formalisation of the large-prime optimisation lemmas from Chapter 2 of Greg
  Baker's PhD thesis.

  Thesis source: multivariate-padic-linear-regression/largeprimeopt.tex
  Thesis labels: lem:large-prime-unit-residuals, lem:large-prime-stability

  Builds on: multivariate-padic-linear-regression/algorithm.tex
  (lem:independent-contacts, rem:existence-minimiser), formalised in
  `PhdThesisLean/ContactTheorem.lean`.
-/

import PhdThesisLean.ContactTheorem

namespace PhdThesisLean.LargePrime

/-!
# Large primes: unit residuals and stability of the optimum

Thesis source: `multivariate-padic-linear-regression/largeprimeopt.tex`.
Thesis labels formalised:

* `lem:large-prime-unit-residuals` — `large_prime_unit_residuals`
  (hypothesis-free core: `exists_min_in_candidateFamily`,
  `unit_residuals_of_large_prime`).
* `lem:large-prime-stability` — `large_prime_stability` and its
  "in particular" clause `large_prime_optimal_iff_most_contacts`
  (hypothesis-free core: `optimal_iff_missCount_le_of_large_prime`,
  `loss_eq_missCount_of_large_prime`).

The thesis argument reduces to the independent-contact refinement
`lem:independent-contacts` (`ContactTheorem.independent_contact_refinement`),
which in Lean assumes non-degenerate data. The thesis lemmas explicitly allow
degenerate data via the affine dimension `d ≤ n` of the predictor points, so
this module first proves a rank-general refinement:

* `affineRank X` is `d + 1`, the dimension of the linear span of the
  augmented predictors `(1, Xᵢ)`;
* `rank_refinement` replaces any model, without increasing any residual norm
  or the loss, by a model fitting `affineRank X` affinely independent
  observations (for non-degenerate data `affineRank X = n + 1`, see
  `affineRank_eq_iff_not_degenerate`, and this is exactly
  `independent_contact_refinement`);
* `interpolant X y A` is a chosen rational interpolant of an independent set
  `A` (always solvable: `exists_fitsOn`), and `candidateFamily X y` is the
  thesis's finite family `ℋ` of chosen interpolants over all independent
  `(d+1)`-subsets, with `|ℋ| ≤ C(k, d+1)` (`card_candidateFamily_le`);
* `residual_eq_of_fitsOn`: all interpolants of a maximal independent set have
  identical residuals, so the choice of extension in `ℋ` is immaterial.

Correspondence notes:

* The bound `p₀` is explicit: `primeBound X y` is the maximum of
  `|num r| * den r` over the nonzero residuals `r` of members of `ℋ`. It
  dominates every prime dividing a numerator or denominator, so it is at
  least the thesis's `p₀`; the thesis statements are existential in `p₀`, so
  the results are at least as strong.
* `candidateFamily X y` depends only on the data, not on the prime, exactly
  as the thesis requires.
* The thesis hypotheses `n + 1 ≤ k` and `yᵢ ≠ yⱼ → Xᵢ ≠ Xⱼ` are kept in the
  statement-faithful wrappers but are not used by the proofs (the core
  statements hold without them), mirroring `ContactTheorem.contact_theorem`.
* Losses are the rational `p`-adic norms `padicNorm p` on `ℚ`, as in
  `ContactTheorem`; "optimal" means `∀ β, loss p X y h ≤ loss p X y β`.
* `missCount X y h` is the number of observations missed by `h`; for every
  prime `p > primeBound X y` and every `h ∈ ℋ`, `loss p X y h = missCount`.
  Nothing is external: every step is checked.
-/

open scoped BigOperators
open PhdThesisLean.ContactTheorem

/-! ### Affine rank of the predictor data -/

/-- The linear span of the augmented predictor vectors `(1, Xᵢ)`. -/
def augmentedSpan {n k : ℕ} (X : Fin k → Point n) : Submodule ℚ (Model n) :=
  Submodule.span ℚ (Set.range fun i ↦ augment (X i))

/-- `d + 1`, where `d` is the affine dimension of the predictor points: the
dimension of the span of the augmented predictors. -/
noncomputable def affineRank {n k : ℕ} (X : Fin k → Point n) : ℕ :=
  Module.finrank ℚ (augmentedSpan X)

theorem affineRank_le {n k : ℕ} (X : Fin k → Point n) : affineRank X ≤ n + 1 := by
  have h := Submodule.finrank_le (augmentedSpan X)
  simpa [affineRank, Model] using h

/-- The span of the augmented predictors indexed by `A`. -/
def spanOn {n k : ℕ} (X : Fin k → Point n) (A : Finset (Fin k)) : Submodule ℚ (Model n) :=
  Submodule.span ℚ ((fun i ↦ augment (X i)) '' (A : Set (Fin k)))

theorem spanOn_le {n k : ℕ} (X : Fin k → Point n) (A : Finset (Fin k)) :
    spanOn X A ≤ augmentedSpan X :=
  Submodule.span_mono (Set.image_subset_range _ _)

/-- An affinely independent index set spans a subspace of dimension its size. -/
theorem finrank_spanOn {n k : ℕ} (X : Fin k → Point n) (A : Finset (Fin k))
    (hAind : Independent X A) : Module.finrank ℚ (spanOn X A) = A.card := by
  classical
  have hcoe : (fun i ↦ augment (X i)) '' (A : Set (Fin k)) =
      ((A.image fun i ↦ augment (X i) : Finset (Model n)) : Set (Model n)) :=
    (Finset.coe_image).symm
  have hind : LinearIndepOn ℚ id
      ((A.image fun i ↦ augment (X i) : Finset (Model n)) : Set (Model n)) := by
    rw [← hcoe]
    exact hAind.id_image
  have h := finrank_span_finset_eq_card hind
  rw [spanOn, hcoe, h]
  exact Finset.card_image_of_injOn hAind.injOn

/-- Fewer than `affineRank X` independent contacts leave some augmented
predictor outside their span. -/
theorem exists_notMem_spanOn {n k : ℕ} (X : Fin k → Point n) (A : Finset (Fin k))
    (hAind : Independent X A) (hAcard : A.card < affineRank X) :
    ∃ j : Fin k, augment (X j) ∉ spanOn X A := by
  by_contra h
  push_neg at h
  have hle : augmentedSpan X ≤ spanOn X A := by
    rw [augmentedSpan, Submodule.span_le]
    rintro z ⟨j, rfl⟩
    exact h j
  have heq : spanOn X A = augmentedSpan X := le_antisymm (spanOn_le X A) hle
  have hrank : affineRank X = A.card := by
    rw [affineRank, ← heq, finrank_spanOn X A hAind]
  omega

/-- Every linear functional on parameter space is a dot product. -/
theorem exists_dot_eq {n : ℕ} (f : Model n →ₗ[ℚ] ℚ) :
    ∃ φ : Model n, ∀ z : Model n, dotProduct φ z = f z := by
  refine ⟨fun q ↦ f (fun j ↦ if q = j then 1 else 0), fun z ↦ ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ f z]
  simp only [dotProduct, smul_eq_mul]
  exact Finset.sum_congr rfl fun q _ ↦ mul_comm _ _

/-- A parameter direction annihilating the contacts in `A` but not the
observation `j`, whenever `(1, Xⱼ)` lies outside the span of `A`. -/
theorem exists_direction_separating {n k : ℕ} (X : Fin k → Point n) (A : Finset (Fin k))
    (j : Fin k) (hj : augment (X j) ∉ spanOn X A) :
    ∃ φ : Model n, (∀ i ∈ A, affineEval φ (X i) = 0) ∧ affineEval φ (X j) ≠ 0 := by
  obtain ⟨f, hfj, hker⟩ := Submodule.exists_le_ker_of_notMem hj
  obtain ⟨φ, hφ⟩ := exists_dot_eq f
  refine ⟨φ, fun i hi ↦ ?_, ?_⟩
  · have hmem : augment (X i) ∈ spanOn X A := Submodule.subset_span ⟨i, hi, rfl⟩
    have h0 := hker hmem
    rw [LinearMap.mem_ker] at h0
    simpa [affineEval, hφ] using h0
  · intro h0
    apply hfj
    rw [← hφ]
    simpa [affineEval] using h0

/-- Characterisation of non-degeneracy: the augmented predictors span the
whole parameter space exactly when `affineRank X = n + 1`. -/
theorem affineRank_eq_iff_not_degenerate {n k : ℕ} (X : Fin k → Point n) :
    affineRank X = n + 1 ↔ ¬ Degenerate X := by
  constructor
  · rintro hrank ⟨φ, hφne, hφ⟩
    have htop : augmentedSpan X = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by simpa [Model] using hrank)
    have hker : augmentedSpan X ≤ LinearMap.ker (dotLinear φ) := by
      rw [augmentedSpan, Submodule.span_le]
      rintro z ⟨i, rfl⟩
      change dotLinear φ (augment (X i)) = 0
      simpa [dotLinear, affineEval] using hφ i
    rw [htop, top_le_iff] at hker
    apply hφne
    funext q
    have hq : dotLinear φ (fun i ↦ if i = q then 1 else 0) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [hker]
      trivial
    simpa [dotLinear, dotProduct] using hq
  · intro hdeg
    by_contra hne
    have hlt : augmentedSpan X < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop ↦ hne ?_
      rw [affineRank, htop]
      simp [Model]
    obtain ⟨f, hfne, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
    obtain ⟨φ, hφ⟩ := exists_dot_eq f
    apply hdeg
    refine ⟨φ, ?_, fun i ↦ ?_⟩
    · intro h0
      apply hfne
      refine LinearMap.ext fun z ↦ ?_
      rw [← hφ, h0, zero_dotProduct, LinearMap.zero_apply]
    · have hmem : augment (X i) ∈ augmentedSpan X := Submodule.subset_span ⟨i, rfl⟩
      have h0 := hker hmem
      rw [LinearMap.mem_ker] at h0
      simpa [affineEval, hφ] using h0

/-! ### Solvability of independent interpolation conditions -/

/-- Independent interpolation conditions can be met with arbitrary prescribed
values: `evalOn X A` is surjective. -/
theorem exists_affineEval_eq {n k : ℕ} (X : Fin k → Point n) (A : Finset (Fin k))
    (hAind : Independent X A) (t : A → ℚ) :
    ∃ φ : Model n, ∀ i : A, affineEval φ (X i.1) = t i := by
  classical
  let v : A → Model n := fun i ↦ augment (X i.1)
  have hlin : LinearIndependent ℚ v := by
    simpa [v, Independent, LinearIndepOn] using hAind
  let g : (A → ℚ) →ₗ[ℚ] Model n := Fintype.linearCombination ℚ v
  have hg : LinearMap.ker g = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      (linearIndependent_iff_injective_fintypeLinearCombination.mp hlin)
  obtain ⟨h, hh⟩ := LinearMap.exists_leftInverse_of_injective g hg
  have hhv : ∀ i : A, h (augment (X i.1)) = Pi.single i 1 := by
    intro i
    have h1 : g (Pi.single i 1) = augment (X i.1) := by
      simp [g, v, Fintype.linearCombination_apply_single]
    have h2 := LinearMap.congr_fun hh (Pi.single i (1 : ℚ))
    simpa [LinearMap.comp_apply, h1] using h2
  let f : Model n →ₗ[ℚ] ℚ := (∑ i : A, t i • LinearMap.proj i) ∘ₗ h
  obtain ⟨φ, hφ⟩ := exists_dot_eq f
  refine ⟨φ, fun i ↦ ?_⟩
  rw [affineEval, hφ]
  simp [f, hhv i, Pi.single_apply]

/-- Independent contact conditions are solvable. -/
theorem exists_fitsOn {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) (A : Finset (Fin k))
    (hAind : Independent X A) : ∃ β : Model n, FitsOn X y A β := by
  obtain ⟨β, hβ⟩ := exists_affineEval_eq X A hAind (fun i ↦ y i.1)
  refine ⟨β, fun i hi ↦ ?_⟩
  have h := hβ ⟨i, hi⟩
  simp [ContactTheorem.residual, h]

open Classical in
/-- The chosen rational interpolant of the contact set `A` (zero if the
interpolation system is unsolvable, which never happens for independent `A`). -/
noncomputable def interpolant {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (A : Finset (Fin k)) : Model n :=
  if h : ∃ β : Model n, FitsOn X y A β then Classical.choose h else 0

theorem interpolant_fitsOn {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (A : Finset (Fin k)) (hAind : Independent X A) :
    FitsOn X y A (interpolant X y A) := by
  have h : ∃ β : Model n, FitsOn X y A β := exists_fitsOn X y A hAind
  rw [interpolant, dif_pos h]
  exact Classical.choose_spec h

/-! ### Residual rigidity on maximal independent contact sets -/

/-- On a maximal independent contact set, the contact predictors span the
whole augmented span. -/
theorem spanOn_eq_augmentedSpan {n k : ℕ} (X : Fin k → Point n) (A : Finset (Fin k))
    (hAcard : A.card = affineRank X) (hAind : Independent X A) :
    spanOn X A = augmentedSpan X := by
  apply Submodule.eq_of_le_of_finrank_eq (spanOn_le X A)
  rw [finrank_spanOn X A hAind, hAcard, affineRank]

/-- Two models fitting the same maximal independent contact set predict
identically at every observation. -/
theorem affineEval_eq_of_fitsOn {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (A : Finset (Fin k)) (hAcard : A.card = affineRank X) (hAind : Independent X A)
    {β γ : Model n} (hβ : FitsOn X y A β) (hγ : FitsOn X y A γ) (j : Fin k) :
    affineEval β (X j) = affineEval γ (X j) := by
  let δ : Model n := β - γ
  have hker : spanOn X A ≤ LinearMap.ker (dotLinear δ) := by
    rw [spanOn, Submodule.span_le]
    rintro z ⟨i, hi, rfl⟩
    have hβi := hβ i hi
    have hγi := hγ i hi
    simp only [ContactTheorem.residual, sub_eq_zero] at hβi hγi
    change affineEval δ (X i) = 0
    simp only [δ, affineEval, sub_dotProduct]
    change affineEval β (X i) - affineEval γ (X i) = 0
    rw [hβi, hγi, sub_self]
  have hmem : augment (X j) ∈ spanOn X A := by
    rw [spanOn_eq_augmentedSpan X A hAcard hAind]
    exact Submodule.subset_span ⟨j, rfl⟩
  have h0 := hker hmem
  rw [LinearMap.mem_ker] at h0
  change affineEval δ (X j) = 0 at h0
  simp only [δ, affineEval, sub_dotProduct] at h0
  change affineEval β (X j) - affineEval γ (X j) = 0 at h0
  exact sub_eq_zero.mp h0

/-- Residual rigidity: all interpolants of a maximal independent contact set
have the same residual vector. -/
theorem residual_eq_of_fitsOn {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (A : Finset (Fin k)) (hAcard : A.card = affineRank X) (hAind : Independent X A)
    {β γ : Model n} (hβ : FitsOn X y A β) (hγ : FitsOn X y A γ) (j : Fin k) :
    residual X y β j = residual X y γ j := by
  simp only [ContactTheorem.residual, affineEval_eq_of_fitsOn X y A hAcard hAind hβ hγ j]

/-- Consequently the loss, for every `p`, is the same for all interpolants. -/
theorem loss_eq_of_fitsOn (p : ℕ) {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (A : Finset (Fin k)) (hAcard : A.card = affineRank X) (hAind : Independent X A)
    {β γ : Model n} (hβ : FitsOn X y A β) (hγ : FitsOn X y A γ) :
    loss p X y β = loss p X y γ := by
  unfold loss
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [residual_eq_of_fitsOn X y A hAcard hAind hβ hγ j]

/-! ### Rank-general independent-contact refinement -/

/-- One lifting step for data of arbitrary affine rank: fewer than
`affineRank X` independent contacts can be extended by one more independent
contact without increasing any residual norm. -/
theorem lift_independent_contacts_rank
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n)
    (A : Finset (Fin k))
    (hAcard : A.card < affineRank X) (hAind : Independent X A)
    (hAfits : FitsOn X y A β) :
    ∃ j : Fin k, ∃ β' : Model n,
      j ∉ A ∧ Independent X (insert j A) ∧ FitsOn X y (insert j A) β' ∧
        (∀ i, padicNorm p (residual X y β' i) ≤ padicNorm p (residual X y β i)) ∧
        loss p X y β' ≤ loss p X y β := by
  obtain ⟨j₀, hj₀⟩ := exists_notMem_spanOn X A hAind hAcard
  obtain ⟨φ, hφA, hφj₀⟩ := exists_direction_separating X A j₀ hj₀
  let active : Finset (Fin k) :=
    Finset.univ.filter fun i ↦ affineEval φ (X i) ≠ 0
  have hactive : active.Nonempty := ⟨j₀, by simp [active, hφj₀]⟩
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
  refine ⟨j, β', hjnotmem, hinsert_ind, hinsert_fits, hnorm_le, ?_⟩
  unfold loss
  exact Finset.sum_le_sum fun i _ ↦ hnorm_le i

/-- Iterate rank-general lifting a prescribed number of times. -/
theorem extend_independent_contacts_rank_aux
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ)
    (remaining : ℕ) (A : Finset (Fin k)) (β : Model n)
    (hcard : A.card + remaining = affineRank X)
    (hAind : Independent X A) (hAfits : FitsOn X y A β) :
    ∃ B : Finset (Fin k), ∃ β' : Model n,
      A ⊆ B ∧ B.card = affineRank X ∧ Independent X B ∧ FitsOn X y B β' ∧
        (∀ i, padicNorm p (residual X y β' i) ≤ padicNorm p (residual X y β i)) ∧
        loss p X y β' ≤ loss p X y β := by
  induction remaining generalizing A β with
  | zero =>
      refine ⟨A, β, Finset.Subset.rfl, ?_, hAind, hAfits, fun _ ↦ le_rfl, le_rfl⟩
      omega
  | succ remaining ih =>
      have hAcard : A.card < affineRank X := by omega
      obtain ⟨j, β₁, hjnotmem, hinsert_ind, hinsert_fits, hnorm_lift, hlift⟩ :=
        lift_independent_contacts_rank p X y β A hAcard hAind hAfits
      have hcard_insert : (insert j A).card + remaining = affineRank X := by
        rw [Finset.card_insert_of_notMem hjnotmem]
        omega
      obtain ⟨B, β', hsubset, hBcard, hBind, hBfits, hnorm_final, hfinal⟩ :=
        ih (insert j A) β₁ hcard_insert hinsert_ind hinsert_fits
      refine ⟨B, β', ?_, hBcard, hBind, hBfits,
        (fun i ↦ (hnorm_final i).trans (hnorm_lift i)), hfinal.trans hlift⟩
      exact (Finset.subset_insert j A).trans hsubset

/-- Rank-general independent-contact refinement (the thesis's reduction of
`lem:independent-contacts` to the affine hull). Every model can be replaced,
without increasing any residual norm or the loss, by a model fitting
`affineRank X = d + 1` affinely independent observations. No non-degeneracy
assumption is needed. -/
theorem rank_refinement
    (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) :
    ∃ A : Finset (Fin k), ∃ β' : Model n,
      A.card = affineRank X ∧ Independent X A ∧ FitsOn X y A β' ∧
        (∀ i, padicNorm p (residual X y β' i) ≤ padicNorm p (residual X y β i)) ∧
        loss p X y β' ≤ loss p X y β := by
  obtain ⟨A, β', _, hAcard, hAind, hAfits, hnorm, hloss⟩ :=
    extend_independent_contacts_rank_aux p X y (affineRank X) ∅ β
      (by simp) (by simp [Independent]) (by simp [FitsOn])
  exact ⟨A, β', hAcard, hAind, hAfits, hnorm, hloss⟩

/-- A maximal affinely independent index set exists. -/
theorem exists_maximal_independent {n k : ℕ} (X : Fin k → Point n) :
    ∃ A : Finset (Fin k), A.card = affineRank X ∧ Independent X A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, _, hAcard, hAind, _, _, _⟩ := rank_refinement 2 X (fun _ ↦ 0) 0
  exact ⟨A, hAcard, hAind⟩

/-! ### The candidate family ℋ -/

open Classical in
/-- The thesis's candidate family `ℋ`: the chosen interpolants of all affinely
independent sets of `d + 1 = affineRank X` observations. It depends only on
the data, not on any prime. -/
noncomputable def candidateFamily {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) :
    Finset (Model n) :=
  ((Finset.univ : Finset (Finset (Fin k))).filter
    fun A ↦ A.card = affineRank X ∧ Independent X A).image (interpolant X y)

theorem mem_candidateFamily {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (h : Model n) :
    h ∈ candidateFamily X y ↔
      ∃ A : Finset (Fin k),
        A.card = affineRank X ∧ Independent X A ∧ interpolant X y A = h := by
  classical
  simp [candidateFamily, and_assoc]

theorem interpolant_mem_candidateFamily {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    {A : Finset (Fin k)} (hAcard : A.card = affineRank X) (hAind : Independent X A) :
    interpolant X y A ∈ candidateFamily X y :=
  (mem_candidateFamily X y _).mpr ⟨A, hAcard, hAind, rfl⟩

/-- Every member of `ℋ` interpolates some maximal independent contact set. -/
theorem candidateFamily_fitsOn {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (h : Model n) (hh : h ∈ candidateFamily X y) :
    ∃ A : Finset (Fin k), A.card = affineRank X ∧ Independent X A ∧ FitsOn X y A h := by
  obtain ⟨A, hAcard, hAind, rfl⟩ := (mem_candidateFamily X y h).mp hh
  exact ⟨A, hAcard, hAind, interpolant_fitsOn X y A hAind⟩

theorem candidateFamily_nonempty {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) :
    (candidateFamily X y).Nonempty := by
  obtain ⟨A, hAcard, hAind⟩ := exists_maximal_independent X
  exact ⟨_, interpolant_mem_candidateFamily X y hAcard hAind⟩

/-- `|ℋ| ≤ C(k, d + 1)`. -/
theorem card_candidateFamily_le {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) :
    (candidateFamily X y).card ≤ k.choose (affineRank X) := by
  classical
  unfold candidateFamily
  refine Finset.card_image_le.trans
    ((Finset.card_le_card
      (t := Finset.powersetCard (affineRank X) (Finset.univ : Finset (Fin k))) ?_).trans ?_)
  · intro A hA
    rw [Finset.mem_powersetCard]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    exact ⟨Finset.subset_univ A, hA.1⟩
  · rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- For non-degenerate data, `ℋ` lies inside the family `CandidateModels` of
`rem:existence-minimiser`. -/
theorem candidateFamily_subset_candidateModels {n k : ℕ} (X : Fin k → Point n)
    (y : Fin k → ℚ) (hdeg : ¬ Degenerate X) :
    ∀ h ∈ candidateFamily X y, h ∈ CandidateModels X y := by
  intro h hh
  obtain ⟨A, hAcard, hAind, hfits⟩ := candidateFamily_fitsOn X y h hh
  refine ⟨A, ?_, hAind, hfits⟩
  rw [hAcard]
  exact (affineRank_eq_iff_not_degenerate X).mpr hdeg

/-- Every model is dominated in loss by a member of `ℋ`, for every prime. -/
theorem exists_candidate_loss_le (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) (β : Model n) :
    ∃ h ∈ candidateFamily X y, loss p X y h ≤ loss p X y β := by
  obtain ⟨A, β', hAcard, hAind, hAfits, _, hloss⟩ := rank_refinement p X y β
  refine ⟨interpolant X y A, interpolant_mem_candidateFamily X y hAcard hAind, ?_⟩
  rw [loss_eq_of_fitsOn p X y A hAcard hAind (interpolant_fitsOn X y A hAind) hAfits]
  exact hloss

/-- For every prime the optimal loss is attained by a member of `ℋ`. -/
theorem exists_min_in_candidateFamily (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (X : Fin k → Point n) (y : Fin k → ℚ) :
    ∃ h ∈ candidateFamily X y, ∀ β : Model n, loss p X y h ≤ loss p X y β := by
  obtain ⟨h, hh, hmin⟩ := Finset.exists_min_image (candidateFamily X y) (loss p X y)
    (candidateFamily_nonempty X y)
  refine ⟨h, hh, fun β ↦ ?_⟩
  obtain ⟨h', hh', hle⟩ := exists_candidate_loss_le p X y β
  exact (hmin h' hh').trans hle

/-! ### The large-prime bound -/

/-- All residual values occurring across the candidate family. -/
noncomputable def residualValues {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) :
    Finset ℚ :=
  (candidateFamily X y).biUnion fun h ↦ Finset.univ.image fun i ↦ residual X y h i

/-- The explicit bound `p₀`: the largest `|num r| * den r` over the nonzero
residual values `r` of members of `ℋ` (`0` if there are none). Every prime
dividing a numerator or denominator of such an `r` is at most this bound. -/
noncomputable def primeBound {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) : ℕ :=
  ((residualValues X y).filter fun r ↦ r ≠ 0).sup fun r ↦ r.num.natAbs * r.den

theorem residual_mem_residualValues {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (h : Model n) (hh : h ∈ candidateFamily X y) (i : Fin k) :
    residual X y h i ∈ residualValues X y := by
  rw [residualValues, Finset.mem_biUnion]
  exact ⟨h, hh, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩

theorem le_primeBound {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (h : Model n) (hh : h ∈ candidateFamily X y) (i : Fin k)
    (hr : residual X y h i ≠ 0) :
    (residual X y h i).num.natAbs * (residual X y h i).den ≤ primeBound X y :=
  Finset.le_sup (f := fun r : ℚ ↦ r.num.natAbs * r.den)
    (Finset.mem_filter.mpr ⟨residual_mem_residualValues X y h hh i, hr⟩)

/-- A nonzero rational has `p`-adic norm one for every prime `p` exceeding
`|num| * den`. -/
theorem padicNorm_eq_one_of_lt (p : ℕ) [Fact p.Prime] (r : ℚ) (hr : r ≠ 0)
    (hlt : r.num.natAbs * r.den < p) : padicNorm p r = 1 := by
  have hnum : r.num ≠ 0 := Rat.num_ne_zero.mpr hr
  have hnumpos : 0 < r.num.natAbs := Int.natAbs_pos.mpr hnum
  have hden : 0 < r.den := r.den_pos
  have h1 : padicNorm p (r.num : ℚ) = 1 := by
    rw [padicNorm.int_eq_one_iff]
    intro hdvd
    have hdvd' : p ∣ r.num.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hdvd
      simpa using this
    have hle : p ≤ r.num.natAbs := Nat.le_of_dvd hnumpos hdvd'
    have : r.num.natAbs ≤ r.num.natAbs * r.den := Nat.le_mul_of_pos_right _ hden
    omega
  have h2 : padicNorm p (r.den : ℚ) = 1 := by
    rw [padicNorm.nat_eq_one_iff]
    intro hdvd
    have hle : p ≤ r.den := Nat.le_of_dvd hden hdvd
    have : r.den ≤ r.num.natAbs * r.den := Nat.le_mul_of_pos_left _ hnumpos
    omega
  calc padicNorm p r = padicNorm p ((r.num : ℚ) / (r.den : ℚ)) := by
        rw [Rat.num_div_den]
    _ = 1 := by rw [padicNorm.div, h1, h2, div_one]

/-- Unit residuals: for every prime `p > primeBound X y`, each residual of each
member of `ℋ` has `p`-adic norm `0` or `1`. -/
theorem unit_residuals_of_large_prime {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (p : ℕ) (hp : p.Prime) (hlarge : primeBound X y < p)
    (h : Model n) (hh : h ∈ candidateFamily X y) (i : Fin k) :
    padicNorm p (residual X y h i) = 0 ∨ padicNorm p (residual X y h i) = 1 := by
  haveI := Fact.mk hp
  by_cases hr : residual X y h i = 0
  · left
    rw [hr, padicNorm.zero]
  · right
    exact padicNorm_eq_one_of_lt p _ hr (lt_of_le_of_lt (le_primeBound X y h hh i hr) hlarge)

/-- Statement-faithful wrapper for thesis Lemma `lem:large-prime-unit-residuals`.

There is a bound `p₀` depending only on the dataset such that for every prime
`p > p₀` the optimal `p`-adic loss is attained by a member of the finite,
prime-independent family `ℋ = candidateFamily X y`, and every residual of every
member of `ℋ` has `p`-adic absolute value `0` or `1`. The dataset-size and
response-consistency hypotheses are retained for exact correspondence although
the proof does not use them. -/
theorem large_prime_unit_residuals {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (_hk : n + 1 ≤ k) (_hconsistent : ∀ i j, y i ≠ y j → X i ≠ X j) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ < p →
      (∃ h ∈ candidateFamily X y, ∀ β : Model n, loss p X y h ≤ loss p X y β) ∧
      ∀ h ∈ candidateFamily X y, ∀ i,
        padicNorm p (residual X y h i) = 0 ∨ padicNorm p (residual X y h i) = 1 := by
  refine ⟨primeBound X y, fun p hp hlarge ↦ ⟨?_, ?_⟩⟩
  · haveI := Fact.mk hp
    exact exists_min_in_candidateFamily p X y
  · intro h hh i
    exact unit_residuals_of_large_prime X y p hp hlarge h hh i

/-! ### Miss counts and stability -/

/-- The number of observations a model misses (fails to fit exactly). -/
def missCount {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ) (h : Model n) : ℕ :=
  (Finset.univ.filter fun i ↦ residual X y h i ≠ 0).card

theorem missCount_add_contactCount {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (h : Model n) : missCount X y h + contactCount X y h = k := by
  unfold missCount contactCount contacts
  rw [add_comm]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k))) (fun i ↦ ContactTheorem.residual X y h i = 0)
  simpa [ne_eq] using hsplit

/-- For large primes the loss of a member of `ℋ` is its miss count, a quantity
independent of the prime. -/
theorem loss_eq_missCount_of_large_prime {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (p : ℕ) (hp : p.Prime) (hlarge : primeBound X y < p)
    (h : Model n) (hh : h ∈ candidateFamily X y) :
    loss p X y h = (missCount X y h : ℚ) := by
  haveI := Fact.mk hp
  have hterm : ∀ i, padicNorm p (residual X y h i) =
      if residual X y h i ≠ 0 then (1 : ℚ) else 0 := by
    intro i
    by_cases hr : residual X y h i = 0
    · simp [hr]
    · rcases unit_residuals_of_large_prime X y p hp hlarge h hh i with h0 | h1
      · exact absurd h0 (padicNorm.nonzero hr)
      · rw [h1, if_pos hr]
  unfold loss missCount
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_boole]

/-- For a large prime, a member of `ℋ` is optimal iff it misses the fewest
observations among members of `ℋ` (equivalently, passes through the most
points). -/
theorem optimal_iff_missCount_le_of_large_prime {n k : ℕ} (X : Fin k → Point n)
    (y : Fin k → ℚ) (p : ℕ) (hp : p.Prime) (hlarge : primeBound X y < p)
    (h : Model n) (hh : h ∈ candidateFamily X y) :
    (∀ β : Model n, loss p X y h ≤ loss p X y β) ↔
      ∀ h' ∈ candidateFamily X y, missCount X y h ≤ missCount X y h' := by
  haveI := Fact.mk hp
  constructor
  · intro hopt h' hh'
    have hle := hopt h'
    rw [loss_eq_missCount_of_large_prime X y p hp hlarge h hh,
      loss_eq_missCount_of_large_prime X y p hp hlarge h' hh'] at hle
    exact_mod_cast hle
  · intro hmiss β
    obtain ⟨h', hh', hle⟩ := exists_candidate_loss_le p X y β
    refine le_trans ?_ hle
    rw [loss_eq_missCount_of_large_prime X y p hp hlarge h hh,
      loss_eq_missCount_of_large_prime X y p hp hlarge h' hh']
    exact_mod_cast hmiss h' hh'

/-- Statement-faithful wrapper for thesis Lemma `lem:large-prime-stability`.

For sufficiently large primes `q₁, q₂`, a member of `ℋ` is optimal for
`q₁`-adic regression iff it is optimal for `q₂`-adic regression: the same
members of `ℋ` attain the optimum for every sufficiently large prime. -/
theorem large_prime_stability {n k : ℕ} (X : Fin k → Point n) (y : Fin k → ℚ)
    (_hk : n + 1 ≤ k) (_hconsistent : ∀ i j, y i ≠ y j → X i ≠ X j) :
    ∃ p₀ : ℕ, ∀ q₁ q₂ : ℕ, q₁.Prime → q₂.Prime → p₀ < q₁ → p₀ < q₂ →
      ∀ h ∈ candidateFamily X y,
        ((∀ β : Model n, loss q₁ X y h ≤ loss q₁ X y β) ↔
          (∀ β : Model n, loss q₂ X y h ≤ loss q₂ X y β)) := by
  refine ⟨primeBound X y, fun q₁ q₂ hq₁ hq₂ h₁ h₂ h hh ↦ ?_⟩
  rw [optimal_iff_missCount_le_of_large_prime X y q₁ hq₁ h₁ h hh,
    optimal_iff_missCount_le_of_large_prime X y q₂ hq₂ h₂ h hh]

/-- The "in particular" clause of `lem:large-prime-stability` together with the
closing remark of the thesis section: for every sufficiently large prime, the
optimal members of `ℋ` are exactly those passing through the most observations
(missing the fewest). -/
theorem large_prime_optimal_iff_most_contacts {n k : ℕ} (X : Fin k → Point n)
    (y : Fin k → ℚ)
    (_hk : n + 1 ≤ k) (_hconsistent : ∀ i j, y i ≠ y j → X i ≠ X j) :
    ∃ p₀ : ℕ, ∀ q : ℕ, q.Prime → p₀ < q →
      ∀ h ∈ candidateFamily X y,
        ((∀ β : Model n, loss q X y h ≤ loss q X y β) ↔
          ∀ h' ∈ candidateFamily X y, missCount X y h ≤ missCount X y h') :=
  ⟨primeBound X y, fun q hq hlarge h hh ↦
    optimal_iff_missCount_le_of_large_prime X y q hq hlarge h hh⟩

end PhdThesisLean.LargePrime

#print axioms PhdThesisLean.LargePrime.rank_refinement
#print axioms PhdThesisLean.LargePrime.exists_min_in_candidateFamily
#print axioms PhdThesisLean.LargePrime.unit_residuals_of_large_prime
#print axioms PhdThesisLean.LargePrime.large_prime_unit_residuals
#print axioms PhdThesisLean.LargePrime.loss_eq_missCount_of_large_prime
#print axioms PhdThesisLean.LargePrime.optimal_iff_missCount_le_of_large_prime
#print axioms PhdThesisLean.LargePrime.large_prime_stability
#print axioms PhdThesisLean.LargePrime.large_prime_optimal_iff_most_contacts
