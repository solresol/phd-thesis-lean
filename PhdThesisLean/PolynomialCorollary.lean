/-
  Polynomial corollaries of the central contact theorem from Chapter 2 of
  Greg Baker's PhD thesis.

  Thesis source: multivariate-padic-linear-regression/polycorr.tex
  Thesis labels: poly-corollary, poly-approxy, cor:residual-simple-roots,
    cor:residual-rational-roots (and the definition "polynomial residual",
    label polynomial-residual)

  Thesis source: multivariate-padic-linear-regression/polyopt.tex
  Thesis label: thm:widespread-equioptimal
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
import PhdThesisLean.ContactTheorem

namespace PhdThesisLean.PolynomialCorollary

/-!
# Polynomial corollaries of the contact theorem

Formalises, from `multivariate-padic-linear-regression/polycorr.tex`,

* Corollary `poly-corollary` (`poly_corollary`, core form `poly_corollary_of_minimizes`):
  a polynomial of degree at most `n` minimising `∑ᵢ |P(xᵢ) - yᵢ|_p` over data with at
  least `n + 1` distinct abscissae interpolates at least `n + 1` of the data points;
* Theorem `poly-approxy` (`poly_approxy`, core form `poly_approxy_filter`): an optimal
  degree-`≤ n` `p`-adic approximant `Q` of `P` on a finite set `S` of at least `n + 1`
  points gives a residual `P - Q` with at least `n + 1` distinct rational zeros;
* Corollary `cor:residual-simple-roots` (`residual_simple_roots`): a polynomial residual
  of degree `n + 1` has no repeated roots;
* Corollary `cor:residual-rational-roots` (`residual_rational_roots`, with
  `residual_splits` and `residual_roots_map`): a polynomial residual of degree `n + 1`
  splits over `ℚ` into `n + 1` distinct linear factors, and acquires no new roots in
  any field extension;

and, from `multivariate-padic-linear-regression/polyopt.tex`,

* Theorem `thm:widespread-equioptimal` (`widespread_equioptimal`): for `n + 1` points
  with pairwise `p`-adically equidistant abscissae and an interpolant of degree exactly
  `n`, the degree-`≤ n - 1` minimisers are exactly the `n + 1` distinct candidates
  `Q_j = P - a ∏_{i ≠ j} (X - xᵢ)`, each missing exactly the point `j`, all with the
  same residual sum `|a|_p c^n`.

## Correspondence notes

* All statements are over `ℚ` with the rational `padicNorm p`, matching the thesis and
  `PhdThesisLean.ContactTheorem`. Polynomials are `Polynomial ℚ`; "degree at most `n`"
  is `natDegree ≤ n`.
* The thesis feature vector is `(xⁿ, …, x)`; here `features n x = (x, x², …, xⁿ)` (the
  coordinate order is reversed, which is immaterial: `poly`/`coeffs` give the bijection
  between `Model n` and polynomials of `natDegree ≤ n`, and
  `eval_poly : (poly β).eval x = affineEval β (features n x)`).
* `poly_corollary` keeps the thesis hypotheses `n + 1 ≤ k` and
  `xᵢ = xⱼ → yᵢ = yⱼ`, but neither is needed: `poly_corollary_of_minimizes` drops both.
  The contact theorem is used in its hypothesis-free form
  `contact_or_degenerate_of_minimizes`, so `n = 0` is covered uniformly (a nonzero
  constant polynomial has no roots, and `n + 1 ≤ #(image x)` forces `k ≥ 1`, so the
  data are non-degenerate for every `n`). No separate `n = 0` argument is needed.
* `poly_approxy_filter` is stronger than the thesis statement: it does not need
  `n < natDegree P` and locates the `n + 1` zeros inside `S`. The thesis form
  `poly_approxy` (zeros counted as `(P - Q).roots.toFinset`) uses `n < natDegree P`
  only to know `P - Q ≠ 0`.
* The residual corollaries take `IsPolynomialResidual p S n R` (the thesis definition
  "polynomial residual", `R = P - Q` with `Q` a degree-`≤ n` minimiser of
  `∑_{x ∈ S} |P(x) - Q(x)|_p`) together with `n + 1 ≤ S.card`, the standing hypothesis
  of `poly-approxy` on which they rest in the thesis (without it they are false:
  for `S = ∅` every `Q` is a minimiser).
* `widespread_equioptimal` makes explicit two hypotheses the thesis uses implicitly:
  `1 ≤ n` (approximation degree `n - 1` must be a genuine degree; for `n = 0` the
  statement is false), and `c ≠ 0` (the thesis proof derives distinctness of the `xᵢ`
  from `|xᵢ - xⱼ|_p = c ≠ 0`; for `c = 0` all abscissae coincide and the statement
  is false). The interpolant `P` is taken as given with `natDegree P = n` and
  `P(xᵢ) = yᵢ`, exactly as in the thesis statement. The conclusion lists: each
  candidate has degree `≤ n - 1`, the candidates are pairwise distinct, candidate `j`
  fits every point except `j`, all candidates have the same loss `|a|_p c^n`, and a
  degree-`≤ n - 1` polynomial is a minimiser iff it is one of the candidates.
* `exists_poly_minimizer` (a global minimiser among degree-`≤ n` polynomials exists
  whenever `n + 1` abscissae are distinct) is derived from
  `exists_global_minimizer_on_independent_contacts`; the thesis uses this tacitly in
  the "candidates tie" step.
-/

open scoped BigOperators
open Polynomial PhdThesisLean.ContactTheorem

/-- Feature map `x ↦ (x, x², …, xⁿ)`. -/
def features (n : ℕ) (x : ℚ) : Point n := fun j ↦ x ^ ((j : ℕ) + 1)

/-- Augmenting the feature vector gives the full monomial vector `(1, x, …, xⁿ)`. -/
theorem augment_features (n : ℕ) (x : ℚ) :
    augment (features n x) = fun i : Fin (n + 1) ↦ x ^ (i : ℕ) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [augment]
  · simp [augment, features]

/-- The polynomial whose coefficient on `X ^ i` is `β i`. -/
noncomputable def poly {n : ℕ} (β : Model n) : ℚ[X] :=
  ∑ i : Fin (n + 1), C (β i) * X ^ (i : ℕ)

/-- Coefficient vector of a polynomial, truncated to degree `n`. -/
def coeffs (n : ℕ) (P : ℚ[X]) : Model n := fun i ↦ P.coeff i

/-- Evaluating `poly β` at `x` is the affine model `β` applied to `features n x`. -/
theorem eval_poly {n : ℕ} (β : Model n) (x : ℚ) :
    (poly β).eval x = affineEval β (features n x) := by
  simp [poly, affineEval, augment_features, dotProduct, eval_finset_sum]

/-- The coefficients of `poly β` are the entries of `β`. -/
theorem coeff_poly {n : ℕ} (β : Model n) (i : Fin (n + 1)) :
    (poly β).coeff i = β i := by
  simp [poly, finset_sum_coeff, Fin.val_inj]

/-- `poly β` has degree at most `n`. -/
theorem natDegree_poly_le {n : ℕ} (β : Model n) : (poly β).natDegree ≤ n := by
  unfold poly
  refine natDegree_sum_le_of_forall_le _ _ fun i _ ↦ ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Fin.is_le i)

/-- Every polynomial of degree at most `n` is `poly` of its coefficient vector. -/
theorem poly_coeffs {n : ℕ} {P : ℚ[X]} (hP : P.natDegree ≤ n) :
    poly (coeffs n P) = P := by
  conv_rhs => rw [P.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hP)]
  unfold poly coeffs
  exact Fin.sum_univ_eq_sum_range (fun i ↦ C (P.coeff i) * X ^ i) (n + 1)

/-- A nonzero parameter vector gives a nonzero polynomial. -/
theorem poly_ne_zero {n : ℕ} {β : Model n} (hβ : β ≠ 0) : poly β ≠ 0 := by
  intro h
  apply hβ
  funext i
  have hi := coeff_poly β i
  rw [h, coeff_zero] at hi
  exact hi.symm

/-- Summed `p`-adic residual of a polynomial fit to data `(x i, y i)`. -/
def polyLoss (p : ℕ) {k : ℕ} (x y : Fin k → ℚ) (P : ℚ[X]) : ℚ :=
  ∑ i, padicNorm p (P.eval (x i) - y i)

/-- The polynomial objective agrees with the affine objective of `ContactTheorem`. -/
theorem polyLoss_poly (p : ℕ) {n k : ℕ} (x y : Fin k → ℚ) (β : Model n) :
    polyLoss p x y (poly β) = loss p (fun i ↦ features n (x i)) y β := by
  simp [polyLoss, loss, ContactTheorem.residual, eval_poly]

/-- Non-degeneracy: with at least `n + 1` distinct abscissae no nonzero affine function
vanishes on every feature vector, since a nonzero polynomial of degree `≤ n` has at most
`n` roots. Valid for every `n`, including `n = 0`. -/
theorem not_degenerate_of_distinct {n k : ℕ} (x : Fin k → ℚ)
    (hdistinct : n + 1 ≤ (Finset.univ.image x).card) :
    ¬ Degenerate (fun i ↦ features n (x i)) := by
  rintro ⟨φ, hφ, hvan⟩
  have hne : poly φ ≠ 0 := poly_ne_zero hφ
  have hsub : (Finset.univ.image x).val ⊆ (poly φ).roots := by
    intro a ha
    rw [Finset.mem_val, Finset.mem_image] at ha
    obtain ⟨i, _, rfl⟩ := ha
    rw [mem_roots hne, IsRoot.def, eval_poly]
    exact hvan i
  have h1 := card_le_degree_of_subset_roots hsub
  have h2 := natDegree_poly_le φ
  omega

/-- Core form of thesis Corollary `poly-corollary`, without the unused hypotheses
`n + 1 ≤ k` and `xᵢ = xⱼ → yᵢ = yⱼ`. -/
theorem poly_corollary_of_minimizes (p : ℕ) [Fact p.Prime] {n k : ℕ}
    (x y : Fin k → ℚ) (hdistinct : n + 1 ≤ (Finset.univ.image x).card)
    (P : ℚ[X]) (hP : P.natDegree ≤ n)
    (hmin : ∀ Q : ℚ[X], Q.natDegree ≤ n → polyLoss p x y P ≤ polyLoss p x y Q) :
    n + 1 ≤ (Finset.univ.filter fun i ↦ P.eval (x i) = y i).card := by
  obtain ⟨β, rfl⟩ : ∃ β : Model n, poly β = P := ⟨coeffs n P, poly_coeffs hP⟩
  have hmin' : ∀ γ : Model n, loss p (fun i ↦ features n (x i)) y β ≤
      loss p (fun i ↦ features n (x i)) y γ := by
    intro γ
    rw [← polyLoss_poly, ← polyLoss_poly]
    exact hmin _ (natDegree_poly_le γ)
  rcases contact_or_degenerate_of_minimizes p _ y β hmin' with h | h
  · have hc : contacts (fun i ↦ features n (x i)) y β =
        Finset.univ.filter fun i ↦ (poly β).eval (x i) = y i := by
      ext i
      simp [contacts, ContactTheorem.residual, eval_poly, sub_eq_zero]
    unfold contactCount at h
    rwa [hc] at h
  · exact absurd h (not_degenerate_of_distinct x hdistinct)


/-- Statement-faithful wrapper for thesis Corollary `poly-corollary`. -/
theorem poly_corollary (p n k : ℕ) [Fact p.Prime] (_hk : n + 1 ≤ k)
    (x y : Fin k → ℚ) (hdistinct : n + 1 ≤ (Finset.univ.image x).card)
    (_hfun : ∀ i j, x i = x j → y i = y j)
    (P : ℚ[X]) (hP : P.natDegree ≤ n)
    (hmin : ∀ Q : ℚ[X], Q.natDegree ≤ n → polyLoss p x y P ≤ polyLoss p x y Q) :
    n + 1 ≤ (Finset.univ.filter fun i ↦ P.eval (x i) = y i).card :=
  poly_corollary_of_minimizes p x y hdistinct P hP hmin

/-- Summed `p`-adic distance between `P` and `Q` over the evaluation set `S`. -/
noncomputable def approxLoss (p : ℕ) (S : Finset ℚ) (P Q : ℚ[X]) : ℚ :=
  ∑ a ∈ S, padicNorm p ((P - Q).eval a)

/-- Enumerating `S` injectively turns the approximation objective into `polyLoss`. -/
theorem approxLoss_eq_polyLoss (p : ℕ) {S : Finset ℚ} {k : ℕ} {x : Fin k → ℚ}
    (hinj : Function.Injective x) (himage : Finset.univ.image x = S) (P Q : ℚ[X]) :
    approxLoss p S P Q = polyLoss p x (fun i ↦ P.eval (x i)) Q := by
  unfold approxLoss polyLoss
  rw [← himage, Finset.sum_image fun _ _ _ _ h ↦ hinj h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eval_sub, ← padicNorm.neg, neg_sub]

/-- Core form of thesis Theorem `poly-approxy`: the optimal approximant agrees with `P`
at no fewer than `n + 1` points of `S`. Does not need `n < natDegree P`. -/
theorem poly_approxy_filter (p : ℕ) [Fact p.Prime] {n : ℕ} (P : ℚ[X])
    (S : Finset ℚ) (hS : n + 1 ≤ S.card) (Q : ℚ[X]) (hQ : Q.natDegree ≤ n)
    (hmin : ∀ Q' : ℚ[X], Q'.natDegree ≤ n → approxLoss p S P Q ≤ approxLoss p S P Q') :
    n + 1 ≤ (S.filter fun a ↦ (P - Q).eval a = 0).card := by
  have hinj : Function.Injective (S.orderEmbOfFin rfl) := (S.orderEmbOfFin rfl).injective
  have himage : Finset.univ.image (S.orderEmbOfFin rfl) = S :=
    Finset.image_orderEmbOfFin_univ S rfl
  have hdistinct : n + 1 ≤ (Finset.univ.image (S.orderEmbOfFin rfl)).card := by
    rw [himage]; exact hS
  have hmin' : ∀ Q' : ℚ[X], Q'.natDegree ≤ n →
      polyLoss p (S.orderEmbOfFin rfl) (fun i ↦ P.eval (S.orderEmbOfFin rfl i)) Q ≤
        polyLoss p (S.orderEmbOfFin rfl) (fun i ↦ P.eval (S.orderEmbOfFin rfl i)) Q' := by
    intro Q' hQ'
    rw [← approxLoss_eq_polyLoss p hinj himage, ← approxLoss_eq_polyLoss p hinj himage]
    exact hmin Q' hQ'
  have h := poly_corollary_of_minimizes p _ _ hdistinct Q hQ hmin'
  calc n + 1 ≤ _ := h
    _ = ((Finset.univ.filter fun i ↦
          Q.eval (S.orderEmbOfFin rfl i) = P.eval (S.orderEmbOfFin rfl i)).image
            (S.orderEmbOfFin rfl)).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (S.filter fun a ↦ (P - Q).eval a = 0).card := by
        apply Finset.card_le_card
        intro a ha
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        obtain ⟨i, hi, rfl⟩ := ha
        simp only [Finset.mem_filter, eval_sub]
        exact ⟨S.orderEmbOfFin_mem rfl i, by rw [hi, sub_self]⟩

/-- Distinct zeros located in `S` are distinct roots. -/
theorem card_roots_toFinset_ge {n : ℕ} {R : ℚ[X]} (hR : R ≠ 0) {S : Finset ℚ}
    (h : n + 1 ≤ (S.filter fun a ↦ R.eval a = 0).card) :
    n + 1 ≤ R.roots.toFinset.card := by
  refine h.trans (Finset.card_le_card ?_)
  intro a ha
  rw [Finset.mem_filter] at ha
  rw [Multiset.mem_toFinset, mem_roots hR, IsRoot.def]
  exact ha.2

/-- Thesis Theorem `poly-approxy`. -/
theorem poly_approxy (p : ℕ) [Fact p.Prime] {n : ℕ} (P : ℚ[X]) (hP : n < P.natDegree)
    (S : Finset ℚ) (hS : n + 1 ≤ S.card) (Q : ℚ[X]) (hQ : Q.natDegree ≤ n)
    (hmin : ∀ Q' : ℚ[X], Q'.natDegree ≤ n → approxLoss p S P Q ≤ approxLoss p S P Q') :
    n + 1 ≤ (P - Q).roots.toFinset.card := by
  have hne : P - Q ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hP
    omega
  exact card_roots_toFinset_ge hne (poly_approxy_filter p P S hS Q hQ hmin)

/-- `R` is a polynomial residual of `P` for approximation degree `n` on `S`. -/
def IsPolynomialResidual (p : ℕ) (S : Finset ℚ) (n : ℕ) (R : ℚ[X]) : Prop :=
  ∃ P Q : ℚ[X], Q.natDegree ≤ n ∧
    (∀ Q' : ℚ[X], Q'.natDegree ≤ n → approxLoss p S P Q ≤ approxLoss p S P Q') ∧ R = P - Q

/-- A polynomial residual of degree `n + 1` has exactly `n + 1` roots, all distinct. -/
theorem residual_card_roots (p : ℕ) [Fact p.Prime] {S : Finset ℚ} {n : ℕ} {R : ℚ[X]}
    (hS : n + 1 ≤ S.card) (hR : IsPolynomialResidual p S n R) (hdeg : R.natDegree = n + 1) :
    Multiset.card R.roots = n + 1 ∧ R.roots.toFinset.card = n + 1 := by
  obtain ⟨P, Q, hQ, hmin, rfl⟩ := hR
  have hne : P - Q ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have h1 : n + 1 ≤ (P - Q).roots.toFinset.card :=
    card_roots_toFinset_ge hne (poly_approxy_filter p P S hS Q hQ hmin)
  have h2 : (P - Q).roots.toFinset.card ≤ Multiset.card (P - Q).roots :=
    Multiset.toFinset_card_le _
  have h3 := card_roots' (P - Q)
  rw [hdeg] at h3
  omega

/-- Thesis Corollary `cor:residual-simple-roots`. -/
theorem residual_simple_roots (p : ℕ) [Fact p.Prime] {S : Finset ℚ} {n : ℕ} {R : ℚ[X]}
    (hS : n + 1 ≤ S.card) (hR : IsPolynomialResidual p S n R) (hdeg : R.natDegree = n + 1) :
    R.roots.Nodup := by
  obtain ⟨h1, h2⟩ := residual_card_roots p hS hR hdeg
  exact Multiset.toFinset_card_eq_card_iff_nodup.mp (h2.trans h1.symm)

/-- A polynomial residual of degree `n + 1` splits over `ℚ`. -/
theorem residual_splits (p : ℕ) [Fact p.Prime] {S : Finset ℚ} {n : ℕ} {R : ℚ[X]}
    (hS : n + 1 ≤ S.card) (hR : IsPolynomialResidual p S n R) (hdeg : R.natDegree = n + 1) :
    R.Splits := by
  obtain ⟨h1, _⟩ := residual_card_roots p hS hR hdeg
  exact splits_iff_card_roots.mpr (h1.trans hdeg.symm)

/-- Thesis Corollary `cor:residual-rational-roots`. -/
theorem residual_rational_roots (p : ℕ) [Fact p.Prime] {S : Finset ℚ} {n : ℕ} {R : ℚ[X]}
    (hS : n + 1 ≤ S.card) (hR : IsPolynomialResidual p S n R) (hdeg : R.natDegree = n + 1) :
    R.roots.toFinset.card = n + 1 ∧
      R = C R.leadingCoeff * ∏ r ∈ R.roots.toFinset, (X - C r) := by
  obtain ⟨h1, h2⟩ := residual_card_roots p hS hR hdeg
  have hnodup : R.roots.Nodup := Multiset.toFinset_card_eq_card_iff_nodup.mp (h2.trans h1.symm)
  refine ⟨h2, ?_⟩
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C (h1.trans hdeg.symm)
  calc R = C R.leadingCoeff * (R.roots.map fun a ↦ X - C a).prod := hprod.symm
    _ = C R.leadingCoeff * ∏ r ∈ R.roots.toFinset, (X - C r) := by
        rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
          Multiset.dedup_eq_self.mpr hnodup]

/-- A polynomial residual of degree `n + 1` acquires no new roots in any field extension
("no irrational roots"). -/
theorem residual_roots_map (p : ℕ) [Fact p.Prime] {S : Finset ℚ} {n : ℕ} {R : ℚ[X]}
    (hS : n + 1 ≤ S.card) (hR : IsPolynomialResidual p S n R) (hdeg : R.natDegree = n + 1)
    {K : Type*} [Field K] (f : ℚ →+* K) :
    (R.map f).roots = R.roots.map f := by
  obtain ⟨h1, _⟩ := residual_card_roots p hS hR hdeg
  exact (roots_map_of_injective_of_card_eq_natDegree f.injective (h1.trans hdeg.symm)).symm

/-! ### Existence of a polynomial minimiser -/

/-- A global minimiser among polynomials of degree at most `n` exists whenever at least
`n + 1` abscissae are distinct (via the finite candidate search of `ContactTheorem`). -/
theorem exists_poly_minimizer (p : ℕ) [Fact p.Prime] {n k : ℕ} (x y : Fin k → ℚ)
    (hdistinct : n + 1 ≤ (Finset.univ.image x).card) :
    ∃ Q : ℚ[X], Q.natDegree ≤ n ∧
      ∀ R : ℚ[X], R.natDegree ≤ n → polyLoss p x y Q ≤ polyLoss p x y R := by
  obtain ⟨β, _, hβ⟩ := exists_global_minimizer_on_independent_contacts p
    (fun i ↦ features n (x i)) y (not_degenerate_of_distinct x hdistinct)
  refine ⟨poly β, natDegree_poly_le β, fun R hR ↦ ?_⟩
  obtain ⟨γ, rfl⟩ : ∃ γ : Model n, poly γ = R := ⟨coeffs n R, poly_coeffs hR⟩
  rw [polyLoss_poly, polyLoss_poly]
  exact hβ γ

/-! ### Equidistant abscissae: `thm:widespread-equioptimal` -/

/-- The monic polynomial `R_j = ∏_{i ≠ j} (X - x i)`. -/
noncomputable def omitProd {m : ℕ} (x : Fin m → ℚ) (j : Fin m) : ℚ[X] :=
  ∏ i ∈ Finset.univ.erase j, (X - C (x i))

/-- The thesis candidate `Q_j = P - a R_j` with `a` the leading coefficient of `P`. -/
noncomputable def candidate {m : ℕ} (x : Fin m → ℚ) (P : ℚ[X]) (j : Fin m) : ℚ[X] :=
  P - C P.leadingCoeff * omitProd x j

/-- `R_j` is monic. -/
theorem monic_omitProd {m : ℕ} (x : Fin m → ℚ) (j : Fin m) : (omitProd x j).Monic :=
  monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)

/-- `R_j` has degree `n` on `n + 1` abscissae. -/
theorem natDegree_omitProd {n : ℕ} (x : Fin (n + 1) → ℚ) (j : Fin (n + 1)) :
    (omitProd x j).natDegree = n := by
  unfold omitProd
  rw [natDegree_prod_of_monic (h := fun i _ ↦ monic_X_sub_C (x i))]
  simp [Finset.card_erase_of_mem]

/-- Evaluation of `R_j`. -/
theorem eval_omitProd {m : ℕ} (x : Fin m → ℚ) (j : Fin m) (t : ℚ) :
    (omitProd x j).eval t = ∏ i ∈ Finset.univ.erase j, (t - x i) := by
  simp [omitProd, eval_prod]

/-- `R_j` vanishes at every abscissa other than `x j`. -/
theorem eval_omitProd_of_ne {m : ℕ} (x : Fin m → ℚ) {i j : Fin m} (hij : i ≠ j) :
    (omitProd x j).eval (x i) = 0 := by
  rw [eval_omitProd]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩) (sub_self _)

/-- `R_j` does not vanish at `x j` when the abscissae are distinct. -/
theorem eval_omitProd_self_ne_zero {m : ℕ} {x : Fin m → ℚ} (hx : Function.Injective x)
    (j : Fin m) : (omitProd x j).eval (x j) ≠ 0 := by
  rw [eval_omitProd]
  refine Finset.prod_ne_zero_iff.mpr fun i hi ↦ ?_
  rw [Finset.mem_erase] at hi
  exact sub_ne_zero.mpr fun h ↦ hi.1 (hx h).symm

/-- `padicNorm` is multiplicative over finite products. -/
theorem padicNorm_prod (p : ℕ) [Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    padicNorm p (∏ i ∈ s, f i) = ∏ i ∈ s, padicNorm p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, padicNorm.mul, ih]

/-- Under equidistance, `|R_j(x_j)|_p = c ^ n`. -/
theorem padicNorm_eval_omitProd_self (p : ℕ) [Fact p.Prime] {n : ℕ} {x : Fin (n + 1) → ℚ}
    {c : ℚ} (hequi : ∀ i j, i ≠ j → padicNorm p (x i - x j) = c) (j : Fin (n + 1)) :
    padicNorm p ((omitProd x j).eval (x j)) = c ^ n := by
  rw [eval_omitProd, padicNorm_prod,
    Finset.prod_congr rfl fun i hi ↦ hequi j i (Finset.ne_of_mem_erase hi).symm]
  simp [Finset.prod_const, Finset.card_erase_of_mem]

/-- The candidate `Q_j` has degree at most `n - 1`: the leading terms cancel. -/
theorem natDegree_candidate_le {n : ℕ} (x : Fin (n + 1) → ℚ) {P : ℚ[X]}
    (hP : P.natDegree = n) (j : Fin (n + 1)) :
    (candidate x P j).natDegree ≤ n - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  unfold candidate
  rw [coeff_sub, coeff_C_mul]
  rcases Nat.lt_or_ge n N with h | h
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by rw [natDegree_omitProd]; exact h)]
    ring
  · have hNn : N = n := by omega
    subst hNn
    have h1 : P.coeff N = P.leadingCoeff := by rw [← hP]; exact coeff_natDegree
    have h2 : (omitProd x j).coeff N = 1 := by
      have := (monic_omitProd x j).coeff_natDegree
      rwa [natDegree_omitProd] at this
    rw [h1, h2]
    ring

/-- Evaluation of the candidate `Q_j`. -/
theorem eval_candidate {m : ℕ} (x : Fin m → ℚ) (P : ℚ[X]) (j i : Fin m) :
    (candidate x P j).eval (x i) =
      P.eval (x i) - P.leadingCoeff * (omitProd x j).eval (x i) := by
  simp [candidate]

/-- `Q_j` fits the data point `i` exactly when `i ≠ j`. -/
theorem eval_candidate_iff {m : ℕ} {x : Fin m → ℚ} (hx : Function.Injective x) {P : ℚ[X]}
    (ha : P.leadingCoeff ≠ 0) (y : Fin m → ℚ) (hPint : ∀ i, P.eval (x i) = y i)
    (j i : Fin m) : (candidate x P j).eval (x i) = y i ↔ i ≠ j := by
  rw [eval_candidate, hPint]
  constructor
  · intro h hij
    subst hij
    have hne := eval_omitProd_self_ne_zero hx i
    have h' : P.leadingCoeff * (omitProd x i).eval (x i) = 0 := by linarith
    exact mul_ne_zero ha hne h'
  · intro hij
    rw [eval_omitProd_of_ne x hij, mul_zero, sub_zero]

/-- Every candidate has residual sum `|a|_p c ^ n`. -/
theorem polyLoss_candidate (p : ℕ) [Fact p.Prime] {n : ℕ} {x : Fin (n + 1) → ℚ} {c : ℚ}
    (hequi : ∀ i j, i ≠ j → padicNorm p (x i - x j) = c) (y : Fin (n + 1) → ℚ) {P : ℚ[X]}
    (hPint : ∀ i, P.eval (x i) = y i) (j : Fin (n + 1)) :
    polyLoss p x y (candidate x P j) = padicNorm p P.leadingCoeff * c ^ n := by
  unfold polyLoss
  rw [Finset.sum_eq_single j]
  · rw [eval_candidate, hPint, sub_sub_cancel_left, padicNorm.neg, padicNorm.mul,
      padicNorm_eval_omitProd_self p hequi]
  · intro i _ hij
    rw [eval_candidate, hPint, sub_sub_cancel_left, eval_omitProd_of_ne x hij, mul_zero,
      neg_zero, padicNorm.zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The `n + 1` candidates are pairwise distinct. -/
theorem candidate_injective {m : ℕ} {x : Fin m → ℚ} (hx : Function.Injective x) {P : ℚ[X]}
    (ha : P.leadingCoeff ≠ 0) : Function.Injective (candidate x P) := by
  intro j k hjk
  by_contra hne
  have h := congrArg (fun Q : ℚ[X] ↦ Q.eval (x j)) hjk
  simp only [eval_candidate] at h
  rw [eval_omitProd_of_ne x hne] at h
  have hne' := eval_omitProd_self_ne_zero hx j
  have h' : P.leadingCoeff * (omitProd x j).eval (x j) = 0 := by linarith
  exact mul_ne_zero ha hne' h'

/-- Exhaustiveness: every degree-`≤ n - 1` minimiser is one of the candidates. -/
theorem eq_candidate_of_minimizes (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n)
    {x : Fin (n + 1) → ℚ} (hx : Function.Injective x) (y : Fin (n + 1) → ℚ)
    {P : ℚ[X]} (hPdeg : P.natDegree = n) (hPint : ∀ i, P.eval (x i) = y i)
    {Q : ℚ[X]} (hQ : Q.natDegree ≤ n - 1)
    (hmin : ∀ R : ℚ[X], R.natDegree ≤ n - 1 → polyLoss p x y Q ≤ polyLoss p x y R) :
    ∃ j, Q = candidate x P j := by
  classical
  have hcard : (Finset.univ.image x).card = n + 1 := by
    rw [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
  have hdistinct : n - 1 + 1 ≤ (Finset.univ.image x).card := by omega
  have hagree := poly_corollary_of_minimizes p x y hdistinct Q hQ hmin
  set A := Finset.univ.filter fun i ↦ Q.eval (x i) = y i with hA
  have hAne : A ≠ Finset.univ := by
    intro hAu
    have hall : ∀ i, Q.eval (x i) = y i := by
      intro i
      have hi : i ∈ A := hAu ▸ Finset.mem_univ i
      simpa [A] using hi
    have hPQ : P - Q = 0 := by
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hx
      · intro i
        rw [eval_sub, hPint, hall, sub_self]
      · rw [Fintype.card_fin]
        calc (P - Q).natDegree ≤ max P.natDegree Q.natDegree := natDegree_sub_le _ _
          _ < n + 1 := by omega
    rw [sub_eq_zero] at hPQ
    rw [hPQ] at hPdeg
    omega
  have hAlt : A.card < Finset.univ.card :=
    Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hAne)
  rw [Finset.card_univ, Fintype.card_fin] at hAlt
  have hcompl : (Finset.univ \ A).card = 1 := by
    rw [Finset.card_univ_diff, Fintype.card_fin]
    omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcompl
  have hAeq : A = Finset.univ.erase j := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hi hij
      subst hij
      have hmem : i ∈ Finset.univ \ A := by
        rw [hj]
        exact Finset.mem_singleton_self i
      exact (Finset.mem_sdiff.mp hmem).2 hi
    · intro hij
      by_contra hi
      have hmem : i ∈ Finset.univ \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩
      rw [hj, Finset.mem_singleton] at hmem
      exact hij hmem
  refine ⟨j, ?_⟩
  have hD : Q - candidate x P j = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ ((Finset.univ.erase j).image x)
    · intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨i, hi, rfl⟩ := ht
      have hiA : i ∈ A := hAeq ▸ hi
      have hQi : Q.eval (x i) = y i := by simpa [A] using hiA
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      rw [eval_sub, eval_candidate, hQi, hPint, eval_omitProd_of_ne x hij, mul_zero, sub_zero,
        sub_self]
    · rw [Finset.card_image_of_injective _ hx, Finset.card_erase_of_mem (Finset.mem_univ j),
        Finset.card_univ, Fintype.card_fin]
      calc (Q - candidate x P j).natDegree
          ≤ max Q.natDegree (candidate x P j).natDegree := natDegree_sub_le _ _
        _ ≤ n - 1 := max_le hQ (natDegree_candidate_le x hPdeg j)
        _ < n + 1 - 1 := by omega
  exact sub_eq_zero.mp hD

/-- Thesis Theorem `thm:widespread-equioptimal`. -/
theorem widespread_equioptimal (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ℚ) {c : ℚ} (hc : c ≠ 0)
    (hequi : ∀ i j, i ≠ j → padicNorm p (x i - x j) = c)
    (P : ℚ[X]) (hPdeg : P.natDegree = n) (hPint : ∀ i, P.eval (x i) = y i) :
    (∀ j, (candidate x P j).natDegree ≤ n - 1) ∧
    Function.Injective (candidate x P) ∧
    (∀ j i, (candidate x P j).eval (x i) = y i ↔ i ≠ j) ∧
    (∀ j, polyLoss p x y (candidate x P j) = padicNorm p P.leadingCoeff * c ^ n) ∧
    (∀ Q : ℚ[X], Q.natDegree ≤ n - 1 →
      ((∀ R : ℚ[X], R.natDegree ≤ n - 1 → polyLoss p x y Q ≤ polyLoss p x y R) ↔
        ∃ j, Q = candidate x P j)) := by
  have hx : Function.Injective x := by
    intro i j hij
    by_contra hne
    have h := hequi i j hne
    rw [hij, sub_self, padicNorm.zero] at h
    exact hc h.symm
  have ha : P.leadingCoeff ≠ 0 := by
    rw [leadingCoeff_ne_zero]
    intro h
    rw [h, natDegree_zero] at hPdeg
    omega
  refine ⟨fun j ↦ natDegree_candidate_le x hPdeg j, candidate_injective hx ha,
    fun j i ↦ eval_candidate_iff hx ha y hPint j i,
    fun j ↦ polyLoss_candidate p hequi y hPint j, ?_⟩
  intro Q hQ
  constructor
  · intro hmin
    exact eq_candidate_of_minimizes p hn hx y hPdeg hPint hQ hmin
  · rintro ⟨j, rfl⟩ R hR
    have hcard : (Finset.univ.image x).card = n + 1 := by
      rw [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
    have hdistinct : n - 1 + 1 ≤ (Finset.univ.image x).card := by omega
    obtain ⟨Q₀, hQ₀, hmin₀⟩ := exists_poly_minimizer p x y hdistinct
    obtain ⟨j₀, hj₀⟩ := eq_candidate_of_minimizes p hn hx y hPdeg hPint hQ₀ hmin₀
    calc polyLoss p x y (candidate x P j)
        = padicNorm p P.leadingCoeff * c ^ n := polyLoss_candidate p hequi y hPint j
      _ = polyLoss p x y (candidate x P j₀) := (polyLoss_candidate p hequi y hPint j₀).symm
      _ = polyLoss p x y Q₀ := by rw [hj₀]
      _ ≤ polyLoss p x y R := hmin₀ R hR

#print axioms poly_corollary
#print axioms poly_approxy
#print axioms residual_simple_roots
#print axioms residual_rational_roots
#print axioms widespread_equioptimal

end PhdThesisLean.PolynomialCorollary
