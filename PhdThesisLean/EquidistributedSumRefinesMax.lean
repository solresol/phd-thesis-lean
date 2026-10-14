import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Fintype.BigOperators
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

namespace PhdThesisLean.EquidistributedSumRefinesMax

open scoped BigOperators
open Finset

/-!
# Equidistributed designs: summed loss refines max loss

This module formalises thesis Theorem `thm:equidistributed-sum-refines-max`
from `complexity-regimes/body.tex` (section
`sec:equidistributed-sum-max`, together with the definitions of `L_1`,
`L_∞` and the residual `r_i(a,b) = y_i - a - b · x_i` immediately above it).

## Setting

Observations are indexed by an arbitrary nonempty finite type `ι`
(the thesis uses `i = 1, …, N`; here `N = Fintype.card ι`).  Predictors are
`x : ι → Fin d → ℤ_[p]` (thesis: `x_i ∈ ℤ_p^d`), responses are
`y : ι → ℚ_[p]`, and an affine model consists of an intercept `a : ℚ_[p]`
and slopes `b : Fin d → ℚ_[p]`.  The intercept is part of the model by
construction, which is the thesis's "the model includes an intercept term".

* `residual x y a b i = y i - a - ∑ j, b j * x i j`,
* `L1 x y a b = ∑ i, ‖residual x y a b i‖`,
* `Linf x y a b = max_i ‖residual x y a b i‖` (a `Finset.sup'` over `univ`),
* `Equidistributed x`: every residue pattern `v : Fin d → ZMod p` is the
  reduction `reduce x i` of exactly the same number `M` of indices
  (`card_eq_pow_mul` derives `N = p ^ d * M`),
* `IsGlobalMin f z := ∀ w, f z ≤ f w` (same shape as in
  `PhdThesisLean.AllDifferent`).

## Headline statements

* `equidistributed_sum_refines_max` is the thesis statement verbatim: under
  equidistribution and the no-exact-fit hypothesis, every global minimiser
  of `L1` is a global minimiser of `Linf`.
* `isGlobalMin_Linf_of_isGlobalMin_L1` is the stronger statement without the
  no-exact-fit hypothesis; the thesis theorem is a corollary.  (If an exact
  fit exists, an `L1`-minimiser has `L1 = 0`, hence `Linf = 0`, and is
  trivially `Linf`-optimal; this is the first case of the proof.)  The
  no-exact-fit hypothesis of the headline is therefore unused and is named
  `_hnofit`.

## Correspondence notes (proof route differs, conclusion identical)

The thesis proof (a) establishes that a max-optimal pair exists by a
compactness argument on nested cosets of `p^t ℤ_p^(d+1)`, and (b) averages
the summed loss over the intercept shifts `a* + p^{T*} u`, `u ∈ ℤ_p`, with
respect to normalised Haar measure, obtaining the average `(p/(p+1)) N p^{-T*}`.

The Lean proof is purely finite and uses neither ingredient.  Suppose `(a,b)`
minimises `L1` but some `(a',b')` has `Linf a' b' < Linf a b`.

* Counting (`card_affZ_zero_mul_le`, `card_filter_norm_affineEval_eq`):
  the difference `h(x) = (a-a') + (b-b')·x` of the two fitted functions has
  coefficient sup-norm `σ`; dividing by a coefficient of norm `σ` and reducing
  mod `p` gives a nonzero affine function on `(ZMod p)^d`, which vanishes on
  at most `p^(d-1)` points (its zero set is a fibre of a surjective affine
  map, and all `p` fibres are translates of each other).  By
  equidistribution, `‖h(x_i)‖ = σ` for at least `(1 - 1/p) N` indices, and
  for those the ultrametric inequality forces `‖r_i(a,b)‖ = σ ≥ Linf a b`.
  Hence `L1 a b ≥ (1 - 1/p) N σ`.
* Competitor (`sum_norm_sub_range_le`): instead of a Haar average over
  `ℤ_p`, average over the `p` intercept shifts `a' + c' u`, `u = 0, …, p-1`,
  where `c'` is a residual of `(a',b')` of maximal norm `ρ'`.  For each `i`
  exactly one `u` makes `‖r_i(a',b') - c' u‖ ≤ ρ'/p` and the others give
  `≤ ρ'`, so `∑_u L1 (a' + c' u) b' ≤ ρ' N (p - 1 + 1/p)`.
* Since `L1 a b ≤ L1 (a' + c' u) b'` for every `u` (minimality) and
  `p ρ' ≤ Linf a b ≤ σ` (norm values are powers of `p`), we get
  `p (p-1) ≤ p - 1 + 1/p`, impossible for `p ≥ 2` (`final_arith`).

Everything is checked in Lean; nothing is external.  The statement is
slightly more general than the thesis in indexing the observations by an
arbitrary nonempty `Fintype` rather than `{1, …, N}`.
-/

variable {p : ℕ} [Fact p.Prime] {d : ℕ}

/-- `IsGlobalMin f z` means `z` is a global minimiser of the real-valued
function `f`. -/
def IsGlobalMin {α : Type*} (f : α → ℝ) (z : α) : Prop :=
  ∀ w, f z ≤ f w

/-! ### Affine functions over `ZMod p` and the size of their zero sets -/

/-- The affine function `v ↦ c + ∑ j, ℓ j * v j` on `(ZMod p)^d`. -/
def affZ (c : ZMod p) (ℓ : Fin d → ZMod p) (v : Fin d → ZMod p) : ZMod p :=
  c + ∑ j, ℓ j * v j

theorem affZ_add_single (c : ZMod p) (ℓ : Fin d → ZMod p) (v : Fin d → ZMod p)
    (j₀ : Fin d) (u : ZMod p) :
    affZ c ℓ (v + Pi.single j₀ u) = affZ c ℓ v + ℓ j₀ * u := by
  have hsingle : ∑ j, ℓ j * (Pi.single j₀ u : Fin d → ZMod p) j = ℓ j₀ * u := by
    simp [Pi.single_apply]
  unfold affZ
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hsingle]
  ring

/-- All fibres of an affine function with a nonzero linear part have the same
size (they are translates of one another). -/
theorem card_fiber_eq (c : ZMod p) (ℓ : Fin d → ZMod p) (j₀ : Fin d) (hj₀ : ℓ j₀ ≠ 0)
    (t : ZMod p) :
    (univ.filter (fun v : Fin d → ZMod p => affZ c ℓ v = t)).card =
      (univ.filter (fun v : Fin d → ZMod p => affZ c ℓ v = 0)).card := by
  symm
  refine Finset.card_nbij' (fun v => v + Pi.single j₀ ((ℓ j₀)⁻¹ * t))
    (fun w => w + Pi.single j₀ (-((ℓ j₀)⁻¹ * t))) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hv ⊢
    rw [affZ_add_single, hv, zero_add, mul_inv_cancel_left₀ hj₀]
  · intro w hw
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hw ⊢
    rw [affZ_add_single, hw, mul_neg, mul_inv_cancel_left₀ hj₀, add_neg_cancel]
  · intro v _
    simp only
    rw [add_assoc, ← Pi.single_add, add_neg_cancel, Pi.single_zero, add_zero]
  · intro w _
    simp only
    rw [add_assoc, ← Pi.single_add, neg_add_cancel, Pi.single_zero, add_zero]

theorem card_univ_pi : (univ : Finset (Fin d → ZMod p)).card = p ^ d := by
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- A nonzero affine function on `(ZMod p)^d` vanishes on at most `p^(d-1)`
points: `#zeros * p ≤ p ^ d`. -/
theorem card_affZ_zero_mul_le (c : ZMod p) (ℓ : Fin d → ZMod p)
    (hne : c ≠ 0 ∨ ∃ j, ℓ j ≠ 0) :
    (univ.filter (fun v : Fin d → ZMod p => affZ c ℓ v = 0)).card * p ≤ p ^ d := by
  by_cases hℓ : ∃ j, ℓ j ≠ 0
  · obtain ⟨j₀, hj₀⟩ := hℓ
    have hsum := Finset.card_eq_sum_card_fiberwise (f := affZ c ℓ)
      (s := (univ : Finset (Fin d → ZMod p))) (t := (univ : Finset (ZMod p)))
      (fun v _ => mem_univ _)
    rw [card_univ_pi] at hsum
    rw [Finset.sum_congr rfl (fun b _ => card_fiber_eq c ℓ j₀ hj₀ b), Finset.sum_const,
      Finset.card_univ, ZMod.card, smul_eq_mul] at hsum
    rw [mul_comm]
    exact hsum.ge
  · push_neg at hℓ
    have hc : c ≠ 0 := by
      rcases hne with h | ⟨j, hj⟩
      · exact h
      · exact absurd (hℓ j) hj
    have : (univ.filter (fun v : Fin d → ZMod p => affZ c ℓ v = 0)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro v _
      simp [affZ, hℓ, hc]
    rw [this]
    simp

/-! ### Equidistributed designs -/

variable {ι : Type*} [Fintype ι]

/-- Reduction of the predictor row `x i ∈ ℤ_p^d` modulo `p`. -/
noncomputable def reduce (x : ι → Fin d → ℤ_[p]) (i : ι) : Fin d → ZMod p :=
  fun j => PadicInt.toZMod (x i j)

/-- The design is exactly equidistributed modulo `p`: every residue pattern
`v ∈ (ZMod p)^d` is the reduction of the same number `M` of rows. -/
def Equidistributed (x : ι → Fin d → ℤ_[p]) : Prop :=
  ∃ M : ℕ, ∀ v : Fin d → ZMod p, (univ.filter (fun i => reduce x i = v)).card = M

/-- Under equidistribution with multiplicity `M`, `N = p ^ d * M`. -/
theorem card_eq_pow_mul (x : ι → Fin d → ℤ_[p]) {M : ℕ}
    (hM : ∀ v : Fin d → ZMod p, (univ.filter (fun i => reduce x i = v)).card = M) :
    Fintype.card ι = p ^ d * M := by
  have h := Finset.card_eq_sum_card_fiberwise (f := reduce x) (s := (univ : Finset ι))
    (t := (univ : Finset (Fin d → ZMod p))) (fun i _ => mem_univ _)
  rw [Finset.card_univ] at h
  rw [h, Finset.sum_congr rfl (fun v _ => hM v), Finset.sum_const, smul_eq_mul, card_univ_pi]

theorem card_filter_affZ_ne (x : ι → Fin d → ℤ_[p]) {M : ℕ}
    (hM : ∀ v : Fin d → ZMod p, (univ.filter (fun i => reduce x i = v)).card = M)
    (c : ZMod p) (ℓ : Fin d → ZMod p) :
    (univ.filter (fun i => affZ c ℓ (reduce x i) ≠ 0)).card =
      (univ.filter (fun v : Fin d → ZMod p => affZ c ℓ v ≠ 0)).card * M := by
  have h := Finset.card_eq_sum_card_fiberwise (f := reduce x)
    (s := univ.filter (fun i => affZ c ℓ (reduce x i) ≠ 0))
    (t := univ.filter (fun v : Fin d → ZMod p => affZ c ℓ v ≠ 0))
    (by
      intro i hi
      simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hi ⊢
      exact hi)
  rw [h, Finset.sum_congr rfl (fun v hv => ?_), Finset.sum_const, smul_eq_mul]
  rw [Finset.filter_filter, ← hM v]
  congr 1
  apply Finset.filter_congr
  intro i _
  simp only [mem_filter, mem_univ, true_and] at hv
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by rw [h]; exact hv, h⟩

/-- Under equidistribution, a nonzero affine function of the reduced rows is
nonzero on at least `(1 - 1/p) N` rows: `N * p ≤ #nonzero * p + N`. -/
theorem card_filter_affZ_ne_bound (x : ι → Fin d → ℤ_[p]) {M : ℕ}
    (hM : ∀ v : Fin d → ZMod p, (univ.filter (fun i => reduce x i = v)).card = M)
    (c : ZMod p) (ℓ : Fin d → ZMod p) (hne : c ≠ 0 ∨ ∃ j, ℓ j ≠ 0) :
    Fintype.card ι * p ≤
      (univ.filter (fun i => affZ c ℓ (reduce x i) ≠ 0)).card * p + Fintype.card ι := by
  rw [card_eq_pow_mul x hM, card_filter_affZ_ne x hM c ℓ]
  have h1 := card_affZ_zero_mul_le c ℓ hne
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin d → ZMod p)))
    (fun v => affZ c ℓ v = 0)
  rw [card_univ_pi] at h2
  simp only [ne_eq] at h1 h2 ⊢
  rw [← h2] at h1 ⊢
  have h3 := Nat.mul_le_mul_right M h1
  nlinarith [h3]

/-! ### `p`-adic helper lemmas -/

/-- An element of `ℤ_[p]` with nonzero reduction mod `p` is a unit. -/
theorem norm_eq_one_of_toZMod_ne_zero (z : ℤ_[p]) (hz : PadicInt.toZMod z ≠ 0) : ‖z‖ = 1 := by
  by_contra hne
  have hlt : ‖z‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one z) hne
  apply hz
  have hmem : z ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
    exact hlt
  exact (RingHom.mem_ker).mp hmem

/-- In `ℚ_[p]`, a norm below `1` is at most `1/p`. -/
theorem norm_le_inv_of_lt_one (w : ℚ_[p]) (hw : ‖w‖ < 1) : ‖w‖ ≤ (p : ℝ)⁻¹ := by
  have := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one w 0).mp (by simpa using hw)
  simpa using this

/-- Every `z ∈ ℚ_[p]` with `‖z‖ ≤ 1` is within distance `< 1` of some
`n ∈ {0, …, p-1}`. -/
theorem exists_nat_lt_norm_sub_lt_one (z : ℚ_[p]) (hz : ‖z‖ ≤ 1) :
    ∃ n : ℕ, n < p ∧ ‖z - n‖ < 1 := by
  obtain ⟨n, hn, hmem⟩ := PadicInt.exists_mem_range (⟨z, hz⟩ : ℤ_[p])
  refine ⟨n, hn, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hmem
  simpa [PadicInt.norm_def] using hmem

/-- Averaging over the `p` residues `u = 0, …, p-1`: for `‖z‖ ≤ 1`,
`∑_{u < p} ‖z - u‖ ≤ (p - 1) + 1/p`. -/
theorem sum_norm_sub_range_le (z : ℚ_[p]) (hz : ‖z‖ ≤ 1) :
    ∑ u ∈ Finset.range p, ‖z - u‖ ≤ ((p : ℝ) - 1) + (p : ℝ)⁻¹ := by
  obtain ⟨n, hn, hlt⟩ := exists_nat_lt_norm_sub_lt_one z hz
  have hn_mem : n ∈ Finset.range p := Finset.mem_range.mpr hn
  rw [← Finset.add_sum_erase _ _ hn_mem]
  have h1 : ‖z - n‖ ≤ (p : ℝ)⁻¹ := norm_le_inv_of_lt_one _ hlt
  have h2 : ∑ u ∈ (Finset.range p).erase n, ‖z - u‖ ≤
      ∑ u ∈ (Finset.range p).erase n, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro u _
    calc ‖z - (u : ℚ_[p])‖ ≤ max ‖z‖ ‖(u : ℚ_[p])‖ := by
          rw [sub_eq_add_neg, ← norm_neg (u : ℚ_[p])]
          exact Padic.nonarchimedean _ _
      _ ≤ 1 := max_le hz (by exact_mod_cast Padic.norm_int_le_one (u : ℤ))
  rw [Finset.sum_const, Finset.card_erase_of_mem hn_mem, Finset.card_range, nsmul_eq_mul,
    mul_one] at h2
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := Nat.cast_pred hp
  linarith

/-- Norm values in `ℚ_[p]` are powers of `p`: a strictly smaller norm is at
most `1/p` times the larger one. -/
theorem norm_le_inv_mul_of_lt (c r : ℚ_[p]) (h : ‖c‖ < ‖r‖) : ‖c‖ ≤ (p : ℝ)⁻¹ * ‖r‖ := by
  have hr' : 0 < ‖r‖ := (norm_nonneg c).trans_lt h
  have : ‖c / r‖ < 1 := by
    rw [norm_div, div_lt_one hr']
    exact h
  have h2 := norm_le_inv_of_lt_one _ this
  rw [norm_div, div_le_iff₀ hr'] at h2
  exact h2

/-- Ultrametric inequality for a difference whose first term is strictly smaller. -/
theorem norm_sub_eq_of_norm_lt (v w : ℚ_[p]) (hlt : ‖v‖ < ‖w‖) : ‖v - w‖ = ‖w‖ := by
  rw [sub_eq_add_neg, Padic.add_eq_max_of_ne (by rw [norm_neg]; exact hlt.ne), norm_neg,
    max_eq_right hlt.le]

/-- The final real-arithmetic contradiction `p (p - 1) ≤ p - 1 + 1/p` for `p ≥ 2`,
packaged with the chain of inequalities that produces it. -/
theorem final_arith (q N σ ρ ρ' C A : ℝ) (hq : 2 ≤ q) (hN : 0 < N) (hσ : 0 < σ)
    (hC : N * (q - 1) ≤ C * q) (h1 : C * σ ≤ A)
    (h3 : A * q ≤ ρ' * N * (q - 1 + q⁻¹)) (h4 : ρ' ≤ q⁻¹ * ρ) (h5 : ρ ≤ σ) : False := by
  have hq0 : 0 < q := by linarith
  have hqt : q * q⁻¹ = 1 := mul_inv_cancel₀ hq0.ne'
  have ht0 : 0 < q⁻¹ := inv_pos.mpr hq0
  have ht2 : q⁻¹ ≤ 1 / 2 := by nlinarith
  have e1 : N * (q - 1) * σ ≤ C * q * σ := mul_le_mul_of_nonneg_right hC hσ.le
  have e2 : C * q * σ ≤ A * q := by nlinarith
  have hρ'σ : ρ' ≤ q⁻¹ * σ := h4.trans (by nlinarith)
  have hpos : 0 ≤ N * (q - 1 + q⁻¹) := mul_nonneg hN.le (by linarith)
  have e4 : ρ' * N * (q - 1 + q⁻¹) ≤ q⁻¹ * σ * N * (q - 1 + q⁻¹) := by nlinarith
  have e5 : (N * σ) * (q - 1) ≤ (N * σ) * (q⁻¹ * (q - 1 + q⁻¹)) := by nlinarith
  have e6 : q - 1 ≤ q⁻¹ * (q - 1 + q⁻¹) := le_of_mul_le_mul_left e5 (by positivity)
  nlinarith

/-! ### Affine functions with `p`-adic coefficients on `ℤ_[p]`-points -/

/-- `affineEval c₀ c v = c₀ + ∑ j, c j * v j` for `v ∈ ℤ_p^d`. -/
noncomputable def affineEval (c₀ : ℚ_[p]) (c : Fin d → ℚ_[p]) (v : Fin d → ℤ_[p]) : ℚ_[p] :=
  c₀ + ∑ j, c j * (v j : ℚ_[p])

theorem norm_affineEval_le (c₀ : ℚ_[p]) (c : Fin d → ℚ_[p]) {σ : ℝ} (hc₀ : ‖c₀‖ ≤ σ)
    (hc : ∀ j, ‖c j‖ ≤ σ) (v : Fin d → ℤ_[p]) : ‖affineEval c₀ c v‖ ≤ σ := by
  have hσ : 0 ≤ σ := (norm_nonneg _).trans hc₀
  unfold affineEval
  refine (Padic.nonarchimedean _ _).trans (max_le hc₀ ?_)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hσ (fun j _ => ?_)
  rw [norm_mul]
  calc ‖c j‖ * ‖(v j : ℚ_[p])‖ ≤ σ * 1 :=
        mul_le_mul (hc j) (PadicInt.norm_le_one (v j)) (norm_nonneg _) hσ
    _ = σ := mul_one σ

/-- The sup-norm of the coefficient vector `(c₀, c)` is attained. -/
theorem exists_sup_coeff (c₀ : ℚ_[p]) (c : Fin d → ℚ_[p]) :
    ∃ σ : ℝ, ‖c₀‖ ≤ σ ∧ (∀ j, ‖c j‖ ≤ σ) ∧
      ∃ u : ℚ_[p], ‖u‖ = σ ∧ (u = c₀ ∨ ∃ j, u = c j) := by
  classical
  let S : Finset ℝ := insert ‖c₀‖ (Finset.univ.image (fun j => ‖c j‖))
  have hSne : S.Nonempty := ⟨‖c₀‖, Finset.mem_insert_self _ _⟩
  refine ⟨S.max' hSne, Finset.le_max' S _ (Finset.mem_insert_self _ _), fun j =>
    Finset.le_max' S _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))),
    ?_⟩
  have hmem : S.max' hSne ∈ S := Finset.max'_mem S hSne
  rw [Finset.mem_insert, Finset.mem_image] at hmem
  rcases hmem with h | ⟨j, -, hj⟩
  · exact ⟨c₀, h.symm, Or.inl rfl⟩
  · exact ⟨c j, hj, Or.inr ⟨j, rfl⟩⟩

/-- **Key counting lemma.** If the coefficient vector of `h = affineEval c₀ c`
has sup-norm `σ > 0`, then under equidistribution `‖h (x i)‖ = σ` for at
least `(1 - 1/p) N` indices `i`, stated as `N * p ≤ #{i | ‖h (x i)‖ = σ} * p + N`. -/
theorem card_filter_norm_affineEval_eq (x : ι → Fin d → ℤ_[p]) {M : ℕ}
    (hM : ∀ v : Fin d → ZMod p, (univ.filter (fun i => reduce x i = v)).card = M)
    (c₀ : ℚ_[p]) (c : Fin d → ℚ_[p]) {σ : ℝ} (hσ : 0 < σ) (hc₀ : ‖c₀‖ ≤ σ)
    (hc : ∀ j, ‖c j‖ ≤ σ) (u : ℚ_[p]) (hu : ‖u‖ = σ) (hu' : u = c₀ ∨ ∃ j, u = c j) :
    Fintype.card ι * p ≤
      (univ.filter (fun i => ‖affineEval c₀ c (x i)‖ = σ)).card * p + Fintype.card ι := by
  classical
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hu
    exact hσ.ne hu
  have hdiv : ∀ w : ℚ_[p], ‖w‖ ≤ σ → ‖w / u‖ ≤ 1 := fun w hw => by
    rw [norm_div, hu, div_le_one hσ]
    exact hw
  let e₀ : ℤ_[p] := ⟨c₀ / u, hdiv c₀ hc₀⟩
  let e : Fin d → ℤ_[p] := fun j => ⟨c j / u, hdiv (c j) (hc j)⟩
  let E : (Fin d → ℤ_[p]) → ℤ_[p] := fun v => e₀ + ∑ j, e j * v j
  have hE : ∀ v, affineEval c₀ c v = u * (E v : ℚ_[p]) := by
    intro v
    simp only [E, affineEval, PadicInt.coe_add, PadicInt.coe_sum, PadicInt.coe_mul]
    show c₀ + ∑ j, c j * (v j : ℚ_[p]) = u * (c₀ / u + ∑ j, (c j / u) * (v j : ℚ_[p]))
    rw [mul_add, Finset.mul_sum, mul_div_cancel₀ _ hu0]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← mul_assoc, mul_div_cancel₀ _ hu0]
  have hred : ∀ v, PadicInt.toZMod (E v) =
      affZ (PadicInt.toZMod e₀) (fun j => PadicInt.toZMod (e j))
        (fun j => PadicInt.toZMod (v j)) := by
    intro v
    simp [E, affZ, map_add, map_sum, map_mul]
  have hne : PadicInt.toZMod e₀ ≠ 0 ∨ ∃ j, PadicInt.toZMod (e j) ≠ 0 := by
    rcases hu' with rfl | ⟨j, rfl⟩
    · left
      have : e₀ = 1 := PadicInt.ext (by
        show u / u = 1
        exact div_self hu0)
      rw [this, map_one]
      exact one_ne_zero
    · right
      refine ⟨j, ?_⟩
      have : e j = 1 := PadicInt.ext (by
        show c j / c j = 1
        exact div_self hu0)
      rw [this, map_one]
      exact one_ne_zero
  have hsub : univ.filter (fun i => affZ (PadicInt.toZMod e₀) (fun j => PadicInt.toZMod (e j))
      (reduce x i) ≠ 0) ⊆ univ.filter (fun i => ‖affineEval c₀ c (x i)‖ = σ) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    have h1 : PadicInt.toZMod (E (x i)) ≠ 0 := by
      rw [hred]
      exact hi
    have h2 := norm_eq_one_of_toZMod_ne_zero _ h1
    rw [hE, norm_mul, hu, ← PadicInt.norm_def, h2, mul_one]
  have hcard := Finset.card_le_card hsub
  have hbound := card_filter_affZ_ne_bound x hM _ _ hne
  exact hbound.trans (Nat.add_le_add_right (Nat.mul_le_mul_right p hcard) _)

/-! ### Affine `p`-adic regression: residuals and the two losses -/

variable (x : ι → Fin d → ℤ_[p]) (y : ι → ℚ_[p])

/-- Residual `r_i(a,b) = y_i - a - b · x_i`. -/
noncomputable def residual (a : ℚ_[p]) (b : Fin d → ℚ_[p]) (i : ι) : ℚ_[p] :=
  y i - a - ∑ j, b j * (x i j : ℚ_[p])

/-- Summed loss `L_1(a,b) = ∑ i, |r_i(a,b)|_p`. -/
noncomputable def L1 (a : ℚ_[p]) (b : Fin d → ℚ_[p]) : ℝ :=
  ∑ i, ‖residual x y a b i‖

/-- Max loss `L_∞(a,b) = max_i |r_i(a,b)|_p` (nonempty index type). -/
noncomputable def Linf [Nonempty ι] (a : ℚ_[p]) (b : Fin d → ℚ_[p]) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ‖residual x y a b i‖)

theorem norm_residual_le_Linf [Nonempty ι] (a : ℚ_[p]) (b : Fin d → ℚ_[p]) (i : ι) :
    ‖residual x y a b i‖ ≤ Linf x y a b :=
  Finset.le_sup' (fun i => ‖residual x y a b i‖) (Finset.mem_univ i)

theorem exists_norm_residual_eq_Linf [Nonempty ι] (a : ℚ_[p]) (b : Fin d → ℚ_[p]) :
    ∃ i, ‖residual x y a b i‖ = Linf x y a b := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι))
    (fun i => ‖residual x y a b i‖)
  exact ⟨i, hi.symm⟩

theorem Linf_nonneg [Nonempty ι] (a : ℚ_[p]) (b : Fin d → ℚ_[p]) : 0 ≤ Linf x y a b := by
  obtain ⟨i, hi⟩ := exists_norm_residual_eq_Linf x y a b
  rw [← hi]
  exact norm_nonneg _

theorem Linf_eq_zero_iff [Nonempty ι] (a : ℚ_[p]) (b : Fin d → ℚ_[p]) :
    Linf x y a b = 0 ↔ ∀ i, residual x y a b i = 0 := by
  constructor
  · intro h i
    have := norm_residual_le_Linf x y a b i
    rw [h] at this
    exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
  · intro h
    obtain ⟨i, hi⟩ := exists_norm_residual_eq_Linf x y a b
    rw [← hi, h i, norm_zero]

theorem L1_nonneg (a : ℚ_[p]) (b : Fin d → ℚ_[p]) : 0 ≤ L1 x y a b :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem L1_eq_zero_iff (a : ℚ_[p]) (b : Fin d → ℚ_[p]) :
    L1 x y a b = 0 ↔ ∀ i, residual x y a b i = 0 := by
  unfold L1
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => norm_nonneg _)]
  simp

omit [Fintype ι] in
/-- `r_i(a,b) = r_i(a',b') - h(x_i)` where `h = (a - a') + (b - b') · x`. -/
theorem residual_sub (a : ℚ_[p]) (b : Fin d → ℚ_[p]) (a' : ℚ_[p]) (b' : Fin d → ℚ_[p]) (i : ι) :
    residual x y a b i =
      residual x y a' b' i - affineEval (a - a') (fun j => b j - b' j) (x i) := by
  unfold residual affineEval
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

omit [Fintype ι] in
/-- Shifting the intercept by `c` shifts every residual by `-c`. -/
theorem residual_add_intercept (a : ℚ_[p]) (b : Fin d → ℚ_[p]) (c : ℚ_[p]) (i : ι) :
    residual x y (a + c) b i = residual x y a b i - c := by
  unfold residual
  ring

/-! ### Main theorem -/

/-- **Equidistributed designs: `argmin L1 ⊆ argmin L∞`** (strong form, no
no-exact-fit hypothesis).  If the design is exactly equidistributed modulo
`p`, every global minimiser of the summed loss `L1` is a global minimiser of
the max loss `Linf`. -/
theorem isGlobalMin_Linf_of_isGlobalMin_L1 [Nonempty ι] (hequi : Equidistributed x)
    (a : ℚ_[p]) (b : Fin d → ℚ_[p])
    (hmin : IsGlobalMin (fun ab : ℚ_[p] × (Fin d → ℚ_[p]) => L1 x y ab.1 ab.2) (a, b)) :
    IsGlobalMin (fun ab : ℚ_[p] × (Fin d → ℚ_[p]) => Linf x y ab.1 ab.2) (a, b) := by
  classical
  obtain ⟨M, hM⟩ := hequi
  rintro ⟨a', b'⟩
  by_contra hlt
  simp only [not_le] at hlt
  have hN : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  obtain ⟨i₁, hi₁⟩ := exists_norm_residual_eq_Linf x y a b
  rcases (Linf_nonneg x y a' b').eq_or_lt with hρ'0 | hρ'pos
  · -- `(a', b')` is an exact fit, so `L1 a' b' = 0 < L1 a b`: contradiction.
    have hfit : ∀ i, residual x y a' b' i = 0 := (Linf_eq_zero_iff x y a' b').mp hρ'0.symm
    have hL1' : L1 x y a' b' = 0 := (L1_eq_zero_iff x y a' b').mpr hfit
    have hpos : 0 < L1 x y a b := by
      have h0 : 0 < ‖residual x y a b i₁‖ := by
        rw [hi₁]
        linarith
      show 0 < ∑ i, ‖residual x y a b i‖
      exact h0.trans_le (Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ i₁))
    have := hmin (a', b')
    simp only at this
    linarith
  · -- Coefficient sup-norm `σ` of `h = (a - a') + (b - b') · x`.
    obtain ⟨σ, hc₀σ, hcσ, u, hu, hu'⟩ := exists_sup_coeff (a - a') (fun j => b j - b' j)
    have hh : ∀ i, ‖affineEval (a - a') (fun j => b j - b' j) (x i)‖ ≤ σ :=
      fun i => norm_affineEval_le _ _ hc₀σ hcσ (x i)
    have hres : ∀ i, residual x y a b i =
        residual x y a' b' i - affineEval (a - a') (fun j => b j - b' j) (x i) :=
      fun i => residual_sub x y a b a' b' i
    -- (i) `Linf a b ≤ σ`.
    have hρσ : Linf x y a b ≤ σ := by
      have h1 : Linf x y a b ≤ max (Linf x y a' b') σ := by
        rw [← hi₁, hres i₁, sub_eq_add_neg]
        refine (Padic.nonarchimedean _ _).trans
          (max_le_max (norm_residual_le_Linf x y a' b' i₁) ?_)
        rw [norm_neg]
        exact hh i₁
      rcases le_max_iff.mp h1 with h | h
      · exact absurd (lt_of_le_of_lt h hlt) (lt_irrefl _)
      · exact h
    have hσpos : 0 < σ := hρ'pos.trans_le (hlt.le.trans hρσ)
    have hρ'σ : Linf x y a' b' < σ := hlt.trans_le hρσ
    -- (ii)+(iii) Lower bound `L1 a b ≥ #A * σ` with `#A ≥ (1 - 1/p) N`.
    have hbound := card_filter_norm_affineEval_eq x hM (a - a') (fun j => b j - b' j) hσpos
      hc₀σ hcσ u hu hu'
    set A := univ.filter (fun i => ‖affineEval (a - a') (fun j => b j - b' j) (x i)‖ = σ)
      with hA
    have hC : (Fintype.card ι : ℝ) * (p - 1) ≤ (A.card : ℝ) * p := by
      have : ((Fintype.card ι * p : ℕ) : ℝ) ≤ ((A.card * p + Fintype.card ι : ℕ) : ℝ) := by
        exact_mod_cast hbound
      push_cast at this
      linarith
    have hL1 : (A.card : ℝ) * σ ≤ L1 x y a b := by
      have h1 : ∑ i ∈ A, ‖residual x y a b i‖ = ∑ i ∈ A, σ := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        simp only [hA, mem_filter, mem_univ, true_and] at hi
        rw [hres i, norm_sub_eq_of_norm_lt]
        · exact hi
        · rw [hi]
          exact (norm_residual_le_Linf x y a' b' i).trans_lt hρ'σ
      rw [Finset.sum_const, nsmul_eq_mul] at h1
      rw [← h1]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        (fun i _ _ => norm_nonneg _)
    -- (iv) Competitors `(a' + c' u, b')`, `u = 0, …, p - 1`.
    obtain ⟨i₀, hi₀⟩ := exists_norm_residual_eq_Linf x y a' b'
    set c' := residual x y a' b' i₀ with hc'
    have hc'0 : c' ≠ 0 := by
      intro h
      rw [h, norm_zero] at hi₀
      exact hρ'pos.ne hi₀
    have hz : ∀ i, ‖residual x y a' b' i / c'‖ ≤ 1 := fun i => by
      rw [norm_div, hi₀, div_le_one hρ'pos]
      exact norm_residual_le_Linf x y a' b' i
    have hshift : ∀ (n : ℕ) (i : ι), ‖residual x y (a' + c' * n) b' i‖ =
        Linf x y a' b' * ‖residual x y a' b' i / c' - n‖ := by
      intro n i
      rw [residual_add_intercept, ← hi₀, ← norm_mul, mul_sub, mul_div_cancel₀ _ hc'0]
    have hsum : ∑ n ∈ Finset.range p, L1 x y (a' + c' * n) b' ≤
        Linf x y a' b' * Fintype.card ι * ((p : ℝ) - 1 + (p : ℝ)⁻¹) := by
      simp only [L1, hshift]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Linf_nonneg x y a' b')
      calc ∑ i, ∑ n ∈ Finset.range p, ‖residual x y a' b' i / c' - n‖
          ≤ ∑ _i : ι, ((p : ℝ) - 1 + (p : ℝ)⁻¹) :=
            Finset.sum_le_sum (fun i _ => sum_norm_sub_range_le _ (hz i))
        _ = Fintype.card ι * ((p : ℝ) - 1 + (p : ℝ)⁻¹) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hmin' : L1 x y a b * p ≤ ∑ n ∈ Finset.range p, L1 x y (a' + c' * n) b' := by
      have : ∑ _n ∈ Finset.range p, L1 x y a b ≤
          ∑ n ∈ Finset.range p, L1 x y (a' + c' * n) b' :=
        Finset.sum_le_sum (fun n _ => hmin (a' + c' * n, b'))
      rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] at this
    -- (v) `p · Linf a' b' ≤ Linf a b` since norm values are powers of `p`.
    have h4 : Linf x y a' b' ≤ (p : ℝ)⁻¹ * Linf x y a b := by
      rw [← hi₀, ← hi₁]
      exact norm_le_inv_mul_of_lt _ _ (by rw [hi₀, hi₁]; exact hlt)
    exact final_arith p (Fintype.card ι) σ (Linf x y a b) (Linf x y a' b') A.card (L1 x y a b)
      hp2 hN hσpos hC hL1 (hmin'.trans hsum) h4 hρσ

/-- **Thesis Theorem `thm:equidistributed-sum-refines-max`.**  For an affine
`p`-adic regression instance with `x_i ∈ ℤ_p^d`, `y_i ∈ ℚ_p`, an intercept in
the model, exactly equidistributed reductions `x̄_i ∈ 𝔽_p^d`, and no exact
affine fit, every minimiser of `L_1` is a minimiser of `L_∞`.

The no-exact-fit hypothesis is not needed (see
`isGlobalMin_Linf_of_isGlobalMin_L1`), hence the underscore. -/
theorem equidistributed_sum_refines_max [Nonempty ι] (hequi : Equidistributed x)
    (_hnofit : ¬ ∃ (a : ℚ_[p]) (b : Fin d → ℚ_[p]), ∀ i, residual x y a b i = 0)
    (a : ℚ_[p]) (b : Fin d → ℚ_[p])
    (hmin : IsGlobalMin (fun ab : ℚ_[p] × (Fin d → ℚ_[p]) => L1 x y ab.1 ab.2) (a, b)) :
    IsGlobalMin (fun ab : ℚ_[p] × (Fin d → ℚ_[p]) => Linf x y ab.1 ab.2) (a, b) :=
  isGlobalMin_Linf_of_isGlobalMin_L1 x y hequi a b hmin

end PhdThesisLean.EquidistributedSumRefinesMax

#print axioms PhdThesisLean.EquidistributedSumRefinesMax.equidistributed_sum_refines_max
#print axioms PhdThesisLean.EquidistributedSumRefinesMax.isGlobalMin_Linf_of_isGlobalMin_L1
#print axioms PhdThesisLean.EquidistributedSumRefinesMax.card_affZ_zero_mul_le
#print axioms PhdThesisLean.EquidistributedSumRefinesMax.card_filter_norm_affineEval_eq
