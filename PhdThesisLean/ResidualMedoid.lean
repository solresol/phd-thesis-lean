import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Tactic

namespace PhdThesisLean.ResidualMedoid

open scoped BigOperators

/-!
# `p`-adic residual medoid and monotone coordinate update

Thesis source: `ecommerce-taxonomy-classification/body.tex` in the thesis
repository (`/Users/gregb/Documents/devel/phd-thesis`), labels
`prop:chapter-residual-medoid` (the `p`-adic residual medoid) and
`cor:chapter-monotone-update` (monotone coordinate update).

Headline declarations.

* `exists_medoid_finset`, `exists_medoid` and `exists_medoid_multiset`
  formalise the proposition: for a nonempty finite family (equivalently a
  nonempty finite multiset) `R ⊂ ℚ_[p]`, the coordinate objective
  `F(a) = ∑_{r ∈ R} ‖r - a‖` has a global minimiser belonging to `R`.
* `monotone_coordinate_update` formalises the corollary for the additive tag
  model with binary indicators: whenever tag `j` has at least one row, some
  observed partial residual `partialResidual X y j a i₀` globally minimises the
  coordinate objective `coordinateCost X y j a`, and replacing coordinate `j`
  by it does not increase the full fitting objective `loss X y`.
* `loss_update_eq` is the bookkeeping identity behind the corollary: after
  updating coordinate `j`, the full objective splits as the coordinate
  objective on `I_j` plus the (unchanged) contribution of the rows without
  tag `j`.

Correspondence notes.

* Rows and tags are indexed by arbitrary finite types instead of
  `{1, …, n}` and `{1, …, m}`; this is strictly more general than the thesis.
* The thesis residual `r_i^{(j)} = y_i - ∑_{k < j} w_k x_{ik}` is the special
  case of `partialResidual` in which the not-yet-fitted coefficients
  (`k > j`) are zero.  The corollary is proved for an arbitrary current
  coefficient vector, which is exactly what "replacing the current coordinate"
  needs, and specialises to the thesis setting.
* No hypotheses beyond those in the thesis (nonemptiness of `R`, respectively
  of `I_j`) are used.  The degenerate empty-`I_j` case, in which the update
  leaves the objective unchanged, is recorded as
  `loss_update_eq_of_tagRows_empty`.
-/

/-- Global minimiser of a real-valued objective (same shape as
`PhdThesisLean.AllDifferent.IsGlobalMin`). -/
def IsGlobalMin {α : Type*} (f : α → ℝ) (x : α) : Prop := ∀ y, f x ≤ f y

variable {p : ℕ} [Fact p.Prime]

/-! ### Proposition `prop:chapter-residual-medoid` -/

section Proposition

/-- Ultrametric key step of the thesis proof: if `c` is at least as close to
`a` as `r` is, then `r` is at least as close to `c` as it is to `a`. -/
theorem norm_sub_le_of_norm_sub_le (r a c : ℚ_[p]) (h : ‖a - c‖ ≤ ‖r - a‖) :
    ‖r - c‖ ≤ ‖r - a‖ := by
  have hsplit : r - c = (r - a) + (a - c) := by ring
  rw [hsplit]
  exact (Padic.nonarchimedean _ _).trans (max_le le_rfl h)

variable {ι : Type*}

/-- Coordinate objective `F(a) = ∑_{i ∈ s} ‖r i - a‖` over an index finset. -/
noncomputable def finsetCost (s : Finset ι) (r : ι → ℚ_[p]) (a : ℚ_[p]) : ℝ :=
  ∑ i ∈ s, ‖r i - a‖

/-- Moving from `a` to a nearest member `r i₀` of the family does not increase
the coordinate objective. -/
theorem finsetCost_nearest_le (s : Finset ι) (r : ι → ℚ_[p]) (a : ℚ_[p]) (i₀ : ι)
    (h : ∀ i ∈ s, ‖a - r i₀‖ ≤ ‖a - r i‖) :
    finsetCost s r (r i₀) ≤ finsetCost s r a := by
  unfold finsetCost
  apply Finset.sum_le_sum
  intro i hi
  apply norm_sub_le_of_norm_sub_le
  rw [norm_sub_rev (r i) a]
  exact h i hi

/-- **Proposition `prop:chapter-residual-medoid`** (finset form): for a
nonempty finset of indices the coordinate objective has a global minimiser
among the indexed values. -/
theorem exists_medoid_finset {s : Finset ι} (hs : s.Nonempty) (r : ι → ℚ_[p]) :
    ∃ i₀ ∈ s, ∀ a, finsetCost s r (r i₀) ≤ finsetCost s r a := by
  obtain ⟨i₀, hi₀s, hi₀⟩ := s.exists_min_image (fun i => finsetCost s r (r i)) hs
  refine ⟨i₀, hi₀s, fun a => ?_⟩
  obtain ⟨i₁, hi₁s, hi₁⟩ := s.exists_min_image (fun i => ‖a - r i‖) hs
  calc finsetCost s r (r i₀) ≤ finsetCost s r (r i₁) := hi₀ i₁ hi₁s
    _ ≤ finsetCost s r a := finsetCost_nearest_le s r a i₁ hi₁

/-- Coordinate objective `F(a) = ∑_i ‖r i - a‖` over a finite index type. -/
noncomputable def medoidCost [Fintype ι] (r : ι → ℚ_[p]) (a : ℚ_[p]) : ℝ :=
  ∑ i, ‖r i - a‖

theorem medoidCost_eq_finsetCost [Fintype ι] (r : ι → ℚ_[p]) (a : ℚ_[p]) :
    medoidCost r a = finsetCost Finset.univ r a := rfl

/-- **Proposition `prop:chapter-residual-medoid`** (indexed-family form): for a
nonempty finite family `r : ι → ℚ_[p]` the function `a ↦ ∑ i, ‖r i - a‖` has a
global minimiser of the form `r i₀`. -/
theorem exists_medoid [Fintype ι] [Nonempty ι] (r : ι → ℚ_[p]) :
    ∃ i₀, IsGlobalMin (medoidCost r) (r i₀) := by
  obtain ⟨i₀, -, h⟩ := exists_medoid_finset Finset.univ_nonempty r
  exact ⟨i₀, h⟩

/-- Coordinate objective `F(a) = ∑_{r ∈ R} ‖r - a‖` over a multiset `R`. -/
noncomputable def multisetCost (R : Multiset ℚ_[p]) (a : ℚ_[p]) : ℝ :=
  (R.map fun r => ‖r - a‖).sum

/-- **Proposition `prop:chapter-residual-medoid`** (multiset form, literally
the thesis statement): for a nonempty finite multiset `R ⊂ ℚ_[p]` the function
`a ↦ ∑_{r ∈ R} ‖r - a‖` has a global minimiser belonging to `R`. -/
theorem exists_medoid_multiset {R : Multiset ℚ_[p]} (hR : R ≠ 0) :
    ∃ r₀ ∈ R, IsGlobalMin (multisetCost R) r₀ := by
  classical
  have hne : R.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hR
  have key : ∀ a : ℚ_[p], ∃ r₁ ∈ R, multisetCost R r₁ ≤ multisetCost R a := by
    intro a
    obtain ⟨r₁, hr₁, hmin⟩ := R.toFinset.exists_min_image (fun r => ‖a - r‖) hne
    refine ⟨r₁, Multiset.mem_toFinset.mp hr₁, ?_⟩
    unfold multisetCost
    apply Multiset.sum_map_le_sum_map
    intro r hr
    apply norm_sub_le_of_norm_sub_le
    rw [norm_sub_rev r a]
    exact hmin r (Multiset.mem_toFinset.mpr hr)
  obtain ⟨r₀, hr₀, hmin⟩ := R.toFinset.exists_min_image (fun r => multisetCost R r) hne
  refine ⟨r₀, Multiset.mem_toFinset.mp hr₀, fun a => ?_⟩
  obtain ⟨r₁, hr₁, h₁⟩ := key a
  exact (hmin r₁ (Multiset.mem_toFinset.mpr hr₁)).trans h₁

end Proposition

/-! ### Corollary `cor:chapter-monotone-update` -/

section Corollary

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq τ]

/-- Prediction of the additive tag model `ŷ_i = ∑_j w_j x_{ij}` with binary
indicators `X i j`. -/
noncomputable def predict (X : ι → τ → Bool) (a : τ → ℚ_[p]) (i : ι) : ℚ_[p] :=
  ∑ j, if X i j then a j else 0

/-- Full fitting objective `L(a) = ∑_i ‖y_i - ŷ_i(a)‖`. -/
noncomputable def loss (X : ι → τ → Bool) (y : ι → ℚ_[p]) (a : τ → ℚ_[p]) : ℝ :=
  ∑ i, ‖y i - predict X a i‖

/-- Rows carrying tag `j`: `I_j = {i : x_{ij} = 1}`. -/
def tagRows (X : ι → τ → Bool) (j : τ) : Finset ι :=
  Finset.univ.filter fun i => X i j = true

/-- Partial residual `r_i^{(j)} = y_i - ∑_{k ≠ j} w_k x_{ik}` (all coordinates
other than `j` kept at their current values). -/
noncomputable def partialResidual (X : ι → τ → Bool) (y : ι → ℚ_[p]) (j : τ) (a : τ → ℚ_[p])
    (i : ι) : ℚ_[p] :=
  y i - ∑ k ∈ Finset.univ.erase j, if X i k then a k else 0

/-- Coordinate objective `F_j(c) = ∑_{i ∈ I_j} ‖r_i^{(j)} - c‖`. -/
noncomputable def coordinateCost (X : ι → τ → Bool) (y : ι → ℚ_[p]) (j : τ)
    (a : τ → ℚ_[p]) (c : ℚ_[p]) : ℝ :=
  finsetCost (tagRows X j) (partialResidual X y j a) c

omit [Fintype τ] [DecidableEq τ] in
theorem mem_tagRows {X : ι → τ → Bool} {j : τ} {i : ι} :
    i ∈ tagRows X j ↔ X i j = true := by
  simp [tagRows]

omit [Fintype ι] in
theorem predict_eq_add_sum_erase (X : ι → τ → Bool) (a : τ → ℚ_[p]) (j : τ) (i : ι) :
    predict X a i =
      (if X i j then a j else 0) + ∑ k ∈ Finset.univ.erase j, if X i k then a k else 0 := by
  exact (Finset.add_sum_erase Finset.univ (fun k => if X i k then a k else 0)
    (Finset.mem_univ j)).symm

omit [Fintype ι] in
theorem predict_update (X : ι → τ → Bool) (a : τ → ℚ_[p]) (j : τ) (c : ℚ_[p]) (i : ι) :
    predict X (Function.update a j c) i =
      (if X i j then c else 0) + ∑ k ∈ Finset.univ.erase j, if X i k then a k else 0 := by
  rw [predict_eq_add_sum_erase X _ j, Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

/-- On a row carrying tag `j`, the residual after updating coordinate `j` to
`c` is the partial residual minus `c`. -/
theorem residual_update_of_mem (X : ι → τ → Bool) (y : ι → ℚ_[p]) (a : τ → ℚ_[p])
    (j : τ) (c : ℚ_[p]) {i : ι} (hi : i ∈ tagRows X j) :
    y i - predict X (Function.update a j c) i = partialResidual X y j a i - c := by
  have hX : X i j = true := mem_tagRows.mp hi
  rw [predict_update, if_pos hX]
  unfold partialResidual
  ring

/-- On a row without tag `j`, updating coordinate `j` does not change the
prediction. -/
theorem predict_update_of_not_mem (X : ι → τ → Bool) (a : τ → ℚ_[p]) (j : τ) (c : ℚ_[p])
    {i : ι} (hi : i ∉ tagRows X j) :
    predict X (Function.update a j c) i = predict X a i := by
  have hX : X i j = false := by
    have := mt mem_tagRows.mpr hi
    simpa using this
  rw [predict_update, predict_eq_add_sum_erase X a j]
  simp [hX]

/-- Decomposition of the full objective after a coordinate update: the rows
with tag `j` contribute the coordinate objective, the other rows are
unchanged. -/
theorem loss_update_eq (X : ι → τ → Bool) (y : ι → ℚ_[p]) (a : τ → ℚ_[p]) (j : τ)
    (c : ℚ_[p]) :
    loss X y (Function.update a j c) =
      coordinateCost X y j a c +
        ∑ i ∈ Finset.univ.filter (fun i => ¬ X i j = true), ‖y i - predict X a i‖ := by
  unfold loss coordinateCost finsetCost
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => X i j = true)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [residual_update_of_mem X y a j c hi]
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ∉ tagRows X j := by
      rw [mem_tagRows]
      exact (Finset.mem_filter.mp hi).2
    rw [predict_update_of_not_mem X a j c hi']

/-- The same decomposition for the current coefficient vector itself. -/
theorem loss_eq_coordinateCost_add (X : ι → τ → Bool) (y : ι → ℚ_[p]) (a : τ → ℚ_[p])
    (j : τ) :
    loss X y a =
      coordinateCost X y j a (a j) +
        ∑ i ∈ Finset.univ.filter (fun i => ¬ X i j = true), ‖y i - predict X a i‖ := by
  have h := loss_update_eq X y a j (a j)
  rwa [Function.update_eq_self] at h

/-- Any global minimiser of the coordinate objective yields a non-increasing
update of the full objective. -/
theorem loss_update_le_of_coordinate_min (X : ι → τ → Bool) (y : ι → ℚ_[p])
    (a : τ → ℚ_[p]) (j : τ) {c₀ : ℚ_[p]}
    (h : ∀ c, coordinateCost X y j a c₀ ≤ coordinateCost X y j a c) :
    loss X y (Function.update a j c₀) ≤ loss X y a := by
  rw [loss_update_eq, loss_eq_coordinateCost_add X y a j]
  exact add_le_add (h (a j)) le_rfl

/-- **Corollary `cor:chapter-monotone-update`**: if tag `j` occurs in at least
one row, some observed partial residual `partialResidual X y j a i₀`
(`i₀ ∈ I_j`) is a global minimiser of the coordinate objective `F_j`, and
replacing coordinate `j` by it cannot increase the full fitting objective. -/
theorem monotone_coordinate_update (X : ι → τ → Bool) (y : ι → ℚ_[p]) (a : τ → ℚ_[p])
    (j : τ) (hj : (tagRows X j).Nonempty) :
    ∃ i₀ ∈ tagRows X j,
      loss X y (Function.update a j (partialResidual X y j a i₀)) ≤ loss X y a ∧
        ∀ c, coordinateCost X y j a (partialResidual X y j a i₀) ≤
          coordinateCost X y j a c := by
  obtain ⟨i₀, hi₀, hmin⟩ := exists_medoid_finset hj (partialResidual X y j a)
  exact ⟨i₀, hi₀, loss_update_le_of_coordinate_min X y a j hmin, hmin⟩

/-- Degenerate case: if no row carries tag `j`, updating coordinate `j` leaves
the full objective unchanged. -/
theorem loss_update_eq_of_tagRows_empty (X : ι → τ → Bool) (y : ι → ℚ_[p])
    (a : τ → ℚ_[p]) (j : τ) (hj : tagRows X j = ∅) (c : ℚ_[p]) :
    loss X y (Function.update a j c) = loss X y a := by
  rw [loss_update_eq, loss_eq_coordinateCost_add X y a j]
  simp [coordinateCost, finsetCost, hj]

end Corollary

#print axioms exists_medoid_finset
#print axioms exists_medoid
#print axioms exists_medoid_multiset
#print axioms loss_update_eq
#print axioms monotone_coordinate_update

end PhdThesisLean.ResidualMedoid
