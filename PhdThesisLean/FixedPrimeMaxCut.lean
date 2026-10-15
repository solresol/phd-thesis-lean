import PhdThesisLean.AllDifferent

namespace PhdThesisLean.FixedPrimeMaxCut

open scoped BigOperators
open PhdThesisLean.FiniteDomainCompiler
open PhdThesisLean.AllDifferent (IsGlobalMin)

/-!
# Fixed-prime Max-Cut reduction for summed `p`-adic linear regression

This module formalises the thesis statements `lem:local-boolean-snapping`,
`thm:fixed-prime-hardness`, `lem:intercept-pinning` and `cor:affine-hardness`
from `padic-regression-complexity/body.tex` (lines 423–655) of the thesis
source tree `/Users/gregb/Documents/devel/phd-thesis`. The published theorem
`thm:main` (same file, line 133) is the `p = 2` special case of the very same
Max-Cut reduction, so it is covered by the fixed-prime statements proved here.

## What is proved

* `local_boolean_snapping` (`lem:local-boolean-snapping`): for every
  `t : ℚ_[p]` there is `b ∈ {0, 1}` with `U b - U t ≤ -‖t - b‖`, where
  `U t = ‖t‖ + ‖t - 1‖`. The thesis's prescribed choice of `b` is recorded by
  `local_boolean_snapping_close` (the residue case, an equality) and
  `local_boolean_snapping_far` (the two cases where no Boolean value is
  within distance `< 1`). The thesis assumes `t ∉ {0, 1}`; that hypothesis is
  only needed for strictness and is used in `local_boolean_snapping_of_ne`.
* `fixed_prime_hardness` (`thm:fixed-prime-hardness`): for a loopless graph on
  `Fin n` with edges indexed by a finite type `ε` via `left right : ε → Fin n`
  and `left e ≠ right e` (simple graphs and multigraphs are both covered), the
  objective `maxCutLoss` with forcing weights `M j = deg j + 1` attains a global
  minimum, every global minimiser is Boolean, the global minimisers are exactly
  the Boolean embeddings of maximum cuts, the Boolean value is
  `∑ M j + monochromatic s`, and the optimal value is
  `∑ M j + |E| - maxCut`.
* `homogeneousLoss_maxCutRows`: the objective is literally the homogeneous
  summed `p`-adic regression loss of an explicit integral row family
  `maxCutRows` (`M j` copies of `(e_j, 0)` and `(e_j, 1)` and one row
  `(e_u + e_v, 1)` per edge), with `5|E| + 2n` rows and all entries in
  `{0, 1}` (`card_maxCutIndex_eq`, `maxCutRows_coeff_mem`,
  `maxCutRows_target_mem`).
* `intercept_pinning` (`lem:intercept-pinning`): for any integral instance and
  any `T`, `L_aff(β, 0) ≤ L_aff(β, c) - (T - r) ‖c‖`; with `T ≥ r + 1` this
  excludes every `c ≠ 0` (`affineLoss_zero_lt`) and
  `isGlobalMin_affine_iff` identifies the affine minimisers with the pairs
  `(β, 0)` for homogeneous minimisers `β`. `affineRowLoss_pinnedRows` shows the
  `T ‖c‖` term is literally `T` appended rows `(0, 0)`.
* `affine_hardness` (`cor:affine-hardness`): with `T = (number of rows) + 1`
  pinning rows, the affine minimisers of the Max-Cut instance are exactly
  `(embed s, 0)` with `s` a maximum cut, the optimal value is again
  `∑ M j + |E| - maxCut`, and the augmented instance has `10|E| + 4n + 1`
  rows.

## Correspondence notes

* Everything is proved over `ℚ_[p]` for an arbitrary prime `p`, which is
  stronger than the thesis's parameter space `ℚ^n`.
* Edges are an arbitrary finite index type, so repeated edges are kept
  distinct; the thesis's unweighted simple graph is the special case of an
  injective edge family.
* `intercept_pinning` is proved without the thesis's standing hypothesis
  `T ≥ r + 1`; that hypothesis is used only where it is needed (strictness and
  the minimiser characterisation).
* As in `FixedPrimeHardness.lean`, the NP-hardness *transfer* is external:
  Mathlib has no P/NP framework, so "Max-Cut is NP-hard" and "the map
  `G ↦ maxCutRows` is polynomial-time computable" are not Lean premises. What is
  machine-checked is the complete reduction: the exact identification of the
  regression loss with the forcing objective, both semantic directions
  (Boolean snapping and the cut-size formula), the intercept-pinning gadget,
  and the explicit row counts and `{0, 1}` data bounds.
-/

section Snapping

variable {p : ℕ} [Fact p.Prime]

/-- Boolean forcing cost `U(t) = |t|_p + |t - 1|_p`. -/
noncomputable def U (t : ℚ_[p]) : ℝ := ‖t‖ + ‖t - 1‖

/-- The Boolean domain `{0, 1} ⊆ ℚ_[p]`. -/
noncomputable def booleanDomain (p : ℕ) [Fact p.Prime] : Finset ℚ_[p] := by
  classical
  exact {0, 1}

theorem mem_booleanDomain {t : ℚ_[p]} :
    t ∈ booleanDomain p ↔ t = 0 ∨ t = 1 := by
  simp [booleanDomain]

theorem zero_mem_booleanDomain : (0 : ℚ_[p]) ∈ booleanDomain p :=
  mem_booleanDomain.mpr (Or.inl rfl)

theorem one_mem_booleanDomain : (1 : ℚ_[p]) ∈ booleanDomain p :=
  mem_booleanDomain.mpr (Or.inr rfl)

theorem booleanDomain_nonempty : (booleanDomain p).Nonempty :=
  ⟨0, zero_mem_booleanDomain⟩

/-- `{0, 1}` is unit-separated: `‖0 - 1‖ = 1`. -/
theorem booleanDomain_unitSeparated : UnitSeparated (booleanDomain p) := by
  intro a ha b hb hab
  rcases mem_booleanDomain.mp ha with rfl | rfl <;>
    rcases mem_booleanDomain.mp hb with rfl | rfl
  · exact (hab rfl).elim
  · simp
  · simp
  · exact (hab rfl).elim

/-- The unary compiler cost of the Boolean domain is exactly `U`. -/
theorem unaryCost_booleanDomain (t : ℚ_[p]) :
    unaryCost (booleanDomain p) t = U t := by
  classical
  simp [unaryCost, booleanDomain, U]

theorem U_zero : U (0 : ℚ_[p]) = 1 := by simp [U]

theorem U_one : U (1 : ℚ_[p]) = 1 := by simp [U]

/-- Both Boolean values have forcing cost `1`. -/
theorem U_boolean : U (0 : ℚ_[p]) = 1 ∧ U (1 : ℚ_[p]) = 1 := ⟨U_zero, U_one⟩

theorem U_of_mem_booleanDomain {b : ℚ_[p]} (hb : b ∈ booleanDomain p) : U b = 1 := by
  rcases mem_booleanDomain.mp hb with rfl | rfl
  · exact U_zero
  · exact U_one

/-- Case 1 of the thesis proof: if `|t|_p > 1` then `|t - 1|_p = |t|_p`. -/
theorem norm_sub_one_of_one_lt_norm {t : ℚ_[p]} (ht : 1 < ‖t‖) : ‖t - 1‖ = ‖t‖ := by
  rw [sub_eq_add_neg, Padic.add_eq_max_of_ne]
  · rw [norm_neg, norm_one, max_eq_left ht.le]
  · rw [norm_neg, norm_one]
    exact ht.ne'

/-- Case 2 of the thesis proof (the residue case): if `t` is within distance
`< 1` of `b ∈ {0, 1}` then `U b - U t = -‖t - b‖` exactly. -/
theorem local_boolean_snapping_close {t b : ℚ_[p]} (hb : b ∈ booleanDomain p)
    (hclose : ‖t - b‖ < 1) : U b - U t = -‖t - b‖ := by
  have h := unaryCost_snap_close booleanDomain_unitSeparated hb hclose
  rw [unaryCost_booleanDomain, unaryCost_booleanDomain] at h
  linarith

/-- Cases 1 and 3 of the thesis proof: if no Boolean value is within distance
`< 1` of `t` then either Boolean `b` satisfies `U b - U t ≤ -‖t - b‖`. -/
theorem local_boolean_snapping_far {t b : ℚ_[p]} (hb : b ∈ booleanDomain p)
    (hfar : ∀ a ∈ booleanDomain p, 1 ≤ ‖t - a‖) : U b - U t ≤ -‖t - b‖ := by
  have h := unaryCost_snap_far booleanDomain_unitSeparated hb hfar
  rw [unaryCost_booleanDomain, unaryCost_booleanDomain] at h
  linarith

/-- Thesis `lem:local-boolean-snapping`: every `t : ℚ_[p]` has a Boolean value
`b` with `U b - U t ≤ -‖t - b‖`. (The thesis assumes `t ∉ {0, 1}`; the
inequality holds without it.) -/
theorem local_boolean_snapping (t : ℚ_[p]) :
    ∃ b ∈ booleanDomain p, U b - U t ≤ -‖t - b‖ := by
  obtain ⟨b, hb, h⟩ :=
    exists_unaryCost_snap booleanDomain_nonempty booleanDomain_unitSeparated (x := t)
  refine ⟨b, hb, ?_⟩
  rw [unaryCost_booleanDomain, unaryCost_booleanDomain] at h
  linarith

/-- The thesis form of the snapping lemma with the hypothesis `t ∉ {0, 1}`:
the snapped Boolean value strictly lowers `U`. -/
theorem local_boolean_snapping_of_ne {t : ℚ_[p]} (ht : t ≠ 0 ∧ t ≠ 1) :
    ∃ b ∈ booleanDomain p, U b - U t ≤ -‖t - b‖ ∧ U b - U t < 0 := by
  obtain ⟨b, hb, h⟩ := local_boolean_snapping t
  refine ⟨b, hb, h, ?_⟩
  have hpos : 0 < ‖t - b‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    rcases mem_booleanDomain.mp hb with rfl | rfl
    · exact ht.1
    · exact ht.2
  linarith

end Snapping

/-- Boolean embedding `s ↦ (if s j then 1 else 0)`. -/
noncomputable def embed (p : ℕ) [Fact p.Prime] {n : ℕ} (s : Fin n → Bool) : Fin n → ℚ_[p] :=
  fun j => if s j then 1 else 0

section MaxCut

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {ε : Type*} [Fintype ε]

/-- Degree of vertex `j`: the number of edges incident to `j`. -/
def deg (left right : ε → Fin n) (j : Fin n) : ℕ :=
  (Finset.univ.filter fun e => left e = j ∨ right e = j).card

/-- Forcing multiplicity `M_j = d_j + 1`. -/
def M (left right : ε → Fin n) (j : Fin n) : ℕ := deg left right j + 1

/-- The Max-Cut forcing objective
`L_p(β) = ∑ j, M_j (|β_j|_p + |β_j - 1|_p) + ∑ (u,v) ∈ E, |β_u + β_v - 1|_p`. -/
noncomputable def maxCutLoss (left right : ε → Fin n) (β : Fin n → ℚ_[p]) : ℝ :=
  ∑ j, (M left right j : ℝ) * U (β j) + ∑ e, ‖β (left e) + β (right e) - 1‖

theorem forcing_update (left right : ε → Fin n) (β : Fin n → ℚ_[p]) (j : Fin n)
    (b : ℚ_[p]) :
    ∑ i, (M left right i : ℝ) * U (Function.update β j b i) -
        ∑ i, (M left right i : ℝ) * U (β i) =
      (M left right j : ℝ) * (U b - U (β j)) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
  · simp only [Function.update_self]
    ring
  · intro i _ hij
    rw [Function.update_of_ne hij, sub_self]
  · intro h
    exact absurd (Finset.mem_univ j) h

omit [Fintype ε] in
/-- Snapping coordinate `j` changes an incident edge term by at most
`‖β j - b‖` (reverse triangle inequality) and a non-incident one not at all. -/
theorem edge_update_le (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    (β : Fin n → ℚ_[p]) (j : Fin n) (b : ℚ_[p]) (e : ε) :
    ‖Function.update β j b (left e) + Function.update β j b (right e) - 1‖ -
        ‖β (left e) + β (right e) - 1‖ ≤
      if left e = j ∨ right e = j then ‖β j - b‖ else 0 := by
  split_ifs with h
  · have hdiff :
        (Function.update β j b (left e) + Function.update β j b (right e) - 1) -
          (β (left e) + β (right e) - 1) = b - β j := by
      rcases h with h | h
      · have hr : right e ≠ j := fun hr => hne e (h.trans hr.symm)
        rw [h, Function.update_self, Function.update_of_ne hr]
        ring
      · have hl : left e ≠ j := fun hl => hne e (hl.trans h.symm)
        rw [h, Function.update_self, Function.update_of_ne hl]
        ring
    calc ‖Function.update β j b (left e) + Function.update β j b (right e) - 1‖ -
          ‖β (left e) + β (right e) - 1‖
        ≤ ‖(Function.update β j b (left e) + Function.update β j b (right e) - 1) -
            (β (left e) + β (right e) - 1)‖ := norm_sub_norm_le _ _
      _ = ‖β j - b‖ := by rw [hdiff, norm_sub_rev]
  · push_neg at h
    simp [Function.update_of_ne h.1, Function.update_of_ne h.2]

theorem edges_update_le (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    (β : Fin n → ℚ_[p]) (j : Fin n) (b : ℚ_[p]) :
    ∑ e, ‖Function.update β j b (left e) + Function.update β j b (right e) - 1‖ -
        ∑ e, ‖β (left e) + β (right e) - 1‖ ≤
      (deg left right j : ℝ) * ‖β j - b‖ := by
  rw [← Finset.sum_sub_distrib]
  calc ∑ e, (‖Function.update β j b (left e) + Function.update β j b (right e) - 1‖ -
          ‖β (left e) + β (right e) - 1‖)
      ≤ ∑ e, (if left e = j ∨ right e = j then ‖β j - b‖ else 0) :=
        Finset.sum_le_sum fun e _ => edge_update_le left right hne β j b e
    _ = (deg left right j : ℝ) * ‖β j - b‖ := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rfl

/-- Snapping coordinate `j` to a Boolean value satisfying the local snapping
inequality lowers the objective by at least `‖β j - b‖`. -/
theorem maxCutLoss_update_le (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    (β : Fin n → ℚ_[p]) (j : Fin n) {b : ℚ_[p]} (hb : U b - U (β j) ≤ -‖β j - b‖) :
    maxCutLoss left right (Function.update β j b) ≤
      maxCutLoss left right β - ‖β j - b‖ := by
  have h1 := forcing_update left right β j b
  have h2 := edges_update_le left right hne β j b
  have h3 : (M left right j : ℝ) * (U b - U (β j)) ≤
      -((deg left right j : ℝ) * ‖β j - b‖) - ‖β j - b‖ := by
    calc (M left right j : ℝ) * (U b - U (β j))
        ≤ (M left right j : ℝ) * (-‖β j - b‖) :=
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = -((deg left right j : ℝ) * ‖β j - b‖) - ‖β j - b‖ := by
          rw [M]
          push_cast
          ring
  unfold maxCutLoss
  linarith

/-- Any non-Boolean coordinate can be snapped to a Boolean value with a strict
decrease of the objective. -/
theorem snap_lt (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    (β : Fin n → ℚ_[p]) (j : Fin n) (hj : β j ≠ 0 ∧ β j ≠ 1) :
    ∃ b ∈ booleanDomain p,
      maxCutLoss left right (Function.update β j b) < maxCutLoss left right β := by
  obtain ⟨b, hb, hU⟩ := local_boolean_snapping (β j)
  refine ⟨b, hb, ?_⟩
  have hpos : 0 < ‖β j - b‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    rcases mem_booleanDomain.mp hb with rfl | rfl
    · exact hj.1
    · exact hj.2
  have h := maxCutLoss_update_le left right hne β j hU
  linarith

/-- Every global minimiser of the Max-Cut objective is Boolean. -/
theorem globalMin_boolean (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    {β : Fin n → ℚ_[p]} (hmin : IsGlobalMin (maxCutLoss left right) β) :
    ∀ j, β j = 0 ∨ β j = 1 := by
  intro j
  by_contra h
  push_neg at h
  obtain ⟨b, _, hlt⟩ := snap_lt left right hne β j h
  exact absurd (hmin (Function.update β j b)) (not_le.mpr hlt)

theorem U_embed (s : Fin n → Bool) (j : Fin n) : U (embed p s j) = 1 := by
  unfold embed
  cases hs : s j <;> simp [U]

omit [Fintype ε] in
/-- The edge residual of a Boolean embedding has norm `1` on monochromatic
edges and `0` on bichromatic ones. -/
theorem norm_edge_embed (left right : ε → Fin n) (s : Fin n → Bool) (e : ε) :
    ‖embed p s (left e) + embed p s (right e) - 1‖ =
      if s (left e) = s (right e) then 1 else 0 := by
  unfold embed
  cases hl : s (left e) <;> cases hr : s (right e) <;> simp

/-- Number of monochromatic edges of the two-colouring `s`. -/
def monochromatic (left right : ε → Fin n) (s : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun e => s (left e) = s (right e)).card

/-- Cut size (number of bichromatic edges) of the two-colouring `s`. -/
def cutSize (left right : ε → Fin n) (s : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun e => s (left e) ≠ s (right e)).card

theorem monochromatic_add_cutSize (left right : ε → Fin n) (s : Fin n → Bool) :
    monochromatic left right s + cutSize left right s = Fintype.card ε := by
  unfold monochromatic cutSize
  rw [← Finset.card_univ]
  exact Finset.card_filter_add_card_filter_not (fun e => s (left e) = s (right e))

/-- On Boolean points the objective is `∑ M_j` plus the number of
monochromatic edges. -/
theorem maxCutLoss_embed (left right : ε → Fin n) (s : Fin n → Bool) :
    maxCutLoss left right (embed p s) =
      (∑ j, (M left right j : ℝ)) + monochromatic left right s := by
  unfold maxCutLoss
  simp only [U_embed, mul_one, norm_edge_embed, Finset.sum_boole, monochromatic]

theorem exists_embed_of_boolean {β : Fin n → ℚ_[p]} (hβ : ∀ j, β j = 0 ∨ β j = 1) :
    ∃ s, β = embed p s := by
  classical
  refine ⟨fun j => decide (β j = 1), ?_⟩
  funext j
  rcases hβ j with h | h <;> simp [embed, h]

/-- Repeated snapping: every point is dominated by some Boolean embedding. -/
theorem exists_embed_le (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    (β : Fin n → ℚ_[p]) :
    ∃ s, maxCutLoss left right (embed p s) ≤ maxCutLoss left right β := by
  classical
  generalize hk : (outsideDomain (fun _ : Fin n => booleanDomain p) β).card = k
  induction k using Nat.strong_induction_on generalizing β with
  | h k ih =>
    by_cases hβ : ∀ j, β j = 0 ∨ β j = 1
    · obtain ⟨s, rfl⟩ := exists_embed_of_boolean hβ
      exact ⟨s, le_rfl⟩
    · push_neg at hβ
      obtain ⟨j, hj⟩ := hβ
      have hjmem : j ∈ outsideDomain (fun _ : Fin n => booleanDomain p) β := by
        simp [outsideDomain, mem_booleanDomain, hj.1, hj.2]
      obtain ⟨b, hb, hlt⟩ := snap_lt left right hne β j hj
      have hcard :
          (outsideDomain (fun _ : Fin n => booleanDomain p)
            (Function.update β j b)).card < k := by
        have hpos : 0 < (outsideDomain (fun _ : Fin n => booleanDomain p) β).card :=
          Finset.card_pos.mpr ⟨j, hjmem⟩
        rw [outsideDomain_update _ β j b hb, Finset.card_erase_of_mem hjmem, hk]
        omega
      obtain ⟨s, hs⟩ := ih _ hcard (Function.update β j b) rfl
      exact ⟨s, hs.trans hlt.le⟩

/-- The Max-Cut objective attains a global minimum. -/
theorem exists_globalMin (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e) :
    ∃ β : Fin n → ℚ_[p], IsGlobalMin (maxCutLoss left right) β := by
  classical
  obtain ⟨s₀, _, hs₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n → Bool))
    (fun s => maxCutLoss left right (embed p s)) ⟨fun _ => false, Finset.mem_univ _⟩
  refine ⟨embed p s₀, fun β => ?_⟩
  obtain ⟨s, hs⟩ := exists_embed_le left right hne β
  exact (hs₀ s (Finset.mem_univ _)).trans hs

/-- Maximum cut size of the graph. -/
def maxCut (left right : ε → Fin n) : ℕ := Finset.univ.sup (cutSize left right)

theorem cutSize_le_maxCut (left right : ε → Fin n) (s : Fin n → Bool) :
    cutSize left right s ≤ maxCut left right :=
  Finset.le_sup (f := cutSize left right) (Finset.mem_univ s)

theorem isMaxCut_iff (left right : ε → Fin n) (s : Fin n → Bool) :
    (∀ s', cutSize left right s' ≤ cutSize left right s) ↔
      cutSize left right s = maxCut left right := by
  constructor
  · intro h
    exact le_antisymm (cutSize_le_maxCut left right s)
      (Finset.sup_le fun s' _ => h s')
  · intro h s'
    rw [h]
    exact cutSize_le_maxCut left right s'

theorem exists_cutSize_eq_maxCut (left right : ε → Fin n) :
    ∃ s, cutSize left right s = maxCut left right := by
  obtain ⟨s, _, hs⟩ := Finset.exists_max_image Finset.univ (cutSize left right)
    ⟨fun _ => false, Finset.mem_univ _⟩
  exact ⟨s, (isMaxCut_iff left right s).mp fun s' => hs s' (Finset.mem_univ _)⟩

theorem maxCut_le_card (left right : ε → Fin n) : maxCut left right ≤ Fintype.card ε := by
  obtain ⟨s, hs⟩ := exists_cutSize_eq_maxCut left right
  rw [← hs, ← monochromatic_add_cutSize left right s]
  exact Nat.le_add_left _ _

/-- Comparing two Boolean points compares their cut sizes (reversed). -/
theorem maxCutLoss_embed_le_iff (left right : ε → Fin n) (s s' : Fin n → Bool) :
    maxCutLoss left right (embed p s) ≤ maxCutLoss left right (embed p s') ↔
      cutSize left right s' ≤ cutSize left right s := by
  rw [maxCutLoss_embed, maxCutLoss_embed]
  have h1 := monochromatic_add_cutSize left right s
  have h2 := monochromatic_add_cutSize left right s'
  constructor
  · intro h
    have hreal : (monochromatic left right s : ℝ) ≤ monochromatic left right s' := by
      linarith
    have hnat : monochromatic left right s ≤ monochromatic left right s' := by
      exact_mod_cast hreal
    omega
  · intro h
    have hnat : monochromatic left right s ≤ monochromatic left right s' := by omega
    have hreal : (monochromatic left right s : ℝ) ≤ monochromatic left right s' := by
      exact_mod_cast hnat
    linarith

/-- Characterisation of global minimisers: exactly the Boolean embeddings of
maximum cuts. -/
theorem isGlobalMin_iff (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    (β : Fin n → ℚ_[p]) :
    IsGlobalMin (maxCutLoss left right) β ↔
      ∃ s, β = embed p s ∧ ∀ s', cutSize left right s' ≤ cutSize left right s := by
  constructor
  · intro hmin
    obtain ⟨s, rfl⟩ := exists_embed_of_boolean (globalMin_boolean left right hne hmin)
    exact ⟨s, rfl, fun s' => (maxCutLoss_embed_le_iff left right s s').mp (hmin (embed p s'))⟩
  · rintro ⟨s, rfl, hs⟩ γ
    obtain ⟨s', hs'⟩ := exists_embed_le left right hne γ
    exact ((maxCutLoss_embed_le_iff left right s s').mpr (hs s')).trans hs'

theorem isGlobalMin_iff_maxCut (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    (β : Fin n → ℚ_[p]) :
    IsGlobalMin (maxCutLoss left right) β ↔
      ∃ s, β = embed p s ∧ cutSize left right s = maxCut left right := by
  rw [isGlobalMin_iff left right hne]
  simp only [isMaxCut_iff]

/-- The optimal value is `∑ M_j + |E| - maxCut`. -/
theorem maxCutLoss_globalMin_eq (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    {β : Fin n → ℚ_[p]} (hmin : IsGlobalMin (maxCutLoss left right) β) :
    maxCutLoss left right β =
      (∑ j, (M left right j : ℝ)) + Fintype.card ε - maxCut left right := by
  obtain ⟨s, rfl, hs⟩ := (isGlobalMin_iff_maxCut left right hne β).mp hmin
  rw [maxCutLoss_embed, ← hs]
  have h : (monochromatic left right s : ℝ) + cutSize left right s = Fintype.card ε := by
    exact_mod_cast monochromatic_add_cutSize left right s
  linarith

/-- Thesis `thm:fixed-prime-hardness` (semantic content, any prime `p`):
the Max-Cut forcing objective attains its minimum, every minimiser is Boolean,
the minimisers are exactly the embeddings of maximum cuts, the optimal value is
`∑ M_j + |E| - maxCut`, and on Boolean points the value is
`∑ M_j + (number of monochromatic edges)`. -/
theorem fixed_prime_hardness (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e) :
    (∃ β : Fin n → ℚ_[p], IsGlobalMin (maxCutLoss left right) β) ∧
    (∀ β : Fin n → ℚ_[p], IsGlobalMin (maxCutLoss left right) β →
      ∀ j, β j = 0 ∨ β j = 1) ∧
    (∀ β : Fin n → ℚ_[p], IsGlobalMin (maxCutLoss left right) β ↔
      ∃ s, β = embed p s ∧ ∀ s', cutSize left right s' ≤ cutSize left right s) ∧
    (∀ β : Fin n → ℚ_[p], IsGlobalMin (maxCutLoss left right) β →
      maxCutLoss left right β =
        (∑ j, (M left right j : ℝ)) + Fintype.card ε - maxCut left right) ∧
    (∀ s : Fin n → Bool, maxCutLoss left right (embed p s) =
      (∑ j, (M left right j : ℝ)) + monochromatic left right s) :=
  ⟨exists_globalMin left right hne,
    fun _ hmin => globalMin_boolean left right hne hmin,
    isGlobalMin_iff left right hne,
    fun _ hmin => maxCutLoss_globalMin_eq left right hne hmin,
    maxCutLoss_embed left right⟩

end MaxCut

section Regression

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- An integral regression row `(x, y)` with `x ∈ ℤ^n`, `y ∈ ℤ`. -/
abbrev Row (n : ℕ) := (Fin n → ℤ) × ℤ

/-- Homogeneous summed `p`-adic regression loss `∑ i, |y_i - x_iᵀ β|_p`. -/
noncomputable def homogeneousLoss {ι : Type*} [Fintype ι] (rows : ι → Row n)
    (β : Fin n → ℚ_[p]) : ℝ :=
  ∑ i, ‖((rows i).2 : ℚ_[p]) - ∑ j, ((rows i).1 j : ℚ_[p]) * β j‖

/-- The forcing row `(e_j, t)`. -/
def unitRow (j : Fin n) (t : ℤ) : Row n := (fun k => if k = j then 1 else 0, t)

/-- The edge row `(e_u + e_v, 1)` for the edge `e = (u, v)`. -/
def edgeRow {ε : Type*} (left right : ε → Fin n) (e : ε) : Row n :=
  (fun k => if k = left e ∨ k = right e then 1 else 0, 1)

theorem unitRow_residual (j : Fin n) (t : ℤ) (β : Fin n → ℚ_[p]) :
    ((unitRow j t).2 : ℚ_[p]) - ∑ k, ((unitRow j t).1 k : ℚ_[p]) * β k =
      (t : ℚ_[p]) - β j := by
  simp [unitRow, Int.cast_ite]

theorem norm_unitRow_residual (j : Fin n) (t : ℤ) (β : Fin n → ℚ_[p]) :
    ‖((unitRow j t).2 : ℚ_[p]) - ∑ k, ((unitRow j t).1 k : ℚ_[p]) * β k‖ =
      ‖β j - t‖ := by
  rw [unitRow_residual, norm_sub_rev]

theorem edgeRow_residual {ε : Type*} (left right : ε → Fin n)
    (hne : ∀ e, left e ≠ right e) (e : ε) (β : Fin n → ℚ_[p]) :
    ((edgeRow left right e).2 : ℚ_[p]) -
        ∑ k, ((edgeRow left right e).1 k : ℚ_[p]) * β k =
      1 - (β (left e) + β (right e)) := by
  have hsum : (∑ k, ((edgeRow left right e).1 k : ℚ_[p]) * β k) =
      β (left e) + β (right e) := by
    rw [Fintype.sum_eq_add (left e) (right e) (hne e)]
    · simp [edgeRow]
    · intro k ⟨hk1, hk2⟩
      simp [edgeRow, hk1, hk2]
  rw [hsum]
  simp [edgeRow]

theorem norm_edgeRow_residual {ε : Type*} (left right : ε → Fin n)
    (hne : ∀ e, left e ≠ right e) (e : ε) (β : Fin n → ℚ_[p]) :
    ‖((edgeRow left right e).2 : ℚ_[p]) -
        ∑ k, ((edgeRow left right e).1 k : ℚ_[p]) * β k‖ =
      ‖β (left e) + β (right e) - 1‖ := by
  rw [edgeRow_residual left right hne, norm_sub_rev]

/-- Row index type of the Max-Cut instance: `M_j` copies of `(e_j, 0)`, `M_j`
copies of `(e_j, 1)`, and one edge row per edge. -/
abbrev MaxCutIndex {ε : Type*} [Fintype ε] (left right : ε → Fin n) :=
  (Σ j : Fin n, Fin (M left right j)) ⊕ ((Σ j : Fin n, Fin (M left right j)) ⊕ ε)

/-- The explicit integral regression instance of the Max-Cut reduction. -/
def maxCutRows {ε : Type*} [Fintype ε] (left right : ε → Fin n) :
    MaxCutIndex left right → Row n
  | Sum.inl ⟨j, _⟩ => unitRow j 0
  | Sum.inr (Sum.inl ⟨j, _⟩) => unitRow j 1
  | Sum.inr (Sum.inr e) => edgeRow left right e

/-- Fidelity to the problem definition: the homogeneous summed regression loss
of `maxCutRows` is exactly the forcing objective `maxCutLoss`. -/
theorem homogeneousLoss_maxCutRows {ε : Type*} [Fintype ε] (left right : ε → Fin n)
    (hne : ∀ e, left e ≠ right e) (β : Fin n → ℚ_[p]) :
    homogeneousLoss (maxCutRows left right) β = maxCutLoss left right β := by
  unfold homogeneousLoss maxCutLoss
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
  simp only [maxCutRows, norm_unitRow_residual, norm_edgeRow_residual left right hne,
    Int.cast_zero, Int.cast_one, sub_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, U, mul_add, Finset.sum_add_distrib]
  ring

theorem card_maxCutIndex {ε : Type*} [Fintype ε] (left right : ε → Fin n) :
    Fintype.card (MaxCutIndex left right) = 2 * ∑ j, M left right j + Fintype.card ε := by
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  ring

/-- Handshake lemma for the loopless edge family. -/
theorem sum_deg {ε : Type*} [Fintype ε] (left right : ε → Fin n)
    (hne : ∀ e, left e ≠ right e) :
    ∑ j, deg left right j = 2 * Fintype.card ε := by
  unfold deg
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have h : ∀ e, (∑ j, if left e = j ∨ right e = j then 1 else 0) = 2 := by
    intro e
    rw [← Finset.card_filter]
    have hset : (Finset.univ.filter fun j => left e = j ∨ right e = j) =
        {left e, right e} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact or_congr eq_comm eq_comm
    rw [hset, Finset.card_pair (hne e)]
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

theorem sum_M {ε : Type*} [Fintype ε] (left right : ε → Fin n)
    (hne : ∀ e, left e ≠ right e) :
    ∑ j, M left right j = 2 * Fintype.card ε + n := by
  have hM : ∑ j, M left right j = ∑ j, deg left right j + n := by
    simp only [M, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
  rw [hM, sum_deg left right hne]

/-- Row count of the homogeneous Max-Cut instance: `5|E| + 2n`. -/
theorem card_maxCutIndex_eq {ε : Type*} [Fintype ε] (left right : ε → Fin n)
    (hne : ∀ e, left e ≠ right e) :
    Fintype.card (MaxCutIndex left right) = 5 * Fintype.card ε + 2 * n := by
  rw [card_maxCutIndex, sum_M left right hne]
  ring

/-- Every coefficient of the Max-Cut instance is `0` or `1`. -/
theorem maxCutRows_coeff_mem {ε : Type*} [Fintype ε] (left right : ε → Fin n)
    (i : MaxCutIndex left right) (k : Fin n) :
    (maxCutRows left right i).1 k = 0 ∨ (maxCutRows left right i).1 k = 1 := by
  rcases i with ⟨j, _⟩ | ⟨j, _⟩ | e
  · by_cases hk : k = j <;> simp [maxCutRows, unitRow, hk]
  · by_cases hk : k = j <;> simp [maxCutRows, unitRow, hk]
  · by_cases hk : k = left e ∨ k = right e <;> simp [maxCutRows, edgeRow, hk]

/-- Every target of the Max-Cut instance is `0` or `1`. -/
theorem maxCutRows_target_mem {ε : Type*} [Fintype ε] (left right : ε → Fin n)
    (i : MaxCutIndex left right) :
    (maxCutRows left right i).2 = 0 ∨ (maxCutRows left right i).2 = 1 := by
  rcases i with ⟨j, _⟩ | ⟨j, _⟩ | e <;> simp [maxCutRows, unitRow, edgeRow]

/-! ### Intercept pinning -/

/-- Affine loss of an instance augmented with `T` pinning rows `(0, 0)`:
`L_aff(β, c) = T |c|_p + ∑ i, |y_i - x_iᵀ β - c|_p`. -/
noncomputable def affineLoss {ι : Type*} [Fintype ι] (rows : ι → Row n) (T : ℕ)
    (β : Fin n → ℚ_[p]) (c : ℚ_[p]) : ℝ :=
  (T : ℝ) * ‖c‖ + ∑ i, ‖((rows i).2 : ℚ_[p]) - ∑ j, ((rows i).1 j : ℚ_[p]) * β j - c‖

/-- Plain affine (intercept-model) loss of a row family. -/
noncomputable def affineRowLoss {ι : Type*} [Fintype ι] (rows : ι → Row n)
    (β : Fin n → ℚ_[p]) (c : ℚ_[p]) : ℝ :=
  ∑ i, ‖((rows i).2 : ℚ_[p]) - ∑ j, ((rows i).1 j : ℚ_[p]) * β j - c‖

/-- The pinning row `(0, 0)`. -/
def zeroRow (n : ℕ) : Row n := (fun _ => 0, 0)

/-- The row family with `T` pinning rows appended. -/
def pinnedRows {ι : Type*} (rows : ι → Row n) (T : ℕ) : ι ⊕ Fin T → Row n
  | Sum.inl i => rows i
  | Sum.inr _ => zeroRow n

/-- The `T ‖c‖` term of `affineLoss` is literally `T` appended rows `(0, 0)`. -/
theorem affineRowLoss_pinnedRows {ι : Type*} [Fintype ι] (rows : ι → Row n) (T : ℕ)
    (β : Fin n → ℚ_[p]) (c : ℚ_[p]) :
    affineRowLoss (pinnedRows rows T) β c = affineLoss rows T β c := by
  unfold affineRowLoss affineLoss
  rw [Fintype.sum_sum_type]
  simp only [pinnedRows, zeroRow, Int.cast_zero, zero_mul, Finset.sum_const_zero, sub_zero,
    zero_sub, norm_neg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The `c = 0` slice of the affine loss is the homogeneous loss. -/
theorem affineLoss_zero {ι : Type*} [Fintype ι] (rows : ι → Row n) (T : ℕ)
    (β : Fin n → ℚ_[p]) :
    affineLoss rows T β 0 = homogeneousLoss rows β := by
  simp [affineLoss, homogeneousLoss]

/-- Thesis `lem:intercept-pinning` (main inequality), proved for every `T`:
`L_aff(β, 0) ≤ L_aff(β, c) - (T - r) |c|_p`. -/
theorem intercept_pinning {ι : Type*} [Fintype ι] (rows : ι → Row n) (T : ℕ)
    (β : Fin n → ℚ_[p]) (c : ℚ_[p]) :
    affineLoss rows T β 0 ≤
      affineLoss rows T β c - ((T : ℝ) - Fintype.card ι) * ‖c‖ := by
  rw [affineLoss_zero]
  unfold homogeneousLoss affineLoss
  have key : ∀ a : ℚ_[p], ‖a‖ ≤ ‖a - c‖ + ‖c‖ := fun a => by
    calc ‖a‖ = ‖a - c + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖a - c‖ + ‖c‖ := norm_add_le _ _
  have hsum :
      ∑ i, ‖((rows i).2 : ℚ_[p]) - ∑ j, ((rows i).1 j : ℚ_[p]) * β j‖ ≤
        ∑ i, (‖((rows i).2 : ℚ_[p]) - ∑ j, ((rows i).1 j : ℚ_[p]) * β j - c‖ + ‖c‖) :=
    Finset.sum_le_sum fun i _ => key _
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  linarith

/-- With `T ≥ r + 1`, no affine model with `c ≠ 0` is optimal. -/
theorem affineLoss_zero_lt {ι : Type*} [Fintype ι] (rows : ι → Row n) {T : ℕ}
    (hT : Fintype.card ι + 1 ≤ T) (β : Fin n → ℚ_[p]) {c : ℚ_[p]} (hc : c ≠ 0) :
    affineLoss rows T β 0 < affineLoss rows T β c := by
  have h := intercept_pinning rows T β c
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hT' : (1 : ℝ) ≤ (T : ℝ) - Fintype.card ι := by
    have hcast : ((Fintype.card ι + 1 : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    push_cast at hcast
    linarith
  have hprod : 1 * ‖c‖ ≤ ((T : ℝ) - Fintype.card ι) * ‖c‖ :=
    mul_le_mul_of_nonneg_right hT' hc'.le
  linarith

/-- With `T ≥ r + 1`, the affine global minimisers are exactly the pairs
`(β, 0)` with `β` a homogeneous global minimiser. -/
theorem isGlobalMin_affine_iff {ι : Type*} [Fintype ι] (rows : ι → Row n) {T : ℕ}
    (hT : Fintype.card ι + 1 ≤ T) (β : Fin n → ℚ_[p]) (c : ℚ_[p]) :
    IsGlobalMin (fun bc : (Fin n → ℚ_[p]) × ℚ_[p] => affineLoss rows T bc.1 bc.2) (β, c) ↔
      c = 0 ∧ IsGlobalMin (homogeneousLoss rows) β := by
  constructor
  · intro hmin
    have hc : c = 0 := by
      by_contra hc
      have h1 : affineLoss rows T β c ≤ affineLoss rows T β 0 := hmin (β, 0)
      exact absurd (affineLoss_zero_lt rows hT β hc) (not_lt.mpr h1)
    subst hc
    refine ⟨rfl, fun β' => ?_⟩
    have h1 : affineLoss rows T β 0 ≤ affineLoss rows T β' 0 := hmin (β', 0)
    rwa [affineLoss_zero, affineLoss_zero] at h1
  · rintro ⟨rfl, hmin⟩ ⟨β', c'⟩
    show affineLoss rows T β 0 ≤ affineLoss rows T β' c'
    have hcard : (Fintype.card ι : ℝ) ≤ T := by
      exact_mod_cast (by omega : Fintype.card ι ≤ T)
    have hnonneg : 0 ≤ ((T : ℝ) - Fintype.card ι) * ‖c'‖ :=
      mul_nonneg (by linarith) (norm_nonneg _)
    have h := intercept_pinning rows T β' c'
    calc affineLoss rows T β 0 = homogeneousLoss rows β := affineLoss_zero rows T β
      _ ≤ homogeneousLoss rows β' := hmin β'
      _ = affineLoss rows T β' 0 := (affineLoss_zero rows T β').symm
      _ ≤ affineLoss rows T β' c' := by linarith

/-- The optimal affine value equals the optimal homogeneous value. -/
theorem affineLoss_globalMin_eq {ι : Type*} [Fintype ι] (rows : ι → Row n) {T : ℕ}
    (hT : Fintype.card ι + 1 ≤ T) {β : Fin n → ℚ_[p]} {c : ℚ_[p]}
    (hmin : IsGlobalMin
      (fun bc : (Fin n → ℚ_[p]) × ℚ_[p] => affineLoss rows T bc.1 bc.2) (β, c)) :
    affineLoss rows T β c = homogeneousLoss rows β := by
  obtain ⟨rfl, _⟩ := (isGlobalMin_affine_iff rows hT β c).mp hmin
  exact affineLoss_zero rows T β

/-! ### Affine hardness for the Max-Cut instance -/

/-- Number of pinning rows for the Max-Cut instance: `(number of rows) + 1`. -/
def pinningCount {ε : Type*} [Fintype ε] (left right : ε → Fin n) : ℕ :=
  Fintype.card (MaxCutIndex left right) + 1

theorem card_add_one_le_pinningCount {ε : Type*} [Fintype ε] (left right : ε → Fin n) :
    Fintype.card (MaxCutIndex left right) + 1 ≤ pinningCount left right :=
  le_rfl

/-- Affine loss of the pinned Max-Cut instance. -/
noncomputable def affineMaxCutLoss {ε : Type*} [Fintype ε] (left right : ε → Fin n)
    (β : Fin n → ℚ_[p]) (c : ℚ_[p]) : ℝ :=
  affineLoss (maxCutRows left right) (pinningCount left right) β c

theorem homogeneousLoss_maxCutRows_eq {ε : Type*} [Fintype ε] (left right : ε → Fin n)
    (hne : ∀ e, left e ≠ right e) :
    homogeneousLoss (p := p) (maxCutRows left right) = maxCutLoss (p := p) left right :=
  funext (homogeneousLoss_maxCutRows left right hne)

/-- Thesis `cor:affine-hardness` (characterisation): the affine global
minimisers of the pinned Max-Cut instance are exactly `(embed s, 0)` with `s` a
maximum cut. -/
theorem affine_hardness_iff {ε : Type*} [Fintype ε] (left right : ε → Fin n)
    (hne : ∀ e, left e ≠ right e) (β : Fin n → ℚ_[p]) (c : ℚ_[p]) :
    IsGlobalMin
        (fun bc : (Fin n → ℚ_[p]) × ℚ_[p] => affineMaxCutLoss left right bc.1 bc.2) (β, c) ↔
      c = 0 ∧ ∃ s, β = embed p s ∧ ∀ s', cutSize left right s' ≤ cutSize left right s := by
  refine (isGlobalMin_affine_iff (maxCutRows left right)
    (card_add_one_le_pinningCount left right) β c).trans ?_
  rw [homogeneousLoss_maxCutRows_eq left right hne, isGlobalMin_iff left right hne]

/-- The pinned Max-Cut instance attains its affine minimum. -/
theorem exists_affine_globalMin {ε : Type*} [Fintype ε] (left right : ε → Fin n)
    (hne : ∀ e, left e ≠ right e) :
    ∃ bc : (Fin n → ℚ_[p]) × ℚ_[p], IsGlobalMin
      (fun bc : (Fin n → ℚ_[p]) × ℚ_[p] => affineMaxCutLoss left right bc.1 bc.2) bc := by
  obtain ⟨β, hβ⟩ := exists_globalMin (p := p) left right hne
  exact ⟨(β, 0), (affine_hardness_iff left right hne β 0).mpr
    ⟨rfl, (isGlobalMin_iff left right hne β).mp hβ⟩⟩

/-- Thesis `cor:affine-hardness` (optimal value): the affine optimum of the
pinned Max-Cut instance is `∑ M_j + |E| - maxCut`. -/
theorem affine_hardness_value {ε : Type*} [Fintype ε] (left right : ε → Fin n)
    (hne : ∀ e, left e ≠ right e) {β : Fin n → ℚ_[p]} {c : ℚ_[p]}
    (hmin : IsGlobalMin
      (fun bc : (Fin n → ℚ_[p]) × ℚ_[p] => affineMaxCutLoss left right bc.1 bc.2) (β, c)) :
    affineMaxCutLoss left right β c =
      (∑ j, (M left right j : ℝ)) + Fintype.card ε - maxCut left right := by
  obtain ⟨rfl, hβ⟩ := (isGlobalMin_affine_iff (maxCutRows left right)
    (card_add_one_le_pinningCount left right) β c).mp hmin
  rw [homogeneousLoss_maxCutRows_eq left right hne] at hβ
  show affineLoss (maxCutRows left right) (pinningCount left right) β 0 = _
  rw [affineLoss_zero, homogeneousLoss_maxCutRows left right hne]
  exact maxCutLoss_globalMin_eq left right hne hβ

/-- Row count of the pinned (affine) Max-Cut instance: `10|E| + 4n + 1`. -/
theorem card_pinned_maxCutIndex {ε : Type*} [Fintype ε] (left right : ε → Fin n)
    (hne : ∀ e, left e ≠ right e) :
    Fintype.card (MaxCutIndex left right ⊕ Fin (pinningCount left right)) =
      10 * Fintype.card ε + 4 * n + 1 := by
  rw [Fintype.card_sum, Fintype.card_fin, pinningCount, card_maxCutIndex_eq left right hne]
  ring

/-- Thesis `cor:affine-hardness` (semantic content, any prime `p`): the pinned
Max-Cut instance attains its affine minimum, its minimisers are exactly the
pairs `(embed s, 0)` with `s` a maximum cut, and the optimal value is
`∑ M_j + |E| - maxCut`. -/
theorem affine_hardness {ε : Type*} [Fintype ε] (left right : ε → Fin n)
    (hne : ∀ e, left e ≠ right e) :
    (∃ bc : (Fin n → ℚ_[p]) × ℚ_[p], IsGlobalMin
      (fun bc : (Fin n → ℚ_[p]) × ℚ_[p] => affineMaxCutLoss left right bc.1 bc.2) bc) ∧
    (∀ (β : Fin n → ℚ_[p]) (c : ℚ_[p]),
      IsGlobalMin
          (fun bc : (Fin n → ℚ_[p]) × ℚ_[p] => affineMaxCutLoss left right bc.1 bc.2) (β, c) ↔
        c = 0 ∧ ∃ s, β = embed p s ∧ ∀ s', cutSize left right s' ≤ cutSize left right s) ∧
    (∀ (β : Fin n → ℚ_[p]) (c : ℚ_[p]),
      IsGlobalMin
          (fun bc : (Fin n → ℚ_[p]) × ℚ_[p] => affineMaxCutLoss left right bc.1 bc.2) (β, c) →
        affineMaxCutLoss left right β c =
          (∑ j, (M left right j : ℝ)) + Fintype.card ε - maxCut left right) :=
  ⟨exists_affine_globalMin left right hne,
    affine_hardness_iff left right hne,
    fun _ _ hmin => affine_hardness_value left right hne hmin⟩

end Regression

end PhdThesisLean.FixedPrimeMaxCut

#print axioms PhdThesisLean.FixedPrimeMaxCut.local_boolean_snapping
#print axioms PhdThesisLean.FixedPrimeMaxCut.local_boolean_snapping_of_ne
#print axioms PhdThesisLean.FixedPrimeMaxCut.snap_lt
#print axioms PhdThesisLean.FixedPrimeMaxCut.globalMin_boolean
#print axioms PhdThesisLean.FixedPrimeMaxCut.maxCutLoss_embed
#print axioms PhdThesisLean.FixedPrimeMaxCut.exists_globalMin
#print axioms PhdThesisLean.FixedPrimeMaxCut.isGlobalMin_iff
#print axioms PhdThesisLean.FixedPrimeMaxCut.maxCutLoss_globalMin_eq
#print axioms PhdThesisLean.FixedPrimeMaxCut.fixed_prime_hardness
#print axioms PhdThesisLean.FixedPrimeMaxCut.homogeneousLoss_maxCutRows
#print axioms PhdThesisLean.FixedPrimeMaxCut.card_maxCutIndex_eq
#print axioms PhdThesisLean.FixedPrimeMaxCut.sum_deg
#print axioms PhdThesisLean.FixedPrimeMaxCut.maxCutRows_coeff_mem
#print axioms PhdThesisLean.FixedPrimeMaxCut.maxCutRows_target_mem
#print axioms PhdThesisLean.FixedPrimeMaxCut.affineRowLoss_pinnedRows
#print axioms PhdThesisLean.FixedPrimeMaxCut.intercept_pinning
#print axioms PhdThesisLean.FixedPrimeMaxCut.affineLoss_zero_lt
#print axioms PhdThesisLean.FixedPrimeMaxCut.isGlobalMin_affine_iff
#print axioms PhdThesisLean.FixedPrimeMaxCut.affine_hardness_iff
#print axioms PhdThesisLean.FixedPrimeMaxCut.affine_hardness_value
#print axioms PhdThesisLean.FixedPrimeMaxCut.card_pinned_maxCutIndex
#print axioms PhdThesisLean.FixedPrimeMaxCut.affine_hardness
