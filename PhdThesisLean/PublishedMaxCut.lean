import Mathlib.NumberTheory.Padics.RingHoms
import PhdThesisLean.FixedPrimeMaxCut

namespace PhdThesisLean.PublishedMaxCut

open scoped BigOperators
open PhdThesisLean.AllDifferent (IsGlobalMin)
open PhdThesisLean.FixedPrimeMaxCut (U U_zero U_one embed monochromatic cutSize maxCut U_embed
  norm_edge_embed monochromatic_add_cutSize exists_embed_of_boolean cutSize_le_maxCut
  isMaxCut_iff Row homogeneousLoss unitRow edgeRow norm_unitRow_residual
  norm_edgeRow_residual)

/-!
# The published `2`-adic Max-Cut reduction (`thm:main`)

This module formalises the published theorem `thm:main` ("`p`-adic linear
regression is NP-hard") of `padic-regression-complexity/body.tex`
(lines 125–420) in the thesis source tree `/Users/gregb/Documents/devel/phd-thesis`,
together with its four lemmas `lem:toobig`, `lem:binary`, `lem:magnitude` and
`lem:rounding`, the value formula `L(s) = M n + m - cutsize(s)` and the decision
form "`G` has a cut of size `≥ K` iff the instance admits `β` with
`L(β) ≤ M n + m - K`".

The thesis-only generalisation to every prime with the *local* multiplicities
`M_j = d_j + 1` lives in `PhdThesisLean/FixedPrimeMaxCut.lean`; this module is
the literal published construction at `p = 2` with the *uniform* multiplicity
`M = m + 1`, reusing the Boolean forcing cost `U`, the embedding `embed`, and the
cut-counting vocabulary (`cutSize`, `monochromatic`, `maxCut`) of that module.

## What is proved

* `binary_lemma` (`lem:binary`, any prime): `1 ≤ U a = ‖a‖ + ‖a - 1‖`, with
  equality iff `a ∈ {0, 1}` (`one_le_U`, `U_eq_one_iff`, `one_lt_U_of_ne`).
* `loss_zero_eq` and `not_optimal_of_ge` (`lem:toobig`): `L(0) = M n + m`, so a
  point with `L(β) ≥ M (n + 1)` is not a global minimiser (because `m < M`).
* `two_le_norm_of_one_lt`: `2`-adic norms are integer powers of `2`, so
  `1 < ‖x‖ → 2 ≤ ‖x‖`; `not_optimal_of_norm_gt_one` (`lem:magnitude`): if
  `1 < ‖β k‖` or `1 < ‖β k - 1‖` then `L(β) ≥ M (n + 1)` and `β` is not optimal;
  `optimal_coord_norm_le_one`: every coordinate of a global minimiser lies in
  `ℤ_2`.
* `round` is the thesis's `φ(x) = x mod 2` (as a Boolean, `true` iff
  `‖x - 1‖ < 1`); `norm_lt_one_or_norm_sub_one_lt_one` is the residue-field
  fact `ℤ_2 / 2ℤ_2 = {0, 1}`; `rounding_le` (`lem:rounding`): for
  `β ∈ ℤ_2^n`, `L(round β) ≤ L(β)`; `rounding_lt` sharpens this to a strict
  inequality when some coordinate is not Boolean, whence `globalMin_boolean`.
* `publishedLoss_embed`: `L(embed s) = M n + m - cutSize s`;
  `exists_boolean_globalMin`: a Boolean global minimiser exists;
  `isGlobalMin_iff`: the global minimisers are exactly the embeddings of maximum
  cuts; `optimal_value`: `L* = M n + m - maxCut`; `cut_ge_iff`: the decision form.
* `homogeneousLoss_publishedRows`: `publishedLoss` is literally the homogeneous
  summed `2`-adic regression loss of the explicit integral instance
  `publishedRows` (one edge row `(e_u + e_v, 1)` per edge, `M` copies each of
  `(e_j, 0)` and `(e_j, 1)` per vertex), with `r = m + 2 M n` rows
  (`card_publishedIndex`) and all data in `{0, 1}` (`publishedRows_coeff_mem`,
  `publishedRows_target_mem`).
* `published_main` bundles the four lemmas, the value formula, the existence of a
  Boolean optimum, the optimal value and the decision equivalence.

## Correspondence notes

* The parameter space is `ℚ_[2]^n`, strictly larger than the thesis's `ℚ^n`;
  every statement is proved for the larger space, so the thesis statements over
  `ℚ` are special cases. `lem:binary` is proved for every prime `p`.
* Edges are an arbitrary finite index type `ε` with endpoint maps
  `left right : ε → Fin n`, so multigraphs are covered; moreover no looplessness
  hypothesis is needed for the objective-level statements (a loop is never cut
  and always contributes `1` on Boolean points). The thesis's simple graph is a
  special case. Looplessness (`hne`) is used only to identify the edge *row*
  `(e_u + e_v, 1)` with the edge term in `homogeneousLoss_publishedRows`, exactly
  as in `FixedPrimeMaxCut.lean`.
* `lem:rounding` is stated in the thesis for `β ∈ ℤ_2^n`; here that is the
  hypothesis `∀ j, ‖β j‖ ≤ 1`, and `optimal_coord_norm_le_one` shows every
  global minimiser satisfies it.
* As in `FixedPrimeMaxCut.lean`, the NP-hardness *transfer* is external: Mathlib
  has no P/NP framework, so "Max-Cut is NP-hard" and "the map `G ↦ publishedRows`
  is polynomial-time computable" are not Lean premises. What is machine-checked
  is the complete reduction: the identification of the regression loss with the
  published objective, the four lemmas, the Boolean rounding, the exact value
  formula `L(s) = M n + m - cutsize(s)`, the optimal value, the decision
  equivalence, and the explicit row count and `{0, 1}` data bounds.
-/

section Binary

variable {p : ℕ} [Fact p.Prime]

/-- Ultrametric step of `lem:binary`: `1 = ‖a - (a - 1)‖ ≤ max ‖a‖ ‖a - 1‖`. -/
theorem one_le_max_norm (a : ℚ_[p]) : 1 ≤ max ‖a‖ ‖a - 1‖ := by
  calc (1 : ℝ) = ‖a + -(a - 1)‖ := by simp
    _ ≤ max ‖a‖ ‖-(a - 1)‖ := Padic.nonarchimedean _ _
    _ = max ‖a‖ ‖a - 1‖ := by rw [norm_neg]

/-- Thesis `lem:binary`, inequality: `|a|_p + |a - 1|_p ≥ 1`. -/
theorem one_le_U (a : ℚ_[p]) : 1 ≤ U a := by
  have h := one_le_max_norm a
  have h3 : max ‖a‖ ‖a - 1‖ ≤ ‖a‖ + ‖a - 1‖ :=
    max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  unfold U
  linarith

/-- Thesis `lem:binary`, equality case: `|a|_p + |a - 1|_p = 1 ↔ a ∈ {0, 1}`. -/
theorem U_eq_one_iff (a : ℚ_[p]) : U a = 1 ↔ a = 0 ∨ a = 1 := by
  constructor
  · intro h
    unfold U at h
    rcases le_max_iff.mp (one_le_max_norm a) with h1 | h1
    · right
      have h0 : ‖a - 1‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
      rwa [norm_eq_zero, sub_eq_zero] at h0
    · left
      have h0 : ‖a‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
      rwa [norm_eq_zero] at h0
  · rintro (rfl | rfl)
    · exact U_zero
    · exact U_one

/-- Thesis `lem:binary` (any prime): `|a|_p + |a - 1|_p ≥ 1`, with equality iff
`a ∈ {0, 1}`. -/
theorem binary_lemma (a : ℚ_[p]) : 1 ≤ U a ∧ (U a = 1 ↔ a = 0 ∨ a = 1) :=
  ⟨one_le_U a, U_eq_one_iff a⟩

/-- Strict form of `lem:binary`: a non-Boolean value has forcing cost `> 1`. -/
theorem one_lt_U_of_ne {a : ℚ_[p]} (ha : a ≠ 0 ∧ a ≠ 1) : 1 < U a := by
  refine lt_of_le_of_ne (one_le_U a) fun h => ?_
  rcases (U_eq_one_iff a).mp h.symm with h0 | h1
  · exact ha.1 h0
  · exact ha.2 h1

/-- Ultrametric: perturbing a norm-`1` element by something of norm `< 1` keeps
the norm equal to `1`. -/
theorem norm_add_eq_one_of_norm_lt_one {a d : ℚ_[p]} (ha : ‖a‖ = 1) (hd : ‖d‖ < 1) :
    ‖a + d‖ = 1 := by
  rw [Padic.add_eq_max_of_ne (by rw [ha]; exact hd.ne'), ha, max_eq_left hd.le]

end Binary

section TwoAdic

/-- `2`-adic norms are integer powers of `2`: there is no `x` with `1 < ‖x‖ < 2`
(the observation in the proof of `lem:magnitude`). -/
theorem two_le_norm_of_one_lt {x : ℚ_[2]} (hx : 1 < ‖x‖) : 2 ≤ ‖x‖ := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx
  have hval : x.valuation < 0 := by
    by_contra h
    push_neg at h
    exact absurd ((Padic.norm_le_one_iff_val_nonneg x).mpr h) (not_le.mpr hx)
  rw [Padic.norm_eq_zpow_neg_valuation hx0]
  have h1 : (1 : ℤ) ≤ -x.valuation := by omega
  calc (2 : ℝ) = ((2 : ℕ) : ℝ) ^ (1 : ℤ) := by norm_num
    _ ≤ ((2 : ℕ) : ℝ) ^ (-x.valuation) := zpow_le_zpow_right₀ (by norm_num) h1

/-- If `|x|_2 > 1` or `|x - 1|_2 > 1` then the forcing cost is at least `2`. -/
theorem two_le_U_of_one_lt {x : ℚ_[2]} (hx : 1 < ‖x‖ ∨ 1 < ‖x - 1‖) : 2 ≤ U x := by
  unfold U
  rcases hx with h | h
  · have := two_le_norm_of_one_lt h
    linarith [norm_nonneg (x - 1)]
  · have := two_le_norm_of_one_lt h
    linarith [norm_nonneg x]

/-- The residue field of `ℤ_2` is `{0, 1}`: every `2`-adic integer is within
distance `< 1` of `0` or of `1` (this is the thesis's `φ(x) = x mod 2`). -/
theorem norm_lt_one_or_norm_sub_one_lt_one {x : ℚ_[2]} (hx : ‖x‖ ≤ 1) :
    ‖x‖ < 1 ∨ ‖x - 1‖ < 1 := by
  obtain ⟨k, hk, hmem⟩ := PadicInt.exists_mem_range (⟨x, hx⟩ : ℤ_[2])
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def, PadicInt.coe_sub,
    PadicInt.coe_natCast] at hmem
  have hzx : ((⟨x, hx⟩ : ℤ_[2]) : ℚ_[2]) = x := rfl
  rw [hzx] at hmem
  interval_cases k
  · left
    simpa using hmem
  · right
    simpa using hmem

end TwoAdic

/-- The published uniform forcing multiplicity `M = m + 1`. -/
def M (ε : Type*) [Fintype ε] : ℕ := Fintype.card ε + 1

section Published

variable {n : ℕ} {ε : Type*} [Fintype ε]

theorem card_lt_M : Fintype.card ε < M ε := Nat.lt_succ_self _

theorem card_add_one_eq_M : (Fintype.card ε : ℝ) + 1 = M ε := by
  unfold M
  push_cast
  ring

theorem M_pos : (0 : ℝ) < M ε := Nat.cast_pos.mpr (Nat.succ_pos _)

/-- The published `2`-adic regression objective
`L(β) = M ∑ j, (|β_j|_2 + |β_j - 1|_2) + ∑ (u,v) ∈ E, |β_u + β_v - 1|_2`
with the uniform forcing multiplicity `M = m + 1`. -/
noncomputable def publishedLoss (left right : ε → Fin n) (β : Fin n → ℚ_[2]) : ℝ :=
  (M ε : ℝ) * ∑ j, U (β j) + ∑ e, ‖β (left e) + β (right e) - 1‖

theorem edgeSum_nonneg (left right : ε → Fin n) (β : Fin n → ℚ_[2]) :
    0 ≤ ∑ e, ‖β (left e) + β (right e) - 1‖ :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The forcing sum is at least `n` (`lem:binary` summed). -/
theorem card_le_sum_U (β : Fin n → ℚ_[2]) : (n : ℝ) ≤ ∑ j, U (β j) := by
  have h : ∑ _j : Fin n, (1 : ℝ) ≤ ∑ j, U (β j) :=
    Finset.sum_le_sum fun j _ => one_le_U (β j)
  simpa using h

/-- The forcing sum exceeds `n` by at least the excess `U (β k) - 1` of any one
coordinate. -/
theorem sum_U_ge (β : Fin n → ℚ_[2]) (k : Fin n) :
    (n : ℝ) + (U (β k) - 1) ≤ ∑ j, U (β j) := by
  have h : U (β k) - 1 ≤ ∑ j, (U (β j) - 1) :=
    Finset.single_le_sum (f := fun j => U (β j) - 1)
      (fun j _ => sub_nonneg.mpr (one_le_U (β j))) (Finset.mem_univ k)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  linarith

/-! ### `lem:toobig` -/

/-- The naive solution `β = 0` has loss `M n + m`. -/
theorem loss_zero_eq (left right : ε → Fin n) :
    publishedLoss left right 0 = (M ε : ℝ) * n + Fintype.card ε := by
  unfold publishedLoss
  simp [U_zero]

/-- Thesis `lem:toobig`: a point with loss `≥ M (n + 1)` is not optimal. -/
theorem not_optimal_of_ge (left right : ε → Fin n) {β : Fin n → ℚ_[2]}
    (h : (M ε : ℝ) * ((n : ℝ) + 1) ≤ publishedLoss left right β) :
    ¬ IsGlobalMin (publishedLoss left right) β := by
  intro hmin
  have h0 := hmin 0
  rw [loss_zero_eq] at h0
  have hM := card_add_one_eq_M (ε := ε)
  nlinarith

/-! ### `lem:magnitude` -/

/-- A coordinate of norm `> 1` (or at distance `> 1` from `1`) forces
`L(β) ≥ M (n + 1)`. -/
theorem loss_ge_of_norm_gt_one (left right : ε → Fin n) (β : Fin n → ℚ_[2]) (k : Fin n)
    (hk : 1 < ‖β k‖ ∨ 1 < ‖β k - 1‖) :
    (M ε : ℝ) * ((n : ℝ) + 1) ≤ publishedLoss left right β := by
  have h2 := two_le_U_of_one_lt hk
  have hsum := sum_U_ge β k
  have hedge := edgeSum_nonneg left right β
  have hM : (0 : ℝ) ≤ M ε := Nat.cast_nonneg _
  have hmul : (M ε : ℝ) * ((n : ℝ) + 1) ≤ (M ε : ℝ) * ∑ j, U (β j) :=
    mul_le_mul_of_nonneg_left (by linarith) hM
  unfold publishedLoss
  linarith

/-- Thesis `lem:magnitude`: if `|β_k|_2 > 1` or `|β_k - 1|_2 > 1` for some `k`,
then `β` is not an optimal solution. -/
theorem not_optimal_of_norm_gt_one (left right : ε → Fin n) {β : Fin n → ℚ_[2]} (k : Fin n)
    (hk : 1 < ‖β k‖ ∨ 1 < ‖β k - 1‖) :
    ¬ IsGlobalMin (publishedLoss left right) β :=
  not_optimal_of_ge left right (loss_ge_of_norm_gt_one left right β k hk)

/-- Consequence of `lem:magnitude`: every coordinate of a global minimiser is a
`2`-adic integer. -/
theorem optimal_coord_norm_le_one (left right : ε → Fin n) {β : Fin n → ℚ_[2]}
    (hmin : IsGlobalMin (publishedLoss left right) β) : ∀ j, ‖β j‖ ≤ 1 := by
  intro j
  by_contra h
  exact not_optimal_of_norm_gt_one left right j (Or.inl (not_le.mp h)) hmin

/-! ### `lem:rounding` -/

/-- The thesis rounding map `φ(x) = x mod 2`, as a Boolean: `true` iff
`x ≡ 1 (mod 2)`, i.e. `‖x - 1‖ < 1`. -/
noncomputable def round (β : Fin n → ℚ_[2]) (j : Fin n) : Bool :=
  decide (‖β j - 1‖ < 1)

theorem embed_round (β : Fin n → ℚ_[2]) (j : Fin n) :
    embed 2 (round β) j = if ‖β j - 1‖ < 1 then 1 else 0 := by
  by_cases h : ‖β j - 1‖ < 1 <;> simp [embed, round, h]

/-- For `β_j ∈ ℤ_2`, the rounded value is within distance `< 1` of `β_j`
(i.e. `β_j = s_j + 2 α_j` with `α_j ∈ ℤ_2`). -/
theorem norm_sub_embed_round_lt_one {β : Fin n → ℚ_[2]} (hβ : ∀ j, ‖β j‖ ≤ 1) (j : Fin n) :
    ‖β j - embed 2 (round β) j‖ < 1 := by
  rw [embed_round]
  split_ifs with h
  · exact h
  · rcases norm_lt_one_or_norm_sub_one_lt_one (hβ j) with h0 | h1
    · simpa using h0
    · exact absurd h1 h

theorem sum_U_embed (s : Fin n → Bool) : ∑ j, U (embed 2 s j) = (n : ℝ) := by
  simp [U_embed]

omit [Fintype ε] in
/-- Edge comparison in `lem:rounding`: for `β ∈ ℤ_2^n` and `s = round β`, each
edge residual of `s` is at most that of `β` (equal to `1` on monochromatic
edges, `0 ≤ anything` on bichromatic ones). -/
theorem edge_round_le (left right : ε → Fin n) {β : Fin n → ℚ_[2]} (hβ : ∀ j, ‖β j‖ ≤ 1)
    (e : ε) :
    ‖embed 2 (round β) (left e) + embed 2 (round β) (right e) - 1‖ ≤
      ‖β (left e) + β (right e) - 1‖ := by
  set s := round β with hs
  have hu := norm_sub_embed_round_lt_one hβ (left e)
  have hv := norm_sub_embed_round_lt_one hβ (right e)
  have hd : ‖(β (left e) - embed 2 s (left e)) + (β (right e) - embed 2 s (right e))‖ < 1 :=
    lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt hu hv)
  have hdecomp : β (left e) + β (right e) - 1 =
      (embed 2 s (left e) + embed 2 s (right e) - 1) +
        ((β (left e) - embed 2 s (left e)) + (β (right e) - embed 2 s (right e))) := by
    ring
  rw [norm_edge_embed]
  split_ifs with h
  · have h1 : ‖embed 2 s (left e) + embed 2 s (right e) - 1‖ = 1 := by
      rw [norm_edge_embed, if_pos h]
    rw [hdecomp, norm_add_eq_one_of_norm_lt_one h1 hd]
  · exact norm_nonneg _

theorem edges_round_le (left right : ε → Fin n) {β : Fin n → ℚ_[2]} (hβ : ∀ j, ‖β j‖ ≤ 1) :
    ∑ e, ‖embed 2 (round β) (left e) + embed 2 (round β) (right e) - 1‖ ≤
      ∑ e, ‖β (left e) + β (right e) - 1‖ :=
  Finset.sum_le_sum fun e _ => edge_round_le left right hβ e

/-- Thesis `lem:rounding`: for `β ∈ ℤ_2^n`, rounding each coordinate modulo `2`
does not increase the loss. -/
theorem rounding_le (left right : ε → Fin n) {β : Fin n → ℚ_[2]} (hβ : ∀ j, ‖β j‖ ≤ 1) :
    publishedLoss left right (embed 2 (round β)) ≤ publishedLoss left right β := by
  have hF : ∑ j, U (embed 2 (round β) j) ≤ ∑ j, U (β j) := by
    rw [sum_U_embed]
    exact card_le_sum_U β
  have hE := edges_round_le left right hβ
  have hM : (0 : ℝ) ≤ M ε := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hF hM
  unfold publishedLoss
  linarith

/-- Strict form of `lem:rounding`: if some coordinate of `β ∈ ℤ_2^n` is not
Boolean, rounding strictly lowers the loss. -/
theorem rounding_lt (left right : ε → Fin n) {β : Fin n → ℚ_[2]} (hβ : ∀ j, ‖β j‖ ≤ 1)
    {k : Fin n} (hk : β k ≠ 0 ∧ β k ≠ 1) :
    publishedLoss left right (embed 2 (round β)) < publishedLoss left right β := by
  have hF : ∑ j, U (embed 2 (round β) j) < ∑ j, U (β j) := by
    rw [sum_U_embed]
    have h1 := sum_U_ge β k
    have h2 := one_lt_U_of_ne hk
    linarith
  have hE := edges_round_le left right hβ
  have hmul := mul_lt_mul_of_pos_left hF (M_pos (ε := ε))
  unfold publishedLoss
  linarith

/-- Every global minimiser of the published objective is Boolean. -/
theorem globalMin_boolean (left right : ε → Fin n) {β : Fin n → ℚ_[2]}
    (hmin : IsGlobalMin (publishedLoss left right) β) : ∀ j, β j = 0 ∨ β j = 1 := by
  intro j
  by_contra h
  push_neg at h
  have hβ := optimal_coord_norm_le_one left right hmin
  exact absurd (hmin (embed 2 (round β))) (not_le.mpr (rounding_lt left right hβ h))

/-! ### The value formula and Max-Cut recovery -/

/-- On Boolean points the loss is `M n` plus the number of monochromatic edges. -/
theorem publishedLoss_embed_mono (left right : ε → Fin n) (s : Fin n → Bool) :
    publishedLoss left right (embed 2 s) = (M ε : ℝ) * n + monochromatic left right s := by
  unfold publishedLoss
  rw [sum_U_embed]
  simp only [norm_edge_embed, Finset.sum_boole, monochromatic]

/-- The published value formula `L(s) = M n + m - cutsize(s)`. -/
theorem publishedLoss_embed (left right : ε → Fin n) (s : Fin n → Bool) :
    publishedLoss left right (embed 2 s) =
      (M ε : ℝ) * n + Fintype.card ε - cutSize left right s := by
  rw [publishedLoss_embed_mono]
  have h : (monochromatic left right s : ℝ) + cutSize left right s = Fintype.card ε := by
    exact_mod_cast monochromatic_add_cutSize left right s
  linarith

theorem embed_false : embed 2 (fun _ : Fin n => false) = 0 := by
  funext j
  simp [embed]

/-- There is a Boolean global minimiser: minimise over `{0, 1}^n`; any `β` with a
coordinate outside `ℤ_2` loses to `0` by `lem:magnitude`/`lem:toobig`, and any
`β ∈ ℤ_2^n` is dominated by its rounding by `lem:rounding`. -/
theorem exists_boolean_globalMin (left right : ε → Fin n) :
    ∃ s : Fin n → Bool, IsGlobalMin (publishedLoss left right) (embed 2 s) := by
  classical
  obtain ⟨s₀, _, hs₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n → Bool))
    (fun s => publishedLoss left right (embed 2 s)) ⟨fun _ => false, Finset.mem_univ _⟩
  refine ⟨s₀, fun β => ?_⟩
  by_cases hβ : ∀ j, ‖β j‖ ≤ 1
  · exact (hs₀ (round β) (Finset.mem_univ _)).trans (rounding_le left right hβ)
  · push_neg at hβ
    obtain ⟨k, hk⟩ := hβ
    have h1 := loss_ge_of_norm_gt_one left right β k (Or.inl hk)
    have h2 := hs₀ (fun _ => false) (Finset.mem_univ _)
    rw [embed_false, loss_zero_eq] at h2
    have hM := card_add_one_eq_M (ε := ε)
    nlinarith

/-- A Boolean point is a global minimiser iff it is a maximum cut. -/
theorem isGlobalMin_embed_iff (left right : ε → Fin n) (s : Fin n → Bool) :
    IsGlobalMin (publishedLoss left right) (embed 2 s) ↔
      cutSize left right s = maxCut left right := by
  constructor
  · intro hmin
    rw [← isMaxCut_iff]
    intro s'
    have h := hmin (embed 2 s')
    rw [publishedLoss_embed, publishedLoss_embed] at h
    have hreal : (cutSize left right s' : ℝ) ≤ cutSize left right s := by linarith
    exact_mod_cast hreal
  · intro hs β
    obtain ⟨s₀, hs₀⟩ := exists_boolean_globalMin left right
    have h1 : publishedLoss left right (embed 2 s) ≤ publishedLoss left right (embed 2 s₀) := by
      rw [publishedLoss_embed, publishedLoss_embed]
      have hreal : (cutSize left right s₀ : ℝ) ≤ cutSize left right s := by
        rw [hs]
        exact_mod_cast cutSize_le_maxCut left right s₀
      linarith
    exact h1.trans (hs₀ β)

/-- Characterisation of the global minimisers: exactly the Boolean embeddings of
maximum cuts. -/
theorem isGlobalMin_iff (left right : ε → Fin n) (β : Fin n → ℚ_[2]) :
    IsGlobalMin (publishedLoss left right) β ↔
      ∃ s, β = embed 2 s ∧ cutSize left right s = maxCut left right := by
  constructor
  · intro hmin
    obtain ⟨s, rfl⟩ := exists_embed_of_boolean (globalMin_boolean left right hmin)
    exact ⟨s, rfl, (isGlobalMin_embed_iff left right s).mp hmin⟩
  · rintro ⟨s, rfl, hs⟩
    exact (isGlobalMin_embed_iff left right s).mpr hs

/-- Max-Cut recovery: the optimal value is `L* = M n + m - maxCut`, i.e.
`cutsize* = M n + m - L*`. -/
theorem optimal_value (left right : ε → Fin n) {β : Fin n → ℚ_[2]}
    (hmin : IsGlobalMin (publishedLoss left right) β) :
    publishedLoss left right β = (M ε : ℝ) * n + Fintype.card ε - maxCut left right := by
  obtain ⟨s, rfl, hs⟩ := (isGlobalMin_iff left right β).mp hmin
  rw [publishedLoss_embed, hs]

/-- Decision form: `G` has a cut of size `≥ K` iff the instance admits `β` with
`L(β) ≤ M n + m - K`. -/
theorem cut_ge_iff (left right : ε → Fin n) (K : ℕ) :
    (∃ s, K ≤ cutSize left right s) ↔
      ∃ β : Fin n → ℚ_[2],
        publishedLoss left right β ≤ (M ε : ℝ) * n + Fintype.card ε - K := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨embed 2 s, ?_⟩
    rw [publishedLoss_embed]
    have hreal : (K : ℝ) ≤ cutSize left right s := by exact_mod_cast hs
    linarith
  · rintro ⟨β, hβ⟩
    obtain ⟨s, hs⟩ := exists_boolean_globalMin left right
    refine ⟨s, ?_⟩
    have h := (hs β).trans hβ
    rw [publishedLoss_embed] at h
    have hreal : (K : ℝ) ≤ cutSize left right s := by linarith
    exact_mod_cast hreal

/-! ### The explicit regression instance -/

/-- Row index type of the published instance: one edge row per edge, then `M`
copies of `(e_j, 0)` and `M` copies of `(e_j, 1)` per vertex, `r = m + 2 M n`
rows in all. -/
abbrev PublishedIndex (n : ℕ) (ε : Type*) [Fintype ε] :=
  ε ⊕ ((Fin n × Fin (M ε)) ⊕ (Fin n × Fin (M ε)))

/-- The explicit integral `2`-adic regression instance of the published
reduction. -/
def publishedRows (left right : ε → Fin n) : PublishedIndex n ε → Row n
  | Sum.inl e => edgeRow left right e
  | Sum.inr (Sum.inl ⟨j, _⟩) => unitRow j 0
  | Sum.inr (Sum.inr ⟨j, _⟩) => unitRow j 1

/-- Fidelity to the problem definition: the homogeneous summed `2`-adic
regression loss of `publishedRows` is exactly the published objective. -/
theorem homogeneousLoss_publishedRows (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    (β : Fin n → ℚ_[2]) :
    homogeneousLoss (publishedRows left right) β = publishedLoss left right β := by
  unfold homogeneousLoss publishedLoss
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [publishedRows, norm_unitRow_residual, norm_edgeRow_residual left right hne,
    Int.cast_zero, Int.cast_one, sub_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, U, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  ring

/-- Row count of the published instance: `r = m + 2 M n`. -/
theorem card_publishedIndex :
    Fintype.card (PublishedIndex n ε) = Fintype.card ε + 2 * M ε * n := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Every coefficient of the published instance is `0` or `1`. -/
theorem publishedRows_coeff_mem (left right : ε → Fin n) (i : PublishedIndex n ε) (k : Fin n) :
    (publishedRows left right i).1 k = 0 ∨ (publishedRows left right i).1 k = 1 := by
  rcases i with e | ⟨j, _⟩ | ⟨j, _⟩
  · by_cases hk : k = left e ∨ k = right e <;> simp [publishedRows, edgeRow, hk]
  · by_cases hk : k = j <;> simp [publishedRows, unitRow, hk]
  · by_cases hk : k = j <;> simp [publishedRows, unitRow, hk]

/-- Every target of the published instance is `0` or `1`. -/
theorem publishedRows_target_mem (left right : ε → Fin n) (i : PublishedIndex n ε) :
    (publishedRows left right i).2 = 0 ∨ (publishedRows left right i).2 = 1 := by
  rcases i with e | ⟨j, _⟩ | ⟨j, _⟩ <;> simp [publishedRows, unitRow, edgeRow]

/-! ### Headline -/

/-- Thesis `thm:main` ("`p`-adic linear regression is NP-hard"), semantic
content of the published `p = 2` reduction with uniform multiplicity
`M = m + 1`: `lem:binary`, `lem:toobig`, `lem:magnitude`, `lem:rounding`, the
value formula `L(s) = M n + m - cutsize(s)`, the existence of a Boolean global
minimiser, the optimal value `M n + m - maxCut`, and the decision equivalence
"`G` has a cut of size `≥ K` iff some `β` has `L(β) ≤ M n + m - K`". The
NP-hardness transfer (Max-Cut is NP-hard; the instance is polynomial-time
computable) is external, as in `FixedPrimeMaxCut.lean`. -/
theorem published_main (left right : ε → Fin n) :
    (∀ a : ℚ_[2], 1 ≤ U a ∧ (U a = 1 ↔ a = 0 ∨ a = 1)) ∧
    (publishedLoss left right 0 = (M ε : ℝ) * n + Fintype.card ε ∧
      ∀ β : Fin n → ℚ_[2], (M ε : ℝ) * ((n : ℝ) + 1) ≤ publishedLoss left right β →
        ¬ IsGlobalMin (publishedLoss left right) β) ∧
    (∀ (β : Fin n → ℚ_[2]) (k : Fin n), (1 < ‖β k‖ ∨ 1 < ‖β k - 1‖) →
        ¬ IsGlobalMin (publishedLoss left right) β) ∧
    (∀ β : Fin n → ℚ_[2], (∀ j, ‖β j‖ ≤ 1) →
        publishedLoss left right (embed 2 (round β)) ≤ publishedLoss left right β) ∧
    (∀ s : Fin n → Bool, publishedLoss left right (embed 2 s) =
        (M ε : ℝ) * n + Fintype.card ε - cutSize left right s) ∧
    (∃ s : Fin n → Bool, IsGlobalMin (publishedLoss left right) (embed 2 s)) ∧
    (∀ β : Fin n → ℚ_[2], IsGlobalMin (publishedLoss left right) β →
        publishedLoss left right β = (M ε : ℝ) * n + Fintype.card ε - maxCut left right) ∧
    (∀ K : ℕ, (∃ s, K ≤ cutSize left right s) ↔
        ∃ β : Fin n → ℚ_[2],
          publishedLoss left right β ≤ (M ε : ℝ) * n + Fintype.card ε - K) :=
  ⟨binary_lemma,
    ⟨loss_zero_eq left right, fun _ h => not_optimal_of_ge left right h⟩,
    fun _ k hk => not_optimal_of_norm_gt_one left right k hk,
    fun _ hβ => rounding_le left right hβ,
    publishedLoss_embed left right,
    exists_boolean_globalMin left right,
    fun _ hmin => optimal_value left right hmin,
    cut_ge_iff left right⟩

end Published

end PhdThesisLean.PublishedMaxCut

#print axioms PhdThesisLean.PublishedMaxCut.binary_lemma
#print axioms PhdThesisLean.PublishedMaxCut.two_le_norm_of_one_lt
#print axioms PhdThesisLean.PublishedMaxCut.norm_lt_one_or_norm_sub_one_lt_one
#print axioms PhdThesisLean.PublishedMaxCut.loss_zero_eq
#print axioms PhdThesisLean.PublishedMaxCut.not_optimal_of_ge
#print axioms PhdThesisLean.PublishedMaxCut.not_optimal_of_norm_gt_one
#print axioms PhdThesisLean.PublishedMaxCut.optimal_coord_norm_le_one
#print axioms PhdThesisLean.PublishedMaxCut.rounding_le
#print axioms PhdThesisLean.PublishedMaxCut.rounding_lt
#print axioms PhdThesisLean.PublishedMaxCut.globalMin_boolean
#print axioms PhdThesisLean.PublishedMaxCut.publishedLoss_embed
#print axioms PhdThesisLean.PublishedMaxCut.exists_boolean_globalMin
#print axioms PhdThesisLean.PublishedMaxCut.isGlobalMin_iff
#print axioms PhdThesisLean.PublishedMaxCut.optimal_value
#print axioms PhdThesisLean.PublishedMaxCut.cut_ge_iff
#print axioms PhdThesisLean.PublishedMaxCut.homogeneousLoss_publishedRows
#print axioms PhdThesisLean.PublishedMaxCut.card_publishedIndex
#print axioms PhdThesisLean.PublishedMaxCut.publishedRows_coeff_mem
#print axioms PhdThesisLean.PublishedMaxCut.publishedRows_target_mem
#print axioms PhdThesisLean.PublishedMaxCut.published_main
