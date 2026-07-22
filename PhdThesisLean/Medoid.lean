/-
  Formalisation of medoid results from Greg Baker's PhD thesis.

  Thesis source: pac-learning-open-questions/body.tex
  Thesis labels: thm:sparse-medoid-representation, prop:medoid-robustness
  Thesis snapshot: 2c6418bcf9643fc6e039237f0f59ace14b2557fc
-/

import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace PhdThesisLean.Medoid

open scoped BigOperators

/-- Radius of the ball of outputs correct to `p`-adic precision `N`. -/
noncomputable def precisionRadius (p N : ℕ) : ℝ := (p : ℝ) ^ (-(N : ℤ))

/-- Membership in the closed ball `y + p^N ℤ_p`, expressed inside `ℚ_p`. -/
def InPrecisionBall {p : ℕ} [Fact p.Prime] (N : ℕ) (y z : ℚ_[p]) : Prop :=
  ‖z - y‖ ≤ precisionRadius p N

theorem norm_sub_center_gt_radius_of_not_mem
    {p : ℕ} [Fact p.Prime] {N : ℕ} {y z : ℚ_[p]}
    (hz : ¬InPrecisionBall N y z) :
    precisionRadius p N < ‖z - y‖ := by
  exact lt_of_not_ge hz

theorem norm_bad_sub_good_eq
    {p : ℕ} [Fact p.Prime] {N : ℕ} {y z w : ℚ_[p]}
    (hz : ¬InPrecisionBall N y z) (hw : InPrecisionBall N y w) :
    ‖z - w‖ = ‖z - y‖ := by
  have hlt : ‖w - y‖ < ‖z - y‖ :=
    lt_of_le_of_lt hw (norm_sub_center_gt_radius_of_not_mem hz)
  rw [show z - w = (z - y) + -(w - y) by ring]
  rw [Padic.add_eq_max_of_ne]
  · simp only [norm_neg]
    exact max_eq_left hlt.le
  · simpa only [norm_neg] using ne_of_gt hlt

theorem norm_good_sub_good_le_radius
    {p : ℕ} [Fact p.Prime] {N : ℕ} {y w u : ℚ_[p]}
    (hw : InPrecisionBall N y w) (hu : InPrecisionBall N y u) :
    ‖w - u‖ ≤ precisionRadius p N := by
  rw [show w - u = (w - y) + -(u - y) by ring]
  apply (Padic.nonarchimedean _ _).trans
  simpa only [norm_neg] using max_le hw hu

/-- Discreteness of the `p`-adic norm supplies the factor-`p` gap between a
bad-to-good distance and the precision radius. -/
theorem p_mul_radius_le_bad_good_distance
    {p : ℕ} [Fact p.Prime] {N : ℕ} {y z w : ℚ_[p]}
    (hz : ¬InPrecisionBall N y z) (hw : InPrecisionBall N y w) :
    (p : ℝ) * precisionRadius p N ≤ ‖z - w‖ := by
  have hDgt : precisionRadius p N < ‖z - w‖ := by
    rw [norm_bad_sub_good_eq hz hw]
    exact norm_sub_center_gt_radius_of_not_mem hz
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpow : (p : ℝ) ^ (-(N : ℤ) + 1) ≤ ‖z - w‖ := by
    by_contra h
    have hlt : ‖z - w‖ < (p : ℝ) ^ (-(N : ℤ) + 1) := lt_of_not_ge h
    have hle := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one (z - w)
      (-(N : ℤ) + 1)).mp hlt
    have hexp : -(N : ℤ) + 1 - 1 = -(N : ℤ) := by ring
    rw [hexp] at hle
    exact (not_le_of_gt hDgt) hle
  calc
    (p : ℝ) * precisionRadius p N =
        (p : ℝ) ^ (-(N : ℤ)) * (p : ℝ) := by rw [precisionRadius, mul_comm]
    _ = (p : ℝ) ^ (-(N : ℤ) + 1) := (zpow_add_one₀ hp0 _).symm
    _ ≤ ‖z - w‖ := hpow

/-- Sum of distances from a candidate value to an indexed candidate multiset. -/
noncomputable def medoidCost
    {p m : ℕ} [Fact p.Prime] (z : Fin m → ℚ_[p]) (c : ℚ_[p]) : ℝ :=
  ∑ i, ‖c - z i‖

/-- Candidate `j` is a medoid when its output minimises total distance among
the indexed candidate multiset. -/
def IsMedoid
    {p m : ℕ} [Fact p.Prime] (z : Fin m → ℚ_[p]) (j : Fin m) : Prop :=
  ∀ l : Fin m, medoidCost z (z j) ≤ medoidCost z (z l)

noncomputable def goodIndices
    {p m : ℕ} [Fact p.Prime] (z : Fin m → ℚ_[p]) (N : ℕ) (y : ℚ_[p]) : Finset (Fin m) :=
  by
    classical
    exact Finset.univ.filter fun i ↦ InPrecisionBall N y (z i)

noncomputable def badIndices
    {p m : ℕ} [Fact p.Prime] (z : Fin m → ℚ_[p]) (N : ℕ) (y : ℚ_[p]) : Finset (Fin m) :=
  by
    classical
    exact Finset.univ.filter fun i ↦ ¬InPrecisionBall N y (z i)

/-- Strong form of thesis Proposition `prop:medoid-robustness`, using the
actual cardinalities of the good and bad candidate index sets. -/
theorem medoid_robustness_core
    (p : ℕ) [Fact p.Prime] {m : ℕ} (z : Fin m → ℚ_[p]) (N : ℕ) (y : ℚ_[p])
    (hbalance :
      (goodIndices z N y).card * (p - 1) > p * (badIndices z N y).card)
    (j : Fin m) (hj : IsMedoid z j) :
    InPrecisionBall N y (z j) := by
  classical
  let G := goodIndices z N y
  let B := badIndices z N y
  by_contra hjbad
  change G.card * (p - 1) > p * B.card at hbalance
  have hGpos : 0 < G.card := by
    by_contra h
    have hzero : G.card = 0 := Nat.eq_zero_of_not_pos h
    rw [hzero] at hbalance
    simp at hbalance
  obtain ⟨w, hwG⟩ := G.card_pos.mp hGpos
  have hw : InPrecisionBall N y (z w) := by
    simpa [G, goodIndices] using hwG
  let D : ℝ := ‖z j - z w‖
  have hRpos : 0 < precisionRadius p N := by
    rw [precisionRadius]
    exact zpow_pos (by exact_mod_cast (Fact.out : Nat.Prime p).pos) _
  have hDgtR : precisionRadius p N < D := by
    dsimp [D]
    rw [norm_bad_sub_good_eq hjbad hw]
    exact norm_sub_center_gt_radius_of_not_mem hjbad
  have hDpos : 0 < D := hRpos.trans hDgtR
  have hpRleD : (p : ℝ) * precisionRadius p N ≤ D :=
    p_mul_radius_le_bad_good_distance hjbad hw
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hRle : precisionRadius p N ≤ D / (p : ℝ) :=
    (le_div_iff₀ hpR).mpr (by simpa [mul_comm] using hpRleD)
  have hgood_bad : ∀ i ∈ G, ‖z j - z i‖ = D := by
    intro i hi
    have hii : InPrecisionBall N y (z i) := by
      simpa [G, goodIndices] using hi
    dsimp [D]
    rw [norm_bad_sub_good_eq hjbad hii, norm_bad_sub_good_eq hjbad hw]
  have hgood_w : ∀ i ∈ G, ‖z w - z i‖ ≤ D / (p : ℝ) := by
    intro i hi
    have hii : InPrecisionBall N y (z i) := by
      simpa [G, goodIndices] using hi
    exact (norm_good_sub_good_le_radius hw hii).trans hRle
  have hbad_w : ∀ i ∈ B, ‖z w - z i‖ ≤ D + ‖z j - z i‖ := by
    intro i _
    calc
      ‖z w - z i‖ = ‖(z w - z j) + (z j - z i)‖ := by ring_nf
      _ ≤ ‖z w - z j‖ + ‖z j - z i‖ := norm_add_le _ _
      _ = D + ‖z j - z i‖ := by rw [norm_sub_rev]
  have hsplit (c : ℚ_[p]) :
      medoidCost z c = (∑ i ∈ G, ‖c - z i‖) + ∑ i ∈ B, ‖c - z i‖ := by
    rw [medoidCost]
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i ↦ InPrecisionBall N y (z i)) (fun i ↦ ‖c - z i‖)
    simpa [G, B, goodIndices, badIndices] using h.symm
  have hjcost :
      medoidCost z (z j) = (G.card : ℝ) * D + ∑ i ∈ B, ‖z j - z i‖ := by
    rw [hsplit]
    congr 1
    calc
      (∑ i ∈ G, ‖z j - z i‖) = ∑ _i ∈ G, D := by
        apply Finset.sum_congr rfl
        exact hgood_bad
      _ = (G.card : ℝ) * D := by simp
  have hwcost :
      medoidCost z (z w) ≤
        (G.card : ℝ) * (D / (p : ℝ)) +
          ((B.card : ℝ) * D + ∑ i ∈ B, ‖z j - z i‖) := by
    rw [hsplit]
    apply add_le_add
    · calc
        (∑ i ∈ G, ‖z w - z i‖) ≤ ∑ _i ∈ G, D / (p : ℝ) := by
          apply Finset.sum_le_sum
          exact hgood_w
        _ = (G.card : ℝ) * (D / (p : ℝ)) := by simp
    · calc
        (∑ i ∈ B, ‖z w - z i‖) ≤ ∑ i ∈ B, (D + ‖z j - z i‖) := by
          apply Finset.sum_le_sum
          exact hbad_w
        _ = (B.card : ℝ) * D + ∑ i ∈ B, ‖z j - z i‖ := by
          rw [Finset.sum_add_distrib]
          simp
  have hbalance' :
      (G.card : ℝ) * ((p : ℝ) - 1) > (p : ℝ) * (B.card : ℝ) := by
    have hb : ((G.card * (p - 1) : ℕ) : ℝ) > ((p * B.card : ℕ) : ℝ) := by
      exact_mod_cast hbalance
    norm_num only [Nat.cast_mul] at hb
    rw [Nat.cast_sub (Fact.out : Nat.Prime p).one_le] at hb
    norm_num at hb ⊢
    exact hb
  have hnumeric :
      (G.card : ℝ) * (D / (p : ℝ)) + (B.card : ℝ) * D <
        (G.card : ℝ) * D := by
    have hgap : 0 <
        ((G.card : ℝ) * ((p : ℝ) - 1) - (p : ℝ) * (B.card : ℝ)) * D :=
      mul_pos (sub_pos.mpr hbalance') hDpos
    field_simp
    nlinarith
  have hstrict : medoidCost z (z w) < medoidCost z (z j) := by
    rw [hjcost]
    exact lt_of_le_of_lt hwcost (by linarith)
  exact (not_lt_of_ge (hj w)) hstrict

/-- Statement-faithful wrapper for thesis Proposition
`prop:medoid-robustness`. -/
theorem medoid_robustness
    (p : ℕ) [Fact p.Prime] {m : ℕ} (z : Fin m → ℚ_[p]) (N : ℕ) (y : ℚ_[p])
    (g b : ℕ)
    (hg : (goodIndices z N y).card = g)
    (hb : (badIndices z N y).card = b)
    (_hbdef : b = m - g)
    (hbalance : g * (p - 1) > p * b) :
    ∀ j : Fin m, IsMedoid z j → InPrecisionBall N y (z j) := by
  intro j hj
  apply medoid_robustness_core p z N y
  · simpa [hg, hb] using hbalance
  · exact hj

end PhdThesisLean.Medoid
