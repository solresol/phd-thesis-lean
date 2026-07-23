/-
  Formalisation of the thresholded-loss coreset obstruction from Greg Baker's
  PhD thesis.

  Thesis source: coreset-obstruction/coreset.tex
  Thesis label: thm:threshold-coreset
  Thesis snapshot: 2c6418bcf9643fc6e039237f0f59ace14b2557fc
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

namespace PhdThesisLean.Coreset

open scoped BigOperators

noncomputable def fullLoss
    {k : ℕ} {Θ : Type*} (loss : Fin k → Θ → ℝ) (β : Θ) : ℝ :=
  ∑ i, loss i β

noncomputable def weightedSubsetLoss
    {k : ℕ} {Θ : Type*} (loss : Fin k → Θ → ℝ)
    (S : Finset (Fin k)) (ω : Fin k → ℝ) (β : Θ) : ℝ :=
  ∑ i ∈ S, ω i * loss i β

def IsEpsilonCoreset
    {k : ℕ} {Θ : Type*} (loss : Fin k → Θ → ℝ)
    (S : Finset (Fin k)) (ω : Fin k → ℝ) (ε : ℝ) : Prop :=
  ∀ β,
    (1 - ε) * fullLoss loss β ≤ weightedSubsetLoss loss S ω β ∧
    weightedSubsetLoss loss S ω β ≤ (1 + ε) * fullLoss loss β

/-- Uniform-cost specialization of the thesis witness-point lemma. If each
parameter `β j` alone fits witness `j`, omitting `j` makes the subset objective
unable to distinguish `β j` from the baseline parameter. -/
theorem witness_point_obstruction
    {k : ℕ} (hk : 1 ≤ k) {Θ : Type*}
    (loss : Fin k → Θ → ℝ) (β₀ : Θ) (β : Fin k → Θ)
    (hbase : ∀ i, loss i β₀ = 1)
    (hmatch : ∀ j, loss j (β j) = 0)
    (hrival : ∀ i j, i ≠ j → loss i (β j) = 1)
    (ε : ℝ) (hε : ε < 1 / (2 * (k : ℝ) - 1))
    (S : Finset (Fin k)) (hS : S.card < k) (ω : Fin k → ℝ) :
    ¬IsEpsilonCoreset loss S ω ε := by
  intro hcore
  have hSne : S ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ, Fintype.card_fin] at hS
    omega
  obtain ⟨j, hj⟩ : ∃ j : Fin k, j ∉ S := by
    simpa [Finset.ext_iff] using hSne
  have hfullBase : fullLoss loss β₀ = k := by
    simp [fullLoss, hbase]
  have hfullMatch : fullLoss loss (β j) = k - 1 := by
    rw [fullLoss]
    calc
      (∑ i, loss i (β j)) =
          ∑ i ∈ Finset.univ.erase j, loss i (β j) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), hmatch, add_zero]
      _ = ∑ i ∈ Finset.univ.erase j, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hrival i j (Finset.ne_of_mem_erase hi)]
      _ = k - 1 := by
        simp [Nat.cast_sub hk]
  have hsubsetEq :
      weightedSubsetLoss loss S ω β₀ = weightedSubsetLoss loss S ω (β j) := by
    rw [weightedSubsetLoss, weightedSubsetLoss]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbase]
    have hij : i ≠ j := fun h ↦ hj (h ▸ hi)
    rw [hrival i j hij]
  have hlower := (hcore β₀).1
  have hupper := (hcore (β j)).2
  rw [hfullBase] at hlower
  rw [hfullMatch, ← hsubsetEq] at hupper
  have hden : 0 < 2 * (k : ℝ) - 1 := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hcross : ε * (2 * (k : ℝ) - 1) < 1 := by
    have := (lt_div_iff₀ hden).mp hε
    simpa [mul_comm] using this
  nlinarith

abbrev Predictor (p n : ℕ) [Fact p.Prime] := Fin n → ℚ_[p]

abbrev Parameter (p n : ℕ) [Fact p.Prime] := Fin n → ℚ_[p]

abbrev RegressionPoint (p n : ℕ) [Fact p.Prime] :=
  Predictor p n × ℚ_[p]

noncomputable def regressionResidual
    {p n : ℕ} [Fact p.Prime]
    (z : RegressionPoint p n) (β : Parameter p n) : ℚ_[p] :=
  z.2 - dotProduct β z.1

noncomputable def thresholdLoss
    {p n : ℕ} [Fact p.Prime] (τ : ℝ)
    (z : RegressionPoint p n) (β : Parameter p n) : ℝ :=
  if ‖regressionResidual z β‖ ≤ τ then 0 else 1

theorem thresholdLoss_zero
    {p n : ℕ} [Fact p.Prime]
    (z : RegressionPoint p n) (β : Parameter p n) :
    thresholdLoss 0 z β = 0 ↔ regressionResidual z β = 0 := by
  simp [thresholdLoss]

def axisVector
    {p n : ℕ} [Fact p.Prime] (i₀ : Fin n) (a : ℚ_[p]) :
    Fin n → ℚ_[p] :=
  fun i ↦ if i = i₀ then a else 0

@[simp]
theorem dotProduct_axisVector
    {p n : ℕ} [Fact p.Prime] (i₀ : Fin n) (a b : ℚ_[p]) :
    dotProduct (axisVector i₀ a) (axisVector i₀ b) = a * b := by
  classical
  rw [dotProduct, Finset.sum_eq_single i₀]
  · simp [axisVector]
  · intro i _hi hne
    simp [axisVector, hne]
  · simp

abbrev DistinctPair (m : ℕ) :=
  {q : Fin m × Fin m // q.1 ≠ q.2}

def parameterScalar
    {p m : ℕ} [Fact p.Prime] (r : Fin m) : ℚ_[p] :=
  (r.val : ℚ_[p])

theorem parameterScalar_injective
    {p m : ℕ} [Fact p.Prime] :
    Function.Injective (parameterScalar (p := p) (m := m)) := by
  intro r s h
  apply Fin.ext
  change (r.val : ℚ_[p]) = (s.val : ℚ_[p]) at h
  exact_mod_cast h

noncomputable def differenceProduct
    (p m : ℕ) [Fact p.Prime] : ℚ_[p] :=
  ∏ q : DistinctPair m,
    (parameterScalar (p := p) q.1.1 - parameterScalar (p := p) q.1.2)

theorem differenceProduct_ne_zero
    (p m : ℕ) [Fact p.Prime] :
    differenceProduct p m ≠ 0 := by
  classical
  rw [differenceProduct]
  rw [Finset.prod_ne_zero_iff]
  intro q _hq
  exact sub_ne_zero.mpr fun h ↦ q.property (parameterScalar_injective h)

theorem norm_parameterScalar_sub_le_one
    {p m : ℕ} [Fact p.Prime] (r s : Fin m) :
    ‖parameterScalar (p := p) r - parameterScalar (p := p) s‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  apply (Padic.nonarchimedean _ _).trans
  apply max_le
  · exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] r.val
  · simpa using IsUltrametricDist.norm_natCast_le_one ℚ_[p] s.val

theorem norm_differenceProduct_le_factor
    {p m : ℕ} [Fact p.Prime] (q : DistinctPair m) :
    ‖differenceProduct p m‖ ≤
      ‖parameterScalar (p := p) q.1.1 - parameterScalar (p := p) q.1.2‖ := by
  classical
  rw [differenceProduct, norm_prod]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun r : DistinctPair m ↦
      ‖parameterScalar (p := p) r.1.1 - parameterScalar (p := p) r.1.2‖)
    (Finset.mem_univ q)]
  have hrest :
      (∏ r ∈ (Finset.univ.erase q),
        ‖parameterScalar (p := p) r.1.1 -
          parameterScalar (p := p) r.1.2‖) ≤ 1 := by
    apply Finset.prod_le_one
    · intro r _hr
      exact norm_nonneg _
    · intro r _hr
      exact norm_parameterScalar_sub_le_one r.1.1 r.1.2
  simpa using mul_le_mul_of_nonneg_left hrest (norm_nonneg
    (parameterScalar (p := p) q.1.1 - parameterScalar (p := p) q.1.2))

noncomputable def largeElement
    (p : ℕ) [Fact p.Prime] (τ : ℝ) : ℚ_[p] :=
  Classical.choose (NormedField.exists_lt_norm ℚ_[p] τ)

theorem norm_largeElement_gt
    (p : ℕ) [Fact p.Prime] (τ : ℝ) :
    τ < ‖largeElement p τ‖ :=
  Classical.choose_spec (NormedField.exists_lt_norm ℚ_[p] τ)

noncomputable def commonScale
    (p m : ℕ) [Fact p.Prime] (τ : ℝ) : ℚ_[p] :=
  largeElement p τ / differenceProduct p m

theorem norm_commonScale_mul_difference_gt
    {p m : ℕ} [Fact p.Prime] (τ : ℝ) (q : DistinctPair m) :
    τ < ‖commonScale p m τ *
      (parameterScalar (p := p) q.1.1 -
        parameterScalar (p := p) q.1.2)‖ := by
  have hPne := differenceProduct_ne_zero p m
  have hPpos : 0 < ‖differenceProduct p m‖ := norm_pos_iff.mpr hPne
  have hfactor :
      1 ≤
        ‖parameterScalar (p := p) q.1.1 -
          parameterScalar (p := p) q.1.2‖ /
            ‖differenceProduct p m‖ :=
    (le_div_iff₀ hPpos).mpr (by
      simpa using norm_differenceProduct_le_factor q)
  rw [commonScale, norm_mul, norm_div]
  calc
    τ < ‖largeElement p τ‖ := norm_largeElement_gt p τ
    _ = ‖largeElement p τ‖ * 1 := by ring
    _ ≤ ‖largeElement p τ‖ *
        (‖parameterScalar (p := p) q.1.1 -
          parameterScalar (p := p) q.1.2‖ /
            ‖differenceProduct p m‖) :=
      mul_le_mul_of_nonneg_left hfactor (norm_nonneg _)
    _ = ‖largeElement p τ‖ / ‖differenceProduct p m‖ *
        ‖parameterScalar (p := p) q.1.1 -
          parameterScalar (p := p) q.1.2‖ := by
      field_simp

def witnessParameter
    {p n m : ℕ} [Fact p.Prime] (i₀ : Fin n) (r : Fin m) :
    Parameter p n :=
  axisVector i₀ (parameterScalar (p := p) r)

noncomputable def witnessDataset
    {p n k : ℕ} [Fact p.Prime] (i₀ : Fin n) (τ : ℝ) :
    Fin k → RegressionPoint p n :=
  fun j ↦
    let scale := commonScale p (k + 1) τ
    (axisVector i₀ scale,
      scale * parameterScalar (p := p) (Fin.succ j))

theorem witness_residual
    {p n k : ℕ} [Fact p.Prime] (i₀ : Fin n) (τ : ℝ)
    (j : Fin k) (r : Fin (k + 1)) :
    regressionResidual (witnessDataset i₀ τ j) (witnessParameter i₀ r) =
      commonScale p (k + 1) τ *
        (parameterScalar (p := p) (Fin.succ j) -
          parameterScalar (p := p) r) := by
  rw [regressionResidual, witnessDataset, witnessParameter,
    dotProduct_axisVector]
  ring

theorem witnessDataset_injective
    {p n k : ℕ} [Fact p.Prime] (i₀ : Fin n) (τ : ℝ) (hτ : 0 ≤ τ) :
    Function.Injective (witnessDataset (p := p) (k := k) i₀ τ) := by
  have hlargePos : 0 < ‖largeElement p τ‖ :=
    hτ.trans_lt (norm_largeElement_gt p τ)
  have hscaleNe : commonScale p (k + 1) τ ≠ 0 := by
    apply div_ne_zero
    · exact norm_pos_iff.mp hlargePos
    · exact differenceProduct_ne_zero p (k + 1)
  intro i j hij
  have hy := congrArg Prod.snd hij
  dsimp [witnessDataset] at hy
  change commonScale p (k + 1) τ *
      parameterScalar (p := p) (Fin.succ i) =
    commonScale p (k + 1) τ *
      parameterScalar (p := p) (Fin.succ j) at hy
  have ha : parameterScalar (p := p) (Fin.succ i) =
      parameterScalar (p := p) (Fin.succ j) :=
    mul_left_cancel₀ hscaleNe hy
  exact Fin.succ_injective k (parameterScalar_injective ha)

theorem thresholdLoss_witness_match
    {p n k : ℕ} [Fact p.Prime] (i₀ : Fin n) (τ : ℝ) (hτ : 0 ≤ τ)
    (j : Fin k) :
    thresholdLoss (p := p) τ (witnessDataset (p := p) i₀ τ j)
      (witnessParameter (p := p) i₀ (Fin.succ j)) = 0 := by
  rw [thresholdLoss, witness_residual (p := p)]
  simp [hτ]

theorem thresholdLoss_witness_base
    {p n k : ℕ} [Fact p.Prime] (i₀ : Fin n) (τ : ℝ)
    (j : Fin k) :
    thresholdLoss (p := p) τ (witnessDataset (p := p) i₀ τ j)
      (witnessParameter (p := p) i₀ (0 : Fin (k + 1))) = 1 := by
  rw [thresholdLoss, witness_residual (p := p)]
  have hne : Fin.succ j ≠ (0 : Fin (k + 1)) := by simp
  let q : DistinctPair (k + 1) := ⟨(Fin.succ j, 0), hne⟩
  have hgt := norm_commonScale_mul_difference_gt (p := p) τ q
  rw [if_neg (not_le_of_gt hgt)]

theorem thresholdLoss_witness_rival
    {p n k : ℕ} [Fact p.Prime] (i₀ : Fin n) (τ : ℝ)
    (i j : Fin k) (hij : i ≠ j) :
    thresholdLoss (p := p) τ (witnessDataset (p := p) i₀ τ i)
      (witnessParameter (p := p) i₀ (Fin.succ j)) = 1 := by
  rw [thresholdLoss, witness_residual (p := p)]
  have hne : Fin.succ i ≠ Fin.succ j :=
    fun h ↦ hij (Fin.succ_injective k h)
  let q : DistinctPair (k + 1) := ⟨(Fin.succ i, Fin.succ j), hne⟩
  have hgt := norm_commonScale_mul_difference_gt (p := p) τ q
  rw [if_neg (not_le_of_gt hgt)]

def HasPositiveWeights
    {k : ℕ} (S : Finset (Fin k)) (ω : Fin k → ℝ) : Prop :=
  ∀ i ∈ S, 0 < ω i

/-- Thesis Theorem `thm:threshold-coreset`: at sufficiently high accuracy,
every point in the constructed `k`-point dataset is required in the support of
a positive-weight surrogate-objective coreset. -/
theorem threshold_coreset
    (p d k : ℕ) [Fact p.Prime] (hd : 2 ≤ d) (hk : 1 ≤ k)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ D : Fin k → RegressionPoint p (d - 1),
      Function.Injective D ∧
      (Set.range D).ncard = k ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 / (2 * (k : ℝ) - 1) →
        ∀ S : Finset (Fin k), S.card < k →
          ∀ ω : Fin k → ℝ, HasPositiveWeights S ω →
            ¬IsEpsilonCoreset
              (fun i β ↦ thresholdLoss τ (D i) β) S ω ε := by
  classical
  let i₀ : Fin (d - 1) := ⟨0, by omega⟩
  let D : Fin k → RegressionPoint p (d - 1) := witnessDataset i₀ τ
  have hDinj : Function.Injective D := by
    exact witnessDataset_injective i₀ τ hτ
  refine ⟨D, hDinj, ?_, ?_⟩
  · rw [Set.ncard_range_of_injective hDinj, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  · intro ε _hεpos hε S hS ω _hω
    apply witness_point_obstruction hk
      (loss := fun i β ↦ thresholdLoss τ (D i) β)
      (β₀ := witnessParameter i₀ (0 : Fin (k + 1)))
      (β := fun j ↦ witnessParameter i₀ (Fin.succ j))
      (ε := ε) (hε := hε) (S := S) (hS := hS) (ω := ω)
    · intro i
      exact thresholdLoss_witness_base i₀ τ i
    · intro j
      exact thresholdLoss_witness_match i₀ τ hτ j
    · intro i j hij
      exact thresholdLoss_witness_rival i₀ τ i j hij

theorem exactFit_coreset
    (p d k : ℕ) [Fact p.Prime] (hd : 2 ≤ d) (hk : 1 ≤ k) :
    ∃ D : Fin k → RegressionPoint p (d - 1),
      Function.Injective D ∧
      (Set.range D).ncard = k ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 / (2 * (k : ℝ) - 1) →
        ∀ S : Finset (Fin k), S.card < k →
          ∀ ω : Fin k → ℝ, HasPositiveWeights S ω →
            ¬IsEpsilonCoreset
              (fun i β ↦ thresholdLoss 0 (D i) β) S ω ε :=
  threshold_coreset p d k hd hk 0 le_rfl

end PhdThesisLean.Coreset
