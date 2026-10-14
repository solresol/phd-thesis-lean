import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

namespace PhdThesisLean.PrefixConsensus

open scoped BigOperators

/-!
# The `p`-adic medoid as prefix consensus

Formalisation of Proposition `prop:medoid-prefix-consensus` from
`athanasius-branch-point/body.tex` of Greg Baker's PhD thesis, together with
the two paragraphs following its proof (rational predictions whose distance is
capped at `1`).

Setting: candidate branch labels `c : ℤ_[p]` and raw predictions
`z : ι → ℤ_[p]` indexed by an arbitrary finite type `ι` (the thesis uses
`z₁, …, z_m`; `m = Fintype.card ι`).

* `cost z c = ∑ j, ‖c - z j‖` is the branch-risk medoid objective.
* `prefixCount z c r = #{j | z j ≡ c (mod p^r)}` is the prefix agreement count
  at depth `r` (congruence is membership of `c - z j` in the ideal `(p^r)`;
  `agrees_iff_norm_le` identifies it with `‖c - z j‖ ≤ p^(-r)`).
* `score z c = ∑' r : ℕ, p^(-r) · prefixCount z c (r + 1)` is the thesis'
  weighted prefix score `∑_{r ≥ 1} p^{-(r-1)} #{j : z_j ≡ c (mod p^r)}`,
  reindexed by `r ↦ r + 1`.

Headline results:

* `prefix_consensus_identity`:
  `cost z c = m - (1 - p⁻¹) · score z c`, the displayed identity of the proof.
* `medoid_iff_maximises_score`: on any finite candidate set `C`, `c ∈ C`
  minimises `cost` over `C` iff it maximises `score` over `C`.
* `isGlobalMin_cost_iff_isGlobalMax_score`: the same over all of `ℤ_[p]`.

Correspondence notes.

* The infinite series is handled as a genuine `HasSum` (`hasSum_score_term`,
  `hasSum_score`), so `score` is a convergent sum, not a formal expression.
* The thesis' convention `p^{-∞} = 0` for `v_j(c) = ∞` (exact match
  `c = z j`, and the "exact-match terminal convention" for finite-depth codes)
  is exactly the `c = z j` case of `hasSum_score_term`, where every indicator
  is `1` and the series is the full geometric series `1 / (1 - p⁻¹)`.
* `prefixCount_antitone` records that prefix agreement is antitone in depth.
* Rational predictions: `norm_sub_eq_of_one_lt_norm` and
  `cappedDist_eq_one_of_one_lt_norm` formalise "if `v_p(z_j) < 0` then
  `|c - z_j|_p = |z_j|_p > 1` for every integral `c`, so the capped
  contribution is the constant `1`"; `cappedCost_eq` splits the implemented
  capped objective over `ℚ_[p]` predictions into the constant count of
  non-integral predictions plus the integral medoid cost of the proposition,
  and `capped_medoid_iff_maximises_score` is the resulting equivalence for
  the implemented bounded medoid ("after the constant non-integral
  contributions are discarded").
* Everything is proved over the arbitrary finite index type `ι` rather than
  `Fin m`, which is strictly more general than the thesis statement.
-/

/-- Local copy of `PhdThesisLean.AllDifferent.IsGlobalMin`. -/
def IsGlobalMin {α : Type*} (f : α → ℝ) (x : α) : Prop :=
  ∀ y, f x ≤ f y

/-- Global maximiser, the dual of `IsGlobalMin`. -/
def IsGlobalMax {α : Type*} (f : α → ℝ) (x : α) : Prop :=
  ∀ y, f y ≤ f x

section Defs

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]

/-- The branch-risk medoid objective `∑ j, |c - z_j|_p`. -/
noncomputable def cost (z : ι → ℤ_[p]) (c : ℤ_[p]) : ℝ :=
  ∑ j, ‖c - z j‖

/-- `z_j ≡ c (mod p^r)`, phrased as membership of `c - z_j` in the ideal `(p^r)`. -/
def Agrees (c zj : ℤ_[p]) (r : ℕ) : Prop :=
  c - zj ∈ (Ideal.span {(p : ℤ_[p]) ^ r} : Ideal ℤ_[p])

/-- Congruence is decided classically (it is a property of `p`-adic integers). -/
noncomputable instance decidableAgrees (c zj : ℤ_[p]) (r : ℕ) : Decidable (Agrees c zj r) :=
  Classical.dec _

/-- Prefix agreement count `#{j : z_j ≡ c (mod p^r)}`. -/
noncomputable def prefixCount (z : ι → ℤ_[p]) (c : ℤ_[p]) (r : ℕ) : ℕ :=
  (Finset.univ.filter fun j => Agrees c (z j) r).card

/-- The geometric prefix weight `p^(-r)`. -/
noncomputable def weight (p : ℕ) (r : ℕ) : ℝ := (p : ℝ) ^ (-(r : ℤ))

/-- The weighted prefix-consensus score
`∑_{r ≥ 1} p^{-(r-1)} #{j : z_j ≡ c (mod p^r)}`, reindexed as a sum over
`r : ℕ` of `p^(-r) · #{j : z_j ≡ c (mod p^(r+1))}`. -/
noncomputable def score (z : ι → ℤ_[p]) (c : ℤ_[p]) : ℝ :=
  ∑' r : ℕ, weight p r * (prefixCount z c (r + 1) : ℝ)

end Defs

section Weight

variable {p : ℕ}

theorem inv_cast_nonneg : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by
  positivity

/-- `p^(-r) = (p⁻¹)^r`: the weight is the `r`-th power of the ratio `p⁻¹`. -/
theorem weight_eq (r : ℕ) : weight p r = ((p : ℝ)⁻¹) ^ r := by
  rw [weight, zpow_neg, zpow_natCast, inv_pow]

end Weight

section Basic

variable {p : ℕ} [hp : Fact p.Prime]

theorem one_lt_cast_prime : (1 : ℝ) < p := by
  exact_mod_cast hp.out.one_lt

theorem inv_cast_prime_lt_one : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ one_lt_cast_prime

theorem one_sub_inv_cast_prime_pos : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
  linarith [inv_cast_prime_lt_one (p := p)]

/-- Congruence modulo `p^r` is the closed-ball condition `‖c - z_j‖ ≤ p^(-r)`
(`PadicInt.norm_le_pow_iff_mem_span_pow`). -/
theorem agrees_iff_norm_le (c zj : ℤ_[p]) (r : ℕ) :
    Agrees c zj r ↔ ‖c - zj‖ ≤ (p : ℝ) ^ (-(r : ℤ)) :=
  (PadicInt.norm_le_pow_iff_mem_span_pow (c - zj) r).symm

/-- For `c ≠ z_j`, congruence modulo `p^r` holds exactly when `r ≤ v_p(c - z_j)`
(`PadicInt.mem_span_pow_iff_le_valuation`). -/
theorem agrees_iff_le_valuation {c zj : ℤ_[p]} (hx : c - zj ≠ 0) (r : ℕ) :
    Agrees c zj r ↔ r ≤ (c - zj).valuation :=
  PadicInt.mem_span_pow_iff_le_valuation (c - zj) hx r

theorem agrees_of_eq (c : ℤ_[p]) (r : ℕ) : Agrees c c r := by
  simp [Agrees]

/-- `‖x‖ = p^(-v_p(x))` for nonzero `x : ℤ_[p]`, written with the ratio `p⁻¹`
(`PadicInt.norm_eq_zpow_neg_valuation`). -/
theorem norm_eq_inv_pow_valuation {x : ℤ_[p]} (hx : x ≠ 0) :
    ‖x‖ = ((p : ℝ)⁻¹) ^ x.valuation := by
  rw [PadicInt.norm_eq_zpow_neg_valuation hx, zpow_neg, zpow_natCast, inv_pow]

end Basic

section Identity

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι]

/-- Per-prediction identity: the weighted indicator series of one prediction
`z_j` sums to `(1 - |c - z_j|_p) / (1 - p⁻¹)`.  When `c = z_j` (the thesis'
`v_j(c) = ∞`, `p^{-∞} = 0`) this is the full geometric series
`(1 - p⁻¹)⁻¹`; otherwise it is the finite geometric sum
`∑_{r < v} p^(-r)` with `v = v_p(c - z_j)`. -/
theorem hasSum_score_term (c zj : ℤ_[p]) :
    HasSum (fun r : ℕ => weight p r * (if Agrees c zj (r + 1) then (1 : ℝ) else 0))
      ((1 - ‖c - zj‖) / (1 - (p : ℝ)⁻¹)) := by
  have hq0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_cast_nonneg
  have hq1 : (p : ℝ)⁻¹ < 1 := inv_cast_prime_lt_one
  have hk : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := one_sub_inv_cast_prime_pos
  by_cases hx : c - zj = 0
  · have hall : ∀ r : ℕ, Agrees c zj (r + 1) := fun r => by
      simp [Agrees, hx]
    simp only [hall, if_true, mul_one, weight_eq, hx, norm_zero, sub_zero, one_div]
    exact hasSum_geometric_of_lt_one hq0 hq1
  · set v := (c - zj).valuation with hv
    have hind : ∀ r : ℕ, Agrees c zj (r + 1) ↔ r < v := fun r => by
      rw [agrees_iff_le_valuation hx]
      omega
    have hzero : ∀ r ∉ Finset.range v,
        weight p r * (if Agrees c zj (r + 1) then (1 : ℝ) else 0) = 0 := by
      intro r hr
      rw [Finset.mem_range] at hr
      rw [if_neg (fun h => hr ((hind r).mp h)), mul_zero]
    have hsum : HasSum (fun r : ℕ => weight p r * (if Agrees c zj (r + 1) then (1 : ℝ) else 0))
        (∑ r ∈ Finset.range v, weight p r * (if Agrees c zj (r + 1) then (1 : ℝ) else 0)) :=
      hasSum_sum_of_ne_finset_zero hzero
    have hfin : ∑ r ∈ Finset.range v, weight p r * (if Agrees c zj (r + 1) then (1 : ℝ) else 0)
        = ∑ r ∈ Finset.range v, ((p : ℝ)⁻¹) ^ r := by
      refine Finset.sum_congr rfl (fun r hr => ?_)
      rw [weight_eq, if_pos ((hind r).mpr (Finset.mem_range.mp hr)), mul_one]
    rw [hfin, geom_sum_eq (ne_of_lt hq1) v] at hsum
    convert hsum using 1
    rw [norm_eq_inv_pow_valuation hx, ← hv,
      div_eq_div_iff hk.ne' (by linarith : (p : ℝ)⁻¹ - 1 ≠ 0)]
    ring

/-- The prefix count as a sum of indicators. -/
theorem prefixCount_eq_sum (z : ι → ℤ_[p]) (c : ℤ_[p]) (r : ℕ) :
    (prefixCount z c r : ℝ) = ∑ j, if Agrees c (z j) r then (1 : ℝ) else 0 := by
  rw [prefixCount, Finset.natCast_card_filter]

/-- The weighted prefix score converges, with value
`∑ j, (1 - |c - z_j|_p) / (1 - p⁻¹)`. -/
theorem hasSum_score (z : ι → ℤ_[p]) (c : ℤ_[p]) :
    HasSum (fun r : ℕ => weight p r * (prefixCount z c (r + 1) : ℝ))
      (∑ j, (1 - ‖c - z j‖) / (1 - (p : ℝ)⁻¹)) := by
  have h := hasSum_sum (s := Finset.univ) (fun j _ => hasSum_score_term c (z j))
  convert h using 1
  funext r
  rw [prefixCount_eq_sum, Finset.mul_sum]

theorem score_eq (z : ι → ℤ_[p]) (c : ℤ_[p]) :
    score z c = ∑ j, (1 - ‖c - z j‖) / (1 - (p : ℝ)⁻¹) :=
  (hasSum_score z c).tsum_eq

/-- **Proposition `prop:medoid-prefix-consensus`, displayed identity.**
`∑ j, |c - z_j|_p = m - (1 - p⁻¹) ∑_{r ≥ 1} p^{-(r-1)} #{j : z_j ≡ c (mod p^r)}`
with `m = Fintype.card ι`. -/
theorem prefix_consensus_identity (z : ι → ℤ_[p]) (c : ℤ_[p]) :
    cost z c = (Fintype.card ι : ℝ) - (1 - (p : ℝ)⁻¹) * score z c := by
  have hk : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := one_sub_inv_cast_prime_pos
  rw [score_eq, Finset.mul_sum, cost]
  have : ∀ j, (1 - (p : ℝ)⁻¹) * ((1 - ‖c - z j‖) / (1 - (p : ℝ)⁻¹)) = 1 - ‖c - z j‖ :=
    fun j => mul_div_cancel₀ _ hk.ne'
  simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]
  ring

/-- Equivalently, `score z c = (m - cost z c) / (1 - p⁻¹)`. -/
theorem score_eq_of_cost (z : ι → ℤ_[p]) (c : ℤ_[p]) :
    score z c = ((Fintype.card ι : ℝ) - cost z c) / (1 - (p : ℝ)⁻¹) := by
  have hk : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := one_sub_inv_cast_prime_pos
  rw [prefix_consensus_identity, sub_sub_cancel, mul_div_cancel_left₀ _ hk.ne']

/-- Comparing two candidates: lower medoid cost is exactly higher prefix score. -/
theorem cost_le_cost_iff (z : ι → ℤ_[p]) (c c' : ℤ_[p]) :
    cost z c ≤ cost z c' ↔ score z c' ≤ score z c := by
  have hk : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := one_sub_inv_cast_prime_pos
  rw [prefix_consensus_identity, prefix_consensus_identity, sub_le_sub_iff_left]
  constructor
  · intro h
    exact le_of_mul_le_mul_left h hk
  · intro h
    exact mul_le_mul_of_nonneg_left h hk.le

/-- **Proposition `prop:medoid-prefix-consensus`.**  On a finite candidate set
`C`, a candidate `c ∈ C` minimises the medoid objective `∑ j, |c - z_j|_p` over
`C` iff it maximises the weighted prefix score
`∑_{r ≥ 1} p^{-(r-1)} #{j : z_j ≡ c (mod p^r)}` over `C`. -/
theorem medoid_iff_maximises_score (z : ι → ℤ_[p]) (C : Finset ℤ_[p]) (c : ℤ_[p]) :
    (∀ c' ∈ C, cost z c ≤ cost z c') ↔ (∀ c' ∈ C, score z c' ≤ score z c) := by
  constructor
  · intro h c' hc'
    exact (cost_le_cost_iff z c c').mp (h c' hc')
  · intro h c' hc'
    exact (cost_le_cost_iff z c c').mpr (h c' hc')

/-- The same equivalence over all of `ℤ_[p]`. -/
theorem isGlobalMin_cost_iff_isGlobalMax_score (z : ι → ℤ_[p]) (c : ℤ_[p]) :
    IsGlobalMin (cost z) c ↔ IsGlobalMax (score z) c := by
  constructor
  · intro h c'
    exact (cost_le_cost_iff z c c').mp (h c')
  · intro h c'
    exact (cost_le_cost_iff z c c').mpr (h c')

/-- Prefix agreement is antitone in the depth `r`: agreement modulo `p^s`
implies agreement modulo `p^r` for `r ≤ s`. -/
theorem agrees_antitone {c zj : ℤ_[p]} {r s : ℕ} (hrs : r ≤ s) (h : Agrees c zj s) :
    Agrees c zj r := by
  unfold Agrees at h ⊢
  rw [Ideal.mem_span_singleton] at h ⊢
  exact (pow_dvd_pow (p : ℤ_[p]) hrs).trans h

theorem prefixCount_antitone (z : ι → ℤ_[p]) (c : ℤ_[p]) :
    Antitone (prefixCount z c) := by
  intro r s hrs
  unfold prefixCount
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, agrees_antitone hrs hj.2⟩

/-- Every prediction agrees with `c` to depth `0`, so `prefixCount z c 0 = m`. -/
theorem prefixCount_zero (z : ι → ℤ_[p]) (c : ℤ_[p]) :
    prefixCount z c 0 = Fintype.card ι := by
  unfold prefixCount
  rw [Finset.filter_true_of_mem, Finset.card_univ]
  intro j _
  simp [Agrees]

end Identity

section Capped

variable {p : ℕ} [hp : Fact p.Prime]

/-- The implemented bounded distance `min 1 |c - z|_p`. -/
noncomputable def cappedDist (c z : ℚ_[p]) : ℝ := min 1 ‖c - z‖

/-- A prediction with negative valuation has norm greater than `1`
(`Padic.norm_le_one_iff_val_nonneg`). -/
theorem one_lt_norm_of_valuation_neg {z : ℚ_[p]} (hz : z.valuation < 0) : 1 < ‖z‖ := by
  by_contra h
  exact absurd ((Padic.norm_le_one_iff_val_nonneg z).mp (not_lt.mp h)) (not_le.mpr hz)

/-- Ultrametric inequality: for integral `c` (`‖c‖ ≤ 1`) and `‖z‖ > 1`,
`|c - z|_p = |z|_p` (`Padic.add_eq_max_of_ne`). -/
theorem norm_sub_eq_of_one_lt_norm {c z : ℚ_[p]} (hc : ‖c‖ ≤ 1) (hz : 1 < ‖z‖) :
    ‖c - z‖ = ‖z‖ := by
  have hne : ‖c‖ ≠ ‖-z‖ := by
    rw [norm_neg]
    exact ne_of_lt (lt_of_le_of_lt hc hz)
  rw [sub_eq_add_neg, Padic.add_eq_max_of_ne hne, norm_neg]
  exact max_eq_right (le_of_lt (lt_of_le_of_lt hc hz))

/-- For every integral candidate `c : ℤ_[p]`, a non-integral prediction `z`
contributes the constant capped distance `1`. -/
theorem cappedDist_eq_one_of_one_lt_norm (c : ℤ_[p]) {z : ℚ_[p]} (hz : 1 < ‖z‖) :
    cappedDist (c : ℚ_[p]) z = 1 := by
  unfold cappedDist
  rw [norm_sub_eq_of_one_lt_norm (PadicInt.norm_le_one c) hz]
  exact min_eq_left hz.le

/-- For integral candidate and integral prediction the cap is inactive. -/
theorem cappedDist_eq_norm_of_norm_le_one (c : ℤ_[p]) {z : ℚ_[p]} (hz : ‖z‖ ≤ 1) :
    cappedDist (c : ℚ_[p]) z = ‖(c : ℚ_[p]) - z‖ := by
  unfold cappedDist
  apply min_eq_right
  calc ‖(c : ℚ_[p]) - z‖ ≤ max ‖(c : ℚ_[p])‖ ‖-z‖ := by
        rw [sub_eq_add_neg]; exact Padic.nonarchimedean _ _
    _ ≤ 1 := by
        rw [norm_neg]; exact max_le (PadicInt.norm_le_one c) hz

variable {ι : Type*} [Fintype ι]

/-- The implemented bounded medoid objective over rational predictions. -/
noncomputable def cappedCost (z : ι → ℚ_[p]) (c : ℤ_[p]) : ℝ :=
  ∑ j, cappedDist (c : ℚ_[p]) (z j)

/-- The integral predictions, as elements of `ℤ_[p]`. -/
noncomputable def integralPart (z : ι → ℚ_[p]) : {j : ι // ‖z j‖ ≤ 1} → ℤ_[p] :=
  fun j => ⟨z j.1, j.2⟩

/-- The bounded medoid objective splits into the constant number of
non-integral predictions plus the integral medoid cost of the proposition. -/
theorem cappedCost_eq (z : ι → ℚ_[p]) (c : ℤ_[p]) :
    cappedCost z c =
      ((Finset.univ.filter fun j : ι => 1 < ‖z j‖).card : ℝ) + cost (integralPart z) c := by
  unfold cappedCost cost
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : ι => 1 < ‖z j‖)]
  congr 1
  · rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_filter] at hj
    rw [cappedDist_eq_one_of_one_lt_norm c hj.2, Nat.cast_one]
  · rw [Finset.sum_subtype (Finset.univ.filter fun j : ι => ¬ 1 < ‖z j‖)
      (p := fun j : ι => ‖z j‖ ≤ 1) (fun j => by simp [not_lt])]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [cappedDist_eq_norm_of_norm_le_one c j.2, PadicInt.norm_def, PadicInt.coe_sub]
    rfl

/-- Comparing integral candidates under the bounded objective only sees the
integral predictions. -/
theorem cappedCost_le_iff (z : ι → ℚ_[p]) (c c' : ℤ_[p]) :
    cappedCost z c ≤ cappedCost z c' ↔
      score (integralPart z) c' ≤ score (integralPart z) c := by
  rw [cappedCost_eq, cappedCost_eq, add_le_add_iff_left, cost_le_cost_iff]

/-- The implemented bounded medoid over rational predictions is the
prefix-consensus maximiser for the integral predictions: on a finite candidate
set `C ⊆ ℤ_[p]`, `c ∈ C` minimises `cappedCost z` over `C` iff it maximises the
weighted prefix score of the integral predictions over `C`. -/
theorem capped_medoid_iff_maximises_score (z : ι → ℚ_[p]) (C : Finset ℤ_[p]) (c : ℤ_[p]) :
    (∀ c' ∈ C, cappedCost z c ≤ cappedCost z c') ↔
      (∀ c' ∈ C, score (integralPart z) c' ≤ score (integralPart z) c) := by
  constructor
  · intro h c' hc'
    exact (cappedCost_le_iff z c c').mp (h c' hc')
  · intro h c' hc'
    exact (cappedCost_le_iff z c c').mpr (h c' hc')

end Capped

end PhdThesisLean.PrefixConsensus

#print axioms PhdThesisLean.PrefixConsensus.hasSum_score_term
#print axioms PhdThesisLean.PrefixConsensus.hasSum_score
#print axioms PhdThesisLean.PrefixConsensus.prefix_consensus_identity
#print axioms PhdThesisLean.PrefixConsensus.medoid_iff_maximises_score
#print axioms PhdThesisLean.PrefixConsensus.isGlobalMin_cost_iff_isGlobalMax_score
#print axioms PhdThesisLean.PrefixConsensus.prefixCount_antitone
#print axioms PhdThesisLean.PrefixConsensus.cappedDist_eq_one_of_one_lt_norm
#print axioms PhdThesisLean.PrefixConsensus.cappedCost_eq
#print axioms PhdThesisLean.PrefixConsensus.capped_medoid_iff_maximises_score
