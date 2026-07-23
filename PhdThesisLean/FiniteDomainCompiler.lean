import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

namespace PhdThesisLean.FiniteDomainCompiler

open scoped BigOperators

/-!
# Finite-domain signed affine compiler

This module formalises the mathematical content of thesis Theorem
`thm:compiler-template` and Corollary `cor:qp-extension` from
`thesis-statements/finite-domain-compilers.tex`.

The domain alphabets are represented directly as finite subsets of `ℚ_[p]`
whose distinct elements are unit-separated. Integer alphabets with distinct
residue classes modulo `p` are a special case. Affine coefficients are allowed
to be arbitrary `p`-adic numbers of norm at most one, strengthening the
thesis's integer-coefficient assumption. The proof works over all of `ℚ_[p]`,
so it includes the extension corollary without a separate argument.

Signed observations are indexed by a finite type rather than stored in a
`Finset`, preserving repeated observations. The theorem proves existence of a
global minimiser in the finite product domain, exclusion of every point outside
that domain from the global minimisers, and the constant-plus-finite-objective
formula on the domain.
-/

def UnitSeparated
    {p : ℕ} [Fact p.Prime] (A : Finset ℚ_[p]) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ‖a - b‖ = 1

noncomputable def unaryCost
    {p : ℕ} [Fact p.Prime] (A : Finset ℚ_[p]) (x : ℚ_[p]) : ℝ :=
  ∑ a ∈ A, ‖x - a‖

theorem unaryCost_at_mem
    {p : ℕ} [Fact p.Prime] {A : Finset ℚ_[p]}
    (hsep : UnitSeparated A) {b : ℚ_[p]} (hb : b ∈ A) :
    unaryCost A b = A.card - 1 := by
  classical
  rw [unaryCost, ← Finset.sum_erase_add _ _ hb]
  have hsum :
      (∑ a ∈ A.erase b, ‖b - a‖) =
        ∑ _a ∈ A.erase b, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact hsep b hb a (Finset.mem_of_mem_erase ha)
      (Ne.symm (Finset.ne_of_mem_erase ha))
  rw [hsum]
  simp [Finset.card_erase_of_mem hb, Nat.cast_sub (Finset.card_pos.mpr ⟨b, hb⟩)]

theorem close_domain_point_unique
    {p : ℕ} [Fact p.Prime] {A : Finset ℚ_[p]}
    (hsep : UnitSeparated A) {x b c : ℚ_[p]}
    (hb : b ∈ A) (hc : c ∈ A)
    (hxb : ‖x - b‖ < 1) (hxc : ‖x - c‖ < 1) :
    b = c := by
  by_contra hbc
  have hle : ‖b - c‖ ≤ max ‖b - x‖ ‖x - c‖ := by
    rw [show b - c = (b - x) + (x - c) by ring]
    exact Padic.nonarchimedean _ _
  have hlt : max ‖b - x‖ ‖x - c‖ < 1 := by
    rw [max_lt_iff]
    simpa [norm_sub_rev] using And.intro hxb hxc
  rw [hsep b hb c hc hbc] at hle
  exact (not_lt_of_ge hle) hlt

theorem norm_sub_eq_one_of_close_to_domain
    {p : ℕ} [Fact p.Prime] {A : Finset ℚ_[p]}
    (hsep : UnitSeparated A) {x b a : ℚ_[p]}
    (hb : b ∈ A) (ha : a ∈ A) (hba : b ≠ a)
    (hxb : ‖x - b‖ < 1) :
    ‖x - a‖ = 1 := by
  rw [show x - a = (x - b) + (b - a) by ring]
  rw [Padic.add_eq_max_of_ne]
  · rw [hsep b hb a ha hba, max_eq_right hxb.le]
  · rw [hsep b hb a ha hba]
    exact ne_of_lt hxb

theorem unaryCost_snap_close
    {p : ℕ} [Fact p.Prime] {A : Finset ℚ_[p]}
    (hsep : UnitSeparated A) {x b : ℚ_[p]}
    (hb : b ∈ A) (hxb : ‖x - b‖ < 1) :
    unaryCost A b + ‖x - b‖ = unaryCost A x := by
  classical
  rw [unaryCost, unaryCost, ← Finset.sum_erase_add _ _ hb,
    ← Finset.sum_erase_add _ _ hb]
  have hleft :
      (∑ a ∈ A.erase b, ‖b - a‖) =
        ∑ _a ∈ A.erase b, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact hsep b hb a (Finset.mem_of_mem_erase ha)
      (Ne.symm (Finset.ne_of_mem_erase ha))
  have hright :
      (∑ a ∈ A.erase b, ‖x - a‖) =
        ∑ _a ∈ A.erase b, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact norm_sub_eq_one_of_close_to_domain hsep hb
      (Finset.mem_of_mem_erase ha)
      (Ne.symm (Finset.ne_of_mem_erase ha)) hxb
  rw [hleft, hright]
  simp

theorem norm_sub_eq_of_no_close
    {p : ℕ} [Fact p.Prime] {A : Finset ℚ_[p]}
    (hsep : UnitSeparated A) {x b : ℚ_[p]}
    (hb : b ∈ A) (hfar : ∀ a ∈ A, 1 ≤ ‖x - a‖) :
    ∀ a ∈ A, ‖x - a‖ = ‖x - b‖ := by
  intro a ha
  by_cases hab : a = b
  · subst a
    rfl
  have hbaNorm : ‖b - a‖ = 1 := hsep b hb a ha (Ne.symm hab)
  have hxb : 1 ≤ ‖x - b‖ := hfar b hb
  by_cases hxb1 : ‖x - b‖ = 1
  · apply le_antisymm
    · calc
        ‖x - a‖ = ‖(x - b) + (b - a)‖ := by ring_nf
        _ ≤ max ‖x - b‖ ‖b - a‖ := Padic.nonarchimedean _ _
        _ = ‖x - b‖ := by simp [hxb1, hbaNorm]
    · simpa [hxb1] using hfar a ha
  · rw [show x - a = (x - b) + (b - a) by ring]
    rw [Padic.add_eq_max_of_ne]
    · rw [hbaNorm, max_eq_left hxb]
    · rw [hbaNorm]
      exact hxb1

theorem unaryCost_eq_card_mul_of_no_close
    {p : ℕ} [Fact p.Prime] {A : Finset ℚ_[p]}
    (hsep : UnitSeparated A) {x b : ℚ_[p]}
    (hb : b ∈ A) (hfar : ∀ a ∈ A, 1 ≤ ‖x - a‖) :
    unaryCost A x = (A.card : ℝ) * ‖x - b‖ := by
  rw [unaryCost]
  calc
    (∑ a ∈ A, ‖x - a‖) = ∑ _a ∈ A, ‖x - b‖ := by
      apply Finset.sum_congr rfl
      intro a ha
      exact norm_sub_eq_of_no_close hsep hb hfar a ha
    _ = (A.card : ℝ) * ‖x - b‖ := by simp

theorem unaryCost_snap_far
    {p : ℕ} [Fact p.Prime] {A : Finset ℚ_[p]}
    (hsep : UnitSeparated A) {x b : ℚ_[p]}
    (hb : b ∈ A) (hfar : ∀ a ∈ A, 1 ≤ ‖x - a‖) :
    unaryCost A b + ‖x - b‖ ≤ unaryCost A x := by
  rw [unaryCost_at_mem hsep hb,
    unaryCost_eq_card_mul_of_no_close hsep hb hfar]
  have hcard : 1 ≤ A.card := Finset.card_pos.mpr ⟨b, hb⟩
  have hnorm : 1 ≤ ‖x - b‖ := hfar b hb
  have hcast : (1 : ℝ) ≤ A.card := by exact_mod_cast hcard
  nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : 0 ≤ (A.card : ℝ) - 1))
    (sub_nonneg.mpr hnorm)]

theorem exists_unaryCost_snap
    {p : ℕ} [Fact p.Prime] {A : Finset ℚ_[p]}
    (hne : A.Nonempty) (hsep : UnitSeparated A) {x : ℚ_[p]} :
    ∃ b ∈ A, unaryCost A b + ‖x - b‖ ≤ unaryCost A x := by
  classical
  by_cases hclose : ∃ b ∈ A, ‖x - b‖ < 1
  · obtain ⟨b, hb, hxb⟩ := hclose
    exact ⟨b, hb, (unaryCost_snap_close hsep hb hxb).le⟩
  · push_neg at hclose
    obtain ⟨b, hb⟩ := hne
    have hfar : ∀ a ∈ A, 1 ≤ ‖x - a‖ := by
      intro a ha
      exact hclose a ha
    exact ⟨b, hb, unaryCost_snap_far hsep hb hfar⟩

abbrev Parameter (p n : ℕ) [Fact p.Prime] := Fin n → ℚ_[p]

structure AffineObservation (p n : ℕ) [Fact p.Prime] where
  sign : ℝ
  weight : ℝ
  coeff : Fin n → ℚ_[p]
  target : ℚ_[p]

noncomputable def affineResidual
    {p n : ℕ} [Fact p.Prime] (t : AffineObservation p n)
    (x : Parameter p n) : ℚ_[p] :=
  ∑ i, t.coeff i * x i - t.target

theorem affineResidual_update
    {p n : ℕ} [Fact p.Prime] (t : AffineObservation p n)
    (x : Parameter p n) (i : Fin n) (b : ℚ_[p]) :
    affineResidual t (Function.update x i b) - affineResidual t x =
      t.coeff i * (b - x i) := by
  classical
  rw [affineResidual, affineResidual]
  simp only [sub_sub_sub_cancel_right]
  have hsum :
      (∑ j ∈ Finset.univ \ {i},
          t.coeff j * Function.update x i b j) =
        ∑ j ∈ Finset.univ \ {i}, t.coeff j * x j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [Function.update, hji]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i),
    Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
  rw [show Function.update x i b i = b by simp [Function.update]]
  rw [hsum]
  ring

theorem affineTerm_update_le
    {p n : ℕ} [Fact p.Prime] (t : AffineObservation p n)
    (x : Parameter p n) (i : Fin n) (b : ℚ_[p])
    (hsign : |t.sign| = 1) (hweight : 0 ≤ t.weight)
    (hcoeff : ‖t.coeff i‖ ≤ 1) :
    t.sign * t.weight * ‖affineResidual t (Function.update x i b)‖ -
        t.sign * t.weight * ‖affineResidual t x‖
      ≤ t.weight * ‖x i - b‖ := by
  have hres :
      |‖affineResidual t (Function.update x i b)‖ -
          ‖affineResidual t x‖| ≤ ‖x i - b‖ := by
    calc
      |‖affineResidual t (Function.update x i b)‖ -
          ‖affineResidual t x‖|
          ≤ ‖affineResidual t (Function.update x i b) -
              affineResidual t x‖ := abs_norm_sub_norm_le _ _
      _ = ‖t.coeff i‖ * ‖b - x i‖ := by
        rw [affineResidual_update, norm_mul]
      _ ≤ 1 * ‖b - x i‖ :=
        mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
      _ = ‖x i - b‖ := by simp [norm_sub_rev]
  calc
    t.sign * t.weight * ‖affineResidual t (Function.update x i b)‖ -
        t.sign * t.weight * ‖affineResidual t x‖ =
        (t.sign * t.weight) *
          (‖affineResidual t (Function.update x i b)‖ -
            ‖affineResidual t x‖) := by ring
    _ ≤ |(t.sign * t.weight) *
          (‖affineResidual t (Function.update x i b)‖ -
            ‖affineResidual t x‖)| := le_abs_self _
    _ = t.weight *
          |‖affineResidual t (Function.update x i b)‖ -
            ‖affineResidual t x‖| := by
      rw [abs_mul, abs_mul, hsign, abs_of_nonneg hweight]
      ring
    _ ≤ t.weight * ‖x i - b‖ :=
      mul_le_mul_of_nonneg_left hres hweight

theorem affineTerm_update_eq_of_coeff_eq_zero
    {p n : ℕ} [Fact p.Prime] (t : AffineObservation p n)
    (x : Parameter p n) (i : Fin n) (b : ℚ_[p])
    (hzero : t.coeff i = 0) :
    t.sign * t.weight * ‖affineResidual t (Function.update x i b)‖ =
      t.sign * t.weight * ‖affineResidual t x‖ := by
  have hres :
      affineResidual t (Function.update x i b) =
        affineResidual t x := by
    apply sub_eq_zero.mp
    rw [affineResidual_update, hzero, zero_mul]
  rw [hres]

noncomputable def interactionLoss
    {p n : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (T : ι → AffineObservation p n) (x : Parameter p n) : ℝ :=
  ∑ l, (T l).sign * (T l).weight * ‖affineResidual (T l) x‖

noncomputable def incidentWeight
    {p n : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (T : ι → AffineObservation p n) (i : Fin n) : ℝ := by
  classical
  exact ∑ l, if (T l).coeff i = 0 then 0 else (T l).weight

theorem interactionLoss_update_le
    {p n : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (T : ι → AffineObservation p n) (x : Parameter p n)
    (i : Fin n) (b : ℚ_[p])
    (hsign : ∀ l, |(T l).sign| = 1)
    (hweight : ∀ l, 0 ≤ (T l).weight)
    (hcoeff : ∀ l j, ‖(T l).coeff j‖ ≤ 1) :
    interactionLoss T (Function.update x i b) - interactionLoss T x
      ≤ incidentWeight T i * ‖x i - b‖ := by
  classical
  rw [interactionLoss, interactionLoss, ← Finset.sum_sub_distrib,
    incidentWeight, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro l _
  by_cases hzero : (T l).coeff i = 0
  · simp [hzero, affineTerm_update_eq_of_coeff_eq_zero (T l) x i b hzero]
  · simpa [hzero] using
      affineTerm_update_le (T l) x i b (hsign l) (hweight l) (hcoeff l i)

noncomputable def pinningLoss
    {p n : ℕ} [Fact p.Prime]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : Fin n → ℝ)
    (x : Parameter p n) : ℝ :=
  ∑ i, pinWeight i * unaryCost (D i) (x i)

theorem pinningLoss_update
    {p n : ℕ} [Fact p.Prime]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : Fin n → ℝ)
    (x : Parameter p n) (i : Fin n) (b : ℚ_[p]) :
    pinningLoss D pinWeight (Function.update x i b) - pinningLoss D pinWeight x =
      pinWeight i * (unaryCost (D i) b - unaryCost (D i) (x i)) := by
  classical
  rw [pinningLoss, pinningLoss]
  have hsum :
      (∑ j ∈ Finset.univ \ {i},
          pinWeight j * unaryCost (D j) (Function.update x i b j)) =
        ∑ j ∈ Finset.univ \ {i},
          pinWeight j * unaryCost (D j) (x j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [Function.update, hji]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i),
    Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
  rw [show Function.update x i b i = b by simp [Function.update]]
  rw [hsum]
  ring

noncomputable def compilerLoss
    {p n : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : Fin n → ℝ)
    (T : ι → AffineObservation p n) (x : Parameter p n) : ℝ :=
  pinningLoss D pinWeight x + interactionLoss T x

theorem compilerLoss_snap_le
    {p n : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : Fin n → ℝ)
    (T : ι → AffineObservation p n) (x : Parameter p n)
    (i : Fin n) (b : ℚ_[p])
    (hunary : unaryCost (D i) b + ‖x i - b‖ ≤ unaryCost (D i) (x i))
    (hpin : 0 ≤ pinWeight i)
    (hsign : ∀ l, |(T l).sign| = 1)
    (hweight : ∀ l, 0 ≤ (T l).weight)
    (hcoeff : ∀ l j, ‖(T l).coeff j‖ ≤ 1) :
    compilerLoss D pinWeight T (Function.update x i b) -
        compilerLoss D pinWeight T x
      ≤ (incidentWeight T i - pinWeight i) * ‖x i - b‖ := by
  have hpinChange :
      pinningLoss D pinWeight (Function.update x i b) -
          pinningLoss D pinWeight x
        ≤ -(pinWeight i * ‖x i - b‖) := by
    rw [pinningLoss_update]
    have hd :
        unaryCost (D i) b - unaryCost (D i) (x i) ≤ -‖x i - b‖ := by
      linarith
    simpa only [mul_neg, neg_mul] using mul_le_mul_of_nonneg_left hd hpin
  have hinteraction :=
    interactionLoss_update_le T x i b hsign hweight hcoeff
  rw [compilerLoss, compilerLoss]
  linarith

theorem exists_compilerLoss_snap
    {p n : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : Fin n → ℝ)
    (T : ι → AffineObservation p n)
    (hne : ∀ i, (D i).Nonempty)
    (hsep : ∀ i, UnitSeparated (D i))
    (hdomination : ∀ i, incidentWeight T i < pinWeight i)
    (hsign : ∀ l, |(T l).sign| = 1)
    (hweight : ∀ l, 0 ≤ (T l).weight)
    (hcoeff : ∀ l j, ‖(T l).coeff j‖ ≤ 1)
    (x : Parameter p n) (i : Fin n) (hxi : x i ∉ D i) :
    ∃ b ∈ D i,
      compilerLoss D pinWeight T (Function.update x i b) <
        compilerLoss D pinWeight T x := by
  obtain ⟨b, hb, hunary⟩ :=
    exists_unaryCost_snap (hne i) (hsep i)
  refine ⟨b, hb, ?_⟩
  have hincident_nonneg : 0 ≤ incidentWeight T i := by
    classical
    rw [incidentWeight]
    exact Finset.sum_nonneg fun l _ => by
      split <;> simp_all
  have hpin : 0 ≤ pinWeight i :=
    le_trans hincident_nonneg (hdomination i).le
  have hsnap := compilerLoss_snap_le D pinWeight T x i b hunary hpin
    hsign hweight hcoeff
  have hdist : 0 < ‖x i - b‖ := norm_pos_iff.mpr fun hxb => by
    apply hxi
    rw [sub_eq_zero.mp hxb]
    exact hb
  have hfactor : incidentWeight T i - pinWeight i < 0 := sub_neg.mpr (hdomination i)
  linarith [mul_neg_of_neg_of_pos hfactor hdist]

def InDomain
    {p n : ℕ} [Fact p.Prime]
    (D : Fin n → Finset ℚ_[p]) (x : Parameter p n) : Prop :=
  ∀ i, x i ∈ D i

noncomputable def outsideDomain
    {p n : ℕ} [Fact p.Prime]
    (D : Fin n → Finset ℚ_[p]) (x : Parameter p n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => x i ∉ D i

theorem outsideDomain_eq_empty_iff
    {p n : ℕ} [Fact p.Prime]
    (D : Fin n → Finset ℚ_[p]) (x : Parameter p n) :
    outsideDomain D x = ∅ ↔ InDomain D x := by
  classical
  simp [outsideDomain, InDomain]

theorem outsideDomain_update
    {p n : ℕ} [Fact p.Prime]
    (D : Fin n → Finset ℚ_[p]) (x : Parameter p n)
    (i : Fin n) (b : ℚ_[p]) (hb : b ∈ D i) :
    outsideDomain D (Function.update x i b) =
      (outsideDomain D x).erase i := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [outsideDomain, Function.update, hb]
  · simp [outsideDomain, Function.update, hji]

theorem compiler_global_minimizer_inDomain
    {p n : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : Fin n → ℝ)
    (T : ι → AffineObservation p n)
    (hne : ∀ i, (D i).Nonempty)
    (hsep : ∀ i, UnitSeparated (D i))
    (hdomination : ∀ i, incidentWeight T i < pinWeight i)
    (hsign : ∀ l, |(T l).sign| = 1)
    (hweight : ∀ l, 0 ≤ (T l).weight)
    (hcoeff : ∀ l j, ‖(T l).coeff j‖ ≤ 1)
    (x : Parameter p n)
    (hmin : ∀ y, compilerLoss D pinWeight T x ≤ compilerLoss D pinWeight T y) :
    InDomain D x := by
  intro i
  by_contra hxi
  obtain ⟨b, hb, hsnap⟩ :=
    exists_compilerLoss_snap D pinWeight T hne hsep hdomination
      hsign hweight hcoeff x i hxi
  exact (not_lt_of_ge (hmin (Function.update x i b))) hsnap

theorem exists_inDomain_not_greater
    {p n : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : Fin n → ℝ)
    (T : ι → AffineObservation p n)
    (hne : ∀ i, (D i).Nonempty)
    (hsep : ∀ i, UnitSeparated (D i))
    (hdomination : ∀ i, incidentWeight T i < pinWeight i)
    (hsign : ∀ l, |(T l).sign| = 1)
    (hweight : ∀ l, 0 ≤ (T l).weight)
    (hcoeff : ∀ l j, ‖(T l).coeff j‖ ≤ 1)
    (x : Parameter p n) :
    ∃ y, InDomain D y ∧
      compilerLoss D pinWeight T y ≤ compilerLoss D pinWeight T x := by
  classical
  generalize hk : (outsideDomain D x).card = k
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
      by_cases hx : InDomain D x
      · exact ⟨x, hx, le_rfl⟩
      · have hbad : (outsideDomain D x).Nonempty := by
          exact Finset.nonempty_iff_ne_empty.mpr fun hempty =>
            hx ((outsideDomain_eq_empty_iff D x).mp hempty)
        obtain ⟨i, hi⟩ := hbad
        have hxi : x i ∉ D i := by
          simpa [outsideDomain] using hi
        obtain ⟨b, hb, hsnap⟩ :=
          exists_compilerLoss_snap D pinWeight T hne hsep hdomination
            hsign hweight hcoeff x i hxi
        let x' := Function.update x i b
        have houtside :
            outsideDomain D x' = (outsideDomain D x).erase i := by
          exact outsideDomain_update D x i b hb
        have hcardlt : (outsideDomain D x').card < k := by
          have hpos : 0 < (outsideDomain D x).card :=
            Finset.card_pos.mpr ⟨i, hi⟩
          rw [houtside, Finset.card_erase_of_mem hi, hk]
          omega
        obtain ⟨y, hyD, hyle⟩ := ih _ hcardlt x' rfl
        exact ⟨y, hyD, hyle.trans hsnap.le⟩

abbrev DomainAssignment
    {p n : ℕ} [Fact p.Prime]
    (D : Fin n → Finset ℚ_[p]) :=
  ∀ i, {a : ℚ_[p] // a ∈ D i}

def DomainAssignment.toParameter
    {p n : ℕ} [Fact p.Prime] {D : Fin n → Finset ℚ_[p]}
    (x : DomainAssignment D) : Parameter p n :=
  fun i => x i

theorem toParameter_inDomain
    {p n : ℕ} [Fact p.Prime] {D : Fin n → Finset ℚ_[p]}
    (x : DomainAssignment D) :
    InDomain D x.toParameter :=
  fun i => (x i).property

theorem exists_compiler_global_minimizer
    {p n : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : Fin n → ℝ)
    (T : ι → AffineObservation p n)
    (hne : ∀ i, (D i).Nonempty)
    (hsep : ∀ i, UnitSeparated (D i))
    (hdomination : ∀ i, incidentWeight T i < pinWeight i)
    (hsign : ∀ l, |(T l).sign| = 1)
    (hweight : ∀ l, 0 ≤ (T l).weight)
    (hcoeff : ∀ l j, ‖(T l).coeff j‖ ≤ 1) :
    ∃ x, InDomain D x ∧
      ∀ y, compilerLoss D pinWeight T x ≤ compilerLoss D pinWeight T y := by
  classical
  let a₀ : DomainAssignment D :=
    fun i => ⟨(hne i).choose, (hne i).choose_spec⟩
  have huniv : (Finset.univ : Finset (DomainAssignment D)).Nonempty :=
    ⟨a₀, Finset.mem_univ _⟩
  obtain ⟨a, _, ha⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (DomainAssignment D))
      (fun z => compilerLoss D pinWeight T z.toParameter) huniv
  refine ⟨a.toParameter, toParameter_inDomain a, ?_⟩
  intro y
  obtain ⟨z, hzD, hzy⟩ :=
    exists_inDomain_not_greater D pinWeight T hne hsep hdomination
      hsign hweight hcoeff y
  let az : DomainAssignment D := fun i => ⟨z i, hzD i⟩
  exact (ha az (Finset.mem_univ _)).trans hzy

noncomputable def domainPinningConstant
    {p n : ℕ} [Fact p.Prime]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : Fin n → ℝ) : ℝ :=
  ∑ i, pinWeight i * ((D i).card - 1)

noncomputable def finiteInteractionObjective
    {p n : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (T : ι → AffineObservation p n) (x : Parameter p n) : ℝ := by
  classical
  exact ∑ l,
    if affineResidual (T l) x = 0 then 0 else (T l).sign * (T l).weight

theorem pinningLoss_on_domain
    {p n : ℕ} [Fact p.Prime]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : Fin n → ℝ)
    (hsep : ∀ i, UnitSeparated (D i))
    (x : Parameter p n) (hx : InDomain D x) :
    pinningLoss D pinWeight x = domainPinningConstant D pinWeight := by
  rw [pinningLoss, domainPinningConstant]
  apply Finset.sum_congr rfl
  intro i _
  rw [unaryCost_at_mem (hsep i) (hx i)]

theorem interactionLoss_on_zero_or_unit_residuals
    {p n : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (T : ι → AffineObservation p n) (x : Parameter p n)
    (hunit : ∀ l, affineResidual (T l) x = 0 ∨
      ‖affineResidual (T l) x‖ = 1) :
    interactionLoss T x = finiteInteractionObjective T x := by
  classical
  rw [interactionLoss, finiteInteractionObjective]
  apply Finset.sum_congr rfl
  intro l _
  rcases hunit l with hzero | hone
  · simp [hzero]
  · have hne : affineResidual (T l) x ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hone
      norm_num at hone
    simp [hne, hone]

theorem compilerLoss_on_domain
    {p n : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : Fin n → ℝ)
    (T : ι → AffineObservation p n)
    (hsep : ∀ i, UnitSeparated (D i))
    (hunit : ∀ x, InDomain D x → ∀ l,
      affineResidual (T l) x = 0 ∨ ‖affineResidual (T l) x‖ = 1)
    (x : Parameter p n) (hx : InDomain D x) :
    compilerLoss D pinWeight T x =
      domainPinningConstant D pinWeight + finiteInteractionObjective T x := by
  rw [compilerLoss, pinningLoss_on_domain D pinWeight hsep x hx,
    interactionLoss_on_zero_or_unit_residuals T x (hunit x hx)]

theorem finite_domain_signed_affine_compiler
    {p n : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : Fin n → ℝ)
    (T : ι → AffineObservation p n)
    (hne : ∀ i, (D i).Nonempty)
    (hsep : ∀ i, UnitSeparated (D i))
    (hdomination : ∀ i, incidentWeight T i < pinWeight i)
    (hsign : ∀ l, |(T l).sign| = 1)
    (hweight : ∀ l, 0 ≤ (T l).weight)
    (hcoeff : ∀ l j, ‖(T l).coeff j‖ ≤ 1)
    (hunit : ∀ x, InDomain D x → ∀ l,
      affineResidual (T l) x = 0 ∨ ‖affineResidual (T l) x‖ = 1) :
    (∃ x, InDomain D x ∧
      ∀ y, compilerLoss D pinWeight T x ≤ compilerLoss D pinWeight T y) ∧
    (∀ x, (∀ y,
      compilerLoss D pinWeight T x ≤ compilerLoss D pinWeight T y) →
      InDomain D x) ∧
    (∀ x, InDomain D x →
      compilerLoss D pinWeight T x =
        domainPinningConstant D pinWeight + finiteInteractionObjective T x) := by
  refine ⟨exists_compiler_global_minimizer D pinWeight T hne hsep
    hdomination hsign hweight hcoeff, ?_, ?_⟩
  · intro x hmin
    exact compiler_global_minimizer_inDomain D pinWeight T hne hsep
      hdomination hsign hweight hcoeff x hmin
  · exact compilerLoss_on_domain D pinWeight T hsep hunit

end PhdThesisLean.FiniteDomainCompiler
