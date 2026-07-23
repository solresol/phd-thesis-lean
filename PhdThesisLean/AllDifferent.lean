import PhdThesisLean.FiniteDomainCompiler

namespace PhdThesisLean.AllDifferent

open scoped BigOperators
open PhdThesisLean.FiniteDomainCompiler

/-!
# All-different and list-colouring objectives

This module formalises the mathematical content of thesis Theorem
`thm:all-different` from `thesis-statements/finite-domain-compilers.tex`.
Edges are indexed by an arbitrary finite type, so repeated constraints remain
distinct and edge weights are supported directly.

The principal theorem `all_different_correctness` proves that the signed
affine p-adic objective attains a global minimum and that its global minimisers
are exactly the domain-respecting assignments of minimum weighted conflict.
`allDifferentLoss_eq` proves the displayed constant-minus-total-edge-weight
plus conflict formula. When a proper assignment exists and every edge weight
is positive, `globalMin_allDifferentLoss_iff_proper_of_satisfiable` proves that
the global minimisers are exactly the proper list-colourings.
-/

noncomputable def edgeObservation
    {p n : ℕ} [Fact p.Prime] {ε : Type*}
    (left right : ε → Fin n) (edgeWeight : ε → ℝ) (e : ε) :
    AffineObservation p n where
  sign := -1
  weight := edgeWeight e
  coeff j := if j = left e then 1 else if j = right e then -1 else 0
  target := 0

theorem edgeResidual
    {p n : ℕ} [Fact p.Prime] {ε : Type*}
    (left right : ε → Fin n) (edgeWeight : ε → ℝ)
    (hne : ∀ e, left e ≠ right e)
    (e : ε) (x : Parameter p n) :
    affineResidual (edgeObservation left right edgeWeight e) x =
      x (left e) - x (right e) := by
  classical
  rw [affineResidual, edgeObservation]
  simp only [sub_zero]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ (left e))]
  rw [if_pos rfl, one_mul]
  have hrmem : right e ∈ Finset.univ \ {left e} := by
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, by simpa using Ne.symm (hne e)⟩
  rw [Finset.sum_eq_add_sum_diff_singleton hrmem]
  rw [if_neg (Ne.symm (hne e)), if_pos rfl, neg_one_mul]
  have hrest :
      (∑ j ∈ (Finset.univ \ {left e}) \ {right e},
        (if j = left e then (1 : ℚ_[p])
          else if j = right e then -1 else 0) * x j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj_outer :=
      Finset.mem_sdiff.mp hj
    have hj_inner :=
      Finset.mem_sdiff.mp hj_outer.1
    have hjl : j ≠ left e := by simpa using hj_inner.2
    have hjr : j ≠ right e := by simpa using hj_outer.2
    simp [hjl, hjr]
  rw [hrest]
  ring

theorem edgeObservation_sign
    {p n : ℕ} [Fact p.Prime] {ε : Type*}
    (left right : ε → Fin n) (edgeWeight : ε → ℝ) (e : ε) :
    |(edgeObservation (p := p) left right edgeWeight e).sign| = 1 := by
  simp [edgeObservation]

theorem edgeObservation_coeff_norm
    {p n : ℕ} [Fact p.Prime] {ε : Type*}
    (left right : ε → Fin n) (edgeWeight : ε → ℝ) (e : ε) (i : Fin n) :
    ‖(edgeObservation (p := p) left right edgeWeight e).coeff i‖ ≤ 1 := by
  simp only [edgeObservation]
  split
  · rw [norm_one]
  · split
    · rw [norm_neg, norm_one]
    · rw [norm_zero]
      exact zero_le_one

noncomputable def allDifferentLoss
    {p n : ℕ} [Fact p.Prime] {ε : Type*} [Fintype ε]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : ℝ)
    (left right : ε → Fin n) (edgeWeight : ε → ℝ)
    (x : Parameter p n) : ℝ :=
  compilerLoss D (fun _ => pinWeight)
    (edgeObservation left right edgeWeight) x

noncomputable def conflictWeight
    {p n : ℕ} [Fact p.Prime] {ε : Type*} [Fintype ε]
    (left right : ε → Fin n) (edgeWeight : ε → ℝ)
    (x : Parameter p n) : ℝ := by
  classical
  exact ∑ e, if x (left e) = x (right e) then edgeWeight e else 0

noncomputable def incidentEdgeWeight
    {n : ℕ} {ε : Type*} [Fintype ε]
    (left right : ε → Fin n) (edgeWeight : ε → ℝ)
    (i : Fin n) : ℝ := by
  classical
  exact ∑ e,
    if i = left e ∨ i = right e then edgeWeight e else 0

theorem incidentWeight_edgeObservation
    {p n : ℕ} [Fact p.Prime] {ε : Type*} [Fintype ε]
    (left right : ε → Fin n) (edgeWeight : ε → ℝ) (i : Fin n) :
    incidentWeight (edgeObservation (p := p) left right edgeWeight) i =
      incidentEdgeWeight left right edgeWeight i := by
  classical
  rw [incidentWeight, incidentEdgeWeight]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hil : i = left e
  · simp [edgeObservation, hil]
  · by_cases hir : i = right e
    · have hrl : right e ≠ left e := by
        intro h
        exact hil (hir.trans h)
      simp [edgeObservation, hir, hrl]
    · simp [edgeObservation, hil, hir]

def GloballyUnitSeparated
    {p n : ℕ} [Fact p.Prime] (D : Fin n → Finset ℚ_[p]) : Prop :=
  ∀ i, ∀ a ∈ D i, ∀ j, ∀ b ∈ D j, a ≠ b → ‖a - b‖ = 1

theorem globallyUnitSeparated_local
    {p n : ℕ} [Fact p.Prime] {D : Fin n → Finset ℚ_[p]}
    (hsep : GloballyUnitSeparated D) (i : Fin n) :
    UnitSeparated (D i) := by
  intro a ha b hb hab
  exact hsep i a ha i b hb hab

theorem edge_zero_or_unit
    {p n : ℕ} [Fact p.Prime] {ε : Type*}
    (D : Fin n → Finset ℚ_[p])
    (left right : ε → Fin n) (edgeWeight : ε → ℝ)
    (hne : ∀ e, left e ≠ right e)
    (hsep : GloballyUnitSeparated D)
    (x : Parameter p n) (hx : InDomain D x) (e : ε) :
    affineResidual (edgeObservation left right edgeWeight e) x = 0 ∨
      ‖affineResidual (edgeObservation left right edgeWeight e) x‖ = 1 := by
  rw [edgeResidual left right edgeWeight hne e x]
  by_cases heq : x (left e) = x (right e)
  · left
    exact sub_eq_zero.mpr heq
  · right
    exact hsep (left e) _ (hx (left e)) (right e) _ (hx (right e)) heq

theorem allDifferentLoss_eq
    {p n : ℕ} [Fact p.Prime] {ε : Type*} [Fintype ε]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : ℝ)
    (left right : ε → Fin n) (edgeWeight : ε → ℝ)
    (hne : ∀ e, left e ≠ right e)
    (hsep : GloballyUnitSeparated D)
    (x : Parameter p n) (hx : InDomain D x) :
    allDifferentLoss D pinWeight left right edgeWeight x =
      pinWeight * (∑ i, (((D i).card : ℝ) - 1)) -
        (∑ e, edgeWeight e) +
        conflictWeight left right edgeWeight x := by
  classical
  have hlocal : ∀ i, UnitSeparated (D i) :=
    globallyUnitSeparated_local hsep
  have hpin :
      domainPinningConstant D (fun _ => pinWeight) =
        pinWeight * (∑ i, (((D i).card : ℝ) - 1)) := by
    rw [domainPinningConstant]
    exact (Finset.mul_sum Finset.univ
      (fun i : Fin n => ((D i).card : ℝ) - 1) pinWeight).symm
  have hedge : ∀ e,
      ‖affineResidual (edgeObservation left right edgeWeight e) x‖ =
        if x (left e) = x (right e) then 0 else 1 := by
    intro e
    rw [edgeResidual left right edgeWeight hne e x]
    split
    · rename_i heq
      rw [heq, sub_self, norm_zero]
    · rename_i hneq
      exact hsep (left e) _ (hx (left e))
        (right e) _ (hx (right e)) hneq
  have hinteraction :
      interactionLoss (edgeObservation left right edgeWeight) x =
        -(∑ e, edgeWeight e) +
          conflictWeight left right edgeWeight x := by
    classical
    rw [interactionLoss, conflictWeight]
    calc
      (∑ e, (edgeObservation left right edgeWeight e).sign *
          (edgeObservation left right edgeWeight e).weight *
          ‖affineResidual (edgeObservation left right edgeWeight e) x‖) =
          ∑ e, (-(edgeWeight e) +
            if x (left e) = x (right e) then edgeWeight e else 0) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [hedge e]
        simp only [edgeObservation]
        split <;> ring
      _ = -(∑ e, edgeWeight e) +
          ∑ e, (if x (left e) = x (right e) then edgeWeight e else 0) := by
        rw [Finset.sum_add_distrib]
        simp
  rw [allDifferentLoss, compilerLoss,
    pinningLoss_on_domain D (fun _ => pinWeight) hlocal x hx,
    hpin, hinteraction]
  ring

def IsGlobalMin {α : Type*} (f : α → ℝ) (x : α) : Prop :=
  ∀ y, f x ≤ f y

def MinimizesConflicts
    {p n : ℕ} [Fact p.Prime] {ε : Type*} [Fintype ε]
    (D : Fin n → Finset ℚ_[p])
    (left right : ε → Fin n) (edgeWeight : ε → ℝ)
    (x : Parameter p n) : Prop :=
  InDomain D x ∧
    ∀ y, InDomain D y →
      conflictWeight left right edgeWeight x ≤
        conflictWeight left right edgeWeight y

theorem globalMin_allDifferentLoss_iff
    {p n : ℕ} [Fact p.Prime] {ε : Type*} [Fintype ε]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : ℝ)
    (left right : ε → Fin n) (edgeWeight : ε → ℝ)
    (hneD : ∀ i, (D i).Nonempty)
    (hneEdge : ∀ e, left e ≠ right e)
    (hsep : GloballyUnitSeparated D)
    (hweight : ∀ e, 0 ≤ edgeWeight e)
    (hdomination : ∀ i,
      incidentEdgeWeight left right edgeWeight i < pinWeight)
    (x : Parameter p n) :
    IsGlobalMin (allDifferentLoss D pinWeight left right edgeWeight) x ↔
      MinimizesConflicts D left right edgeWeight x := by
  let T : ε → AffineObservation p n :=
    edgeObservation left right edgeWeight
  have hlocal : ∀ i, UnitSeparated (D i) :=
    globallyUnitSeparated_local hsep
  have hdomination' : ∀ i, incidentWeight T i < (fun _ => pinWeight) i := by
    intro i
    rw [incidentWeight_edgeObservation left right edgeWeight i]
    exact hdomination i
  have hsign : ∀ e, |(T e).sign| = 1 :=
    edgeObservation_sign left right edgeWeight
  have hcoeff : ∀ e i, ‖(T e).coeff i‖ ≤ 1 :=
    edgeObservation_coeff_norm left right edgeWeight
  constructor
  · intro hmin
    have hxD : InDomain D x := by
      apply compiler_global_minimizer_inDomain D (fun _ => pinWeight) T
        hneD hlocal hdomination' hsign hweight hcoeff x
      simpa [IsGlobalMin, allDifferentLoss, T] using hmin
    refine ⟨hxD, ?_⟩
    intro y hyD
    have hxy := hmin y
    rw [allDifferentLoss_eq D pinWeight left right edgeWeight hneEdge hsep x hxD,
      allDifferentLoss_eq D pinWeight left right edgeWeight hneEdge hsep y hyD] at hxy
    linarith
  · rintro ⟨hxD, hxConflict⟩
    intro y
    obtain ⟨z, hzD, hzy⟩ :=
      exists_inDomain_not_greater D (fun _ => pinWeight) T
        hneD hlocal hdomination' hsign hweight hcoeff y
    have hxzConflict := hxConflict z hzD
    have hxz :
        allDifferentLoss D pinWeight left right edgeWeight x ≤
          allDifferentLoss D pinWeight left right edgeWeight z := by
      rw [allDifferentLoss_eq D pinWeight left right edgeWeight hneEdge hsep x hxD,
        allDifferentLoss_eq D pinWeight left right edgeWeight hneEdge hsep z hzD]
      linarith
    exact hxz.trans (by simpa [allDifferentLoss, T] using hzy)

theorem exists_allDifferentLoss_globalMin
    {p n : ℕ} [Fact p.Prime] {ε : Type*} [Fintype ε]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : ℝ)
    (left right : ε → Fin n) (edgeWeight : ε → ℝ)
    (hneD : ∀ i, (D i).Nonempty)
    (_hneEdge : ∀ e, left e ≠ right e)
    (hsep : GloballyUnitSeparated D)
    (hweight : ∀ e, 0 ≤ edgeWeight e)
    (hdomination : ∀ i,
      incidentEdgeWeight left right edgeWeight i < pinWeight) :
    ∃ x, IsGlobalMin
      (allDifferentLoss D pinWeight left right edgeWeight) x := by
  let T : ε → AffineObservation p n :=
    edgeObservation left right edgeWeight
  have hlocal : ∀ i, UnitSeparated (D i) :=
    globallyUnitSeparated_local hsep
  have hdomination' : ∀ i, incidentWeight T i < (fun _ => pinWeight) i := by
    intro i
    rw [incidentWeight_edgeObservation left right edgeWeight i]
    exact hdomination i
  obtain ⟨x, _, hmin⟩ :=
    exists_compiler_global_minimizer D (fun _ => pinWeight) T
      hneD hlocal hdomination'
      (edgeObservation_sign left right edgeWeight) hweight
      (edgeObservation_coeff_norm left right edgeWeight)
  exact ⟨x, by simpa [IsGlobalMin, allDifferentLoss, T] using hmin⟩

theorem all_different_correctness
    {p n : ℕ} [Fact p.Prime] {ε : Type*} [Fintype ε]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : ℝ)
    (left right : ε → Fin n) (edgeWeight : ε → ℝ)
    (hneD : ∀ i, (D i).Nonempty)
    (hneEdge : ∀ e, left e ≠ right e)
    (hsep : GloballyUnitSeparated D)
    (hweight : ∀ e, 0 ≤ edgeWeight e)
    (hdomination : ∀ i,
      incidentEdgeWeight left right edgeWeight i < pinWeight) :
    (∃ x, IsGlobalMin
      (allDifferentLoss D pinWeight left right edgeWeight) x) ∧
    ∀ x, IsGlobalMin
      (allDifferentLoss D pinWeight left right edgeWeight) x ↔
        MinimizesConflicts D left right edgeWeight x := by
  exact ⟨exists_allDifferentLoss_globalMin D pinWeight left right edgeWeight
    hneD hneEdge hsep hweight hdomination,
    globalMin_allDifferentLoss_iff D pinWeight left right edgeWeight
      hneD hneEdge hsep hweight hdomination⟩

def IsProper
    {p n : ℕ} [Fact p.Prime] {ε : Type*}
    (D : Fin n → Finset ℚ_[p])
    (left right : ε → Fin n) (x : Parameter p n) : Prop :=
  InDomain D x ∧ ∀ e, x (left e) ≠ x (right e)

theorem conflictWeight_nonneg
    {p n : ℕ} [Fact p.Prime] {ε : Type*} [Fintype ε]
    (left right : ε → Fin n) (edgeWeight : ε → ℝ)
    (hweight : ∀ e, 0 ≤ edgeWeight e)
    (x : Parameter p n) :
    0 ≤ conflictWeight left right edgeWeight x := by
  classical
  rw [conflictWeight]
  exact Finset.sum_nonneg fun e _ => by
    split
    · exact hweight e
    · exact le_rfl

theorem conflictWeight_eq_zero_iff
    {p n : ℕ} [Fact p.Prime] {ε : Type*} [Fintype ε]
    (left right : ε → Fin n) (edgeWeight : ε → ℝ)
    (hpositive : ∀ e, 0 < edgeWeight e)
    (x : Parameter p n) :
    conflictWeight left right edgeWeight x = 0 ↔
      ∀ e, x (left e) ≠ x (right e) := by
  classical
  constructor
  · intro hzero e heq
    have hrest :
        0 ≤ ∑ j ∈ Finset.univ \ {e},
          (if x (left j) = x (right j) then edgeWeight j else 0) := by
      exact Finset.sum_nonneg fun j _ => by
        split
        · exact (hpositive j).le
        · exact le_rfl
    rw [conflictWeight,
      Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ e)] at hzero
    simp only [heq, if_pos] at hzero
    linarith [hpositive e]
  · intro hproper
    rw [conflictWeight]
    apply Finset.sum_eq_zero
    intro e _
    simp [hproper e]

theorem globalMin_allDifferentLoss_iff_proper_of_satisfiable
    {p n : ℕ} [Fact p.Prime] {ε : Type*} [Fintype ε]
    (D : Fin n → Finset ℚ_[p]) (pinWeight : ℝ)
    (left right : ε → Fin n) (edgeWeight : ε → ℝ)
    (hneD : ∀ i, (D i).Nonempty)
    (hneEdge : ∀ e, left e ≠ right e)
    (hsep : GloballyUnitSeparated D)
    (hpositive : ∀ e, 0 < edgeWeight e)
    (hdomination : ∀ i,
      incidentEdgeWeight left right edgeWeight i < pinWeight)
    (hsat : ∃ y, IsProper D left right y)
    (x : Parameter p n) :
    IsGlobalMin (allDifferentLoss D pinWeight left right edgeWeight) x ↔
      IsProper D left right x := by
  have hweight : ∀ e, 0 ≤ edgeWeight e := fun e => (hpositive e).le
  rw [globalMin_allDifferentLoss_iff D pinWeight left right edgeWeight
    hneD hneEdge hsep hweight hdomination x]
  constructor
  · rintro ⟨hxD, hxMin⟩
    obtain ⟨y, hyD, hyProper⟩ := hsat
    have hyzero :
        conflictWeight left right edgeWeight y = 0 :=
      (conflictWeight_eq_zero_iff left right edgeWeight hpositive y).mpr hyProper
    have hxle := hxMin y hyD
    have hxnonneg :=
      conflictWeight_nonneg left right edgeWeight hweight x
    have hxzero :
        conflictWeight left right edgeWeight x = 0 := by
      linarith
    exact ⟨hxD,
      (conflictWeight_eq_zero_iff left right edgeWeight hpositive x).mp hxzero⟩
  · rintro ⟨hxD, hxProper⟩
    refine ⟨hxD, ?_⟩
    intro y _
    rw [(conflictWeight_eq_zero_iff left right edgeWeight hpositive x).mpr hxProper]
    exact conflictWeight_nonneg left right edgeWeight hweight y

end PhdThesisLean.AllDifferent
