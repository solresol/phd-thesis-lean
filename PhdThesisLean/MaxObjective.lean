import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Tactic

namespace PhdThesisLean.MaxObjective

open scoped BigOperators
open Matrix

/-!
# The `max` objective: attainment, rational optimum, and the algorithm's reductions

This module formalises the mathematical core of thesis Theorem
`thm:max-polytime` (section `sec:max-objective`) from
`complexity-regimes/body.tex`:

> `ρ_max(X, y) = min_{β ∈ ℚ_p^n} max_i |y_i - x_iᵀβ|_p`, with `X ∈ ℚ^{m×n}` and
> `y ∈ ℚ^m`, and an optimal `β` can be computed in polynomial time; moreover an
> optimal `β` may be chosen in `ℚ^n`.

## Setting

The sup norm `‖z‖_{∞,p} = max_i |z_i|_p` on `ι → ℚ_[p]` is Mathlib's `Pi` norm
`‖z‖`; `supResidual_eq_sup'` records that it is literally the finite maximum
of the coordinate norms.  The objective is
`supResidual A b β := ‖b - A *ᵥ β‖` and `rhoMax A b := ⨅ β, supResidual A b β`.

## What is formalised

* `exists_isGlobalMin_supResidual` / `max_objective_attained`: for any
  `A : Matrix ι κ ℚ_[p]` and `b : ι → ℚ_[p]` the infimum defining `ρ_max` is
  attained, so the thesis's `min` is justified (`rhoMax_attained`).  This is
  stronger than the thesis statement, which only needs rational data.
* `exists_rat_isGlobalMin` / `max_objective_rational_optimum`: for rational
  data `A : Matrix ι κ ℚ`, `b : ι → ℚ` there is an optimal `β ∈ ℚ^κ`, i.e. the
  "moreover" clause of the theorem, and `max_objective_rational_optimum_rhoMax`
  says this rational `β` realises `ρ_max`.
* `exists_rat_solution_of_padic_solution`: a rational linear system solvable
  over `ℚ_[p]` is solvable over `ℚ` (the `ρ_max = 0` case).
* The reductions the thesis's algorithm relies on:
  `norm_mulVec_intMatrix_le` (an integer matrix does not increase the sup
  norm), `norm_mulVec_unimodular` / `norm_mulVec_generalLinearGroup`
  (invariance of the sup norm under `GL_m(ℤ)`), and
  `supResidual_clear_denominators` / `isGlobalMin_clear_denominators_iff`
  (clearing denominators with an integer `D ≠ 0` scales the objective by
  `|D|_p` and preserves the minimisers).
* `sum_objective_not_unimodular_invariant`: the thesis's closing remark that
  the *summed* objective is not invariant under `GL_m(ℤ)`, witnessed by a
  `2 × 2` example over `ℚ_[2]`.

## Correspondence notes

* Index types: observations and coefficients are indexed by arbitrary finite
  types `ι`, `κ` in the general lemmas; the headline theorems use `Fin m`,
  `Fin n` as in the thesis.
* Everything is stated with the `p`-adic absolute value realised as Mathlib's
  norm on `ℚ_[p]`; rational data are cast into `ℚ_[p]` explicitly
  (`A.map (Rat.cast)` and `fun i => (b i : ℚ_[p])`).
* **External / not formalised.**  The polynomial-time computability claim
  (Mathlib has no complexity framework) and the Smith-normal-form algorithm
  (`U A V = S`, Kannan–Bachem) are external.  The closed formula
  `ρ_max(A, b) = max_{t < i ≤ m} |b'_i|_p` for `b' = U b` is *not* formalised;
  what is formalised is the mathematical content the algorithm relies on
  (invariance of the objective under the row/column operations, the
  denominator-clearing step, existence of a minimiser and of a rational one).
* **Proof route.**  Attainment uses properness of `ℚ_[p]`
  (`Padic.instProperSpace`), closedness of the finite-dimensional range of
  `β ↦ Aβ` (`Submodule.closed_of_finiteDimensional`) and
  `IsClosed.exists_infDist_eq_dist`.  The rational optimum uses density of
  `ℚ^κ` in `ℚ_[p]^κ` (`Padic.denseRange_ratCast`, `DenseRange.piMap`) together
  with the ultrametric inequality in the sup norm (`Pi.instIsUltrametricDist`):
  any rational `β` with `‖A(β - β₀)‖ < ρ_max` is optimal.  When `ρ_max = 0`
  the system `Aβ = b` has a `p`-adic solution and the base-change lemma
  (proved with a rational dual functional,
  `Subspace.dualAnnihilator_dualCoannihilator_eq`) gives a rational one.
  The thesis instead reads the optimum off the Smith normal form; the
  conclusions are identical.
-/

variable {p : ℕ} [Fact p.Prime]

/-- `x` is a global minimiser of `f` (same shape as `PhdThesisLean.AllDifferent.IsGlobalMin`). -/
def IsGlobalMin {α : Type*} (f : α → ℝ) (x : α) : Prop := ∀ y, f x ≤ f y

section General

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The `max` objective `max_i |b_i - (Aβ)_i|_p`, written with the sup norm on `ι → ℚ_[p]`. -/
noncomputable def supResidual (A : Matrix ι κ ℚ_[p]) (b : ι → ℚ_[p]) (β : κ → ℚ_[p]) : ℝ :=
  ‖b - A *ᵥ β‖

/-- `ρ_max(A, b) = inf_β max_i |b_i - (Aβ)_i|_p`; `rhoMax_attained` shows it is a minimum. -/
noncomputable def rhoMax (A : Matrix ι κ ℚ_[p]) (b : ι → ℚ_[p]) : ℝ :=
  ⨅ β, supResidual A b β

/-- The sup norm is the maximum of the coordinate `p`-adic absolute values. -/
theorem supResidual_eq_sup' [Nonempty ι] (A : Matrix ι κ ℚ_[p]) (b : ι → ℚ_[p])
    (β : κ → ℚ_[p]) :
    supResidual A b β =
      Finset.univ.sup' Finset.univ_nonempty (fun i => ‖b i - (A *ᵥ β) i‖) := by
  unfold supResidual
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonempty]
    intro i
    simpa using Finset.le_sup' (fun i => ‖b i - (A *ᵥ β) i‖) (Finset.mem_univ i)
  · apply Finset.sup'_le
    intro i _
    simpa using norm_le_pi_norm (b - A *ᵥ β) i

/-! ### Attainment of the minimum -/

/-- The `max` objective attains its infimum: there is a `β₀ ∈ ℚ_p^κ` with
`‖b - Aβ₀‖ ≤ ‖b - Aβ‖` for every `β`.  (Properness of `ℚ_[p]` plus closedness of the
finite-dimensional range of `β ↦ Aβ`.) -/
theorem exists_isGlobalMin_supResidual (A : Matrix ι κ ℚ_[p]) (b : ι → ℚ_[p]) :
    ∃ β₀ : κ → ℚ_[p], IsGlobalMin (supResidual A b) β₀ := by
  classical
  let W : Submodule ℚ_[p] (ι → ℚ_[p]) := LinearMap.range (Matrix.mulVecLin A)
  have hW : IsClosed (W : Set (ι → ℚ_[p])) := W.closed_of_finiteDimensional
  have hne : (W : Set (ι → ℚ_[p])).Nonempty := ⟨0, W.zero_mem⟩
  obtain ⟨w, hwW, hw⟩ := hW.exists_infDist_eq_dist hne b
  obtain ⟨β₀, rfl⟩ := LinearMap.mem_range.mp hwW
  refine ⟨β₀, fun β => ?_⟩
  have hβ : (Matrix.mulVecLin A β) ∈ (W : Set (ι → ℚ_[p])) :=
    LinearMap.mem_range_self (Matrix.mulVecLin A) β
  have hle := Metric.infDist_le_dist_of_mem (x := b) hβ
  rw [hw] at hle
  simpa [supResidual, dist_eq_norm] using hle

theorem rhoMax_eq_of_isGlobalMin {A : Matrix ι κ ℚ_[p]} {b : ι → ℚ_[p]} {β₀ : κ → ℚ_[p]}
    (h : IsGlobalMin (supResidual A b) β₀) : rhoMax A b = supResidual A b β₀ := by
  unfold rhoMax iInf
  exact IsLeast.csInf_eq ⟨⟨β₀, rfl⟩, fun _ ⟨β, hβ⟩ => hβ ▸ h β⟩

/-- `ρ_max` is a minimum, not merely an infimum. -/
theorem rhoMax_attained (A : Matrix ι κ ℚ_[p]) (b : ι → ℚ_[p]) :
    ∃ β₀ : κ → ℚ_[p], supResidual A b β₀ = rhoMax A b ∧
      ∀ β : κ → ℚ_[p], rhoMax A b ≤ supResidual A b β := by
  obtain ⟨β₀, h⟩ := exists_isGlobalMin_supResidual A b
  refine ⟨β₀, (rhoMax_eq_of_isGlobalMin h).symm, fun β => ?_⟩
  rw [rhoMax_eq_of_isGlobalMin h]
  exact h β

/-! ### Base change: rational solvability of rational systems -/

/-- A rational linear system `Aβ = b` that is solvable over `ℚ_[p]` is solvable over `ℚ`.
Proof: if `b` were outside the `ℚ`-column span `W` of `A`, a rational functional `c`
vanishing on `W` with `c ⬝ᵥ b ≠ 0` would, after casting, vanish on `Aγ` for every
`γ ∈ ℚ_p^κ` but not on `b`. -/
theorem exists_rat_solution_of_padic_solution (A : Matrix ι κ ℚ) (b : ι → ℚ)
    (γ : κ → ℚ_[p]) (hγ : A.map (Rat.cast : ℚ → ℚ_[p]) *ᵥ γ = fun i => (b i : ℚ_[p])) :
    ∃ β : κ → ℚ, A *ᵥ β = b := by
  classical
  by_contra hcon
  push_neg at hcon
  let W : Submodule ℚ (ι → ℚ) := LinearMap.range (Matrix.mulVecLin A)
  have hbW : b ∉ W := by
    intro hb
    obtain ⟨β, hβ⟩ := LinearMap.mem_range.mp hb
    exact hcon β (by simpa using hβ)
  have hb' : b ∉ W.dualAnnihilator.dualCoannihilator := by
    rwa [Subspace.dualAnnihilator_dualCoannihilator_eq]
  rw [Submodule.mem_dualCoannihilator] at hb'
  push_neg at hb'
  obtain ⟨φ, hφW, hφb⟩ := hb'
  rw [Submodule.mem_dualAnnihilator] at hφW
  -- the coefficient vector of `φ`
  let c : ι → ℚ := fun i => φ (fun j => if i = j then 1 else 0)
  have hφ_eq : ∀ v : ι → ℚ, φ v = v ⬝ᵥ c := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp [dotProduct, c, smul_eq_mul]
  have hcA : c ᵥ* A = 0 := by
    funext j
    have h1 : φ (A *ᵥ Pi.single j 1) = 0 :=
      hφW _ (LinearMap.mem_range_self (Matrix.mulVecLin A) (Pi.single j 1))
    rw [hφ_eq, dotProduct_comm, dotProduct_mulVec, dotProduct_single, mul_one] at h1
    simpa using h1
  -- cast everything to `ℚ_[p]`
  let f : ℚ →+* ℚ_[p] := Rat.castHom ℚ_[p]
  have hcA' : (f ∘ c) ᵥ* A.map f = 0 := by
    funext j
    rw [← RingHom.map_vecMul, hcA]
    simp
  have h0 : (f ∘ c) ⬝ᵥ (A.map f *ᵥ γ) = 0 := by
    rw [dotProduct_mulVec, hcA', zero_dotProduct]
  have hmap : A.map f = A.map (Rat.cast : ℚ → ℚ_[p]) := rfl
  rw [hmap, hγ] at h0
  have h1 : (f ∘ c) ⬝ᵥ (fun i => (b i : ℚ_[p])) = f (c ⬝ᵥ b) := by
    rw [RingHom.map_dotProduct]
    rfl
  rw [h1] at h0
  have hcb : c ⬝ᵥ b = 0 := f.injective (by simpa using h0)
  apply hφb
  rw [hφ_eq, dotProduct_comm]
  exact hcb

/-! ### A rational optimum -/

/-- For rational data an optimal coefficient vector may be chosen in `ℚ^κ`: the
"moreover" clause of `thm:max-polytime`. -/
theorem exists_rat_isGlobalMin (A : Matrix ι κ ℚ) (b : ι → ℚ) :
    ∃ β : κ → ℚ,
      IsGlobalMin (supResidual (A.map (Rat.cast : ℚ → ℚ_[p])) (fun i => (b i : ℚ_[p])))
        (fun j => (β j : ℚ_[p])) := by
  classical
  set Ap : Matrix ι κ ℚ_[p] := A.map (Rat.cast : ℚ → ℚ_[p])
  set bp : ι → ℚ_[p] := fun i => (b i : ℚ_[p])
  obtain ⟨β₀, hβ₀⟩ := exists_isGlobalMin_supResidual Ap bp
  rcases eq_or_lt_of_le (norm_nonneg (bp - Ap *ᵥ β₀)) with h0 | hpos
  · -- `ρ_max = 0`: exact fit over `ℚ_[p]`, hence over `ℚ`.
    have hfit : Ap *ᵥ β₀ = bp := by
      have : bp - Ap *ᵥ β₀ = 0 := norm_eq_zero.mp h0.symm
      exact (sub_eq_zero.mp this).symm
    obtain ⟨β, hβ⟩ := exists_rat_solution_of_padic_solution A b β₀ hfit
    refine ⟨β, fun γ => ?_⟩
    have hcast : Ap *ᵥ (fun j => (β j : ℚ_[p])) = bp := by
      funext i
      have h := RingHom.map_mulVec (Rat.castHom ℚ_[p]) A β i
      rw [hβ] at h
      simpa [Function.comp_def, Ap, bp] using h.symm
    have : supResidual Ap bp (fun j => (β j : ℚ_[p])) = 0 := by
      simp [supResidual, hcast]
    rw [this]
    exact norm_nonneg _
  · -- `ρ_max > 0`: a rational `β` with `‖A(β - β₀)‖ < ρ_max` is optimal (ultrametric).
    set ρ : ℝ := ‖bp - Ap *ᵥ β₀‖
    have hcont : Continuous fun β : κ → ℚ_[p] => Ap *ᵥ (β - β₀) := by
      have h : Continuous fun β : κ → ℚ_[p] => Ap *ᵥ β := by
        have := (Matrix.mulVecLin Ap).continuous_of_finiteDimensional
        simpa [Matrix.coe_mulVecLin] using this
      exact h.comp (continuous_id.sub continuous_const)
    have hopen : IsOpen {β : κ → ℚ_[p] | ‖Ap *ᵥ (β - β₀)‖ < ρ} := by
      have hset : {β : κ → ℚ_[p] | ‖Ap *ᵥ (β - β₀)‖ < ρ} =
          (fun β : κ → ℚ_[p] => Ap *ᵥ (β - β₀)) ⁻¹' Metric.ball 0 ρ := by
        ext β
        simp [Metric.mem_ball, dist_zero_right]
      rw [hset]
      exact hcont.isOpen_preimage _ Metric.isOpen_ball
    have hmem : β₀ ∈ {β : κ → ℚ_[p] | ‖Ap *ᵥ (β - β₀)‖ < ρ} := by
      simpa using hpos
    have hdense : DenseRange (fun β : κ → ℚ => fun j => (β j : ℚ_[p])) :=
      DenseRange.piMap (fun _ : κ => Padic.denseRange_ratCast p)
    obtain ⟨β, hβ⟩ := hdense.exists_mem_open hopen ⟨β₀, hmem⟩
    refine ⟨β, fun γ => le_trans ?_ (hβ₀ γ)⟩
    have hdecomp : bp - Ap *ᵥ (fun j => (β j : ℚ_[p])) =
        (bp - Ap *ᵥ β₀) + -(Ap *ᵥ ((fun j => (β j : ℚ_[p])) - β₀)) := by
      rw [Matrix.mulVec_sub]
      abel
    show ‖bp - Ap *ᵥ (fun j => (β j : ℚ_[p]))‖ ≤ ρ
    rw [hdecomp]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le le_rfl ?_)
    rw [norm_neg]
    exact le_of_lt hβ

/-! ### Reductions used by the thesis's algorithm -/

/-- An integer matrix does not increase the `p`-adic sup norm (ultrametric inequality plus
`|k|_p ≤ 1` for integers `k`). -/
theorem norm_mulVec_intMatrix_le (U : Matrix ι κ ℤ) (z : κ → ℚ_[p]) :
    ‖U.map (Int.cast : ℤ → ℚ_[p]) *ᵥ z‖ ≤ ‖z‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg z)]
  intro i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg z)
  intro j _
  rw [norm_mul]
  calc ‖((U i j : ℤ) : ℚ_[p])‖ * ‖z j‖ ≤ 1 * ‖z‖ :=
        mul_le_mul (Padic.norm_int_le_one _) (norm_le_pi_norm z j) (norm_nonneg _)
          zero_le_one
    _ = ‖z‖ := one_mul _

/-- The sup norm is invariant under integer matrices with an integer left inverse
(`V * U = 1`): the thesis's "`‖Mz‖_{∞,p} = ‖z‖_{∞,p}` for `M ∈ GL_m(ℤ)`". -/
theorem norm_mulVec_unimodular [DecidableEq ι] (U V : Matrix ι ι ℤ) (hVU : V * U = 1)
    (z : ι → ℚ_[p]) :
    ‖U.map (Int.cast : ℤ → ℚ_[p]) *ᵥ z‖ = ‖z‖ := by
  apply le_antisymm (norm_mulVec_intMatrix_le U z)
  have hmul : (V * U).map (Int.cast : ℤ → ℚ_[p]) =
      V.map (Int.cast : ℤ → ℚ_[p]) * U.map (Int.cast : ℤ → ℚ_[p]) :=
    Matrix.map_mul (f := Int.castRingHom ℚ_[p])
  have hz : z = V.map (Int.cast : ℤ → ℚ_[p]) *ᵥ (U.map (Int.cast : ℤ → ℚ_[p]) *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← hmul, hVU, Matrix.map_one _ Int.cast_zero Int.cast_one,
      Matrix.one_mulVec]
  calc ‖z‖ = ‖V.map (Int.cast : ℤ → ℚ_[p]) *ᵥ (U.map (Int.cast : ℤ → ℚ_[p]) *ᵥ z)‖ := by
        rw [← hz]
    _ ≤ ‖U.map (Int.cast : ℤ → ℚ_[p]) *ᵥ z‖ := norm_mulVec_intMatrix_le _ _

/-- Sup-norm invariance for `U ∈ GL_m(ℤ)`. -/
theorem norm_mulVec_generalLinearGroup [DecidableEq ι] (U : Matrix.GeneralLinearGroup ι ℤ)
    (z : ι → ℚ_[p]) :
    ‖(U : Matrix ι ι ℤ).map (Int.cast : ℤ → ℚ_[p]) *ᵥ z‖ = ‖z‖ :=
  norm_mulVec_unimodular (U : Matrix ι ι ℤ) ((U⁻¹ : Matrix.GeneralLinearGroup ι ℤ) : Matrix ι ι ℤ)
    (Units.inv_mul U) z

/-- Scaling data by `D` scales the objective by `|D|_p`. -/
theorem supResidual_smul (X : Matrix ι κ ℚ_[p]) (y : ι → ℚ_[p]) (D : ℚ_[p]) (β : κ → ℚ_[p]) :
    supResidual (D • X) (D • y) β = ‖D‖ * supResidual X y β := by
  unfold supResidual
  rw [Matrix.smul_mulVec, ← smul_sub, norm_smul]

/-- Denominator clearing (`A = D X`, `b = D y` with `D ∈ ℤ \ {0}`):
`max_i |y_i - x_iᵀβ|_p = |D|_p⁻¹ max_i |b_i - (Aβ)_i|_p`. -/
theorem supResidual_clear_denominators (X : Matrix ι κ ℚ) (y : ι → ℚ) (D : ℤ) (hD : D ≠ 0)
    (β : κ → ℚ_[p]) :
    supResidual (X.map (Rat.cast : ℚ → ℚ_[p])) (fun i => (y i : ℚ_[p])) β =
      ‖(D : ℚ_[p])‖⁻¹ *
        supResidual (((D : ℚ) • X).map (Rat.cast : ℚ → ℚ_[p]))
          (fun i => (((D : ℚ) • y) i : ℚ_[p])) β := by
  have hX : ((D : ℚ) • X).map (Rat.cast : ℚ → ℚ_[p]) =
      (D : ℚ_[p]) • X.map (Rat.cast : ℚ → ℚ_[p]) := by
    ext i j
    simp
  have hy : (fun i => (((D : ℚ) • y) i : ℚ_[p])) = (D : ℚ_[p]) • fun i => (y i : ℚ_[p]) := by
    funext i
    simp
  rw [hX, hy, supResidual_smul]
  have hDne : ‖(D : ℚ_[p])‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact_mod_cast hD
  field_simp

/-- Denominator clearing preserves the set of minimisers. -/
theorem isGlobalMin_clear_denominators_iff (X : Matrix ι κ ℚ_[p]) (y : ι → ℚ_[p]) {D : ℚ_[p]}
    (hD : D ≠ 0) (β : κ → ℚ_[p]) :
    IsGlobalMin (supResidual (D • X) (D • y)) β ↔ IsGlobalMin (supResidual X y) β := by
  have hpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  constructor
  · intro h γ
    have := h γ
    rw [supResidual_smul, supResidual_smul] at this
    exact le_of_mul_le_mul_left this hpos
  · intro h γ
    rw [supResidual_smul, supResidual_smul]
    exact mul_le_mul_of_nonneg_left (h γ) hpos.le

/-- The summed objective is *not* invariant under `GL_m(ℤ)` (thesis remark after the proof):
with `U = [[1, 1], [0, 1]]` and `r = (1, 1)` over `ℚ_[2]`, `∑_i |(Ur)_i|_2 = 3/2 ≠ 2 = ∑_i |r_i|_2`,
whereas `‖Ur‖ = ‖r‖ = 1` by `norm_mulVec_unimodular`. -/
theorem sum_objective_not_unimodular_invariant :
    let U : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, 1], ![0, 1]]
    let r : Fin 2 → ℚ_[2] := ![1, 1]
    ∑ i, ‖(U.map (Int.cast : ℤ → ℚ_[2]) *ᵥ r) i‖ ≠ ∑ i, ‖r i‖ := by
  intro U r
  have h2 : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by
    have := Padic.norm_p (p := 2)
    simpa using this
  have hU : (U.map (Int.cast : ℤ → ℚ_[2]) *ᵥ r) = ![2, 1] := by
    funext i
    fin_cases i <;> norm_num [U, r, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hU]
  simp [Fin.sum_univ_two, r, h2]

end General

/-! ### Headline statements (`Fin m` observations, `Fin n` coefficients, as in the thesis) -/

/-- **Attainment** (`thm:max-polytime`, the `min` in the definition of `ρ_max`): for any
`A ∈ ℚ_p^{m×n}`, `b ∈ ℚ_p^m` there is `β₀ ∈ ℚ_p^n` with
`max_i |b_i - (Aβ₀)_i|_p ≤ max_i |b_i - (Aβ)_i|_p` for all `β ∈ ℚ_p^n`. -/
theorem max_objective_attained {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ_[p])
    (b : Fin m → ℚ_[p]) :
    ∃ β₀ : Fin n → ℚ_[p], ∀ β : Fin n → ℚ_[p], ‖b - A *ᵥ β₀‖ ≤ ‖b - A *ᵥ β‖ :=
  exists_isGlobalMin_supResidual A b

/-- **Rational optimum** (`thm:max-polytime`, "an optimal `β` may be chosen in `ℚ^n`"): for
`A ∈ ℚ^{m×n}`, `b ∈ ℚ^m` there is `β ∈ ℚ^n` with
`max_i |b_i - (Aβ)_i|_p ≤ max_i |b_i - (Aγ)_i|_p` for every `γ ∈ ℚ_p^n`. -/
theorem max_objective_rational_optimum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    ∃ β : Fin n → ℚ, ∀ γ : Fin n → ℚ_[p],
      ‖(fun i => (b i : ℚ_[p])) - A.map (Rat.cast : ℚ → ℚ_[p]) *ᵥ (fun j => (β j : ℚ_[p]))‖ ≤
        ‖(fun i => (b i : ℚ_[p])) - A.map (Rat.cast : ℚ → ℚ_[p]) *ᵥ γ‖ :=
  exists_rat_isGlobalMin A b

/-- The rational optimum realises `ρ_max`. -/
theorem max_objective_rational_optimum_rhoMax {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    ∃ β : Fin n → ℚ,
      ‖(fun i => (b i : ℚ_[p])) - A.map (Rat.cast : ℚ → ℚ_[p]) *ᵥ (fun j => (β j : ℚ_[p]))‖ =
        rhoMax (A.map (Rat.cast : ℚ → ℚ_[p])) (fun i => (b i : ℚ_[p])) := by
  obtain ⟨β, hβ⟩ := exists_rat_isGlobalMin (p := p) A b
  exact ⟨β, (rhoMax_eq_of_isGlobalMin hβ).symm⟩

end PhdThesisLean.MaxObjective

#print axioms PhdThesisLean.MaxObjective.max_objective_attained
#print axioms PhdThesisLean.MaxObjective.max_objective_rational_optimum
#print axioms PhdThesisLean.MaxObjective.max_objective_rational_optimum_rhoMax
#print axioms PhdThesisLean.MaxObjective.exists_rat_solution_of_padic_solution
#print axioms PhdThesisLean.MaxObjective.norm_mulVec_generalLinearGroup
#print axioms PhdThesisLean.MaxObjective.supResidual_clear_denominators
#print axioms PhdThesisLean.MaxObjective.sum_objective_not_unimodular_invariant
#print axioms PhdThesisLean.MaxObjective.rhoMax_attained
#print axioms PhdThesisLean.MaxObjective.isGlobalMin_clear_denominators_iff
