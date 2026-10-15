import PhdThesisLean.MaxObjective

/-!
# The Smith-normal-form formula for the max objective

Thesis Theorem `thm:max-polytime` (`complexity-regimes/body.tex`) computes
`ρ_max(X, y) = min_β max_i |y_i - x_iᵀβ|_p` by clearing denominators (`A = DX`, `b = Dy`)
and reading the answer off a Smith normal form `UAV = S` with `U ∈ GL_m(ℤ)`,
`V ∈ GL_n(ℤ)`: with `b' = Ub`, the optimum is `max_{i > t} |b'_i|_p` over the zero rows of
`S`, attained at `β = Vγ` with `γ_i = b'_i / s_i`.

This module proves that step for any decomposition the algorithm may return.

* `supResidual_smith`: for every `β`, the objective equals `‖b' - S (V⁻¹ β)‖`.
* `smith_isGlobalMin` and `rhoMax_smith`: the explicit `β* = V γ*` is a global minimiser
  and `ρ_max = ‖maskZero b'‖`, the sup norm of `b'` restricted to the zero rows of `S`
  (`0` when there are none). `smith_optimizer_rational` records that `β*` is the image of
  a rational vector.
* `rhoMax_rational_smith`: the thesis's full formula
  `ρ_max(X, y) = |D|_p⁻¹ max_{i > t} |b'_i|_p` for rational data.

The Smith decomposition is a hypothesis: the decomposition itself and the polynomial
running time of computing it (Kannan–Bachem) remain external.
-/

namespace PhdThesisLean.MaxObjectiveSmith

open Matrix PhdThesisLean.MaxObjective

variable {p : ℕ} [Fact p.Prime] {m n : ℕ}

/-- Cast an integer matrix to `ℚ_[p]`. -/
noncomputable abbrev castM {a b : Type*} (M : Matrix a b ℤ) : Matrix a b ℚ_[p] :=
  M.map (Int.cast : ℤ → ℚ_[p])

/-- Cast an integer vector to `ℚ_[p]`. -/
noncomputable abbrev castV {a : Type*} (v : a → ℤ) : a → ℚ_[p] := fun i => (v i : ℚ_[p])

/-- The zero rows of `S`. -/
def zeroRow (S : Matrix (Fin m) (Fin n) ℤ) (i : Fin m) : Prop := ∀ j, S i j = 0

/-- The vector `b'` restricted to the zero rows of `S`. -/
noncomputable def maskZero (S : Matrix (Fin m) (Fin n) ℤ) (b' : Fin m → ℤ) : Fin m → ℚ_[p] :=
  fun i => by classical exact if zeroRow S i then (b' i : ℚ_[p]) else 0

/-- The optimal `γ`: `γ_j = b'_j / s_j` on the nonzero diagonal of `S`, `0` elsewhere. -/
noncomputable def gammaStar (S : Matrix (Fin m) (Fin n) ℤ) (b' : Fin m → ℤ) : Fin n → ℚ :=
  fun j => if h : (j : ℕ) < m then
    (if S ⟨j, h⟩ j = 0 then 0 else (b' ⟨j, h⟩ : ℚ) / S ⟨j, h⟩ j) else 0

theorem castM_mul {a b c : Type*} [Fintype b] (M : Matrix a b ℤ) (N : Matrix b c ℤ) :
    (castM (p := p) (M * N)) = castM M * castM N :=
  Matrix.map_mul (f := Int.castRingHom ℚ_[p])

theorem castM_one {a : Type*} [Fintype a] [DecidableEq a] :
    castM (p := p) (1 : Matrix a a ℤ) = 1 :=
  Matrix.map_one _ Int.cast_zero Int.cast_one

/-- The objective in Smith coordinates: `‖b - Aβ‖ = ‖b' - S (V⁻¹ β)‖`. -/
theorem supResidual_smith (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (U U' : Matrix (Fin m) (Fin m) ℤ) (V V' : Matrix (Fin n) (Fin n) ℤ) (hU : U' * U = 1)
    (hV : V * V' = 1) (β : Fin n → ℚ_[p]) :
    supResidual (castM A) (castV b) β =
      ‖castV (U *ᵥ b) - castM (U * A * V) *ᵥ (castM V' *ᵥ β)‖ := by
  unfold supResidual
  rw [← norm_mulVec_unimodular U U' hU]
  congr 1
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← castM_mul (U * A * V) V',
    Matrix.mul_assoc (U * A) V V', hV, Matrix.mul_one, castM_mul U A]
  congr 1
  funext i
  simp [castV, Matrix.mulVec, dotProduct]

open Classical in
theorem smith_row (S : Matrix (Fin m) (Fin n) ℤ)
    (hS : ∀ (i : Fin m) (j : Fin n), (i : ℕ) ≠ j → S i j = 0)
    (b' : Fin m → ℤ) (i : Fin m) :
    (castM (p := p) S *ᵥ (fun j => ((gammaStar S b' j : ℚ) : ℚ_[p]))) i =
      if zeroRow S i then 0 else (b' i : ℚ_[p]) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  by_cases hz : zeroRow S i
  · rw [if_pos hz]
    apply Finset.sum_eq_zero
    intro j _
    rw [hz j]; simp
  · rw [if_neg hz]
    obtain ⟨j₀, hj₀⟩ : ∃ j, S i j ≠ 0 := by
      by_contra h; push_neg at h; exact hz h
    have hij : (i : ℕ) = j₀ := by
      by_contra h; exact hj₀ (hS i j₀ h)
    rw [Finset.sum_eq_single j₀]
    · have hlt : (j₀ : ℕ) < m := hij ▸ i.2
      have hi : (⟨j₀, hlt⟩ : Fin m) = i := Fin.ext hij.symm
      simp only [gammaStar, dif_pos hlt, hi, if_neg hj₀]
      have hs : ((S i j₀ : ℤ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hj₀
      push_cast
      rw [mul_div_cancel₀ _ hs]
    · intro j _ hj
      rw [hS i j (fun h => hj (Fin.ext (h.symm.trans hij)))]
      simp
    · simp

/-- **The Smith optimiser.** With `b' = Ub`, the point `β* = V γ*` is a global minimiser of
the max objective, and the optimal residual vector is `b'` restricted to the zero rows of
`S = UAV`. -/
theorem smith_isGlobalMin (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (U U' : Matrix (Fin m) (Fin m) ℤ) (V V' : Matrix (Fin n) (Fin n) ℤ) (hU : U' * U = 1)
    (hV : V * V' = 1) (hS : ∀ (i : Fin m) (j : Fin n), (i : ℕ) ≠ j → (U * A * V) i j = 0) :
    IsGlobalMin (supResidual (castM A) (castV b))
        (castM V *ᵥ fun j => ((gammaStar (U * A * V) (U *ᵥ b) j : ℚ) : ℚ_[p])) ∧
      supResidual (castM A) (castV b)
        (castM V *ᵥ fun j => ((gammaStar (U * A * V) (U *ᵥ b) j : ℚ) : ℚ_[p])) =
        ‖maskZero (p := p) (U * A * V) (U *ᵥ b)‖ := by
  classical
  set S := U * A * V
  have hV' : V' * V = 1 := mul_eq_one_comm.mp hV
  have hval : supResidual (castM A) (castV b)
      (castM V *ᵥ fun j => ((gammaStar S (U *ᵥ b) j : ℚ) : ℚ_[p])) =
      ‖maskZero (p := p) S (U *ᵥ b)‖ := by
    have hVV : castM (p := p) V' *ᵥ (castM V *ᵥ fun j => ((gammaStar S (U *ᵥ b) j : ℚ) : ℚ_[p])) =
        fun j => ((gammaStar S (U *ᵥ b) j : ℚ) : ℚ_[p]) := by
      rw [Matrix.mulVec_mulVec, ← castM_mul, hV', castM_one, Matrix.one_mulVec]
    rw [supResidual_smith A b U U' V V' hU hV, hVV]
    congr 1
    funext i
    rw [Pi.sub_apply, smith_row S hS]
    unfold maskZero
    split_ifs <;> simp [castV]
  refine ⟨?_, hval⟩
  intro β
  rw [hval, supResidual_smith A b U U' V V' hU hV]
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  unfold maskZero
  split_ifs with hz
  · have : (castM (p := p) S *ᵥ (castM (p := p) V' *ᵥ β)) i = 0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
      apply Finset.sum_eq_zero
      intro j _
      rw [hz j]; simp
    calc ‖((U *ᵥ b) i : ℚ_[p])‖ =
        ‖(castV (p := p) (U *ᵥ b) - castM (p := p) S *ᵥ (castM (p := p) V' *ᵥ β)) i‖ := by
          rw [Pi.sub_apply, this, sub_zero]
      _ ≤ _ := norm_le_pi_norm _ i
  · simp

/-- **Thesis `thm:max-polytime`, the formula step.** For a Smith decomposition `UAV = S`,
`ρ_max(A, b) = max_{i > t} |(Ub)_i|_p`, the sup norm of `Ub` over the zero rows of `S`. -/
theorem rhoMax_smith (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (U U' : Matrix (Fin m) (Fin m) ℤ) (V V' : Matrix (Fin n) (Fin n) ℤ) (hU : U' * U = 1)
    (hV : V * V' = 1) (hS : ∀ (i : Fin m) (j : Fin n), (i : ℕ) ≠ j → (U * A * V) i j = 0) :
    rhoMax (castM (p := p) A) (castV b) = ‖maskZero (p := p) (U * A * V) (U *ᵥ b)‖ := by
  obtain ⟨hmin, hval⟩ := smith_isGlobalMin (p := p) A b U U' V V' hU hV hS
  rw [rhoMax_eq_of_isGlobalMin hmin, hval]

/-- The Smith optimiser is the image of a rational vector: `β* = V γ*` with
`γ* ∈ ℚ^n`. -/
theorem smith_optimizer_rational (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (U : Matrix (Fin m) (Fin m) ℤ) (V : Matrix (Fin n) (Fin n) ℤ) :
    (castM (p := p) V *ᵥ fun j => ((gammaStar (U * A * V) (U *ᵥ b) j : ℚ) : ℚ_[p])) =
      fun i =>
        ((((V.map (Int.cast : ℤ → ℚ)) *ᵥ gammaStar (U * A * V) (U *ᵥ b)) i : ℚ) : ℚ_[p]) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply]

/-- **Thesis `thm:max-polytime`, the full formula for rational data.** If `A = DX` and
`b = Dy` are integral with `D ≠ 0`, and `UAV = S` is a Smith decomposition, then
`ρ_max(X, y) = |D|_p⁻¹ max_{i > t} |(Ub)_i|_p`. -/
theorem rhoMax_rational_smith (X : Matrix (Fin m) (Fin n) ℚ) (y : Fin m → ℚ) (D : ℤ)
    (hD : D ≠ 0) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, (A i j : ℚ) = D * X i j) (hb : ∀ i, (b i : ℚ) = D * y i)
    (U U' : Matrix (Fin m) (Fin m) ℤ) (V V' : Matrix (Fin n) (Fin n) ℤ) (hU : U' * U = 1)
    (hV : V * V' = 1) (hS : ∀ (i : Fin m) (j : Fin n), (i : ℕ) ≠ j → (U * A * V) i j = 0) :
    rhoMax (X.map (Rat.cast : ℚ → ℚ_[p])) (fun i => (y i : ℚ_[p])) =
      ‖(D : ℚ_[p])‖⁻¹ * ‖maskZero (p := p) (U * A * V) (U *ᵥ b)‖ := by
  have hDp : (D : ℚ_[p]) ≠ 0 := by exact_mod_cast hD
  have hAx : castM (p := p) A = (D : ℚ_[p]) • X.map (Rat.cast : ℚ → ℚ_[p]) := by
    ext i j
    simp only [castM, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    have := congrArg (fun q : ℚ => (q : ℚ_[p])) (hA i j)
    push_cast at this
    exact this
  have hbx : castV (p := p) b = (D : ℚ_[p]) • fun i => (y i : ℚ_[p]) := by
    funext i
    simp only [castV, Pi.smul_apply, smul_eq_mul]
    have := congrArg (fun q : ℚ => (q : ℚ_[p])) (hb i)
    push_cast at this
    exact this
  have hrho := rhoMax_smith (p := p) A b U U' V V' hU hV hS
  rw [hAx, hbx] at hrho
  have hscale : rhoMax ((D : ℚ_[p]) • X.map (Rat.cast : ℚ → ℚ_[p]))
      ((D : ℚ_[p]) • fun i => (y i : ℚ_[p])) =
      ‖(D : ℚ_[p])‖ * rhoMax (X.map (Rat.cast : ℚ → ℚ_[p])) (fun i => (y i : ℚ_[p])) := by
    unfold rhoMax
    simp only [supResidual_smul]
    rw [Real.mul_iInf_of_nonneg (norm_nonneg _)]
  rw [hscale] at hrho
  have hDn : ‖(D : ℚ_[p])‖ ≠ 0 := norm_ne_zero_iff.mpr hDp
  field_simp
  linarith [hrho]

end PhdThesisLean.MaxObjectiveSmith

#print axioms PhdThesisLean.MaxObjectiveSmith.rhoMax_smith
#print axioms PhdThesisLean.MaxObjectiveSmith.rhoMax_rational_smith
