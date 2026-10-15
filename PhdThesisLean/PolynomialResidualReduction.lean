import PhdThesisLean.PolynomialResidualLanguage
import PhdThesisLean.SignedThreeSatReduction

/-!
# A multilinear polynomial-residual reduction from exact 3-SAT

This module gives the semantic half of the NP-hardness transfer for thesis Corollary
`cor:sudoku-polynomial-dyadic-hardness` (`sudoku-via-padic-regression/body.tex`):
global minimisation of positive polynomial-residual objectives over `ℤ_2^n` is NP-hard,
already when every non-unary residual is multilinear of degree at most three.

## The construction

The thesis's clause residual is the product `∏ δ(λ; x)` of the literal-failure values
of the clause, where `x_v = 0` encodes true. Clauses of the library's exact 3-SAT may
repeat a variable, which would make that product non-multilinear, so each literal
occurrence `k` gets its own coordinate `y_k` (literal index `2k + 1`) carrying the
failure value of the literal, and each source variable `v` keeps a coordinate `x_v`
(literal index `2v + 2`). The residuals are:

* for each occurrence `k` of a literal `l` on `v`: two Boolean forcing pairs on `y_k`
  and the affine linking residual `y_k - δ(l; x)` (`litBlock`);
* for each clause starting at occurrence `k`: the product `y_k y_{k+1} y_{k+2}`
  (`product`), whose three factors involve distinct coordinates;
* one Boolean forcing pair on `x_v` per occurrence of `v` (`xForcing`);
* harmless zero residuals (`dummy`) that the streaming machine needs.

Every residual is multilinear of degree at most three (`multilinear_polyReduce`). The
bound is `9m` for `m` clauses.

## Correctness

Snapping all coordinates with `snapZ` does not increase the contribution of a clause
(`clauseValue_snap_le`): the forcing pairs dominate the linking residuals and the
`1`-Lipschitz product on `ℤ_p`. At a Boolean point a width-three clause contributes at
least `9` plus its falsity indicator under the assignment read from the `x`
coordinates (`clauseValue_bool_ge`), with equality `9` at the consistent point of a
satisfying assignment (`clauseValue_point`). Hence `poly_iff`: for every prime `p` and
every formula of exact width three, the formula is satisfiable iff the instance
`polyReduce F` is accepted by `PolyRegressionLangML p`.

The chosen weights differ from the thesis's `α = 1 + Δ`: one forcing pair per literal
occurrence (two on the occurrence coordinate), which is what a streaming machine can
emit. At the exact threshold, linking mismatches and false clauses must both vanish, so
unit linking weights suffice.
-/

namespace PhdThesisLean.PolynomialResidualReduction

open LeanNPHardness LeanNPHardness.CNF
open PhdThesisLean.PadicRegressionLanguage PhdThesisLean.PolynomialResidualLanguage
open PhdThesisLean.SignedThreeSatReduction (litVar)

/-! ### The construction -/

/-- The literal index of the occurrence coordinate `y_k`. -/
def yIdx (k : ℕ) : ℕ := 2 * k + 1

/-- The literal index of the variable coordinate `x_v`. -/
def xIdx (v : ℕ) : ℕ := 2 * v + 2

/-- A Boolean forcing pair on literal index `i`. -/
def forcingRes (i : ℕ) : List PolyResidual :=
  [([.positive i], []), ([.positive i, .positive 0], [])]

/-- The linking residual `y_k - δ(l; x)` of occurrence `k` of literal `l`. -/
def linking (k : ℕ) : Literal ℕ → PolyResidual
  | .positive v => ([.positive (yIdx k), .negative (xIdx v)], [])
  | .negative v => ([.positive (yIdx k), .positive 0, .positive (xIdx v)], [])

/-- The residuals of one literal occurrence. -/
def litBlock (k : ℕ) (l : Literal ℕ) : List PolyResidual :=
  forcingRes (yIdx k) ++ forcingRes (yIdx k) ++ [linking k l]

/-- The clause product `y_k y_{k+1} y_{k+2}`. -/
def product (k : ℕ) : PolyResidual :=
  ([.positive (yIdx k)], [[.positive (yIdx (k + 1))], [.positive (yIdx (k + 2))]])

/-- The zero residual: its only factor is the empty affine form. -/
def dummy : PolyResidual := ([], [])

/-- The occurrence residuals of a clause from occurrence `k`. -/
def litsBlock : ℕ → Clause ℕ → List PolyResidual
  | _, [] => []
  | k, l :: ls => litBlock k l ++ litsBlock (k + 1) ls

/-- The residuals of a clause starting at occurrence `k`. -/
def clauseBlock (k : ℕ) (c : Clause ℕ) : List PolyResidual := litsBlock k c ++ [product k, dummy]

/-- The clause residuals of a formula from occurrence `k`. -/
def formulaBlocks : ℕ → Formula ℕ → List PolyResidual
  | _, [] => []
  | k, c :: F => clauseBlock k c ++ formulaBlocks (k + c.length) F

/-- One forcing pair on `x_v` per occurrence of `v`, in reverse order of occurrence. -/
def xForcing (F : Formula ℕ) : List PolyResidual :=
  F.reverse.flatMap fun c => c.reverse.flatMap fun l => forcingRes (xIdx (litVar l))

/-- The reduction from CNF formulas to polynomial-residual instances. -/
def polyReduce (F : Formula ℕ) : List PolyResidual × ℕ :=
  (dummy :: formulaBlocks 0 F ++ xForcing F, 9 * F.length)

/-! ### Multilinearity -/

theorem multilinear_forcingRes (i : ℕ) : ∀ r ∈ forcingRes i, MultilinearDeg3 r := by
  intro r hr
  simp [forcingRes] at hr
  rcases hr with rfl | rfl <;> simp [MultilinearDeg3]

theorem multilinear_litBlock (k : ℕ) (l : Literal ℕ) : ∀ r ∈ litBlock k l, MultilinearDeg3 r := by
  intro r hr
  simp only [litBlock, List.mem_append, List.mem_singleton] at hr
  rcases hr with (h | h) | rfl
  · exact multilinear_forcingRes _ r h
  · exact multilinear_forcingRes _ r h
  · cases l <;> simp [MultilinearDeg3, linking]

theorem multilinear_litsBlock (c : Clause ℕ) : ∀ k, ∀ r ∈ litsBlock k c, MultilinearDeg3 r := by
  induction c with
  | nil => intro k r hr; simp [litsBlock] at hr
  | cons l c ih =>
      intro k r hr
      simp only [litsBlock, List.mem_append] at hr
      rcases hr with h | h
      · exact multilinear_litBlock k l r h
      · exact ih (k + 1) r h

theorem multilinear_product (k : ℕ) : MultilinearDeg3 (product k) := by
  refine ⟨by simp [product], ?_⟩
  simp [product, factorVars, yIdx]

theorem multilinear_formulaBlocks (F : Formula ℕ) :
    ∀ k, ∀ r ∈ formulaBlocks k F, MultilinearDeg3 r := by
  induction F with
  | nil => intro k r hr; simp [formulaBlocks] at hr
  | cons c F ih =>
      intro k r hr
      simp only [formulaBlocks, clauseBlock, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with ((h | rfl | rfl) | h)
      · exact multilinear_litsBlock c k r h
      · exact multilinear_product k
      · simp [MultilinearDeg3, dummy]
      · exact ih _ r h

/-- Every residual of the produced instance is multilinear of degree at most three. -/
theorem multilinear_polyReduce (F : Formula ℕ) : ∀ r ∈ (polyReduce F).1, MultilinearDeg3 r := by
  intro r hr
  simp only [polyReduce, List.cons_append, List.mem_cons, List.mem_append] at hr
  rcases hr with rfl | h | h
  · simp [MultilinearDeg3, dummy]
  · exact multilinear_formulaBlocks F 0 r h
  · simp only [xForcing, List.mem_flatMap] at h
    obtain ⟨_, _, l, _, h⟩ := h
    exact multilinear_forcingRes _ r h

/-! ### Values -/

noncomputable section

open Classical

variable {p : ℕ} [hp : Fact p.Prime]

/-- Boolean forcing cost on `ℤ_p`. -/
def UZ (t : ℤ_[p]) : ℝ := ‖t‖ + ‖t - 1‖

theorem UZ_zero : UZ (0 : ℤ_[p]) = 1 := by simp [UZ]

theorem UZ_one : UZ (1 : ℤ_[p]) = 1 := by simp [UZ]

theorem polyLoss_append (x : ℕ → ℤ_[p]) (A B : List PolyResidual) :
    polyLoss p x (A ++ B) = polyLoss p x A + polyLoss p x B := by
  simp [polyLoss, List.map_append, List.sum_append]

theorem polyLoss_forcingRes (x : ℕ → ℤ_[p]) (i : ℕ) :
    polyLoss p x (forcingRes (i + 1)) = UZ (x i) := by
  simp [polyLoss, forcingRes, residualValue, factorValue, termZ, UZ, sub_eq_add_neg]

/-- The value of the linking residual. -/
def linkVal (x : ℕ → ℤ_[p]) (k : ℕ) : Literal ℕ → ℤ_[p]
  | .positive v => x (2 * k) - x (2 * v + 1)
  | .negative v => x (2 * k) - 1 + x (2 * v + 1)

theorem polyLoss_litBlock (x : ℕ → ℤ_[p]) (k : ℕ) (l : Literal ℕ) :
    polyLoss p x (litBlock k l) = 2 * UZ (x (2 * k)) + ‖linkVal x k l‖ := by
  rw [litBlock, polyLoss_append, polyLoss_append, yIdx, polyLoss_forcingRes]
  have : polyLoss p x [linking k l] = ‖linkVal x k l‖ := by
    cases l <;> simp [polyLoss, linking, residualValue, factorValue, termZ, linkVal, yIdx,
      xIdx] <;> ring_nf
  rw [this]
  ring

theorem polyLoss_product (x : ℕ → ℤ_[p]) (k : ℕ) :
    polyLoss p x [product k] = ‖x (2 * k) * x (2 * k + 2) * x (2 * k + 4)‖ := by
  simp [polyLoss, product, residualValue, factorValue, termZ, yIdx]
  ring_nf

theorem polyLoss_dummy (x : ℕ → ℤ_[p]) : polyLoss p x [dummy] = 0 := by
  simp [polyLoss, dummy, residualValue, factorValue]

/-- The contribution of a clause of exact width three starting at occurrence `k`,
including the forcing pairs on its variables. -/
def clauseValue (x : ℕ → ℤ_[p]) (k : ℕ) (c : Clause ℕ) : ℝ :=
  polyLoss p x (clauseBlock k c) + (c.map fun l => UZ (x (2 * litVar l + 1))).sum

theorem polyLoss_xForcing (x : ℕ → ℤ_[p]) (F : Formula ℕ) :
    polyLoss p x (xForcing F) =
      (F.map fun c => (c.map fun l => UZ (x (2 * litVar l + 1))).sum).sum := by
  have hflat : ∀ {α : Type} (f : α → List PolyResidual) (L : List α),
      polyLoss p x (L.flatMap f) = (L.map fun a => polyLoss p x (f a)).sum := by
    intro α f L
    induction L with
    | nil => rfl
    | cons a L ih => rw [List.flatMap_cons, polyLoss_append, ih, List.map_cons, List.sum_cons]
  rw [xForcing, hflat]
  simp only [hflat, xIdx, show ∀ v, 2 * v + 2 = (2 * v + 1) + 1 from fun v => rfl,
    polyLoss_forcingRes, List.map_reverse, List.sum_reverse]

/-- The total objective, written per clause. -/
def sumValue (x : ℕ → ℤ_[p]) : ℕ → Formula ℕ → ℝ
  | _, [] => 0
  | k, c :: F => clauseValue x k c + sumValue x (k + c.length) F

theorem polyLoss_polyReduce (x : ℕ → ℤ_[p]) (F : Formula ℕ) :
    polyLoss p x (polyReduce F).1 = sumValue x 0 F := by
  have key : ∀ k, polyLoss p x (formulaBlocks k F) +
      (F.map fun c => (c.map fun l => UZ (x (2 * litVar l + 1))).sum).sum = sumValue x k F := by
    induction F with
    | nil => intro k; simp [formulaBlocks, sumValue, polyLoss]
    | cons c F ih =>
        intro k
        rw [formulaBlocks, polyLoss_append, List.map_cons, List.sum_cons, sumValue, clauseValue,
          ← ih]
        ring
  rw [polyReduce, List.cons_append, show dummy :: (formulaBlocks 0 F ++ xForcing F) =
    [dummy] ++ (formulaBlocks 0 F ++ xForcing F) from rfl, polyLoss_append, polyLoss_append,
    polyLoss_dummy, polyLoss_xForcing, zero_add, key]

/-! ### Snapping on `ℤ_p` -/

/-- Snap to `1` when `p`-adically close to `1`, and to `0` otherwise. -/
def snapZ (t : ℤ_[p]) : ℤ_[p] := if ‖t - 1‖ < 1 then 1 else 0

theorem snapZ_bool (t : ℤ_[p]) : snapZ t = 0 ∨ snapZ t = 1 := by
  unfold snapZ; split_ifs <;> simp

theorem snapZ_le (t : ℤ_[p]) : UZ (snapZ t) + ‖t - snapZ t‖ ≤ UZ t := by
  unfold snapZ
  split_ifs with h
  · rw [UZ_one, UZ]
    have h1 : (1 : ℝ) ≤ ‖t‖ := by
      have := PadicInt.nonarchimedean t (-(t - 1))
      rw [show t + -(t - 1) = 1 by ring, norm_one, norm_neg] at this
      rcases le_max_iff.mp this with h' | h'
      · exact h'
      · linarith
    linarith
  · rw [UZ_zero, UZ, sub_zero]
    push_neg at h
    linarith

theorem norm_mul3_sub_le (a b c a' b' c' : ℤ_[p]) :
    ‖a * b * c - a' * b' * c'‖ ≤ ‖a - a'‖ + ‖b - b'‖ + ‖c - c'‖ := by
  have hsplit : a * b * c - a' * b' * c' =
      (a - a') * (b * c) + a' * ((b - b') * c) + a' * b' * (c - c') := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  refine add_le_add (le_trans (norm_add_le _ _) (add_le_add ?_ ?_)) ?_
  · rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
  · rw [norm_mul, norm_mul]
    calc ‖a'‖ * (‖b - b'‖ * ‖c‖) ≤ 1 * (‖b - b'‖ * 1) := by
          gcongr
          · exact PadicInt.norm_le_one _
          · exact PadicInt.norm_le_one _
      _ = ‖b - b'‖ := by ring
  · rw [norm_mul, norm_mul]
    calc ‖a'‖ * ‖b'‖ * ‖c - c'‖ ≤ 1 * 1 * ‖c - c'‖ := by
          gcongr
          · exact PadicInt.norm_le_one _
          · exact PadicInt.norm_le_one _
      _ = ‖c - c'‖ := by ring

theorem linkVal_snap_le (x : ℕ → ℤ_[p]) (k : ℕ) (l : Literal ℕ) :
    ‖linkVal (fun i => snapZ (x i)) k l‖ ≤ ‖linkVal x k l‖ +
      ‖x (2 * k) - snapZ (x (2 * k))‖ +
        ‖x (2 * litVar l + 1) - snapZ (x (2 * litVar l + 1))‖ := by
  cases l with
  | positive v =>
      have := norm_add_le (linkVal x k (.positive v))
        (-(x (2 * k) - snapZ (x (2 * k))) + (x (2 * v + 1) - snapZ (x (2 * v + 1))))
      have h2 := norm_add_le (-(x (2 * k) - snapZ (x (2 * k))))
        (x (2 * v + 1) - snapZ (x (2 * v + 1)))
      rw [norm_neg] at h2
      simp only [linkVal, litVar] at this ⊢
      rw [show x (2 * k) - x (2 * v + 1) + (-(x (2 * k) - snapZ (x (2 * k))) +
        (x (2 * v + 1) - snapZ (x (2 * v + 1)))) = snapZ (x (2 * k)) - snapZ (x (2 * v + 1))
        by ring] at this
      linarith
  | negative v =>
      have := norm_add_le (linkVal x k (.negative v))
        (-(x (2 * k) - snapZ (x (2 * k))) + -(x (2 * v + 1) - snapZ (x (2 * v + 1))))
      have h2 := norm_add_le (-(x (2 * k) - snapZ (x (2 * k))))
        (-(x (2 * v + 1) - snapZ (x (2 * v + 1))))
      rw [norm_neg, norm_neg] at h2
      simp only [linkVal, litVar] at this ⊢
      rw [show x (2 * k) - 1 + x (2 * v + 1) + (-(x (2 * k) - snapZ (x (2 * k))) +
        -(x (2 * v + 1) - snapZ (x (2 * v + 1)))) =
        snapZ (x (2 * k)) - 1 + snapZ (x (2 * v + 1)) by ring] at this
      linarith

theorem clauseValue_three (x : ℕ → ℤ_[p]) (k : ℕ) (l₀ l₁ l₂ : Literal ℕ) :
    clauseValue x k [l₀, l₁, l₂] =
      2 * UZ (x (2 * k)) + ‖linkVal x k l₀‖ + (2 * UZ (x (2 * (k + 1))) +
        ‖linkVal x (k + 1) l₁‖) + (2 * UZ (x (2 * (k + 2))) + ‖linkVal x (k + 2) l₂‖) +
        ‖x (2 * k) * x (2 * k + 2) * x (2 * k + 4)‖ +
        (UZ (x (2 * litVar l₀ + 1)) + UZ (x (2 * litVar l₁ + 1)) + UZ (x (2 * litVar l₂ + 1))) := by
  simp only [clauseValue, clauseBlock, litsBlock, List.append_nil, polyLoss_append,
    polyLoss_litBlock, show [product k, dummy] = [product k] ++ [dummy] from rfl,
    polyLoss_product, polyLoss_dummy, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [show k + 1 + 1 = k + 2 by ring]
  ring

/-- Snapping all coordinates does not increase the contribution of a width-three
clause. -/
theorem clauseValue_snap_le (x : ℕ → ℤ_[p]) (k : ℕ) (l₀ l₁ l₂ : Literal ℕ) :
    clauseValue (fun i => snapZ (x i)) k [l₀, l₁, l₂] ≤ clauseValue x k [l₀, l₁, l₂] := by
  rw [clauseValue_three, clauseValue_three]
  have y0 := snapZ_le (x (2 * k))
  have y1 := snapZ_le (x (2 * (k + 1)))
  have y2 := snapZ_le (x (2 * (k + 2)))
  have v0 := snapZ_le (x (2 * litVar l₀ + 1))
  have v1 := snapZ_le (x (2 * litVar l₁ + 1))
  have v2 := snapZ_le (x (2 * litVar l₂ + 1))
  have k0 := linkVal_snap_le x k l₀
  have k1 := linkVal_snap_le x (k + 1) l₁
  have k2 := linkVal_snap_le x (k + 2) l₂
  have hp := norm_mul3_sub_le (snapZ (x (2 * k))) (snapZ (x (2 * k + 2)))
    (snapZ (x (2 * k + 4))) (x (2 * k)) (x (2 * k + 2)) (x (2 * k + 4))
  have hpn : ‖snapZ (x (2 * k)) * snapZ (x (2 * k + 2)) * snapZ (x (2 * k + 4))‖ ≤
      ‖x (2 * k) * x (2 * k + 2) * x (2 * k + 4)‖ +
        ‖snapZ (x (2 * k)) * snapZ (x (2 * k + 2)) * snapZ (x (2 * k + 4)) -
          x (2 * k) * x (2 * k + 2) * x (2 * k + 4)‖ := by
    have := norm_add_le (x (2 * k) * x (2 * k + 2) * x (2 * k + 4))
      (snapZ (x (2 * k)) * snapZ (x (2 * k + 2)) * snapZ (x (2 * k + 4)) -
        x (2 * k) * x (2 * k + 2) * x (2 * k + 4))
    rwa [add_sub_cancel] at this
  rw [norm_sub_rev (snapZ (x (2 * k))), norm_sub_rev (snapZ (x (2 * k + 2))),
    norm_sub_rev (snapZ (x (2 * k + 4)))] at hp
  simp only [show 2 * (k + 1) = 2 * k + 2 by ring, show 2 * (k + 2) = 2 * k + 4 by ring]
    at y1 y2 k1 k2 ⊢
  linarith

/-! ### Boolean points -/

/-- The value of a Boolean colour in `ℤ_p`. -/
def bz (c : Bool) : ℤ_[p] := if c then 1 else 0

theorem UZ_bz (c : Bool) : UZ (bz (p := p) c) = 1 := by
  cases c <;> simp [bz, UZ_zero, UZ_one]

theorem norm_bz (c : Bool) : ‖(bz (p := p) c)‖ = if c then 1 else 0 := by
  cases c <;> simp [bz]

/-- The failure value of a literal at the assignment `a`, as a Boolean. -/
def fails (a : ℕ → Bool) (l : Literal ℕ) : Bool := !(l.eval a)

theorem bool_of_bz (x : ℕ → ℤ_[p]) (hx : ∀ i, x i = bz (decide (x i = 1))) (i : ℕ) :
    x i = 0 ∨ x i = 1 := by
  rw [hx i]; unfold bz; split <;> simp

theorem linkVal_bool_ge (x : ℕ → ℤ_[p]) (hx : ∀ i, x i = bz (decide (x i = 1))) (k : ℕ)
    (l : Literal ℕ) (hl : fails (fun v => decide (x (2 * v + 1) = 0)) l = true) :
    x (2 * k) = 1 ∨ 1 ≤ ‖linkVal x k l‖ := by
  rcases bool_of_bz x hx (2 * k) with hy | hy
  · right
    cases l with
    | positive v =>
        have hv : x (2 * v + 1) = 1 := by
          rcases bool_of_bz x hx (2 * v + 1) with h | h
          · simp [fails, Literal.eval, h] at hl
          · exact h
        simp [linkVal, hy, hv]
    | negative v =>
        have hv : x (2 * v + 1) = 0 := by
          rcases bool_of_bz x hx (2 * v + 1) with h | h
          · exact h
          · simp [fails, Literal.eval, h] at hl
        simp [linkVal, hy, hv]
  · left; exact hy

/-- At a Boolean point, a width-three clause contributes at least `9` plus its falsity
indicator under the assignment read from the variable coordinates. -/
theorem clauseValue_bool_ge (x : ℕ → ℤ_[p]) (hx : ∀ i, x i = bz (decide (x i = 1))) (k : ℕ)
    (l₀ l₁ l₂ : Literal ℕ) :
    9 + (if Clause.eval (fun v => decide (x (2 * v + 1) = 0)) [l₀, l₁, l₂] then 0 else 1) ≤
      clauseValue x k [l₀, l₁, l₂] := by
  rw [clauseValue_three]
  have hU : ∀ i, UZ (x i) = 1 := fun i => by rw [hx i, UZ_bz]
  simp only [hU]
  have n0 := norm_nonneg (linkVal x k l₀)
  have n1 := norm_nonneg (linkVal x (k + 1) l₁)
  have n2 := norm_nonneg (linkVal x (k + 2) l₂)
  have np := norm_nonneg (x (2 * k) * x (2 * k + 2) * x (2 * k + 4))
  split_ifs with hc
  · linarith
  · have hf : ∀ l ∈ [l₀, l₁, l₂], fails (fun v => decide (x (2 * v + 1) = 0)) l = true := by
      intro l hl
      simp only [Clause.eval, List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hc
      have := hc l hl
      simp only [fails, this, Bool.not_false]
    rcases linkVal_bool_ge x hx k l₀ (hf l₀ (by simp)) with h0 | h0
    · rcases linkVal_bool_ge x hx (k + 1) l₁ (hf l₁ (by simp)) with h1 | h1
      · rcases linkVal_bool_ge x hx (k + 2) l₂ (hf l₂ (by simp)) with h2 | h2
        · rw [show 2 * (k + 1) = 2 * k + 2 by ring] at h1
          rw [show 2 * (k + 2) = 2 * k + 4 by ring] at h2
          rw [h0, h1, h2]
          simp only [mul_one, norm_one]
          linarith
        · linarith
      · linarith
    · linarith

/-- The consistent point of an assignment: occurrence coordinates carry the failure
values of their literals, variable coordinates carry `0` for true and `1` for false. -/
def point (a : ℕ → Bool) (occ : List (Literal ℕ)) : ℕ → ℤ_[p] := fun i =>
  if i % 2 = 0 then bz ((occ[i / 2]?.map (fails a)).getD false) else bz (!a (i / 2))

theorem point_y (a : ℕ → Bool) (occ : List (Literal ℕ)) (k : ℕ) :
    point (p := p) a occ (2 * k) = bz ((occ[k]?.map (fails a)).getD false) := by
  simp [point]

theorem point_x (a : ℕ → Bool) (occ : List (Literal ℕ)) (v : ℕ) :
    point (p := p) a occ (2 * v + 1) = bz (!a v) := by
  simp [point, Nat.add_mod, show (2 * v + 1) / 2 = v by omega]

theorem linkVal_point (a : ℕ → Bool) (occ : List (Literal ℕ)) (k : ℕ) (l : Literal ℕ)
    (hk : occ[k]? = some l) : linkVal (point (p := p) a occ) k l = 0 := by
  rw [show linkVal (point (p := p) a occ) k l = linkVal (point (p := p) a occ) k l from rfl]
  cases l with
  | positive v =>
      simp only [linkVal, point_y, hk, Option.map_some, Option.getD_some, point_x, fails,
        Literal.eval]
      cases a v <;> simp [bz]
  | negative v =>
      simp only [linkVal, point_y, hk, Option.map_some, Option.getD_some, point_x, fails,
        Literal.eval]
      cases a v <;> simp [bz]

/-- At the consistent point of an assignment, a satisfied width-three clause contributes
exactly `9`. -/
theorem clauseValue_point (a : ℕ → Bool) (occ : List (Literal ℕ)) (k : ℕ)
    (l₀ l₁ l₂ : Literal ℕ) (h₀ : occ[k]? = some l₀) (h₁ : occ[k + 1]? = some l₁)
    (h₂ : occ[k + 2]? = some l₂) (hsat : Clause.eval a [l₀, l₁, l₂] = true) :
    clauseValue (point (p := p) a occ) k [l₀, l₁, l₂] = 9 := by
  rw [clauseValue_three, linkVal_point a occ k l₀ h₀, linkVal_point a occ (k + 1) l₁ h₁,
    linkVal_point a occ (k + 2) l₂ h₂]
  have hU : ∀ i, UZ (point (p := p) a occ i) = 1 := by
    intro i; unfold point; split_ifs <;> exact UZ_bz _
  simp only [hU, norm_zero]
  have hprod : point (p := p) a occ (2 * k) * point a occ (2 * k + 2) * point a occ (2 * k + 4)
      = 0 := by
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, show 2 * k + 4 = 2 * (k + 2) by ring, point_y,
      point_y, point_y, h₀, h₁, h₂]
    simp only [Option.map_some, Option.getD_some]
    simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true] at hsat
    rcases hsat with h | h | h
    · have hf : fails a l₀ = false := by simp [fails, h]
      rw [hf]; simp [bz]
    · have hf : fails a l₁ = false := by simp [fails, h]
      rw [hf]; simp [bz]
    · have hf : fails a l₂ = false := by simp [fails, h]
      rw [hf]; simp [bz]
  rw [hprod, norm_zero]
  norm_num

/-! ### Correctness -/

theorem sumValue_snap_le (x : ℕ → ℤ_[p]) (F : Formula ℕ) (hF : F.ExactWidth 3) :
    ∀ k, sumValue (fun i => snapZ (x i)) k F ≤ sumValue x k F := by
  induction F with
  | nil => intro k; simp [sumValue]
  | cons c F ih =>
      intro k
      have hc := hF c (List.mem_cons_self ..)
      obtain ⟨l₀, l₁, l₂, rfl⟩ : ∃ l₀ l₁ l₂, c = [l₀, l₁, l₂] := by
        match c, hc with
        | [l₀, l₁, l₂], _ => exact ⟨l₀, l₁, l₂, rfl⟩
      simp only [sumValue]
      exact add_le_add (clauseValue_snap_le x k l₀ l₁ l₂)
        (ih (fun c' hc' => hF c' (List.mem_cons_of_mem _ hc')) _)

theorem sumValue_bool_ge (x : ℕ → ℤ_[p]) (hx : ∀ i, x i = bz (decide (x i = 1)))
    (F : Formula ℕ) (hF : F.ExactWidth 3) : ∀ k,
    9 * (F.length : ℝ) + ((F.filter fun c =>
      !Clause.eval (fun v => decide (x (2 * v + 1) = 0)) c).length : ℝ) ≤ sumValue x k F := by
  induction F with
  | nil => intro k; simp [sumValue]
  | cons c F ih =>
      intro k
      have hc := hF c (List.mem_cons_self ..)
      obtain ⟨l₀, l₁, l₂, rfl⟩ : ∃ l₀ l₁ l₂, c = [l₀, l₁, l₂] := by
        match c, hc with
        | [l₀, l₁, l₂], _ => exact ⟨l₀, l₁, l₂, rfl⟩
      have h1 := clauseValue_bool_ge x hx k l₀ l₁ l₂
      have h2 := ih (fun c' hc' => hF c' (List.mem_cons_of_mem _ hc')) (k + 3)
      simp only [sumValue, List.length_cons, List.length_nil, List.filter_cons, Nat.zero_add,
        Nat.reduceAdd]
      by_cases hs : Clause.eval (fun v => decide (x (2 * v + 1) = 0)) [l₀, l₁, l₂] = true
      · rw [if_pos hs] at h1
        simp only [hs, Bool.not_true, Bool.false_eq_true, if_false]
        push_cast
        linarith
      · have hs' := Bool.eq_false_iff.mpr hs
        rw [if_neg hs] at h1
        simp only [hs', Bool.not_false, if_true, List.length_cons]
        push_cast
        linarith

theorem sumValue_point (a : ℕ → Bool) (F₀ F : Formula ℕ) (hF : F.ExactWidth 3)
    (hsat : F.Satisfied a) : ∀ k, F₀.flatten.drop k = F.flatten →
    sumValue (point (p := p) a F₀.flatten) k F = 9 * F.length := by
  induction F with
  | nil => intro k _; simp [sumValue]
  | cons c F ih =>
      intro k hk
      have hc := hF c (List.mem_cons_self ..)
      obtain ⟨l₀, l₁, l₂, rfl⟩ : ∃ l₀ l₁ l₂, c = [l₀, l₁, l₂] := by
        match c, hc with
        | [l₀, l₁, l₂], _ => exact ⟨l₀, l₁, l₂, rfl⟩
      have hget : ∀ j, F₀.flatten[k + j]? = ([l₀, l₁, l₂] ++ F.flatten)[j]? := by
        intro j
        rw [← List.getElem?_drop, hk]
        simp
      have hs : Clause.eval a [l₀, l₁, l₂] = true :=
        (Clause.eval_eq_true a _).mpr (hsat _ (List.mem_cons_self ..))
      simp only [sumValue]
      rw [clauseValue_point a F₀.flatten k l₀ l₁ l₂ (by simpa using hget 0)
        (by simpa using hget 1) (by simpa using hget 2) hs]
      rw [show k + [l₀, l₁, l₂].length = k + 3 from rfl,
        ih (fun c' hc' => hF c' (List.mem_cons_of_mem _ hc'))
        (fun c' hc' => hsat c' (List.mem_cons_of_mem _ hc')) (k + 3)]
      · simp; ring
      · rw [← List.drop_drop, hk]
        simp

/-- **The multilinear polynomial-residual reduction preserves membership.** For every
prime `p` and every formula of exact width three, the formula is satisfiable iff the
instance `polyReduce F` (all of whose residuals are multilinear of degree at most
three) has a point of `ℤ_p` with objective at most `9m`. -/
theorem poly_iff (F : Formula ℕ) (hF : F.ExactWidth 3) :
    F.Satisfiable ↔ PolyRegressionLangML p (polyReduce F) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨multilinear_polyReduce F, point a F.flatten, ?_⟩
    rw [polyLoss_polyReduce, sumValue_point a F F hF ha 0 (by simp)]
    simp [polyReduce]
  · rintro ⟨_, x, hx⟩
    rw [polyLoss_polyReduce] at hx
    have hsnap := sumValue_snap_le x F hF 0
    set b : ℕ → ℤ_[p] := fun i => snapZ (x i) with hb
    have hbool : ∀ i, b i = bz (decide (b i = 1)) := by
      intro i
      rcases snapZ_bool (x i) with h | h <;> simp [hb, h, bz]
    have hge := sumValue_bool_ge b hbool F hF 0
    set a : ℕ → Bool := fun v => decide (b (2 * v + 1) = 0)
    refine ⟨a, fun c hc => (Clause.eval_eq_true a c).mp ?_⟩
    by_contra hne
    have hne' : Clause.eval a c = false := Bool.eq_false_iff.mpr hne
    have hpos : 1 ≤ ((F.filter fun c => !Clause.eval a c).length : ℝ) := by
      have : c ∈ F.filter fun c => !Clause.eval a c :=
        List.mem_filter.mpr ⟨hc, by simp [hne']⟩
      exact_mod_cast List.length_pos_of_mem this
    have : (polyReduce F).2 = 9 * F.length := rfl
    simp only [this] at hx
    push_cast at hx
    linarith

end

end PhdThesisLean.PolynomialResidualReduction

#print axioms PhdThesisLean.PolynomialResidualReduction.poly_iff
