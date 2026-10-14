import PhdThesisLean.AllDifferent

namespace PhdThesisLean.NestedEasyHardEasy

open scoped BigOperators
open PhdThesisLean.AllDifferent (IsGlobalMin)

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-!
# A nested easy–hard–easy family

This module formalises thesis Theorem `thm:nested-easy-hard-easy` from
`complexity-regimes/body.tex` (section `sec:nested-easy-hard-easy`), including
the three stages of its proof and Claims 1–3 of Stage 3.

The prime is fixed at `p = 5`.  A regression row is a pair
`(predictor vector, target)` in `(Fin n → ℚ_[5]) × ℚ_[5]`; a dataset is a
`Multiset` of rows, so repeated copies are retained and the nesting
`A_G ≤ A'_G ≤ A''_G` is literal multiset inclusion.  The summed loss
`loss A β = ∑_{r ∈ A} ‖target − ⟪predictor, β⟫‖` is the thesis's ordinary summed
`5`-adic objective.

Correspondence notes.

* Stronger than the thesis: coefficient vectors range over `ℚ_[5]` rather than
  `ℚ`, and the graph may be a multigraph (edges form an arbitrary finite type
  `ε` with endpoint maps `left right : ε → Fin n`; the only hypothesis is
  `hne : ∀ e, left e ≠ right e`, i.e. no self-loops).
* Stage 1 (`stage1_globalMin_iff`, `loss_A_zero`): the unique optimum of
  `A_G` is `β = 0`, with loss `0`.
* Stage 2 (`loss_A'`, `card_A'`): the loss of `A'_G` is exactly the displayed
  Max-Cut objective `∑ j, M j (‖β j‖ + ‖β j − 1‖) + ∑ e, ‖β u + β v − 1‖` and
  `|A'_G| = 5|E| + 2|V|`.  The NP-hardness of minimising this objective is the
  thesis's Theorem `thm:fixed-prime-hardness`; it is *not* proved here (a
  separate module handles that reduction) and this file does not depend on it.
* Stage 3 (`stage3_globalMin_iff`, `stage3_optimum`, `loss_A''_optimum`): for
  every `L ≥ 1` the global minimisers of `A''_G` are exactly the grid points
  `T^n`, so `β* = (c, …, c)` is an explicit closed-form optimum with loss
  `m_H 5^L + 4 n N 5^L`.  Claims 1–3 are `loss_A'_of_inBox`,
  `S_grid`/`S_gt_of_inBox_not_grid`, and `S_ge_of_not_inBox`.
* The polynomial-time nature of "output `β*`" is not formalised as a complexity
  statement; the closed form itself is.
-/

/-- A regression row: a predictor vector and a target. -/
abbrev Row (n : ℕ) := (Fin n → ℚ_[5]) × ℚ_[5]

/-- Ordinary summed `5`-adic loss of a multiset of rows. -/
noncomputable def loss {n : ℕ} (A : Multiset (Row n)) (β : Fin n → ℚ_[5]) : ℝ :=
  (A.map (fun r => ‖r.2 - ∑ j, r.1 j * β j‖)).sum

section LossLemmas

variable {n : ℕ}

theorem loss_zero (β : Fin n → ℚ_[5]) : loss (0 : Multiset (Row n)) β = 0 := by
  simp [loss]

theorem loss_add (A B : Multiset (Row n)) (β : Fin n → ℚ_[5]) :
    loss (A + B) β = loss A β + loss B β := by
  simp [loss, Multiset.map_add, Multiset.sum_add]

theorem loss_singleton (r : Row n) (β : Fin n → ℚ_[5]) :
    loss ({r} : Multiset (Row n)) β = ‖r.2 - ∑ j, r.1 j * β j‖ := by
  simp [loss]

theorem loss_replicate (k : ℕ) (r : Row n) (β : Fin n → ℚ_[5]) :
    loss (Multiset.replicate k r) β = k * ‖r.2 - ∑ j, r.1 j * β j‖ := by
  simp [loss, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]

theorem loss_sum {ι : Type*} (s : Finset ι) (A : ι → Multiset (Row n))
    (β : Fin n → ℚ_[5]) :
    loss (∑ i ∈ s, A i) β = ∑ i ∈ s, loss (A i) β := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [loss_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, loss_add, ih, Finset.sum_insert ha]

theorem loss_nonneg (A : Multiset (Row n)) (β : Fin n → ℚ_[5]) : 0 ≤ loss A β := by
  unfold loss
  apply Multiset.sum_nonneg
  intro x hx
  obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hx
  exact norm_nonneg _

end LossLemmas

/-- The `j`-th standard basis vector. -/
noncomputable def basis {n : ℕ} (j : Fin n) : Fin n → ℚ_[5] := Pi.single j 1

theorem sum_basis_mul {n : ℕ} (j : Fin n) (β : Fin n → ℚ_[5]) :
    ∑ k, basis j k * β k = β j := by
  simp [basis, Pi.single_apply]

theorem sum_basis_add_mul {n : ℕ} (u v : Fin n) (β : Fin n → ℚ_[5]) :
    ∑ k, (basis u + basis v) k * β k = β u + β v := by
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, sum_basis_mul]

section Graph

variable {n : ℕ} {ε : Type*} [Fintype ε]

/-- Degree of vertex `j` in the (multi)graph with endpoint maps `left`, `right`. -/
def deg (left right : ε → Fin n) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun e => left e = j ∨ right e = j)).card

/-- The pinning multiplicity `M_j = d_j + 1`. -/
def M (left right : ε → Fin n) (j : Fin n) : ℕ := deg left right j + 1

theorem M_sub_one (left right : ε → Fin n) (j : Fin n) :
    M left right j - 1 = deg left right j := Nat.add_sub_cancel _ _

/-- Double counting: `∑ j, d_j = 2 |E|` (each edge has two distinct endpoints). -/
theorem sum_deg (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e) :
    ∑ j, deg left right j = 2 * Fintype.card ε := by
  unfold deg
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have h2 : ∀ e : ε, (∑ j : Fin n, if left e = j ∨ right e = j then 1 else 0) = 2 := by
    intro e
    rw [← Finset.card_filter]
    have hset : (Finset.univ.filter (fun j : Fin n => left e = j ∨ right e = j)) =
        {left e, right e} := by
      ext j
      simp [eq_comm]
    rw [hset, Finset.card_pair (hne e)]
  simp only [h2, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

/-- Stage 1 dataset: one row `(e_j, 0)` per vertex. -/
noncomputable def A_G (n : ℕ) : Multiset (Row n) :=
  ∑ j : Fin n, ({(basis j, 0)} : Multiset (Row n))

/-- Stage 2 dataset `A'_G`. -/
noncomputable def A'_G (left right : ε → Fin n) : Multiset (Row n) :=
  A_G n
    + ∑ j : Fin n, Multiset.replicate (M left right j - 1) (basis j, 0)
    + ∑ j : Fin n, Multiset.replicate (M left right j) (basis j, 1)
    + ∑ e : ε, ({(basis (left e) + basis (right e), 1)} : Multiset (Row n))

theorem A_le_A' (left right : ε → Fin n) : A_G n ≤ A'_G left right := by
  unfold A'_G
  exact le_trans (Multiset.le_add_right _ _)
    (le_trans (Multiset.le_add_right _ _) (Multiset.le_add_right _ _))

/-! ### Stage 1 -/

theorem loss_A (β : Fin n → ℚ_[5]) : loss (A_G n) β = ∑ j, ‖β j‖ := by
  unfold A_G
  rw [loss_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [loss_singleton]
  simp [sum_basis_mul]

theorem loss_A_zero : loss (A_G n) 0 = 0 := by
  simp [loss_A]

theorem stage1_globalMin_iff (β : Fin n → ℚ_[5]) :
    IsGlobalMin (loss (A_G n)) β ↔ β = 0 := by
  constructor
  · intro h
    have h0 := h 0
    rw [loss_A_zero, loss_A] at h0
    have hsum : ∑ j, ‖β j‖ = 0 :=
      le_antisymm h0 (Finset.sum_nonneg fun j _ => norm_nonneg _)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => norm_nonneg (β j)).mp hsum
    funext j
    exact norm_eq_zero.mp (hall j (Finset.mem_univ j))
  · rintro rfl y
    rw [loss_A_zero]
    exact loss_nonneg _ _

/-! ### Stage 2 -/

/-- The loss of `A'_G` is exactly the thesis's Max-Cut objective. -/
theorem loss_A' (left right : ε → Fin n) (β : Fin n → ℚ_[5]) :
    loss (A'_G left right) β =
      ∑ j, (M left right j : ℝ) * (‖β j‖ + ‖β j - 1‖)
        + ∑ e, ‖β (left e) + β (right e) - 1‖ := by
  unfold A'_G
  rw [loss_add, loss_add, loss_add, loss_A, loss_sum, loss_sum, loss_sum]
  simp only [loss_replicate, loss_singleton, sum_basis_mul, sum_basis_add_mul, M_sub_one]
  have h1 : ∀ j, ‖(1 : ℚ_[5]) - β j‖ = ‖β j - 1‖ := fun j => norm_sub_rev _ _
  have h2 : ∀ e, ‖(1 : ℚ_[5]) - (β (left e) + β (right e))‖ =
      ‖β (left e) + β (right e) - 1‖ := fun e => norm_sub_rev _ _
  simp only [h1, h2, zero_sub, norm_neg]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [M]
  push_cast
  ring

theorem card_A' (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e) :
    Multiset.card (A'_G left right) = 5 * Fintype.card ε + 2 * n := by
  unfold A'_G A_G
  simp only [Multiset.card_add, Multiset.card_sum, Multiset.card_replicate,
    Multiset.card_singleton, M_sub_one]
  simp only [M, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, sum_deg left right hne]
  ring

end Graph

/-! ### Stage 3: p-adic norm facts -/

theorem norm_five_zpow (k : ℤ) : ‖(5 : ℚ_[5]) ^ k‖ = (5 : ℝ) ^ (-k) := by
  have h := Padic.norm_p_zpow (p := 5) k
  simpa using h

theorem norm_five_inv : ‖(5 : ℚ_[5])⁻¹‖ = 5 := by
  have h := Padic.norm_p (p := 5)
  simp only [Nat.cast_ofNat] at h
  rw [norm_inv, h, inv_inv]

theorem norm_two : ‖(2 : ℚ_[5])‖ = 1 := by
  have h := (Padic.norm_natCast_eq_one_iff (p := 5) (n := 2)).mpr (by norm_num)
  simpa using h

theorem norm_natCast_le_one (a : ℕ) : ‖((a : ℕ) : ℚ_[5])‖ ≤ 1 := by
  have h := Padic.norm_int_le_one (p := 5) (a : ℤ)
  simpa using h

/-- Non-archimedean "dominant term" rule. -/
theorem norm_add_eq_left {x y : ℚ_[5]} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [Padic.add_eq_max_of_ne (ne_of_gt h), max_eq_left h.le]

theorem norm_sub_le_max (x y : ℚ_[5]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have h := Padic.nonarchimedean x (-y)
  simpa [sub_eq_add_neg] using h

theorem five_zpow_pos (k : ℤ) : (0 : ℝ) < (5 : ℝ) ^ k := zpow_pos (by norm_num) k

theorem five_zpow_sub_one_lt (L : ℕ) : (5 : ℝ) ^ ((L : ℤ) - 1) < (5 : ℝ) ^ (L : ℤ) :=
  zpow_lt_zpow_right₀ (by norm_num) (by omega)

theorem one_le_five_zpow_sub_one {L : ℕ} (hL : 1 ≤ L) :
    (1 : ℝ) ≤ (5 : ℝ) ^ ((L : ℤ) - 1) :=
  one_le_zpow₀ (by norm_num) (by omega)

theorem five_mul_five_zpow_sub_one (L : ℕ) :
    (5 : ℝ) * (5 : ℝ) ^ ((L : ℤ) - 1) = (5 : ℝ) ^ (L : ℤ) := by
  rw [zpow_sub_one₀ (by norm_num)]
  ring

/-- `‖x‖ > 5^(L-1)` forces `‖x‖ ≥ 5^L`, because `5`-adic norms are powers of `5`. -/
theorem five_zpow_le_norm_of_lt {L : ℕ} {x : ℚ_[5]} (hx : (5 : ℝ) ^ ((L : ℤ) - 1) < ‖x‖) :
    (5 : ℝ) ^ (L : ℤ) ≤ ‖x‖ := by
  by_contra h
  push_neg at h
  have h' := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one x (L : ℤ)).mp (by simpa using h)
  simp only [Nat.cast_ofNat] at h'
  linarith

/-! ### Stage 3: the shell constants -/

/-- `c = 2 · 5^(-L)`. -/
noncomputable def c (L : ℕ) : ℚ_[5] := 2 * (5 : ℚ_[5]) ^ (-(L : ℤ))

/-- `δ = 5^(1-L)`. -/
noncomputable def δ (L : ℕ) : ℚ_[5] := (5 : ℚ_[5]) ^ ((1 : ℤ) - L)

/-- The five centres `t_a = c + a δ`, `a = 0, …, 4`. -/
noncomputable def t (L : ℕ) (a : Fin 5) : ℚ_[5] := c L + ((a : ℕ) : ℚ_[5]) * δ L

theorem t_zero (L : ℕ) : t L 0 = c L := by
  simp [t]

theorem norm_c (L : ℕ) : ‖c L‖ = (5 : ℝ) ^ (L : ℤ) := by
  rw [c, norm_mul, norm_two, one_mul, norm_five_zpow, neg_neg]

theorem norm_δ (L : ℕ) : ‖δ L‖ = (5 : ℝ) ^ ((L : ℤ) - 1) := by
  rw [δ, norm_five_zpow]
  congr 1
  ring

theorem norm_t_sub_c (L : ℕ) (a : Fin 5) : ‖t L a - c L‖ ≤ (5 : ℝ) ^ ((L : ℤ) - 1) := by
  have h : t L a - c L = ((a : ℕ) : ℚ_[5]) * δ L := by
    rw [t]
    ring
  rw [h, norm_mul, norm_δ]
  calc ‖((a : ℕ) : ℚ_[5])‖ * (5 : ℝ) ^ ((L : ℤ) - 1)
      ≤ 1 * (5 : ℝ) ^ ((L : ℤ) - 1) :=
        mul_le_mul_of_nonneg_right (norm_natCast_le_one a) (five_zpow_pos _).le
    _ = (5 : ℝ) ^ ((L : ℤ) - 1) := one_mul _

/-- Distinct centres are at distance exactly `5^(L-1)`: `a − b` is a `5`-adic unit. -/
theorem norm_t_sub_t (L : ℕ) {a b : Fin 5} (hab : a ≠ b) :
    ‖t L a - t L b‖ = (5 : ℝ) ^ ((L : ℤ) - 1) := by
  have h : t L a - t L b = (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) : ℤ) * δ L := by
    rw [t, t]
    push_cast
    ring
  rw [h, norm_mul, norm_δ]
  have hunit : ‖((((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) : ℤ) : ℚ_[5])‖ = 1 := by
    refine le_antisymm (Padic.norm_int_le_one _) (not_lt.mp ?_)
    rw [Padic.norm_intCast_lt_one_iff]
    intro hdvd
    have ha := a.isLt
    have hb := b.isLt
    have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
    omega
  rw [hunit, one_mul]

/-! ### Stage 3: the box and Claim 1 -/

/-- The `5`-adic box `C = ∏_j (c + δ ℤ_5)`, i.e. `‖β_j − c‖ ≤ 5^(L-1)` for all `j`. -/
def InBox {n : ℕ} (L : ℕ) (β : Fin n → ℚ_[5]) : Prop :=
  ∀ j, ‖β j - c L‖ ≤ (5 : ℝ) ^ ((L : ℤ) - 1)

theorem norm_of_box {L : ℕ} {x : ℚ_[5]} (hx : ‖x - c L‖ ≤ (5 : ℝ) ^ ((L : ℤ) - 1)) :
    ‖x‖ = (5 : ℝ) ^ (L : ℤ) := by
  have h : x = c L + (x - c L) := by ring
  rw [h, norm_add_eq_left, norm_c]
  rw [norm_c]
  exact lt_of_le_of_lt hx (five_zpow_sub_one_lt L)

theorem norm_sub_one_of_box {L : ℕ} (hL : 1 ≤ L) {x : ℚ_[5]}
    (hx : ‖x - c L‖ ≤ (5 : ℝ) ^ ((L : ℤ) - 1)) :
    ‖x - 1‖ = (5 : ℝ) ^ (L : ℤ) := by
  have h : x - 1 = c L + ((x - c L) - 1) := by ring
  rw [h, norm_add_eq_left, norm_c]
  rw [norm_c]
  calc ‖(x - c L) - 1‖ ≤ max ‖x - c L‖ ‖(1 : ℚ_[5])‖ := norm_sub_le_max _ _
    _ ≤ (5 : ℝ) ^ ((L : ℤ) - 1) :=
        max_le hx (by rw [norm_one]; exact one_le_five_zpow_sub_one hL)
    _ < (5 : ℝ) ^ (L : ℤ) := five_zpow_sub_one_lt L

theorem norm_edge_of_box {L : ℕ} (hL : 1 ≤ L) {u v : ℚ_[5]}
    (hu : ‖u - c L‖ ≤ (5 : ℝ) ^ ((L : ℤ) - 1))
    (hv : ‖v - c L‖ ≤ (5 : ℝ) ^ ((L : ℤ) - 1)) :
    ‖u + v - 1‖ = (5 : ℝ) ^ (L : ℤ) := by
  have h : u + v - 1 = 2 * c L + (((u - c L) + (v - c L)) - 1) := by ring
  have h2c : ‖(2 : ℚ_[5]) * c L‖ = (5 : ℝ) ^ (L : ℤ) := by
    rw [norm_mul, norm_two, one_mul, norm_c]
  rw [h, norm_add_eq_left, h2c]
  rw [h2c]
  calc ‖((u - c L) + (v - c L)) - 1‖
      ≤ max ‖(u - c L) + (v - c L)‖ ‖(1 : ℚ_[5])‖ := norm_sub_le_max _ _
    _ ≤ (5 : ℝ) ^ ((L : ℤ) - 1) := by
        refine max_le ?_ (by rw [norm_one]; exact one_le_five_zpow_sub_one hL)
        exact le_trans (Padic.nonarchimedean _ _) (max_le hu hv)
    _ < (5 : ℝ) ^ (L : ℤ) := five_zpow_sub_one_lt L

section Stage3

variable {n : ℕ} {ε : Type*} [Fintype ε]

/-- `m_H = |A'_G|`. -/
noncomputable def mH (left right : ε → Fin n) : ℕ := Multiset.card (A'_G left right)

/-- `N = m_H + 1`. -/
noncomputable def N (left right : ε → Fin n) : ℕ := mH left right + 1

/-- The shell row `(5⁻¹ e_j, 5⁻¹ t_a)`. -/
noncomputable def shellRow (L : ℕ) (j : Fin n) (a : Fin 5) : Row n :=
  ((5 : ℚ_[5])⁻¹ • basis j, (5 : ℚ_[5])⁻¹ * t L a)

/-- Stage 3 dataset `A''_G`: `A'_G` plus `N` copies of every shell row. -/
noncomputable def A''_G (left right : ε → Fin n) (L : ℕ) : Multiset (Row n) :=
  A'_G left right
    + ∑ j : Fin n, ∑ a : Fin 5, Multiset.replicate (N left right) (shellRow L j a)

theorem A'_le_A'' (left right : ε → Fin n) (L : ℕ) :
    A'_G left right ≤ A''_G left right L :=
  Multiset.le_add_right _ _

theorem N_pos (left right : ε → Fin n) : (0 : ℝ) < N left right := by
  unfold N
  positivity

/-- Claim 1: on the box every hard residual has norm exactly `5^L`, so the hard part is
the constant `m_H 5^L`. -/
theorem loss_A'_of_inBox (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    {L : ℕ} (hL : 1 ≤ L) {β : Fin n → ℚ_[5]} (hβ : InBox L β) :
    loss (A'_G left right) β = (mH left right : ℝ) * (5 : ℝ) ^ (L : ℤ) := by
  rw [loss_A']
  simp only [norm_of_box (hβ _), norm_sub_one_of_box hL (hβ _),
    norm_edge_of_box hL (hβ _) (hβ _)]
  rw [mH, card_A' left right hne]
  have hdeg : (∑ j, (deg left right j : ℝ)) = 2 * Fintype.card ε := by
    rw [← Nat.cast_sum, sum_deg left right hne]
    push_cast
    ring
  simp only [M, Nat.cast_add, Nat.cast_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, hdeg, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-! ### Stage 3: the shell -/

/-- The shell contribution of coordinate `j`. -/
noncomputable def S (left right : ε → Fin n) (L : ℕ) (j : Fin n) (β : Fin n → ℚ_[5]) : ℝ :=
  (N left right : ℝ) * ∑ a : Fin 5, ‖(5 : ℚ_[5])⁻¹ * (β j - t L a)‖

theorem shell_term (L : ℕ) (x : ℚ_[5]) (a : Fin 5) :
    ‖(5 : ℚ_[5])⁻¹ * (x - t L a)‖ = 5 * ‖x - t L a‖ := by
  rw [norm_mul, norm_five_inv]

theorem loss_A'' (left right : ε → Fin n) (L : ℕ) (β : Fin n → ℚ_[5]) :
    loss (A''_G left right L) β = loss (A'_G left right) β + ∑ j, S left right L j β := by
  unfold A''_G
  rw [loss_add, loss_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [loss_sum, S, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [loss_replicate, shellRow]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, sum_basis_mul]
  rw [← mul_sub, norm_mul, norm_mul, norm_sub_rev]

/-- Claim 2 (grid points): at a centre the shell contributes exactly `4 N 5^L`. -/
theorem S_grid (left right : ε → Fin n) (L : ℕ) (j : Fin n) (β : Fin n → ℚ_[5])
    {a : Fin 5} (ha : β j = t L a) :
    S left right L j β = 4 * (N left right : ℝ) * (5 : ℝ) ^ (L : ℤ) := by
  unfold S
  rw [← Finset.sum_add_sum_compl {a}, Finset.sum_singleton, ha, sub_self, mul_zero, norm_zero,
    zero_add]
  have hterms : ∀ b ∈ ({a}ᶜ : Finset (Fin 5)),
      ‖(5 : ℚ_[5])⁻¹ * (t L a - t L b)‖ = (5 : ℝ) ^ (L : ℤ) := by
    intro b hb
    have hb' : b ≠ a := by simpa using hb
    rw [shell_term, norm_t_sub_t L hb'.symm, five_mul_five_zpow_sub_one]
  rw [Finset.sum_congr rfl hterms, Finset.sum_const, Finset.card_compl, Fintype.card_fin,
    Finset.card_singleton, nsmul_eq_mul]
  push_cast
  ring

theorem norm_sub_t_le_of_box {L : ℕ} {x : ℚ_[5]}
    (hx : ‖x - c L‖ ≤ (5 : ℝ) ^ ((L : ℤ) - 1)) (a : Fin 5) :
    ‖x - t L a‖ ≤ (5 : ℝ) ^ ((L : ℤ) - 1) := by
  have h : x - t L a = (x - c L) - (t L a - c L) := by ring
  rw [h]
  exact le_trans (norm_sub_le_max _ _) (max_le hx (norm_t_sub_c L a))

/-- At most one centre can be strictly closer than `5^(L-1)`. -/
theorem close_centre_unique {L : ℕ} {x : ℚ_[5]} {a b : Fin 5}
    (ha : ‖x - t L a‖ < (5 : ℝ) ^ ((L : ℤ) - 1))
    (hb : ‖x - t L b‖ < (5 : ℝ) ^ ((L : ℤ) - 1)) : a = b := by
  by_contra hab
  have h := norm_t_sub_t L hab
  have hrw : t L a - t L b = (x - t L b) - (x - t L a) := by ring
  rw [hrw] at h
  have hlt := lt_of_le_of_lt (norm_sub_le_max _ _) (max_lt hb ha)
  linarith

/-- Claim 2, box case: the five shell terms sum to at least `4 · 5^L`, strictly more unless
`x` is one of the centres. -/
theorem shellSum_of_box {L : ℕ} {x : ℚ_[5]}
    (hx : ‖x - c L‖ ≤ (5 : ℝ) ^ ((L : ℤ) - 1)) :
    4 * (5 : ℝ) ^ (L : ℤ) ≤ ∑ a : Fin 5, ‖(5 : ℚ_[5])⁻¹ * (x - t L a)‖ ∧
      ((∀ a, x ≠ t L a) →
        4 * (5 : ℝ) ^ (L : ℤ) < ∑ a : Fin 5, ‖(5 : ℚ_[5])⁻¹ * (x - t L a)‖) := by
  set g : Fin 5 → ℝ := fun a => ‖(5 : ℚ_[5])⁻¹ * (x - t L a)‖ with hg
  set Bad : Finset (Fin 5) :=
    Finset.univ.filter (fun a : Fin 5 => ‖x - t L a‖ < (5 : ℝ) ^ ((L : ℤ) - 1)) with hBad
  have hcard : Bad.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    exact close_centre_unique (by simpa [hBad] using ha) (by simpa [hBad] using hb)
  have hgood : ∀ a ∈ Badᶜ, g a = (5 : ℝ) ^ (L : ℤ) := by
    intro a ha
    have hnot : ¬ ‖x - t L a‖ < (5 : ℝ) ^ ((L : ℤ) - 1) := by simpa [hBad] using ha
    simp only [hg]
    rw [shell_term, le_antisymm (norm_sub_t_le_of_box hx a) (not_lt.mp hnot),
      five_mul_five_zpow_sub_one]
  have hsplit : ∑ a, g a = ∑ a ∈ Badᶜ, g a + ∑ a ∈ Bad, g a := by
    rw [add_comm, Finset.sum_add_sum_compl]
  have hgoodsum : ∑ a ∈ Badᶜ, g a = ((5 - Bad.card : ℕ) : ℝ) * (5 : ℝ) ^ (L : ℤ) := by
    rw [Finset.sum_congr rfl hgood, Finset.sum_const, Finset.card_compl, Fintype.card_fin,
      nsmul_eq_mul]
  have hbadnn : 0 ≤ ∑ a ∈ Bad, g a := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h5 := five_zpow_pos (L : ℤ)
  constructor
  · show 4 * (5 : ℝ) ^ (L : ℤ) ≤ ∑ a, g a
    rw [hsplit, hgoodsum]
    have h4 : (4 : ℝ) ≤ ((5 - Bad.card : ℕ) : ℝ) := by
      have : 4 ≤ 5 - Bad.card := by omega
      exact_mod_cast this
    nlinarith
  · intro hne
    show 4 * (5 : ℝ) ^ (L : ℤ) < ∑ a, g a
    rw [hsplit, hgoodsum]
    rcases Nat.eq_zero_or_pos Bad.card with h0 | hpos
    · have hc : ((5 - Bad.card : ℕ) : ℝ) = 5 := by
        rw [h0]
        norm_num
      rw [hc]
      linarith
    · have h1 : Bad.card = 1 := by omega
      obtain ⟨a₀, ha₀⟩ := Finset.card_eq_one.mp h1
      have hc : ((5 - Bad.card : ℕ) : ℝ) = 4 := by
        rw [h1]
        norm_num
      rw [hc, ha₀, Finset.sum_singleton]
      have hpos' : 0 < g a₀ := by
        simp only [hg]
        rw [norm_pos_iff]
        exact mul_ne_zero (inv_ne_zero (by norm_num)) (sub_ne_zero.mpr (hne a₀))
      linarith

/-- Claim 3 (norm part): outside the box coordinate, every centre is at the same distance
`‖x − c‖ ≥ 5^L`. -/
theorem norm_sub_t_of_not_box {L : ℕ} {x : ℚ_[5]}
    (hx : (5 : ℝ) ^ ((L : ℤ) - 1) < ‖x - c L‖) (a : Fin 5) :
    ‖x - t L a‖ = ‖x - c L‖ := by
  have h : x - t L a = (x - c L) + (-(t L a - c L)) := by ring
  rw [h, norm_add_eq_left]
  rw [norm_neg]
  exact lt_of_le_of_lt (norm_t_sub_c L a) hx

theorem shellSum_of_not_box {L : ℕ} {x : ℚ_[5]}
    (hx : (5 : ℝ) ^ ((L : ℤ) - 1) < ‖x - c L‖) :
    25 * (5 : ℝ) ^ (L : ℤ) ≤ ∑ a : Fin 5, ‖(5 : ℚ_[5])⁻¹ * (x - t L a)‖ := by
  have hterm : ∀ a ∈ (Finset.univ : Finset (Fin 5)),
      5 * (5 : ℝ) ^ (L : ℤ) ≤ ‖(5 : ℚ_[5])⁻¹ * (x - t L a)‖ := by
    intro a _
    rw [shell_term, norm_sub_t_of_not_box hx]
    exact mul_le_mul_of_nonneg_left (five_zpow_le_norm_of_lt hx) (by norm_num)
  calc 25 * (5 : ℝ) ^ (L : ℤ) = ∑ _a : Fin 5, 5 * (5 : ℝ) ^ (L : ℤ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ _ := Finset.sum_le_sum hterm

/-- Uniform lower bound: every coordinate's shell contribution is at least `4 N 5^L`. -/
theorem S_ge (left right : ε → Fin n) (L : ℕ) (j : Fin n) (β : Fin n → ℚ_[5]) :
    4 * (N left right : ℝ) * (5 : ℝ) ^ (L : ℤ) ≤ S left right L j β := by
  unfold S
  have hN := N_pos left right
  by_cases hbox : ‖β j - c L‖ ≤ (5 : ℝ) ^ ((L : ℤ) - 1)
  · have h := (shellSum_of_box hbox).1
    nlinarith
  · push_neg at hbox
    have h := shellSum_of_not_box hbox
    have h5 := five_zpow_pos (L : ℤ)
    nlinarith

/-- Claim 2, strict form: inside the box coordinate but off the centres, the shell is strictly
larger than `4 N 5^L`. -/
theorem S_gt_of_inBox_not_grid (left right : ε → Fin n) (L : ℕ) (j : Fin n)
    (β : Fin n → ℚ_[5]) (hbox : ‖β j - c L‖ ≤ (5 : ℝ) ^ ((L : ℤ) - 1))
    (hne : ∀ a, β j ≠ t L a) :
    4 * (N left right : ℝ) * (5 : ℝ) ^ (L : ℤ) < S left right L j β := by
  unfold S
  have hN := N_pos left right
  have h := (shellSum_of_box hbox).2 hne
  nlinarith

/-- Claim 3: leaving the box in coordinate `j` costs at least `25 N 5^L` on the shell. -/
theorem S_ge_of_not_inBox (left right : ε → Fin n) (L : ℕ) (j : Fin n)
    (β : Fin n → ℚ_[5]) (hbox : (5 : ℝ) ^ ((L : ℤ) - 1) < ‖β j - c L‖) :
    25 * (N left right : ℝ) * (5 : ℝ) ^ (L : ℤ) ≤ S left right L j β := by
  unfold S
  have hN := N_pos left right
  have h := shellSum_of_not_box hbox
  nlinarith

/-! ### Stage 3: the main theorem -/

/-- The grid `T^n`: every coordinate is one of the five centres. -/
def OnGrid {n : ℕ} (L : ℕ) (β : Fin n → ℚ_[5]) : Prop := ∀ j, ∃ a : Fin 5, β j = t L a

theorem inBox_of_onGrid {L : ℕ} {β : Fin n → ℚ_[5]} (h : OnGrid L β) : InBox L β := by
  intro j
  obtain ⟨a, ha⟩ := h j
  rw [ha]
  exact norm_t_sub_c L a

theorem onGrid_const_c (L : ℕ) : OnGrid L (fun _ : Fin n => c L) :=
  fun _ => ⟨0, (t_zero L).symm⟩

/-- On the grid the loss of `A''_G` is the constant `m_H 5^L + 4 n N 5^L`. -/
theorem loss_A''_of_onGrid (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    {L : ℕ} (hL : 1 ≤ L) {β : Fin n → ℚ_[5]} (hβ : OnGrid L β) :
    loss (A''_G left right L) β =
      (mH left right : ℝ) * (5 : ℝ) ^ (L : ℤ)
        + 4 * n * (N left right : ℝ) * (5 : ℝ) ^ (L : ℤ) := by
  rw [loss_A'', loss_A'_of_inBox left right hne hL (inBox_of_onGrid hβ)]
  congr 1
  have hterms : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      S left right L j β = 4 * (N left right : ℝ) * (5 : ℝ) ^ (L : ℤ) := by
    intro j _
    obtain ⟨a, ha⟩ := hβ j
    exact S_grid left right L j β ha
  rw [Finset.sum_congr rfl hterms, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- Off the grid the loss of `A''_G` is strictly larger than the grid value. -/
theorem loss_A''_gt_of_not_onGrid (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    {L : ℕ} (hL : 1 ≤ L) {β : Fin n → ℚ_[5]} (hβ : ¬ OnGrid L β) :
    (mH left right : ℝ) * (5 : ℝ) ^ (L : ℤ)
        + 4 * n * (N left right : ℝ) * (5 : ℝ) ^ (L : ℤ)
      < loss (A''_G left right L) β := by
  unfold OnGrid at hβ
  push_neg at hβ
  obtain ⟨j₀, hj₀⟩ := hβ
  rw [loss_A'']
  have h5 := five_zpow_pos (L : ℤ)
  by_cases hbox : InBox L β
  · rw [loss_A'_of_inBox left right hne hL hbox]
    have hlt : ∑ _j : Fin n, 4 * (N left right : ℝ) * (5 : ℝ) ^ (L : ℤ)
        < ∑ j, S left right L j β :=
      Finset.sum_lt_sum (fun j _ => S_ge left right L j β)
        ⟨j₀, Finset.mem_univ _, S_gt_of_inBox_not_grid left right L j₀ β (hbox j₀) hj₀⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
    linarith
  · unfold InBox at hbox
    push_neg at hbox
    obtain ⟨j₁, hj₁⟩ := hbox
    have h1 := S_ge_of_not_inBox left right L j₁ β hj₁
    have h2 : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ S left right L j β - 4 * (N left right : ℝ) * (5 : ℝ) ^ (L : ℤ) :=
      fun j _ => sub_nonneg.mpr (S_ge left right L j β)
    have h3 := Finset.single_le_sum h2 (Finset.mem_univ j₁)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h3
    have h4 := loss_nonneg (A'_G left right) β
    have hN : (N left right : ℝ) = mH left right + 1 := by
      simp [N]
    have hmH : (0 : ℝ) ≤ mH left right := Nat.cast_nonneg _
    have hkey : (0 : ℝ) < (20 * (mH left right : ℝ) + 21) * (5 : ℝ) ^ (L : ℤ) := by
      positivity
    rw [hN] at h1 h3 ⊢
    nlinarith

/-- Stage 3, main statement: the global minimisers of `A''_G` are exactly the grid points
`T^n`. -/
theorem stage3_globalMin_iff (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    {L : ℕ} (hL : 1 ≤ L) (β : Fin n → ℚ_[5]) :
    IsGlobalMin (loss (A''_G left right L)) β ↔ ∀ j, ∃ a : Fin 5, β j = t L a := by
  constructor
  · intro h
    by_contra hβ
    have h1 := loss_A''_gt_of_not_onGrid left right hne hL hβ
    have h2 := h (fun _ => c L)
    rw [loss_A''_of_onGrid left right hne hL (onGrid_const_c L)] at h2
    linarith
  · intro hgrid y
    rw [loss_A''_of_onGrid left right hne hL hgrid]
    by_cases hy : OnGrid L y
    · rw [loss_A''_of_onGrid left right hne hL hy]
    · exact (loss_A''_gt_of_not_onGrid left right hne hL hy).le

/-- Stage 3: `β* = (c, …, c)` is a global minimiser of `A''_G`. -/
theorem stage3_optimum (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    {L : ℕ} (hL : 1 ≤ L) :
    IsGlobalMin (loss (A''_G left right L)) (fun _ : Fin n => c L) :=
  (stage3_globalMin_iff left right hne hL _).mpr (onGrid_const_c L)

/-- The optimal value in closed form. -/
theorem loss_A''_optimum (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    {L : ℕ} (hL : 1 ≤ L) :
    loss (A''_G left right L) (fun _ : Fin n => c L) =
      (mH left right : ℝ) * (5 : ℝ) ^ L + 4 * n * (N left right : ℝ) * (5 : ℝ) ^ L := by
  rw [loss_A''_of_onGrid left right hne hL (onGrid_const_c L), zpow_natCast]

/-! ### Headline -/

/-- Thesis Theorem `thm:nested-easy-hard-easy` (bundled).  For every finite (multi)graph
without self-loops and every `L ≥ 1`:
nesting `A_G ≤ A'_G ≤ A''_G`;
Stage 1: `loss A_G β = ∑ j ‖β j‖`, the unique optimum is `β = 0` with loss `0`;
Stage 2: `loss A'_G` is exactly the Max-Cut objective and `|A'_G| = 5|E| + 2|V|`;
Stage 3: `β* = (c, …, c)` is optimal with closed-form loss `m_H 5^L + 4 n N 5^L`, and the
global minimisers are exactly the grid points `T^n`. -/
theorem nested_easy_hard_easy (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e)
    {L : ℕ} (hL : 1 ≤ L) :
    (A_G n ≤ A'_G left right ∧ A'_G left right ≤ A''_G left right L) ∧
    ((∀ β : Fin n → ℚ_[5], loss (A_G n) β = ∑ j, ‖β j‖) ∧
      (∀ β : Fin n → ℚ_[5], IsGlobalMin (loss (A_G n)) β ↔ β = 0) ∧
      loss (A_G n) 0 = 0) ∧
    ((∀ β : Fin n → ℚ_[5], loss (A'_G left right) β =
        ∑ j, (M left right j : ℝ) * (‖β j‖ + ‖β j - 1‖)
          + ∑ e, ‖β (left e) + β (right e) - 1‖) ∧
      Multiset.card (A'_G left right) = 5 * Fintype.card ε + 2 * n) ∧
    (IsGlobalMin (loss (A''_G left right L)) (fun _ : Fin n => c L) ∧
      loss (A''_G left right L) (fun _ : Fin n => c L) =
        (mH left right : ℝ) * (5 : ℝ) ^ L + 4 * n * (N left right : ℝ) * (5 : ℝ) ^ L ∧
      ∀ β : Fin n → ℚ_[5],
        IsGlobalMin (loss (A''_G left right L)) β ↔ ∀ j, ∃ a : Fin 5, β j = t L a) :=
  ⟨⟨A_le_A' left right, A'_le_A'' left right L⟩,
    ⟨loss_A, stage1_globalMin_iff, loss_A_zero⟩,
    ⟨loss_A' left right, card_A' left right hne⟩,
    ⟨stage3_optimum left right hne hL, loss_A''_optimum left right hne hL,
      stage3_globalMin_iff left right hne hL⟩⟩

end Stage3

end PhdThesisLean.NestedEasyHardEasy

#print axioms PhdThesisLean.NestedEasyHardEasy.stage1_globalMin_iff
#print axioms PhdThesisLean.NestedEasyHardEasy.loss_A'
#print axioms PhdThesisLean.NestedEasyHardEasy.card_A'
#print axioms PhdThesisLean.NestedEasyHardEasy.stage3_globalMin_iff
#print axioms PhdThesisLean.NestedEasyHardEasy.stage3_optimum
#print axioms PhdThesisLean.NestedEasyHardEasy.loss_A''_optimum
#print axioms PhdThesisLean.NestedEasyHardEasy.nested_easy_hard_easy
