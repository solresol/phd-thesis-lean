import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace PhdThesisLean.StrictRefinement

open scoped BigOperators

/-!
# Strict refinement prevents coarse-level cancellation

Thesis source: `ecommerce-taxonomy-classification/body.tex` in the thesis
repository (`/Users/gregb/Documents/devel/phd-thesis`), label
`prop:strict-refinement`.

The proposition: for nonzero `c₁, …, c_k ∈ ℚ_p` with strictly increasing
valuations `v_p(c₁) < v_p(c₂) < ⋯ < v_p(c_k)`, every tail sum satisfies
`v_p(c_j + ⋯ + c_k) = v_p(c_j)`; in particular
`v_p(c₁ + ⋯ + c_k) = v_p(c₁)`.  In words: the coarsest active tag cannot be
cancelled by finer ones.

Headline declarations.

* `norm_sum_eq_norm_head`: the norm form.  If `i ↦ ‖c i‖` is strictly
  decreasing on `Fin k`, then `‖∑ i ∈ Finset.Ici j, c i‖ = ‖c j‖` for every `j`.
* `valuation_sum_eq_valuation_head`: the valuation form of the thesis.  If
  every `c i` is nonzero and `i ↦ (c i).valuation` is strictly increasing, then
  `(∑ i ∈ Finset.Ici j, c i).valuation = (c j).valuation` for every `j`.
* `valuation_sum_univ_eq_valuation_head`: the displayed special case
  `v_p(c₁ + ⋯ + c_k) = v_p(c₁)` for `k ≥ 1` (indexing by `Fin (k + 1)`).
* `tailSum_ne_zero`: every tail sum is nonzero (so the valuation statement is
  about genuine, not conventional, valuations).

Correspondence notes.

* The thesis quantifies over `c_i ∈ ℚ_p^×`; here this is the hypothesis
  `∀ i, c i ≠ 0`.  It is needed because Mathlib's `Padic.valuation 0 = 0` is a
  convention, and it is exactly what the thesis assumes.
* The norm form needs no nonvanishing hypothesis at all (a strictly
  decreasing norm sequence can only vanish at the last index, and the
  statement remains true there), so it is slightly stronger.
* The general ultrametric lemma `norm_sum_eq_of_forall_lt` (one term of a
  finite sum strictly dominates all the others, hence determines the norm of
  the sum) is proved for an arbitrary finset and is the only ingredient; the
  `Fin k` tail statements are instances of it.
-/

variable {p : ℕ} [Fact p.Prime]

/-! ### Ultrametric lemmas -/

/-- If `‖b‖ < ‖a‖` then `‖a + b‖ = ‖a‖` (the larger norm dominates). -/
theorem norm_add_eq_left_of_norm_lt {a b : ℚ_[p]} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [Padic.add_eq_max_of_ne h.ne']
  exact max_eq_left h.le

/-- Valuation form of the thesis' basic step: if `v_p(a) < v_p(b)` for nonzero
`a, b`, then `v_p(a + b) = v_p(a)`. -/
theorem norm_lt_norm_of_valuation_lt {a b : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.valuation < b.valuation) : ‖b‖ < ‖a‖ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [Padic.norm_eq_zpow_neg_valuation ha, Padic.norm_eq_zpow_neg_valuation hb,
    zpow_lt_zpow_iff_right₀ hp]
  omega

theorem valuation_eq_of_norm_eq {a b : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ‖a‖ = ‖b‖) : a.valuation = b.valuation := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast (Fact.out : p.Prime).ne_one
  rw [Padic.norm_eq_zpow_neg_valuation ha, Padic.norm_eq_zpow_neg_valuation hb,
    zpow_right_inj₀ hp0 hp1, neg_inj] at h
  exact h

theorem valuation_add_eq_left_of_lt {a b : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.valuation < b.valuation) : (a + b).valuation = a.valuation := by
  have hnorm : ‖a + b‖ = ‖a‖ :=
    norm_add_eq_left_of_norm_lt (norm_lt_norm_of_valuation_lt ha hb h)
  have hne : a + b ≠ 0 := by
    intro h0
    have : ‖a‖ = 0 := by rw [← hnorm, h0, norm_zero]
    exact ha (norm_eq_zero.mp this)
  exact valuation_eq_of_norm_eq hne ha hnorm

/-- A finite sum all of whose terms have norm below a positive bound `B` has
norm below `B` (ultrametric inequality iterated). -/
theorem norm_sum_lt_of_forall_lt {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p]) {B : ℝ}
    (hB : 0 < B) (h : ∀ i ∈ s, ‖f i‖ < B) : ‖∑ i ∈ s, f i‖ < B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (Padic.nonarchimedean _ _).trans_lt (max_lt ?_ ?_)
    · exact h a (Finset.mem_insert_self a s)
    · exact ih fun i hi => h i (Finset.mem_insert_of_mem hi)

/-- If one term `f m` of a finite sum strictly dominates every other term in
norm, then the sum has the norm of that term. -/
theorem norm_sum_eq_of_forall_lt {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (f : ι → ℚ_[p]) {m : ι} (hm : m ∈ s) (h : ∀ i ∈ s, i ≠ m → ‖f i‖ < ‖f m‖) :
    ‖∑ i ∈ s, f i‖ = ‖f m‖ := by
  rw [← Finset.add_sum_erase s f hm]
  by_cases hrest : ∀ i ∈ s.erase m, f i = 0
  · rw [Finset.sum_eq_zero hrest, add_zero]
  · push_neg at hrest
    obtain ⟨i₁, hi₁, hne⟩ := hrest
    have hpos : 0 < ‖f m‖ :=
      lt_of_le_of_lt (norm_nonneg _)
        (h i₁ (Finset.mem_of_mem_erase hi₁) (Finset.ne_of_mem_erase hi₁))
    apply norm_add_eq_left_of_norm_lt
    exact norm_sum_lt_of_forall_lt _ f hpos fun i hi =>
      h i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)

/-! ### Proposition `prop:strict-refinement` -/

/-- Tail sum `c_j + c_{j+1} + ⋯ + c_k`. -/
noncomputable def tailSum {k : ℕ} (c : Fin k → ℚ_[p]) (j : Fin k) : ℚ_[p] :=
  ∑ i ∈ Finset.Ici j, c i

/-- **Proposition `prop:strict-refinement`, norm form**: if the norms
`‖c i‖` are strictly decreasing in `i`, every tail sum has the norm of its
first term. -/
theorem norm_sum_eq_norm_head {k : ℕ} (c : Fin k → ℚ_[p])
    (hc : StrictAnti fun i => ‖c i‖) (j : Fin k) :
    ‖∑ i ∈ Finset.Ici j, c i‖ = ‖c j‖ := by
  apply norm_sum_eq_of_forall_lt c (Finset.mem_Ici.mpr le_rfl)
  intro i hi hij
  have hji : j < i := lt_of_le_of_ne (Finset.mem_Ici.mp hi) (Ne.symm hij)
  exact hc hji

theorem norm_tailSum_eq {k : ℕ} (c : Fin k → ℚ_[p]) (hc : StrictAnti fun i => ‖c i‖)
    (j : Fin k) : ‖tailSum c j‖ = ‖c j‖ :=
  norm_sum_eq_norm_head c hc j

/-- Strictly increasing valuations of nonzero elements give strictly
decreasing norms. -/
theorem strictAnti_norm_of_strictMono_valuation {k : ℕ} (c : Fin k → ℚ_[p])
    (hne : ∀ i, c i ≠ 0) (hv : StrictMono fun i => (c i).valuation) :
    StrictAnti fun i => ‖c i‖ := by
  intro i i' hii'
  exact norm_lt_norm_of_valuation_lt (hne i) (hne i') (hv hii')

/-- Every tail sum of a family with strictly increasing valuations of nonzero
terms is nonzero. -/
theorem tailSum_ne_zero {k : ℕ} (c : Fin k → ℚ_[p]) (hne : ∀ i, c i ≠ 0)
    (hv : StrictMono fun i => (c i).valuation) (j : Fin k) :
    ∑ i ∈ Finset.Ici j, c i ≠ 0 := by
  intro h0
  have h := norm_sum_eq_norm_head c (strictAnti_norm_of_strictMono_valuation c hne hv) j
  rw [h0, norm_zero] at h
  exact hne j (norm_eq_zero.mp h.symm)

/-- **Proposition `prop:strict-refinement`, valuation form**: for nonzero
`c_1, …, c_k` with `v_p(c_1) < ⋯ < v_p(c_k)`, every tail sum satisfies
`v_p(c_j + ⋯ + c_k) = v_p(c_j)`. -/
theorem valuation_sum_eq_valuation_head {k : ℕ} (c : Fin k → ℚ_[p])
    (hne : ∀ i, c i ≠ 0) (hv : StrictMono fun i => (c i).valuation) (j : Fin k) :
    (∑ i ∈ Finset.Ici j, c i).valuation = (c j).valuation :=
  valuation_eq_of_norm_eq (tailSum_ne_zero c hne hv j) (hne j)
    (norm_sum_eq_norm_head c (strictAnti_norm_of_strictMono_valuation c hne hv) j)

theorem Ici_zero_eq_univ (k : ℕ) : Finset.Ici (0 : Fin (k + 1)) = Finset.univ := by
  ext i
  simp [Finset.mem_Ici, Fin.zero_le]

/-- The displayed special case `v_p(c_1 + ⋯ + c_k) = v_p(c_1)` (with `k ≥ 1`
written as `Fin (k + 1)`). -/
theorem valuation_sum_univ_eq_valuation_head {k : ℕ} (c : Fin (k + 1) → ℚ_[p])
    (hne : ∀ i, c i ≠ 0) (hv : StrictMono fun i => (c i).valuation) :
    (∑ i, c i).valuation = (c 0).valuation := by
  rw [← Ici_zero_eq_univ k]
  exact valuation_sum_eq_valuation_head c hne hv 0

/-- Norm version of the displayed special case. -/
theorem norm_sum_univ_eq_norm_head {k : ℕ} (c : Fin (k + 1) → ℚ_[p])
    (hc : StrictAnti fun i => ‖c i‖) : ‖∑ i, c i‖ = ‖c 0‖ := by
  rw [← Ici_zero_eq_univ k]
  exact norm_sum_eq_norm_head c hc 0

#print axioms norm_sum_eq_of_forall_lt
#print axioms norm_sum_eq_norm_head
#print axioms valuation_sum_eq_valuation_head
#print axioms valuation_sum_univ_eq_valuation_head
#print axioms tailSum_ne_zero

end PhdThesisLean.StrictRefinement
