import Mathlib

namespace PhdThesisLean.SudokuDiagnostics

open scoped BigOperators
open Polynomial

/-!
# Constraint-locator fingerprints and robust sublevel decoding

This module formalises two propositions from
`sudoku-via-padic-regression/body.tex`:

* `prop:sudoku-locator-fingerprint` (subsection
  `subsec:sudoku-future-locator`, "Random fingerprint of a committed
  locator"), together with the displayed algebraic facts about the
  constraint-locator polynomial `Λ_x(Z) = ∏_{c : v_c(x) = 1} (Z − α_c)`:
  it is monic, its degree is the number of violated constraints, it equals
  `1` exactly when every constraint is satisfied, its roots are exactly the
  addresses of the violated constraints, and it can be evaluated by streaming
  over the constraints.
* `prop:sudoku-robust-decoding` (subsection
  `subsec:sudoku-future-robustness`, "Robust sublevel decoding") under the
  robust-soundness hypothesis `L_Φ(x) ≥ γ · d_H(x, 𝒮)`
  (`eq:sudoku-robust-soundness`).

## Correspondence notes

### Locator fingerprint

* The thesis works over `𝔽_Q`; here `F` is an arbitrary finite field.  The
  constraint index `κ` is an arbitrary finite type (the thesis's clauses), the
  addresses are `α : κ → F`, and the violation indicator `v : κ → Bool` plays
  the role of `c ↦ v_c(x)`; the assignment `x` itself is irrelevant to the
  algebra, so the indicator is taken as the datum (instantiate
  `v := fun c => v_c x`).  Distinctness of the addresses is *not* needed for
  any statement here (the fingerprint bound is purely about polynomial
  degrees, and `roots_locator` lists the violated addresses as a multiset).
* The thesis asks the claimant to commit to a *monic* polynomial of degree at
  most `D`.  Monicity is never used, so `locator_fingerprint` drops it: the
  bound holds for any committed `Λ' ≠ Λ_x` with `natDegree Λ' ≤ D`.  The
  thesis's proof also uses (implicitly) that `deg Λ_x ≤ D`; this is recorded
  as the explicit hypothesis `(locator α v).natDegree ≤ D`.  Since the
  locator's degree is at most the number of constraints,
  `locator_fingerprint_card_constraints` gives the hypothesis-free form with
  `D := Fintype.card κ`.
* "`τ` sampled uniformly from `𝔽_Q`" is read as: the probability of an event
  `P τ` is `#{τ | P τ} / Q`.  `card_eval_eq_le_natDegree` is the counting
  statement (`#{τ | Λ'(τ) = Λ_x(τ)} ≤ D`, the univariate Schwartz–Zippel /
  DeMillo–Lipton bound the thesis cites) and `locator_fingerprint_prob`
  divides through by `Q = Fintype.card F` in an arbitrary ordered field
  (so both `ℚ` and `ℝ` readings are instances).

### Robust sublevel decoding

* Assignments are `ι → A` for an arbitrary finite index type `ι` and an
  arbitrary alphabet `A` with decidable equality (the thesis uses Boolean
  assignments on `n` variables); Hamming distance is Mathlib's `hammingDist`.
* The solution set `𝒮` is a finite set `S` with `hS : S.Nonempty`;
  `distToSet S hS x` is `d_H(x, 𝒮) = min_{s ∈ S} d_H(x, s)` and
  `IsNearest S hS x s` says `s ∈ S` attains it.
* The thesis's minimum distance `d_min` is formalised in two layers.  The
  main theorems `unique_nearest` and `separation` take any `d : ℕ` with
  `IsPairwiseLowerBound S d` (every two distinct solutions are at Hamming
  distance `≥ d`); this is at least as strong as using `d_min` itself.  For
  `2 ≤ S.card` the actual minimum `dmin S h2` is defined and
  `unique_nearest_dmin` / `separation_dmin` specialise to it, which is the
  thesis statement verbatim.  (When `S.card ≤ 1` the thesis's `d_min` is
  undefined; the general theorems then hold vacuously for every `d`.)
* `0 < γ` is an explicit hypothesis.  The thesis treats `γ` as a positive
  robustness constant without saying so; for `γ ≤ 0` the proposition is
  false, so this hypothesis is genuinely needed, not an extra assumption.
* `separation` is stated *without* the thesis's side condition
  `ℓ < γ d_min / 2`: the inequality `d_H(x, y) ≥ d_min − 2ℓ/γ` only needs
  `L(x), L(y) ≤ ℓ` and the two (nearest) solutions to differ.  The thesis's
  version is the special case.
-/

/-! ## Part (a): the constraint-locator polynomial and its fingerprint -/

section Locator

variable {F : Type*} [Field F]
variable {κ : Type*} [Fintype κ]

/-- The violated constraints `V(x) = {c : v_c(x) = 1}`, with the violation
indicator `v` standing for `c ↦ v_c(x)`. -/
def violated (v : κ → Bool) : Finset κ :=
  Finset.univ.filter fun c => v c = true

theorem mem_violated {v : κ → Bool} {c : κ} : c ∈ violated v ↔ v c = true := by
  simp [violated]

/-- The constraint-locator polynomial `Λ_x(Z) = ∏_{c : v_c(x) = 1} (Z − α_c)`
(`eq:sudoku-future-locator`, in its simplified discrete form). -/
noncomputable def locator (α : κ → F) (v : κ → Bool) : F[X] :=
  ∏ c ∈ violated v, (X - C (α c))

/-- The locator is monic. -/
theorem locator_monic (α : κ → F) (v : κ → Bool) : (locator α v).Monic :=
  monic_prod_of_monic _ _ fun c _ => monic_X_sub_C (α c)

theorem locator_ne_zero (α : κ → F) (v : κ → Bool) : locator α v ≠ 0 :=
  (locator_monic α v).ne_zero

/-- `deg Λ_x = #{c : v_c(x) = 1}`: the degree counts the violated
constraints. -/
theorem natDegree_locator (α : κ → F) (v : κ → Bool) :
    (locator α v).natDegree = (violated v).card :=
  natDegree_finset_prod_X_sub_C_eq_card _ _

/-- The locator's degree is at most the number of constraints. -/
theorem natDegree_locator_le_card (α : κ → F) (v : κ → Bool) :
    (locator α v).natDegree ≤ Fintype.card κ := by
  rw [natDegree_locator]
  exact Finset.card_le_univ _

/-- `Λ_x = 1` exactly when `x` satisfies every constraint. -/
theorem locator_eq_one_iff (α : κ → F) (v : κ → Bool) :
    locator α v = 1 ↔ ∀ c, v c = false := by
  constructor
  · intro h c
    have hdeg := natDegree_locator α v
    rw [h, natDegree_one] at hdeg
    by_contra hc
    have hc' : c ∈ violated v := mem_violated.mpr (by simpa using hc)
    have hpos := Finset.card_pos.mpr ⟨c, hc'⟩
    omega
  · intro h
    have hempty : violated v = ∅ := by
      ext c
      simp [mem_violated, h c]
    rw [locator, hempty, Finset.prod_empty]

/-- Streamed evaluation: `Λ_x(τ) = ∏_{c : v_c(x) = 1} (τ − α_c)`, computable in
one pass over the constraints with constant extra memory. -/
theorem locator_eval (α : κ → F) (v : κ → Bool) (τ : F) :
    (locator α v).eval τ = ∏ c ∈ violated v, (τ - α c) := by
  simp [locator, eval_prod]

/-- The roots of the locator, as a multiset, are the addresses of the violated
constraints (so when the addresses are distinct, the root *set* is exactly
`{α_c : v_c(x) = 1}` and the roots identify the failed constraints). -/
theorem roots_locator (α : κ → F) (v : κ → Bool) :
    (locator α v).roots = (violated v).val.map α := by
  have hmap : (violated v).val.map (fun c => X - C (α c)) =
      ((violated v).val.map α).map (fun a : F => X - C a) := by
    rw [Multiset.map_map]
    rfl
  rw [locator, Finset.prod_eq_multiset_prod, hmap, roots_multiset_prod_X_sub_C]

/-- `Λ_x(τ) = 0` iff `τ` is the address of some violated constraint. -/
theorem eval_locator_eq_zero_iff (α : κ → F) (v : κ → Bool) (τ : F) :
    (locator α v).eval τ = 0 ↔ ∃ c, v c = true ∧ α c = τ := by
  rw [locator_eval, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨c, hc, hτ⟩
    exact ⟨c, mem_violated.mp hc, (sub_eq_zero.mp hτ).symm⟩
  · rintro ⟨c, hc, hτ⟩
    exact ⟨c, mem_violated.mpr hc, sub_eq_zero.mpr hτ.symm⟩

end Locator

section Fingerprint

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Univariate Schwartz–Zippel / DeMillo–Lipton: two distinct polynomials of
degree at most `D` over a finite field agree at no more than `D` points. -/
theorem card_eval_eq_le_natDegree {D : ℕ} (f g : F[X]) (hne : f ≠ g)
    (hf : f.natDegree ≤ D) (hg : g.natDegree ≤ D) :
    (Finset.univ.filter fun τ : F => f.eval τ = g.eval τ).card ≤ D := by
  have hsub : f - g ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (f - g).natDegree ≤ D := by
    simpa using natDegree_sub_le_of_le hf hg
  refine le_trans (card_le_degree_of_subset_roots (p := f - g) ?_) hdeg
  intro τ hτ
  rw [Finset.mem_val, Finset.mem_filter] at hτ
  rw [mem_roots hsub, IsRoot.def, eval_sub, hτ.2, sub_self]

variable {κ : Type*} [Fintype κ]

/-- `prop:sudoku-locator-fingerprint`, counting form.  If a claimant commits to
`Λ' ≠ Λ_x` of degree at most `D` (and the honest locator also has degree at
most `D`), then at most `D` challenges `τ ∈ F` satisfy `Λ'(τ) = Λ_x(τ)`.
Monicity of `Λ'` is not needed. -/
theorem locator_fingerprint {D : ℕ} (α : κ → F) (v : κ → Bool) (Λ' : F[X])
    (hne : Λ' ≠ locator α v) (hD : Λ'.natDegree ≤ D)
    (hD' : (locator α v).natDegree ≤ D) :
    (Finset.univ.filter fun τ : F => Λ'.eval τ = (locator α v).eval τ).card ≤ D :=
  card_eval_eq_le_natDegree Λ' (locator α v) hne hD hD'

/-- `prop:sudoku-locator-fingerprint` with `D` the number of constraints: the
honest locator automatically has degree at most `Fintype.card κ`. -/
theorem locator_fingerprint_card_constraints (α : κ → F) (v : κ → Bool) (Λ' : F[X])
    (hne : Λ' ≠ locator α v) (hD : Λ'.natDegree ≤ Fintype.card κ) :
    (Finset.univ.filter fun τ : F => Λ'.eval τ = (locator α v).eval τ).card ≤
      Fintype.card κ :=
  locator_fingerprint α v Λ' hne hD (natDegree_locator_le_card α v)

/-- `prop:sudoku-locator-fingerprint`, probability form.  Reading
`Pr[Λ'(τ) = Λ_x(τ)]` for `τ` uniform on `F` as `#{τ | Λ'(τ) = Λ_x(τ)} / Q` with
`Q = Fintype.card F`, the collision probability is at most `D / Q`.  Stated in
an arbitrary ordered field `K` (`ℚ` or `ℝ`). -/
theorem locator_fingerprint_prob {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {D : ℕ} (α : κ → F) (v : κ → Bool) (Λ' : F[X])
    (hne : Λ' ≠ locator α v) (hD : Λ'.natDegree ≤ D)
    (hD' : (locator α v).natDegree ≤ D) :
    ((Finset.univ.filter fun τ : F => Λ'.eval τ = (locator α v).eval τ).card : K) /
        Fintype.card F ≤ (D : K) / Fintype.card F := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast locator_fingerprint α v Λ' hne hD hD'

end Fingerprint

/-! ## Part (b): robust sublevel decoding -/

section RobustDecoding

variable {ι : Type*} [Fintype ι] {A : Type*} [DecidableEq A]

/-- `d_H(x, 𝒮) = min_{s ∈ 𝒮} d_H(x, s)` for a nonempty finite solution set. -/
noncomputable def distToSet (S : Finset (ι → A)) (hS : S.Nonempty) (x : ι → A) : ℕ :=
  S.inf' hS fun s => hammingDist x s

/-- `s` is a nearest solution to `x`: it lies in `𝒮` and attains `d_H(x, 𝒮)`. -/
def IsNearest (S : Finset (ι → A)) (hS : S.Nonempty) (x s : ι → A) : Prop :=
  s ∈ S ∧ hammingDist x s = distToSet S hS x

theorem distToSet_le {S : Finset (ι → A)} (hS : S.Nonempty) {x s : ι → A} (hs : s ∈ S) :
    distToSet S hS x ≤ hammingDist x s :=
  Finset.inf'_le _ hs

theorem exists_isNearest {S : Finset (ι → A)} (hS : S.Nonempty) (x : ι → A) :
    ∃ s, IsNearest S hS x s := by
  obtain ⟨s, hs, hsd⟩ := Finset.exists_mem_eq_inf' hS fun s => hammingDist x s
  exact ⟨s, hs, hsd.symm⟩

theorem isNearest_iff {S : Finset (ι → A)} (hS : S.Nonempty) {x s : ι → A} :
    IsNearest S hS x s ↔ s ∈ S ∧ ∀ t ∈ S, hammingDist x s ≤ hammingDist x t := by
  constructor
  · rintro ⟨hs, hsd⟩
    refine ⟨hs, fun t ht => ?_⟩
    rw [hsd]
    exact distToSet_le hS ht
  · rintro ⟨hs, hmin⟩
    refine ⟨hs, le_antisymm ?_ (distToSet_le hS hs)⟩
    exact (Finset.le_inf'_iff hS _).mpr hmin

theorem distToSet_eq_zero_iff {S : Finset (ι → A)} (hS : S.Nonempty) {x : ι → A} :
    distToSet S hS x = 0 ↔ x ∈ S := by
  constructor
  · intro h
    obtain ⟨s, hs, hsd⟩ := exists_isNearest hS x
    rw [h, hammingDist_eq_zero] at hsd
    exact hsd ▸ hs
  · intro hx
    have h := distToSet_le hS (x := x) hx
    rw [hammingDist_self] at h
    omega

theorem distToSet_eq_zero_of_mem {S : Finset (ι → A)} (hS : S.Nonempty) {x : ι → A}
    (hx : x ∈ S) : distToSet S hS x = 0 :=
  (distToSet_eq_zero_iff hS).mpr hx

/-- `d` is a lower bound on the Hamming distance between any two distinct
solutions (so `d ≤ d_min`, and `d_min` itself satisfies this). -/
def IsPairwiseLowerBound (S : Finset (ι → A)) (d : ℕ) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, s ≠ t → d ≤ hammingDist s t

theorem offDiag_nonempty_of_two_le_card {S : Finset (ι → A)} (h2 : 2 ≤ S.card) :
    S.offDiag.Nonempty := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
  exact ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩⟩

/-- The minimum distance `d_min = min_{s ≠ t ∈ 𝒮} d_H(s, t)` of a solution set
with at least two elements. -/
noncomputable def dmin (S : Finset (ι → A)) (h2 : 2 ≤ S.card) : ℕ :=
  S.offDiag.inf' (offDiag_nonempty_of_two_le_card h2) fun st => hammingDist st.1 st.2

theorem dmin_le {S : Finset (ι → A)} (h2 : 2 ≤ S.card) {s t : ι → A}
    (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t) : dmin S h2 ≤ hammingDist s t := by
  unfold dmin
  exact Finset.inf'_le (b := (s, t)) (fun st : (ι → A) × (ι → A) => hammingDist st.1 st.2)
    (Finset.mem_offDiag.mpr ⟨hs, ht, hst⟩)

theorem dmin_isPairwiseLowerBound {S : Finset (ι → A)} (h2 : 2 ≤ S.card) :
    IsPairwiseLowerBound S (dmin S h2) :=
  fun _ hs _ ht hst => dmin_le h2 hs ht hst

theorem exists_dmin_eq {S : Finset (ι → A)} (h2 : 2 ≤ S.card) :
    ∃ s ∈ S, ∃ t ∈ S, s ≠ t ∧ hammingDist s t = dmin S h2 := by
  obtain ⟨⟨s, t⟩, hst, heq⟩ := Finset.exists_mem_eq_inf'
    (offDiag_nonempty_of_two_le_card h2)
    (fun st : (ι → A) × (ι → A) => hammingDist st.1 st.2)
  obtain ⟨hs, ht, hne⟩ := Finset.mem_offDiag.mp hst
  exact ⟨s, hs, t, ht, hne, heq.symm⟩

theorem dmin_pos {S : Finset (ι → A)} (h2 : 2 ≤ S.card) : 0 < dmin S h2 := by
  obtain ⟨s, _, t, _, hne, heq⟩ := exists_dmin_eq h2
  rw [← heq]
  exact hammingDist_pos.mpr hne

/-- Robust soundness `eq:sudoku-robust-soundness`: `L(x) ≥ γ · d_H(x, 𝒮)` for
every assignment. -/
def RobustlySound (S : Finset (ι → A)) (hS : S.Nonempty) (L : (ι → A) → ℝ) (γ : ℝ) :
    Prop :=
  ∀ x, γ * distToSet S hS x ≤ L x

/-- Under robust soundness, `L(x) < γ d / 2` forces `d_H(x, 𝒮) < d / 2`. -/
theorem distToSet_lt_half {S : Finset (ι → A)} {hS : S.Nonempty} {L : (ι → A) → ℝ}
    {γ : ℝ} (hγ : 0 < γ) (hrobust : RobustlySound S hS L γ) {d : ℕ} {x : ι → A}
    (hx : L x < γ * d / 2) : 2 * distToSet S hS x < d := by
  have h1 : γ * (distToSet S hS x : ℝ) < γ * (d / 2) := by
    have := hrobust x
    linarith
  have h2 : (distToSet S hS x : ℝ) < d / 2 := lt_of_mul_lt_mul_left h1 hγ.le
  have h3 : ((2 * distToSet S hS x : ℕ) : ℝ) < d := by
    push_cast
    linarith
  exact_mod_cast h3

/-- `prop:sudoku-robust-decoding`, first part, for any pairwise lower bound
`d` on the solution set: if `L(x) < γ d / 2` then `x` has a unique nearest
solution. -/
theorem unique_nearest {S : Finset (ι → A)} (hS : S.Nonempty) {d : ℕ}
    (hd : IsPairwiseLowerBound S d) {L : (ι → A) → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hrobust : RobustlySound S hS L γ) {x : ι → A} (hx : L x < γ * d / 2) :
    ∃! s, IsNearest S hS x s := by
  obtain ⟨s, hs, hsd⟩ := exists_isNearest hS x
  refine ⟨s, ⟨hs, hsd⟩, ?_⟩
  rintro t ⟨ht, htd⟩
  by_contra hts
  have hlt := distToSet_lt_half hγ hrobust hx
  have hdst := hd s hs t ht (Ne.symm hts)
  have htri := hammingDist_triangle s x t
  have hcomm := hammingDist_comm s x
  omega

/-- `prop:sudoku-robust-decoding`, second part, for any pairwise lower bound
`d`: if `L(x), L(y) ≤ ℓ` and the nearest solutions `s` of `x` and `t` of `y`
differ, then `d_H(x, y) ≥ d − 2ℓ/γ`.  (The thesis's extra side condition
`ℓ < γ d / 2` is not needed.) -/
theorem separation {S : Finset (ι → A)} (hS : S.Nonempty) {d : ℕ}
    (hd : IsPairwiseLowerBound S d) {L : (ι → A) → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hrobust : RobustlySound S hS L γ) {x y : ι → A} {ℓ : ℝ}
    (hx : L x ≤ ℓ) (hy : L y ≤ ℓ) {s t : ι → A}
    (hs : IsNearest S hS x s) (ht : IsNearest S hS y t) (hst : s ≠ t) :
    (d : ℝ) - 2 * ℓ / γ ≤ hammingDist x y := by
  obtain ⟨hsS, hsd⟩ := hs
  obtain ⟨htS, htd⟩ := ht
  have hxs : γ * (hammingDist x s : ℝ) ≤ ℓ := by
    have := hrobust x
    rw [← hsd] at this
    linarith
  have hyt : γ * (hammingDist y t : ℝ) ≤ ℓ := by
    have := hrobust y
    rw [← htd] at this
    linarith
  have hdst : d ≤ hammingDist s t := hd s hsS t htS hst
  have htri : hammingDist s t ≤ hammingDist s x + hammingDist x y + hammingDist y t := by
    calc hammingDist s t ≤ hammingDist s y + hammingDist y t := hammingDist_triangle s y t
      _ ≤ hammingDist s x + hammingDist x y + hammingDist y t := by
        have := hammingDist_triangle s x y
        omega
  have hcomm : hammingDist s x = hammingDist x s := hammingDist_comm s x
  have hreal : (d : ℝ) ≤ hammingDist x s + hammingDist x y + hammingDist y t := by
    have h : d ≤ hammingDist x s + hammingDist x y + hammingDist y t := by omega
    exact_mod_cast h
  have hsum : (hammingDist x s : ℝ) + hammingDist y t ≤ 2 * ℓ / γ := by
    rw [le_div_iff₀ hγ]
    nlinarith
  linarith

/-- `prop:sudoku-robust-decoding`, first part, verbatim with `d_min`: every
assignment with `L(x) < γ d_min / 2` has a unique nearest solution. -/
theorem unique_nearest_dmin {S : Finset (ι → A)} (hS : S.Nonempty) (h2 : 2 ≤ S.card)
    {L : (ι → A) → ℝ} {γ : ℝ} (hγ : 0 < γ) (hrobust : RobustlySound S hS L γ)
    {x : ι → A} (hx : L x < γ * dmin S h2 / 2) :
    ∃! s, IsNearest S hS x s :=
  unique_nearest hS (dmin_isPairwiseLowerBound h2) hγ hrobust hx

/-- `prop:sudoku-robust-decoding`, second part, verbatim with `d_min`: if
`L(x), L(y) ≤ ℓ < γ d_min / 2` and the nearest solutions of `x` and `y` differ,
then `d_H(x, y) ≥ d_min − 2ℓ/γ`. -/
theorem separation_dmin {S : Finset (ι → A)} (hS : S.Nonempty) (h2 : 2 ≤ S.card)
    {L : (ι → A) → ℝ} {γ : ℝ} (hγ : 0 < γ) (hrobust : RobustlySound S hS L γ)
    {x y : ι → A} {ℓ : ℝ} (hx : L x ≤ ℓ) (hy : L y ≤ ℓ) (_hℓ : ℓ < γ * dmin S h2 / 2)
    {s t : ι → A} (hs : IsNearest S hS x s) (ht : IsNearest S hS y t) (hst : s ≠ t) :
    (dmin S h2 : ℝ) - 2 * ℓ / γ ≤ hammingDist x y :=
  separation hS (dmin_isPairwiseLowerBound h2) hγ hrobust hx hy hs ht hst

end RobustDecoding

end PhdThesisLean.SudokuDiagnostics

#print axioms PhdThesisLean.SudokuDiagnostics.locator_monic
#print axioms PhdThesisLean.SudokuDiagnostics.natDegree_locator
#print axioms PhdThesisLean.SudokuDiagnostics.locator_eq_one_iff
#print axioms PhdThesisLean.SudokuDiagnostics.locator_eval
#print axioms PhdThesisLean.SudokuDiagnostics.roots_locator
#print axioms PhdThesisLean.SudokuDiagnostics.eval_locator_eq_zero_iff
#print axioms PhdThesisLean.SudokuDiagnostics.card_eval_eq_le_natDegree
#print axioms PhdThesisLean.SudokuDiagnostics.locator_fingerprint
#print axioms PhdThesisLean.SudokuDiagnostics.locator_fingerprint_card_constraints
#print axioms PhdThesisLean.SudokuDiagnostics.locator_fingerprint_prob
#print axioms PhdThesisLean.SudokuDiagnostics.distToSet_eq_zero_iff
#print axioms PhdThesisLean.SudokuDiagnostics.unique_nearest
#print axioms PhdThesisLean.SudokuDiagnostics.separation
#print axioms PhdThesisLean.SudokuDiagnostics.unique_nearest_dmin
#print axioms PhdThesisLean.SudokuDiagnostics.separation_dmin
