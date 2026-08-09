/-
  Formalisation of the precision-indexed prediction growth results from
  Greg Baker's PhD thesis.

  Thesis source: pac-learning-open-questions/body.tex, Section
  `sec:precision-indexed-growth` in the active thesis checkout (post-snapshot
  formalisation queue; see THEOREM_STATUS.md).

  Thesis labels: def:precision-indexed-growth, prop:precision-growth-covering,
  prop:precision-growth-vc, thm:affine-precision-growth,
  prop:tree-syntax-growth-bound, cor:binary-tree-precision-growth.
-/

import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.MetricSpace.Pseudo.Pi

namespace PhdThesisLean.PrecisionGrowth

open scoped BigOperators

/-! ### The finite-precision prediction-pattern interface

`patternSet H ρ S` is the set of reduced prediction patterns realised by the
hypothesis class `H` on the ordered sample `S`, where `ρ` is the reduction
from raw outputs to finite-precision outputs.  `patternCount` is the thesis
quantity `N_{\mathcal H}(S, k)` and `growth` is the precision-indexed growth
function `Π_{\mathcal H}^{(p)}(m, k)`, both stated for an arbitrary reduction
so that the `p`-adic, residue-ring, and already-reduced instances share one
interface. -/

/-- The set of reduced prediction patterns realised by `H` on the ordered
sample `S`. -/
def patternSet {X Ω Ω' : Type*} {m : ℕ} (H : Set (X → Ω)) (ρ : Ω → Ω')
    (S : Fin m → X) : Set (Fin m → Ω') :=
  (fun h => fun i => ρ (h (S i))) '' H

/-- `N_{\mathcal H}(S, k)`: the number of realised reduced patterns. -/
noncomputable def patternCount {X Ω Ω' : Type*} {m : ℕ} (H : Set (X → Ω))
    (ρ : Ω → Ω') (S : Fin m → X) : ℕ :=
  (patternSet H ρ S).ncard

/-- The precision-indexed growth function `Π_{\mathcal H}^{(p)}(m, k)`,
stated as the supremum of the realised pattern counts over ordered
`m`-samples. -/
noncomputable def growth {X Ω Ω' : Type*} (H : Set (X → Ω)) (ρ : Ω → Ω')
    (m : ℕ) : ℕ :=
  sSup {n | ∃ S : Fin m → X, patternCount H ρ S = n}

theorem mem_patternSet {X Ω Ω' : Type*} {m : ℕ} {H : Set (X → Ω)} {ρ : Ω → Ω'}
    {S : Fin m → X} {h : X → Ω} (hh : h ∈ H) :
    (fun i => ρ (h (S i))) ∈ patternSet H ρ S :=
  ⟨h, hh, rfl⟩

/-- Every pattern count is bounded by the number of all reduced labellings of
the sample.  This is the upper half of the thesis display
`0 ≤ E_{\mathcal H}^{(p)}(m, k) ≤ km`. -/
theorem patternCount_le_card {X Ω Ω' : Type*} [Fintype Ω'] {m : ℕ}
    (H : Set (X → Ω)) (ρ : Ω → Ω') (S : Fin m → X) :
    patternCount H ρ S ≤ Fintype.card Ω' ^ m := by
  classical
  have h := Set.ncard_le_ncard (Set.subset_univ (patternSet H ρ S))
    Set.finite_univ
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin] at h

/-- A nonempty class realises at least one pattern. -/
theorem one_le_patternCount {X Ω Ω' : Type*} [Finite Ω'] {m : ℕ}
    {H : Set (X → Ω)} (hH : H.Nonempty) (ρ : Ω → Ω') (S : Fin m → X) :
    1 ≤ patternCount H ρ S := by
  obtain ⟨h, hh⟩ := hH
  have hne : (patternSet H ρ S).Nonempty := ⟨_, mem_patternSet hh⟩
  exact (Set.ncard_pos (Set.toFinite _)).mpr hne

theorem growth_le {X Ω Ω' : Type*} {H : Set (X → Ω)} {ρ : Ω → Ω'} {m B : ℕ}
    (hub : ∀ S : Fin m → X, patternCount H ρ S ≤ B) :
    growth H ρ m ≤ B := by
  refine csSup_le' ?_
  rintro n ⟨S, rfl⟩
  exact hub S

theorem le_growth {X Ω Ω' : Type*} {H : Set (X → Ω)} {ρ : Ω → Ω'} {m B : ℕ}
    (hub : ∀ S : Fin m → X, patternCount H ρ S ≤ B) (S : Fin m → X) :
    patternCount H ρ S ≤ growth H ρ m := by
  refine le_csSup ⟨B, ?_⟩ ⟨S, rfl⟩
  rintro n ⟨S', rfl⟩
  exact hub S'

/-- The growth function is computed by a uniform upper bound that is attained
by some sample. -/
theorem growth_eq_of_bounds {X Ω Ω' : Type*} {H : Set (X → Ω)} {ρ : Ω → Ω'}
    {m B : ℕ} (hub : ∀ S : Fin m → X, patternCount H ρ S ≤ B)
    (hex : ∃ S : Fin m → X, patternCount H ρ S = B) :
    growth H ρ m = B := by
  obtain ⟨S, hS⟩ := hex
  exact le_antisymm (growth_le hub) (hS ▸ le_growth hub S)

/-! ### Affine residue models: `thm:affine-precision-growth`

The class `𝒜_{d,K}` of affine maps on `(ZMod (p ^ K))^d` with coefficients in
`ZMod (p ^ K)`, reduced from precision `K` to precision `k ≤ K`.  The maximal
reduced pattern count on an `m`-sample is exactly `p ^ (k * min m (d + 1))`,
witnessed by the sample `0, e_1, …, e_{r-1}` padded by zeros. -/

/-- The affine residue class `𝒜_{d,K}` on `X = (ZMod (p ^ K))^d`, with the
intercept in coordinate zero. -/
def affineClass (p K d : ℕ) : Set ((Fin d → ZMod (p ^ K)) → ZMod (p ^ K)) :=
  {f | ∃ a : Fin (d + 1) → ZMod (p ^ K),
    f = fun x => a 0 + ∑ j : Fin d, a j.succ * x j}

/-- Reduction from precision `K` to precision `k ≤ K`, as a ring
homomorphism. -/
def reduceHom (p : ℕ) {k K : ℕ} (hk : k ≤ K) :
    ZMod (p ^ K) →+* ZMod (p ^ k) :=
  ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k))

/-- The thesis sample `0, e_1, …, e_{r-1}` (padded by zero vectors): sample
point `i` is the `(i-1)`-st standard basis vector for `1 ≤ i ≤ d` and the
zero vector otherwise. -/
def basisSample (p K d m : ℕ) : Fin m → Fin d → ZMod (p ^ K) :=
  fun i j => if (j : ℕ) + 1 = (i : ℕ) then 1 else 0

/-- The reduced pattern prescribing arbitrary targets `y` on the first `r`
sample positions and repeating the first target elsewhere. -/
def padPattern {O : Type*} {m r : ℕ} (hr : 0 < r) (y : Fin r → O) :
    Fin m → O :=
  fun i => if hi : (i : ℕ) < r then y ⟨i, hi⟩ else y ⟨0, hr⟩

/-- The interpolating coefficients `a_0 = y_1`, `a_j = y_{j+1} - y_1`, lifted
from precision `k` back to precision `K` via `ZMod.val`. -/
def interpCoeff (p : ℕ) {k : ℕ} (K d : ℕ) {r : ℕ} (hr : 0 < r)
    (y : Fin r → ZMod (p ^ k)) : Fin (d + 1) → ZMod (p ^ K) :=
  fun t =>
    if (t : ℕ) = 0 then (((y ⟨0, hr⟩).val : ℕ) : ZMod (p ^ K))
    else if ht : (t : ℕ) < r then
      (((y ⟨t, ht⟩ - y ⟨0, hr⟩).val : ℕ) : ZMod (p ^ K))
    else 0

/-- Upper half of `thm:affine-precision-growth`: after reduction modulo
`p ^ k` every pattern is determined by the reduced coefficient vector, so no
sample realises more than `p ^ (k * min m (d + 1))` patterns. -/
theorem affine_patternCount_le {p : ℕ} [hp : Fact p.Prime] {K k d m : ℕ}
    (hk : k ≤ K) (S : Fin m → Fin d → ZMod (p ^ K)) :
    patternCount (affineClass p K d) (⇑(reduceHom p hk)) S
      ≤ p ^ (k * min m (d + 1)) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩
  rcases le_total m (d + 1) with hmd | hmd
  · calc patternCount (affineClass p K d) (⇑(reduceHom p hk)) S
        ≤ Fintype.card (ZMod (p ^ k)) ^ m := patternCount_le_card _ _ _
      _ = p ^ (k * m) := by rw [ZMod.card, ← pow_mul]
      _ = p ^ (k * min m (d + 1)) := by rw [min_eq_left hmd]
  · rw [min_eq_right hmd]
    have hsub : patternSet (affineClass p K d) (⇑(reduceHom p hk)) S ⊆
        Set.range (fun b : Fin (d + 1) → ZMod (p ^ k) =>
          fun i => b 0 + ∑ j : Fin d, b j.succ * reduceHom p hk (S i j)) := by
      rintro g ⟨h, ⟨a, rfl⟩, rfl⟩
      refine ⟨fun t => reduceHom p hk (a t), ?_⟩
      funext i
      simp [map_add, map_sum, map_mul]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hrange :
        (Set.range (fun b : Fin (d + 1) → ZMod (p ^ k) =>
          fun i => b 0 + ∑ j : Fin d, b j.succ * reduceHom p hk (S i j))).ncard
          ≤ Nat.card (Fin (d + 1) → ZMod (p ^ k)) := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (Set.ncard_univ _).le
    have hcard : Nat.card (Fin (d + 1) → ZMod (p ^ k)) = p ^ (k * (d + 1)) := by
      classical
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
        Fintype.card_fin, ← pow_mul]
    exact hle.trans (hrange.trans hcard.le)

/-- On the thesis sample, the affine model with the interpolating
coefficients realises exactly the padded target pattern. -/
theorem pattern_interpCoeff {p : ℕ} [hp : Fact p.Prime] {K k d m : ℕ}
    (hk : k ≤ K) (hm : 0 < m)
    (y : Fin (min m (d + 1)) → ZMod (p ^ k)) :
    (fun i => reduceHom p hk
        (interpCoeff p K d (lt_min hm d.succ_pos) y 0 +
          ∑ j : Fin d, interpCoeff p K d (lt_min hm d.succ_pos) y j.succ *
            basisSample p K d m i j))
      = padPattern (lt_min hm d.succ_pos) y := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩
  have hlift : ∀ x : ZMod (p ^ k),
      reduceHom p hk (((x.val : ℕ) : ZMod (p ^ K))) = x := by
    intro x
    rw [map_natCast, ZMod.natCast_zmod_val]
  have h0 : interpCoeff p K d (lt_min hm d.succ_pos) y 0
      = (((y ⟨0, lt_min hm d.succ_pos⟩).val : ℕ) : ZMod (p ^ K)) := by
    simp [interpCoeff]
  funext i
  by_cases hir : (i : ℕ) < min m (d + 1)
  · by_cases hi0 : (i : ℕ) = 0
    · have hsum : ∑ j : Fin d,
          interpCoeff p K d (lt_min hm d.succ_pos) y j.succ *
            basisSample p K d m i j = 0 :=
        Finset.sum_eq_zero fun j _ => by
          simp [basisSample, hi0]
      rw [hsum, add_zero, h0, hlift]
      simp only [padPattern]
      rw [dif_pos hir]
      congr 1
      exact Fin.ext hi0.symm
    · have hi1 : 1 ≤ (i : ℕ) := Nat.pos_of_ne_zero hi0
      have hjlt : (i : ℕ) - 1 < d := by omega
      have hval : ((⟨(i : ℕ) - 1, hjlt⟩ : Fin d) : ℕ) = (i : ℕ) - 1 := rfl
      have hsuccval : (((⟨(i : ℕ) - 1, hjlt⟩ : Fin d).succ : Fin (d + 1)) : ℕ)
          = (i : ℕ) := by
        rw [Fin.val_succ, hval]
        omega
      have hsum : ∑ j : Fin d,
          interpCoeff p K d (lt_min hm d.succ_pos) y j.succ *
            basisSample p K d m i j
          = interpCoeff p K d (lt_min hm d.succ_pos) y
              (⟨(i : ℕ) - 1, hjlt⟩ : Fin d).succ := by
        rw [Finset.sum_eq_single (⟨(i : ℕ) - 1, hjlt⟩ : Fin d)]
        · simp only [basisSample]
          rw [if_pos (by omega), mul_one]
        · intro b _ hb
          have hbv : ¬((b : ℕ) + 1 = (i : ℕ)) := fun hcontra =>
            hb (Fin.ext (by omega))
          simp only [basisSample]
          rw [if_neg hbv, mul_zero]
        · intro habs
          exact absurd (Finset.mem_univ _) habs
      have hcoeff : interpCoeff p K d (lt_min hm d.succ_pos) y
          (⟨(i : ℕ) - 1, hjlt⟩ : Fin d).succ
          = (((y ⟨(i : ℕ), hir⟩ - y ⟨0, lt_min hm d.succ_pos⟩).val : ℕ) :
              ZMod (p ^ K)) := by
        simp only [interpCoeff, hsuccval]
        rw [if_neg hi0, dif_pos hir]
      rw [hsum, hcoeff, h0, map_add, hlift, hlift]
      simp only [padPattern]
      rw [dif_pos hir]
      ring
  · have hsum : ∑ j : Fin d,
        interpCoeff p K d (lt_min hm d.succ_pos) y j.succ *
          basisSample p K d m i j = 0 :=
      Finset.sum_eq_zero fun j _ => by
        have hj := j.isLt
        have him := i.isLt
        have hbv : ¬((j : ℕ) + 1 = (i : ℕ)) := by omega
        simp only [basisSample]
        rw [if_neg hbv, mul_zero]
    rw [hsum, add_zero, h0, hlift]
    simp only [padPattern]
    rw [dif_neg hir]

/-- Lower half of `thm:affine-precision-growth`: on the thesis sample the
affine class realises exactly `p ^ (k * min m (d + 1))` reduced patterns. -/
theorem affine_patternCount_basisSample {p : ℕ} [hp : Fact p.Prime]
    {K k d m : ℕ} (hk : k ≤ K) :
    patternCount (affineClass p K d) (⇑(reduceHom p hk)) (basisSample p K d m)
      = p ^ (k * min m (d + 1)) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hmemH : (fun x : Fin d → ZMod (p ^ K) =>
        (0 : Fin (d + 1) → ZMod (p ^ K)) 0 +
          ∑ j : Fin d, (0 : Fin (d + 1) → ZMod (p ^ K)) j.succ * x j)
        ∈ affineClass p K d := ⟨0, rfl⟩
    have hne : (patternSet (affineClass p K d) (⇑(reduceHom p hk))
        (basisSample p K d 0)).Nonempty := ⟨_, mem_patternSet hmemH⟩
    have hsub : (patternSet (affineClass p K d) (⇑(reduceHom p hk))
        (basisSample p K d 0)).Subsingleton :=
      fun x _ y _ => Subsingleton.elim x y
    rcases hsub.eq_empty_or_singleton with hemp | ⟨x, hx⟩
    · rw [hemp] at hne
      exact absurd hne Set.not_nonempty_empty
    · rw [patternCount, hx, Set.ncard_singleton]
      simp
  · refine le_antisymm (affine_patternCount_le hk _) ?_
    have hr : 0 < min m (d + 1) := lt_min hm d.succ_pos
    have hinj : Function.Injective
        (fun y : Fin (min m (d + 1)) → ZMod (p ^ k) =>
          padPattern (m := m) hr y) := by
      intro y y' hyy
      funext t
      have ht : (t : ℕ) < m := lt_of_lt_of_le t.isLt (min_le_left _ _)
      have hcomp := congrFun hyy ⟨(t : ℕ), ht⟩
      simp only [padPattern] at hcomp
      rw [dif_pos t.isLt] at hcomp
      rw [dif_pos t.isLt] at hcomp
      simpa using hcomp
    have hmem : ∀ y : Fin (min m (d + 1)) → ZMod (p ^ k),
        padPattern (m := m) hr y ∈
          patternSet (affineClass p K d) (⇑(reduceHom p hk))
            (basisSample p K d m) := by
      intro y
      refine ⟨fun x => interpCoeff p K d hr y 0 +
        ∑ j : Fin d, interpCoeff p K d hr y j.succ * x j,
        ⟨interpCoeff p K d hr y, rfl⟩, ?_⟩
      exact pattern_interpCoeff hk hm y
    calc p ^ (k * min m (d + 1))
        = (Set.range (fun y : Fin (min m (d + 1)) → ZMod (p ^ k) =>
            padPattern (m := m) hr y)).ncard := by
          classical
          rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj,
            Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun,
            ZMod.card, Fintype.card_fin, ← pow_mul]
      _ ≤ patternCount (affineClass p K d) (⇑(reduceHom p hk))
            (basisSample p K d m) := by
          refine Set.ncard_le_ncard ?_ (Set.toFinite _)
          rintro g ⟨y, rfl⟩
          exact hmem y

/-- Thesis `thm:affine-precision-growth`, growth-function form:
`Π_{𝒜_{d,K}}^{(p)}(m, k) = p ^ (k * min m (d + 1))`. -/
theorem affine_precision_growth {p : ℕ} [hp : Fact p.Prime] {K k d : ℕ}
    (hk : k ≤ K) (m : ℕ) :
    growth (affineClass p K d) (⇑(reduceHom p hk)) m
      = p ^ (k * min m (d + 1)) :=
  growth_eq_of_bounds (fun S => affine_patternCount_le hk S)
    ⟨basisSample p K d m, affine_patternCount_basisSample hk⟩

/-- Thesis `thm:affine-precision-growth`, base-`p` logarithm form:
`E_{𝒜_{d,K}}^{(p)}(m, k) = k * min m (d + 1)`. -/
theorem affine_precision_growth_log {p : ℕ} [hp : Fact p.Prime] {K k d : ℕ}
    (hk : k ≤ K) (m : ℕ) :
    Nat.log p (growth (affineClass p K d) (⇑(reduceHom p hk)) m)
      = k * min m (d + 1) := by
  rw [affine_precision_growth hk m, Nat.log_pow hp.out.one_lt]

/-! ### Covering interpretation: `prop:precision-growth-covering`

For a fixed sample, the realised precision-`k` pattern count is the minimum
number of closed balls of radius `p ^ (-k)`, in the product sup metric on
`ℤ_p^m`, required to cover the prediction set: occupied residue classes are
disjoint, each needs one covering ball, and one ball covers a full class. -/

/-- The set of prediction vectors of `H` on the sample `S`. -/
def predictionSet {p : ℕ} [Fact p.Prime] {X : Type*} {m : ℕ}
    (H : Set (X → ℤ_[p])) (S : Fin m → X) : Set (Fin m → ℤ_[p]) :=
  (fun h => fun i => h (S i)) '' H

/-- The covering number of `P` by closed balls of radius `r`: the least
cardinality of a finite set of centres whose closed balls cover `P`. -/
noncomputable def coveringNumber {α : Type*} [PseudoMetricSpace α] (r : ℝ)
    (P : Set α) : ℕ :=
  sInf {n | ∃ t : Finset α, t.card = n ∧ P ⊆ ⋃ c ∈ t, Metric.closedBall c r}

/-- Two `p`-adic vectors lie within `p ^ (-k)` of each other in the product
sup metric exactly when they agree coordinatewise modulo `p ^ k`. -/
theorem mem_closedBall_iff_toZModPow {p : ℕ} [Fact p.Prime] {m k : ℕ}
    (u v : Fin m → ℤ_[p]) :
    u ∈ Metric.closedBall v ((p : ℝ) ^ (-(k : ℤ))) ↔
      ∀ i, PadicInt.toZModPow k (u i) = PadicInt.toZModPow k (v i) := by
  rw [Metric.mem_closedBall, dist_pi_le_iff (zpow_nonneg (Nat.cast_nonneg p) _)]
  refine forall_congr' fun i => ?_
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]

/-- The covering number of any set of `p`-adic vectors at radius `p ^ (-k)`
is the number of occupied coordinatewise residue classes modulo `p ^ k`. -/
theorem coveringNumber_eq_ncard_image {p : ℕ} [hp : Fact p.Prime] {m k : ℕ}
    (P : Set (Fin m → ℤ_[p])) :
    coveringNumber ((p : ℝ) ^ (-(k : ℤ))) P
      = ((fun u : Fin m → ℤ_[p] =>
          fun i => PadicInt.toZModPow k (u i)) '' P).ncard := by
  classical
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩
  set ρ : (Fin m → ℤ_[p]) → (Fin m → ZMod (p ^ k)) :=
    fun u => fun i => PadicInt.toZModPow k (u i) with hρ
  have hQfin : (ρ '' P).Finite := Set.toFinite _
  have hcov : P ⊆ ⋃ c ∈ hQfin.toFinset.image (Function.invFunOn ρ P),
      Metric.closedBall c ((p : ℝ) ^ (-(k : ℤ))) := by
    intro v hv
    have hexv : ∃ a ∈ P, ρ a = ρ v := ⟨v, hv, rfl⟩
    refine Set.mem_iUnion₂.mpr ⟨Function.invFunOn ρ P (ρ v), ?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨ρ v, hQfin.mem_toFinset.mpr ⟨v, hv, rfl⟩, rfl⟩
    · rw [mem_closedBall_iff_toZModPow]
      intro i
      exact (congrFun (Function.invFunOn_eq hexv) i).symm
  have hmem : (hQfin.toFinset.image (Function.invFunOn ρ P)).card ∈
      {n | ∃ t : Finset (Fin m → ℤ_[p]), t.card = n ∧
        P ⊆ ⋃ c ∈ t, Metric.closedBall c ((p : ℝ) ^ (-(k : ℤ)))} :=
    ⟨_, rfl, hcov⟩
  refine le_antisymm ((Nat.sInf_le hmem).trans ?_) (le_csInf ⟨_, hmem⟩ ?_)
  · calc (hQfin.toFinset.image (Function.invFunOn ρ P)).card
        ≤ hQfin.toFinset.card := Finset.card_image_le
      _ = (ρ '' P).ncard := by rw [Set.ncard_eq_toFinset_card _ hQfin]
  · rintro n ⟨t, rfl, hcovt⟩
    have hex : ∀ w ∈ ρ '' P,
        ∃ c ∈ (↑t : Set (Fin m → ℤ_[p])), ρ c = w := by
      rintro w ⟨v, hv, rfl⟩
      obtain ⟨c, hc, hvc⟩ := Set.mem_iUnion₂.mp (hcovt hv)
      refine ⟨c, hc, ?_⟩
      funext i
      exact ((mem_closedBall_iff_toZModPow v c).mp hvc i).symm
    calc (ρ '' P).ncard
        ≤ (↑t : Set (Fin m → ℤ_[p])).ncard := by
          refine Set.ncard_le_ncard_of_injOn (Function.invFunOn ρ ↑t)
            (fun w hw => Function.invFunOn_mem (hex w hw)) ?_ t.finite_toSet
          intro w hw w' hw' heq
          rw [← Function.invFunOn_eq (hex w hw),
            ← Function.invFunOn_eq (hex w' hw'), heq]
      _ = t.card := Set.ncard_coe_finset t

/-- Thesis `prop:precision-growth-covering`: for a fixed sample, the number
of realised precision-`k` patterns is the covering number of the prediction
set by closed balls of radius `p ^ (-k)` in the product sup metric. -/
theorem precision_growth_covering {p : ℕ} [hp : Fact p.Prime] {X : Type*}
    {m k : ℕ} (H : Set (X → ℤ_[p])) (S : Fin m → X) :
    patternCount H (⇑(PadicInt.toZModPow k)) S
      = coveringNumber ((p : ℝ) ^ (-(k : ℤ))) (predictionSet H S) := by
  rw [coveringNumber_eq_ncard_image, patternCount]
  congr 1
  rw [patternSet, predictionSet, Set.image_image]

/-! ### Recovery of binary growth and VC dimension:
`prop:precision-growth-vc`

At `p = 2` and `k = 1` the finite-precision pattern count is the ordinary
binary growth function of the reduced class, and complete residue shattering
recovers the usual VC criterion. -/

/-- Complete residue shattering: the class realises every reduced labelling
of the sample. -/
def Shatters {X O : Type*} {m : ℕ} (H' : Set (X → O)) (S : Fin m → X) : Prop :=
  patternSet H' id S = Set.univ

/-- The VC dimension of a class of already-reduced hypotheses: the largest
sample size on which every labelling is realised. -/
noncomputable def vcDim {X O : Type*} (H' : Set (X → O)) : ℕ :=
  sSup {m | ∃ S : Fin m → X, Shatters H' S}

theorem patternSet_image_comp {X Ω Ω' : Type*} {m : ℕ} (H : Set (X → Ω))
    (ρ : Ω → Ω') (S : Fin m → X) :
    patternSet ((fun h => ρ ∘ h) '' H) id S = patternSet H ρ S := by
  rw [patternSet, patternSet, Set.image_image]
  rfl

theorem patternCount_image_comp {X Ω Ω' : Type*} {m : ℕ} (H : Set (X → Ω))
    (ρ : Ω → Ω') (S : Fin m → X) :
    patternCount ((fun h => ρ ∘ h) '' H) id S = patternCount H ρ S := by
  rw [patternCount, patternCount, patternSet_image_comp]

/-- Thesis `prop:precision-growth-vc`, growth-function half: at `p = 2` and
`k = 1` the precision-indexed growth function is the ordinary binary growth
function of the reduced class `H̄ = ρ₁ ∘ H`. -/
theorem precision_growth_binary {X : Type*} (H : Set (X → ℤ_[2])) (m : ℕ) :
    growth H (⇑(PadicInt.toZModPow (p := 2) 1)) m
      = growth ((fun h => ⇑(PadicInt.toZModPow (p := 2) 1) ∘ h) '' H) id m := by
  rw [growth, growth]
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨S, patternCount_image_comp H _ S⟩
  · rintro ⟨S, rfl⟩
    exact ⟨S, (patternCount_image_comp H _ S).symm⟩

/-- Shattering is exactly attainment of the full labelling count. -/
theorem shatters_iff_patternCount_eq {X O : Type*} [Fintype O] {m : ℕ}
    (H' : Set (X → O)) (S : Fin m → X) :
    Shatters H' S ↔ patternCount H' id S = Fintype.card O ^ m := by
  classical
  have huniv : (Set.univ : Set (Fin m → O)).ncard = Fintype.card O ^ m := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun,
      Fintype.card_fin]
  constructor
  · intro hS
    rw [patternCount, hS, huniv]
  · intro hc
    exact Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      (huniv.trans_le hc.ge) Set.finite_univ

/-- Thesis `prop:precision-growth-vc`, VC-criterion half: the VC dimension of
the reduced binary class is the largest sample size at which the
precision-one growth function attains `2 ^ m`. -/
theorem precision_growth_vc {X : Type*} (H : Set (X → ℤ_[2])) :
    vcDim ((fun h => ⇑(PadicInt.toZModPow (p := 2) 1) ∘ h) '' H)
      = sSup {m | growth H (⇑(PadicInt.toZModPow (p := 2) 1)) m = 2 ^ m} := by
  haveI : NeZero ((2 : ℕ) ^ 1) := ⟨by norm_num⟩
  rw [vcDim]
  congr 1
  ext m
  simp only [Set.mem_setOf_eq]
  have hub : ∀ S : Fin m → X,
      patternCount H (⇑(PadicInt.toZModPow (p := 2) 1)) S ≤ 2 ^ m := by
    intro S'
    have h := patternCount_le_card H (⇑(PadicInt.toZModPow (p := 2) 1)) S'
    rw [ZMod.card] at h
    exact h
  constructor
  · rintro ⟨S, hS⟩
    have hcount : patternCount H (⇑(PadicInt.toZModPow (p := 2) 1)) S
        = 2 ^ m := by
      rw [← patternCount_image_comp H _ S]
      have h := (shatters_iff_patternCount_eq _ S).mp hS
      rw [ZMod.card] at h
      exact h
    exact growth_eq_of_bounds hub ⟨S, hcount⟩
  · intro hgr
    have hne : {n | ∃ S : Fin m → X,
        patternCount H (⇑(PadicInt.toZModPow (p := 2) 1)) S = n}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      rw [growth, hemp, csSup_empty] at hgr
      exact (pow_pos two_pos m).ne' hgr.symm
    have hbdd : BddAbove {n | ∃ S : Fin m → X,
        patternCount H (⇑(PadicInt.toZModPow (p := 2) 1)) S = n} := by
      refine ⟨2 ^ m, ?_⟩
      rintro n ⟨S, rfl⟩
      exact hub S
    obtain ⟨S, hS⟩ := Nat.sSup_mem hne hbdd
    refine ⟨S, (shatters_iff_patternCount_eq _ S).mpr ?_⟩
    rw [patternCount_image_comp, ZMod.card]
    exact hS.trans hgr

/-! ### Tree-syntax growth bounds: `prop:tree-syntax-growth-bound` and
`cor:binary-tree-precision-growth`

Counting model descriptions bounds the realised pattern count for any
interpretation of a finite family of tree shapes, and the ordered binary tree
case is counted by the Catalan numbers with `L = I + 1`. -/

/-- The class described by a finite family of shapes: each model of shape
`T` chooses one of `R` split rules at each of the `I T` internal nodes and an
output label at each of the `L T` leaves, interpreted by `interp`. -/
def syntaxClass {X Shape : Type*} (𝔗 : Finset Shape) (I L : Shape → ℕ)
    (R : ℕ) (O : Type*)
    (interp : (T : Shape) → ((Fin (I T) → Fin R) × (Fin (L T) → O)) →
      (X → O)) : Set (X → O) :=
  ⋃ T ∈ 𝔗, Set.range (interp T)

theorem ncard_biUnion_le {α γ : Type*} (s : Finset γ) (f : γ → Set α) :
    (⋃ i ∈ s, f i).ncard ≤ ∑ i ∈ s, (f i).ncard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add le_rfl ih)

/-- Thesis `prop:tree-syntax-growth-bound`: the description count bounds the
realised pattern count for any interpretation of a finite family of tree
shapes with at most `R` split-rule choices per internal node and `p ^ k`
residue outputs per leaf. -/
theorem tree_syntax_growth_bound {p : ℕ} [hp : Fact p.Prime] {X Shape : Type*}
    {k m : ℕ} (𝔗 : Finset Shape) (I L : Shape → ℕ) (R : ℕ)
    (interp : (T : Shape) →
      ((Fin (I T) → Fin R) × (Fin (L T) → ZMod (p ^ k))) →
        (X → ZMod (p ^ k)))
    (S : Fin m → X) :
    patternCount (syntaxClass 𝔗 I L R (ZMod (p ^ k)) interp) id S
      ≤ min (p ^ (k * m)) (∑ T ∈ 𝔗, R ^ I T * p ^ (k * L T)) := by
  classical
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩
  refine le_min ?_ ?_
  · have h := patternCount_le_card
      (syntaxClass 𝔗 I L R (ZMod (p ^ k)) interp) id S
    rwa [ZMod.card, ← pow_mul] at h
  · have hset : patternSet (syntaxClass 𝔗 I L R (ZMod (p ^ k)) interp) id S
        = ⋃ T ∈ 𝔗, patternSet (Set.range (interp T)) id S := by
      simp only [patternSet, syntaxClass, Set.image_iUnion]
    rw [patternCount, hset]
    refine (ncard_biUnion_le 𝔗 _).trans (Finset.sum_le_sum ?_)
    intro T _
    have himg : patternSet (Set.range (interp T)) id S
        = Set.range
            (fun md : (Fin (I T) → Fin R) × (Fin (L T) → ZMod (p ^ k)) =>
              fun i => interp T md (S i)) := by
      rw [patternSet, ← Set.range_comp]
      rfl
    rw [himg]
    have h1 : (Set.range
        (fun md : (Fin (I T) → Fin R) × (Fin (L T) → ZMod (p ^ k)) =>
          fun i => interp T md (S i))).ncard
        ≤ Nat.card ((Fin (I T) → Fin R) × (Fin (L T) → ZMod (p ^ k))) := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (Set.ncard_univ _).le
    have h2 : Nat.card ((Fin (I T) → Fin R) × (Fin (L T) → ZMod (p ^ k)))
        = R ^ I T * p ^ (k * L T) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin,
        Fintype.card_fin, ← pow_mul]
    exact h1.trans h2.le

open Tree in
/-- Thesis `cor:binary-tree-precision-growth`: for ordered full binary tree
shapes with at most `n` internal nodes — counted by the Catalan numbers, with
`L = I + 1` leaves — the description bound becomes
`∑_{i ≤ n} C_i R^i p^(k(i+1))`. -/
theorem binary_tree_precision_growth {p : ℕ} [hp : Fact p.Prime] {X : Type*}
    {k m : ℕ} (n R : ℕ)
    (interp : (T : Tree Unit) →
      ((Fin T.numNodes → Fin R) × (Fin T.numLeaves → ZMod (p ^ k))) →
        (X → ZMod (p ^ k)))
    (S : Fin m → X) :
    patternCount
      (syntaxClass ((Finset.range (n + 1)).biUnion treesOfNumNodesEq)
        Tree.numNodes Tree.numLeaves R (ZMod (p ^ k)) interp) id S
      ≤ min (p ^ (k * m))
          (∑ i ∈ Finset.range (n + 1),
            catalan i * (R ^ i * p ^ (k * (i + 1)))) := by
  classical
  refine (tree_syntax_growth_bound _ _ _ _ interp S).trans (le_of_eq ?_)
  have hdisj : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint
      treesOfNumNodesEq := by
    intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro T hTa hTb
    rw [mem_treesOfNumNodesEq] at hTa hTb
    exact hab (hTa.symm.trans hTb)
  have hsum : ∑ T ∈ (Finset.range (n + 1)).biUnion treesOfNumNodesEq,
      R ^ T.numNodes * p ^ (k * T.numLeaves)
      = ∑ i ∈ Finset.range (n + 1),
          catalan i * (R ^ i * p ^ (k * (i + 1))) := by
    rw [Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hconst : ∀ T ∈ treesOfNumNodesEq i,
        R ^ T.numNodes * p ^ (k * T.numLeaves)
          = R ^ i * p ^ (k * (i + 1)) := by
      intro T hT
      rw [mem_treesOfNumNodesEq] at hT
      rw [numLeaves_eq_numNodes_succ, hT]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const,
      treesOfNumNodesEq_card_eq_catalan, smul_eq_mul]
  rw [hsum]

#print axioms affine_precision_growth
#print axioms affine_precision_growth_log
#print axioms precision_growth_covering
#print axioms precision_growth_binary
#print axioms precision_growth_vc
#print axioms tree_syntax_growth_bound
#print axioms binary_tree_precision_growth

end PhdThesisLean.PrecisionGrowth
