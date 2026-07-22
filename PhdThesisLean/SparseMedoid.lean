/-
  Formalisation of the sparse medoid representation theorem from Greg Baker's
  PhD thesis.

  Thesis source: pac-learning-open-questions/body.tex
  Thesis label: thm:sparse-medoid-representation
  Thesis snapshot: 2c6418bcf9643fc6e039237f0f59ace14b2557fc
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace PhdThesisLean.Medoid

open scoped BigOperators

abbrev RK (p K : ℕ) := ZMod (p ^ K)

def MultipleAt (p K t : ℕ) (u : RK p K) : Prop :=
  ∃ c : RK p K, u = (p : RK p K) ^ t * c

theorem multipleAt_zero (p K : ℕ) (u : RK p K) : MultipleAt p K 0 u := by
  exact ⟨u, by simp⟩

theorem multipleAt_mono {p K t s : ℕ} {u : RK p K}
    (hts : t ≤ s) (hu : MultipleAt p K s u) : MultipleAt p K t u := by
  obtain ⟨c, rfl⟩ := hu
  refine ⟨(p : RK p K) ^ (s - t) * c, ?_⟩
  rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hts]

theorem multipleAt_zero_value (p K t : ℕ) : MultipleAt p K t (0 : RK p K) := by
  exact ⟨0, by simp⟩

noncomputable def divisibilityLevels (p K : ℕ) (u : RK p K) : Finset ℕ :=
  by
    classical
    exact (Finset.range (K + 1)).filter fun t ↦ MultipleAt p K t u

theorem divisibilityLevels_nonempty (p K : ℕ) (u : RK p K) :
    (divisibilityLevels p K u).Nonempty := by
  classical
  exact ⟨0, by simp [divisibilityLevels, multipleAt_zero]⟩

noncomputable def truncatedVal (p K : ℕ) (u : RK p K) : ℕ :=
  (divisibilityLevels p K u).max' (divisibilityLevels_nonempty p K u)

theorem truncatedVal_le (p K : ℕ) (u : RK p K) : truncatedVal p K u ≤ K := by
  classical
  have hm := Finset.max'_mem (divisibilityLevels p K u) (divisibilityLevels_nonempty p K u)
  exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)

theorem multipleAt_truncatedVal (p K : ℕ) (u : RK p K) :
    MultipleAt p K (truncatedVal p K u) u := by
  classical
  have hm := Finset.max'_mem (divisibilityLevels p K u) (divisibilityLevels_nonempty p K u)
  exact (Finset.mem_filter.mp hm).2

theorem multipleAt_iff_le_truncatedVal
    {p K t : ℕ} (ht : t ≤ K) (u : RK p K) :
    MultipleAt p K t u ↔ t ≤ truncatedVal p K u := by
  classical
  constructor
  · intro hu
    apply Finset.le_max'
    rw [divisibilityLevels, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ht), hu⟩
  · intro h
    exact multipleAt_mono h (multipleAt_truncatedVal p K u)

noncomputable def finitePadicDist
    (p K : ℕ) (u v : RK p K) : ℝ :=
  if u = v then 0 else (p : ℝ) ^ (-(truncatedVal p K (u - v) : ℤ))

theorem finitePadicDist_nonneg (p K : ℕ) [Fact p.Prime] (u v : RK p K) :
    0 ≤ finitePadicDist p K u v := by
  rw [finitePadicDist]
  split_ifs
  · rfl
  · exact (zpow_pos (by exact_mod_cast (Fact.out : Nat.Prime p).pos) _).le

theorem finitePadicDist_le_iff_multipleAt
    {p K t : ℕ} [Fact p.Prime] (ht : t ≤ K) (u v : RK p K) :
    finitePadicDist p K u v ≤ (p : ℝ) ^ (-(t : ℤ)) ↔
      MultipleAt p K t (u - v) := by
  by_cases huv : u = v
  · subst v
    simp [finitePadicDist, multipleAt_zero_value]
  · rw [finitePadicDist, if_neg huv]
    rw [zpow_le_zpow_iff_right₀ (show 1 < (p : ℝ) by
      exact_mod_cast (Fact.out : Nat.Prime p).one_lt)]
    rw [multipleAt_iff_le_truncatedVal ht]
    omega

theorem finitePadicDist_translate
    (p K : ℕ) (u v a : RK p K) :
    finitePadicDist p K (u + a) (v + a) = finitePadicDist p K u v := by
  simp [finitePadicDist]

theorem finitePadicDist_eq_of_sub_eq
    {p K : ℕ} {u v u' v' : RK p K} (h : u - v = u' - v') :
    finitePadicDist p K u v = finitePadicDist p K u' v' := by
  have heq : u = v ↔ u' = v' := by simpa [sub_eq_zero] using congrArg (· = 0) h
  by_cases huv : u = v
  · have hu'v' := heq.mp huv
    simp [finitePadicDist, huv, hu'v']
  · have hu'v' : u' ≠ v' := fun h' ↦ huv (heq.mpr h')
    simp only [finitePadicDist, if_neg huv, if_neg hu'v']
    rw [h]

theorem finitePadicDist_pos_of_ne
    {p K : ℕ} [Fact p.Prime] {u v : RK p K} (h : u ≠ v) :
    0 < finitePadicDist p K u v := by
  rw [finitePadicDist, if_neg h]
  exact zpow_pos (by exact_mod_cast (Fact.out : Nat.Prime p).pos) _

theorem multipleAt_add
    {p K t : ℕ} {u v : RK p K}
    (hu : MultipleAt p K t u) (hv : MultipleAt p K t v) :
    MultipleAt p K t (u + v) := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  exact ⟨a + b, by ring⟩

theorem multipleAt_neg
    {p K t : ℕ} {u : RK p K} (hu : MultipleAt p K t u) :
    MultipleAt p K t (-u) := by
  obtain ⟨a, rfl⟩ := hu
  exact ⟨-a, by ring⟩

theorem multipleAt_sub
    {p K t : ℕ} {u v : RK p K}
    (hu : MultipleAt p K t u) (hv : MultipleAt p K t v) :
    MultipleAt p K t (u - v) := by
  simpa [sub_eq_add_neg] using multipleAt_add hu (multipleAt_neg hv)

def slopeOffset
    {p K d : ℕ} (S : Finset (Fin d)) (x r : Fin d → RK p K)
    (a : S → RK p K) : RK p K :=
  ∑ j : S, a j * (x j - r j)

theorem slopeOffset_add
    {p K d : ℕ} (S : Finset (Fin d)) (x r : Fin d → RK p K)
    (a b : S → RK p K) :
    slopeOffset S x r (a + b) = slopeOffset S x r a + slopeOffset S x r b := by
  simp [slopeOffset, add_mul, Finset.sum_add_distrib]

theorem slopeOffset_sub
    {p K d : ℕ} (S : Finset (Fin d)) (x r : Fin d → RK p K)
    (a b : S → RK p K) :
    slopeOffset S x r (a - b) = slopeOffset S x r a - slopeOffset S x r b := by
  simp [slopeOffset, sub_mul, Finset.sum_sub_distrib]

def affineRegressorOutput
    {p K d : ℕ} (F : (Fin d → RK p K) → RK p K)
    (S : (Fin d → RK p K) → Finset (Fin d))
    (x r : Fin d → RK p K) (a : S r → RK p K) : RK p K :=
  F r + slopeOffset (S r) x r a

noncomputable def blockCost
    {p K d : ℕ} [Fact p.Prime]
    (F : (Fin d → RK p K) → RK p K)
    (S : (Fin d → RK p K) → Finset (Fin d))
    (x r : Fin d → RK p K) (c : RK p K) : ℝ :=
  ∑ a : S r → RK p K, finitePadicDist p K c (affineRegressorOutput F S x r a)

theorem blockCost_eq_of_mem_image
    {p K d : ℕ} [Fact p.Prime]
    (F : (Fin d → RK p K) → RK p K)
    (S : (Fin d → RK p K) → Finset (Fin d))
    (x r : Fin d → RK p K) {c₁ c₂ : RK p K}
    (h₁ : ∃ a₁ : S r → RK p K, c₁ = affineRegressorOutput F S x r a₁)
    (h₂ : ∃ a₂ : S r → RK p K, c₂ = affineRegressorOutput F S x r a₂) :
    blockCost F S x r c₁ = blockCost F S x r c₂ := by
  obtain ⟨a₁, rfl⟩ := h₁
  obtain ⟨a₂, rfl⟩ := h₂
  let e := Equiv.addRight (a₂ - a₁)
  apply Fintype.sum_equiv e
  intro a
  apply finitePadicDist_eq_of_sub_eq
  dsimp [e, affineRegressorOutput]
  rw [slopeOffset_add, slopeOffset_sub]
  ring

theorem blockCost_lt_of_mem_not_mem
    {p K d t : ℕ} [Fact p.Prime] (ht : t ≤ K)
    (F : (Fin d → RK p K) → RK p K)
    (S : (Fin d → RK p K) → Finset (Fin d))
    (x r : Fin d → RK p K) {c₁ c₂ : RK p K}
    (himage : ∀ u : RK p K, MultipleAt p K t u ↔
      ∃ a : S r → RK p K, u = slopeOffset (S r) x r a)
    (hc₁ : MultipleAt p K t (c₁ - F r))
    (hc₂ : ¬MultipleAt p K t (c₂ - F r)) :
    blockCost F S x r c₁ < blockCost F S x r c₂ := by
  rw [blockCost, blockCost]
  have hterm : ∀ a : S r → RK p K,
      finitePadicDist p K c₁ (affineRegressorOutput F S x r a) <
        finitePadicDist p K c₂ (affineRegressorOutput F S x r a) := by
    intro a
    let out := affineRegressorOutput F S x r a
    have hout : MultipleAt p K t (out - F r) := by
      dsimp [out, affineRegressorOutput]
      rw [add_sub_cancel_left]
      exact (himage _).mpr ⟨a, rfl⟩
    have hleft : finitePadicDist p K c₁ out ≤ (p : ℝ) ^ (-(t : ℤ)) := by
      rw [finitePadicDist_le_iff_multipleAt ht]
      have : c₁ - out = (c₁ - F r) - (out - F r) := by ring
      rw [this]
      exact multipleAt_sub hc₁ hout
    have hright : (p : ℝ) ^ (-(t : ℤ)) < finitePadicDist p K c₂ out := by
      apply lt_of_not_ge
      rw [finitePadicDist_le_iff_multipleAt ht]
      intro hdiff
      apply hc₂
      have : c₂ - F r = (c₂ - out) + (out - F r) := by ring
      rw [this]
      exact multipleAt_add hdiff hout
    exact hleft.trans_lt hright
  apply Finset.sum_lt_sum
  · intro a _
    exact (hterm a).le
  · exact ⟨0, Finset.mem_univ _, hterm 0⟩

theorem multipleAt_mul_left
    {p K t : ℕ} (a : RK p K) {u : RK p K}
    (hu : MultipleAt p K t u) : MultipleAt p K t (a * u) := by
  obtain ⟨c, rfl⟩ := hu
  exact ⟨a * c, by ring⟩

theorem pow_precision_eq_zero (p K : ℕ) :
    (p : RK p K) ^ K = 0 := by
  rw [← Nat.cast_pow]
  exact ZMod.natCast_self (p ^ K)

theorem multipleAt_precision_iff_eq_zero (p K : ℕ) (u : RK p K) :
    MultipleAt p K K u ↔ u = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [pow_precision_eq_zero, zero_mul]
  · rintro rfl
    exact multipleAt_zero_value p K K

/-- Algebraic form of local sparse non-expansiveness. The common factor
condition and the unit witness express that `t` is the minimum truncated
valuation of the active coordinate differences. -/
def LocallySparseNonexpansive
    {p K d : ℕ}
    (F : (Fin d → RK p K) → RK p K)
    (S : (Fin d → RK p K) → Finset (Fin d)) (s : ℕ) : Prop :=
  (∀ r, (S r).card ≤ s) ∧
    ∀ r x, ∃ t ≤ K,
      (∀ j ∈ S r, MultipleAt p K t (x j - r j)) ∧
      (t = K ∨ ∃ j ∈ S r, ∃ u : RK p K,
        IsUnit u ∧ x j - r j = (p : RK p K) ^ t * u) ∧
      MultipleAt p K t (F x - F r)

theorem slopeOffset_multipleAt
    {p K d t : ℕ} (S : Finset (Fin d)) (x r : Fin d → RK p K)
    (hall : ∀ j ∈ S, MultipleAt p K t (x j - r j))
    (a : S → RK p K) :
    MultipleAt p K t (slopeOffset S x r a) := by
  classical
  unfold slopeOffset
  let U : Finset S := Finset.univ
  change MultipleAt p K t (∑ j ∈ U, a j * (x j - r j))
  induction U using Finset.induction_on with
  | empty => simp [multipleAt_zero_value]
  | @insert j T hj ih =>
      rw [Finset.sum_insert hj]
      apply multipleAt_add
      · exact multipleAt_mul_left _ (hall j.1 j.2)
      · exact ih

theorem slopeOffset_image_eq_multipleAt
    {p K d t : ℕ}
    (S : Finset (Fin d)) (x r : Fin d → RK p K)
    (hall : ∀ j ∈ S, MultipleAt p K t (x j - r j))
    (hexact : t = K ∨ ∃ j ∈ S, ∃ u : RK p K,
      IsUnit u ∧ x j - r j = (p : RK p K) ^ t * u) :
    ∀ q : RK p K, MultipleAt p K t q ↔
      ∃ a : S → RK p K, q = slopeOffset S x r a := by
  classical
  intro q
  constructor
  · intro hq
    rcases hexact with htK | ⟨j, hj, u, hu, hdiff⟩
    · have hqK : MultipleAt p K K q := by simpa [htK] using hq
      have hq0 : q = 0 := (multipleAt_precision_iff_eq_zero p K q).mp hqK
      exact ⟨0, by simp [hq0, slopeOffset]⟩
    · obtain ⟨u', rfl⟩ := hu
      obtain ⟨c, hc⟩ := hq
      let jS : S := ⟨j, hj⟩
      let a : S → RK p K := fun k ↦
        if k = jS then c * (↑(u'⁻¹) : RK p K) else 0
      refine ⟨a, ?_⟩
      rw [hc, slopeOffset]
      rw [Fintype.sum_eq_single jS]
      · dsimp [a, jS]
        simp only [if_pos, hdiff]
        calc
          (p : RK p K) ^ t * c = (p : RK p K) ^ t * c * 1 := by simp
          _ = (p : RK p K) ^ t * c *
              ((↑(u'⁻¹) : RK p K) * (u' : RK p K)) := by
            rw [Units.inv_mul]
          _ = c * ((↑(u'⁻¹) : RK p K) *
              ((p : RK p K) ^ t * (u' : RK p K))) := by
            ring
          _ = c * (↑(u'⁻¹) : RK p K) *
              ((p : RK p K) ^ t * (u' : RK p K)) :=
            (mul_assoc _ _ _).symm
      · intro k hk
        simp [a, hk]
  · rintro ⟨a, rfl⟩
    exact slopeOffset_multipleAt S x r hall a

abbrev EnsembleIndex
    {p K d : ℕ} (S : (Fin d → RK p K) → Finset (Fin d)) :=
  Σ r : Fin d → RK p K, S r → RK p K

def ensembleOutput
    {p K d : ℕ} (F : (Fin d → RK p K) → RK p K)
    (S : (Fin d → RK p K) → Finset (Fin d))
    (x : Fin d → RK p K) (e : EnsembleIndex S) : RK p K :=
  affineRegressorOutput F S x e.1 e.2

noncomputable def ensembleCost
    {p K d : ℕ} [Fact p.Prime]
    (F : (Fin d → RK p K) → RK p K)
    (S : (Fin d → RK p K) → Finset (Fin d))
    (x : Fin d → RK p K) (c : RK p K) : ℝ :=
  ∑ e : EnsembleIndex S, finitePadicDist p K c (ensembleOutput F S x e)

def IsEnsembleMedoid
    {p K d : ℕ} [Fact p.Prime]
    (F : (Fin d → RK p K) → RK p K)
    (S : (Fin d → RK p K) → Finset (Fin d))
    (x : Fin d → RK p K) (e : EnsembleIndex S) : Prop :=
  ∀ f : EnsembleIndex S,
    ensembleCost F S x (ensembleOutput F S x e) ≤
      ensembleCost F S x (ensembleOutput F S x f)

theorem ensembleCost_eq_sum_blockCost
    {p K d : ℕ} [Fact p.Prime]
    (F : (Fin d → RK p K) → RK p K)
    (S : (Fin d → RK p K) → Finset (Fin d))
    (x : Fin d → RK p K) (c : RK p K) :
    ensembleCost F S x c = ∑ r, blockCost F S x r c := by
  rw [ensembleCost, Fintype.sum_sigma]
  rfl

theorem sparse_medoid_representation
    (p K d s : ℕ) [Fact p.Prime] (_hK : 1 ≤ K)
    (F : (Fin d → RK p K) → RK p K)
    (S : (Fin d → RK p K) → Finset (Fin d))
    (hlocal : LocallySparseNonexpansive F S s) (x : Fin d → RK p K) :
    (∀ r, (S r).card ≤ s) ∧
    let exactIndex : EnsembleIndex S := ⟨x, 0⟩
    ensembleOutput F S x exactIndex = F x ∧
    IsEnsembleMedoid F S x exactIndex ∧
    ∀ e : EnsembleIndex S,
      IsEnsembleMedoid F S x e → ensembleOutput F S x e = F x := by
  refine ⟨hlocal.1, ?_⟩
  dsimp only
  have hexact : ensembleOutput F S x (⟨x, 0⟩ : EnsembleIndex S) = F x := by
    simp [ensembleOutput, affineRegressorOutput, slopeOffset]
  refine ⟨hexact, ?_, ?_⟩
  · intro e
    rw [hexact, ensembleCost_eq_sum_blockCost, ensembleCost_eq_sum_blockCost]
    apply Finset.sum_le_sum
    intro r _
    obtain ⟨t, ht, hall, hexact, hFx⟩ := hlocal.2 r x
    have himage := slopeOffset_image_eq_multipleAt (S r) x r hall hexact
    by_cases he : MultipleAt p K t (ensembleOutput F S x e - F r)
    · apply le_of_eq
      apply blockCost_eq_of_mem_image F S x r
      · obtain ⟨a, ha⟩ := (himage _).mp hFx
        refine ⟨a, ?_⟩
        dsimp [affineRegressorOutput]
        rw [← ha]
        ring
      · obtain ⟨a, ha⟩ := (himage _).mp he
        refine ⟨a, ?_⟩
        dsimp [affineRegressorOutput, ensembleOutput] at ha ⊢
        rw [← ha]
        ring
    · exact (blockCost_lt_of_mem_not_mem ht F S x r himage hFx he).le
  · intro e hemed
    by_contra hne
    have hstrictBlock :
        blockCost F S x x (F x) <
          blockCost F S x x (ensembleOutput F S x e) := by
      rw [blockCost, blockCost]
      apply Finset.sum_lt_sum
      · intro a _
        have hout : affineRegressorOutput F S x x a = F x := by
          simp [affineRegressorOutput, slopeOffset]
        rw [hout]
        simpa [finitePadicDist] using
          (finitePadicDist_pos_of_ne (p := p) (K := K) hne).le
      · exact ⟨0, Finset.mem_univ _, by
          simp only [affineRegressorOutput, slopeOffset, Pi.zero_apply, zero_mul,
            Finset.sum_const_zero, add_zero]
          simpa [finitePadicDist] using
            finitePadicDist_pos_of_ne (p := p) (K := K) hne⟩
    have hallWeak : ∀ r,
        blockCost F S x r (F x) ≤
          blockCost F S x r (ensembleOutput F S x e) := by
      intro r
      obtain ⟨t, ht, hall, hexact, hFx⟩ := hlocal.2 r x
      have himage := slopeOffset_image_eq_multipleAt (S r) x r hall hexact
      by_cases he : MultipleAt p K t (ensembleOutput F S x e - F r)
      · apply le_of_eq
        apply blockCost_eq_of_mem_image F S x r
        · obtain ⟨a, ha⟩ := (himage _).mp hFx
          refine ⟨a, ?_⟩
          dsimp [affineRegressorOutput]
          rw [← ha]
          ring
        · obtain ⟨a, ha⟩ := (himage _).mp he
          refine ⟨a, ?_⟩
          dsimp [affineRegressorOutput, ensembleOutput] at ha ⊢
          rw [← ha]
          ring
      · exact (blockCost_lt_of_mem_not_mem ht F S x r himage hFx he).le
    have hcostStrict :
        ensembleCost F S x (F x) <
          ensembleCost F S x (ensembleOutput F S x e) := by
      rw [ensembleCost_eq_sum_blockCost, ensembleCost_eq_sum_blockCost]
      apply Finset.sum_lt_sum
      · intro r _
        exact hallWeak r
      · exact ⟨x, Finset.mem_univ x, hstrictBlock⟩
    have hmedAgainstExact := hemed (⟨x, 0⟩ : EnsembleIndex S)
    rw [hexact] at hmedAgainstExact
    exact (not_lt_of_ge hmedAgainstExact) hcostStrict

end PhdThesisLean.Medoid
