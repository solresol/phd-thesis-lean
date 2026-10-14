/-
  Formalisation of the "Sparse junta case" corollary from Greg Baker's PhD
  thesis.

  Thesis source: pac-learning-open-questions/body.tex
  Thesis label: unlabelled corollary "Sparse junta case", stated immediately
  after `thm:sparse-medoid-representation`.
-/

import PhdThesisLean.SparseMedoid

namespace PhdThesisLean.SparseJunta

open scoped BigOperators
open PhdThesisLean.Medoid

/-!
# Sparse junta case of the sparse medoid representation theorem

Thesis source: `pac-learning-open-questions/body.tex` in the thesis repository
(`/Users/gregb/Documents/devel/phd-thesis`), the corollary "Sparse junta case"
(unlabelled) that follows `thm:sparse-medoid-representation`, together with
the surrounding definitions of `v_K`, `ν_S` and local sparse non-expansiveness.

Thesis statement. Suppose `F(x) = H(x_T)` for some `T ⊆ {1, …, d}` with
`|T| ≤ s`, and `H : R_K^T → R_K` is non-expansive,
`v_K(H(u) − H(v)) ≥ min_{j ∈ T} v_K(u_j − v_j)`. Then `F` is represented
exactly by a medoid ensemble whose regressors use only the features in `T`.

Headline declarations.

* `NonExpansive p K H` is the divisibility form of non-expansiveness of a
  map `H : (ι → RK p K) → RK p K` (`ι` any finite index type, in particular
  `↥T`): whenever every coordinate difference `u j - v j` is a multiple of
  `p ^ t` (with `t ≤ K`), so is `H u - H v`. `NonExpansiveVal p K H` is the
  thesis's valuation form `ν_ι(u − v) ≤ v_K(H u − H v)` using the truncated
  valuation `truncatedVal` and `minVal` (the thesis's `ν`, with `ν_∅ = K`).
  `nonExpansive_iff_val` shows the two forms are equivalent.
* `juntaF T H x = H (fun j : T ↦ x j)` is the junta `F(x) = H(x_T)`.
* `junta_locallySparseNonexpansive`: a junta on `T` with `|T| ≤ s` and
  non-expansive `H` is locally `s`-sparse non-expansive with the constant
  active set `S r = T`. This is the thesis remark that a single global sparse
  junta is a special case of local sparsity.
* `sparse_junta_case`: the corollary. For every input `x`, the medoid ensemble
  `{ H(r_T) + ∑_{j ∈ T} a_j (x_j − r_j) : r ∈ R_K^d, a ∈ R_K^T }` has the
  regressor with centre `x` and zero slopes as a medoid, its value is
  `F x = H(x_T)`, every medoid outputs `F x`, and every regressor in the
  ensemble depends on its input only through the coordinates in `T`.

Correspondence notes.

* The ensemble is exactly the one of `thm:sparse-medoid-representation`
  specialised to the constant active set `S r = T`, so each regressor's slope
  vector is indexed by `↥T` (by the type of `EnsembleIndex (fun _ ↦ T)`), and
  `ensembleOutput_junta_congr` records that the output of every regressor is
  unchanged when the input is modified outside `T`.
* The thesis convention `v_K(0) = K` and `ν_∅ = K` is matched by
  `truncatedVal` (from `SparseMedoid`) and `minVal` here.
* Non-expansiveness is formalised for an arbitrary finite index type `ι`, of
  which the thesis's `R_K^T` is the case `ι = ↥T`; this is a harmless
  generalisation.
* The hypothesis `1 ≤ K` is inherited from the signature of
  `sparse_medoid_representation` (where it is unused); it only expresses that
  the working precision is at least one digit.
* `exists_unit_of_truncatedVal_lt` is the standard fact that an element of
  `ZMod (p ^ K)` of truncated valuation `t < K` factors as `p ^ t` times a
  unit; it is proved here from `ZMod.isUnit_iff_coprime`.
-/

section Valuation

variable {p K : ℕ} {ι : Type*} [Fintype ι]

/-- The thesis's `ν`: the minimum truncated valuation of the coordinates of
`w`, with the convention that an empty index type gives `K`. -/
noncomputable def minVal (p K : ℕ) (w : ι → RK p K) : ℕ :=
  if h : (Finset.univ : Finset ι).Nonempty then
    Finset.univ.inf' h (fun j ↦ truncatedVal p K (w j))
  else K

theorem minVal_le_truncatedVal (w : ι → RK p K) (j : ι) :
    minVal p K w ≤ truncatedVal p K (w j) := by
  unfold minVal
  rw [dif_pos ⟨j, Finset.mem_univ j⟩]
  exact Finset.inf'_le _ (Finset.mem_univ j)

theorem minVal_le (w : ι → RK p K) : minVal p K w ≤ K := by
  unfold minVal
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    exact (Finset.inf'_le _ hj).trans (truncatedVal_le p K _)
  · exact le_rfl

theorem minVal_of_isEmpty [IsEmpty ι] (w : ι → RK p K) : minVal p K w = K := by
  unfold minVal
  rw [dif_neg]
  rw [Finset.univ_nonempty_iff]
  exact not_nonempty_iff.mpr inferInstance

theorem le_minVal_iff {t : ℕ} (w : ι → RK p K) :
    t ≤ minVal p K w ↔ t ≤ K ∧ ∀ j, t ≤ truncatedVal p K (w j) := by
  unfold minVal
  split_ifs with h
  · rw [Finset.le_inf'_iff]
    constructor
    · intro hall
      obtain ⟨j, hj⟩ := h
      exact ⟨(hall j hj).trans (truncatedVal_le p K _),
        fun j ↦ hall j (Finset.mem_univ j)⟩
    · rintro ⟨-, hall⟩ j _
      exact hall j
  · rw [Finset.univ_nonempty_iff, not_nonempty_iff] at h
    exact ⟨fun ht ↦ ⟨ht, fun j ↦ (h.false j).elim⟩, fun h ↦ h.1⟩

theorem exists_truncatedVal_eq_minVal [Nonempty ι] (w : ι → RK p K) :
    ∃ j, truncatedVal p K (w j) = minVal p K w := by
  unfold minVal
  rw [dif_pos Finset.univ_nonempty]
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun j ↦ truncatedVal p K (w j))
  exact ⟨j, hj.symm⟩

theorem multipleAt_of_le_minVal {t : ℕ} (w : ι → RK p K)
    (ht : t ≤ minVal p K w) (j : ι) : MultipleAt p K t (w j) :=
  (multipleAt_iff_le_truncatedVal (ht.trans (minVal_le w)) _).mpr
    (ht.trans (minVal_le_truncatedVal w j))

theorem multipleAt_minVal (w : ι → RK p K) (j : ι) :
    MultipleAt p K (minVal p K w) (w j) :=
  multipleAt_of_le_minVal w le_rfl j

theorem le_minVal_of_multipleAt {t : ℕ} (ht : t ≤ K) (w : ι → RK p K)
    (hall : ∀ j, MultipleAt p K t (w j)) : t ≤ minVal p K w :=
  (le_minVal_iff w).mpr
    ⟨ht, fun j ↦ (multipleAt_iff_le_truncatedVal ht _).mp (hall j)⟩

/-- `ν(w) ≥ t` (for `t ≤ K`) is exactly `w_j ≡ 0 (mod p^t)` for every `j`,
the thesis's "equivalently" remark. -/
theorem le_minVal_iff_multipleAt {t : ℕ} (ht : t ≤ K) (w : ι → RK p K) :
    t ≤ minVal p K w ↔ ∀ j, MultipleAt p K t (w j) :=
  ⟨multipleAt_of_le_minVal w, le_minVal_of_multipleAt ht w⟩

/-- An element of `ZMod (p ^ K)` whose truncated valuation `t` is below the
precision `K` factors as `p ^ t` times a unit. -/
theorem exists_unit_of_truncatedVal_lt [Fact p.Prime] {u : RK p K}
    (h : truncatedVal p K u < K) :
    ∃ w : RK p K, IsUnit w ∧ u = (p : RK p K) ^ truncatedVal p K u * w := by
  obtain ⟨c, hc⟩ := multipleAt_truncatedVal p K u
  refine ⟨c, ?_, hc⟩
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.ne_zero⟩
  by_contra hunit
  rw [← ZMod.natCast_zmod_val c, ZMod.isUnit_iff_coprime,
    Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm,
    hp.coprime_iff_not_dvd, not_not] at hunit
  obtain ⟨m, hm⟩ := hunit
  have hcm : c = (p : RK p K) * (m : RK p K) := by
    rw [← ZMod.natCast_zmod_val c, hm, Nat.cast_mul]
  have hnext : MultipleAt p K (truncatedVal p K u + 1) u := by
    refine ⟨m, ?_⟩
    calc u = (p : RK p K) ^ truncatedVal p K u * c := hc
      _ = (p : RK p K) ^ (truncatedVal p K u + 1) * m := by
        rw [hcm, pow_succ]; ring
  rw [multipleAt_iff_le_truncatedVal h] at hnext
  omega

end Valuation

section NonExpansive

variable {p K : ℕ} {ι : Type*} [Fintype ι]

/-- Divisibility form of non-expansiveness: if every coordinate difference is
a multiple of `p ^ t` then so is the difference of outputs. -/
def NonExpansive (p K : ℕ) (H : (ι → RK p K) → RK p K) : Prop :=
  ∀ t ≤ K, ∀ u v : ι → RK p K,
    (∀ j, MultipleAt p K t (u j - v j)) → MultipleAt p K t (H u - H v)

/-- The thesis's valuation form of non-expansiveness:
`v_K(H(u) − H(v)) ≥ min_j v_K(u_j − v_j)`. -/
def NonExpansiveVal (p K : ℕ) (H : (ι → RK p K) → RK p K) : Prop :=
  ∀ u v : ι → RK p K,
    minVal p K (fun j ↦ u j - v j) ≤ truncatedVal p K (H u - H v)

theorem nonExpansive_iff_val (H : (ι → RK p K) → RK p K) :
    NonExpansive p K H ↔ NonExpansiveVal p K H := by
  constructor
  · intro hH u v
    have ht := minVal_le (p := p) (K := K) (fun j ↦ u j - v j)
    exact (multipleAt_iff_le_truncatedVal ht _).mp
      (hH _ ht u v (multipleAt_minVal _))
  · intro hH t ht u v hall
    exact (multipleAt_iff_le_truncatedVal ht _).mpr
      ((le_minVal_of_multipleAt ht _ hall).trans (hH u v))

end NonExpansive

section Junta

variable {p K d : ℕ}

/-- Restriction of an input to the coordinates in `T`: the thesis's `x_T`. -/
def restrict (T : Finset (Fin d)) (x : Fin d → RK p K) : T → RK p K :=
  fun j ↦ x j

/-- The junta `F(x) = H(x_T)`. -/
def juntaF (T : Finset (Fin d)) (H : (T → RK p K) → RK p K) :
    (Fin d → RK p K) → RK p K :=
  fun x ↦ H (restrict T x)

theorem juntaF_apply (T : Finset (Fin d)) (H : (T → RK p K) → RK p K)
    (x : Fin d → RK p K) : juntaF T H x = H (fun j : T ↦ x j) := rfl

theorem restrict_eq_of_agree (T : Finset (Fin d)) {x y : Fin d → RK p K}
    (hxy : ∀ j ∈ T, x j = y j) : restrict T x = restrict T y := by
  funext j
  exact hxy j j.2

theorem juntaF_congr (T : Finset (Fin d)) (H : (T → RK p K) → RK p K)
    {x y : Fin d → RK p K} (hxy : ∀ j ∈ T, x j = y j) :
    juntaF T H x = juntaF T H y := by
  unfold juntaF
  rw [restrict_eq_of_agree T hxy]

/-- A single global sparse junta is locally sparse non-expansive with the
constant active set `S r = T`. -/
theorem junta_locallySparseNonexpansive [Fact p.Prime] {s : ℕ}
    (T : Finset (Fin d)) (hT : T.card ≤ s)
    (H : (T → RK p K) → RK p K) (hH : NonExpansive p K H) :
    LocallySparseNonexpansive (juntaF T H) (fun _ ↦ T) s := by
  refine ⟨fun _ ↦ hT, ?_⟩
  intro r x
  let w : T → RK p K := fun j ↦ x j - r j
  refine ⟨minVal p K w, minVal_le w, ?_, ?_, ?_⟩
  · intro j hj
    exact multipleAt_minVal w ⟨j, hj⟩
  · by_cases ht : minVal p K w = K
    · exact Or.inl ht
    · right
      have hlt : minVal p K w < K := lt_of_le_of_ne (minVal_le w) ht
      haveI hne : Nonempty T := by
        by_contra hempty
        rw [not_nonempty_iff] at hempty
        exact ht (minVal_of_isEmpty w)
      obtain ⟨j, hj⟩ := exists_truncatedVal_eq_minVal w
      obtain ⟨c, hc, hcu⟩ := exists_unit_of_truncatedVal_lt (hj ▸ hlt)
      refine ⟨j.1, j.2, c, hc, ?_⟩
      rw [hj] at hcu
      exact hcu
  · exact hH _ (minVal_le w) (restrict T x) (restrict T r) (multipleAt_minVal w)

/-- Explicit form of a regressor of the junta ensemble: it depends on the
input `x` only through the coordinates `x j`, `j ∈ T`. -/
theorem ensembleOutput_junta (T : Finset (Fin d)) (H : (T → RK p K) → RK p K)
    (x : Fin d → RK p K) (e : EnsembleIndex (fun _ : Fin d → RK p K ↦ T)) :
    ensembleOutput (juntaF T H) (fun _ ↦ T) x e =
      H (restrict T e.1) + ∑ j : T, e.2 j * (x j - e.1 j) := rfl

/-- Every regressor of the junta ensemble uses only the features in `T`:
its output is unchanged by modifying the input outside `T`. -/
theorem ensembleOutput_junta_congr (T : Finset (Fin d))
    (H : (T → RK p K) → RK p K) {x y : Fin d → RK p K}
    (hxy : ∀ j ∈ T, x j = y j) (e : EnsembleIndex (fun _ : Fin d → RK p K ↦ T)) :
    ensembleOutput (juntaF T H) (fun _ ↦ T) x e =
      ensembleOutput (juntaF T H) (fun _ ↦ T) y e := by
  rw [ensembleOutput_junta, ensembleOutput_junta]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hxy j j.2]

/-- **Sparse junta case.** If `F x = H (x_T)` with `|T| ≤ s` and `H`
non-expansive, then for every input `x` the medoid ensemble of affine
regressors `H(r_T) + ∑_{j ∈ T} a_j (x_j − r_j)` (centres `r ∈ R_K^d`, slopes
`a ∈ R_K^T`) represents `F` exactly: every regressor uses only the features in
`T`, the regressor with centre `x` and zero slopes outputs `F x = H (x_T)`
and is a medoid, and every medoid outputs `F x`. -/
theorem sparse_junta_case (p K d s : ℕ) [Fact p.Prime] (hK : 1 ≤ K)
    (T : Finset (Fin d)) (hT : T.card ≤ s)
    (H : (T → RK p K) → RK p K) (hH : NonExpansive p K H)
    (x : Fin d → RK p K) :
    (∀ e : EnsembleIndex (fun _ : Fin d → RK p K ↦ T),
      ∀ y : Fin d → RK p K, (∀ j ∈ T, y j = x j) →
        ensembleOutput (juntaF T H) (fun _ ↦ T) y e =
          ensembleOutput (juntaF T H) (fun _ ↦ T) x e) ∧
    ensembleOutput (juntaF T H) (fun _ ↦ T) x ⟨x, 0⟩ = H (restrict T x) ∧
    IsEnsembleMedoid (juntaF T H) (fun _ ↦ T) x ⟨x, 0⟩ ∧
    ∀ e : EnsembleIndex (fun _ : Fin d → RK p K ↦ T),
      IsEnsembleMedoid (juntaF T H) (fun _ ↦ T) x e →
        ensembleOutput (juntaF T H) (fun _ ↦ T) x e = H (restrict T x) := by
  obtain ⟨-, hexact, hmed, huniq⟩ :=
    sparse_medoid_representation p K d s hK (juntaF T H) (fun _ ↦ T)
      (junta_locallySparseNonexpansive T hT H hH) x
  refine ⟨fun e y hyx ↦ ensembleOutput_junta_congr T H hyx e, hexact, hmed, huniq⟩

end Junta

end PhdThesisLean.SparseJunta

#print axioms PhdThesisLean.SparseJunta.sparse_junta_case
#print axioms PhdThesisLean.SparseJunta.junta_locallySparseNonexpansive
#print axioms PhdThesisLean.SparseJunta.nonExpansive_iff_val
#print axioms PhdThesisLean.SparseJunta.exists_unit_of_truncatedVal_lt
