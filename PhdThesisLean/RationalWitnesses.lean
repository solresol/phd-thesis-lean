import PhdThesisLean.RegularisedCandidates

/-!
# Rational contact witnesses for arbitrary summed regression

Source: `complexity-regimes/eth-addendum.tex`, `prop:regression-np-complete`.
This module proves the semantic independent-column and contact-refinement
steps over rational inputs. No coefficient-size or machine-time bound is
asserted. Rows are indexed, so repetitions and conflicting targets remain.
-/

namespace PhdThesisLean.RationalWitnesses

open scoped BigOperators Matrix
open RegularisedCandidates

/-- Ordinary summed rational p-adic regression, with matrix times coefficient
vector minus target as residual (the norm is unchanged by reversing the sign). -/
def loss (p : ℕ) {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (β : Fin d → ℚ) : ℚ :=
  ∑ i, padicNorm p (hres A y β i)

/-- Exact correspondence with the residual sign used in the thesis. -/
theorem loss_eq_thesis (p : ℕ) {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (β : Fin d → ℚ) :
    loss p A y β = ∑ i, padicNorm p (y i - (A *ᵥ β) i) := by
  apply Finset.sum_congr rfl
  intro i _
  change padicNorm p ((A *ᵥ β) i - y i) = _
  rw [← neg_sub (y i) ((A *ᵥ β) i), padicNorm.neg]

/-- Retain the indicated distinct columns, in their specified order. -/
def columns {r d s : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (e : Fin s ↪ Fin d) : Matrix (Fin r) (Fin s) ℚ :=
  fun i j => A i (e j)

/-- Embed reduced coefficients, filling unselected coordinates with zero. -/
def extend {d s : ℕ} (e : Fin s ↪ Fin d) (γ : Fin s → ℚ) : Fin d → ℚ :=
  ∑ j, γ j • Pi.single (e j) 1

theorem extend_apply {d s : ℕ} (e : Fin s ↪ Fin d) (γ : Fin s → ℚ) (j : Fin s) :
    extend e γ (e j) = γ j := by
  simp [extend, Pi.single_apply, e.injective.eq_iff]

theorem extend_eq_zero {d s : ℕ} (e : Fin s ↪ Fin d) (γ : Fin s → ℚ)
    (j : Fin d) (hj : j ∉ Set.range e) : extend e γ j = 0 := by
  have hne : ∀ i, e i ≠ j := fun i h => hj ⟨i, h⟩
  simp [extend, hne]

theorem mulVec_extend {r d s : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (e : Fin s ↪ Fin d) (γ : Fin s → ℚ) :
    A *ᵥ extend e γ = columns A e *ᵥ γ := by
  ext i
  simp [extend, Matrix.mulVec, dotProduct, Finset.mul_sum,
    Finset.sum_comm, columns, Pi.single_apply, mul_comm]

/-- Independent columns span exactly the original prediction space. This
includes rank zero: the selected index type is then empty. -/
theorem exists_column_reduction {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ) :
    ∃ s : ℕ, ∃ e : Fin s ↪ Fin d,
      s = A.rank ∧ LinearIndependent ℚ (columns A e).col ∧
      LinearMap.range (columns A e).mulVecLin = LinearMap.range A.mulVecLin := by
  classical
  obtain ⟨ι, a, ha, hspan, hind⟩ := exists_linearIndependent' ℚ A.col
  let : Finite ι := Finite.of_injective a ha
  let : Fintype ι := Fintype.ofFinite ι
  let q := (Fintype.equivFin ι).symm
  let e : Fin (Fintype.card ι) ↪ Fin d := ⟨a ∘ q, ha.comp q.injective⟩
  have hcol : (columns A e).col = (A.col ∘ a) ∘ q := rfl
  have hli : LinearIndependent ℚ (columns A e).col := by
    rw [hcol]
    exact hind.comp q q.injective
  have hrange : LinearMap.range (columns A e).mulVecLin =
      LinearMap.range A.mulVecLin := by
    rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin, hcol,
      q.surjective.range_comp, hspan]
  refine ⟨Fintype.card ι, e, ?_, hli, hrange⟩
  have hd := LinearMap.finrank_range_of_inj (f := (columns A e).mulVecLin)
    (Matrix.mulVec_injective_iff.mpr hli)
  calc
    Fintype.card ι = Module.finrank ℚ (Fin (Fintype.card ι) → ℚ) := by simp
    _ = Module.finrank ℚ (LinearMap.range (columns A e).mulVecLin) := hd.symm
    _ = A.rank := by rw [hrange]; rfl

/-- Full column independence is precisely the non-degeneracy needed by the
existing homogeneous contact-lifting theorem. -/
theorem not_degenerate_of_columns_independent {r s : ℕ}
    (C : Matrix (Fin r) (Fin s) ℚ) (hC : LinearIndependent ℚ C.col) :
    ¬ HDegenerate C := by
  rintro ⟨φ, hφ, hz⟩
  apply hφ
  apply Matrix.mulVec_injective_iff.mpr hC
  ext i
  simpa [Matrix.mulVec] using hz i

/-- Every prediction has reduced coordinates, without a rank assumption. -/
theorem exists_reduced_prediction {r d s : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (e : Fin s ↪ Fin d)
    (hspan : LinearMap.range (columns A e).mulVecLin = LinearMap.range A.mulVecLin)
    (β : Fin d → ℚ) : ∃ γ, columns A e *ᵥ γ = A *ᵥ β := by
  have hmem : A *ᵥ β ∈ LinearMap.range (columns A e).mulVecLin := by
    rw [hspan]
    exact ⟨β, rfl⟩
  exact hmem

/-- On any independent column basis, contact refinement produces a sparse
coefficient vector with no larger residual norm at any original row. -/
theorem contact_refinement (p : ℕ) [Fact p.Prime] {r d s : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (e : Fin s ↪ Fin d)
    (hind : LinearIndependent ℚ (columns A e).col)
    (hspan : LinearMap.range (columns A e).mulVecLin = LinearMap.range A.mulVecLin)
    (β : Fin d → ℚ) :
    ∃ I : Finset (Fin r), ∃ γ : Fin s → ℚ,
      I.card = s ∧ HIndependent (columns A e) I ∧ HFitsOn (columns A e) y I γ ∧
      (∀ i, padicNorm p (hres A y (extend e γ) i) ≤ padicNorm p (hres A y β i)) ∧
      loss p A y (extend e γ) ≤ loss p A y β := by
  obtain ⟨θ, hθ⟩ := exists_reduced_prediction A e hspan β
  obtain ⟨I, γ, hcard, hI, hfit, hnorm⟩ :=
    hindependent_contact_refinement p (columns A e) y θ
      (not_degenerate_of_columns_independent _ hind)
  have hres_extend : ∀ i, hres A y (extend e γ) i = hres (columns A e) y γ i := by
    intro i
    exact congrArg (fun z : Fin r → ℚ => z i - y i) (mulVec_extend A e γ)
  have hres_θ : ∀ i, hres (columns A e) y θ i = hres A y β i := by
    intro i
    exact congrArg (fun z : Fin r → ℚ => z i - y i) hθ
  have hn : ∀ i, padicNorm p (hres A y (extend e γ) i) ≤ padicNorm p (hres A y β i) := by
    intro i
    rw [hres_extend, ← hres_θ]
    exact hnorm i
  exact ⟨I, γ, hcard, hI, hfit, hn, Finset.sum_le_sum fun i _ => hn i⟩

/-- The data-only family of zero-extended full independent interpolants. -/
def candidateModels {r d s : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (e : Fin s ↪ Fin d) : Set (Fin d → ℚ) :=
  extend e '' HCandidateModels (columns A e) y

theorem finite_candidateModels {r d s : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (e : Fin s ↪ Fin d) : (candidateModels A y e).Finite :=
  (hfinite_candidateModels (columns A e) y).image (extend e)

/-- Every rational model is pointwise dominated by a member of the finite
contact family, with no assumptions on the original design's rank or rows. -/
theorem exists_candidate_le (p : ℕ) [Fact p.Prime] {r d s : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (e : Fin s ↪ Fin d)
    (hind : LinearIndependent ℚ (columns A e).col)
    (hspan : LinearMap.range (columns A e).mulVecLin = LinearMap.range A.mulVecLin)
    (β : Fin d → ℚ) :
    ∃ β' ∈ candidateModels A y e,
      (∀ i, padicNorm p (hres A y β' i) ≤ padicNorm p (hres A y β i)) ∧
      loss p A y β' ≤ loss p A y β := by
  obtain ⟨I, γ, hcard, hI, hfit, hn, hl⟩ := contact_refinement p A y e hind hspan β
  exact ⟨extend e γ, ⟨γ, ⟨I, hcard, hI, hfit⟩, rfl⟩, hn, hl⟩

/-- The threshold problem has a witness in the same finite family for every
rational bound, including negative bounds. This is a semantic equivalence. -/
theorem threshold_iff_candidate (p : ℕ) [Fact p.Prime] {r d s : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (e : Fin s ↪ Fin d)
    (hind : LinearIndependent ℚ (columns A e).col)
    (hspan : LinearMap.range (columns A e).mulVecLin = LinearMap.range A.mulVecLin)
    (B : ℚ) :
    (∃ β, loss p A y β ≤ B) ↔ ∃ β ∈ candidateModels A y e, loss p A y β ≤ B := by
  constructor
  · rintro ⟨β, hβ⟩
    obtain ⟨γ, hγ, _, hle⟩ := exists_candidate_le p A y e hind hspan β
    exact ⟨γ, hγ, hle.trans hβ⟩
  · rintro ⟨β, _, hβ⟩
    exact ⟨β, hβ⟩

/-- Semantic attainment step of `prop:regression-np-complete`: at every prime,
the global optimum occurs at a rational contact interpolant supported on a
basis of the original columns. Certificate size and runtime are separate. -/
theorem exists_global_minimizer (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) :
    ∃ s : ℕ, ∃ e : Fin s ↪ Fin d,
      s = A.rank ∧ LinearIndependent ℚ (columns A e).col ∧
      ∃ β ∈ candidateModels A y e, ∀ β', loss p A y β ≤ loss p A y β' := by
  classical
  obtain ⟨s, e, hs, hind, hspan⟩ := exists_column_reduction A
  have hdom := exists_candidate_le p A y e hind hspan
  have hne : (candidateModels A y e).Nonempty := by
    obtain ⟨β, hβ, _⟩ := hdom 0
    exact ⟨β, hβ⟩
  obtain ⟨β, hβ, hmin⟩ := Set.exists_min_image _ (loss p A y)
    (finite_candidateModels A y e) hne
  refine ⟨s, e, hs, hind, β, hβ, fun β' => ?_⟩
  obtain ⟨γ, hγ, _, hle⟩ := hdom β'
  exact (hmin γ hγ).trans hle

/-- A full independent contact set supplies an invertible square row minor
and the exact Cramer formula for its coefficients. No size bound is hidden
in the word "interpolant". -/
theorem contact_cramer {r s : ℕ} (C : Matrix (Fin r) (Fin s) ℚ)
    (y : Fin r → ℚ) (I : Finset (Fin r)) (γ : Fin s → ℚ)
    (hcard : I.card = s) (hind : HIndependent C I) (hfit : HFitsOn C y I γ) :
    ∃ f : Fin s ↪ Fin r,
      (∀ i, f i ∈ I) ∧ (C.submatrix f id).det ≠ 0 ∧
      ∀ j, γ j = ((C.submatrix f id).updateCol j (y ∘ f)).det /
        (C.submatrix f id).det := by
  classical
  let q : Fin s ≃ I := (I.equivFinOfCardEq hcard).symm
  let f : Fin s ↪ Fin r := ⟨fun i => (q i).val, Subtype.val_injective.comp q.injective⟩
  let D : Matrix (Fin s) (Fin s) ℚ := C.submatrix f id
  have hrow : LinearIndependent ℚ D.row := by
    exact hind.comp q q.injective
  have hdet : D.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det D).mp (Matrix.linearIndependent_row_iff_isUnit.mp hrow)).ne_zero
  have hmul : D *ᵥ γ = y ∘ f := by
    ext i
    exact sub_eq_zero.mp (hfit (f i) (q i).property)
  have hcramer : D.cramer (y ∘ f) = D.det • γ := by
    rw [← hmul, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  refine ⟨f, fun i => (q i).property, hdet, fun j => ?_⟩
  apply (eq_div_iff hdet).mpr
  have hj := congrFun hcramer j
  simpa [Matrix.cramer_apply, smul_eq_mul, mul_comm] using hj.symm

/-- A global optimum can be selected as a zero-extended Cramer solution
of a nonsingular minor of size exactly `rank A`. This is the algebraic input
for a future determinant bit-length bound, not such a bound itself. -/
theorem exists_global_minimizer_cramer (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) :
    ∃ s : ℕ, ∃ e : Fin s ↪ Fin d, ∃ f : Fin s ↪ Fin r, ∃ γ : Fin s → ℚ,
      s = A.rank ∧ (A.submatrix f e).det ≠ 0 ∧
      (∀ j, γ j = ((A.submatrix f e).updateCol j (y ∘ f)).det /
        (A.submatrix f e).det) ∧
      (∀ j, j ∉ Set.range e → extend e γ j = 0) ∧
      ∀ β, loss p A y (extend e γ) ≤ loss p A y β := by
  obtain ⟨s, e, hs, _, β, ⟨γ, ⟨I, hcard, hind, hfit⟩, rfl⟩, hmin⟩ :=
    exists_global_minimizer p A y
  obtain ⟨f, _, hdet, hformula⟩ := contact_cramer (columns A e) y I γ hcard hind hfit
  exact ⟨s, e, f, γ, hs, hdet, hformula, extend_eq_zero e γ, hmin⟩

/-- Adding a column of ones gives exactly the affine objective. -/
theorem loss_affineDesign (p : ℕ) {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (c : ℚ) (β : Fin d → ℚ) :
    loss p (affineDesign A) y (Fin.cons c β) =
      ∑ i, padicNorm p (y i - ((A *ᵥ β) i + c)) := by
  rw [loss_eq_thesis p (affineDesign A) y (Fin.cons c β)]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  simp [affineDesign, ContactTheorem.augment, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, add_comm]

/-- Affine semantic attainment follows by appending the column of ones;
arbitrary rank and repeated rows remain permitted. -/
theorem exists_affine_global_minimizer (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) :
    ∃ c : ℚ, ∃ β : Fin d → ℚ, ∀ c' : ℚ, ∀ β' : Fin d → ℚ,
      (∑ i, padicNorm p (y i - ((A *ᵥ β) i + c))) ≤
        ∑ i, padicNorm p (y i - ((A *ᵥ β') i + c')) := by
  obtain ⟨_, _, _, _, θ, _, hmin⟩ := exists_global_minimizer p (affineDesign A) y
  refine ⟨θ 0, fun i => θ i.succ, fun c' β' => ?_⟩
  have hθ : Fin.cons (θ 0) (fun i => θ i.succ) = θ := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [← loss_affineDesign, hθ, ← loss_affineDesign]
  exact hmin (Fin.cons c' β')

#print axioms exists_column_reduction
#print axioms contact_refinement
#print axioms finite_candidateModels
#print axioms threshold_iff_candidate
#print axioms exists_global_minimizer
#print axioms contact_cramer
#print axioms exists_global_minimizer_cramer
#print axioms exists_affine_global_minimizer

end PhdThesisLean.RationalWitnesses
