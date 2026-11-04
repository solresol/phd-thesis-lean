import PhdThesisLean.SmithPivotBounds
import PhdThesisLean.RationalWitnessBounds

/-!
# Reducing the Smith growth obligation to the forward transformations

For an integral state satisfying the existing inverse and transformation
identities, bounds on `U,V` imply bounds on both inverses and `S`. The inverse
entries are signed cofactors because the determinant is a unit. Reuse the
existing determinant bit bound rather than introduce another determinant core.

These are conditional size bounds, also for every actual trace prefix. No
global forward-map bound for the diagonalizer or encoded-machine cost is
assumed to have been proved here.
-/

namespace PhdThesisLean.SmithForwardBounds

open Matrix SmithTrace SmithPivotBounds SmithEncoding SmithDecomposition
open scoped BigOperators

variable {m n k : ℕ}

/-- The row-replacement formula bounds each cofactor without nonempty guards. -/
theorem adjugate_natAbs_le_pow (A : Matrix (Fin m) (Fin m) ℤ) (d : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ d) :
    ∀ i j, (A.adjugate i j).natAbs ≤ 2 ^ (m * (d + m.size)) := by
  intro i j
  rw [Matrix.adjugate_apply]
  apply RationalWitnessBounds.det_natAbs_le_pow
  intro r c
  by_cases hr : r = j
  · subst r
    by_cases hc : c = i
    · subst c
      simpa using Nat.one_le_pow d 2 (by decide)
    · simp [Matrix.updateRow, hc]
  · simpa [Matrix.updateRow, hr] using hA r c

/-- A supplied integral left inverse is the adjugate up to a unit sign.
This is a theorem about an existing inverse, not an inverse algorithm. -/
theorem inverse_entry_natAbs_eq_adjugate (A B : Matrix (Fin m) (Fin m) ℤ)
    (hBA : B * A = 1) (i j : Fin m) :
    (B i j).natAbs = (A.adjugate i j).natAbs := by
  have hdet : A.det.natAbs = 1 :=
    Int.isUnit_iff_natAbs_eq.mp (Matrix.isUnit_det_of_left_inverse hBA)
  have hadj : A.adjugate = A.det • B := by
    calc
      A.adjugate = (B * A) * A.adjugate := by rw [hBA, Matrix.one_mul]
      _ = B * (A * A.adjugate) := Matrix.mul_assoc _ _ _
      _ = B * (A.det • 1) := by rw [Matrix.mul_adjugate]
      _ = A.det • B := by rw [Matrix.mul_smul, Matrix.mul_one]
  rw [hadj]
  simp only [Matrix.smul_apply, smul_eq_mul, Int.natAbs_mul, hdet, one_mul]

/-- Inverse widths need no independent growth recurrence once a forward map
is bounded and the integral inverse identity is established. -/
theorem inverse_natAbs_le_pow (A B : Matrix (Fin m) (Fin m) ℤ) (d : ℕ)
    (hBA : B * A = 1) (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ d) :
    ∀ i j, (B i j).natAbs ≤ 2 ^ (m * (d + m.size)) := by
  intro i j
  rw [inverse_entry_natAbs_eq_adjugate A B hBA]
  exact adjugate_natAbs_le_pow A d hA i j

/-- A rectangular matrix product pays for every summand, including an empty
inner dimension. This is an arithmetic bound, not a multiplication machine. -/
theorem mul_entry_natAbs_le (A : Matrix (Fin m) (Fin k) ℤ)
    (B : Matrix (Fin k) (Fin n) ℤ) (H K : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ H) (hB : ∀ i j, (B i j).natAbs ≤ K) :
    ∀ i j, ((A * B) i j).natAbs ≤ k * (H * K) := by
  intro i j
  calc
    ((A * B) i j).natAbs ≤ ∑ l : Fin k, (A i l * B l j).natAbs := by
      simpa only [Matrix.mul_apply] using
        Int.natAbs_sum_le Finset.univ (fun l : Fin k => A i l * B l j)
    _ ≤ ∑ _l : Fin k, H * K := by
      apply Finset.sum_le_sum
      intro l _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hA i l) (hB l j)
    _ = k * (H * K) := by simp

/-- One common polynomial exponent in actual input bits `s` and a proposed
forward-map exponent `d`. It does not assert that `d` is globally bounded. -/
def stateWidth (s d : ℕ) : ℕ := (s + 2) * (d + s + 1)

/-- A polynomial forward-map invariant would suffice for all five matrices.
The hypotheses do not assume a bound on either inverse or the transformed
matrix. Unary dimension costs are essential to the specialization below. -/
theorem bounded_of_forward (A : Matrix (Fin m) (Fin n) ℤ) (Q : State m n)
    (s d : ℕ) (hm : m ≤ s) (hn : n ≤ s) (hQ : Invariant A Q)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ s)
    (hU : ∀ i j, (Q.U i j).natAbs ≤ 2 ^ d)
    (hV : ∀ i j, (Q.V i j).natAbs ≤ 2 ^ d) :
    Bounded Q (2 ^ stateWidth s d) := by
  have hsize (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self
  have hi (a : ℕ) (ha : a ≤ s) : a * (d + a.size) ≤ stateWidth s d := by
    have hs := hsize a
    dsimp [stateWidth]
    nlinarith
  have hd : d ≤ stateWidth s d := by dsimp [stateWidth]; nlinarith
  have hs : 2 * d + 3 * s ≤ stateWidth s d := by dsimp [stateWidth]; nlinarith
  have hdim (a : ℕ) (ha : a ≤ s) : a ≤ 2 ^ s :=
    ha.trans ((Nat.lt_size_self s).le.trans
      (Nat.pow_le_pow_right (by decide) (hsize s)))
  refine ⟨fun i j => (hU i j).trans (Nat.pow_le_pow_right (by decide) hd),
    fun i j => (inverse_natAbs_le_pow Q.U Q.Uinv d hQ.Uinv_U hU i j).trans
      (Nat.pow_le_pow_right (by decide) (hi m hm)),
    fun i j => (hV i j).trans (Nat.pow_le_pow_right (by decide) hd),
    fun i j => (inverse_natAbs_le_pow Q.V Q.Vinv d hQ.Vinv_V hV i j).trans
      (Nat.pow_le_pow_right (by decide) (hi n hn)), ?_⟩
  intro i j
  rw [← hQ.transformed]
  have hUA := mul_entry_natAbs_le Q.U A _ _ hU hA
  have hUAV := mul_entry_natAbs_le (Q.U * A) Q.V _ _ hUA hV i j
  calc
    ((Q.U * A * Q.V) i j).natAbs ≤ n * (m * (2 ^ d * 2 ^ s) * 2 ^ d) := hUAV
    _ ≤ 2 ^ s * (2 ^ s * (2 ^ d * 2 ^ s) * 2 ^ d) := by
      gcongr
      · exact hdim n hn
      · exact hdim m hm
    _ = 2 ^ (2 * d + 3 * s) := by
      simp only [← pow_add]
      congr 1
      ring
    _ ≤ 2 ^ stateWidth s d := Nat.pow_le_pow_right (by decide) hs

/-- Charge the incoming entries and dimensions to their complete existing
signed/framed binary encoding; do not switch to a unit-cost matrix model. -/
theorem bounded_of_input_forward (A : Dense) (Q : State A.rows A.cols) (d : ℕ)
    (hQ : Invariant A.toMatrix Q)
    (hU : ∀ i j, (Q.U i j).natAbs ≤ 2 ^ d)
    (hV : ∀ i j, (Q.V i j).natAbs ≤ 2 ^ d) :
    Bounded Q (2 ^ stateWidth (SmithEncoding.encode A).length d) := by
  have hd := dimensions_le_length A
  exact bounded_of_forward A.toMatrix Q _ d (by omega) (by omega) hQ
    (fun i j => (Nat.size_le.mp
      (SmithIsolationCount.entry_size_le_input_length A i j)).le) hU hV

/-- Apply the implication to an actual prefix, including unfinished swaps.
Proving the two forward-map hypotheses uniformly is still the global gap. -/
theorem trace_prefix_bound (A : Dense) (ops : List (Op A.rows A.cols)) (t d : ℕ)
    (hU : ∀ i j, ((run (initial A.toMatrix) (ops.take t)).U i j).natAbs ≤ 2 ^ d)
    (hV : ∀ i j, ((run (initial A.toMatrix) (ops.take t)).V i j).natAbs ≤ 2 ^ d) :
    Bounded (run (initial A.toMatrix) (ops.take t))
      (2 ^ stateWidth (SmithEncoding.encode A).length d) :=
  bounded_of_input_forward A _ d (run_invariant (initial_invariant A.toMatrix) _) hU hV

/-- Conditional full-output size, including both inverses, signs, field frames
and dimensions. This supplies no global forward bound or serializer runtime. -/
theorem output_length_le_of_forward (A : Dense) (Q : State A.rows A.cols) (d : ℕ)
    (hQ : Invariant A.toMatrix Q)
    (hU : ∀ i j, (Q.U i j).natAbs ≤ 2 ^ d)
    (hV : ∀ i j, (Q.V i j).natAbs ≤ 2 ^ d) :
    (SmithDecomposition.encode Q.result).length ≤
      2 * (5 * (SmithEncoding.encode A).length + 10 +
        2 * (SmithEncoding.encode A).length * (SmithEncoding.encode A).length *
          (2 * (stateWidth (SmithEncoding.encode A).length d + 1) + 2)) + 5 :=
  encode_length_le_of_input_bits A _ _
    (bounded_of_input_forward A Q d hQ hU hV).result_entry_bits

-- Kernel-checked specializations: a negative determinant changes the cofactor
-- sign; empty transformed matrices can still have nontrivial forward/inverse
-- maps. These finite cases are separate from the universal size proofs above.
private abbrev signedMap : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 3; 0, 1]
example : (signedMap 0 1).natAbs = (signedMap.adjugate 0 1).natAbs :=
  inverse_entry_natAbs_eq_adjugate signedMap signedMap (by decide) 0 1
example : signedMap.adjugate 0 1 = -3 := by decide

private abbrev rectangularInput : Dense := ⟨2, 3, [6, -4, 0, 22, -14, 0], rfl⟩
private abbrev swapPrefix : List (Op 2 3) := [.row 0 1 (by decide) 1]
example : Bounded (run (initial rectangularInput.toMatrix) (swapPrefix.take 1))
    (2 ^ stateWidth (SmithEncoding.encode rectangularInput).length 1) :=
  trace_prefix_bound rectangularInput swapPrefix 1 1 (by decide) (by decide)

private abbrev emptyRows : Dense := ⟨0, 2, [], rfl⟩
private abbrev emptyCols : Dense := ⟨2, 0, [], rfl⟩
example : Bounded (run (initial emptyRows.toMatrix) [.col 1 0 (by decide) (-3)])
    (2 ^ stateWidth (SmithEncoding.encode emptyRows).length 2) :=
  trace_prefix_bound emptyRows [.col 1 0 (by decide) (-3)] 1 2 (by decide) (by decide)
example : Bounded (run (initial emptyCols.toMatrix) [.row 1 0 (by decide) (-3)])
    (2 ^ stateWidth (SmithEncoding.encode emptyCols).length 2) :=
  trace_prefix_bound emptyCols [.row 1 0 (by decide) (-3)] 1 2 (by decide) (by decide)
example : Bounded (initial (⟨0, 0, [], rfl⟩ : Dense).toMatrix)
    (2 ^ stateWidth (SmithEncoding.encode (⟨0, 0, [], rfl⟩ : Dense)).length 0) :=
  trace_prefix_bound ⟨0, 0, [], rfl⟩ [] 0 0 (by decide) (by decide)
example : ∀ i j, (((0 : Matrix (Fin 2) (Fin 0) ℤ) *
    (0 : Matrix (Fin 0) (Fin 3) ℤ)) i j).natAbs ≤ 0 * (1 * 1) :=
  mul_entry_natAbs_le _ _ 1 1 (by decide) (by decide)

#print axioms adjugate_natAbs_le_pow
#print axioms inverse_entry_natAbs_eq_adjugate
#print axioms inverse_natAbs_le_pow
#print axioms mul_entry_natAbs_le
#print axioms stateWidth
#print axioms bounded_of_forward
#print axioms bounded_of_input_forward
#print axioms trace_prefix_bound
#print axioms output_length_le_of_forward

end PhdThesisLean.SmithForwardBounds
