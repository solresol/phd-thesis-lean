import PhdThesisLean.SmithIsolation

/-!
# Computed integral diagonal decomposition

Recurse over every available diagonal position, protecting the completed
off-diagonal prefix. The output contains both integral transformations and
their inverses and satisfies the weak decomposition contract for every dense
integer matrix, including singular, rectangular and empty inputs.

This is a terminating diagonalizer, without canonical Smith normalization,
global coefficient bounds, polynomial operation counts or a uniform machine.
The existing signed-binary input and five-matrix output encodings are reused;
their conditional entry-width bounds do not become unconditional here.
-/

namespace PhdThesisLean.SmithDiagonalization

open Matrix SmithTrace SmithIsolation SmithDecomposition SmithEncoding

variable {m n : ℕ}

/-- Every off-diagonal entry touching the completed prefix is zero. This
includes both zero-block boundaries and the completed diagonal block. -/
def Prefix (Q : State m n) (k : ℕ) : Prop :=
  ∀ (i : Fin m) (j : Fin n), i.val ≠ j.val →
    (i.val < k ∨ j.val < k) → Q.S i j = 0

theorem prefix_zero (Q : State m n) : Prefix Q 0 := by
  intro i j _ h
  omega

/-- Isolating the next position preserves the completed diagonal block and
advances both zero-block boundaries, including when the new pivot is zero. -/
theorem isolate_prefix_succ (Q : State m n) (k : ℕ) (hQ : Prefix Q k) :
    Prefix (isolate Q k) (k + 1) := by
  have hlower : ∀ (i : Fin m) (j : Fin n),
      k ≤ i.val → j.val < k → Q.S i j = 0 := by
    intro i j hi hj
    exact hQ i j (by omega) (Or.inr hj)
  have hupper : ∀ (i : Fin m) (j : Fin n),
      i.val < k → k ≤ j.val → Q.S i j = 0 := by
    intro i j hi hj
    exact hQ i j (by omega) (Or.inl hi)
  have hnext := isolate_next_zero Q k hlower hupper
  intro i j hij hpos
  by_cases hold : i.val < k ∨ j.val < k
  · rw [isolate_prefix Q k hlower hupper i j hold]
    exact hQ i j hij hold
  · rcases hpos with hi | hj
    · exact hnext.2 i j hi (by omega)
    · exact hnext.1 i j (by omega) hj

/-- Complete the remaining diagonal positions. The outer recursion has
`min m n - k` steps; no bound on the work inside each isolation is asserted. -/
def finish (Q : State m n) (k : ℕ) : State m n :=
  if _h : k < min m n then finish (isolate Q k) (k + 1) else Q
termination_by min m n - k
decreasing_by omega

theorem finish_of_done (Q : State m n) (k : ℕ) (h : min m n ≤ k) :
    finish Q k = Q := by
  rw [finish]
  split_ifs with hactive
  · omega
  · rfl

theorem finish_invariant {A : Matrix (Fin m) (Fin n) ℤ} (Q : State m n)
    (hQ : Invariant A Q) (k : ℕ) : Invariant A (finish Q k) := by
  rw [finish]
  split_ifs with h
  · exact finish_invariant (isolate Q k) (isolate_invariant hQ k) (k + 1)
  · exact hQ
termination_by min m n - k
decreasing_by omega

/-- The final off-diagonal entries vanish without a rank, nonzero-pivot or
square hypothesis. A zero diagonal entry may precede a nonzero one. -/
theorem finish_diagonal (Q : State m n) (k : ℕ) (hQ : Prefix Q k) :
    ∀ (i : Fin m) (j : Fin n), i.val ≠ j.val → (finish Q k).S i j = 0 := by
  rw [finish]
  split_ifs with h
  · exact finish_diagonal (isolate Q k) (k + 1) (isolate_prefix_succ Q k hQ)
  · intro i j hij
    exact hQ i j hij (by have hi := i.isLt; have hj := j.isLt; omega)
termination_by min m n - k
decreasing_by omega

/-- Compute all five stored matrices from the input alone. No supplied trace,
decomposition, diagonal witness or runtime witness is an extra argument. -/
def decompose (A : Dense) : Result A.rows A.cols :=
  (finish (initial A.toMatrix) 0).result

theorem decompose_valid (A : Dense) : Valid A.toMatrix (decompose A) := by
  have h := finish_invariant (initial A.toMatrix) (initial_invariant A.toMatrix) 0
  have hd := finish_diagonal (initial A.toMatrix) 0 (prefix_zero _)
  simpa only [Valid, decompose, State.result, pack_matrix] using
    And.intro h.Uinv_U ⟨h.U_Uinv, h.V_Vinv, h.Vinv_V, h.transformed, hd⟩

theorem decompose_check (A : Dense) : check A.toMatrix (decompose A) = true :=
  (check_eq_true_iff _ _).2 (decompose_valid A)

/-- With no available diagonal position the complete state, including all
four transformations, is unchanged. Dense output still pays for identities. -/
theorem decompose_of_empty (A : Dense) (h : A.rows = 0 ∨ A.cols = 0) :
    decompose A = (initial A.toMatrix).result := by
  unfold decompose
  rw [finish_of_done _ 0 (by rcases h with h | h <;> simp [h])]

-- Kernel-checked specializations of the universal contract, including zero
-- pivots, negative entries, rank deficiency and both rectangular orientations.
example : Valid (⟨2, 3, [6, 4, 0, 0, 6, 0], rfl⟩ : Dense).toMatrix
    (decompose ⟨2, 3, [6, 4, 0, 0, 6, 0], rfl⟩) := decompose_valid _

example : Valid (⟨3, 2, [0, -6, 0, 12, 0, 0], rfl⟩ : Dense).toMatrix
    (decompose ⟨3, 2, [0, -6, 0, 12, 0, 0], rfl⟩) := decompose_valid _

example : decompose (⟨0, 3, [], rfl⟩ : Dense) =
    (initial (⟨0, 3, [], rfl⟩ : Dense).toMatrix).result :=
  decompose_of_empty _ (Or.inl rfl)

example : decompose (⟨3, 0, [], rfl⟩ : Dense) =
    (initial (⟨3, 0, [], rfl⟩ : Dense).toMatrix).result :=
  decompose_of_empty _ (Or.inr rfl)

example : decompose (⟨0, 0, [], rfl⟩ : Dense) =
    (initial (⟨0, 0, [], rfl⟩ : Dense).toMatrix).result :=
  decompose_of_empty _ (Or.inl rfl)

-- These concrete evaluations are regression evidence. They do not bound the
-- intermediate coefficients or runtime of the universal algorithm.
/-- info: [-2, 0, 0, 0, -18, 0] -/
#guard_msgs in
#eval (decompose ⟨2, 3, [6, 4, 0, 0, 6, 0], rfl⟩).S.val.entries

/-- info: [0, 0, 0, 5] -/
#guard_msgs in
#eval (decompose ⟨2, 2, [0, 0, 0, 5], rfl⟩).S.val.entries

/-- info: true -/
#guard_msgs in
#eval check (⟨3, 2, [0, -6, 0, 12, 0, 0], rfl⟩ : Dense).toMatrix
  (decompose ⟨3, 2, [0, -6, 0, 12, 0, 0], rfl⟩)

end PhdThesisLean.SmithDiagonalization

#print axioms PhdThesisLean.SmithDiagonalization.Prefix
#print axioms PhdThesisLean.SmithDiagonalization.prefix_zero
#print axioms PhdThesisLean.SmithDiagonalization.isolate_prefix_succ
#print axioms PhdThesisLean.SmithDiagonalization.finish
#print axioms PhdThesisLean.SmithDiagonalization.finish_of_done
#print axioms PhdThesisLean.SmithDiagonalization.finish_invariant
#print axioms PhdThesisLean.SmithDiagonalization.finish_diagonal
#print axioms PhdThesisLean.SmithDiagonalization.decompose
#print axioms PhdThesisLean.SmithDiagonalization.decompose_valid
#print axioms PhdThesisLean.SmithDiagonalization.decompose_check
#print axioms PhdThesisLean.SmithDiagonalization.decompose_of_empty
