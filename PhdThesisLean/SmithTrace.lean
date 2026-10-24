import PhdThesisLean.SmithRowOperations
import PhdThesisLean.SmithDecomposition

/-!
# Executable integer transformation traces with accumulated inverses

The interpreter constructs all five matrices from an input and a finite trace
of row/column additions. It does not choose a diagonalizing trace. The invariant
is integral and two-sided, including for rectangular and empty inputs. Packing
the computed matrices uses the existing dense signed-binary format; no trace
codec, coefficient-growth theorem or machine-time bound is asserted here.
-/

namespace PhdThesisLean.SmithTrace

open Matrix SmithRowOperations SmithDecomposition SmithEncoding

variable {m n : ℕ}

/-- Add source column `s`, multiplied by `c`, to destination column `r`. -/
def colAdd (A : Matrix (Fin m) (Fin n) ℤ) (r s : Fin n) (c : ℤ) :
    Matrix (Fin m) (Fin n) ℤ :=
  fun i j => if j = r then A i j + c * A i s else A i j

theorem colAdd_eq_mul_transvection (A : Matrix (Fin m) (Fin n) ℤ)
    (r s : Fin n) (c : ℤ) :
    colAdd A r s c = A * Matrix.transvection s r c := by
  ext i j
  by_cases hj : j = r
  · subst j
    simp [colAdd]
  · simp [colAdd, hj, Matrix.mul_transvection_apply_of_ne]

/-- The inverse must be accumulated in the opposite multiplication order. -/
private theorem transvection_cancel {k : ℕ} (r s : Fin k) (h : r ≠ s) (c : ℤ) :
    Matrix.transvection r s (-c) * Matrix.transvection r s c = 1 ∧
      Matrix.transvection r s c * Matrix.transvection r s (-c) = 1 := by
  constructor <;> simp [Matrix.transvection_mul_transvection_same r s h]

/-- Distinctness proofs are erased; indices and the integer multiplier are data.
This is an interpreter input, not a claimed polynomial-size decomposition. -/
inductive Op (m n : ℕ) where
  | row (r s : Fin m) (different : r ≠ s) (c : ℤ)
  | col (r s : Fin n) (different : r ≠ s) (c : ℤ)

/-- Intermediate matrices are executable finite-index functions over integers. -/
structure State (m n : ℕ) where
  U : Matrix (Fin m) (Fin m) ℤ
  Uinv : Matrix (Fin m) (Fin m) ℤ
  V : Matrix (Fin n) (Fin n) ℤ
  Vinv : Matrix (Fin n) (Fin n) ℤ
  S : Matrix (Fin m) (Fin n) ℤ

/-- No diagonal hypothesis belongs to the execution invariant. -/
structure Invariant (A : Matrix (Fin m) (Fin n) ℤ) (Q : State m n) : Prop where
  Uinv_U : Q.Uinv * Q.U = 1
  U_Uinv : Q.U * Q.Uinv = 1
  V_Vinv : Q.V * Q.Vinv = 1
  Vinv_V : Q.Vinv * Q.V = 1
  transformed : Q.U * A * Q.V = Q.S

def initial (A : Matrix (Fin m) (Fin n) ℤ) : State m n :=
  ⟨1, 1, 1, 1, A⟩

theorem initial_invariant (A : Matrix (Fin m) (Fin n) ℤ) :
    Invariant A (initial A) := by
  constructor <;> simp [initial]

/-- Update the transformed matrix, forward map and backward map together.
In particular a row operation on `U` is a column operation on `Uinv`. -/
def step (Q : State m n) : Op m n → State m n
  | .row r s _ c =>
      { Q with
        U := rowAdd Q.U r s c
        Uinv := colAdd Q.Uinv s r (-c)
        S := rowAdd Q.S r s c }
  | .col r s _ c =>
      { Q with
        V := colAdd Q.V r s c
        Vinv := rowAdd Q.Vinv s r (-c)
        S := colAdd Q.S r s c }

theorem step_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (op : Op m n) : Invariant A (step Q op) := by
  cases op with
  | row r s h c =>
      obtain ⟨hback, hfwd⟩ := transvection_cancel r s h c
      constructor
      · simp only [step, colAdd_eq_mul_transvection, rowAdd_eq_transvection_mul]
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.transvection r s (-c)),
          hback, Matrix.one_mul, hQ.Uinv_U]
      · simp only [step, colAdd_eq_mul_transvection, rowAdd_eq_transvection_mul]
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q.U, hQ.U_Uinv,
          Matrix.one_mul, hfwd]
      · exact hQ.V_Vinv
      · exact hQ.Vinv_V
      · simp only [step, rowAdd_eq_transvection_mul]
        simpa only [Matrix.mul_assoc] using
          congrArg (fun B => Matrix.transvection r s c * B) hQ.transformed
  | col r s h c =>
      obtain ⟨hback, hfwd⟩ := transvection_cancel s r h.symm c
      constructor
      · exact hQ.Uinv_U
      · exact hQ.U_Uinv
      · simp only [step, colAdd_eq_mul_transvection, rowAdd_eq_transvection_mul]
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.transvection s r c),
          hfwd, Matrix.one_mul, hQ.V_Vinv]
      · simp only [step, colAdd_eq_mul_transvection, rowAdd_eq_transvection_mul]
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q.Vinv, hQ.Vinv_V,
          Matrix.one_mul, hback]
      · simp only [step, colAdd_eq_mul_transvection]
        rw [← Matrix.mul_assoc, hQ.transformed]

/-- Execute in list order, without selecting operations or assuming diagonality. -/
def run (Q : State m n) : List (Op m n) → State m n
  | [] => Q
  | op :: ops => run (step Q op) ops

theorem run_invariant {A : Matrix (Fin m) (Fin n) ℤ} {Q : State m n}
    (hQ : Invariant A Q) (ops : List (Op m n)) : Invariant A (run Q ops) := by
  induction ops generalizing Q with
  | nil => exact hQ
  | cons op ops ih => exact ih (step_invariant hQ op)

/-- Materialize every finite-index entry in the established row-major storage.
This performs an actual enumeration; efficient machine serialization is separate. -/
def pack (A : Matrix (Fin m) (Fin n) ℤ) : Block m n :=
  ⟨⟨m, n, List.ofFn (fun k : Fin (m * n) =>
      A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2), by simp⟩, rfl, rfl⟩

@[simp]
theorem pack_matrix (A : Matrix (Fin m) (Fin n) ℤ) : (pack A).matrix = A := by
  ext i j
  have hij : i.val * n + j.val < m * n := calc
    i.val * n + j.val < (i.val + 1) * n := by
      simpa only [Nat.add_mul, Nat.one_mul] using Nat.add_lt_add_left j.isLt (i.val * n)
    _ ≤ m * n := Nat.mul_le_mul_right n i.isLt
  change (List.ofFn (fun k : Fin (m * n) =>
      A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))[i.val * n + j.val]'(by
        simpa using hij) = _
  rw [List.getElem_ofFn]
  have hk : (⟨i.val * n + j.val, hij⟩ : Fin (m * n)) =
      finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp only [hk, Equiv.symm_apply_apply]

def State.result (Q : State m n) : Result m n :=
  ⟨pack Q.U, pack Q.Uinv, pack Q.V, pack Q.Vinv, pack Q.S⟩

/-- Compute the complete finite output from the matrix and trace. -/
def execute (A : Matrix (Fin m) (Fin n) ℤ) (ops : List (Op m n)) : Result m n :=
  (run (initial A) ops).result

/-- Entry point using the existing stored input, including its runtime dimensions.
The trace is still additional input whose construction and bit cost are open. -/
def executeDense (A : Dense) (ops : List (Op A.rows A.cols)) : Result A.rows A.cols :=
  execute A.toMatrix ops

/-- The interpreter always establishes the integral equivalence identities.
It makes no claim that its transformed matrix is diagonal. -/
theorem execute_equivalence (A : Matrix (Fin m) (Fin n) ℤ) (ops : List (Op m n)) :
    let R := execute A ops
    R.Uinv.matrix * R.U.matrix = 1 ∧ R.U.matrix * R.Uinv.matrix = 1 ∧
      R.V.matrix * R.Vinv.matrix = 1 ∧ R.Vinv.matrix * R.V.matrix = 1 ∧
      R.U.matrix * A * R.V.matrix = R.S.matrix := by
  have h := run_invariant (initial_invariant A) ops
  simpa [execute, State.result] using
    And.intro h.Uinv_U ⟨h.U_Uinv, h.V_Vinv, h.Vinv_V, h.transformed⟩

/-- If the computed output is diagonal, it meets exactly the existing weak
contract. Finding such a trace with controlled growth remains open. -/
theorem execute_valid_of_diagonal (A : Matrix (Fin m) (Fin n) ℤ)
    (ops : List (Op m n))
    (hdiag : ∀ (i : Fin m) (j : Fin n), i.val ≠ j.val →
      (execute A ops).S.matrix i j = 0) : Valid A (execute A ops) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := execute_equivalence A ops
  exact ⟨h1, h2, h3, h4, h5, hdiag⟩

-- Kernel-checked execution examples. Multiple noncommuting operations on each
-- side exercise inverse order; empty inputs can still change a transformation.
private def rectangularInput : Dense := ⟨2, 3, [6, -4, 0, 22, -14, 0], rfl⟩
private def rectangularOps : List (Op 2 3) :=
  [.col 1 0 (by decide) 1, .col 0 1 (by decide) (-2),
    .row 1 0 (by decide) (-3), .row 0 1 (by decide) (-1)]
example : (executeDense rectangularInput rectangularOps).S.val.entries =
    [2, 0, 0, 0, 2, 0] := by decide
example : check rectangularInput.toMatrix (executeDense rectangularInput rectangularOps) =
    true := by decide
private def rankOneInput : Dense := ⟨2, 3, [2, 4, 0, 0, 0, 0], rfl⟩
private def rankOneOps : List (Op 2 3) := [.col 1 0 (by decide) (-2)]
example : check rankOneInput.toMatrix
    (executeDense rankOneInput rankOneOps) = true := by decide
example : check (0 : Matrix (Fin 0) (Fin 2) ℤ)
    (execute 0 [.col 1 0 (by decide) 3]) = true := by decide
example : check (0 : Matrix (Fin 2) (Fin 0) ℤ)
    (execute 0 [.row 1 0 (by decide) (-3)]) = true := by decide
example : check (0 : Matrix (Fin 0) (Fin 0) ℤ) (execute 0 []) = true := by decide

#print axioms colAdd_eq_mul_transvection
#print axioms initial_invariant
#print axioms step_invariant
#print axioms run_invariant
#print axioms pack_matrix
#print axioms execute
#print axioms executeDense
#print axioms execute_equivalence
#print axioms execute_valid_of_diagonal

end PhdThesisLean.SmithTrace
