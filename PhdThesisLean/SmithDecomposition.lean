import PhdThesisLean.SmithEncoding
import PhdThesisLean.MaxObjectiveSmith

/-!
# Executable Smith decomposition output contract

This module checks supplied finite outputs; it does not construct a Smith form.
All five matrices retain dense signed-binary storage. Proofs of shape and
correctness are erased, not extra uncharged computational input. The weak
contract suffices for the existing max-objective formula; the separately named
canonical contract additionally orders signs, zeros and divisibility.
No coefficient-growth, termination, serializer-machine or runtime claim is made.
-/

namespace PhdThesisLean.SmithDecomposition

open SmithEncoding Matrix

/-- A dimension-checked view of the existing dense storage, with no new codec. -/
abbrev Block (m n : ℕ) := {A : Dense // A.rows = m ∧ A.cols = n}

/-- Interpret the stored entries at their checked dimensions. -/
def Block.matrix {m n : ℕ} (B : Block m n) : Matrix (Fin m) (Fin n) ℤ :=
  fun i j => B.val.toMatrix (Fin.cast B.property.1.symm i) (Fin.cast B.property.2.symm j)

/-- Finite output data. Both transformations and their integral inverses are
stored explicitly, including in rectangular and zero-dimensional cases. -/
structure Result (m n : ℕ) where
  U : Block m m
  Uinv : Block m m
  V : Block n n
  Vinv : Block n n
  S : Block m n

/-- The weak decomposition contract required by the max-objective formula.
Both inverse directions are checked over integers, not over a fraction field. -/
def Valid {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (R : Result m n) : Prop :=
  R.Uinv.matrix * R.U.matrix = 1 ∧
  R.U.matrix * R.Uinv.matrix = 1 ∧
  R.V.matrix * R.Vinv.matrix = 1 ∧
  R.Vinv.matrix * R.V.matrix = 1 ∧
  R.U.matrix * A * R.V.matrix = R.S.matrix ∧
  ∀ (i : Fin m) (j : Fin n), i.val ≠ j.val → R.S.matrix i j = 0

instance {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (R : Result m n) :
    Decidable (Valid A R) := by unfold Valid; infer_instance

/-- An executable checker of a supplied output. This is not a decomposition
algorithm and its finite decision procedure has no polynomial runtime proof. -/
def check {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (R : Result m n) : Bool :=
  decide (Valid A R)

@[simp]
theorem check_eq_true_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (R : Result m n) : check A R = true ↔ Valid A R := by simp [check]

/-- Restrict to the actual rectangular diagonal; no square completion is used. -/
def diagonal {m n : ℕ} (R : Result m n) (i : Fin (min m n)) : ℤ :=
  R.S.matrix (Fin.castLE (Nat.min_le_left m n) i) (Fin.castLE (Nat.min_le_right m n) i)

/-- Canonical Smith conditions are additional to the weak contract. Nonzero
entries precede zeros, and consecutive diagonal entries divide their successors.
All conditions are vacuous for an empty rectangular diagonal. -/
def Canonical {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (R : Result m n) : Prop :=
  Valid A R ∧
  (∀ i, 0 ≤ diagonal R i) ∧
  (∀ i j, i < j → diagonal R i = 0 → diagonal R j = 0) ∧
  (∀ i j, i.val + 1 = j.val → diagonal R i ∣ diagonal R j)

instance {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (R : Result m n) :
    Decidable (Canonical A R) := by unfold Canonical; infer_instance

/-- The weak projection does not require a sign or divisibility hypothesis. -/
theorem Canonical.valid {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ}
    {R : Result m n} (h : Canonical A R) : Valid A R := h.1

/-- Exactly the integral identities and rectangular diagonality consumed by
`MaxObjectiveSmith`; no canonical Smith condition enters this projection. -/
theorem Valid.maxHypotheses {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ}
    {R : Result m n} (h : Valid A R) :
    R.Uinv.matrix * R.U.matrix = 1 ∧ R.V.matrix * R.Vinv.matrix = 1 ∧
      ∀ (i : Fin m) (j : Fin n), i.val ≠ j.val →
        (R.U.matrix * A * R.V.matrix) i j = 0 := by
  refine ⟨h.1, h.2.2.1, ?_⟩
  intro i j hij
  rw [h.2.2.2.2.1]
  exact h.2.2.2.2.2 i j hij

/-- A checked finite result can instantiate the existing rational max formula.
This still assumes a valid result; it is not a polynomial-time optimizer. -/
theorem rhoMax_of_valid {p m n : ℕ} [Fact p.Prime]
    (X : Matrix (Fin m) (Fin n) ℚ) (y : Fin m → ℚ) (D : ℤ) (hD : D ≠ 0)
    (A : Block m n) (b : Fin m → ℤ)
    (hA : ∀ i j, (A.matrix i j : ℚ) = D * X i j)
    (hb : ∀ i, (b i : ℚ) = D * y i) (R : Result m n)
    (h : Valid A.matrix R) :
    MaxObjective.rhoMax (X.map (Rat.cast : ℚ → ℚ_[p])) (fun i => (y i : ℚ_[p])) =
      ‖(D : ℚ_[p])‖⁻¹ *
        ‖MaxObjectiveSmith.maskZero (p := p) R.S.matrix (R.U.matrix *ᵥ b)‖ := by
  obtain ⟨hU, hV, hS⟩ := h.maxHypotheses
  have hf := MaxObjectiveSmith.rhoMax_rational_smith (p := p) X y D hD
    A.matrix b hA hb
    R.U.matrix R.Uinv.matrix R.V.matrix R.Vinv.matrix hU hV hS
  rw [h.2.2.2.2.1] at hf
  exact hf

/-- Concrete output bits: five library-framed matrix encodings in the fixed
order `U,Uinv,V,Vinv,S`. This only defines serialization, not its machine cost
or a combined output decoder. Dimension headers are retained in every block. -/
def encode {m n : ℕ} (R : Result m n) : List Bool :=
  LeanNPHardness.BinaryNatLists.frame (SmithEncoding.encode R.U.val) ++
  LeanNPHardness.BinaryNatLists.frame (SmithEncoding.encode R.Uinv.val) ++
  LeanNPHardness.BinaryNatLists.frame (SmithEncoding.encode R.V.val) ++
  LeanNPHardness.BinaryNatLists.frame (SmithEncoding.encode R.Vinv.val) ++
  LeanNPHardness.BinaryNatLists.frame (SmithEncoding.encode R.S.val)

/-- Charge all five matrices, including inverses and framing. -/
theorem encode_length {m n : ℕ} (R : Result m n) :
    (encode R).length = 2 * ((SmithEncoding.encode R.U.val).length +
      (SmithEncoding.encode R.Uinv.val).length +
      (SmithEncoding.encode R.V.val).length +
      (SmithEncoding.encode R.Vinv.val).length +
      (SmithEncoding.encode R.S.val).length) + 5 := by
  simp [encode, LeanNPHardness.BinaryNatLists.frame_length]
  omega

/-- A conditional complete-output bound, not a proof that an algorithm can
maintain the assumed bound on every stored coefficient's binary magnitude. -/
theorem encode_length_le_of_entry_bits {m n : ℕ} (R : Result m n) (b : ℕ)
    (h : ∀ B ∈ [R.U.val, R.Uinv.val, R.V.val, R.Vinv.val, R.S.val],
      ∀ z ∈ B.entries, (Computability.encodeNat z.natAbs).length ≤ b) :
    (encode R).length ≤
      2 * (5 * m + 5 * n + 10 + (2 * m * m + 2 * n * n + m * n) * (2 * b + 2)) + 5 := by
  have hU := SmithEncoding.encode_length_le_of_entry_bits R.U.val b (h _ (by simp))
  have hUi := SmithEncoding.encode_length_le_of_entry_bits R.Uinv.val b (h _ (by simp))
  have hV := SmithEncoding.encode_length_le_of_entry_bits R.V.val b (h _ (by simp))
  have hVi := SmithEncoding.encode_length_le_of_entry_bits R.Vinv.val b (h _ (by simp))
  have hS := SmithEncoding.encode_length_le_of_entry_bits R.S.val b (h _ (by simp))
  rw [R.U.property.1, R.U.property.2] at hU
  rw [R.Uinv.property.1, R.Uinv.property.2] at hUi
  rw [R.V.property.1, R.V.property.2] at hV
  rw [R.Vinv.property.1, R.Vinv.property.2] at hVi
  rw [R.S.property.1, R.S.property.2] at hS
  rw [encode_length]
  calc
    _ ≤ 2 * ((m + m + 2 + m * m * (2 * b + 2)) +
      (m + m + 2 + m * m * (2 * b + 2)) +
      (n + n + 2 + n * n * (2 * b + 2)) +
      (n + n + 2 + n * n * (2 * b + 2)) +
      (m + n + 2 + m * n * (2 * b + 2))) + 5 := by omega
    _ = _ := by ring

/-- Express the same conditional output bound in the actual input bit length.
The coefficient parameter `b` still needs an algorithmic polynomial bound. -/
theorem encode_length_le_of_input_bits (A : Dense) (R : Result A.rows A.cols) (b : ℕ)
    (h : ∀ B ∈ [R.U.val, R.Uinv.val, R.V.val, R.Vinv.val, R.S.val],
      ∀ z ∈ B.entries, (Computability.encodeNat z.natAbs).length ≤ b) :
    (encode R).length ≤ 2 * (5 * (SmithEncoding.encode A).length + 10 +
      2 * (SmithEncoding.encode A).length * (SmithEncoding.encode A).length * (2 * b + 2)) + 5 := by
  have hd := SmithEncoding.dimensions_le_length A
  have hd' : A.rows + A.cols ≤ (SmithEncoding.encode A).length := by omega
  have hs := Nat.mul_le_mul hd' hd'
  have hc : 2 * A.rows * A.rows + 2 * A.cols * A.cols + A.rows * A.cols ≤
      2 * (SmithEncoding.encode A).length * (SmithEncoding.encode A).length := by
    nlinarith
  have hw := Nat.mul_le_mul_right (2 * b + 2) hc
  have hr := encode_length_le_of_entry_bits R b h
  nlinarith

-- Kernel checks exercise the actual finite checker, not native execution.
private def unitOne : Block 1 1 := ⟨⟨1, 1, [1], rfl⟩, rfl, rfl⟩
private def unitTwo : Block 2 2 := ⟨⟨2, 2, [1, 0, 0, 1], rfl⟩, rfl, rfl⟩
private def emptyBlock (m n : ℕ) (h : m * n = 0) : Block m n :=
  ⟨⟨m, n, [], by simpa using h.symm⟩, rfl, rfl⟩
private def negativeResult : Result 1 2 :=
  ⟨unitOne, unitOne, unitTwo, unitTwo, ⟨⟨1, 2, [-3, 0], rfl⟩, rfl, rfl⟩⟩
example : check negativeResult.S.matrix negativeResult = true := by decide
example : ¬ Canonical negativeResult.S.matrix negativeResult := by decide
example : check negativeResult.S.matrix
    { negativeResult with Uinv := ⟨⟨1, 1, [2], rfl⟩, rfl, rfl⟩ } = false := by decide
example : check negativeResult.S.matrix
    { negativeResult with S := ⟨⟨1, 2, [-3, 1], rfl⟩, rfl, rfl⟩ } = false := by decide
private def emptyRows : Result 0 2 :=
  ⟨emptyBlock 0 0 rfl, emptyBlock 0 0 rfl, unitTwo, unitTwo, emptyBlock 0 2 rfl⟩
private def emptyCols : Result 2 0 :=
  ⟨unitTwo, unitTwo, emptyBlock 0 0 rfl, emptyBlock 0 0 rfl, emptyBlock 2 0 rfl⟩
example : check emptyRows.S.matrix emptyRows = true := by decide
example : Canonical emptyRows.S.matrix emptyRows := by decide
example : check emptyCols.S.matrix emptyCols = true := by decide
example : Canonical emptyCols.S.matrix emptyCols := by decide

#print axioms Block.matrix
#print axioms check
#print axioms check_eq_true_iff
#print axioms Canonical.valid
#print axioms Valid.maxHypotheses
#print axioms rhoMax_of_valid
#print axioms encode_length
#print axioms encode_length_le_of_entry_bits
#print axioms encode_length_le_of_input_bits

end PhdThesisLean.SmithDecomposition
