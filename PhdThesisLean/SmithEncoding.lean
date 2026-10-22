import LeanNPHardness.BinaryNatLists
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Checked dense integer-matrix wire format for Smith decomposition

Dimensions are unary (including zero) and entries are row-major, signed binary.
A sign bit precedes each library-framed binary magnitude; zero has positive sign.
The complete decoder re-encodes its result to reject noncanonical magnitudes,
negative zero and trailing bits. Both dimensions therefore cost input bits even
when there are no entries. This is an encoding interface, not a machine or a
Smith algorithm. The same format can serialize each returned transformation,
its inverse and the rectangular diagonal matrix.
-/

namespace PhdThesisLean.SmithEncoding

open LeanNPHardness

/-- Positive sign is `false`, negative sign is `true`; magnitude is framed binary. -/
def encodeInt (z : ℤ) : List Bool :=
  decide (z < 0) :: BinaryNatLists.encodeNat z.natAbs

/-- Parse one signed entry and retain the unused suffix. Canonicality is checked
by the complete matrix decoder. -/
def decodeIntPrefix : List Bool → Option (ℤ × List Bool)
  | [] => none
  | sign :: bits => do
      let (n, rest) ← BinaryNatLists.decodeNatPrefix bits
      pure ((if sign then -(n : ℤ) else (n : ℤ)), rest)

@[simp]
theorem decodeIntPrefix_encode_append (z : ℤ) (rest : List Bool) :
    decodeIntPrefix (encodeInt z ++ rest) = some (z, rest) := by
  cases z with
  | ofNat n => simp [encodeInt, decodeIntPrefix]
  | negSucc n => simp [encodeInt, decodeIntPrefix]; omega

/-- Decode exactly the dimension product many entries. -/
def decodeEntries : ℕ → List Bool → Option (List ℤ × List Bool)
  | 0, bits => some ([], bits)
  | n + 1, bits => do
      let (z, rest) ← decodeIntPrefix bits
      let (zs, tail) ← decodeEntries n rest
      pure (z :: zs, tail)

@[simp]
theorem decodeEntries_encode_append (zs : List ℤ) (rest : List Bool) :
    decodeEntries zs.length (zs.flatMap encodeInt ++ rest) = some (zs, rest) := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp [decodeEntries, List.append_assoc, ih]

theorem decodeEntries_length {n : ℕ} {bits : List Bool} {zs : List ℤ}
    {rest : List Bool} (h : decodeEntries n bits = some (zs, rest)) :
    zs.length = n := by
  induction n generalizing bits zs rest with
  | zero =>
      have heq : [] = zs := (by simpa [decodeEntries] using h : [] = zs ∧ bits = rest).1
      simp [← heq]
  | succ n ih =>
      simp only [decodeEntries] at h
      cases hp : decodeIntPrefix bits with
      | none => simp [hp] at h
      | some pair =>
          rcases pair with ⟨z, tail⟩
          cases hq : decodeEntries n tail with
          | none => simp [hp, hq] at h
          | some pair =>
              rcases pair with ⟨entries, suffix⟩
              have heq : z :: entries = zs := (by simpa [hp, hq] using h : z :: entries = zs ∧ suffix = rest).1
              rw [← heq, List.length_cons, ih hq]

/-- Finite executable dense storage, with no missing or excess cells. A `0 × n`
matrix still remembers `n`. No nonempty-dimension assumption is imposed. -/
structure Dense where
  rows : ℕ
  cols : ℕ
  entries : List ℤ
  entryCount : entries.length = rows * cols
  deriving DecidableEq

/-- Interpret the storage as a rectangular integer matrix. -/
def Dense.toMatrix (A : Dense) : Matrix (Fin A.rows) (Fin A.cols) ℤ :=
  fun i j => A.entries[i.val * A.cols + j.val]'(by
    rw [A.entryCount]
    calc
      i.val * A.cols + j.val < i.val * A.cols + A.cols := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * A.cols := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ A.rows * A.cols := Nat.mul_le_mul_right _ i.isLt)

/-- Dimension headers followed by exactly `rows * cols` row-major signed fields.
Unary headers are intentional: a short binary dimension for an empty input must
not require an exponentially large dense inverse in the eventual output. -/
def encode (A : Dense) : List Bool :=
  List.replicate A.rows true ++ false ::
    (List.replicate A.cols true ++ false :: A.entries.flatMap encodeInt)

/-- Structural parser, checking entry count and complete input exhaustion. -/
def decodeRaw (bits : List Bool) : Option Dense := do
  let (m, rest) ← BinaryNatLists.readUnary bits
  let (n, payload) ← BinaryNatLists.readUnary rest
  let (zs, tail) ← decodeEntries (m * n) payload
  if tail = [] then
    if h : zs.length = m * n then some ⟨m, n, zs, h⟩ else none
  else none

@[simp]
theorem decodeRaw_encode (A : Dense) : decodeRaw (encode A) = some A := by
  rcases A with ⟨m, n, zs, h⟩
  have he := decodeEntries_encode_append zs []
  simp only [List.append_nil] at he
  simp [decodeRaw, encode, ← h, he]

/-- Require the exact canonical wire representation, as well as structural
validity. This rejects negative zero and redundant binary magnitude bits. -/
def decode (bits : List Bool) : Option Dense := do
  let A ← decodeRaw bits
  if encode A = bits then some A else none

@[simp]
theorem decode_encode (A : Dense) : decode (encode A) = some A := by
  simp [decode]

/-- Every accepted input is the exact encoding of its decoded matrix. -/
theorem encode_of_decode {bits : List Bool} {A : Dense}
    (h : decode bits = some A) : encode A = bits := by
  simp only [decode] at h
  cases hr : decodeRaw bits with
  | none => simp [hr] at h
  | some B =>
      by_cases hb : encode B = bits
      · have heq : B = A := by simpa [hr, hb] using h
        simpa [heq] using hb
      · simp [hr, hb] at h

/-- Boolean encoding for uniform machines over all runtime dimensions. -/
def finEncoding : FinEncoding Dense where
  Γ := Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := Bool.fintype

/-- Exact signed-field cost, including the sign and the magnitude's framing. -/
theorem encodeInt_length (z : ℤ) :
    (encodeInt z).length = 2 * (Computability.encodeNat z.natAbs).length + 2 := by
  simp [encodeInt, BinaryNatLists.natWireSize]

/-- Exact complete wire cost; neither headers nor zero coefficients are free. -/
theorem encode_length (A : Dense) :
    (encode A).length = A.rows + A.cols + 2 +
      (A.entries.map (fun z => 2 * (Computability.encodeNat z.natAbs).length + 2)).sum := by
  simp [encode, List.length_flatMap, encodeInt_length]
  omega

/-- Both dimensions are bounded even if their product is zero. -/
theorem dimensions_le_length (A : Dense) :
    A.rows + A.cols + 2 ≤ (encode A).length := by
  rw [encode_length]
  omega

/-- Every declared cell pays at least its sign and magnitude separator. -/
theorem cells_le_length (A : Dense) :
    2 * (A.rows * A.cols) ≤ (encode A).length := by
  have h : 2 * A.entries.length ≤
      (A.entries.map (fun z => 2 * (Computability.encodeNat z.natAbs).length + 2)).sum := by
    induction A.entries with
    | nil => simp
    | cons z zs ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
  rw [A.entryCount] at h
  rw [encode_length]
  omega

/-- Serialization cost under a genuine binary-magnitude bound. Supplying `b`
does not assert that a Smith algorithm can maintain such a bound. -/
theorem encode_length_le_of_entry_bits (A : Dense) (b : ℕ)
    (h : ∀ z ∈ A.entries, (Computability.encodeNat z.natAbs).length ≤ b) :
    (encode A).length ≤ A.rows + A.cols + 2 + A.rows * A.cols * (2 * b + 2) := by
  have hs :
      (A.entries.map (fun z => 2 * (Computability.encodeNat z.natAbs).length + 2)).sum ≤
        A.entries.length * (2 * b + 2) := by
    have hs := List.sum_le_length_nsmul
      (A.entries.map (fun z => 2 * (Computability.encodeNat z.natAbs).length + 2))
      (2 * b + 2) (by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
        have := h z hz
        omega)
    simpa using hs
  rw [A.entryCount] at hs
  rw [encode_length]
  omega

/-- Size bounds apply to actual accepted bit strings, not only canonical inputs
supplied externally with an uncharged dimension witness. -/
theorem accepted_dimensions_le_length {bits : List Bool} {A : Dense}
    (h : decode bits = some A) : A.rows + A.cols + 2 ≤ bits.length := by
  rw [← encode_of_decode h]
  exact dimensions_le_length A

-- Kernel-checked edge and rejection cases; no native execution is used.
example : decode (encode ⟨0, 3, [], rfl⟩) = some ⟨0, 3, [], rfl⟩ := decode_encode _
example : decode (encode ⟨3, 0, [], rfl⟩) = some ⟨3, 0, [], rfl⟩ := decode_encode _
example : decode (encode ⟨1, 2, [0, -7], rfl⟩) = some ⟨1, 2, [0, -7], rfl⟩ :=
  decode_encode _
example : decode [true, false, true, false, true, false] = none := by decide
example : decode (encode ⟨0, 0, [], rfl⟩ ++ [true]) = none := by decide

#print axioms decodeIntPrefix_encode_append
#print axioms decodeEntries_length
#print axioms decodeRaw_encode
#print axioms decode_encode
#print axioms encode_of_decode
#print axioms Dense.toMatrix
#print axioms encodeInt_length
#print axioms encode_length
#print axioms dimensions_le_length
#print axioms cells_le_length
#print axioms accepted_dimensions_le_length
#print axioms encode_length_le_of_entry_bits

end PhdThesisLean.SmithEncoding
