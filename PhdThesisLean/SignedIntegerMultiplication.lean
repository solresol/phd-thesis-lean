import PhdThesisLean.SignedMultiplicationAssembly

/-!
# Polynomial-time multiplication of signed binary integers

The input is two concatenated signed/framed integer words; the output is one
word in exactly the same integer format. Actual finite machines parse the
signs and frames, multiply the magnitudes, retain the sign, correct zero's sign
and serialize the result. The checked sequential and pair adapters charge
all transfers. This is an arithmetic component, not a whole regression verifier.
-/
namespace PhdThesisLean.SignedIntegerMultiplication

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool TM2ComputableInPolyTime)
open LeanNPHardness.MachineComposition LeanNPHardness.MachineAdapters

set_option backward.isDefEq.respectTransparency false

def decodeInteger (bits : List Bool) : Option ℤ := do
  let (z, rest) ← SmithEncoding.decodeIntPrefix bits
  if rest.isEmpty then some z else none

@[simp] theorem decodeInteger_encode (z : ℤ) :
    decodeInteger (SmithEncoding.encodeInt z) = some z := by
  have h := SmithEncoding.decodeIntPrefix_encode_append z []
  simp only [List.append_nil] at h
  simp [decodeInteger, h]

def integerEncoding : FinEncoding ℤ where
  Γ := Bool
  encode := SmithEncoding.encodeInt
  decode := decodeInteger
  decode_encode := decodeInteger_encode
  ΓFin := inferInstance

def multiplyFields (x : Fields) : ProductFields := (x.1.1 * x.1.2, x.2)

/-- Magnitude multiplication while preserving the sign on actual machine stacks. -/
noncomputable def fieldsComputableInPolyTime :
    TM2ComputableInPolyTime fieldsEncoding productEncoding multiplyFields :=
  pairReductionComputableInPolyTime pairEncoding finEncodingNatBool finEncodingBoolBool
    (fun x => x.1 * x.2) BinaryMultiplication.computableInPolyTime

/-- The sign xor, gated by nonzero magnitude, is precisely the product sign. -/
theorem product_sign (a b : ℤ) :
    (xor (decide (a < 0)) (decide (b < 0)) && decide (a.natAbs * b.natAbs ≠ 0)) =
      decide (a * b < 0) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have hmag : a.natAbs * b.natAbs ≠ 0 := by
    simpa only [ne_eq, mul_eq_zero, Int.natAbs_eq_zero, not_or] using And.intro ha hb
  by_cases hsa : a < 0 <;> by_cases hsb : b < 0
  · have hp : ¬a * b < 0 := not_lt.mpr (le_of_lt (mul_pos_of_neg_of_neg hsa hsb))
    simp [hsa, hsb, hp, hmag]
  · have hp : a * b < 0 := mul_neg_of_neg_of_pos hsa (by omega)
    simp [hsa, hsb, hp, hmag]
  · have hp : a * b < 0 := mul_neg_of_pos_of_neg (by omega) hsb
    simp [hsa, hsb, hp, hmag]
  · have hp : ¬a * b < 0 := not_lt.mpr (mul_nonneg (by omega) (by omega))
    simp [hsa, hsb, hp, hmag]

/-- Exact output-format equality, including the canonical positive sign of zero. -/
theorem assemble_multiply_prepare (x : ℤ × ℤ) :
    assemble (multiplyFields (prepare x)) = SmithEncoding.encodeInt (x.1 * x.2) := by
  simp only [assemble, multiplyFields, prepare, SmithEncoding.encodeInt,
    product_sign, Int.natAbs_mul]

noncomputable def serializedComputableInPolyTime :
    TM2ComputableInPolyTime SignedIntegerComparison.encoding
      LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding
      (fun x => SmithEncoding.encodeInt (x.1 * x.2)) := by
  let evaluated := compositionComputableInPolyTime _ _ _ _ _
    Prepare.computableInPolyTime fieldsComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _ evaluated Assemble.computableInPolyTime
  exact { composed with
    outputsFun := fun x => by
      simpa only [Function.comp_def, assemble_multiply_prepare] using composed.outputsFun x }

/-- Polynomial time in the full Boolean input length, without an arithmetic-cost
or runtime premise. The input domain consists of encoded integer pairs. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime SignedIntegerComparison.encoding integerEncoding
      (fun x => x.1 * x.2) where
  toTM2ComputableAux := serializedComputableInPolyTime.toTM2ComputableAux
  time := serializedComputableInPolyTime.time
  outputsFun x := serializedComputableInPolyTime.outputsFun x

/-- The framed result is no longer than the concatenated framed operands. -/
theorem output_length_le (x : ℤ × ℤ) :
    (SmithEncoding.encodeInt (x.1 * x.2)).length ≤ (SignedIntegerComparison.encode x).length := by
  simp only [SmithEncoding.encodeInt_length, SignedIntegerComparison.encode_length,
    LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size, Int.natAbs_mul]
  have h := RationalVerifierBounds.Fraction.size_mul x.1.natAbs x.2.natAbs
  omega

#print axioms Prepare.run
#print axioms Prepare.outputsInTime
#print axioms Assemble.run
#print axioms Assemble.outputsInTime
#print axioms fieldsComputableInPolyTime
#print axioms product_sign
#print axioms assemble_multiply_prepare
#print axioms computableInPolyTime
#print axioms output_length_le

end PhdThesisLean.SignedIntegerMultiplication
