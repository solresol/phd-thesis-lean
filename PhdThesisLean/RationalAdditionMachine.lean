import PhdThesisLean.RationalAdditionRouting

/-!
# Polynomial-time addition and subtraction of binary fractions

The source is a pair of original Boolean fraction encodings. Three signed
multiplications, one signed addition/subtraction, source copying, denominator
projection, pair adapters and serialization are composed with checked runtime
bounds. There is no arithmetic-cost premise and no gcd normalization.
-/
namespace PhdThesisLean.RationalAddition

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)
open LeanNPHardness.MachineComposition LeanNPHardness.MachineAdapters
open RationalVerifierBounds RationalArithmetic

set_option backward.isDefEq.respectTransparency false

/-- The exact unreduced representation used by the existing loss evaluator. -/
def operation (subtract : Bool) (x : Fraction × Fraction) : Fraction :=
  if subtract then x.1.sub x.2 else x.1.add x.2

def numerator (subtract : Bool) (x : Fraction × Fraction) : ℤ :=
  SignedIntegerAddition.operation subtract (x.1.num * x.2.den) ((x.1.den : ℤ) * x.2.num)

def denominator (x : Fraction × Fraction) : ℤ := (x.1.den : ℤ) * x.2.den

theorem numerator_eq (subtract : Bool) (x : Fraction × Fraction) :
    numerator subtract x = (operation subtract x).num := by
  cases subtract <;> simp [numerator, operation, SignedIntegerAddition.operation,
    Fraction.add, Fraction.sub, Fraction.neg, sub_eq_add_neg, mul_comm]

theorem denominator_eq (subtract : Bool) (x : Fraction × Fraction) :
    denominator x = ((operation subtract x).den : ℤ) := by
  cases subtract <;> simp [denominator, operation, Fraction.add, Fraction.sub, Fraction.neg]

theorem value_correct (subtract : Bool) (x : Fraction × Fraction) :
    (operation subtract x).value =
      if subtract then x.1.value - x.2.value else x.1.value + x.2.value := by
  cases subtract <;> simp [operation]

noncomputable def numeratorComputableInPolyTime (subtract : Bool) :
    TM2ComputableInPolyTime encoding SignedIntegerMultiplication.integerEncoding (numerator subtract) := by
  exact compositionComputableInPolyTime _ _ _ _ _ crossProductsComputableInPolyTime
    (SignedIntegerAddition.computableInPolyTime subtract)

/-- Extract the two denominator fields from the original source and multiply
both variable binary integers. The discarded numerator fields are charged. -/
noncomputable def denominatorComputableInPolyTime :
    TM2ComputableInPolyTime encoding SignedIntegerMultiplication.integerEncoding denominator := by
  let routed := compositionComputableInPolyTime _ _ _ _ _ (Prepare.computableInPolyTime false)
    Right.computableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _ routed
    SignedIntegerMultiplication.computableInPolyTime
  exact { composed with
    outputsFun := fun x => by
      simpa only [Function.comp_def, prepare, Bool.false_eq_true, ↓reduceIte,
        Prod.snd, denominator] using composed.outputsFun x }

noncomputable def fieldsComputableInPolyTime (subtract : Bool) :
    TM2ComputableInPolyTime encoding productEncoding (fun x => (numerator subtract x, denominator x)) := by
  let left := pairReductionComputableInPolyTime encoding SignedIntegerMultiplication.integerEncoding
    encoding (numerator subtract) (numeratorComputableInPolyTime subtract)
  let right := pairRightComputableInPolyTime SignedIntegerMultiplication.integerEncoding
    encoding SignedIntegerMultiplication.integerEncoding denominator denominatorComputableInPolyTime
  let copied := compositionComputableInPolyTime _ _ _ _ _ Copy.computableInPolyTime left
  exact compositionComputableInPolyTime _ _ _ _ _ copied right

theorem assemble_operation (subtract : Bool) (x : Fraction × Fraction) :
    assemble true (numerator subtract x, denominator x) = (operation subtract x).encode := by
  rw [numerator_eq, denominator_eq subtract]
  simp [assemble, Fraction.encode, SmithEncoding.encodeInt]

/-- Actual finite-machine computation on original Boolean input words. Every
adapter transfer and both the output fields' construction are included. -/
noncomputable def computableInPolyTime (subtract : Bool) :
    TM2ComputableInPolyTime encoding RationalNorm.fractionEncoding (operation subtract) := by
  let serialized := compositionComputableInPolyTime _ _ _ _ _ (fieldsComputableInPolyTime subtract)
    (Assemble.computableInPolyTime true)
  exact { serialized with
    outputsFun := fun x => by
      simpa only [Function.comp_def, assemble_operation,
        LeanNPHardness.MachinePrimitives.RawBoolList.encode_eq, RationalNorm.fractionEncoding]
        using serialized.outputsFun x }

noncomputable def additionComputableInPolyTime :
    TM2ComputableInPolyTime encoding RationalNorm.fractionEncoding (fun x => x.1.add x.2) :=
  computableInPolyTime false

noncomputable def subtractionComputableInPolyTime :
    TM2ComputableInPolyTime encoding RationalNorm.fractionEncoding (fun x => x.1.sub x.2) :=
  computableInPolyTime true

/-- A separate linear output-size bound in the full input serialization. -/
theorem output_length_le (subtract : Bool) (x : Fraction × Fraction) :
    (operation subtract x).encode.length ≤ 2 * (encode x).length := by
  have hn := SignedIntegerAddition.output_length_le subtract
    (x.1.num * x.2.den) ((x.1.den : ℤ) * x.2.num)
  have hc := crossProducts_length_le x
  have hd := Fraction.size_mul x.1.den x.2.den
  change (SmithEncoding.encodeInt (numerator subtract x)).length ≤
    (SignedIntegerComparison.encode (crossProducts x)).length at hn
  have hd' : (operation subtract x).den = x.1.den * x.2.den := by
    cases subtract <;> rfl
  simp only [SmithEncoding.encodeInt_length,
    LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size] at hn
  change 2 * (numerator subtract x).natAbs.size + 2 ≤ _ at hn
  rw [numerator_eq] at hn
  simp only [Fraction.encode_length, hd']
  simp only [encode, List.length_append, Fraction.encode_length] at hc ⊢
  omega

#print axioms Copy.run
#print axioms Right.run
#print axioms numeratorComputableInPolyTime
#print axioms denominatorComputableInPolyTime
#print axioms fieldsComputableInPolyTime
#print axioms additionComputableInPolyTime
#print axioms subtractionComputableInPolyTime
#print axioms value_correct
#print axioms output_length_le

end PhdThesisLean.RationalAddition
