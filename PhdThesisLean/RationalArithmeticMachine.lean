import PhdThesisLean.RationalArithmeticAssembly

/-!
# Polynomial-time fraction multiplication and comparison

These machines consume concatenated original Boolean fraction words. They
perform both integer products, retaining the other pair on actual stacks,
serialize the result and (for comparison) run the signed comparison machine.
All routing and adapter transfers are charged. Fractions may be unreduced;
this does not include whole-input validation, residual or loss evaluation.
-/
namespace PhdThesisLean.RationalArithmetic

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)
open LeanNPHardness.MachineComposition LeanNPHardness.MachineAdapters
open RationalVerifierBounds

set_option backward.isDefEq.respectTransparency false

def products (x : Fields) : ℤ × ℤ := (x.1.1 * x.1.2, x.2.1 * x.2.2)

/-- Execute both variable signed products, including preservation and transfers. -/
noncomputable def productsComputableInPolyTime :
    TM2ComputableInPolyTime fieldsEncoding productEncoding products := by
  let left := pairReductionComputableInPolyTime SignedIntegerComparison.encoding
    SignedIntegerMultiplication.integerEncoding SignedIntegerComparison.encoding
    (fun x => x.1 * x.2) SignedIntegerMultiplication.computableInPolyTime
  let right := pairRightComputableInPolyTime SignedIntegerMultiplication.integerEncoding
    SignedIntegerComparison.encoding SignedIntegerMultiplication.integerEncoding
    (fun x => x.1 * x.2) SignedIntegerMultiplication.computableInPolyTime
  let both := compositionComputableInPolyTime _ _ _ _ _ left right
  exact { both with
    outputsFun := fun x => by
      simpa only [Function.comp_def, products, fieldsEncoding, productEncoding] using both.outputsFun x }

noncomputable def serializedComputableInPolyTime (cross dropSign : Bool) :
    TM2ComputableInPolyTime encoding LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding
      (fun x => assemble dropSign (products (prepare cross x))) := by
  let evaluated := compositionComputableInPolyTime _ _ _ _ _
    (Prepare.computableInPolyTime cross) productsComputableInPolyTime
  exact compositionComputableInPolyTime _ _ _ _ _ evaluated (Assemble.computableInPolyTime dropSign)

theorem assemble_mul (x : Fraction × Fraction) :
    assemble true (products (prepare false x)) = (x.1.mul x.2).encode := by
  simp [assemble, products, prepare, Fraction.mul, Fraction.encode, SmithEncoding.encodeInt,
    Int.natAbs_mul]

/-- Exact multiplication in the existing unreduced fraction representation. -/
noncomputable def multiplicationComputableInPolyTime :
    TM2ComputableInPolyTime encoding RationalNorm.fractionEncoding (fun x => x.1.mul x.2) where
  toTM2ComputableAux := (serializedComputableInPolyTime false true).toTM2ComputableAux
  time := (serializedComputableInPolyTime false true).time
  outputsFun x := by
    simpa only [assemble_mul, LeanNPHardness.MachinePrimitives.RawBoolList.encode_eq,
      RationalNorm.fractionEncoding] using (serializedComputableInPolyTime false true).outputsFun x

/-- The right product is ordered to follow the input stream; multiplication
commutativity identifies it with the evaluator's conventional cross-product. -/
def crossProducts (x : Fraction × Fraction) : ℤ × ℤ :=
  (x.1.num * x.2.den, (x.1.den : ℤ) * x.2.num)

theorem assemble_crossProducts (x : Fraction × Fraction) :
    assemble false (products (prepare true x)) = SignedIntegerComparison.encode (crossProducts x) := rfl

/-- The cross-products are computed and serialized from the original fractions. -/
noncomputable def crossProductsComputableInPolyTime :
    TM2ComputableInPolyTime encoding SignedIntegerComparison.encoding crossProducts where
  toTM2ComputableAux := (serializedComputableInPolyTime true false).toTM2ComputableAux
  time := (serializedComputableInPolyTime true false).time
  outputsFun x := (serializedComputableInPolyTime true false).outputsFun x

/-- Complete fraction comparison, including construction of both cross-products. -/
noncomputable def comparisonComputableInPolyTime :
    TM2ComputableInPolyTime encoding LeanNPHardness.finEncodingBoolBool (fun x => x.1.le x.2) := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    crossProductsComputableInPolyTime SignedIntegerComparison.computableInPolyTime
  exact { composed with
    outputsFun := fun x => by
      simpa only [Function.comp_def, crossProducts, Fraction.le, mul_comm x.2.num]
        using composed.outputsFun x }

theorem multiplication_value_correct (x : Fraction × Fraction) :
    (x.1.mul x.2).value = x.1.value * x.2.value := Fraction.value_mul _ _

theorem comparison_value_correct (x : Fraction × Fraction) :
    x.1.le x.2 = true ↔ x.1.value ≤ x.2.value := Fraction.le_correct _ _

/-- Output growth is bounded independently of the composition runtime. -/
theorem multiplication_length_le (x : Fraction × Fraction) :
    (x.1.mul x.2).encode.length ≤ (encode x).length := by
  simp only [encode, List.length_append, Fraction.encode_length, Fraction.mul, Int.natAbs_mul]
  have hn := Fraction.size_mul x.1.num.natAbs x.2.num.natAbs
  have hd := Fraction.size_mul x.1.den x.2.den
  omega

theorem crossProducts_length_le (x : Fraction × Fraction) :
    (SignedIntegerComparison.encode (crossProducts x)).length ≤ (encode x).length := by
  simp only [encode, List.length_append, Fraction.encode_length, SignedIntegerComparison.encode_length,
    crossProducts, Int.natAbs_mul, Int.natAbs_natCast]
  have hl := Fraction.size_mul x.1.num.natAbs x.2.den
  have hr := Fraction.size_mul x.1.den x.2.num.natAbs
  omega

/-- Specialization to the actual loss checker. The sum itself is supplied;
this phase now includes all cross-product computation and serialization. -/
noncomputable def lossComparisonOutputsInTime (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) :
    TM2OutputsInTime comparisonComputableInPolyTime.tm
      ((encode (sum (losses p A y β), Fraction.ofRat B)).map
        comparisonComputableInPolyTime.inputAlphabet.symm)
      (some ([check p A y B β].map comparisonComputableInPolyTime.outputAlphabet.symm))
      (comparisonComputableInPolyTime.time.eval
        (encode (sum (losses p A y β), Fraction.ofRat B)).length) :=
  comparisonComputableInPolyTime.outputsFun (sum (losses p A y β), Fraction.ofRat B)

theorem loss_answer_correct (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) :
    (sum (losses p A y β)).le (Fraction.ofRat B) = true ↔ RationalWitnesses.loss p A y β ≤ B :=
  check_correct p A y B β

/-- The original regression input/certificate width bounds also charge the
complete two-fraction input to this final phase. -/
theorem loss_input_length_le (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    (encode (sum (losses p A y β), Fraction.ofRat B)).length ≤
      4 * compareWidth p (totalBits A y B β) + 6 := by
  have hl := Fraction.encode_length_le (loss_bounds p A y B β hr)
  have hb := Fraction.encode_length_le (source_bounds A y B β hr).2.2.1
  simp only [encode, List.length_append, compareWidth]
  omega

/-- A concrete polynomial in the original combined input/certificate bits.
Its outer polynomial is the checked composed machine's actual time bound. -/
noncomputable def lossComparisonTime (p : ℕ) : Polynomial ℕ :=
  comparisonComputableInPolyTime.time.comp
    (4 * (2 * Polynomial.C p.size * Polynomial.X^3 +
      3 * Polynomial.C p.size * Polynomial.X^2 +
      Polynomial.C (p.size + 3) * Polynomial.X + 1) + 6)

theorem lossComparisonTime_eval (p S : ℕ) :
    (lossComparisonTime p).eval S =
      comparisonComputableInPolyTime.time.eval (4 * compareWidth p S + 6) := by
  simp [lossComparisonTime, Polynomial.eval_comp, compareWidth_polynomial]

/-- Actual final-phase time in the original bits, including both cross-products.
The input is the already evaluated loss fraction and threshold, not the data. -/
noncomputable def boundedLossComparisonOutputsInTime (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    TM2OutputsInTime comparisonComputableInPolyTime.tm
      ((encode (sum (losses p A y β), Fraction.ofRat B)).map
        comparisonComputableInPolyTime.inputAlphabet.symm)
      (some ([check p A y B β].map comparisonComputableInPolyTime.outputAlphabet.symm))
      ((lossComparisonTime p).eval (totalBits A y B β)) := by
  apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (lossComparisonOutputsInTime p A y B β)
  rw [lossComparisonTime_eval]
  exact LeanNPHardness.MachineRuntime.polynomial_eval_mono _ (loss_input_length_le p A y B β hr)

#print axioms Prepare.run
#print axioms Prepare.outputsInTime
#print axioms Assemble.run
#print axioms Assemble.outputsInTime
#print axioms productsComputableInPolyTime
#print axioms multiplicationComputableInPolyTime
#print axioms crossProductsComputableInPolyTime
#print axioms comparisonComputableInPolyTime
#print axioms lossComparisonOutputsInTime
#print axioms loss_answer_correct
#print axioms boundedLossComparisonOutputsInTime

end PhdThesisLean.RationalArithmetic
