import PhdThesisLean.RationalNormAssembly

/-!
# Polynomial-time p-adic norm of a binary rational fraction

All routing, both valuation-power calls, pair retention, field exchange and
binary output serialization are performed by concrete finite TM2 machines.
The input/output format is the existing signed, framed Fraction encoding.
The prime is fixed in the finite program. Fractions need not be reduced.
This is a component of the loss verifier, not the entire verifier or NP theorem.
-/
namespace PhdThesisLean.RationalNorm

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool TM2ComputableInPolyTime)
open LeanNPHardness.MachineComposition LeanNPHardness.MachineAdapters
open RationalVerifierBounds

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime]

def powerPair (x : ℕ × ℕ) : ℕ × ℕ :=
  (p ^ padicValNat p x.1, p ^ padicValNat p x.2)

def powerFields (x : Fields) : Fields := (powerPair p x.1, x.2)

/-- Both powers, computed with the checked pair-retaining adapters. -/
noncomputable def pairPowerComputableInPolyTime :
    TM2ComputableInPolyTime pairEncoding pairEncoding (powerPair p) := by
  let power := FixedBasePowerMachine.valuationPowerComputableInPolyTime p (Fact.out : p.Prime).pos
  let left := pairReductionComputableInPolyTime finEncodingNatBool finEncodingNatBool
    finEncodingNatBool (fun n => p ^ padicValNat p n) power
  let right := pairRightComputableInPolyTime finEncodingNatBool finEncodingNatBool
    finEncodingNatBool (fun n => p ^ padicValNat p n) power
  let both := compositionComputableInPolyTime _ _ _ _ _ left right
  exact { both with
    outputsFun := fun x => by
      simpa only [Function.comp_def, powerPair, pairEncoding] using both.outputsFun x }

/-- Retaining the zero flag is also part of the finite machine and runtime. -/
noncomputable def fieldsPowerComputableInPolyTime :
    TM2ComputableInPolyTime fieldsEncoding fieldsEncoding (powerFields p) :=
  pairReductionComputableInPolyTime pairEncoding pairEncoding finEncodingBoolBool
    (powerPair p) (pairPowerComputableInPolyTime p)

/-- Exact equality of serialized output to the already-audited norm evaluator. -/
theorem assemble_power_prepare (x : Fraction) :
    assemble (powerFields p (prepare x)) = (x.norm p).encode := by
  by_cases hn : x.num = 0
  · simp [assemble, powerFields, prepare, Fraction.norm, hn]
  · simp [assemble, powerFields, powerPair, prepare, Fraction.norm, Fraction.encode,
      SmithEncoding.encodeInt, hn]

/-- Composition includes every inter-machine transfer, reset and cleanup. -/
noncomputable def serializedComputableInPolyTime :
    TM2ComputableInPolyTime fractionEncoding
      LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding
      (fun x => (x.norm p).encode) := by
  let evaluated := compositionComputableInPolyTime _ _ _ _ _
    Prepare.computableInPolyTime (fieldsPowerComputableInPolyTime p)
  let composed := compositionComputableInPolyTime _ _ _ _ _ evaluated Assemble.computableInPolyTime
  exact { composed with
    outputsFun := fun x => by
      simpa only [Function.comp_def, assemble_power_prepare] using composed.outputsFun x }

/-- A genuine polynomial-time binary-input/binary-output norm machine, with
no supplied arithmetic-cost or runtime hypothesis. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime fractionEncoding fractionEncoding (Fraction.norm p) where
  toTM2ComputableAux := (serializedComputableInPolyTime p).toTM2ComputableAux
  time := (serializedComputableInPolyTime p).time
  outputsFun x := (serializedComputableInPolyTime p).outputsFun x

/-- The machine computes the thesis norm even for unreduced signed fractions. -/
theorem value_correct (x : Fraction) :
    (x.norm p).value = padicNorm p (x.num / x.den) := Fraction.value_norm p x

/-- Exact input-format bridge for the thesis's binary rational encoding. -/
theorem ofRat_encode (q : ℚ) :
    (Fraction.ofRat q).encode = RationalWitnessEncoding.encodeRat q := rfl

/-- The component also computes the norm of every canonically encoded rational. -/
noncomputable def rationalOutputsInTime (q : ℚ) :
    TM2OutputsInTime (computableInPolyTime p).tm
      ((RationalWitnessEncoding.encodeRat q).map (computableInPolyTime p).inputAlphabet.symm)
      (some (((Fraction.ofRat q).norm p).encode.map (computableInPolyTime p).outputAlphabet.symm))
      ((computableInPolyTime p).time.eval (RationalWitnessEncoding.encodeRat q).length) :=
  (computableInPolyTime p).outputsFun (Fraction.ofRat q)

/-- The result need not be reduced; decoding it has the correct rational value. -/
theorem rational_value_correct (q : ℚ) :
    ((Fraction.ofRat q).norm p).value = padicNorm p q := by
  simpa only [Fraction.value_ofRat] using Fraction.value_norm p (Fraction.ofRat q)

/-- Polynomial output size in the original concrete bit length, including all
sign and frame bits. Zero is included. This is separate from runtime. -/
theorem output_length_le (x : Fraction) :
    (x.norm p).encode.length ≤ 4 * p.size * x.encode.length + 7 := by
  have h : x.Bounded x.encode.length := by
    simp only [Fraction.Bounded, Fraction.encode_length]
    omega
  have hb := Fraction.encode_length_le (Fraction.bounded_norm p h)
  nlinarith

#print axioms Prepare.outputsInTime
#print axioms Prepare.computableInPolyTime
#print axioms Assemble.outputsInTime
#print axioms Assemble.computableInPolyTime
#print axioms assemble_power_prepare
#print axioms pairPowerComputableInPolyTime
#print axioms fieldsPowerComputableInPolyTime
#print axioms computableInPolyTime
#print axioms rationalOutputsInTime
#print axioms rational_value_correct
#print axioms output_length_le

end PhdThesisLean.RationalNorm
