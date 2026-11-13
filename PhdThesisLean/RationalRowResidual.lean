import PhdThesisLean.RationalDotProduct
import PhdThesisLean.AllDifferentCSPUnaryBridge

/-!
# Polynomial-time evaluation of one rational regression residual

The runtime-length input is a response paired with the serialized column pairs.
The machine retains the response during product traversal and accumulation,
removes the pair tags, and subtracts the result. The exact unreduced output
agrees with the existing left-subtraction evaluator. Original-record parsing,
column pairing and traversal of all observations remain separate phases.
-/
namespace PhdThesisLean.RationalRowResidual

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open RationalVerifierBounds
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)
open LeanNPHardness.MachineComposition LeanNPHardness.MachineAdapters

set_option backward.isDefEq.respectTransparency false

def encoding : FinEncoding (Fraction × List (Fraction × Fraction)) :=
  LeanNPHardness.PairEncoding.finEncoding RationalNorm.fractionEncoding RationalDotProduct.encoding

def taggedFractions : FinEncoding (Fraction × Fraction) :=
  LeanNPHardness.PairEncoding.finEncoding RationalNorm.fractionEncoding RationalNorm.fractionEncoding

def untag : Sum Bool Bool → Bool := Sum.elim id id

theorem untag_encode (x : Fraction × Fraction) :
    (taggedFractions.encode x).map untag = RationalArithmetic.encode x := by
  simp [taggedFractions, LeanNPHardness.PairEncoding.finEncoding, RationalNorm.fractionEncoding,
    List.map_append, List.map_map, untag, Function.comp_def, RationalArithmetic.encode]

/-- Two complete passes remove tags in `2L+2` transitions, retaining all bits. -/
noncomputable def untagComputableInPolyTime :
    TM2ComputableInPolyTime taggedFractions RationalArithmetic.encoding id where
  tm := AllDifferentCSPMachine.UnaryBridgeMachine.computer (Sum.inl false) untag
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun x := by
    have h := AllDifferentCSPMachine.UnaryBridgeMachine.outputsInTime (Sum.inl false) untag
        (taggedFractions.encode x)
    rw [PhdThesisLean.RationalRowResidual.untag_encode] at h
    simpa [Equiv.refl, RationalArithmetic.encoding] using h

def evaluate (x : Fraction × List (Fraction × Fraction)) : Fraction :=
  x.1.sub (sum (x.2.map RationalDotProduct.multiply))

/-- The response stays on actual stacks through the complete dot-product run. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encoding RationalNorm.fractionEncoding evaluate := by
  let dot := pairRightComputableInPolyTime RationalNorm.fractionEncoding
    RationalDotProduct.encoding RationalNorm.fractionEncoding
    (fun xs => sum (xs.map RationalDotProduct.multiply)) RationalDotProduct.sumComputableInPolyTime
  let serialized := compositionComputableInPolyTime _ _ _ _ _ dot untagComputableInPolyTime
  exact compositionComputableInPolyTime _ _ _ _ _ serialized
    RationalAddition.subtractionComputableInPolyTime

theorem sub_add (z a b : Fraction) : (z.sub a).sub b = z.sub (a.add b) := by
  cases z; cases a; cases b
  simp only [Fraction.sub, Fraction.add, Fraction.neg, Nat.cast_mul]
  congr 1 <;> ring

theorem sub_zero (z : Fraction) : z.sub Fraction.zero = z := by
  cases z
  simp [Fraction.sub, Fraction.add, Fraction.neg, Fraction.zero]

theorem fold_sub_eq (xs : List Fraction) (z a : Fraction) :
    xs.foldl Fraction.sub (z.sub a) = z.sub (xs.foldl Fraction.add a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons b xs ih => simpa only [List.foldl_cons, sub_add] using ih (a.add b)

theorem fold_sub_eq_sub_sum (xs : List Fraction) (z : Fraction) :
    xs.foldl Fraction.sub z = z.sub (sum xs) := by
  simpa only [sub_zero, sum] using fold_sub_eq xs z Fraction.zero

theorem evaluate_row {d : ℕ} (row β : Fin d → ℚ) (y : ℚ) :
    evaluate (Fraction.ofRat y, RationalDotProduct.pairs row β) = residual row β y := by
  rw [evaluate, RationalDotProduct.map_pairs, RationalVerifierBounds.residual, fold_sub_eq_sub_sum]

theorem value_correct {d : ℕ} (row β : Fin d → ℚ) (y : ℚ) :
    (evaluate (Fraction.ofRat y, RationalDotProduct.pairs row β)).value =
      y - ∑ j, row j * β j := by
  rw [evaluate_row, value_residual]

/-- This run produces the exact stored residual, not only a value-equivalent fraction. -/
noncomputable def rowOutputsInTime {d : ℕ} (row β : Fin d → ℚ) (y : ℚ) :
    TM2OutputsInTime computableInPolyTime.tm
      ((encoding.encode (Fraction.ofRat y, RationalDotProduct.pairs row β)).map
        computableInPolyTime.inputAlphabet.symm)
      (some ((residual row β y).encode.map computableInPolyTime.outputAlphabet.symm))
      (computableInPolyTime.time.eval
        (encoding.encode (Fraction.ofRat y, RationalDotProduct.pairs row β)).length) := by
  simpa only [evaluate_row, RationalNorm.fractionEncoding] using!
    computableInPolyTime.outputsFun (Fraction.ofRat y, RationalDotProduct.pairs row β)

theorem input_length_le {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) (i : Fin r) :
    (encoding.encode (Fraction.ofRat (y i), RationalDotProduct.pairs (A i) β)).length ≤
      8 * (totalBits A y B β)^2 + 11 * totalBits A y B β + 3 := by
  have hd := RationalDotProduct.row_input_length_le A y B β hr i
  have hy := Fraction.encode_length_le ((source_bounds A y B β hr).2.2.2.1 i)
  simp only [encoding, LeanNPHardness.PairEncoding.finEncoding_encode_length,
    RationalNorm.fractionEncoding, RationalDotProduct.encoding]
  nlinarith

noncomputable def time : Polynomial ℕ := computableInPolyTime.time.comp
  (8 * Polynomial.X^2 + 11 * Polynomial.X + 3)

theorem time_eval (s : ℕ) : time.eval s =
    computableInPolyTime.time.eval (8 * s^2 + 11 * s + 3) := by
  simp [time, Polynomial.eval_comp]

/-- Complete residual arithmetic in polynomial original combined bit size.
The machine starts with the response and paired row already serialized. -/
noncomputable def boundedRowOutputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) (i : Fin r) :
    TM2OutputsInTime computableInPolyTime.tm
      ((encoding.encode (Fraction.ofRat (y i), RationalDotProduct.pairs (A i) β)).map
        computableInPolyTime.inputAlphabet.symm)
      (some ((residual (A i) β (y i)).encode.map computableInPolyTime.outputAlphabet.symm))
      (time.eval (totalBits A y B β)) := by
  apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (rowOutputsInTime (A i) β (y i))
  rw [time_eval]
  exact LeanNPHardness.MachineRuntime.polynomial_eval_mono _ (input_length_le A y B β hr i)

#print axioms untagComputableInPolyTime
#print axioms computableInPolyTime
#print axioms evaluate_row
#print axioms value_correct
#print axioms boundedRowOutputsInTime

end PhdThesisLean.RationalRowResidual
