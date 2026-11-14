import PhdThesisLean.RationalColumnPairingMachine

/-!
# Linear-time column pairing and residual evaluation from separate lists

The source serializes the row coefficients and the certificate coefficients
in separate delimited lists. A finite machine pairs them, checks equal list
length, and produces exactly the existing dot-product input. Composing it with
the response-preserving residual machine charges all per-row work, starting
from this internal separated representation. Binary-record parsing, producing
these lists, retaining the certificate across observations, and the outer loop
remain outside this theorem.
-/
namespace PhdThesisLean.RationalColumnPairing

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open RationalVerifierBounds
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)
open LeanNPHardness.MachineComposition LeanNPHardness.MachineAdapters

set_option backward.isDefEq.respectTransparency false

noncomputable def listPairEncoding : FinEncoding (List Fraction × List Fraction) :=
  LeanNPHardness.PairEncoding.finEncoding RationalNormList.encoding RationalNormList.encoding

/-- The mathematical list of pairs is stored as two separate physical lists. -/
noncomputable def encoding : FinEncoding (List (Fraction × Fraction)) where
  Γ := Sum (Option Bool) (Option Bool)
  encode xs := listPairEncoding.encode (xs.map Prod.fst, xs.map Prod.snd)
  decode bits := do
    let (xs, ys) ← listPairEncoding.decode bits
    if xs.length = ys.length then some (xs.zip ys) else none
  decode_encode xs := by
    rw [listPairEncoding.decode_encode]
    simp [List.zip_map']
  ΓFin := inferInstance

theorem fields_encode (xs : List Fraction) :
    Machine.fields (xs.map Fraction.encode) = RationalSum.fields xs := by
  rw [Machine.fields, RationalSum.fields, List.flatMap_map]
  rfl

theorem input_encode (xs ys : List Fraction) :
    Machine.input (xs.map Fraction.encode) (ys.map Fraction.encode) =
      listPairEncoding.encode (xs, ys) := by
  simp only [Machine.input, fields_encode, listPairEncoding,
    LeanNPHardness.PairEncoding.finEncoding, RationalNormList.encoding]

theorem paired_output (xs : List (Fraction × Fraction)) :
    Machine.fields ((xs.map (fun x => x.1.encode)).zipWith List.append
      (xs.map (fun x => x.2.encode))) = RationalDotProduct.pairFields xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa [Machine.fields, Machine.field, RationalDotProduct.pairFields,
        RationalDotProduct.pairField, RationalArithmetic.encode, List.append_assoc] using
        congrArg (fun tail => RationalDotProduct.pairField x ++ tail) ih

/-- The source has one delimiter per fraction in each separate list. -/
theorem input_length (xs : List (Fraction × Fraction)) :
    (encoding.encode xs).length = (RationalDotProduct.pairFields xs).length + xs.length := by
  simp only [encoding, listPairEncoding, LeanNPHardness.PairEncoding.finEncoding,
    RationalNormList.encoding, List.length_append, List.length_map]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, RationalSum.fields, List.flatMap_cons, RationalSum.field,
        RationalDotProduct.pairFields, RationalDotProduct.pairField, RationalArithmetic.encode,
        List.length_append, List.length_map, List.length_cons, List.length_nil] at *
      omega

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encoding RationalDotProduct.encoding id where
  tm := Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 2
  outputsFun xs := by
    have h := Machine.outputsInTime ((xs.map Prod.fst).map Fraction.encode)
      ((xs.map Prod.snd).map Fraction.encode) (by simp)
    rw [input_encode] at h
    simp only [List.map_map, Function.comp_def, paired_output] at h
    simpa [encoding, RationalDotProduct.encoding, Equiv.refl] using h

/-- A distinct rejected word, with every private stack and partial output cleared. -/
noncomputable def rejectsInTime (xs ys : List Fraction) (h : xs.length ≠ ys.length) :
    TM2OutputsInTime Machine.computer (listPairEncoding.encode (xs, ys)) (some [none])
      (3 * (listPairEncoding.encode (xs, ys)).length + 5) := by
  have hr := Machine.rejectsInTime (xs.map Fraction.encode) (ys.map Fraction.encode) (by simpa using h)
  simpa only [input_encode] using hr

theorem reject_not_output (xs : List (Fraction × Fraction)) :
    RationalDotProduct.pairFields xs ≠ [none] := by
  intro h
  have he := congrArg (fun bits => RationalDotProduct.readPairs bits []) h
  rw [RationalDotProduct.readPairs_pairFields] at he
  contradiction

noncomputable def rowEncoding : FinEncoding (Fraction × List (Fraction × Fraction)) :=
  LeanNPHardness.PairEncoding.finEncoding RationalNorm.fractionEncoding encoding

/-- Pairing is performed on stacks while retaining the response; the complete
existing product/sum/subtraction machine then runs on the produced input. -/
noncomputable def rowComputableInPolyTime :
    TM2ComputableInPolyTime rowEncoding RationalNorm.fractionEncoding RationalRowResidual.evaluate := by
  let pairer := pairRightComputableInPolyTime RationalNorm.fractionEncoding encoding
    RationalDotProduct.encoding id computableInPolyTime
  exact compositionComputableInPolyTime _ _ _ _ _ pairer RationalRowResidual.computableInPolyTime

/-- Identify the physical source: response, separate row list, separate certificate list. -/
theorem row_encode {d : ℕ} (row β : Fin d → ℚ) (y : ℚ) :
    rowEncoding.encode (Fraction.ofRat y, RationalDotProduct.pairs row β) =
      (Fraction.ofRat y).encode.map Sum.inl ++
        (listPairEncoding.encode (List.ofFn (fun j => Fraction.ofRat (row j)),
          List.ofFn (fun j => Fraction.ofRat (β j)))).map Sum.inr := by
  simp [rowEncoding, encoding, LeanNPHardness.PairEncoding.finEncoding,
    RationalNorm.fractionEncoding, RationalDotProduct.pairs, List.map_ofFn, Function.comp_def]

noncomputable def rowOutputsInTime {d : ℕ} (row β : Fin d → ℚ) (y : ℚ) :
    TM2OutputsInTime rowComputableInPolyTime.tm
      ((rowEncoding.encode (Fraction.ofRat y, RationalDotProduct.pairs row β)).map
        rowComputableInPolyTime.inputAlphabet.symm)
      (some ((residual row β y).encode.map rowComputableInPolyTime.outputAlphabet.symm))
      (rowComputableInPolyTime.time.eval
        (rowEncoding.encode (Fraction.ofRat y, RationalDotProduct.pairs row β)).length) := by
  simpa only [RationalRowResidual.evaluate_row, RationalNorm.fractionEncoding] using!
    rowComputableInPolyTime.outputsFun (Fraction.ofRat y, RationalDotProduct.pairs row β)

/-- Original combined bits charge both separately stored lists and the response. -/
theorem row_input_length_le {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) (i : Fin r) :
    (rowEncoding.encode (Fraction.ofRat (y i), RationalDotProduct.pairs (A i) β)).length ≤
      8 * (totalBits A y B β)^2 + 12 * totalBits A y B β + 3 := by
  have hd := RationalDotProduct.row_input_length_le A y B β hr i
  have hs := source_bounds A y B β hr
  have hy := Fraction.encode_length_le (hs.2.2.2.1 i)
  simp only [rowEncoding, LeanNPHardness.PairEncoding.finEncoding_encode_length,
    RationalNorm.fractionEncoding, input_length, RationalDotProduct.pairs, List.length_ofFn]
  change (Fraction.ofRat (y i)).encode.length +
    ((RationalDotProduct.pairFields (RationalDotProduct.pairs (A i) β)).length + d) ≤ _
  have hdim := hs.2.1
  nlinarith

noncomputable def rowTime : Polynomial ℕ := rowComputableInPolyTime.time.comp
  (8 * Polynomial.X^2 + 12 * Polynomial.X + 3)

theorem rowTime_eval (s : ℕ) : rowTime.eval s =
    rowComputableInPolyTime.time.eval (8 * s^2 + 12 * s + 3) := by
  simp [rowTime, Polynomial.eval_comp]

/-- Full per-row pairing and arithmetic in polynomial original combined bits.
Source extraction and retaining/reusing the certificate for later rows are not
costed here; the machine consumes the two already delimited source lists. -/
noncomputable def boundedRowOutputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) (i : Fin r) :
    TM2OutputsInTime rowComputableInPolyTime.tm
      ((rowEncoding.encode (Fraction.ofRat (y i), RationalDotProduct.pairs (A i) β)).map
        rowComputableInPolyTime.inputAlphabet.symm)
      (some ((residual (A i) β (y i)).encode.map rowComputableInPolyTime.outputAlphabet.symm))
      (rowTime.eval (totalBits A y B β)) := by
  apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (rowOutputsInTime (A i) β (y i))
  rw [rowTime_eval]
  exact LeanNPHardness.MachineRuntime.polynomial_eval_mono _ (row_input_length_le A y B β hr i)

#print axioms computableInPolyTime
#print axioms rejectsInTime
#print axioms reject_not_output
#print axioms rowComputableInPolyTime
#print axioms row_encode
#print axioms boundedRowOutputsInTime

end PhdThesisLean.RationalColumnPairing
