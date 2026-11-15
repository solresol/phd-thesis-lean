import PhdThesisLean.RationalCertificateBroadcastMachine

/-!
# Polynomial-time certificate reuse and observation source construction

One certificate is stored in the input, regardless of the number of rows.
The finite broadcast machine produces the ordered list of separated per-row
sources. In original input/certificate bit length `S`, construction takes at
most `12*S^2 + 16*S + 5` actual TM2 steps. This does not charge parsing the
original binary record, nor execute the residual machine on the produced list.
-/
namespace PhdThesisLean.RationalCertificateBroadcast

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open RationalVerifierBounds
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)
set_option backward.isDefEq.respectTransparency false

/-- Delimit a finite-alphabet word without interpreting its symbols. -/
def frame {Γ : Type} (bits : List Γ) : List (Option Γ) := bits.map some ++ [none]
def frames {Γ : Type} (words : List (List Γ)) : List (Option Γ) := words.flatMap frame

/-- The semantic decoder is separate from the broadcast execution proof. -/
def readFrames {α : Type} (e : FinEncoding α) :
    List (Option e.Γ) → List e.Γ → Option (List α)
  | [], [] => some []
  | [], _ :: _ => none
  | some b :: bs, acc => readFrames e bs (b :: acc)
  | none :: bs, acc => do
      let x ← e.decode acc.reverse
      let xs ← readFrames e bs []
      pure (x :: xs)

theorem readFrames_bits {α : Type} (e : FinEncoding α) (bits : List e.Γ)
    (tail : List (Option e.Γ)) (acc : List e.Γ) :
    readFrames e (bits.map some ++ tail) acc = readFrames e tail (bits.reverse ++ acc) := by
  induction bits generalizing acc with
  | nil => rfl
  | cons b bits ih => simpa [readFrames, List.reverse_cons, List.append_assoc] using ih (b :: acc)

theorem readFrames_frames {α : Type} (e : FinEncoding α) (xs : List α) :
    readFrames e (frames (xs.map e.encode)) [] = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [frames, List.map_cons, List.flatMap_cons] at ih ⊢
      simp [frame, List.append_assoc, readFrames_bits, readFrames, e.decode_encode, ih]

def listEncoding {α : Type} (e : FinEncoding α) : FinEncoding (List α) where
  Γ := Option e.Γ
  encode xs := frames (xs.map e.encode)
  decode bits := readFrames e bits []
  decode_encode := readFrames_frames e
  ΓFin := by
    letI := e.ΓFin
    infer_instance

abbrev Row := Fraction × List Fraction
noncomputable def rowEncoding : FinEncoding Row :=
  LeanNPHardness.PairEncoding.finEncoding RationalNorm.fractionEncoding RationalNormList.encoding
noncomputable def sourceEncoding : FinEncoding (List Fraction × List Row) :=
  LeanNPHardness.PairEncoding.finEncoding RationalNormList.encoding (listEncoding rowEncoding)
noncomputable def separatedRowEncoding : FinEncoding (Fraction × (List Fraction × List Fraction)) :=
  LeanNPHardness.PairEncoding.finEncoding RationalNorm.fractionEncoding
    RationalColumnPairing.listPairEncoding
noncomputable def outputEncoding := listEncoding separatedRowEncoding

def broadcast (x : List Fraction × List Row) : List (Fraction × (List Fraction × List Fraction)) :=
  x.2.map fun row => (row.1, (row.2, x.1))

theorem source_encode (cert : List Fraction) (rows : List Row) :
    sourceEncoding.encode (cert, rows) =
      Machine.input (RationalSum.fields cert) (rows.map rowEncoding.encode) := rfl

theorem outputField_encode (cert : List Fraction) (row : Row) :
    Machine.outputField (RationalSum.fields cert) (rowEncoding.encode row) =
      frame (separatedRowEncoding.encode (row.1, (row.2, cert))) := by
  simp [Machine.outputField, rowEncoding, separatedRowEncoding, RationalColumnPairing.listPairEncoding,
    LeanNPHardness.PairEncoding.finEncoding, RationalNorm.fractionEncoding, RationalNormList.encoding,
    Machine.rowCell, Machine.certCell, frame, List.map_append, List.map_map, Function.comp_def,
    List.append_assoc]

theorem output_encode (cert : List Fraction) (rows : List Row) :
    Machine.output (RationalSum.fields cert) (rows.map rowEncoding.encode) =
      outputEncoding.encode (broadcast (cert, rows)) := by
  simp only [Machine.output, List.flatMap_map, outputEncoding, listEncoding, frames,
    broadcast, List.map_map]
  congr 1
  funext row
  exact outputField_encode cert row

/-- A finite polynomial-time transformer; no cost premise is supplied. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime sourceEncoding outputEncoding broadcast where
  tm := Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X^2 + 8 * Polynomial.X + 5
  outputsFun x := by
    have h := Machine.outputsInTime (RationalSum.fields x.1) (x.2.map rowEncoding.encode)
    rw [output_encode, ← source_encode] at h
    simpa [Equiv.refl] using h

theorem output_length_le (cert : List Fraction) (rows : List Row) :
    (outputEncoding.encode (broadcast (cert, rows))).length ≤
      (sourceEncoding.encode (cert, rows)).length ^ 2 +
        (sourceEncoding.encode (cert, rows)).length := by
  rw [← output_encode, Machine.output_length, source_encode]
  have hc := Machine.count_le_length (rows.map rowEncoding.encode)
  simp only [List.length_map] at hc
  have hm := Nat.mul_le_mul_right (RationalSum.fields cert).length hc
  simp only [Machine.input, List.length_append, List.length_map]
  nlinarith

/-- Source length charges the original bits once, plus one delimiter per fraction. -/
theorem rational_fields_length_le (qs : List ℚ) :
    (RationalSum.fields (qs.map Fraction.ofRat)).length ≤
      2 * (RationalWitnessEncoding.encodeRats qs).length := by
  have he : (RationalSum.fields (qs.map Fraction.ofRat)).length =
      (qs.map (fun q => 2 * RationalWitnessBounds.ratBits q + 3)).sum + qs.length := by
    induction qs with
    | nil => rfl
    | cons q qs ih =>
        simp only [List.map_cons, RationalSum.fields, List.flatMap_cons, List.length_append,
          RationalSum.field, List.length_map, List.length_cons, List.length_nil,
          RationalNorm.ofRat_encode, RationalWitnessEncoding.encodeRat_length,
          List.sum_cons] at *
        omega
  have hc := RationalWitnessEncoding.count_le_encodeRats qs
  rw [he, RationalWitnessEncoding.encodeRats_length]
  rw [RationalWitnessEncoding.encodeRats_length] at hc
  omega

/-- The response comes first; row and certificate repetitions are retained. -/
def observations {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) : List Row :=
  List.ofFn fun i => (Fraction.ofRat (y i), List.ofFn fun j => Fraction.ofRat (A i j))
def certificate {d : ℕ} (β : Fin d → ℚ) : List Fraction :=
  List.ofFn fun j => Fraction.ofRat (β j)

theorem row_length (row : Row) :
    (frame (rowEncoding.encode row)).length = (RationalSum.fields (row.1 :: row.2)).length := by
  simp [frame, rowEncoding, LeanNPHardness.PairEncoding.finEncoding,
    RationalNorm.fractionEncoding, RationalNormList.encoding, RationalSum.fields, RationalSum.field]

theorem observations_length {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) :
    ((listEncoding rowEncoding).encode (observations A y)).length =
      (RationalSum.fields ((RationalWitnessEncoding.inputEntries A y).map Fraction.ofRat)).length := by
  simp only [listEncoding, frames, List.length_flatMap, List.map_map]
  conv_lhs => arg 1; arg 1; ext row; rw [Function.comp_apply, row_length]
  simp [observations, RationalWitnessEncoding.inputEntries, RationalSum.fields,
    List.map_flatten, List.length_flatMap,
    List.map_ofFn, List.sum_ofFn, Function.comp_def]

/-- Linear source-size bound in original bits, including empty dimensions. -/
theorem source_length_le {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) :
    (sourceEncoding.encode (certificate β, observations A y)).length ≤
      2 * totalBits A y B β := by
  simp only [sourceEncoding, LeanNPHardness.PairEncoding.finEncoding_encode_length,
    RationalNormList.encoding, observations_length]
  have hc := rational_fields_length_le (List.ofFn β)
  have hd := rational_fields_length_le (RationalWitnessEncoding.inputEntries A y)
  simp only [List.map_ofFn, Function.comp_def] at hc
  simp only [certificate, totalBits, RationalWitnessEncoding.encodeInput, List.length_append]
  omega

/-- Exact produced row words, in the existing evaluator's physical input format. -/
theorem regression_output {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (β : Fin d → ℚ) :
    outputEncoding.encode (broadcast (certificate β, observations A y)) =
      frames (List.ofFn fun i => RationalColumnPairing.rowEncoding.encode
        (Fraction.ofRat (y i), RationalDotProduct.pairs (A i) β)) := by
  simp only [outputEncoding, listEncoding, broadcast, observations, List.map_ofFn]
  congr 2
  funext i
  rw [RationalColumnPairing.row_encode]
  rfl

/-- The single original certificate is copied for every observation by the
machine. Original-record parsing and subsequent row evaluation are separate. -/
noncomputable def regressionOutputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) :
    TM2OutputsInTime Machine.computer
      (sourceEncoding.encode (certificate β, observations A y))
      (some (frames (List.ofFn fun i => RationalColumnPairing.rowEncoding.encode
        (Fraction.ofRat (y i), RationalDotProduct.pairs (A i) β))))
      (12 * (totalBits A y B β)^2 + 16 * totalBits A y B β + 5) := by
  have h := Machine.outputsInTime (RationalSum.fields (certificate β))
    ((observations A y).map rowEncoding.encode)
  rw [← source_encode, output_encode, regression_output] at h
  apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono h
  have hs := source_length_le A y B β
  nlinarith [sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _) |>.2 hs]

#print axioms Machine.rows_run
#print axioms Machine.outputsInTime
#print axioms computableInPolyTime
#print axioms source_length_le
#print axioms regression_output
#print axioms regressionOutputsInTime

end PhdThesisLean.RationalCertificateBroadcast
