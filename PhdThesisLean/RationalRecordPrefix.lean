import PhdThesisLean.RationalDimensionRouting
import PhdThesisLean.RationalRectangular

/-!
# Original binary dimensions and counted rational data

The finite machine starts on the original binary record, reads and safely
expands both dimension headers, retains them during counted-data validation,
and preserves the exact raw suffix. Each dimension retains its terminator,
so a failed header remains distinguishable from a valid zero dimension.
Rectangular count agreement and the threshold/certificate suffix are separate
stages; this module does not assert a whole-record verifier.
-/
namespace PhdThesisLean.RationalRecordPrefix

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open LeanNPHardness RationalVerifierBounds RationalDimensionRouting
open LeanNPHardness.MachineComposition LeanNPHardness.MachineAdapters
set_option backward.isDefEq.respectTransparency false

abbrev Result := Bits × Bits × Bits

def outputEncoding : FinEncoding Result :=
  PairEncoding.finEncoding RationalFractionPrefix.Machine.outputEncoding
    (PairEncoding.finEncoding RationalFractionPrefix.Machine.outputEncoding
      RationalFractionPrefix.Machine.outputEncoding)

def columns (bits : List Bool) : Bits × Bits :=
  let x := splitCount bits
  (x.1,RationalCountedList.output x.2)

def output (bits : List Bool) : Result :=
  let x := splitCount bits
  (x.1,columns x.2)

/-- All three parsers and the preservation of both headers are machine executions. -/
noncomputable def columnsComputableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding
      (PairEncoding.finEncoding RationalFractionPrefix.Machine.outputEncoding
        RationalFractionPrefix.Machine.outputEncoding) columns :=
  compositionComputableInPolyTime _ _ _ _ _ RationalDimensionRouting.computableInPolyTime
    (pairRightComputableInPolyTime _ _ _ _ RationalCountedList.computableInPolyTime)

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding outputEncoding output :=
  compositionComputableInPolyTime _ _ _ _ _ RationalDimensionRouting.computableInPolyTime
    (pairRightComputableInPolyTime _ _ _ _ columnsComputableInPolyTime)

def complete (x : Result) : Prop := x.1 ≠ [] ∧ x.2.1 ≠ [] ∧ x.2.2 ≠ []

/-- Success indicators describe parsing, not rectangular agreement or exhaustion. -/
theorem output_encode (r d : ℕ) (xs : List Fraction) (tail : List Bool)
    (hd : d ≤ (BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail).length)
    (hr : r ≤ (BinaryNatLists.encodeNat d ++ BinaryNatLists.encodeNat xs.length ++
      xs.flatMap Fraction.encode ++ tail).length) :
    output (BinaryNatLists.encodeNat r ++ BinaryNatLists.encodeNat d ++
      BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail) =
        (countWord r,countWord d,
          RationalCountedFields.wire (xs.map Fraction.encode) ++ none :: tail.map some) := by
  simp only [List.append_assoc] at hr hd ⊢
  simp only [output, splitCount_encode_append, hr, ite_true, columns, hd]
  simpa only [List.append_assoc] using congrArg (fun fs => (countWord r,countWord d,fs))
    (RationalCountedList.output_encode_append xs tail)

/-- On arbitrary raw words, both dimensions are canonical and payload bounded,
and exactly the declared number of fractions have been checked. The suffix is
retained literally and is not claimed to be valid. -/
theorem complete_iff (bits : List Bool) : complete (output bits) ↔
    ∃ (r d : ℕ) (xs : List Fraction) (tail : List Bool),
      bits = BinaryNatLists.encodeNat r ++ BinaryNatLists.encodeNat d ++
        BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail ∧
      r ≤ (BinaryNatLists.encodeNat d ++ BinaryNatLists.encodeNat xs.length ++
        xs.flatMap Fraction.encode ++ tail).length ∧
      d ≤ (BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail).length := by
  constructor
  · intro h
    rcases splitCount_cases bits with hf | ⟨r,rest,hs,he,hr⟩
    · simp [complete, output, hf] at h
    · rcases splitCount_cases rest with hf | ⟨d,data,hsd,hed,hd⟩
      · simp [complete, output, hs, columns, hf] at h
      · have hc : RationalCountedList.output data ≠ [] := by
          simpa [complete, output, hs, columns, hsd, countWord] using h
        obtain ⟨xs,tail,hdata⟩ := (RationalCountedList.output_success_iff data).1 hc
        refine ⟨r,d,xs,tail,?_,?_,?_⟩
        · simp [he,hed,hdata,List.append_assoc]
        · simpa [hed,hdata,List.append_assoc] using hr
        · simpa [hdata,List.append_assoc] using hd
  · rintro ⟨r,d,xs,tail,rfl,hr,hd⟩
    rw [output_encode r d xs tail hd hr]
    simp [complete,countWord]

/-- A stage failure cannot be confused with the delimiter for a zero count. -/
theorem incomplete_iff (bits : List Bool) : ¬ complete (output bits) ↔
    ¬ ∃ (r d : ℕ) (xs : List Fraction) (tail : List Bool),
      bits = BinaryNatLists.encodeNat r ++ BinaryNatLists.encodeNat d ++
        BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail ∧
      r ≤ (BinaryNatLists.encodeNat d ++ BinaryNatLists.encodeNat xs.length ++
        xs.flatMap Fraction.encode ++ tail).length ∧
      d ≤ (BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail).length :=
  not_congr (complete_iff bits)

theorem splitCount_length_le (bits : List Bool) :
    (splitCount bits).1.length + (splitCount bits).2.length ≤ 2*bits.length+1 := by
  have h := tagged_length_le true (BoundedBinaryCount.output bits)
  rw [tagged_encode] at h
  simp only [pairEncoding, PairEncoding.finEncoding, RationalFractionPrefix.Machine.outputEncoding,
    MachinePrimitives.RawBoolList.finEncoding, List.length_append, List.length_map] at h
  exact h.trans (BoundedBinaryCount.output_length_le bits)

theorem output_length_le (bits : List Bool) :
    (outputEncoding.encode (output bits)).length ≤ 8*bits.length+7 := by
  have hr := splitCount_length_le bits
  have hd := splitCount_length_le (splitCount bits).2
  have hf := RationalCountedList.output_length_le (splitCount (splitCount bits).2).2
  simp only [outputEncoding, PairEncoding.finEncoding, RationalFractionPrefix.Machine.outputEncoding,
    List.length_append,List.length_map,output,columns,id_eq]
  omega

/-- Total finite-machine time on every binary word, with no typed input premise. -/
noncomputable def outputsInTime (bits : List Bool) :
    Turing.TM2OutputsInTime computableInPolyTime.tm
      (bits.map computableInPolyTime.inputAlphabet.symm)
      (some ((outputEncoding.encode (output bits)).map computableInPolyTime.outputAlphabet.symm))
      (computableInPolyTime.time.eval bits.length) := computableInPolyTime.outputsFun bits

/-- Exact original regression record, including any suffix following the threshold.
Positive row count ensures that the column dimension is bounded by its payload. -/
theorem output_original_append {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (tail : List Bool) (hr : 0 < r) :
    output (RationalWitnessEncoding.encodeInput A y B ++ tail) =
      (countWord r,countWord d,
        RationalCountedFields.wire
          ((RationalWitnessEncoding.inputEntries A y).map RationalWitnessEncoding.encodeRat) ++
          none :: (RationalWitnessEncoding.encodeRat B ++ tail).map some) := by
  let rest := RationalWitnessEncoding.encodeRats (RationalWitnessEncoding.inputEntries A y) ++
    RationalWitnessEncoding.encodeRat B ++ tail
  have hd : d ≤ rest.length := by
    have h := RationalWitnessEncoding.count_le_encodeRats (RationalWitnessEncoding.inputEntries A y)
    rw [RationalWitnessEncoding.inputEntries_length] at h
    simp only [rest,List.length_append]
    nlinarith
  have hrows : r ≤ (BinaryNatLists.encodeNat d ++ rest).length := by
    have h := RationalWitnessEncoding.count_le_encodeRats (RationalWitnessEncoding.inputEntries A y)
    rw [RationalWitnessEncoding.inputEntries_length] at h
    simp only [rest,List.length_append]
    nlinarith
  have he : RationalWitnessEncoding.encodeInput A y B ++ tail =
      BinaryNatLists.encodeNat r ++ (BinaryNatLists.encodeNat d ++ rest) := by
    simp [rest,RationalWitnessEncoding.encodeInput,List.append_assoc]
  rw [he]
  simp only [output,splitCount_encode_append,hrows,ite_true,columns,hd]
  simpa [rest,List.append_assoc] using
    congrArg (fun fields => (countWord r,countWord d,fields))
      (RationalCountedList.output_encodeRats_append (RationalWitnessEncoding.inputEntries A y)
        (RationalWitnessEncoding.encodeRat B ++ tail))

theorem output_original {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    output (RationalWitnessEncoding.encodeInput A y B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β)) =
      (countWord r,countWord d,RationalRectangularFields.parsedData A y B β) := by
  rw [output_original_append A y B _ hr]
  simp [RationalRectangularFields.parsedData,RationalRectangularFields.dataSuffix,
    RationalCountedList.output_encodeRats_append]

/-- End-to-end prefix parsing charged to original input plus certificate bits;
this time includes the dimension construction and data-parser transfers. -/
noncomputable def originalOutputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    Turing.TM2OutputsInTime computableInPolyTime.tm
      ((RationalWitnessEncoding.encodeInput A y B ++
        RationalWitnessEncoding.encodeRats (List.ofFn β)).map computableInPolyTime.inputAlphabet.symm)
      (some ((outputEncoding.encode
        (countWord r,countWord d,RationalRectangularFields.parsedData A y B β)).map
          computableInPolyTime.outputAlphabet.symm))
      (computableInPolyTime.time.eval (totalBits A y B β)) := by
  simpa only [output_original A y B β hr, List.length_append, totalBits] using!
    outputsInTime (RationalWitnessEncoding.encodeInput A y B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β))

#print axioms computableInPolyTime
#print axioms complete_iff
#print axioms output_original
#print axioms output_length_le
#print axioms originalOutputsInTime

end PhdThesisLean.RationalRecordPrefix
