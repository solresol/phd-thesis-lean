import PhdThesisLean.RationalRectangleAssembly

/-!
# Original binary input through rectangular data validation

This pipeline reads both binary dimensions, validates the counted rational data,
constructs the physical rectangular-stage input while retaining the column count,
and executes row partitioning. All machine transfers and copying are charged to
the original binary word. Threshold and certificate suffix validation is separate.
-/
namespace PhdThesisLean.RationalRecordData

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open LeanNPHardness RationalVerifierBounds RationalDimensionRouting
open LeanNPHardness.MachineComposition LeanNPHardness.MachineAdapters
set_option backward.isDefEq.respectTransparency false

abbrev Result := ℕ × List RationalRectangularFields.Cell

def outputEncoding : FinEncoding Result :=
  PairEncoding.finEncoding RationalTailAssembly.unaryEncoding RationalRectangularFields.outputEncoding

def prepared (bits : List Bool) := RationalRectangleAssembly.prepare (RationalRecordPrefix.output bits)

def output (bits : List Bool) : Result :=
  let x := prepared bits
  (x.1,RationalRectangularFields.output x.2.1 x.2.2.1 x.2.2.2)

noncomputable def preparedComputableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding
      RationalRectangleAssembly.preparedEncoding prepared := by
  let raw := compositionComputableInPolyTime _ _ _ _ _
    RationalRecordPrefix.computableInPolyTime RationalRectangleAssembly.computableInPolyTime
  exact { raw with
    outputsFun := fun bits => by
      simpa only [Function.comp_apply,RationalRectangleAssembly.output_prefix,
        RationalRectangleAssembly.outputEncoding,prepared] using! raw.outputsFun bits }

/-- Includes binary dimension parsing, counted-list parsing, actual header
assembly and copying, rectangular validation, and all generic transfers. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding outputEncoding output :=
  compositionComputableInPolyTime _ _ _ _ _ preparedComputableInPolyTime
    (pairRightComputableInPolyTime _ _ _ _ RationalRectangularFields.computableInPolyTime)

/-- A malformed original prefix always fails rectangular validation. -/
theorem output_of_incomplete (bits : List Bool)
    (h : ¬ RationalRecordPrefix.complete (RationalRecordPrefix.output bits)) :
    (output bits).2 = [] := by
  let x := RationalRecordPrefix.output bits
  change ¬ (x.1 ≠ [] ∧ x.2.1 ≠ [] ∧ x.2.2 ≠ []) at h
  change RationalRectangularFields.output (RationalRectangleAssembly.prepare x).2.1
    (RationalRectangleAssembly.prepare x).2.2.1 (RationalRectangleAssembly.prepare x).2.2.2 = []
  by_cases hn : x.1 = [] ∨ x.2.1 = []
  · simp only [RationalRectangleAssembly.prepare,hn,ite_true]
    rfl
  · have hc : x.2.2 = [] := by tauto
    simp only [RationalRectangleAssembly.prepare,hn,ite_false,hc]
    cases x.1.length-1 <;> simp [RationalRectangularFields.output,
      RationalRectangularFields.rows,RationalRectangularFields.ending,
      RationalRectangularFields.field,RationalRectangularFields.render]

theorem output_encode (r d : ℕ) (xs : List Fraction) (tail : List Bool)
    (hd : d ≤ (BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail).length)
    (hr : r ≤ (BinaryNatLists.encodeNat d ++ BinaryNatLists.encodeNat xs.length ++
      xs.flatMap Fraction.encode ++ tail).length) :
    output (BinaryNatLists.encodeNat r ++ BinaryNatLists.encodeNat d ++
      BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail) =
      (d,RationalRectangularFields.output r d
        (RationalCountedFields.wire (xs.map Fraction.encode) ++ none :: tail.map some)) := by
  simp only [output,prepared,RationalRecordPrefix.output_encode r d xs tail hd hr]
  simp [RationalRectangleAssembly.prepare,countWord]

/-- Accepted original prefixes have exactly the declared rectangular data count.
The raw suffix is preserved and is deliberately not validated at this stage. -/
theorem output_success_iff (bits : List Bool) : (output bits).2 ≠ [] ↔
    ∃ (r d : ℕ) (xs : List Fraction) (tail : List Bool),
      bits = BinaryNatLists.encodeNat r ++ BinaryNatLists.encodeNat d ++
        BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail ∧
      r ≤ (BinaryNatLists.encodeNat d ++ BinaryNatLists.encodeNat xs.length ++
        xs.flatMap Fraction.encode ++ tail).length ∧
      d ≤ (BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail).length ∧
      xs.length = r*(d+1) := by
  have nonempty (xs : List Fraction) : ∀ f ∈ xs.map Fraction.encode, f ≠ [] := by
    intro f hf
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hf
    exact RationalCertificateTail.fraction_nonempty x
  constructor
  · intro h
    have hp : RationalRecordPrefix.complete (RationalRecordPrefix.output bits) := by
      by_contra hf
      exact h (output_of_incomplete bits hf)
    obtain ⟨r,d,xs,tail,he,hr,hd⟩ := (RationalRecordPrefix.complete_iff bits).1 hp
    refine ⟨r,d,xs,tail,he,hr,hd,?_⟩
    rw [he,output_encode r d xs tail hd hr] at h
    simpa using (RationalRectangularFields.output_fields_success_iff r d
      (xs.map Fraction.encode) tail (nonempty xs)).1 h
  · rintro ⟨r,d,xs,tail,rfl,hr,hd,hc⟩
    rw [output_encode r d xs tail hd hr]
    exact (RationalRectangularFields.output_fields_success_iff r d
      (xs.map Fraction.encode) tail (nonempty xs)).2 (by simpa using hc)

theorem output_nil_iff (bits : List Bool) : (output bits).2 = [] ↔
    ¬ ∃ (r d : ℕ) (xs : List Fraction) (tail : List Bool),
      bits = BinaryNatLists.encodeNat r ++ BinaryNatLists.encodeNat d ++
        BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail ∧
      r ≤ (BinaryNatLists.encodeNat d ++ BinaryNatLists.encodeNat xs.length ++
        xs.flatMap Fraction.encode ++ tail).length ∧
      d ≤ (BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail).length ∧
      xs.length = r*(d+1) := by
  simpa using not_congr (output_success_iff bits)

theorem output_length_le (bits : List Bool) :
    (outputEncoding.encode (output bits)).length ≤ 8*bits.length+7 := by
  have hp := RationalRecordPrefix.output_length_le bits
  let x := RationalRecordPrefix.output bits
  have hl : x.1.length + x.2.1.length + x.2.2.length ≤ 8*bits.length+7 := by
    simpa [x,RationalRecordPrefix.outputEncoding,PairEncoding.finEncoding,
      RationalFractionPrefix.Machine.outputEncoding,Nat.add_assoc] using hp
  have hr := RationalRectangularFields.output_length_le (x.1.length-1) (x.2.1.length-1) x.2.2
  simp only [outputEncoding,PairEncoding.finEncoding_encode_length,
    RationalTailAssembly.unaryEncoding,RationalRectangularFields.outputEncoding]
  change (List.replicate (output bits).1 ()).length + (output bits).2.length ≤ _
  rw [List.length_replicate]
  change (RationalRectangleAssembly.prepare x).1 +
    (RationalRectangularFields.output (RationalRectangleAssembly.prepare x).2.1
      (RationalRectangleAssembly.prepare x).2.2.1 (RationalRectangleAssembly.prepare x).2.2.2).length ≤ _
  by_cases h : x.1 = [] ∨ x.2.1 = []
  · simp [RationalRectangleAssembly.prepare,h,RationalRectangularFields.output,
      RationalRectangularFields.rows,RationalRectangularFields.ending,RationalRectangularFields.render]
  · simp only [RationalRectangleAssembly.prepare,h,ite_false]
    omega

theorem output_original_append {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (tail : List Bool) (hr : 0 < r) :
    output (RationalWitnessEncoding.encodeInput A y B ++ tail) =
      (d,((RationalCertificateBroadcast.listEncoding RationalCertificateBroadcast.rowEncoding).encode
        (RationalCertificateBroadcast.observations A y)).map RationalRectangularFields.rowCell ++
        .dataEnd :: (RationalWitnessEncoding.encodeRat B ++ tail).map RationalRectangularFields.Cell.tail) := by
  simp only [output,prepared,RationalRecordPrefix.output_original_append A y B tail hr]
  simp only [RationalRectangleAssembly.prepare,countWord,List.append_eq_nil_iff,
    List.replicate_eq_nil_iff,List.cons_ne_nil,and_false,or_self,ite_false,
    List.length_append,List.length_replicate,List.length_singleton,Nat.add_sub_cancel]
  rw [← RationalCountedList.output_encodeRats_append]
  rw [RationalRectangularFields.output_original_data]

theorem output_original {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    output (RationalWitnessEncoding.encodeInput A y B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β)) =
      (d,((RationalCertificateBroadcast.listEncoding RationalCertificateBroadcast.rowEncoding).encode
        (RationalCertificateBroadcast.observations A y)).map RationalRectangularFields.rowCell ++
        .dataEnd :: (RationalRectangularFields.dataSuffix B β).map RationalRectangularFields.Cell.tail) :=
  output_original_append A y B _ hr

/-- Total execution on arbitrary binary words, including all failed parses. -/
noncomputable def outputsInTime (bits : List Bool) :
    Turing.TM2OutputsInTime computableInPolyTime.tm
      (bits.map computableInPolyTime.inputAlphabet.symm)
      (some ((outputEncoding.encode (output bits)).map computableInPolyTime.outputAlphabet.symm))
      (computableInPolyTime.time.eval bits.length) := computableInPolyTime.outputsFun bits

/-- No prepared dimension or payload is supplied: all earlier stages and their
transfers execute within this polynomial in the original combined bit length. -/
noncomputable def originalOutputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    Turing.TM2OutputsInTime computableInPolyTime.tm
      ((RationalWitnessEncoding.encodeInput A y B ++
        RationalWitnessEncoding.encodeRats (List.ofFn β)).map computableInPolyTime.inputAlphabet.symm)
      (some ((outputEncoding.encode
        (d,((RationalCertificateBroadcast.listEncoding RationalCertificateBroadcast.rowEncoding).encode
          (RationalCertificateBroadcast.observations A y)).map RationalRectangularFields.rowCell ++
            .dataEnd :: (RationalRectangularFields.dataSuffix B β).map RationalRectangularFields.Cell.tail)).map
              computableInPolyTime.outputAlphabet.symm))
      (computableInPolyTime.time.eval (totalBits A y B β)) := by
  simpa only [output_original A y B β hr,List.length_append,totalBits] using!
    outputsInTime (RationalWitnessEncoding.encodeInput A y B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β))

#print axioms computableInPolyTime
#print axioms output_success_iff
#print axioms output_nil_iff
#print axioms output_length_le
#print axioms output_original
#print axioms originalOutputsInTime

end PhdThesisLean.RationalRecordData
