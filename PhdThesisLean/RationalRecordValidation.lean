import PhdThesisLean.RationalRecordRouting

/-!
# Whole-record rational data and certificate validation

The original binary word enters one composed finite machine. It reads the
dimensions, validates and partitions the data, preserves the rows during suffix
validation, checks the certificate count, and enforces complete exhaustion.
The output retains separate failure components. Combining them into a guarded
internal-checker input and executing the loss comparison is a further step.
-/
namespace PhdThesisLean.RationalRecordValidation

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open LeanNPHardness RationalVerifierBounds
open LeanNPHardness.MachineComposition LeanNPHardness.MachineAdapters
open RationalRectangularFields (Cell)
open RationalRecordRouting (split)
set_option backward.isDefEq.respectTransparency false

abbrev Result := List Cell × List RationalTailAssembly.Out
def outputEncoding : FinEncoding Result :=
  PairEncoding.finEncoding RationalRectangularFields.outputEncoding RationalTailAssembly.outputEncoding
def prepared (bits : List Bool) := RationalRecordRouting.prepare (RationalRecordData.output bits)
def output (bits : List Bool) : Result :=
  let x := prepared bits
  (x.1,RationalCertificateTail.output x.2.1 x.2.2)

noncomputable def preparedComputableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding
      RationalRecordRouting.preparedEncoding prepared :=
  compositionComputableInPolyTime _ _ _ _ _ RationalRecordData.computableInPolyTime
    RationalRecordRouting.computableInPolyTime

/-- All original parsers, row retention, suffix validation and machine transfers
are executed in polynomial time in the length of the original binary word. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding outputEncoding output :=
  compositionComputableInPolyTime _ _ _ _ _ preparedComputableInPolyTime
    (pairRightComputableInPolyTime _ _ _ _ RationalCertificateTail.computableInPolyTime)

/-- Both failure components must be checked before calling the arithmetic machine. -/
def Validated (bits : List Bool) : Prop := (output bits).1 ≠ [] ∧ (output bits).2 ≠ []
instance (bits : List Bool) : Decidable (Validated bits) :=
  inferInstanceAs (Decidable ((output bits).1 ≠ [] ∧ (output bits).2 ≠ []))

theorem output_of_failed_data (bits : List Bool) (h : (RationalRecordData.output bits).2 = []) :
    output bits = ([],[]) := by
  have ht : ∀ d, RationalCertificateTail.output d [] = [] := by
    intro d
    exact RationalCertificateTail.output_of_invalid_prefix d [] rfl
  simp [output,prepared,RationalRecordRouting.prepare,h,split,ht]

theorem prepared_encode (r d : ℕ) (xs : List Fraction) (tail : List Bool)
    (hd : d ≤ (BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail).length)
    (hr : r ≤ (BinaryNatLists.encodeNat d ++ BinaryNatLists.encodeNat xs.length ++
      xs.flatMap Fraction.encode ++ tail).length)
    (hc : xs.length = r*(d+1)) :
    ∃ rs : List RationalRectangularFields.Row,
      prepared (BinaryNatLists.encodeNat r ++ BinaryNatLists.encodeNat d ++
        BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail) =
        (RationalRectangularFields.rowsWire rs ++ [.dataEnd],d,tail) := by
  have hn : ∀ f ∈ xs.map Fraction.encode, f ≠ [] := by
    intro f hf
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hf
    exact RationalCertificateTail.fraction_nonempty x
  obtain ⟨rs,hlen,hv,he⟩ := RationalRectangularFields.exists_rows_of_length r d
    (xs.map Fraction.encode) (by simpa using hc) hn
  have ho := (RationalRectangularFields.rows_success_iff r d
    (RationalCountedFields.wire (xs.map Fraction.encode) ++ none :: tail.map some)
    (RationalRectangularFields.rowsWire rs ++ .dataEnd :: tail.map Cell.tail)).2
      ⟨rs,tail,hlen,hv,by rw [he]; rfl,rfl⟩
  refine ⟨rs,?_⟩
  simp only [prepared,RationalRecordData.output_encode r d xs tail hd hr,
    RationalRecordRouting.prepare,RationalRectangularFields.output,ho,
    RationalRectangularFields.render,List.reverse_nil,List.nil_append]
  rw [RationalRecordRouting.split_rowsWire]

/-- Exact accepted syntax, including original binary headers and final exhaustion.
The stored fractions may be unreduced; signs, values and multiplicities survive. -/
theorem validated_iff (bits : List Bool) : Validated bits ↔
    ∃ (r d : ℕ) (xs : List Fraction) (B : Fraction) (cert : List Fraction),
      let tail := B.encode ++ BinaryNatLists.encodeNat cert.length ++ cert.flatMap Fraction.encode
      bits = BinaryNatLists.encodeNat r ++ BinaryNatLists.encodeNat d ++
        BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail ∧
      r ≤ (BinaryNatLists.encodeNat d ++ BinaryNatLists.encodeNat xs.length ++
        xs.flatMap Fraction.encode ++ tail).length ∧
      d ≤ (BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail).length ∧
      xs.length = r*(d+1) ∧ cert.length = d := by
  constructor
  · intro h
    have hn : (RationalRecordData.output bits).2 ≠ [] := by
      intro hf
      have ho := output_of_failed_data bits hf
      exact h.1 (congrArg Prod.fst ho)
    obtain ⟨r,d,xs,tail,he,hr,hd,hc⟩ := (RationalRecordData.output_success_iff bits).1 hn
    obtain ⟨rs,hp⟩ := prepared_encode r d xs tail hd hr hc
    have ht : RationalCertificateTail.output d tail ≠ [] := by
      simpa only [Validated,output,he,hp] using h.2
    obtain ⟨B,cert,hcert,hb⟩ := (RationalCertificateTail.output_success_iff d tail).1 ht
    exact ⟨r,d,xs,B,cert,by simpa [hb] using he,by simpa [hb] using hr,
      by simpa [hb] using hd,hc,hcert⟩
  · rintro ⟨r,d,xs,B,cert,he,hr,hd,hc,hcert⟩
    obtain ⟨rs,hp⟩ := prepared_encode r d xs _ hd hr hc
    have ht := (RationalCertificateTail.output_success_iff d
      (B.encode ++ BinaryNatLists.encodeNat cert.length ++ cert.flatMap Fraction.encode)).2
        ⟨B,cert,hcert,rfl⟩
    simp only [Validated,output,he,hp]
    exact ⟨by simp,ht⟩

theorem output_length_le (bits : List Bool) :
    (outputEncoding.encode (output bits)).length ≤ 16*bits.length+14 := by
  have hd := RationalRecordData.output_length_le bits
  have hs := RationalRecordRouting.split_length (RationalRecordData.output bits).2
  have ht := RationalCertificateTail.output_length_le (RationalRecordData.output bits).1
    (split (RationalRecordData.output bits).2).2
  simp only [RationalRecordData.outputEncoding,PairEncoding.finEncoding_encode_length,
    RationalTailAssembly.unaryEncoding,RationalRectangularFields.outputEncoding,
    List.length_replicate,id_eq] at hd
  simp only [outputEncoding,PairEncoding.finEncoding_encode_length,
    RationalRectangularFields.outputEncoding,RationalTailAssembly.outputEncoding,
    output,prepared,RationalRecordRouting.prepare,id_eq]
  omega

theorem output_original {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    output (RationalWitnessEncoding.encodeInput A y B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β)) =
      (((RationalCertificateBroadcast.listEncoding RationalCertificateBroadcast.rowEncoding).encode
          (RationalCertificateBroadcast.observations A y)).map RationalRectangularFields.rowCell ++ [.dataEnd],
        RationalCertificateTail.resultEncoding.encode
          (RationalCertificateBroadcast.certificate β,Fraction.ofRat B)) := by
  simp only [output,prepared,RationalRecordRouting.prepare,
    RationalRecordData.output_original A y B β hr,RationalRectangularFields.dataSuffix,
    RationalRecordRouting.split_internalRows,RationalCertificateTail.output_original]

theorem validated_original {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    Validated (RationalWitnessEncoding.encodeInput A y B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β)) := by
  rw [Validated,output_original A y B β hr]
  refine ⟨by simp,?_⟩
  change RationalCertificateTail.resultEncoding.encode _ ≠ []
  rw [← RationalCertificateTail.result_encode]
  exact RationalCertificateTail.result_ne_nil _ _

noncomputable def outputsInTime (bits : List Bool) :
    Turing.TM2OutputsInTime computableInPolyTime.tm
      (bits.map computableInPolyTime.inputAlphabet.symm)
      (some ((outputEncoding.encode (output bits)).map computableInPolyTime.outputAlphabet.symm))
      (computableInPolyTime.time.eval bits.length) := computableInPolyTime.outputsFun bits

/-- Executes the complete validation pipeline from the original combined bits;
no prepared rows, unary dimensions or suffix are supplied by the caller. -/
noncomputable def originalOutputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    Turing.TM2OutputsInTime computableInPolyTime.tm
      ((RationalWitnessEncoding.encodeInput A y B ++
        RationalWitnessEncoding.encodeRats (List.ofFn β)).map computableInPolyTime.inputAlphabet.symm)
      (some ((outputEncoding.encode
        (((RationalCertificateBroadcast.listEncoding RationalCertificateBroadcast.rowEncoding).encode
          (RationalCertificateBroadcast.observations A y)).map RationalRectangularFields.rowCell ++ [.dataEnd],
          RationalCertificateTail.resultEncoding.encode
            (RationalCertificateBroadcast.certificate β,Fraction.ofRat B))).map
              computableInPolyTime.outputAlphabet.symm))
      (computableInPolyTime.time.eval (totalBits A y B β)) := by
  simpa only [output_original A y B β hr,List.length_append,totalBits] using!
    outputsInTime (RationalWitnessEncoding.encodeInput A y B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β))

#print axioms computableInPolyTime
#print axioms validated_iff
#print axioms output_original
#print axioms originalOutputsInTime

end PhdThesisLean.RationalRecordValidation
