import PhdThesisLean.RationalTailAssembly

/-!
# Polynomial-time validation of the original threshold/certificate suffix

The threshold and counted certificate enter in their original binary format.
The expected column count is supplied in bounded unary form. The composed
finite machine validates all fractions, checks the certificate count against
that dimension, rejects any trailing symbols, and emits the internal pair of
certificate and threshold. No arithmetic-operation cost premise is used.
-/
namespace PhdThesisLean.RationalCertificateTail

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open LeanNPHardness RationalVerifierBounds
open LeanNPHardness.MachineComposition LeanNPHardness.MachineAdapters
set_option backward.isDefEq.respectTransparency false

def prepared (bits : List Bool) : List Bool × List (Option Bool) :=
  let p := RationalPrefixRouting.splitPrefix bits
  (p.1,RationalCountedList.output p.2)

def output (d : ℕ) (bits : List Bool) : List RationalTailAssembly.Out :=
  RationalTailAssembly.output d (prepared bits).1 (prepared bits).2

def inputEncoding : FinEncoding (ℕ × List Bool) :=
  PairEncoding.finEncoding RationalTailAssembly.unaryEncoding MachinePrimitives.RawBoolList.finEncoding

noncomputable def preparedComputableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding
      (PairEncoding.finEncoding MachinePrimitives.RawBoolList.finEncoding
        RationalFractionPrefix.Machine.outputEncoding) prepared :=
  compositionComputableInPolyTime _ _ _ _ _ RationalPrefixRouting.computableInPolyTime
    (pairRightComputableInPolyTime _ _ _ _ RationalCountedList.computableInPolyTime)

/-- Includes threshold parsing, delimiter routing, counted-list validation,
dimension preservation through both passes, final count/exhaustion checks,
reordering, and every machine transfer. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputEncoding RationalTailAssembly.outputEncoding
      (fun x => output x.1 x.2) :=
  compositionComputableInPolyTime _ _ _ _ _
    (pairRightComputableInPolyTime _ _ _ _ preparedComputableInPolyTime)
    RationalTailAssembly.computableInPolyTime

theorem fraction_nonempty (x : Fraction) : x.encode ≠ [] := by
  simp [Fraction.encode, SmithEncoding.encodeInt]

def result (xs : List Fraction) (B : Fraction) : List RationalTailAssembly.Out :=
  (RationalCountedFields.wire (xs.map Fraction.encode)).map Sum.inl ++ B.encode.map Sum.inr

theorem result_ne_nil (xs : List Fraction) (B : Fraction) : result xs B ≠ [] := by
  simp [result, fraction_nonempty]

/-- Unreduced fields are retained literally; extra trailing bits reject. -/
theorem output_encode_append (d : ℕ) (B : Fraction) (xs : List Fraction) (tail : List Bool) :
    output d (B.encode ++ BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail) =
      if xs.length = d ∧ tail = [] then result xs B else [] := by
  have hp : RationalFractionPrefix.parse
      (B.encode ++ (BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail)) =
        some (B.encode, BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail) :=
    (RationalFractionPrefix.parse_iff _ _ _).2 ⟨B,rfl,rfl⟩
  have hf : ∀ f ∈ xs.map Fraction.encode, f ≠ [] := by
    intro f hf
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hf
    exact fraction_nonempty x
  simp only [output, prepared]
  rw [show B.encode ++ BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail =
    B.encode ++ (BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail) by simp [List.append_assoc],
    RationalPrefixRouting.prefix_of_parse _ _ _ hp]
  rw [RationalCountedList.output_encode_append]
  change RationalTailAssembly.output d B.encode
    (RationalTailAssembly.wire (xs.map Fraction.encode) ++ none :: tail.map some) = _
  rw [RationalTailAssembly.output_wire d B.encode _ _ hf]
  simp [fraction_nonempty, result, RationalTailAssembly.wire]

theorem output_of_invalid_prefix (d : ℕ) (bits : List Bool)
    (h : RationalFractionPrefix.parse bits = none) : output d bits = [] := by
  simp [output, prepared, RationalPrefixRouting.prefix_of_none _ h, RationalTailAssembly.output]

theorem assembly_empty (d : ℕ) (t : List Bool) : RationalTailAssembly.output d t [] = [] := by
  cases d <;> simp [RationalTailAssembly.output, RationalTailAssembly.fields,
    RationalTailAssembly.field, RationalTailAssembly.finish, RationalTailAssembly.render]

/-- Exact accepted language on every raw suffix: one valid threshold, the
original binary-counted list of exactly d fractions, and complete exhaustion. -/
theorem output_success_iff (d : ℕ) (bits : List Bool) :
    output d bits ≠ [] ↔ ∃ B : Fraction, ∃ xs : List Fraction,
      xs.length = d ∧ bits = B.encode ++ BinaryNatLists.encodeNat xs.length ++
        xs.flatMap Fraction.encode := by
  constructor
  · intro h
    cases hp : RationalFractionPrefix.parse bits with
    | none => exact (h (output_of_invalid_prefix d bits hp)).elim
    | some p =>
        rcases p with ⟨part,rest⟩
        obtain ⟨B,rfl,he⟩ := (RationalFractionPrefix.parse_iff _ _ _).1 hp
        have hc : RationalCountedList.output rest ≠ [] := by
          intro hc
          apply h
          simp [output, prepared, RationalPrefixRouting.prefix_of_parse _ _ _ hp, hc, assembly_empty]
        obtain ⟨xs,tail,hr⟩ := (RationalCountedList.output_success_iff rest).1 hc
        have hb : bits = B.encode ++ BinaryNatLists.encodeNat xs.length ++
            xs.flatMap Fraction.encode ++ tail := by simp [he, hr, List.append_assoc]
        rw [hb, output_encode_append] at h
        by_cases hs : xs.length = d ∧ tail = []
        · exact ⟨B,xs,hs.1,by simpa [hs.2] using hb⟩
        · simp [hs] at h
  · rintro ⟨B,xs,rfl,rfl⟩
    simpa using (show output xs.length
      (B.encode ++ BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ []) ≠ [] by
        rw [output_encode_append]; simp [result_ne_nil])

theorem output_nil_iff (d : ℕ) (bits : List Bool) :
    output d bits = [] ↔ ¬ ∃ B : Fraction, ∃ xs : List Fraction,
      xs.length = d ∧ bits = B.encode ++ BinaryNatLists.encodeNat xs.length ++
        xs.flatMap Fraction.encode := by
  simpa using not_congr (output_success_iff d bits)

theorem output_encode (B : Fraction) (xs : List Fraction) :
    output xs.length (B.encode ++ BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode) =
      result xs B := by
  simpa using output_encode_append xs.length B xs []

theorem result_length (xs : List Fraction) (B : Fraction) :
    (result xs B).length = (xs.flatMap Fraction.encode).length + xs.length + B.encode.length := by
  simp [result, RationalCountedFields.wire_length, ← List.flatMap_def]

/-- Even accepted output is linear in the raw suffix, independently of the
supplied expected dimension. Rejection emits the empty word. -/
theorem output_length_le (d : ℕ) (bits : List Bool) : (output d bits).length ≤ 2*bits.length := by
  by_cases h : output d bits = []
  · simp [h]
  · obtain ⟨B,xs,rfl,rfl⟩ := (output_success_iff d bits).1 h
    rw [output_encode, result_length]
    have hc := RationalCountedList.fields_count_le xs
    simp only [List.length_append]
    omega

/-- The exact pair consumed when the certificate and threshold are attached
to the independently validated observation rows. -/
noncomputable def resultEncoding : FinEncoding (List Fraction × Fraction) :=
  PairEncoding.finEncoding RationalNormList.encoding RationalNorm.fractionEncoding

theorem result_encode (xs : List Fraction) (B : Fraction) :
    result xs B = resultEncoding.encode (xs,B) := by
  simp only [result, resultEncoding, PairEncoding.finEncoding, RationalNormList.encoding,
    RationalNorm.fractionEncoding]
  simp only [RationalCountedFields.wire, RationalSum.fields, List.flatMap_map]
  rfl

theorem output_original {d : ℕ} (B : ℚ) (β : Fin d → ℚ) :
    output d (RationalWitnessEncoding.encodeRat B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β)) =
        resultEncoding.encode (RationalCertificateBroadcast.certificate β, Fraction.ofRat B) := by
  have h := output_encode (Fraction.ofRat B) ((List.ofFn β).map Fraction.ofRat)
  rw [result_encode] at h
  have he : ((List.ofFn β).map Fraction.ofRat).flatMap Fraction.encode =
      (List.ofFn β).flatMap RationalWitnessEncoding.encodeRat := by
    rw [List.flatMap_map]
    rfl
  rw [he] at h
  simpa only [RationalCertificateBroadcast.certificate, RationalWitnessEncoding.encodeRats,
    List.length_map, List.length_ofFn, RationalNorm.ofRat_encode,
    List.map_ofFn, List.append_assoc, Function.comp_def] using h

theorem input_length (d : ℕ) (bits : List Bool) :
    (inputEncoding.encode (d,bits)).length = d+bits.length := by
  simp [inputEncoding, RationalTailAssembly.unaryEncoding,
    MachinePrimitives.RawBoolList.finEncoding]

/-- Total execution in unary expected dimension plus raw binary suffix length.
The dimension must be obtained from the completed bounded-count parser when
the enclosing original record is assembled. -/
noncomputable def outputsInTime (d : ℕ) (bits : List Bool) :
    Turing.TM2OutputsInTime computableInPolyTime.tm
      ((inputEncoding.encode (d,bits)).map computableInPolyTime.inputAlphabet.symm)
      (some ((output d bits).map computableInPolyTime.outputAlphabet.symm))
      (computableInPolyTime.time.eval (d+bits.length)) := by
  simpa only [input_length, RationalTailAssembly.outputEncoding] using!
    computableInPolyTime.outputsFun (d,bits)

theorem original_input_length_le {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) :
    (inputEncoding.encode (d, RationalWitnessEncoding.encodeRat B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β))).length ≤ 2*totalBits A y B β := by
  have hd := RationalWitnessEncoding.count_le_encodeRats (List.ofFn β)
  simp only [List.length_ofFn] at hd
  simp only [input_length, totalBits, RationalWitnessEncoding.encodeInput, List.length_append]
  omega

noncomputable def originalTime : Polynomial ℕ := computableInPolyTime.time.comp (2*Polynomial.X)

/-- The full suffix pipeline, including its parsers and transfers, charged to
original input-plus-certificate bits. Preparing the suffix and expected unary
dimension from the enclosing record is still a separate obligation. -/
noncomputable def originalOutputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) :
    Turing.TM2OutputsInTime computableInPolyTime.tm
      ((inputEncoding.encode (d, RationalWitnessEncoding.encodeRat B ++
        RationalWitnessEncoding.encodeRats (List.ofFn β))).map computableInPolyTime.inputAlphabet.symm)
      (some ((resultEncoding.encode (RationalCertificateBroadcast.certificate β,
        Fraction.ofRat B)).map computableInPolyTime.outputAlphabet.symm))
      (originalTime.eval (totalBits A y B β)) := by
  have h := computableInPolyTime.outputsFun
    (d,RationalWitnessEncoding.encodeRat B ++ RationalWitnessEncoding.encodeRats (List.ofFn β))
  have hb := MachineRuntime.polynomial_eval_mono computableInPolyTime.time
    (original_input_length_le A y B β)
  have ht := MachinePrimitives.evalsToInTimeMono h hb
  simpa [RationalTailAssembly.outputEncoding, output_original, originalTime, Polynomial.eval_comp] using! ht

#print axioms computableInPolyTime
#print axioms output_success_iff
#print axioms output_nil_iff
#print axioms output_original
#print axioms output_length_le
#print axioms outputsInTime
#print axioms originalOutputsInTime

end PhdThesisLean.RationalCertificateTail
