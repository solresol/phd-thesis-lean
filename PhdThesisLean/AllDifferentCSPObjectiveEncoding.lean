import PhdThesisLean.AllDifferentCSPBinaryHeader

/-!
# Serialize an objective with its exact outer row count

The payload already contains the variable/prime header and every tagged
residual row. Reuse the counted-row machine to construct its outer count,
convert that tally to binary, and frame all fields into the canonical Boolean
encoding. No count or size invariant is supplied by the caller. This pass
is separate from constructing and attaching the variable/prime header.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace ObjectiveEncoding

/-- Full objective rows through exhaustion, without the redundant outer count. -/
def payloadEncode (objective : RuntimeObjective) : List (Option Bool) :=
  DomainFieldSection.rowPayloadEncode objective.toNatLists

def payloadDecode (wire : List (Option Bool)) : Option RuntimeObjective :=
  (DomainFieldSection.rowPayloadDecode wire).bind RuntimeObjective.ofNatLists

@[simp]
theorem payloadDecode_encode (objective : RuntimeObjective) :
    payloadDecode (payloadEncode objective) = some objective := by
  simp [payloadDecode, payloadEncode]

def payloadFinEncoding : FinEncoding RuntimeObjective where
  Γ := Option Bool
  encode := payloadEncode
  decode := payloadDecode
  decode_encode := payloadDecode_encode
  ΓFin := inferInstance

/-- Retain every payload cell alongside a unary tally, checked by the decoder. -/
def countedPairFinEncoding : FinEncoding (RuntimeObjective × ℕ) :=
  LeanNPHardness.PairEncoding.finEncoding payloadFinEncoding unaryFinEncodingNat

def countedDecode (wire : List (Sum (Option Bool) Bool)) : Option RuntimeObjective :=
  (countedPairFinEncoding.decode wire).bind fun value =>
    if value.2 = value.1.rows.length + 1 then some value.1 else none

def countedFinEncoding : FinEncoding RuntimeObjective where
  Γ := Sum (Option Bool) Bool
  encode objective := countedPairFinEncoding.encode (objective, objective.rows.length + 1)
  decode := countedDecode
  decode_encode objective := by
    simp [countedDecode, countedPairFinEncoding.decode_encode]
  ΓFin := inferInstance

@[simp]
theorem counted_encode (objective : RuntimeObjective) :
    countedFinEncoding.encode objective =
      (payloadEncode objective).map Sum.inl ++
        List.replicate (objective.rows.length + 1) (.inr true) := by
  simp [countedFinEncoding, countedPairFinEncoding, payloadFinEncoding,
    unaryFinEncodingNat, unaryEncodeNat_eq_replicate_true]

theorem counted_length (objective : RuntimeObjective) :
    (countedFinEncoding.encode objective).length =
      (payloadEncode objective).length + objective.rows.length + 1 := by
  rw [counted_encode]
  simp [Nat.add_assoc]

theorem rowCount_le_payload_length (objective : RuntimeObjective) :
    objective.rows.length + 1 ≤ (payloadEncode objective).length := by
  simpa [payloadEncode, RuntimeObjective.toNatLists] using
    DomainCountedPayload.variableCount_le_payload_length objective.toNatLists

theorem counted_length_le (objective : RuntimeObjective) :
    (countedFinEncoding.encode objective).length ≤ 2 * (payloadEncode objective).length := by
  rw [counted_length]
  have h := rowCount_le_payload_length objective
  omega

/-- The existing reversed raw-field codec, with objective arity and tags checked. -/
def rawFinEncoding : FinEncoding RuntimeObjective where
  Γ := Option Bool
  encode objective := RawNatLists.encode objective.toNatLists
  decode wire := (RawNatLists.decode wire).bind RuntimeObjective.ofNatLists
  decode_encode objective := by simp
  ΓFin := inferInstance

/-- Exact serialization boundary, including the header row in the outer count. -/
theorem raw_encode (objective : RuntimeObjective) :
    rawFinEncoding.encode objective =
      (SourceOrderRawFields.encode [objective.rows.length + 1] ++ payloadEncode objective).reverse := by
  change RawNatLists.encode objective.toNatLists = _
  apply List.reverse_injective
  simp only [List.reverse_reverse]
  change SourceOrderRawNatLists.encode objective.toNatLists = _
  rw [← DomainFieldSection.inputEncode_eq_sourceOrderRawNatLists]
  simp [DomainFieldSection.inputEncode, DomainFieldSection.inputFields,
    payloadEncode, DomainFieldSection.rowPayloadEncode, SourceOrderRawFields.encode,
    RuntimeObjective.toNatLists]

theorem raw_length_le (objective : RuntimeObjective) :
    (rawFinEncoding.encode objective).length ≤ 2 * (payloadEncode objective).length + 1 := by
  rw [raw_encode]
  simp only [List.length_reverse, List.length_append]
  have h := rowCount_le_payload_length objective
  have hb := BinaryNatLists.encodeNat_length_le (objective.rows.length + 1)
  simp only [SourceOrderRawFields.encode, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.length_cons, List.length_map]
  omega

/-- The shared finite traversal counts the header and each residual row itself. -/
def count_outputsInTime (objective : RuntimeObjective) :
    TM2OutputsInTime StructuralRowCountMachine.computer (payloadEncode objective)
      (some (countedFinEncoding.encode objective))
      (20 * ((payloadEncode objective).length + 1) ^ 2) := by
  simpa only [DomainCountedPayload.encode_retain, RuntimeObjective.toNatLists,
    List.length_cons, List.length_map, counted_encode, payloadEncode] using
      domainVariableCount_outputsInTime objective.toNatLists

noncomputable def countComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeObjective RuntimeObjective
      payloadFinEncoding countedFinEncoding id where
  tm := StructuralRowCountMachine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 20 * (Polynomial.X + 1) ^ 2
  outputsFun objective := by
    simpa [payloadFinEncoding, Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_natCast, Polynomial.eval_one,
      Polynomial.eval_X] using count_outputsInTime objective

/-- Count unary marks by explicit carries, prepend the binary count, and reverse. -/
def header_outputsInTime (objective : RuntimeObjective) :
    TM2OutputsInTime StructuralBinaryHeaderMachine.computer
      (countedFinEncoding.encode objective) (some (rawFinEncoding.encode objective))
      (8 * ((countedFinEncoding.encode objective).length + 1) ^ 2) := by
  rw [counted_length]
  simpa only [counted_encode, raw_encode, Nat.add_assoc] using
    StructuralBinaryHeaderMachine.rawOutputsInTime (payloadEncode objective) (objective.rows.length + 1)

noncomputable def headerComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeObjective RuntimeObjective
      countedFinEncoding rawFinEncoding id where
  tm := StructuralBinaryHeaderMachine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 8 * (Polynomial.X + 1) ^ 2
  outputsFun objective := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using header_outputsInTime objective

/-- Use the dependency's checked linear framing pass, with the exact objective codec. -/
noncomputable def framingComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeObjective RuntimeObjective
      rawFinEncoding RuntimeObjective.finEncoding id where
  tm := listFrameComputer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X
  outputsFun objective := by
    simpa [rawFinEncoding, RuntimeObjective.finEncoding, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_X] using
        nestedListFrame_outputsInTime objective.toNatLists

/-- Full serialization from the objective payload; its outer count is computed internally. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime RuntimeObjective RuntimeObjective
      payloadFinEncoding RuntimeObjective.finEncoding id := by
  let raw := compositionComputableInPolyTime _ _ _ _ _ countComputableInPolyTime headerComputableInPolyTime
  let framed := compositionComputableInPolyTime _ _ _ _ _ raw framingComputableInPolyTime
  exact { framed with
    outputsFun := fun objective => by simpa only [Function.comp_def, id_eq] using framed.outputsFun objective }

example : payloadDecode (DomainFieldSection.rowPayloadEncode [[3]]) = none := by
  simp [payloadDecode, RuntimeObjective.ofNatLists]

example : countedFinEncoding.decode (countedFinEncoding.encode ⟨0, 2, []⟩) =
    some ⟨0, 2, []⟩ := countedFinEncoding.decode_encode _
example : countedDecode (countedPairFinEncoding.encode (⟨0, 2, []⟩, 0)) = none := by
  simp [countedDecode, countedPairFinEncoding.decode_encode]
example : countedDecode (countedPairFinEncoding.encode (⟨3, 7, [.pin 0 1 2, .unequal 0 2]⟩, 3)) =
    some ⟨3, 7, [.pin 0 1 2, .unequal 0 2]⟩ := by
  simp [countedDecode, countedPairFinEncoding.decode_encode]
example : payloadDecode (payloadEncode ⟨0, 1000000, [.pin 0 999999 1000000]⟩) =
    some ⟨0, 1000000, [.pin 0 999999 1000000]⟩ := payloadDecode_encode _

#print axioms payloadFinEncoding
#print axioms countedFinEncoding
#print axioms rawFinEncoding
#print axioms rowCount_le_payload_length
#print axioms counted_length_le
#print axioms raw_encode
#print axioms raw_length_le
#print axioms count_outputsInTime
#print axioms header_outputsInTime
#print axioms framingComputableInPolyTime
#print axioms computableInPolyTime

end ObjectiveEncoding

end PhdThesisLean.AllDifferentCSPMachine
