import PhdThesisLean.AllDifferentCSPOccurrenceCount

/-!
# Exact pair-membership queries and extraction of the next occurrence

A positive row is selected only when both fields match the same retained
occurrence. Reuse the checked counted-row extractor to expose one ordered
`[0, index, rank]` record, retaining the query and exact remaining stream.
This constructs the next comparison input with a genuine polynomial bound;
the pair comparison and repeated membership controller remain separate.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding

namespace PositiveMembership

abbrev Input := (ℕ × ℕ) × List (ℕ × ℕ)

def finEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding ScopeExtraction.endpointsFinEncoding
    DomainFieldRow.outputFinEncoding

def contains (input : Input) : Bool := decide (input.1 ∈ input.2)

/-- Coordinate matches must belong to one record, not to separate occurrences. -/
theorem contains_cons (query head : ℕ × ℕ) (tail : List (ℕ × ℕ)) :
    contains (query, head :: tail) =
      ((decide (query.1 = head.1) && decide (query.2 = head.2)) ||
        contains (query, tail)) := by
  simp [contains, Prod.ext_iff]

theorem enumerate_eq_filter (n : ℕ) (occurrences : List (ℕ × ℕ)) :
    PositiveEnumeration.enumerate n occurrences =
      (PositiveEnumeration.candidates n occurrences).filter
        (fun query => contains (query, occurrences)) := by
  rw [PositiveEnumeration.enumerate_eq_filter]
  congr 1
  funext query
  simp [contains]

theorem input_length (input : Input) :
    (finEncoding.encode input).length =
      (encodeNat input.1.1).length + (encodeNat input.1.2).length +
        (DomainFieldRow.outputEncode input.2).length := by
  simp [finEncoding, ScopeExtraction.endpointsFinEncoding, finEncodingNatBool,
    encodingNatBool, DomainFieldRow.outputFinEncoding, Nat.add_assoc]

/-- Both binary query words fit within the two retained unary scan bounds. -/
theorem input_length_le_sections (sections : CountedPositiveSections.Value) (index rank : ℕ)
    (hi : index < sections.1.1.2) (hr : rank ≤ sections.1.1.1.2) :
    (finEncoding.encode ((index, rank), sections.1.1.1.1)).length ≤
      (CountedPositiveSections.finEncoding.encode sections).length := by
  have hi' := (BinaryNatLists.encodeNat_length_le index).trans hi.le
  have hr' := (BinaryNatLists.encodeNat_length_le rank).trans hr
  rw [input_length]
  simp only [CountedPositiveSections.finEncoding, CountedPositiveSections.sectionsFinEncoding,
    CountedPositiveSections.domainsFinEncoding, OccurrenceCount.finEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length,
    DomainFieldRow.outputFinEncoding, unaryFinEncodingNat,
    unaryEncodeNat_eq_replicate_true, List.length_replicate]
  omega

example : contains ((0, 1), [(0, 2), (1, 1)]) = false := by decide
example : contains ((0, 1), [(0, 1), (0, 1)]) = true := by decide
example : contains ((0, 0), []) = false := by decide
example : contains ((0, 0), [(0, 0)]) = true := by decide

end PositiveMembership

namespace PositiveOccurrenceHead

abbrev Input := (ℕ × ℕ) × List (ℕ × ℕ)

def source (input : Input) : List (ℕ × ℕ) := input.1 :: input.2

/-- The source is still the contiguous checked occurrence stream. -/
def inputFinEncoding : FinEncoding Input where
  Γ := Option Bool
  encode input := DomainFieldRow.outputEncode (source input)
  decode cells := do
    let occurrences ← DomainFieldRow.outputDecode cells
    match occurrences with
    | [] => none
    | head :: tail => some (head, tail)
  decode_encode input := by simp [source]
  ΓFin := inferInstance

/-- Expose the ordered payload; retain its zero tag as a checked field. -/
def recordFinEncoding : FinEncoding (ℕ × ℕ) where
  Γ := Option Bool
  encode pair := SourceOrderRawFields.encode [0, pair.1, pair.2]
  decode cells := do
    match ← SourceOrderRawFields.decode cells with
    | [0, index, rank] => some (index, rank)
    | _ => none
  decode_encode pair := by simp
  ΓFin := inferInstance

def outputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding recordFinEncoding DomainFieldRow.outputFinEncoding

def asScope (input : Input) : ScopeHead.Input :=
  ([0, input.1.1, input.1.2], input.2.map fun pair => [0, pair.1, pair.2])

theorem input_encode (input : Input) :
    inputFinEncoding.encode input = ScopeHead.inputFinEncoding.encode (asScope input) := by
  simp only [inputFinEncoding, source, OccurrenceCount.occurrenceWire_eq_rows,
    List.map_cons, ScopeHead.inputFinEncoding, asScope]

theorem output_encode (input : Input) :
    outputFinEncoding.encode input = ScopeExtraction.payloadFinEncoding.encode (asScope input) := by
  simp only [outputFinEncoding, recordFinEncoding, DomainFieldRow.outputFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding, ScopeExtraction.payloadFinEncoding,
    SourceOrderRawFields.finEncoding, DomainFieldSection.rowPayloadFinEncoding, asScope, OccurrenceCount.occurrenceWire_eq_rows]

/-- Removing the row count removes precisely the delimiter and the binary `3`. -/
theorem output_length_balance (input : Input) :
    (outputFinEncoding.encode input).length + 3 =
      (inputFinEncoding.encode input).length := by
  have hzero : encodeNat 0 = [] := by
    change encodeNum (Num.ofNat' 0) = []
    rw [Num.ofNat'_zero]
    rfl
  have hthree : encodeNat 3 = [true, true] := by
    change encodeNum (Num.ofNat' 3) = [true, true]
    rw [show (3 : ℕ) = Nat.bit true 1 by norm_num [Nat.bit], Num.ofNat'_bit,
      Num.ofNat'_one]
    rfl
  simp [inputFinEncoding, outputFinEncoding, recordFinEncoding, source,
    DomainFieldRow.outputFinEncoding, DomainFieldRow.outputEncode,
    DomainOccurrenceFieldBlock.outputEncode, SourceOrderRawFields.encode, hzero, hthree]

/-- Reuse the existing finite extractor and count-removal machine unchanged. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime Input Input inputFinEncoding outputFinEncoding id where
  tm := scopeHeadPayloadComputableInPolyTime.tm
  inputAlphabet := scopeHeadPayloadComputableInPolyTime.inputAlphabet
  outputAlphabet := scopeHeadPayloadComputableInPolyTime.outputAlphabet
  time := scopeHeadPayloadComputableInPolyTime.time
  outputsFun input := by
    simpa only [id_eq, input_encode, output_encode] using
      scopeHeadPayloadComputableInPolyTime.outputsFun (asScope input)

example : recordFinEncoding.decode (SourceOrderRawFields.encode [1, 0, 1]) = none := by simp [recordFinEncoding]
example : recordFinEncoding.decode (SourceOrderRawFields.encode [0, 1]) = none := by simp [recordFinEncoding]

end PositiveOccurrenceHead

namespace PositiveMembershipExtraction

abbrev Input := (ℕ × ℕ) × PositiveOccurrenceHead.Input

def inputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding ScopeExtraction.endpointsFinEncoding
    PositiveOccurrenceHead.inputFinEncoding

def outputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding ScopeExtraction.endpointsFinEncoding
    PositiveOccurrenceHead.outputFinEncoding

def source (input : Input) : PositiveMembership.Input :=
  (input.1, PositiveOccurrenceHead.source input.2)

def remaining (input : Input) : PositiveMembership.Input := (input.1, input.2.2)

theorem input_encode (input : Input) :
    inputFinEncoding.encode input = PositiveMembership.finEncoding.encode (source input) := rfl

theorem output_length_balance (input : Input) :
    (outputFinEncoding.encode input).length + 3 =
      (inputFinEncoding.encode input).length := by
  simp only [inputFinEncoding, outputFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length]
  have h := PositiveOccurrenceHead.output_length_balance input.2
  omega

/-- Every iteration removes both fields of exactly one occurrence and its header. -/
theorem remaining_length_balance (input : Input) :
    (PositiveMembership.finEncoding.encode (remaining input)).length +
        (encodeNat input.2.1.1).length + (encodeNat input.2.1.2).length + 6 =
      (inputFinEncoding.encode input).length := by
  have hzero : encodeNat 0 = [] := by
    change encodeNum (Num.ofNat' 0) = []
    rw [Num.ofNat'_zero]
    rfl
  have hthree : encodeNat 3 = [true, true] := by
    change encodeNum (Num.ofNat' 3) = [true, true]
    rw [show (3 : ℕ) = Nat.bit true 1 by norm_num [Nat.bit], Num.ofNat'_bit,
      Num.ofNat'_one]
    rfl
  rw [input_encode, PositiveMembership.input_length, PositiveMembership.input_length]
  simp [source, remaining, PositiveOccurrenceHead.source, DomainFieldRow.outputEncode,
    DomainOccurrenceFieldBlock.outputEncode, SourceOrderRawFields.encode, hzero, hthree]
  omega

theorem remaining_length_lt (input : Input) :
    (PositiveMembership.finEncoding.encode (remaining input)).length <
      (inputFinEncoding.encode input).length := by
  have h := remaining_length_balance input
  omega

theorem contains_step (input : Input) :
    PositiveMembership.contains (source input) =
      ((decide (input.1.1 = input.2.1.1) && decide (input.1.2 = input.2.1.2)) ||
        PositiveMembership.contains (remaining input)) :=
  PositiveMembership.contains_cons _ _ _

end PositiveMembershipExtraction

/-- Retain both candidate fields while extracting the next exact ordered occurrence. -/
noncomputable def positiveMembershipExtractionComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveMembershipExtraction.Input PositiveMembershipExtraction.Input
      PositiveMembershipExtraction.inputFinEncoding PositiveMembershipExtraction.outputFinEncoding id :=
  LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    ScopeExtraction.endpointsFinEncoding PositiveOccurrenceHead.inputFinEncoding
    PositiveOccurrenceHead.outputFinEncoding id PositiveOccurrenceHead.computableInPolyTime

#print axioms PositiveMembership.contains_cons
#print axioms PositiveMembership.enumerate_eq_filter
#print axioms PositiveMembership.input_length_le_sections
#print axioms PositiveOccurrenceHead.inputFinEncoding
#print axioms PositiveOccurrenceHead.recordFinEncoding
#print axioms PositiveOccurrenceHead.output_length_balance
#print axioms PositiveOccurrenceHead.computableInPolyTime
#print axioms PositiveMembershipExtraction.remaining_length_balance
#print axioms PositiveMembershipExtraction.remaining_length_lt
#print axioms PositiveMembershipExtraction.contains_step
#print axioms positiveMembershipExtractionComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
