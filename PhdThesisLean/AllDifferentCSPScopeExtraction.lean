import PhdThesisLean.AllDifferentCSPScopePayload
import PhdThesisLean.AllDifferentCSPScopeCooccurrence

/-!
# Extract the next scope while retaining both endpoints and the remaining scopes

The input contains a single contiguous nonempty counted scope section. The
checked source parser separates its first row, the existing header-removal
machine exposes the row's entries, and the pinned pair adapters preserve both
binary endpoints and the entire remaining section. This is preparation for
the repeated same-scope predicate, not yet that outer traversal.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace ScopeExtraction

abbrev Input := (ℕ × ℕ) × ScopeHead.Input

def endpointsFinEncoding : FinEncoding (ℕ × ℕ) :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingNatBool finEncodingNatBool

def payloadFinEncoding : FinEncoding ScopeHead.Input :=
  LeanNPHardness.PairEncoding.finEncoding SourceOrderRawFields.finEncoding
    ScopeFieldSection.rowPayloadFinEncoding

def inputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding endpointsFinEncoding ScopeHead.inputFinEncoding

def outputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding endpointsFinEncoding payloadFinEncoding

/-- Query supplied to the checked one-scope predicate after extraction. -/
def query (input : Input) : ScopeQueries.Input := (input.1, input.2.1)

/-- The exact state to retain for subsequent scopes. -/
def remaining (input : Input) : (ℕ × ℕ) × List (List ℕ) := (input.1, input.2.2)

def remainingFinEncoding : FinEncoding ((ℕ × ℕ) × List (List ℕ)) :=
  LeanNPHardness.PairEncoding.finEncoding endpointsFinEncoding
    ScopeFieldSection.rowPayloadFinEncoding

/-- Every cell removed is part of the first scope's count field. -/
theorem output_length_balance (input : Input) :
    (outputFinEncoding.encode input).length + (encodeNat input.2.1.length).length + 1 =
      (inputFinEncoding.encode input).length := by
  have hhead := ScopeHead.output_length input.2
  have hcount := ScopePayload.input_length input.2.1
  simp only [inputFinEncoding, outputFinEncoding, payloadFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length]
  simp only [ScopeHead.outputFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length] at hhead
  simp only [SourceOrderRawFields.finEncoding]
  omega

theorem output_length_lt (input : Input) :
    (outputFinEncoding.encode input).length < (inputFinEncoding.encode input).length := by
  have h := output_length_balance input
  omega

/-- Even empty scopes consume a delimiter, so repeated extraction progresses. -/
theorem remaining_length_lt (input : Input) :
    (remainingFinEncoding.encode (remaining input)).length <
      (inputFinEncoding.encode input).length := by
  have h := ScopeHead.tail_length_lt input.2
  simpa [remainingFinEncoding, remaining, inputFinEncoding] using
    Nat.add_lt_add_left h (endpointsFinEncoding.encode input.1).length

/-- A complete membership query fits within the original retained state. -/
theorem query_length_le (input : Input) :
    (ScopeQueries.inputFinEncoding.encode (query input)).length ≤
      (inputFinEncoding.encode input).length := by
  have h := output_length_balance input
  simp [outputFinEncoding, payloadFinEncoding, SourceOrderRawFields.finEncoding] at h
  simpa [ScopeQueries.inputFinEncoding, query, endpointsFinEncoding,
    SourceOrderRawFields.finEncoding, Nat.add_assoc] using
    (show (endpointsFinEncoding.encode input.1).length +
        (SourceOrderRawFields.encode input.2.1).length ≤
      (inputFinEncoding.encode input).length by omega)

/-- The extracted query concerns one whole scope; the remaining adjacency
question retains the same endpoints and all other scopes. -/
theorem adjacent_step (input : Input) :
    PrimalEdgeEnumeration.adjacent (input.2.1 :: input.2.2) input.1.1 input.1.2 =
      (ScopeCooccurrence.evaluate (query input) ||
        PrimalEdgeEnumeration.adjacent (remaining input).2
          (remaining input).1.1 (remaining input).1.2) := by
  exact ScopeCooccurrence.adjacent_cons input.2.1 input.2.2 input.1.1 input.1.2

example : query ((0, 0), ([], [[0]])) = ((0, 0), []) := rfl
example : remaining ((0, 0), ([], [[0]])) = ((0, 0), [[0]]) := rfl
example : ScopeCooccurrence.evaluate (query ((2, 7), ([2], [[7]]))) = false := by decide
example : ScopeCooccurrence.evaluate (query ((0, 1000000), ([1000000, 0, 0], []))) = true := by
  decide

end ScopeExtraction

/-- Extract one scope and remove only its length header, preserving the exact
remaining counted rows. All parsing, transfer and cleanup costs compose. -/
noncomputable def scopeHeadPayloadComputableInPolyTime :
    @TM2ComputableInPolyTime ScopeHead.Input ScopeHead.Input
      ScopeHead.inputFinEncoding ScopeExtraction.payloadFinEncoding id := by
  let strip := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    ScopeFieldBlock.inputFinEncoding SourceOrderRawFields.finEncoding
    ScopeFieldSection.rowPayloadFinEncoding id scopePayloadComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _
    scopeHeadComputableInPolyTime strip
  exact composed

/-- A genuine finite-machine polynomial bound for extraction from the complete
serialized endpoint/nonempty-scope state, with both endpoints retained. -/
noncomputable def scopeExtractionComputableInPolyTime :
    @TM2ComputableInPolyTime ScopeExtraction.Input ScopeExtraction.Input
      ScopeExtraction.inputFinEncoding ScopeExtraction.outputFinEncoding id := by
  let lifted := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    ScopeExtraction.endpointsFinEncoding ScopeHead.inputFinEncoding
    ScopeExtraction.payloadFinEncoding id scopeHeadPayloadComputableInPolyTime
  exact lifted

#print axioms ScopeExtraction.output_length_balance
#print axioms ScopeExtraction.remaining_length_lt
#print axioms ScopeExtraction.query_length_le
#print axioms ScopeExtraction.adjacent_step
#print axioms scopeHeadPayloadComputableInPolyTime
#print axioms scopeExtractionComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
