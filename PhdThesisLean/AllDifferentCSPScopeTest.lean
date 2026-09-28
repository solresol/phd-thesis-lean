import PhdThesisLean.AllDifferentCSPScopeRouting

/-!
# Extract and test one scope, preserving both endpoints and the remaining scopes

The input is the original contiguous nonempty counted scope section together
with its two binary endpoints. Extraction, endpoint duplication, query routing,
and both membership calls are all performed by the composed finite machine.
The output is the same-scope result paired with the exact continuation state.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace ScopeTest

abbrev Input := ScopeExtraction.Input
abbrev Output := Bool × ScopeRouting.Remaining

abbrev inputFinEncoding := ScopeExtraction.inputFinEncoding

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingBoolBool
    ScopeExtraction.remainingFinEncoding

def evaluate (input : Input) : Output :=
  (ScopeCooccurrence.evaluate (ScopeExtraction.query input), ScopeExtraction.remaining input)

/-- The result concerns the same first scope, never a union of different scopes. -/
theorem result_eq_true (input : Input) :
    (evaluate input).1 = true ↔ input.1.1 ∈ input.2.1 ∧ input.1.2 ∈ input.2.1 := by
  exact ScopeCooccurrence.evaluate_eq_true (ScopeExtraction.query input)

theorem remaining_eq (input : Input) : (evaluate input).2 = (input.1, input.2.2) := rfl

/-- One result bit replaces the first counted scope, including its length field. -/
theorem output_length_balance (input : Input) :
    (outputFinEncoding.encode (evaluate input)).length +
        (ScopeFieldBlock.inputFinEncoding.encode input.2.1).length =
      (inputFinEncoding.encode input).length + 1 := by
  have h := ScopeHead.output_length input.2
  simp only [ScopeHead.outputFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length] at h
  simp [outputFinEncoding, evaluate, ScopeExtraction.remaining,
    ScopeExtraction.remainingFinEncoding, ScopeExtraction.inputFinEncoding,
    finEncodingBoolBool, encodeBool]
  omega

theorem output_length_le (input : Input) :
    (outputFinEncoding.encode (evaluate input)).length ≤
      (inputFinEncoding.encode input).length := by
  have h := output_length_balance input
  have count := ScopePayload.input_length input.2.1
  omega

theorem adjacent_step (input : Input) :
    PrimalEdgeEnumeration.adjacent (input.2.1 :: input.2.2) input.1.1 input.1.2 =
      ((evaluate input).1 ||
        PrimalEdgeEnumeration.adjacent (evaluate input).2.2
          (evaluate input).2.1.1 (evaluate input).2.1.2) :=
  ScopeExtraction.adjacent_step input

example : evaluate ((0, 1), ([0], [[1]])) = (false, (0, 1), [[1]]) := by decide
example : evaluate ((0, 0), ([], [[0]])) = (false, (0, 0), [[0]]) := by decide
example : evaluate ((0, 1000000), ([1000000, 0, 0], [])) =
    (true, (0, 1000000), []) := by decide

end ScopeTest

/-- Complete one-scope testing from the unsplit counted source. No query,
answer, or duplicated endpoint is supplied externally. -/
noncomputable def scopeTestComputableInPolyTime :
    @TM2ComputableInPolyTime ScopeTest.Input ScopeTest.Output
      ScopeTest.inputFinEncoding ScopeTest.outputFinEncoding ScopeTest.evaluate := by
  let routed := compositionComputableInPolyTime _ _ _ _ _
    scopeExtractionComputableInPolyTime scopeRoutingComputableInPolyTime
  let tested := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    ScopeQueries.inputFinEncoding finEncodingBoolBool ScopeExtraction.remainingFinEncoding
    ScopeCooccurrence.evaluate scopeCooccurrenceComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _ routed tested
  exact composed

#print axioms ScopeTest.result_eq_true
#print axioms ScopeTest.output_length_balance
#print axioms ScopeTest.output_length_le
#print axioms ScopeTest.adjacent_step
#print axioms scopeTestComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
