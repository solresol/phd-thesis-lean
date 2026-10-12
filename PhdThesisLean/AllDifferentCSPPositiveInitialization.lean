import PhdThesisLean.AllDifferentCSPPositiveLoop
import PhdThesisLean.AllDifferentCSPScopeInitialization

/-!
# Complete serialized positive-membership decision

Reuse the exact false-bit initializer on the identical query alphabet, then
compose the complete occurrence loop. The input contains only the candidate
pair and original counted occurrences; neither an answer nor split records
are assumed. Every initialization, comparison, dispatch and cleanup cost is
included in the polynomial bound.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PositiveInitialization

def seed (input : PositiveMembership.Input) : PositiveIteration.Output := (false, input)

def asScope (input : PositiveMembership.Input) : ScopeRouting.Remaining :=
  (input.1, input.2.map fun pair => [0, pair.1, pair.2])

theorem input_encode (input : PositiveMembership.Input) :
    PositiveMembership.finEncoding.encode input =
      ScopeExtraction.remainingFinEncoding.encode (asScope input) := by
  simp only [PositiveMembership.finEncoding, DomainFieldRow.outputFinEncoding,
    OccurrenceCount.occurrenceWire_eq_rows, ScopeExtraction.remainingFinEncoding,
    DomainFieldSection.rowPayloadFinEncoding, asScope,
    LeanNPHardness.PairEncoding.finEncoding]

theorem output_encode (input : PositiveMembership.Input) :
    PositiveIteration.outputFinEncoding.encode (seed input) =
      ScopeIteration.outputFinEncoding.encode (ScopeInitialization.seed (asScope input)) := by
  rw [PositiveAccumulator.output_encode]
  rfl

theorem output_length (input : PositiveMembership.Input) :
    (PositiveIteration.outputFinEncoding.encode (seed input)).length =
      (PositiveMembership.finEncoding.encode input).length + 1 := by
  simp [PositiveTest.outputFinEncoding, seed, finEncodingBoolBool, encodeBool]

theorem finish_initialize (input : PositiveMembership.Input) :
    PositiveLoop.result (seed input) = PositiveMembership.contains input :=
  PositiveIteration.finish_false_eq_contains _ _

/-- On the actual compiler intermediate, acceptance is exactly membership in
this variable's canonical relabelled domain. -/
theorem result_ofRuntimeSystem (C : RuntimeSystem) (index : Fin C.domains.length) (rank : ℕ) :
    PositiveLoop.result (seed ((index.val, rank),
      (CountedPositiveSections.ofRuntimeSystem C).1.1.1.1)) = true ↔
        rank ∈ C.toExplicitSystem.relabeledDomain index := by
  rw [finish_initialize]
  change decide ((index.val, rank) ∈ (BoundedRelabelledSections.ofRuntimeSystem C).1.1) = true ↔ _
  rw [decide_eq_true_eq]
  exact PositiveEnumeration.retained_mem C index rank

end PositiveInitialization

/-- Copy the complete query and prepend false, in at most `2s+2` steps. -/
def positiveInitialization_outputsInTime (input : PositiveMembership.Input) :
    TM2OutputsInTime ScopeInitializationMachine.computer
      (PositiveMembership.finEncoding.encode input)
      (some (PositiveIteration.outputFinEncoding.encode (PositiveInitialization.seed input)))
      (2 * (PositiveMembership.finEncoding.encode input).length + 2) := by
  simpa only [PositiveInitialization.input_encode, PositiveInitialization.output_encode] using
    scopeInitialization_outputsInTime (PositiveInitialization.asScope input)

noncomputable def positiveInitializationComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveMembership.Input PositiveIteration.Output
      PositiveMembership.finEncoding PositiveIteration.outputFinEncoding PositiveInitialization.seed where
  tm := scopeInitializationComputableInPolyTime.tm
  inputAlphabet := scopeInitializationComputableInPolyTime.inputAlphabet
  outputAlphabet := scopeInitializationComputableInPolyTime.outputAlphabet
  time := scopeInitializationComputableInPolyTime.time
  outputsFun input := by
    simpa only [PositiveInitialization.input_encode, PositiveInitialization.output_encode] using
      scopeInitializationComputableInPolyTime.outputsFun (PositiveInitialization.asScope input)

/-- Decide exact ordered-pair membership from the full serialized candidate and
occurrence list, including initialization, all repeated calls and final cleanup. -/
noncomputable def positiveMembershipComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveMembership.Input Bool
      PositiveMembership.finEncoding finEncodingBoolBool PositiveMembership.contains := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    positiveInitializationComputableInPolyTime positiveLoopComputableInPolyTime
  exact { composed with
    outputsFun := fun input => by
      simpa only [Function.comp_def, PositiveInitialization.finish_initialize] using
        composed.outputsFun input }

/-- All bounded grid candidates have the same original-section polynomial bound.
Candidate construction and retention for the next grid point remain separate. -/
theorem positiveMembership_steps_le (sections : CountedPositiveSections.Value) (index rank : ℕ)
    (hi : index < sections.1.1.2) (hr : rank ≤ sections.1.1.1.2) :
    (positiveMembershipComputableInPolyTime.outputsFun
      ((index, rank), sections.1.1.1.1)).steps ≤
      positiveMembershipComputableInPolyTime.time.eval
        (CountedPositiveSections.finEncoding.encode sections).length := by
  exact (positiveMembershipComputableInPolyTime.outputsFun
    ((index, rank), sections.1.1.1.1)).steps_le_m.trans
      (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
        (PositiveMembership.input_length_le_sections sections index rank hi hr))

example : PositiveLoop.result (PositiveInitialization.seed ((0, 1), [(0, 2), (1, 1)])) = false := by decide
example : PositiveLoop.result (PositiveInitialization.seed ((0, 1), [(0, 2), (0, 1), (0, 1)])) = true := by decide
example : PositiveLoop.result (PositiveInitialization.seed ((0, 0), [])) = false := rfl
example : PositiveLoop.result (PositiveInitialization.seed ((0, 0), [(0, 0)])) = true := by decide
example : PositiveLoop.result (PositiveInitialization.seed ((7, 1000000), [(1000000, 7)])) = false := by decide
example : PositiveLoop.result (PositiveInitialization.seed ((7, 1000000), [(7, 1000000)])) = true := by decide

#print axioms PositiveInitialization.input_encode
#print axioms PositiveInitialization.output_encode
#print axioms PositiveInitialization.output_length
#print axioms PositiveInitialization.finish_initialize
#print axioms PositiveInitialization.result_ofRuntimeSystem
#print axioms positiveInitialization_outputsInTime
#print axioms positiveInitializationComputableInPolyTime
#print axioms positiveMembershipComputableInPolyTime
#print axioms positiveMembership_steps_le

end PhdThesisLean.AllDifferentCSPMachine
