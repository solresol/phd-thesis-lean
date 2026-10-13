import PhdThesisLean.AllDifferentCSPPositiveCandidateQueries

/-!
# Decide a positive candidate while preserving the complete compiler state

Compose the checked query constructor, complete membership loop and generic
pair-left machine. Acceptance is exactly relabelled-domain membership. A
closed-bound state estimate includes accumulated positive rows and their full
binary weights, providing a uniform polynomial call bound for the future
rectangular scan. Repeated selection and emission remain separate.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PositiveCandidateTest

abbrev Output := Bool × PositiveCandidateQueries.Input

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingBoolBool PositiveCandidateQueries.inputFinEncoding

def accept (input : PositiveCandidateQueries.Input) : Bool :=
  PositiveMembership.contains (PositiveCandidateQueries.query input)

def evaluate (input : PositiveCandidateQueries.Input) : Output := (accept input, input)

theorem accept_eq_true (input : PositiveCandidateQueries.Input) :
    accept input = true ↔ input.1 ∈ input.2.1.1.1.1.1 := by
  simp [accept, PositiveMembership.contains, PositiveCandidateQueries.query]

theorem retained_eq (input : PositiveCandidateQueries.Input) : (evaluate input).2 = input := rfl

/-- Exactly one result cell is added to the full original state. -/
theorem output_length (input : PositiveCandidateQueries.Input) :
    (outputFinEncoding.encode (evaluate input)).length =
      (PositiveCandidateQueries.inputFinEncoding.encode input).length + 1 := by
  simp [outputFinEncoding, evaluate, finEncodingBoolBool, encodeBool, Nat.add_comm]

/-- No candidate bounds are needed for exact domain acceptance. -/
theorem accept_ofRuntimeSystem (C : RuntimeSystem) (index : Fin C.domains.length) (rank : ℕ)
    (emitted : List PositiveBlock.Value) :
    accept ((index.val, rank), CountedPositiveSections.ofRuntimeSystem C, emitted) = true ↔
      rank ∈ C.toExplicitSystem.relabeledDomain index := by
  simpa only [PositiveInitialization.finish_initialize] using
    PositiveInitialization.result_ofRuntimeSystem C index rank

/-- Filtering the existing candidate order gives exactly the semantic positive scan. -/
theorem filter_eq_enumerate (sections : CountedPositiveSections.Value)
    (emitted : List PositiveBlock.Value) :
    (PositiveEnumeration.candidates sections.1.1.2 sections.1.1.1.1).filter
      (fun candidate => accept (candidate, sections, emitted)) =
        PositiveEnumeration.enumerate sections.1.1.2 sections.1.1.1.1 :=
  (PositiveMembership.enumerate_eq_filter sections.1.1.2 sections.1.1.1.1).symm

/-- Charge every stored row's two coordinates, common weight and structural cells. -/
theorem rows_length_le (sections : CountedPositiveSections.Value) (rows : List PositiveBlock.Value)
    (bounded : ∀ row ∈ rows, row.1.1 < sections.1.1.2 ∧
      row.1.2 ≤ sections.1.1.1.2 ∧ row.2 = sections.2.2) :
    (PositiveRows.outputEncode rows).length ≤
      rows.length * (sections.1.1.2 + sections.1.1.1.2 + (encodeNat sections.2.2).length + 8) := by
  induction rows with
  | nil => simp [PositiveRows.outputEncode]
  | cons row rows ih =>
      have hb := bounded row (by simp)
      have hi := (BinaryNatLists.encodeNat_length_le row.1.1).trans hb.1.le
      have hr := (BinaryNatLists.encodeNat_length_le row.1.2).trans hb.2.1
      have head : (PositiveBlock.outputEncode row).length ≤
          sections.1.1.2 + sections.1.1.1.2 + (encodeNat sections.2.2).length + 8 := by
        rw [PositiveRows.block_length, hb.2.2]
        omega
      have tail := ih (fun value hv => bounded value (by simp [hv]))
      simp only [PositiveRows.outputEncode, List.flatMap_cons, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul] at *
      omega

/-- Closed coordinate bounds include the terminal state. Even a full grid of
stored rows fits cubically in the immutable section's complete bit length. -/
theorem state_length_le_cubic (sections : CountedPositiveSections.Value) (candidate : ℕ × ℕ)
    (emitted : List PositiveBlock.Value)
    (hi : candidate.1 ≤ sections.1.1.2) (hr : candidate.2 ≤ sections.1.1.1.2)
    (count : emitted.length ≤ sections.1.1.2 * (sections.1.1.1.2 + 1))
    (bounded : ∀ row ∈ emitted, row.1.1 < sections.1.1.2 ∧
      row.1.2 ≤ sections.1.1.1.2 ∧ row.2 = sections.2.2) :
    (PositiveCandidateQueries.inputFinEncoding.encode (candidate, sections, emitted)).length ≤
      16 * ((CountedPositiveSections.finEncoding.encode sections).length + 1) ^ 3 := by
  let s := (CountedPositiveSections.finEncoding.encode sections).length
  have hn : sections.1.1.2 ≤ s := CountedPositiveSections.variableCount_le_encode_length sections
  have hq : sections.1.1.1.2 ≤ s := CountedPositiveSections.count_le_encode_length sections
  have hw : (encodeNat sections.2.2).length ≤ s := by
    simp only [s, CountedPositiveSections.finEncoding, CountedPositiveSections.sectionsFinEncoding,
      CountedPositiveSections.domainsFinEncoding, OccurrenceCount.finEncoding,
      PinningWeight.negativeFinEncoding, LeanNPHardness.PairEncoding.finEncoding_encode_length,
      UnaryBoundEncoding.output_length]
    omega
  have hc : emitted.length ≤ s * (s + 1) :=
    count.trans (CountedPositiveSections.gridSize_le_wire_quadratic sections)
  have he : (PositiveRows.outputEncode emitted).length ≤ s * (s + 1) * (3 * s + 8) :=
    (rows_length_le sections emitted bounded).trans
      (Nat.mul_le_mul hc (by omega))
  have hil := (BinaryNatLists.encodeNat_length_le candidate.1).trans (hi.trans hn)
  have hrl := (BinaryNatLists.encodeNat_length_le candidate.2).trans (hr.trans hq)
  rw [PositiveCandidateQueries.input_length]
  simp only [ScopeExtraction.endpointsFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length, finEncodingNatBool, encodingNatBool]
  change (encodeNat candidate.1).length + (encodeNat candidate.2).length + s +
      (PositiveRows.outputEncode emitted).length ≤ 16 * (s + 1) ^ 3
  nlinarith

example : accept ((0, 1), (((([(0, 2), (1, 1)], 2), 2), []), ([], 1)), []) = false := by decide
example : accept ((0, 1), (((([(0, 1), (0, 1)], 2), 1), [[]]), ([], 1)),
    [((0, 0), 1)]) = true := by decide
example : evaluate ((0, 0), (((([], 0), 0), []), ([], 1)), []) =
    (false, (0, 0), (((([], 0), 0), []), ([], 1)), []) := rfl
example : accept ((7, 1000000), (((([(7, 1000000)], 1), 8), []), ([], 0)), []) = true := by decide
example : accept ((7, 1000000), (((([(1000000, 7)], 1), 8), []), ([], 0)), []) = false := by decide
example : accept ((0, 0), (((([(0, 0)], 1), 1), []), ([], 3)), []) = true := by decide

end PositiveCandidateTest

/-- The full test includes query copying, false initialization, repeated
same-record comparison, pair transfers and cleanup while retaining all state. -/
noncomputable def positiveCandidateTestComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveCandidateQueries.Input PositiveCandidateTest.Output
      PositiveCandidateQueries.inputFinEncoding PositiveCandidateTest.outputFinEncoding
      PositiveCandidateTest.evaluate := by
  let retained := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    PositiveMembership.finEncoding finEncodingBoolBool PositiveCandidateQueries.inputFinEncoding
    PositiveMembership.contains positiveMembershipComputableInPolyTime
  exact compositionComputableInPolyTime _ _ _ _ _ positiveCandidateQueriesComputableInPolyTime retained

/-- A caller may bound the complete state once and reuse this polynomial at every call. -/
theorem positiveCandidateTest_steps_le (input : PositiveCandidateQueries.Input) (bound : ℕ)
    (h : (PositiveCandidateQueries.inputFinEncoding.encode input).length ≤ bound) :
    (positiveCandidateTestComputableInPolyTime.outputsFun input).steps ≤
      positiveCandidateTestComputableInPolyTime.time.eval bound :=
  (positiveCandidateTestComputableInPolyTime.outputsFun input).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _ h)

/-- Uniform original-section cost, including any previously emitted bounded rows. -/
theorem positiveCandidateTest_bounded_steps_le (sections : CountedPositiveSections.Value)
    (candidate : ℕ × ℕ) (emitted : List PositiveBlock.Value)
    (hi : candidate.1 ≤ sections.1.1.2) (hr : candidate.2 ≤ sections.1.1.1.2)
    (count : emitted.length ≤ sections.1.1.2 * (sections.1.1.1.2 + 1))
    (bounded : ∀ row ∈ emitted, row.1.1 < sections.1.1.2 ∧
      row.1.2 ≤ sections.1.1.1.2 ∧ row.2 = sections.2.2) :
    (positiveCandidateTestComputableInPolyTime.outputsFun (candidate, sections, emitted)).steps ≤
      positiveCandidateTestComputableInPolyTime.time.eval
        (16 * ((CountedPositiveSections.finEncoding.encode sections).length + 1) ^ 3) :=
  positiveCandidateTest_steps_le _ _
    (PositiveCandidateTest.state_length_le_cubic sections candidate emitted hi hr count bounded)

#print axioms PositiveCandidateTest.accept_eq_true
#print axioms PositiveCandidateTest.retained_eq
#print axioms PositiveCandidateTest.output_length
#print axioms PositiveCandidateTest.accept_ofRuntimeSystem
#print axioms PositiveCandidateTest.filter_eq_enumerate
#print axioms PositiveCandidateTest.rows_length_le
#print axioms PositiveCandidateTest.state_length_le_cubic
#print axioms positiveCandidateTestComputableInPolyTime
#print axioms positiveCandidateTest_steps_le
#print axioms positiveCandidateTest_bounded_steps_le

end PhdThesisLean.AllDifferentCSPMachine
