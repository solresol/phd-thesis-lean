import PhdThesisLean.AllDifferentCSPObjectiveRows
import PhdThesisLean.AllDifferentCSPUnaryBridge

/-!
# Compute both objective header fields while retaining the exact residual rows

The occurrence count is copied from the completed scan, prime selection runs
on that count, and both the prime and original variable count are converted to
binary. All three components use checked encodings and finite pair adapters.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open LeanNPHardness (FinEncoding unaryFinEncodingNat TM2ComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open PhdThesisLean.AllDifferentCSP.ExplicitSystem
open LeanNPHardness.MachineComposition

namespace ObjectiveHeader

abbrev Value := ℕ × ObjectiveRows.Value

def rowsFinEncoding : FinEncoding ObjectiveRows.Value :=
  LeanNPHardness.PairEncoding.finEncoding UnaryBoundEncoding.outputFinEncoding ObjectiveRows.finEncoding

def finEncoding : FinEncoding Value :=
  LeanNPHardness.PairEncoding.finEncoding UnaryBoundEncoding.outputFinEncoding rowsFinEncoding

def prepare (input : PositiveCandidateQueries.Input) : Value :=
  (selectPrimeAbove (PositiveBound.bound true input), ObjectiveRows.assemble input)

def ofRuntimeSystem (C : RuntimeSystem) : Value :=
  (C.domainEntryPrime, ObjectiveRows.ofRuntimeSystem C)

theorem prepare_result (C : RuntimeSystem) :
    prepare (PositiveScanLoop.result (CountedPositiveSections.ofRuntimeSystem C)) =
      ofRuntimeSystem C := by
  apply Prod.ext
  · change selectPrimeAbove (CountedPositiveSections.ofRuntimeSystem C).1.1.1.2 = _
    rw [CountedPositiveSections.count_eq]
    rfl
  · exact ObjectiveRows.assemble_result C

/-- Both binary fields include their delimiters; every residual cell is counted. -/
theorem encoded_length (value : Value) :
    (finEncoding.encode value).length =
      (encodeNat value.1).length + 1 + (encodeNat value.2.1).length + 1 +
        (ObjectiveRows.encode value.2.2).length := by
  simp [finEncoding, rowsFinEncoding, ObjectiveRows.finEncoding,
    UnaryBoundEncoding.output_length, Nat.add_assoc]

theorem output_length_le (input : PositiveCandidateQueries.Input) :
    (finEncoding.encode (prepare input)).length ≤
      3 * (PositiveCandidateQueries.inputFinEncoding.encode input).length + 4 := by
  have hq := PositiveBound.bound_le_length true input
  have hr := ObjectiveRowsMachine.output_length_le input
  rw [ObjectiveRows.output_length] at hr
  have hp : selectPrimeAbove (PositiveBound.bound true input) ≤
      2 * PositiveBound.bound true input + 2 := by
    by_cases h : PositiveBound.bound true input = 0
    · simp [h, selectPrimeAbove_zero]
    · exact (selectPrimeAbove_le_two_mul h).trans (by omega)
  have hpbits := BinaryNatLists.encodeNat_length_le (selectPrimeAbove (PositiveBound.bound true input))
  have hnbits := BinaryNatLists.encodeNat_length_le input.2.1.1.1.2
  rw [encoded_length]
  simp only [prepare, ObjectiveRows.assemble]
  have hrows : (ObjectiveRows.encode (input.2.2.map PositiveRows.row ++
        NegativeRows.rows input.2.1.2.1)).length =
      (PositiveRows.outputEncode input.2.2).length +
        (NegativeRows.outputEncode input.2.1.2.1).length := by
    rw [ObjectiveRows.encode_append]
    simp only [ObjectiveRows.encode, ← PositiveRows.outputEncode_eq_rows,
      ← NegativeRows.outputEncode_eq_rows, List.length_append]
  rw [hrows]
  omega

/-- Complete finite prime selection and binary counting, retaining all rows. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime PositiveCandidateQueries.Input Value
      PositiveCandidateQueries.inputFinEncoding finEncoding prepare := by
  let prime := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    UnaryBoundEncoding.inputFinEncoding UnaryBoundEncoding.outputFinEncoding
    PositiveCandidateQueries.inputFinEncoding selectPrimeAbove selectedPrimeBinaryComputableInPolyTime
  let prepared := compositionComputableInPolyTime _ _ _ _ _
    (positiveBoundPrepareComputableInPolyTime true) prime
  let rows := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    UnaryBoundEncoding.outputFinEncoding PositiveCandidateQueries.inputFinEncoding
    ObjectiveRows.countedFinEncoding ObjectiveRows.assemble objectiveRowsComputableInPolyTime
  let collected := compositionComputableInPolyTime _ _ _ _ _ prepared rows
  let variableCounter := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    unaryFinEncodingNat UnaryBoundEncoding.outputFinEncoding ObjectiveRows.finEncoding
    id plainUnaryBinaryComputableInPolyTime
  let header := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    UnaryBoundEncoding.outputFinEncoding ObjectiveRows.countedFinEncoding rowsFinEncoding
    (fun value : ObjectiveRows.Value => (value.1, value.2)) variableCounter
  let complete := compositionComputableInPolyTime _ _ _ _ _ collected header
  exact { complete with
    outputsFun := fun input => by
      simpa only [Function.comp_def, id_eq, prepare, PositiveBound.prepare, finEncoding] using! complete.outputsFun input }

/-- Actual Boolean compiler input to computed binary prime/count and exact rows. -/
noncomputable def runtimeCompilerComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem Value RuntimeCompilerInput.finEncoding
      finEncoding ofRuntimeSystem := by
  let complete := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerPositiveEnumerationComputableInPolyTime computableInPolyTime
  exact { complete with
    outputsFun := fun C => by
      simpa only [Function.comp_def, prepare_result] using complete.outputsFun C }

example : prepare ((0, 0), (((([], 0), 0), []), ([], 1)), []) = (2, 0, []) := rfl
example : prepare ((3, 0), (((([(0, 1), (1, 2), (2, 1)], 3), 3), []), ([(0, 1)], 2)),
    [((0, 1), 2), ((1, 2), 2), ((2, 1), 2)]) =
      (5, 3, [.pin 0 1 2, .pin 1 2 2, .pin 2 1 2, .unequal 0 1]) := rfl

#print axioms prepare_result
#print axioms encoded_length
#print axioms output_length_le
#print axioms computableInPolyTime
#print axioms runtimeCompilerComputableInPolyTime

end ObjectiveHeader

end PhdThesisLean.AllDifferentCSPMachine
