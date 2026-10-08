import PhdThesisLean.AllDifferentCSPPositiveBlock
import PhdThesisLean.AllDifferentCSPPositiveEnumeration
import PhdThesisLean.AllDifferentCSPPinningWeight

/-!
# Checked raw positive-row section and exact compiler correspondence

The positive section concatenates the local machine's complete row blocks.
Its decoder checks every row length and tag. The executable construction from
weighted ranked sections has exactly the semantic compiler's row order and a
quadratic output-wire bound. Only the local block emitter has a machine runtime
theorem here; repeated selection, weight copying and emission still need a
complete finite-machine implementation.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding

namespace PositiveRows

def row (value : PositiveBlock.Value) : RuntimeResidualRow :=
  .pin value.1.1 value.1.2 value.2

def outputEncode (values : List PositiveBlock.Value) : List (Option Bool) :=
  values.flatMap PositiveBlock.outputEncode

/-- Reject negative rows and every wrong arity after the counted-row parser. -/
def parseRow : List ℕ → Option PositiveBlock.Value
  | [0, index, target, weight] => some ((index, target), weight)
  | _ => none

def outputDecode (wire : List (Option Bool)) : Option (List PositiveBlock.Value) := do
  let rows ← DomainFieldSection.rowPayloadDecode wire
  rows.mapM parseRow

theorem outputEncode_eq_rows (values : List PositiveBlock.Value) :
    outputEncode values = DomainFieldSection.rowPayloadEncode
      ((values.map row).map RuntimeResidualRow.toNatList) := by
  simp [outputEncode, row, RuntimeResidualRow.toNatList,
    DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
    SourceOrderRawFields.encode, List.map_map, List.flatMap_assoc,
    List.flatMap_map, Function.comp_def]
  apply List.flatMap_congr
  intro value _
  simp [PositiveBlock.outputEncode, SourceOrderRawFields.encode]

@[simp]
theorem parseRows (values : List PositiveBlock.Value) :
    ((values.map row).map RuntimeResidualRow.toNatList).mapM parseRow = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.map_cons, List.mapM_cons, row, RuntimeResidualRow.toNatList, parseRow, ih]
    rfl

@[simp]
theorem outputDecode_encode (values : List PositiveBlock.Value) :
    outputDecode (outputEncode values) = some values := by
  rw [outputEncode_eq_rows]
  simp only [outputDecode, DomainFieldSection.rowPayloadDecode_encode]
  exact parseRows values

def outputFinEncoding : FinEncoding (List PositiveBlock.Value) where
  Γ := Option Bool
  encode := outputEncode
  decode := outputDecode
  decode_encode := outputDecode_encode
  ΓFin := inferInstance

def ofWeightedSections (value : WeightedGraphSections.Value) : List PositiveBlock.Value :=
  (PositiveEnumeration.enumerate value.1.1.2 value.1.1.1).map fun pair => (pair, value.2.2)

/-- Exact row order, multiplicity and computed weight, with no caller invariant. -/
theorem rows_ofRuntimeSystem (C : RuntimeSystem) :
    (ofWeightedSections (WeightedGraphSections.ofRuntimeSystem C)).map row =
      C.toExplicitSystem.pinningRows.map RuntimeResidualRow.ofResidualRow := by
  simpa [ofWeightedSections, List.map_map, row, PositiveEnumeration.rows,
    WeightedGraphSections.ofRuntimeSystem, PinningWeight.retain] using
      PositiveEnumeration.rows_eq_pinningRows C

theorem outputEncode_ofRuntimeSystem (C : RuntimeSystem) :
    outputEncode (ofWeightedSections (WeightedGraphSections.ofRuntimeSystem C)) =
      DomainFieldSection.rowPayloadEncode
        ((C.toExplicitSystem.pinningRows.map RuntimeResidualRow.ofResidualRow).map
          RuntimeResidualRow.toNatList) := by
  rw [outputEncode_eq_rows, rows_ofRuntimeSystem]

/-- All three arbitrary binary fields and eight fixed tag/delimiter cells. -/
theorem block_length (value : PositiveBlock.Value) :
    (PositiveBlock.outputEncode value).length =
      8 + (encodeNat value.1.1).length + (encodeNat value.1.2).length +
        (encodeNat value.2).length := by
  rw [PositiveBlock.outputEncode_length]
  simp [PositiveBlock.inputEncode, SourceOrderRawFields.encode]
  omega

theorem outputEncode_length_le (n : ℕ) (occurrences : List (ℕ × ℕ)) (weight : ℕ) :
    (outputEncode ((PositiveEnumeration.enumerate n occurrences).map
      fun pair => (pair, weight))).length ≤
      occurrences.length * (n + occurrences.length + (encodeNat weight).length + 8) := by
  have perRow (pair : ℕ × ℕ) (h : pair ∈ PositiveEnumeration.enumerate n occurrences) :
      (PositiveBlock.outputEncode (pair, weight)).length ≤
        n + occurrences.length + (encodeNat weight).length + 8 := by
    have hb := (PositiveEnumeration.mem_enumerate n occurrences pair.1 pair.2).mp h
    have hi := (BinaryNatLists.encodeNat_length_le pair.1).trans hb.1.le
    have ha := (BinaryNatLists.encodeNat_length_le pair.2).trans hb.2.1
    rw [block_length]
    dsimp only
    omega
  have total : ∀ pairs : List (ℕ × ℕ),
      (∀ pair ∈ pairs, (PositiveBlock.outputEncode (pair, weight)).length ≤
        n + occurrences.length + (encodeNat weight).length + 8) →
      (outputEncode (pairs.map fun pair => (pair, weight))).length ≤
        pairs.length * (n + occurrences.length + (encodeNat weight).length + 8) := by
    intro pairs
    induction pairs with
    | nil => simp [outputEncode]
    | cons pair pairs ih =>
      intro bounded
      have hh := bounded pair (by simp)
      have ht := ih (fun p hp => bounded p (by simp [hp]))
      simp only [List.map_cons, outputEncode, List.flatMap_cons, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul] at *
      omega
  exact (total _ perRow).trans (Nat.mul_le_mul_right _
    (PositiveEnumeration.enumerate_length_le n occurrences))

/-- A quadratic bound in the complete weighted-section input wire, including
the actual binary weight field. It is an output-size bound, not a runtime. -/
theorem outputEncode_length_le_wire_quadratic (value : WeightedGraphSections.Value) :
    (outputEncode (ofWeightedSections value)).length ≤
      11 * ((WeightedGraphSections.finEncoding.encode value).length + 1) ^ 2 := by
  have hs : (WeightedGraphSections.finEncoding.encode value).length =
      (BoundedRelabelledSections.finEncoding.encode value.1).length +
        (NegativeRows.outputEncode value.2.1).length + (encodeNat value.2.2).length + 1 := by
    simp [WeightedGraphSections.finEncoding, PinningWeight.negativeFinEncoding,
      NegativeRows.outputFinEncoding, UnaryBoundEncoding.output_length, Nat.add_assoc]
  have hn := BoundedRelabelledSections.variableCount_le_encode_length value.1
  have ho := PositiveEnumeration.occurrenceCount_le_wire value.1.1.1
  have hb := BoundedRelabelledSections.encode_length value.1
  have hocc : value.1.1.1.length ≤ (WeightedGraphSections.finEncoding.encode value).length := by
    omega
  have hn' : value.1.1.2 ≤ (WeightedGraphSections.finEncoding.encode value).length := by omega
  have hw : (encodeNat value.2.2).length ≤
      (WeightedGraphSections.finEncoding.encode value).length := by omega
  apply (outputEncode_length_le value.1.1.2 value.1.1.1 value.2.2).trans
  have bound := Nat.mul_le_mul hocc (Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add hn' hocc) hw) 8)
  exact bound.trans (by nlinarith)

example : outputDecode (DomainFieldSection.rowPayloadEncode [[1, 0, 1]]) = none := by
  simp [outputDecode, parseRow]
example : outputDecode (DomainFieldSection.rowPayloadEncode [[0, 1, 2]]) = none := by
  simp [outputDecode, parseRow]
example : outputDecode (outputEncode [((0, 1), 4), ((2, 3), 4)]) =
    some [((0, 1), 4), ((2, 3), 4)] := outputDecode_encode _
example : outputEncode [] = [] := rfl
example : ofWeightedSections (WeightedGraphSections.ofRuntimeSystem ⟨[[], []], [[]]⟩) = [] := by
  decide
example : ofWeightedSections (WeightedGraphSections.ofRuntimeSystem
    ⟨[[100, 7, 100], [], [42, 7]], [[0, 2], [2, 0, 2]]⟩) =
    [((0, 1), 2), ((0, 3), 2), ((2, 1), 2), ((2, 2), 2)] := by decide

#print axioms outputDecode_encode
#print axioms rows_ofRuntimeSystem
#print axioms outputEncode_ofRuntimeSystem
#print axioms outputEncode_length_le_wire_quadratic

end PositiveRows

end PhdThesisLean.AllDifferentCSPMachine
