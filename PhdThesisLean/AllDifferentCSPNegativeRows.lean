import PhdThesisLean.AllDifferentCSPPrimalEdges

/-!
# Checked negative-row emission from an explicit primal-edge list

An edge is a two-entry counted row. The existing scope-section machine adds
exactly the tag and length needed by a negative residual row: `[2,i,j]`
becomes `[3,1,i,j]` in raw fields. Reuse that finite machine, with decoders that
check pair arity, instead of building another copying/tagging implementation.

The edge list must already be supplied. Polynomial-time construction of that
list from retained scopes is still open. This machine emits the raw negative
row section; complete objective headers, positive rows and framing are later
assembly stages.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open PhdThesisLean.AllDifferentCSP

namespace NegativeRows

/-- Untagged endpoint pairs, each with exactly two entries. -/
def pairRows (edges : List (ℕ × ℕ)) : List (List ℕ) :=
  edges.map fun edge => [edge.1, edge.2]

/-- Reject wrong arity after the shared counted-row decoder has parsed the wire. -/
def parsePair : List ℕ → Option (ℕ × ℕ)
  | [i, j] => some (i, j)
  | _ => none

@[simp]
theorem parsePair_pairRows (edges : List (ℕ × ℕ)) :
    (pairRows edges).mapM parsePair = some edges := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      change List.mapM parsePair ([edge.1, edge.2] :: pairRows edges) = some (edge :: edges)
      simp [parsePair, ih]

def inputEncode (edges : List (ℕ × ℕ)) : List (Option Bool) :=
  DomainFieldSection.rowPayloadEncode (pairRows edges)

def outputEncode (edges : List (ℕ × ℕ)) : List (Option Bool) :=
  ScopeFieldSection.outputEncode (pairRows edges)

def inputDecode (wire : List (Option Bool)) : Option (List (ℕ × ℕ)) := do
  let rows ← DomainFieldSection.rowPayloadDecode wire
  rows.mapM parsePair

def outputDecode (wire : List (Option Bool)) : Option (List (ℕ × ℕ)) := do
  let rows ← ScopeFieldSection.outputDecode wire
  rows.mapM parsePair

@[simp]
theorem inputDecode_encode (edges : List (ℕ × ℕ)) :
    inputDecode (inputEncode edges) = some edges := by
  simp [inputDecode, inputEncode]

@[simp]
theorem outputDecode_encode (edges : List (ℕ × ℕ)) :
    outputDecode (outputEncode edges) = some edges := by
  simp [outputDecode, outputEncode]

/-- Checked source endpoint stream, using the existing raw counted-row codec. -/
def inputFinEncoding : FinEncoding (List (ℕ × ℕ)) where
  Γ := Option Bool
  encode := inputEncode
  decode := inputDecode
  decode_encode := inputDecode_encode
  ΓFin := inferInstance

/-- Checked negative-row section: exact row length, tag and two endpoint fields. -/
def outputFinEncoding : FinEncoding (List (ℕ × ℕ)) where
  Γ := Option Bool
  encode := outputEncode
  decode := outputDecode
  decode_encode := outputDecode_encode
  ΓFin := inferInstance

/-- The serialized data are precisely the compiler's negative residual rows. -/
def rows (edges : List (ℕ × ℕ)) : List RuntimeResidualRow :=
  edges.map fun edge => .unequal edge.1 edge.2

theorem outputEncode_eq_rows (edges : List (ℕ × ℕ)) :
    outputEncode edges = DomainFieldSection.rowPayloadEncode
      ((rows edges).map RuntimeResidualRow.toNatList) := by
  rw [outputEncode, ScopeFieldSection.outputEncode_eq_taggedRowPayload]
  simp [pairRows, rows, List.map_map, Function.comp_def, RuntimeResidualRow.toNatList]

/-- Exact residual-row order, retaining the semantic compiler's signs and tags. -/
theorem rows_enumerate_eq (C : RuntimeSystem) :
    rows (PrimalEdgeEnumeration.ofRuntimeSystem C) =
      C.toExplicitSystem.unequalRows.map RuntimeResidualRow.ofResidualRow := by
  rw [PrimalEdgeEnumeration.ofRuntimeSystem,
    PrimalEdgeEnumeration.enumerate_eq_sorted_primalEdges]
  simp [rows, ExplicitSystem.unequalRows, List.map_map, Function.comp_def,
    PrimalEdgeEnumeration.eraseEdge, RuntimeResidualRow.ofResidualRow]

theorem outputEncode_enumerate_eq (C : RuntimeSystem) :
    outputEncode (PrimalEdgeEnumeration.ofRuntimeSystem C) =
      DomainFieldSection.rowPayloadEncode
        ((C.toExplicitSystem.unequalRows.map RuntimeResidualRow.ofResidualRow).map
          RuntimeResidualRow.toNatList) := by
  rw [outputEncode_eq_rows, rows_enumerate_eq]

/-- Counting emitted edges gives exactly the weight used by positive pinning rows. -/
theorem pinningWeight_eq_edgeCount (C : RuntimeSystem) :
    C.toExplicitSystem.pinningWeight =
      (PrimalEdgeEnumeration.ofRuntimeSystem C).length + 1 := by
  rw [PrimalEdgeEnumeration.ofRuntimeSystem,
    PrimalEdgeEnumeration.enumerate_eq_sorted_primalEdges]
  simp [ExplicitSystem.pinningWeight]

@[simp]
theorem inputEncode_nil : inputEncode [] = [] := rfl

@[simp]
theorem outputEncode_nil : outputEncode [] = [] := rfl

/-- Exact charged cells: every endpoint bit and every count/tag delimiter. -/
theorem inputEncode_cons_length (edge : ℕ × ℕ) (edges : List (ℕ × ℕ)) :
    (inputEncode (edge :: edges)).length =
      5 + (encodeNat edge.1).length + (encodeNat edge.2).length +
        (inputEncode edges).length := by
  have htwo : (encodeNat 2).length = 2 := by
    rw [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size,
      show 2 = 2 ^ 1 by norm_num, Nat.size_pow]
    norm_num
  simp [inputEncode, pairRows, DomainFieldSection.rowPayloadEncode,
    DomainFieldSection.rowFields, SourceOrderRawFields.encode, htwo]
  omega

theorem outputEncode_cons_length (edge : ℕ × ℕ) (edges : List (ℕ × ℕ)) :
    (outputEncode (edge :: edges)).length =
      7 + (encodeNat edge.1).length + (encodeNat edge.2).length +
        (outputEncode edges).length := by
  have hone : (encodeNat 1).length = 1 := by
    rw [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size, Nat.size_one]
  have hthree : (encodeNat 3).length = 2 := by
    rw [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size,
      show 3 = Nat.bit true 1 by norm_num [Nat.bit], Nat.size_bit (by norm_num [Nat.bit]),
      Nat.size_one]
  simp [outputEncode, pairRows, ScopeFieldSection.outputEncode,
    ScopeFieldBlock.outputEncode, SourceOrderRawFields.encode, hthree, hone]
  omega

/-- Two cells per edge are added: the tag delimiter and its single payload bit. -/
theorem outputEncode_length (edges : List (ℕ × ℕ)) :
    (outputEncode edges).length = (inputEncode edges).length + 2 * edges.length := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      rw [inputEncode_cons_length, outputEncode_cons_length, List.length_cons, ih]
      omega

theorem outputEncode_length_le (n : ℕ) (edges : List (ℕ × ℕ))
    (bounded : ∀ edge ∈ edges, edge.1 < n ∧ edge.2 < n) :
    (outputEncode edges).length ≤ edges.length * (2 * n + 7) := by
  induction edges with
  | nil => simp
  | cons edge edges ih =>
      have hb := bounded edge (by simp)
      have hi := (BinaryNatLists.encodeNat_length_le edge.1).trans hb.1.le
      have hj := (BinaryNatLists.encodeNat_length_le edge.2).trans hb.2.le
      have ht := ih (fun e he => bounded e (by simp [he]))
      rw [outputEncode_cons_length, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Actual raw output size, not a count of high-level operations. -/
theorem enumerate_output_length_le_cubic (n : ℕ) (scopes : List (List ℕ)) :
    (outputEncode (PrimalEdgeEnumeration.enumerate n scopes)).length ≤
      9 * (n + 1) ^ 3 := by
  have h := outputEncode_length_le n (PrimalEdgeEnumeration.enumerate n scopes) (by
    rintro ⟨i, j⟩ he
    have hb := (PrimalEdgeEnumeration.mem_enumerate n scopes i j).mp he
    exact ⟨hb.1, hb.2.1⟩)
  have count := Nat.mul_le_mul_right (2 * n + 7)
    (PrimalEdgeEnumeration.enumerate_length_le n scopes)
  exact h.trans (count.trans (by nlinarith))

theorem compiler_output_length_le_cubic (C : RuntimeSystem) :
    (outputEncode (PrimalEdgeEnumeration.ofRuntimeSystem C)).length ≤
      9 * ((RuntimeCompilerInput.encode C).length + 1) ^ 3 := by
  have hn := C.variableCount_le_encodedSize.trans
    (RuntimeCompilerInput.compact_encodedSize_le_encode_length C)
  exact (enumerate_output_length_le_cubic C.domains.length C.scopes).trans
    (Nat.mul_le_mul_left 9 (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 3))

example : outputDecode (ScopeFieldSection.outputEncode [[0, 1, 2]]) = none := by
  simp [outputDecode, parsePair]
example : inputDecode (DomainFieldSection.rowPayloadEncode [[0]]) = none := by
  simp [inputDecode, parsePair]
example : outputDecode (DomainFieldSection.rowPayloadEncode [[0, 0, 1]]) = none := by
  simp [outputDecode, ScopeFieldSection.outputDecode, ScopeFieldSection.untag]
example : rows (PrimalEdgeEnumeration.enumerate 3 [[2, 0, 2], [1, 2]]) =
    [.unequal 0 2, .unequal 1 2] := by decide

end NegativeRows

/-- Reuse the complete scope-tagging machine on checked two-endpoint rows.
Every copy, count update and cleanup is included in its quadratic bit cost. -/
def negativeRows_outputsInTime (edges : List (ℕ × ℕ)) :
    TM2OutputsInTime ScopeSectionMachine.computer
      (NegativeRows.inputEncode edges) (some (NegativeRows.outputEncode edges))
      (20 * ((NegativeRows.inputEncode edges).length + 1) ^ 2) :=
  scopeSection_outputsInTime (NegativeRows.pairRows edges)

/-- Polynomial-time emission from an already enumerated binary edge stream.
This does not yet construct the edges from compiler-input scopes. -/
noncomputable def negativeRowsComputableInPolyTime :
    @TM2ComputableInPolyTime (List (ℕ × ℕ)) (List (ℕ × ℕ))
      NegativeRows.inputFinEncoding NegativeRows.outputFinEncoding id where
  tm := scopeSectionComputableInPolyTime.tm
  inputAlphabet := scopeSectionComputableInPolyTime.inputAlphabet
  outputAlphabet := scopeSectionComputableInPolyTime.outputAlphabet
  time := scopeSectionComputableInPolyTime.time
  outputsFun edges := scopeSectionComputableInPolyTime.outputsFun (NegativeRows.pairRows edges)

#print axioms NegativeRows.outputDecode_encode
#print axioms NegativeRows.rows_enumerate_eq
#print axioms NegativeRows.pinningWeight_eq_edgeCount
#print axioms NegativeRows.outputEncode_length
#print axioms NegativeRows.compiler_output_length_le_cubic
#print axioms negativeRows_outputsInTime
#print axioms negativeRowsComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
