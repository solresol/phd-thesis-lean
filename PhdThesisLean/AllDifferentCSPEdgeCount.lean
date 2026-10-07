import PhdThesisLean.AllDifferentCSPPairFinalization

/-!
# Compute and retain the exact primal-edge count

Reuse the checked row-counting machine on two-endpoint edge rows. The tally
counts the already deduplicated graph, not scope occurrences. It is constructed
inside the composed compiler and charged to the full input wire length.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace EdgeCount

abbrev Value := List (ℕ × ℕ) × ℕ

def finEncoding : FinEncoding Value :=
  LeanNPHardness.PairEncoding.finEncoding NegativeRows.inputFinEncoding unaryFinEncodingNat

def retain (edges : List (ℕ × ℕ)) : Value := (edges, edges.length)

@[simp]
theorem encode_retain (edges : List (ℕ × ℕ)) :
    finEncoding.encode (retain edges) =
      (NegativeRows.inputEncode edges).map Sum.inl ++
        List.replicate edges.length (.inr true) := by
  simp [finEncoding, retain, NegativeRows.inputFinEncoding, unaryFinEncodingNat,
    unaryEncodeNat_eq_replicate_true]

/-- Each edge contributes an explicit counted row, even with zero endpoints. -/
theorem count_le_input_length (edges : List (ℕ × ℕ)) :
    edges.length ≤ (NegativeRows.inputEncode edges).length := by
  simpa [NegativeRows.inputEncode, NegativeRows.pairRows] using
    DomainCountedPayload.variableCount_le_payload_length (NegativeRows.pairRows edges)

theorem encode_retain_length (edges : List (ℕ × ℕ)) :
    (finEncoding.encode (retain edges)).length =
      (NegativeRows.inputEncode edges).length + edges.length := by
  rw [encode_retain]
  simp

/-- Includes both retained endpoints and every unary tally mark. -/
theorem encode_retain_length_le (edges : List (ℕ × ℕ)) :
    (finEncoding.encode (retain edges)).length ≤ 2 * (NegativeRows.inputEncode edges).length := by
  rw [encode_retain_length]
  have h := count_le_input_length edges
  omega

/-- The shared machine retains the exact graph and clears every scratch stack. -/
def outputsInTime (edges : List (ℕ × ℕ)) :
    TM2OutputsInTime StructuralRowCountMachine.computer (NegativeRows.inputEncode edges)
      (some (finEncoding.encode (retain edges)))
      (20 * ((NegativeRows.inputEncode edges).length + 1) ^ 2) := by
  simpa only [DomainCountedPayload.encode_retain, NegativeRows.inputEncode,
    NegativeRows.pairRows, List.length_map, encode_retain] using
    domainVariableCount_outputsInTime (NegativeRows.pairRows edges)

noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime (List (ℕ × ℕ)) Value NegativeRows.inputFinEncoding
      finEncoding retain where
  tm := StructuralRowCountMachine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 20 * (Polynomial.X + 1) ^ 2
  outputsFun edges := by
    simpa [NegativeRows.inputFinEncoding, Equiv.refl, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_natCast,
      Polynomial.eval_one, Polynomial.eval_X] using outputsInTime edges

example : retain [] = ([], 0) := rfl
example : retain [(0, 0), (0, 0), (7, 8)] = ([(0, 0), (0, 0), (7, 8)], 3) := rfl
example : (retain (PrimalEdgeEnumeration.enumerate 3 [[0, 1, 1], [1, 0]])).2 = 1 := by
  decide

end EdgeCount

namespace CountedGraphSections

abbrev Value := BoundedRelabelledSections.Value × EdgeCount.Value

def finEncoding : FinEncoding Value :=
  LeanNPHardness.PairEncoding.finEncoding BoundedRelabelledSections.finEncoding EdgeCount.finEncoding

def retain (value : GraphSections.Value) : Value := (value.1, EdgeCount.retain value.2)

def ofRuntimeSystem (C : RuntimeSystem) : Value := retain (GraphSections.ofRuntimeSystem C)

/-- The graph count is derived from the semantic graph, never a supplied header. -/
theorem count_eq (C : RuntimeSystem) :
    (ofRuntimeSystem C).2.2 + 1 = C.toExplicitSystem.pinningWeight :=
  (NegativeRows.pinningWeight_eq_edgeCount C).symm

/-- Retaining the count costs at most one additional cell per edge. -/
theorem encode_length_le (value : GraphSections.Value) :
    (finEncoding.encode (retain value)).length ≤
      2 * (PairQueries.retainedFinEncoding.encode value).length := by
  have h := EdgeCount.encode_retain_length_le value.2
  simp only [finEncoding, retain, PairQueries.retainedFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length]
  change _ ≤ 2 * (_ + (NegativeRows.inputEncode value.2).length)
  omega

end CountedGraphSections

/-- Count all constructed edges while preserving every ranked source section. -/
noncomputable def runtimeCompilerCountedGraphSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem CountedGraphSections.Value
      RuntimeCompilerInput.finEncoding CountedGraphSections.finEncoding
      CountedGraphSections.ofRuntimeSystem := by
  let count := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    BoundedRelabelledSections.finEncoding NegativeRows.inputFinEncoding
    EdgeCount.finEncoding EdgeCount.retain EdgeCount.computableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerGraphSectionsComputableInPolyTime count
  exact { composed with
    outputsFun := fun C => by simpa only [Function.comp_def, CountedGraphSections.ofRuntimeSystem,
      CountedGraphSections.retain] using composed.outputsFun C }

#print axioms EdgeCount.outputsInTime
#print axioms EdgeCount.computableInPolyTime
#print axioms EdgeCount.encode_retain_length_le
#print axioms CountedGraphSections.count_eq
#print axioms CountedGraphSections.encode_length_le
#print axioms runtimeCompilerCountedGraphSectionsComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
