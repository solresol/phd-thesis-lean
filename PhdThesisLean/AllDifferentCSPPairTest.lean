import PhdThesisLean.AllDifferentCSPPairQueries

/-!
# Test a candidate edge while preserving all state for the next pair

Run binary strict comparison and complete same-scope adjacency on the copies
constructed by the routing machine, then conjoin the two answers. The full
scan state survives unchanged. Bounds on candidate endpoints belong to the
future outer dispatcher; this module supplies its exact filtering predicate.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PairTest

abbrev Output := Bool × PairQueries.Input

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingBoolBool PairQueries.inputFinEncoding

def testQueries (queries : PairQueries.Queries) : Bool :=
  DomainSymbolComparison.less queries.1 &&
    PrimalEdgeEnumeration.adjacent queries.2.2 queries.2.1.1 queries.2.1.2

def accept (input : PairQueries.Input) : Bool := testQueries (PairQueries.queries input)

def evaluate (input : PairQueries.Input) : Output := (accept input, input)

/-- Strict orientation rejects self-pairs and reverse copies, even in shared scopes. -/
theorem accept_eq_true (input : PairQueries.Input) :
    accept input = true ↔ input.1.1 < input.1.2 ∧
      ∃ scope ∈ input.2.1.2, input.1.1 ∈ scope ∧ input.1.2 ∈ scope := by
  simp [accept, testQueries, PairQueries.queries, DomainSymbolComparison.less]

/-- Within the unary-bounded grid, this is exactly the established edge filter. -/
theorem accept_iff_mem_enumerate (input : PairQueries.Input)
    (hi : input.1.1 < input.2.1.1.2) (hj : input.1.2 < input.2.1.1.2) :
    accept input = true ↔ input.1 ∈ BoundedRelabelledSections.edges input.2.1 := by
  rw [accept_eq_true, BoundedRelabelledSections.edges,
    PrimalEdgeEnumeration.mem_enumerate]
  simp only [hi, hj, true_and]

theorem retained_eq (input : PairQueries.Input) : (evaluate input).2 = input := rfl

/-- A tested state adds exactly one answer cell; no scope or old edge is consumed. -/
theorem output_length (input : PairQueries.Input) :
    (outputFinEncoding.encode (evaluate input)).length =
      (PairQueries.inputFinEncoding.encode input).length + 1 := by
  simp [outputFinEncoding, evaluate, finEncodingBoolBool, encodeBool, Nat.add_comm]

/-- The filter correspondence reaches the thesis primal graph on compiler-produced sections. -/
theorem accept_ofRuntimeSystem (C : RuntimeSystem) (i j : Fin C.domains.length)
    (emitted : List (ℕ × ℕ)) :
    accept ((i.val, j.val), BoundedRelabelledSections.ofRuntimeSystem C, emitted) = true ↔
      (i, j) ∈ C.toExplicitSystem.primalEdges := by
  rw [accept_iff_mem_enumerate _ i.isLt j.isLt,
    BoundedRelabelledSections.edges_ofRuntimeSystem]
  exact PrimalEdgeEnumeration.mem_enumerate_iff_primalEdges C i j

/-- Closed endpoint bounds also cover the terminal `(n,0)` state. A candidate
and at most a grid's worth of bounded emitted edges fit in a cubic number of
cells in the immutable intermediate's wire length. -/
theorem state_length_le_cubic_of_le (input : PairQueries.Input)
    (hi : input.1.1 ≤ input.2.1.1.2) (hj : input.1.2 ≤ input.2.1.1.2)
    (count : input.2.2.length ≤ input.2.1.1.2 ^ 2)
    (bounded : ∀ edge ∈ input.2.2,
      edge.1 < input.2.1.1.2 ∧ edge.2 < input.2.1.1.2) :
    (PairQueries.inputFinEncoding.encode input).length ≤
      12 * ((BoundedRelabelledSections.finEncoding.encode input.2.1).length + 1) ^ 3 := by
  let s := (BoundedRelabelledSections.finEncoding.encode input.2.1).length
  have hn : input.2.1.1.2 ≤ s := BoundedRelabelledSections.variableCount_le_encode_length _
  have hl := (BinaryNatLists.encodeNat_length_le input.1.1).trans (hi.trans hn)
  have hr := (BinaryNatLists.encodeNat_length_le input.1.2).trans (hj.trans hn)
  have he := NegativeRows.outputEncode_length_le input.2.1.1.2 input.2.2 bounded
  have he' : (NegativeRows.inputEncode input.2.2).length ≤
      s ^ 2 * (2 * s + 7) := by
    rw [NegativeRows.outputEncode_length] at he
    have hc : input.2.2.length ≤ s ^ 2 := count.trans (Nat.pow_le_pow_left hn 2)
    have product := Nat.mul_le_mul hc (show 2 * input.2.1.1.2 + 7 ≤ 2 * s + 7 by omega)
    omega
  rw [PairQueries.input_length]
  simp only [ScopeExtraction.endpointsFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length, finEncodingNatBool, encodingNatBool]
  change (encodeNat input.1.1).length + (encodeNat input.1.2).length + s +
      (NegativeRows.inputEncode input.2.2).length ≤ 12 * (s + 1) ^ 3
  nlinarith

/-- The active-candidate specialization of the closed-bound estimate. -/
theorem state_length_le_cubic (input : PairQueries.Input)
    (hi : input.1.1 < input.2.1.1.2) (hj : input.1.2 < input.2.1.1.2)
    (count : input.2.2.length ≤ input.2.1.1.2 ^ 2)
    (bounded : ∀ edge ∈ input.2.2,
      edge.1 < input.2.1.1.2 ∧ edge.2 < input.2.1.1.2) :
    (PairQueries.inputFinEncoding.encode input).length ≤
      12 * ((BoundedRelabelledSections.finEncoding.encode input.2.1).length + 1) ^ 3 :=
  state_length_le_cubic_of_le input hi.le hj.le count bounded

example : accept ((0, 1), (([], 2), [[0], [1]]), []) = false := by decide
example : accept ((0, 1), (([], 2), [[], [1, 0, 0], [0, 1]]), [(7, 8)]) = true := by decide
example : accept ((1, 0), (([], 2), [[0, 1]]), []) = false := by decide
example : accept ((0, 0), (([], 1), [[0, 0]]), []) = false := by decide
example : accept ((0, 1000000), (([], 1000001), [[1000000, 0]]), []) = true := by decide
example : evaluate ((0, 0), (([], 0), []), []) =
    (false, (0, 0), (([], 0), []), []) := rfl

end PairTest

/-- Both finite predicates and their conjunction, with all paired transfers charged. -/
noncomputable def pairQueryTestComputableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Queries Bool PairQueries.queriesFinEncoding
      finEncodingBoolBool PairTest.testQueries := by
  let comparison := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    DomainSymbolComparison.finEncoding finEncodingBoolBool ScopeExtraction.remainingFinEncoding
    DomainSymbolComparison.less domainSymbolLessComputableInPolyTime
  let adjacency := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    finEncodingBoolBool ScopeExtraction.remainingFinEncoding finEncodingBoolBool
    (fun query => PrimalEdgeEnumeration.adjacent query.2 query.1.1 query.1.2)
    scopeAdjacencyComputableInPolyTime
  let tested := compositionComputableInPolyTime _ _ _ _ _ comparison adjacency
  let composed := compositionComputableInPolyTime _ _ _ _ _ tested
    ScopeConjunctionMachine.computableInPolyTime
  exact composed

/-- Complete candidate filtering from one serialized state. Endpoint/scope copies,
comparison, initialization, all scope tests and scratch cleanup are internal. -/
noncomputable def pairTestComputableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Input PairTest.Output
      PairQueries.inputFinEncoding PairTest.outputFinEncoding PairTest.evaluate := by
  let retained := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    PairQueries.queriesFinEncoding finEncodingBoolBool PairQueries.inputFinEncoding
    PairTest.testQueries pairQueryTestComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _ pairQueriesComputableInPolyTime retained
  exact composed

/-- Uniform bound for complete calls when the outer loop bounds its entire state. -/
theorem pairTest_steps_le (input : PairQueries.Input) (bound : ℕ)
    (h : (PairQueries.inputFinEncoding.encode input).length ≤ bound) :
    (pairTestComputableInPolyTime.outputsFun input).steps ≤
      pairTestComputableInPolyTime.time.eval bound := by
  exact (pairTestComputableInPolyTime.outputsFun input).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _ h)

/-- Complete candidate tests are uniformly polynomial in the original retained
sections, provided the outer grid invariant bounds endpoints and accumulated rows. -/
theorem pairTest_bounded_steps_le (input : PairQueries.Input)
    (hi : input.1.1 < input.2.1.1.2) (hj : input.1.2 < input.2.1.1.2)
    (count : input.2.2.length ≤ input.2.1.1.2 ^ 2)
    (bounded : ∀ edge ∈ input.2.2,
      edge.1 < input.2.1.1.2 ∧ edge.2 < input.2.1.1.2) :
    (pairTestComputableInPolyTime.outputsFun input).steps ≤
      pairTestComputableInPolyTime.time.eval
        (12 * ((BoundedRelabelledSections.finEncoding.encode input.2.1).length + 1) ^ 3) :=
  pairTest_steps_le input _ (PairTest.state_length_le_cubic input hi hj count bounded)

#print axioms PairTest.state_length_le_cubic_of_le
#print axioms PairTest.state_length_le_cubic
#print axioms pairTest_bounded_steps_le
#print axioms PairTest.accept_eq_true
#print axioms PairTest.accept_iff_mem_enumerate
#print axioms PairTest.retained_eq
#print axioms PairTest.output_length
#print axioms PairTest.accept_ofRuntimeSystem
#print axioms pairQueryTestComputableInPolyTime
#print axioms pairTestComputableInPolyTime
#print axioms pairTest_steps_le

end PhdThesisLean.AllDifferentCSPMachine
