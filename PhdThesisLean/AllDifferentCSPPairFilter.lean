import PhdThesisLean.AllDifferentCSPPairEmit

/-!
# Compute the candidate decision and emit the accepted row

Compose the complete scope/ordering test with conditional emission. No answer
bit or copied query is supplied externally. `AllDifferentCSPPairStepBranches`
composes each checked counter action after this body. Branch selection and
repeated finite dispatch remain open.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PairFilter

def filter (state : PairQueries.Input) : PairQueries.Input :=
  PairEmit.emit (PairTest.evaluate state)

theorem retained_eq (state : PairQueries.Input) :
    (filter state).1 = state.1 ∧ (filter state).2.1 = state.2.1 := ⟨rfl, rfl⟩

/-- Both the decision and the appended row are now computed from the same state. -/
theorem rows_eq (state : PairQueries.Input) :
    (filter state).2.2 =
      if PairTest.accept state then state.2.2 ++ [state.1] else state.2.2 := rfl

theorem mem_rows (state : PairQueries.Input) (edge : ℕ × ℕ) :
    edge ∈ (filter state).2.2 ↔
      edge ∈ state.2.2 ∨ (PairTest.accept state = true ∧ edge = state.1) := by
  rw [rows_eq]
  cases PairTest.accept state <;> simp

/-- The remaining abstract transition changes only the endpoint counters. -/
theorem afterTest_eq (state : PairQueries.Input) :
    PairAdvance.afterTest (PairTest.evaluate state) =
      (PairAdvance.nextPair state.2.1.1.2 state.1, (filter state).2) := rfl

/-- Reached active states keep the same cubic wire bound after emission, before
counter advance. The already proved abstract invariant supplies the row bound. -/
theorem output_length_le_cubic (state : PairQueries.Input) (h : PairAdvance.Invariant state)
    (hi : state.1.1 < state.2.1.1.2) :
    (PairQueries.inputFinEncoding.encode (filter state)).length ≤
      12 * ((BoundedRelabelledSections.finEncoding.encode state.2.1).length + 1) ^ 3 := by
  have hj : state.1.2 < state.2.1.1.2 := by
    rcases h.counters with hc | hc <;> omega
  have next := PairAdvance.afterTest_invariant state h hi
  apply PairTest.state_length_le_cubic (filter state) hi hj
  · exact next.count_le.trans (PairAdvance.position_le_square _ next.counters)
  · intro edge he
    have hs := (PrimalEdgeEnumeration.mem_enumerate _ _ _ _).mp (next.sound edge he)
    exact ⟨hs.1, hs.2.1⟩

/-- Filtering an exhausted canonical state changes nothing, including n=0. -/
theorem exhausted_eq (state : PairQueries.Input) (hi : state.1.1 = state.2.1.1.2)
    (hj : state.1.2 = 0) : filter state = state := by
  have reject : PairTest.accept state = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have less := (PairTest.accept_eq_true state).mp ht |>.1
    omega
  simp [filter, PairEmit.emit, PairTest.evaluate, reject]

theorem mem_rows_iff_primalEdges (C : RuntimeSystem) (i j : Fin C.domains.length)
    (emitted : List (ℕ × ℕ)) (edge : ℕ × ℕ) :
    edge ∈ (filter ((i.val, j.val), BoundedRelabelledSections.ofRuntimeSystem C, emitted)).2.2 ↔
      edge ∈ emitted ∨ ((i, j) ∈ C.toExplicitSystem.primalEdges ∧ edge = (i.val, j.val)) := by
  rw [mem_rows, PairTest.accept_ofRuntimeSystem]

example : (filter ((0, 1), (([], 2), [[0], [1]]), [])).2.2 = [] := by decide
example : (filter ((0, 1), (([], 2), [[], [1, 0, 0], [0, 1]]), [])).2.2 = [(0, 1)] := by decide
example : filter ((0, 0), (([], 0), []), []) = ((0, 0), (([], 0), []), []) := rfl

end PairFilter

/-- Complete filtering and emission from the serialized candidate state, including
query construction, all scope tests, transfers, row framing and cleanup. -/
noncomputable def pairFilterComputableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Input PairQueries.Input
      PairQueries.inputFinEncoding PairQueries.inputFinEncoding PairFilter.filter := by
  exact compositionComputableInPolyTime _ _ _ _ _
    pairTestComputableInPolyTime pairEmitComputableInPolyTime

/-- Every call along the semantic scan has a uniform original-input polynomial
bound. Conditional invocation and repeated finite dispatch remain separate. -/
theorem pairFilter_iterate_steps_le (value : BoundedRelabelledSections.Value) (k : ℕ) :
    (pairFilterComputableInPolyTime.outputsFun (PairAdvance.run value k)).steps ≤
      pairFilterComputableInPolyTime.time.eval
        (12 * ((BoundedRelabelledSections.finEncoding.encode value).length + 1) ^ 3) :=
  (pairFilterComputableInPolyTime.outputsFun _).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
      (PairAdvance.iterate_length_le_cubic value k))

#print axioms PairFilter.retained_eq
#print axioms PairFilter.mem_rows
#print axioms PairFilter.afterTest_eq
#print axioms PairFilter.output_length_le_cubic
#print axioms PairFilter.exhausted_eq
#print axioms PairFilter.mem_rows_iff_primalEdges
#print axioms pairFilterComputableInPolyTime
#print axioms pairFilter_iterate_steps_le

end PhdThesisLean.AllDifferentCSPMachine
