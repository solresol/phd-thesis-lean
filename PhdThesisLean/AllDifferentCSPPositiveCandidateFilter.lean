import PhdThesisLean.AllDifferentCSPPositiveCandidateEmit

/-!
# Test a positive candidate and conditionally append its exact pinning row

The complete serialized membership decision and retaining emitter compose into
one polynomial-time call. The semantic contract identifies its decision with
relabelled-domain membership; bounded coordinates, a shared weight and row
capacity suffice to preserve the encoded-state bound for the future scan.
Counter advance and repeated finite control are separate obligations.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PositiveCandidateFilter

def filter (input : PositiveCandidateQueries.Input) : PositiveCandidateQueries.Input :=
  PositiveCandidateEmit.emit (PositiveCandidateTest.evaluate input)

theorem retained_eq (input : PositiveCandidateQueries.Input) :
    (filter input).1 = input.1 ∧ (filter input).2.1 = input.2.1 := ⟨rfl, rfl⟩

/-- Occurrence multiplicity affects neither the decision nor the number appended. -/
theorem rows_eq (input : PositiveCandidateQueries.Input) :
    (filter input).2.2 =
      if input.1 ∈ input.2.1.1.1.1.1 then
        input.2.2 ++ [PositiveCandidateEmit.row input] else input.2.2 := by
  simp [filter, PositiveCandidateEmit.emit, PositiveCandidateTest.evaluate,
    PositiveCandidateTest.accept_eq_true]

theorem rows_length (input : PositiveCandidateQueries.Input) :
    (filter input).2.2.length = input.2.2.length +
      if input.1 ∈ input.2.1.1.1.1.1 then 1 else 0 := by
  rw [rows_eq]
  split <;> simp

theorem rows_length_le (input : PositiveCandidateQueries.Input) :
    (filter input).2.2.length ≤ input.2.2.length + 1 := by
  rw [rows_length]
  split <;> omega

/-- For actual compiler sections, exactly the values in this variable's
canonical domain emit a row, using the retained graph-derived weight. -/
theorem rows_ofRuntimeSystem (C : RuntimeSystem) (index : Fin C.domains.length)
    (rank : ℕ) (emitted : List PositiveBlock.Value) :
    (filter ((index.val, rank), CountedPositiveSections.ofRuntimeSystem C, emitted)).2.2 =
      if rank ∈ C.toExplicitSystem.relabeledDomain index then
        emitted ++ [((index.val, rank), (CountedPositiveSections.ofRuntimeSystem C).2.2)]
      else emitted := by
  simp only [filter, PositiveCandidateEmit.emit, PositiveCandidateTest.evaluate,
    PositiveCandidateEmit.row, PositiveCandidateTest.accept_ofRuntimeSystem]

/-- A bounded candidate preserves the coordinate and common-weight invariant. -/
theorem rows_bounded (sections : CountedPositiveSections.Value) (candidate : ℕ × ℕ)
    (emitted : List PositiveBlock.Value)
    (hi : candidate.1 < sections.1.1.2) (hr : candidate.2 ≤ sections.1.1.1.2)
    (bounded : ∀ row ∈ emitted, row.1.1 < sections.1.1.2 ∧
      row.1.2 ≤ sections.1.1.1.2 ∧ row.2 = sections.2.2) :
    ∀ row ∈ (filter (candidate, sections, emitted)).2.2,
      row.1.1 < sections.1.1.2 ∧ row.1.2 ≤ sections.1.1.1.2 ∧ row.2 = sections.2.2 := by
  rw [rows_eq]
  split
  · intro row h
    rcases List.mem_append.mp h with old | new
    · exact bounded row old
    · simp only [List.mem_singleton] at new
      subst row
      exact ⟨hi, hr, rfl⟩
  · exact bounded

/-- If one grid slot remains, accepting this candidate cannot overflow capacity. -/
theorem rows_capacity (sections : CountedPositiveSections.Value) (candidate : ℕ × ℕ)
    (emitted : List PositiveBlock.Value)
    (capacity : emitted.length < sections.1.1.2 * (sections.1.1.1.2 + 1)) :
    (filter (candidate, sections, emitted)).2.2.length ≤
      sections.1.1.2 * (sections.1.1.1.2 + 1) := by
  have h := rows_length_le (candidate, sections, emitted)
  exact h.trans (Nat.succ_le_of_lt capacity)

/-- The future scan supplies freshness by visiting each candidate once. -/
theorem rows_nodup (input : PositiveCandidateQueries.Input) (old : input.2.2.Nodup)
    (fresh : PositiveCandidateEmit.row input ∉ input.2.2) : (filter input).2.2.Nodup := by
  rw [rows_eq]
  split
  · apply List.nodup_append.mpr
    refine ⟨old, by simp, ?_⟩
    intro value hv other ho equal
    have ho' : other = PositiveCandidateEmit.row input := List.mem_singleton.mp ho
    apply fresh
    simpa only [equal, ho'] using hv
  · exact old

/-- After emission the same cubic bit bound still applies, before counter advance. -/
theorem state_length_le_cubic (sections : CountedPositiveSections.Value) (candidate : ℕ × ℕ)
    (emitted : List PositiveBlock.Value)
    (hi : candidate.1 < sections.1.1.2) (hr : candidate.2 ≤ sections.1.1.1.2)
    (capacity : emitted.length < sections.1.1.2 * (sections.1.1.1.2 + 1))
    (bounded : ∀ row ∈ emitted, row.1.1 < sections.1.1.2 ∧
      row.1.2 ≤ sections.1.1.1.2 ∧ row.2 = sections.2.2) :
    (PositiveCandidateQueries.inputFinEncoding.encode (filter (candidate, sections, emitted))).length ≤
      16 * ((CountedPositiveSections.finEncoding.encode sections).length + 1) ^ 3 := by
  exact PositiveCandidateTest.state_length_le_cubic sections candidate _ hi.le hr
    (rows_capacity sections candidate emitted capacity)
    (rows_bounded sections candidate emitted hi hr bounded)

example : (filter ((0, 1), (((([(0, 1), (0, 1)], 2), 1), [[]]), ([], 3)), [])).2.2 =
    [((0, 1), 3)] := by decide
example : (filter ((0, 1), (((([(0, 2), (1, 1)], 2), 2), []), ([], 3)),
    [((0, 0), 3)])).2.2 = [((0, 0), 3)] := by decide
example : (filter ((0, 0), (((([(0, 0)], 1), 1), []), ([], 0)), [])).2.2 =
    [((0, 0), 0)] := by decide
example : (filter ((7, 1000000), (((([(7, 1000000)], 1), 8), []), ([], 1000000)),
    [])).2.2 = [((7, 1000000), 1000000)] := by decide

end PositiveCandidateFilter

/-- One complete test-and-emit call, including both machines and their transfer. -/
noncomputable def positiveCandidateFilterComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveCandidateQueries.Input PositiveCandidateQueries.Input
      PositiveCandidateQueries.inputFinEncoding PositiveCandidateQueries.inputFinEncoding
      PositiveCandidateFilter.filter :=
  compositionComputableInPolyTime _ _ _ _ _
    positiveCandidateTestComputableInPolyTime positiveCandidateEmitComputableInPolyTime

/-- One polynomial in the immutable section size covers all bounded calls,
including the complete membership decision, copied weight and accumulated rows. -/
theorem positiveCandidateFilter_bounded_steps_le (sections : CountedPositiveSections.Value)
    (candidate : ℕ × ℕ) (emitted : List PositiveBlock.Value)
    (hi : candidate.1 ≤ sections.1.1.2) (hr : candidate.2 ≤ sections.1.1.1.2)
    (count : emitted.length ≤ sections.1.1.2 * (sections.1.1.1.2 + 1))
    (bounded : ∀ row ∈ emitted, row.1.1 < sections.1.1.2 ∧
      row.1.2 ≤ sections.1.1.1.2 ∧ row.2 = sections.2.2) :
    (positiveCandidateFilterComputableInPolyTime.outputsFun (candidate, sections, emitted)).steps ≤
      positiveCandidateFilterComputableInPolyTime.time.eval
        (16 * ((CountedPositiveSections.finEncoding.encode sections).length + 1) ^ 3) :=
  (positiveCandidateFilterComputableInPolyTime.outputsFun _).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
      (PositiveCandidateTest.state_length_le_cubic sections candidate emitted hi hr count bounded))

#print axioms PositiveCandidateFilter.retained_eq
#print axioms PositiveCandidateFilter.rows_eq
#print axioms PositiveCandidateFilter.rows_length
#print axioms PositiveCandidateFilter.rows_ofRuntimeSystem
#print axioms PositiveCandidateFilter.rows_bounded
#print axioms PositiveCandidateFilter.rows_capacity
#print axioms PositiveCandidateFilter.rows_nodup
#print axioms PositiveCandidateFilter.state_length_le_cubic
#print axioms positiveCandidateFilterComputableInPolyTime
#print axioms positiveCandidateFilter_bounded_steps_le

end PhdThesisLean.AllDifferentCSPMachine
