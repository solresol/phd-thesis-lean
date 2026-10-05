import PhdThesisLean.AllDifferentCSPPairCounters

/-!
# Complete filtering and counter-update branches

Each branch computes the candidate test, conditionally emits its edge and
updates the counters, with every stage executed by a checked finite machine.
The semantic branch conditions identify their outputs with the established
scan recurrence. `AllDifferentCSPPairControl` computes the selection and
exhaustion predicates. `AllDifferentCSPPairDispatch` supplies checked conditional
invocation; repeating that complete dispatch remains a separate obligation.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PairStepBranches

def inner (state : PairQueries.Input) : PairQueries.Input :=
  PairCounters.inner (PairFilter.filter state)

def outer (state : PairQueries.Input) : PairQueries.Input :=
  PairCounters.outer (PairFilter.filter state)

theorem afterTest_eq (state : PairQueries.Input) :
    PairAdvance.afterTest (PairTest.evaluate state) =
      if state.1.2 + 1 < state.2.1.1.2 then inner state else outer state := by
  rw [PairFilter.afterTest_eq]
  exact PairCounters.nextPair_eq (PairFilter.filter state)

theorem advance_eq_inner (state : PairQueries.Input)
    (hi : state.1.1 < state.2.1.1.2) (hj : state.1.2 + 1 < state.2.1.1.2) :
    PairAdvance.advance state = inner state := by
  simp only [PairAdvance.advance, if_pos hi, afterTest_eq, if_pos hj]

theorem advance_eq_outer (state : PairQueries.Input)
    (hi : state.1.1 < state.2.1.1.2) (hj : ¬ state.1.2 + 1 < state.2.1.1.2) :
    PairAdvance.advance state = outer state := by
  simp only [PairAdvance.advance, if_pos hi, afterTest_eq, if_neg hj]

theorem inner_invariant (state : PairQueries.Input) (h : PairAdvance.Invariant state)
    (hi : state.1.1 < state.2.1.1.2) (hj : state.1.2 + 1 < state.2.1.1.2) :
    PairAdvance.Invariant (inner state) := by
  rw [← advance_eq_inner state hi hj]
  exact PairAdvance.advance_invariant state h

theorem outer_invariant (state : PairQueries.Input) (h : PairAdvance.Invariant state)
    (hi : state.1.1 < state.2.1.1.2) (hj : ¬ state.1.2 + 1 < state.2.1.1.2) :
    PairAdvance.Invariant (outer state) := by
  rw [← advance_eq_outer state hi hj]
  exact PairAdvance.advance_invariant state h

/-- The selected complete branch removes exactly one candidate from the budget. -/
theorem budget (state : PairQueries.Input) (h : PairAdvance.Invariant state)
    (hi : state.1.1 < state.2.1.1.2) :
    PairAdvance.budget
      (if state.1.2 + 1 < state.2.1.1.2 then inner state else outer state) + 1 =
        PairAdvance.budget state := by
  rw [← afterTest_eq]
  simpa only [PairAdvance.advance, if_pos hi] using PairAdvance.advance_budget state h hi

theorem run_succ_eq (value : BoundedRelabelledSections.Value) (k : ℕ)
    (hk : k < value.1.2 ^ 2) :
    PairAdvance.run value (k + 1) =
      if (PairAdvance.run value k).1.2 + 1 < value.1.2 then
        inner (PairAdvance.run value k) else outer (PairAdvance.run value k) := by
  have hi := (PairAdvance.run_active_iff value k).mpr hk
  rw [PairAdvance.run_succ]
  simp only [PairAdvance.advance, PairAdvance.run_retained, if_pos hi,
    afterTest_eq]

/-- The reached-state cubic bound is preserved after the correct complete branch. -/
theorem run_succ_length_le (value : BoundedRelabelledSections.Value) (k : ℕ)
    (hk : k < value.1.2 ^ 2) :
    (PairQueries.inputFinEncoding.encode
      (if (PairAdvance.run value k).1.2 + 1 < value.1.2 then
        inner (PairAdvance.run value k) else outer (PairAdvance.run value k))).length ≤
      12 * ((BoundedRelabelledSections.finEncoding.encode value).length + 1) ^ 3 := by
  rw [← run_succ_eq value k hk]
  exact PairAdvance.iterate_length_le_cubic value (k + 1)

/-- The last active call reaches canonical exhaustion without losing the final row. -/
theorem final_outer (value : BoundedRelabelledSections.Value) (hn : 0 < value.1.2) :
    outer (PairAdvance.run value (value.1.2 ^ 2 - 1)) =
      ((value.1.2, 0), value, BoundedRelabelledSections.edges value) := by
  have hn2 : 0 < value.1.2 ^ 2 := Nat.pow_pos hn
  have hk : value.1.2 ^ 2 - 1 < value.1.2 ^ 2 := by omega
  have hi := (PairAdvance.run_active_iff value _).mpr hk
  have hp := PairAdvance.run_position value (value.1.2 ^ 2 - 1)
  rw [Nat.min_eq_left hk.le] at hp
  have hc := (PairAdvance.run_invariant value (value.1.2 ^ 2 - 1)).counters
  simp only [PairAdvance.Counters, PairAdvance.run_retained] at hc
  have hj : (PairAdvance.run value (value.1.2 ^ 2 - 1)).1.2 + 1 = value.1.2 := by
    simp only [PairAdvance.position, PairAdvance.ordinal, PairAdvance.run_retained] at hp
    have hp' : (PairAdvance.run value (value.1.2 ^ 2 - 1)).1.1 * value.1.2 +
        (PairAdvance.run value (value.1.2 ^ 2 - 1)).1.2 + 1 = value.1.2 ^ 2 := by omega
    have hm := Nat.mul_le_mul_right value.1.2 (Nat.succ_le_of_lt hi)
    rcases hc with hc | hc <;> nlinarith
  have hs := run_succ_eq value (value.1.2 ^ 2 - 1) hk
  rw [hj, if_neg (Nat.lt_irrefl _), Nat.sub_add_cancel hn2] at hs
  rw [← hs]
  exact Prod.ext (PairAdvance.run_exhausted value)
    (Prod.ext (PairAdvance.run_retained value _) (PairAdvance.run_edges_eq value))

example : inner ((0, 1), (([], 3), [[0, 1]]), []) =
    ((0, 2), (([], 3), [[0, 1]]), [(0, 1)]) := by decide
example : outer ((0, 1), (([], 2), [[0, 1], [1, 0, 1]]), []) =
    ((1, 0), (([], 2), [[0, 1], [1, 0, 1]]), [(0, 1)]) := by decide
example : outer ((0, 0), (([], 1), [[0, 0]]), []) =
    ((1, 0), (([], 1), [[0, 0]]), []) := by decide

end PairStepBranches

noncomputable def pairInnerStepComputableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Input PairQueries.Input
      PairQueries.inputFinEncoding PairQueries.inputFinEncoding PairStepBranches.inner :=
  compositionComputableInPolyTime _ _ _ _ _
    pairFilterComputableInPolyTime pairInnerCounterComputableInPolyTime

noncomputable def pairOuterStepComputableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Input PairQueries.Input
      PairQueries.inputFinEncoding PairQueries.inputFinEncoding PairStepBranches.outer :=
  compositionComputableInPolyTime _ _ _ _ _
    pairFilterComputableInPolyTime pairOuterCounterComputableInPolyTime

/-- Complete inner calls along the semantic scan share one original-input bound. -/
theorem pairInnerStep_iterate_steps_le (value : BoundedRelabelledSections.Value) (k : ℕ) :
    (pairInnerStepComputableInPolyTime.outputsFun (PairAdvance.run value k)).steps ≤
      pairInnerStepComputableInPolyTime.time.eval
        (12 * ((BoundedRelabelledSections.finEncoding.encode value).length + 1) ^ 3) :=
  (pairInnerStepComputableInPolyTime.outputsFun _).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
      (PairAdvance.iterate_length_le_cubic value k))

/-- Complete outer calls include resetting, carry, transfers and all filtering. -/
theorem pairOuterStep_iterate_steps_le (value : BoundedRelabelledSections.Value) (k : ℕ) :
    (pairOuterStepComputableInPolyTime.outputsFun (PairAdvance.run value k)).steps ≤
      pairOuterStepComputableInPolyTime.time.eval
        (12 * ((BoundedRelabelledSections.finEncoding.encode value).length + 1) ^ 3) :=
  (pairOuterStepComputableInPolyTime.outputsFun _).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
      (PairAdvance.iterate_length_le_cubic value k))

#print axioms PairStepBranches.afterTest_eq
#print axioms PairStepBranches.inner_invariant
#print axioms PairStepBranches.outer_invariant
#print axioms PairStepBranches.budget
#print axioms PairStepBranches.run_succ_eq
#print axioms PairStepBranches.run_succ_length_le
#print axioms PairStepBranches.final_outer
#print axioms pairInnerStepComputableInPolyTime
#print axioms pairOuterStepComputableInPolyTime
#print axioms pairInnerStep_iterate_steps_le
#print axioms pairOuterStep_iterate_steps_le

end PhdThesisLean.AllDifferentCSPMachine
