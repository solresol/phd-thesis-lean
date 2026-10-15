import PhdThesisLean.AllDifferentCSPPositiveAdvance

/-!
# Binary counter actions for the rectangular positive scan

Reuse the checked successor and pair adapters, including every retained field.
A one-stack eraser resets the inner binary word to canonical zero. The two
continuations are polynomial-time finite machines; deciding and repeatedly
dispatching between them is a separate obligation.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool TM2ComputableInPolyTime)
open LeanNPHardness.MachineComposition

namespace PositiveCounters

def resetRank (state : PositiveAdvance.State) : PositiveAdvance.State :=
  ((state.1.1, 0), state.2)

def inner (state : PositiveAdvance.State) : PositiveAdvance.State :=
  ((state.1.1, state.1.2 + 1), state.2)

def incrementIndex (state : PositiveAdvance.State) : PositiveAdvance.State :=
  ((state.1.1 + 1, state.1.2), state.2)

def outer (state : PositiveAdvance.State) : PositiveAdvance.State := incrementIndex (resetRank state)

theorem resetRank_length (state : PositiveAdvance.State) :
    (PositiveCandidateQueries.inputFinEncoding.encode (resetRank state)).length +
      (encodeNat state.1.2).length = (PositiveCandidateQueries.inputFinEncoding.encode state).length := by
  simp [PositiveCandidateQueries.input_length, resetRank, ScopeExtraction.endpointsFinEncoding,
    finEncodingNatBool, encodeNat, encodeNum]
  omega

theorem inner_length_le (state : PositiveAdvance.State) :
    (PositiveCandidateQueries.inputFinEncoding.encode (inner state)).length ≤
      (PositiveCandidateQueries.inputFinEncoding.encode state).length + 1 := by
  have h := LeanNPHardness.MachinePrimitives.binarySuccBits_length_le (encodeNat state.1.2)
  rw [LeanNPHardness.MachinePrimitives.binarySuccBits_encodeNat] at h
  simp only [PositiveCandidateQueries.input_length, inner, ScopeExtraction.endpointsFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length, finEncodingNatBool]
  omega

theorem outer_length_le (state : PositiveAdvance.State) :
    (PositiveCandidateQueries.inputFinEncoding.encode (outer state)).length ≤
      (PositiveCandidateQueries.inputFinEncoding.encode state).length + 1 := by
  have h := LeanNPHardness.MachinePrimitives.binarySuccBits_length_le (encodeNat state.1.1)
  rw [LeanNPHardness.MachinePrimitives.binarySuccBits_encodeNat] at h
  simp only [PositiveCandidateQueries.input_length, outer, incrementIndex, resetRank,
    ScopeExtraction.endpointsFinEncoding, LeanNPHardness.PairEncoding.finEncoding_encode_length,
    finEncodingNatBool]
  have hz : (encodeNat 0).length = 0 := by simp [encodeNat, encodeNum]
  omega

theorem retained_eq (state : PositiveAdvance.State) :
    (inner state).2 = state.2 ∧ (outer state).2 = state.2 := ⟨rfl, rfl⟩

/-- The last rank is included before resetting; the two bounds need not be equal. -/
theorem step_eq (state : PositiveAdvance.State) :
    PositiveAdvance.step state =
      if state.1.2 < state.2.1.1.1.1.2 then inner (PositiveCandidateFilter.filter state)
      else outer (PositiveCandidateFilter.filter state) := by
  unfold PositiveAdvance.step PositiveAdvance.nextPair
  split <;> rfl

/-- The reached-state proof determines exactly which finite continuation is needed. -/
theorem run_succ_eq (sections : CountedPositiveSections.Value) (k : ℕ)
    (active : k < PositiveAdvance.gridSize sections) :
    PositiveAdvance.run sections (k + 1) =
      if (PositiveAdvance.run sections k).1.2 < sections.1.1.1.2 then
        inner (PositiveCandidateFilter.filter (PositiveAdvance.run sections k))
      else outer (PositiveCandidateFilter.filter (PositiveAdvance.run sections k)) := by
  have hi := (PositiveAdvance.run_active_iff sections k).mpr active
  rw [PositiveAdvance.run_succ, PositiveAdvance.advance,
    PositiveAdvance.run_retained, ite_eq_left hi, step_eq, PositiveAdvance.run_retained]

example : inner ((2, 7), (((([], 8), 3), [[]]), ([(0, 2)], 1000000)),
    [((0, 1), 1000000)]) =
    ((2, 8), (((([], 8), 3), [[]]), ([(0, 2)], 1000000)), [((0, 1), 1000000)]) := rfl
example : outer ((7, 2), (((([], 2), 8), [[]]), ([], 0)), [((0, 1), 0)]) =
    ((8, 0), (((([], 2), 8), [[]]), ([], 0)), [((0, 1), 0)]) := rfl

end PositiveCounters

namespace PositiveRankResetMachine

/-- The same stack is input and output: popping the binary word leaves encoded zero. -/
def computer : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstance
  m := fun _ => .pop () (fun _ cell => cell) <|
    .branch Option.isSome (.goto fun _ => ()) (.load (fun _ => none) .halt)

private def cfg (label : Option Unit) (state : Option Bool) (bits : List Bool) : computer.Cfg :=
  ⟨label, state, fun _ => bits⟩

private def run (bits : List Bool) (state : Option Bool) :
    EvalsToInTime computer.step (cfg (some ()) state bits) (some (cfg none none []))
      (bits.length + 1) := by
  induction bits generalizing state with
  | nil =>
    exact { steps := 1
            evals_in_steps := by simp [computer, FinTM2.step, cfg, flip]
            steps_le_m := le_rfl }
  | cons bit bits ih =>
    have head : EvalsToInTime computer.step (cfg (some ()) state (bit :: bits))
        (some (cfg (some ()) (some bit) bits)) 1 := by
      refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_rfl }
      simp [computer, FinTM2.step, cfg, flip]
      funext k
      cases k
      rfl
    have tail := ih (some bit)
    simpa only [List.length_cons, Nat.add_comm 1] using
      EvalsToInTime.trans computer.step 1 (bits.length + 1)
        (cfg (some ()) state (bit :: bits)) (cfg (some ()) (some bit) bits)
        (some (cfg none none [])) head tail

/-- Exact cleanup, including the final empty-stack test; no natural-size assumption. -/
def outputsInTime (n : ℕ) :
    TM2OutputsInTime computer (finEncodingNatBool.encode n)
      (some (finEncodingNatBool.encode 0)) ((encodeNat n).length + 1) := by
  have init : initList computer (encodeNat n) = cfg (some ()) none (encodeNat n) := by
    simp only [initList, computer, cfg]
    congr 1
  have halt : haltList computer [] = cfg none none [] := by
    simp only [haltList, computer, cfg]
    congr 1
  change EvalsToInTime computer.step (initList computer (encodeNat n))
    (some (haltList computer [])) _
  rw [init, halt]
  exact run (encodeNat n) none

noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime ℕ ℕ finEncodingNatBool finEncodingNatBool (fun _ => 0) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun n := by
    simpa [Equiv.refl, finEncodingNatBool, List.map_id] using! outputsInTime n

end PositiveRankResetMachine

/-- Reset only the rank, preserving both bounds, sections, weight and all accumulated rows. -/
noncomputable def positiveRankResetComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveAdvance.State PositiveAdvance.State
      PositiveCandidateQueries.inputFinEncoding PositiveCandidateQueries.inputFinEncoding
      PositiveCounters.resetRank :=
  LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    ScopeExtraction.endpointsFinEncoding ScopeExtraction.endpointsFinEncoding
    PositiveCandidateQueries.retainedFinEncoding _
    (LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
      finEncodingNatBool finEncodingNatBool finEncodingNatBool _
      PositiveRankResetMachine.computableInPolyTime)

noncomputable def positiveInnerCounterComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveAdvance.State PositiveAdvance.State
      PositiveCandidateQueries.inputFinEncoding PositiveCandidateQueries.inputFinEncoding
      PositiveCounters.inner :=
  LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    ScopeExtraction.endpointsFinEncoding ScopeExtraction.endpointsFinEncoding
    PositiveCandidateQueries.retainedFinEncoding _
    (LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
      finEncodingNatBool finEncodingNatBool finEncodingNatBool _ binarySuccComputableInPolyTime)

noncomputable def positiveIndexCounterComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveAdvance.State PositiveAdvance.State
      PositiveCandidateQueries.inputFinEncoding PositiveCandidateQueries.inputFinEncoding
      PositiveCounters.incrementIndex :=
  LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    ScopeExtraction.endpointsFinEncoding ScopeExtraction.endpointsFinEncoding
    PositiveCandidateQueries.retainedFinEncoding _
    (LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
      finEncodingNatBool finEncodingNatBool finEncodingNatBool _ binarySuccComputableInPolyTime)

noncomputable def positiveOuterCounterComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveAdvance.State PositiveAdvance.State
      PositiveCandidateQueries.inputFinEncoding PositiveCandidateQueries.inputFinEncoding
      PositiveCounters.outer :=
  compositionComputableInPolyTime _ _ _ _ _
    positiveRankResetComputableInPolyTime positiveIndexCounterComputableInPolyTime

/-- Full membership, conditional emission and the inner counter, including all transfers. -/
noncomputable def positiveInnerStepComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveAdvance.State PositiveAdvance.State
      PositiveCandidateQueries.inputFinEncoding PositiveCandidateQueries.inputFinEncoding
      (fun state => PositiveCounters.inner (PositiveCandidateFilter.filter state)) :=
  compositionComputableInPolyTime _ _ _ _ _
    positiveCandidateFilterComputableInPolyTime positiveInnerCounterComputableInPolyTime

/-- Full membership, conditional emission and the outer counter, including all transfers. -/
noncomputable def positiveOuterStepComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveAdvance.State PositiveAdvance.State
      PositiveCandidateQueries.inputFinEncoding PositiveCandidateQueries.inputFinEncoding
      (fun state => PositiveCounters.outer (PositiveCandidateFilter.filter state)) :=
  compositionComputableInPolyTime PositiveCandidateQueries.inputFinEncoding
    PositiveCandidateQueries.inputFinEncoding PositiveCandidateQueries.inputFinEncoding
    PositiveCandidateFilter.filter PositiveCounters.outer
    positiveCandidateFilterComputableInPolyTime positiveOuterCounterComputableInPolyTime

/-- Each complete branch has one polynomial bound throughout the original scan. -/
theorem positiveInnerStep_run_steps_le (sections : CountedPositiveSections.Value) (k : ℕ) :
    (positiveInnerStepComputableInPolyTime.outputsFun (PositiveAdvance.run sections k)).steps ≤
      positiveInnerStepComputableInPolyTime.time.eval
        (16 * ((CountedPositiveSections.finEncoding.encode sections).length + 1) ^ 3) :=
  (positiveInnerStepComputableInPolyTime.outputsFun _).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
      (PositiveAdvance.run_length_le_cubic sections k))

theorem positiveOuterStep_run_steps_le (sections : CountedPositiveSections.Value) (k : ℕ) :
    (positiveOuterStepComputableInPolyTime.outputsFun (PositiveAdvance.run sections k)).steps ≤
      positiveOuterStepComputableInPolyTime.time.eval
        (16 * ((CountedPositiveSections.finEncoding.encode sections).length + 1) ^ 3) :=
  (positiveOuterStepComputableInPolyTime.outputsFun _).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
      (PositiveAdvance.run_length_le_cubic sections k))

#print axioms PositiveCounters.run_succ_eq
#print axioms positiveInnerStep_run_steps_le
#print axioms positiveOuterStep_run_steps_le
#print axioms PositiveCounters.resetRank_length
#print axioms PositiveCounters.inner_length_le
#print axioms PositiveCounters.outer_length_le
#print axioms PositiveCounters.step_eq
#print axioms PositiveRankResetMachine.outputsInTime
#print axioms PositiveRankResetMachine.computableInPolyTime
#print axioms positiveRankResetComputableInPolyTime
#print axioms positiveInnerCounterComputableInPolyTime
#print axioms positiveOuterCounterComputableInPolyTime
#print axioms positiveInnerStepComputableInPolyTime
#print axioms positiveOuterStepComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
