import PhdThesisLean.AllDifferentCSPPairFilter

/-!
# Finite counter actions for the candidate-pair scan

Reuse the checked binary successor and pair adapters for endpoint arithmetic.
A finite filtering pass resets the second endpoint to canonical zero while
preserving all other state. Both row-major continuations are thus genuine
polynomial-time machines. `AllDifferentCSPPairDispatch` chooses and invokes
the continuation; repeated dispatch remains a separate obligation.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PairCounters

def resetSecond (state : PairQueries.Input) : PairQueries.Input :=
  ((state.1.1, 0), state.2)

def incrementFirst (state : PairQueries.Input) : PairQueries.Input :=
  ((state.1.1 + 1, state.1.2), state.2)

def inner (state : PairQueries.Input) : PairQueries.Input :=
  ((state.1.1, state.1.2 + 1), state.2)

def outer (state : PairQueries.Input) : PairQueries.Input :=
  incrementFirst (resetSecond state)

theorem resetSecond_length (state : PairQueries.Input) :
    (PairQueries.inputFinEncoding.encode (resetSecond state)).length +
      (encodeNat state.1.2).length = (PairQueries.inputFinEncoding.encode state).length := by
  simp [PairQueries.input_length, resetSecond, ScopeExtraction.endpointsFinEncoding,
    finEncodingNatBool, encodingNatBool, encodeNat, encodeNum]
  omega

theorem inner_length_le (state : PairQueries.Input) :
    (PairQueries.inputFinEncoding.encode (inner state)).length ≤
      (PairQueries.inputFinEncoding.encode state).length + 1 := by
  have h := LeanNPHardness.MachinePrimitives.binarySuccBits_length_le (encodeNat state.1.2)
  rw [LeanNPHardness.MachinePrimitives.binarySuccBits_encodeNat] at h
  simp only [PairQueries.input_length, inner, ScopeExtraction.endpointsFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length, finEncodingNatBool, encodingNatBool]
  omega

theorem outer_length_le (state : PairQueries.Input) :
    (PairQueries.inputFinEncoding.encode (outer state)).length ≤
      (PairQueries.inputFinEncoding.encode state).length + 1 := by
  have h := LeanNPHardness.MachinePrimitives.binarySuccBits_length_le (encodeNat state.1.1)
  rw [LeanNPHardness.MachinePrimitives.binarySuccBits_encodeNat] at h
  simp only [PairQueries.input_length, outer, incrementFirst, resetSecond,
    ScopeExtraction.endpointsFinEncoding, LeanNPHardness.PairEncoding.finEncoding_encode_length,
    finEncodingNatBool, encodingNatBool]
  have hz : (encodeNat 0).length = 0 := by simp [encodeNat, encodeNum]
  omega

/-- Neither continuation changes any immutable section or accumulated edge. -/
theorem retained_eq (state : PairQueries.Input) :
    (inner state).2 = state.2 ∧ (outer state).2 = state.2 := ⟨rfl, rfl⟩

theorem nextPair_eq (state : PairQueries.Input) :
    (PairAdvance.nextPair state.2.1.1.2 state.1, state.2) =
      if state.1.2 + 1 < state.2.1.1.2 then inner state else outer state := by
  unfold PairAdvance.nextPair
  split <;> rfl

example : inner ((7, 7), (([], 9), [[]]), [(0, 1)]) =
    ((7, 8), (([], 9), [[]]), [(0, 1)]) := rfl
example : outer ((7, 8), (([], 9), [[]]), [(0, 1)]) =
    ((8, 0), (([], 9), [[]]), [(0, 1)]) := rfl

end PairCounters

namespace PairCounterResetMachine

abbrev Wire := PairQueriesMachine.Input
abbrev State := Option Wire

inductive Stack
  | input | saved | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | emit
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : Stack) := Wire

def keep : Wire → Bool
  | .inl (.inr _) => false
  | _ => true

private def observe (_ : State) (cell : Option Wire) : State := cell
private def cell (s : State) : Wire := s.getD (.inr (.inr none))

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch Option.isSome
      (.branch (fun s => keep (cell s))
        (.push .saved cell <| .goto fun _ => .scan)
        (.goto fun _ => .scan))
      (.goto fun _ => .emit)
  | .emit => .pop .saved observe <| .branch Option.isSome
      (.push .output cell <| .goto fun _ => .emit)
      (.load (fun _ => none) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := none
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input saved output : List Wire) : (k : Stack) → List (Alphabet k)
  | .input => input | .saved => saved | .output => output

private def cfg (label : Option Label) (state : State) (input saved output : List Wire) :
    computer.Cfg := ⟨label, state, stackContents input saved output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "counter_reset_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe,
    cell, keep, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input saved output : List Wire) (state : State) :
    Run (cfg (some .scan) state input saved output)
      (cfg (some .emit) none [] ((input.filter keep).reverse ++ saved) output)
      (input.length + 1) := by
  induction input generalizing saved state with
  | nil => exact one (by counter_reset_step)
  | cons c input ih =>
      have step : Run (cfg (some .scan) state (c :: input) saved output)
          (cfg (some .scan) (some c) input ((if keep c then [c] else []) ++ saved) output) 1 := by
        apply one
        rcases c with (b | b) | rest <;> counter_reset_step
      have tail := ih ((if keep c then [c] else []) ++ saved) (some c)
      rcases c with (b | b) | rest <;>
        simpa [keep, List.reverse_cons, List.append_assoc, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using seq step tail

private def emit_run (saved output : List Wire) (state : State) :
    Run (cfg (some .emit) state [] saved output)
      (cfg none none [] [] (saved.reverse ++ output)) (saved.length + 1) := by
  induction saved generalizing output state with
  | nil => exact one (by counter_reset_step)
  | cons c saved ih =>
      have step : Run (cfg (some .emit) state [] (c :: saved) output)
          (cfg (some .emit) (some c) [] saved (c :: output)) 1 := one (by counter_reset_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq step (ih (c :: output) (some c))

private def run (input : List Wire) :
    Run (cfg (some .scan) none input [] [])
      (cfg none none [] [] (input.filter keep)) (2 * input.length + 2) := by
  have hs := scan_run input [] [] none
  have he := emit_run (input.filter keep).reverse [] none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hs he
  apply evalsToInTimeMono (seq hs he)
  have h := List.length_filter_le keep input
  omega

private theorem init_eq (input : List Wire) :
    initList computer input = cfg (some .scan) none input [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Wire) :
    haltList computer output = cfg none none [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem reset_encode (input : PairQueries.Input) :
    (PairQueries.inputFinEncoding.encode input).filter keep =
      PairQueries.inputFinEncoding.encode (PairCounters.resetSecond input) := by
  simp [PairQueries.inputFinEncoding, PairCounters.resetSecond,
    ScopeExtraction.endpointsFinEncoding, LeanNPHardness.PairEncoding.finEncoding,
    finEncodingNatBool, encodingNatBool, encodeNat, encodeNum,
    List.filter_map, Function.comp_def, keep]

end PairCounterResetMachine

/-- Reset only the second counter, including all copies and work-stack cleanup. -/
def pairCounterReset_outputsInTime (input : PairQueries.Input) :
    TM2OutputsInTime PairCounterResetMachine.computer (PairQueries.inputFinEncoding.encode input)
      (some (PairQueries.inputFinEncoding.encode (PairCounters.resetSecond input)))
      (2 * (PairQueries.inputFinEncoding.encode input).length + 2) := by
  rw [TM2OutputsInTime, PairCounterResetMachine.init_eq]
  simp only [Option.map_some]
  rw [PairCounterResetMachine.halt_eq, ← PairCounterResetMachine.reset_encode]
  exact PairCounterResetMachine.run _

noncomputable def pairCounterResetComputableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Input PairQueries.Input
      PairQueries.inputFinEncoding PairQueries.inputFinEncoding PairCounters.resetSecond where
  tm := PairCounterResetMachine.computer
  inputAlphabet := Equiv.refl PairCounterResetMachine.Wire
  outputAlphabet := Equiv.refl PairCounterResetMachine.Wire
  time := 2 * Polynomial.X + 2
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_X] using pairCounterReset_outputsInTime input

/-- Increment the inner binary counter using only checked generic adapters. -/
noncomputable def pairInnerCounterComputableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Input PairQueries.Input
      PairQueries.inputFinEncoding PairQueries.inputFinEncoding PairCounters.inner :=
  LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    ScopeExtraction.endpointsFinEncoding ScopeExtraction.endpointsFinEncoding
    PairQueries.retainedFinEncoding _
    (LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
      finEncodingNatBool finEncodingNatBool finEncodingNatBool _ binarySuccComputableInPolyTime)

noncomputable def pairFirstCounterComputableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Input PairQueries.Input
      PairQueries.inputFinEncoding PairQueries.inputFinEncoding PairCounters.incrementFirst :=
  LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    ScopeExtraction.endpointsFinEncoding ScopeExtraction.endpointsFinEncoding
    PairQueries.retainedFinEncoding _
    (LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
      finEncodingNatBool finEncodingNatBool finEncodingNatBool _ binarySuccComputableInPolyTime)

/-- Move to the next row, resetting the inner counter and handling binary carry. -/
noncomputable def pairOuterCounterComputableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Input PairQueries.Input
      PairQueries.inputFinEncoding PairQueries.inputFinEncoding PairCounters.outer :=
  compositionComputableInPolyTime _ _ _ _ _
    pairCounterResetComputableInPolyTime pairFirstCounterComputableInPolyTime

#print axioms PairCounters.resetSecond_length
#print axioms PairCounters.inner_length_le
#print axioms PairCounters.outer_length_le
#print axioms PairCounters.retained_eq
#print axioms PairCounters.nextPair_eq
#print axioms pairCounterReset_outputsInTime
#print axioms pairCounterResetComputableInPolyTime
#print axioms pairInnerCounterComputableInPolyTime
#print axioms pairOuterCounterComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
