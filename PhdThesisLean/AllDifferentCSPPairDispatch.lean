import PhdThesisLean.AllDifferentCSPPairGate

/-!
# One complete finite pair-scan dispatch

Compute continuation, invoke exactly the selected complete branch, and remove
the temporary decision. An outer gate computes exhaustion and skips the whole
active step when finished. The resulting machine implements `PairAdvance.advance`
on every checked state, including arbitrary exhausted states and zero variables.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PairDecisionEraseMachine

abbrev Wire := PairQueriesMachine.Input
abbrev Input := Sum Bool Wire
abbrev State := Option Input × Option Wire

inductive Stack
  | input | saved | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | emit
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input
  | _ => Wire

private def observe (_ : State) (bit : Option Input) : State := (bit, none)
private def remember (_ : State) (bit : Option Wire) : State := (none, bit)
private def retained (s : State) : Option Wire := s.1.bind Sum.getRight?
private def cell (s : State) : Wire := (retained s).getD (.inl (.inl false))
private def savedCell (s : State) : Wire := s.2.getD (.inl (.inl false))

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch (fun s => s.1.isSome)
      (.branch (fun s => (retained s).isSome)
        (.push .saved cell <| .goto fun _ => .scan)
        (.goto fun _ => .scan))
      (.goto fun _ => .emit)
  | .emit => .pop .saved remember <| .branch (fun s => s.2.isSome)
      (.push .output savedCell <| .goto fun _ => .emit)
      (.load (fun _ => (none, none)) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := (none, none)
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input : List Input) (saved output : List Wire) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .saved => saved | .output => output

private def cfg (label : Option Label) (state : State)
    (input : List Input) (saved output : List Wire) : computer.Cfg :=
  ⟨label, state, stackContents input saved output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) :=
  EvalsToInTime computer.step a (some b) time

private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }

private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "erase_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, observe, remember,
    retained, cell, savedCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Input) (saved output : List Wire) (state : State) :
    Run (cfg (some .scan) state input saved output)
      (cfg (some .emit) (none, none) []
        ((input.filterMap Sum.getRight?).reverse ++ saved) output) (input.length + 1) := by
  induction input generalizing saved state with
  | nil => exact one (by erase_step)
  | cons bit input ih =>
      cases bit with
      | inl bit =>
          have h : Run (cfg (some .scan) state (.inl bit :: input) saved output)
              (cfg (some .scan) (some (.inl bit), none) input saved output) 1 :=
            one (by erase_step)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            seq h (ih saved (some (.inl bit), none))
      | inr bit =>
          have h : Run (cfg (some .scan) state (.inr bit :: input) saved output)
              (cfg (some .scan) (some (.inr bit), none) input (bit :: saved) output) 1 :=
            one (by erase_step)
          simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using seq h (ih (bit :: saved) (some (.inr bit), none))

private def emit_run (saved output : List Wire) (state : State) :
    Run (cfg (some .emit) state [] saved output)
      (cfg none (none, none) [] [] (saved.reverse ++ output)) (saved.length + 1) := by
  induction saved generalizing output state with
  | nil => exact one (by erase_step)
  | cons bit saved ih =>
      have h : Run (cfg (some .emit) state [] (bit :: saved) output)
          (cfg (some .emit) (none, some bit) [] saved (bit :: output)) 1 := one (by erase_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (bit :: output) (none, some bit))

private theorem init_eq (input : List Input) :
    initList computer input = cfg (some .scan) (none, none) input [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Wire) :
    haltList computer output = cfg none (none, none) [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

def outputsInTime (input : PairTest.Output) :
    TM2OutputsInTime computer (PairTest.outputFinEncoding.encode input)
      (some (PairQueries.inputFinEncoding.encode input.2))
      (2 * (PairTest.outputFinEncoding.encode input).length + 2) := by
  have hs := scan_run (PairTest.outputFinEncoding.encode input) [] [] (none, none)
  have he := emit_run ((PairTest.outputFinEncoding.encode input).filterMap Sum.getRight?).reverse
    [] (none, none)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hs he
  have selected : (PairTest.outputFinEncoding.encode input).filterMap Sum.getRight? =
      PairQueries.inputFinEncoding.encode input.2 := by
    simp [PairTest.outputFinEncoding, LeanNPHardness.PairEncoding.finEncoding,
      finEncodingBoolBool, encodeBool, List.filterMap_map, Function.comp_def]
  have run := seq hs he
  rw [selected] at run
  rw [TM2OutputsInTime, init_eq]
  simp only [Option.map_some, halt_eq]
  apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono run
  have h := List.length_filterMap_le Sum.getRight? (PairTest.outputFinEncoding.encode input)
  rw [selected] at h
  omega

end PairDecisionEraseMachine

/-- Discard the temporary control answer, retaining every original state cell. -/
noncomputable def pairDecisionEraseComputableInPolyTime :
    @TM2ComputableInPolyTime PairTest.Output PairQueries.Input
      PairTest.outputFinEncoding PairQueries.inputFinEncoding Prod.snd where
  tm := PairDecisionEraseMachine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X] using PairDecisionEraseMachine.outputsInTime input

namespace PairDispatch

def selectedStep (state : PairQueries.Input) : PairQueries.Input :=
  if PairControl.continues state then PairStepBranches.inner state else PairStepBranches.outer state

/-- Both gates retain the original choice, so exactly one branch is invoked. -/
noncomputable def selectedComputableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Input PairQueries.Input
      PairQueries.inputFinEncoding PairQueries.inputFinEncoding selectedStep := by
  let inner := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    finEncodingBoolBool PairQueries.inputFinEncoding PairQueries.inputFinEncoding
    PairStepBranches.inner pairInnerStepComputableInPolyTime
  let outer := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    finEncodingBoolBool PairQueries.inputFinEncoding PairQueries.inputFinEncoding
    PairStepBranches.outer pairOuterStepComputableInPolyTime
  let first := compositionComputableInPolyTime _ _ _ _ _ pairContinuesComputableInPolyTime
    (PairGateMachine.computableInPolyTime inner true)
  let branches := compositionComputableInPolyTime _ _ _ _ _ first
    (PairGateMachine.computableInPolyTime outer false)
  let composed := compositionComputableInPolyTime _ _ _ _ _ branches pairDecisionEraseComputableInPolyTime
  exact { composed with
    outputsFun := fun state => by
      cases h : PairControl.continues state <;>
        simpa [Function.comp_def, PairControl.evaluate, selectedStep, h] using composed.outputsFun state }

/-- Exhaustion skips the complete active step; no predicate is supplied by the caller. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Input PairQueries.Input
      PairQueries.inputFinEncoding PairQueries.inputFinEncoding PairAdvance.advance := by
  let active := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    finEncodingBoolBool PairQueries.inputFinEncoding PairQueries.inputFinEncoding
    selectedStep selectedComputableInPolyTime
  let gated := compositionComputableInPolyTime _ _ _ _ _ pairActiveComputableInPolyTime
    (PairGateMachine.computableInPolyTime active true)
  let composed := compositionComputableInPolyTime _ _ _ _ _ gated pairDecisionEraseComputableInPolyTime
  exact { composed with
    outputsFun := fun state => by
      rw [PairControl.advance_eq]
      cases h : PairControl.active state <;>
        simpa [Function.comp_def, PairControl.evaluate, selectedStep, h] using composed.outputsFun state }

/-- Complete dispatched calls have a uniform bound in the original retained input. -/
theorem iterate_steps_le (value : BoundedRelabelledSections.Value) (k : ℕ) :
    (computableInPolyTime.outputsFun (PairAdvance.run value k)).steps ≤
      computableInPolyTime.time.eval
        (12 * ((BoundedRelabelledSections.finEncoding.encode value).length + 1) ^ 3) :=
  (computableInPolyTime.outputsFun _).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
      (PairAdvance.iterate_length_le_cubic value k))

/-- Exact next-state output with every dispatch cost bounded in the original
retained-section length. This is the body contract for the remaining loop. -/
noncomputable def run_step_outputsInTime
    (value : BoundedRelabelledSections.Value) (k : ℕ) :
    TM2OutputsInTime computableInPolyTime.tm
      ((PairQueries.inputFinEncoding.encode (PairAdvance.run value k)).map
        computableInPolyTime.inputAlphabet.symm)
      (some ((PairQueries.inputFinEncoding.encode (PairAdvance.run value (k + 1))).map
        computableInPolyTime.outputAlphabet.symm))
      (computableInPolyTime.time.eval
        (12 * ((BoundedRelabelledSections.finEncoding.encode value).length + 1) ^ 3)) := by
  rw [PairAdvance.run_succ]
  exact LeanNPHardness.MachinePrimitives.evalsToInTimeMono
    (computableInPolyTime.outputsFun (PairAdvance.run value k))
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
      (PairAdvance.iterate_length_le_cubic value k))

-- Zero variables, a singleton's final rejecting pair, binary carry, row wrap,
-- and an exhausted state whose out-of-range endpoints would otherwise emit.
example : PairAdvance.advance ((0, 0), (([], 0), []), []) =
    ((0, 0), (([], 0), []), []) := rfl
example : PairAdvance.advance ((0, 0), (([], 1), [[0, 0]]), []) =
    ((1, 0), (([], 1), [[0, 0]]), []) := by decide
example : selectedStep ((0, 7), (([], 9), [[], [0, 7], [7, 0]]), [(0, 1)]) =
    ((0, 8), (([], 9), [[], [0, 7], [7, 0]]), [(0, 1), (0, 7)]) := by decide
example : selectedStep ((0, 8), (([], 9), [[0, 8]]), [(0, 1)]) =
    ((1, 0), (([], 9), [[0, 8]]), [(0, 1), (0, 8)]) := by decide
example : PairAdvance.advance ((9, 10), (([], 9), [[9, 10]]), [(0, 1)]) =
    ((9, 10), (([], 9), [[9, 10]]), [(0, 1)]) := rfl

end PairDispatch

#print axioms PairDecisionEraseMachine.outputsInTime
#print axioms pairDecisionEraseComputableInPolyTime
#print axioms PairDispatch.selectedComputableInPolyTime
#print axioms PairDispatch.computableInPolyTime
#print axioms PairDispatch.iterate_steps_le
#print axioms PairDispatch.run_step_outputsInTime

end PhdThesisLean.AllDifferentCSPMachine
