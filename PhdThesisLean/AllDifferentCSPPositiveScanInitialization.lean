import PhdThesisLean.AllDifferentCSPPositiveCounters

/-!
# Initialize the complete rectangular positive scan

Retain both unary bounds, ranked occurrences, scopes, negative rows and the
common binary weight. The binary candidate starts at `(0, 0)` and the emitted
positive list is empty. This finite pass constructs the exact `PositiveAdvance`
seed from the internally computed sections, preserving every input bit.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PositiveScanInitialization

abbrev seed := PositiveAdvance.seed

theorem retained_eq (value : CountedPositiveSections.Value) : (seed value).2.1 = value := rfl

theorem output_length (value : CountedPositiveSections.Value) :
    (PositiveCandidateQueries.inputFinEncoding.encode (seed value)).length =
      (CountedPositiveSections.finEncoding.encode value).length := by
  simp [PositiveCandidateQueries.input_length, seed, PositiveAdvance.seed, ScopeExtraction.endpointsFinEncoding,
    finEncodingNatBool, encodeNat, encodeNum, PositiveRows.outputEncode]

/-- The initialized state already satisfies the complete reached-state invariant. -/
theorem invariant (value : CountedPositiveSections.Value) :
    PositiveAdvance.Invariant (seed value) := PositiveAdvance.seed_invariant value

end PositiveScanInitialization

namespace PositiveScanInitializationMachine

abbrev Query := PositiveCandidateQueriesMachine.Counted
abbrev Output := PositiveCandidateQueriesMachine.Input

def tag (cell : Query) : Output := .inr (.inl cell)

inductive Stack
  | input | saved | output
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input | .saved => Query | .output => Output

inductive Label
  | copy | emit
  deriving DecidableEq, Fintype

abbrev State := Option Query

def program : Label → TM2.Stmt Alphabet Label State
  | .copy => .pop .input (fun _ cell => cell) <|
      .branch Option.isSome
        (.push .saved (fun cell => cell.getD (.inr (.inr none))) <| .goto fun _ => .copy)
        (.goto fun _ => .emit)
  | .emit => .pop .saved (fun _ cell => cell) <|
      .branch Option.isSome
        (.push .output (fun cell => tag (cell.getD (.inr (.inr none)))) <| .goto fun _ => .emit)
        (.load (fun _ => none) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .copy
  σ := State
  initialState := none
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input saved : List Query) (output : List Output) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .saved => saved | .output => output

private def cfg (label : Option Label) (state : State) (input saved : List Query)
    (output : List Output) : computer.Cfg := ⟨label, state, stackContents input saved output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using! h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using! EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "initialize_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, Function.update, tag]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def copy_run (input saved : List Query) (state : State) :
    Run (cfg (some .copy) state input saved [])
      (cfg (some .emit) none [] (input.reverse ++ saved) []) (input.length + 1) := by
  induction input generalizing saved state with
  | nil => exact one (by initialize_step)
  | cons cell input ih =>
      have h : Run (cfg (some .copy) state (cell :: input) saved [])
          (cfg (some .copy) (some cell) input (cell :: saved) []) 1 := one (by initialize_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (cell :: saved) (some cell))

private def emit_run (saved : List Query) (output : List Output) (state : State) :
    Run (cfg (some .emit) state [] saved output)
      (cfg none none [] [] (saved.reverse.map tag ++ output)) (saved.length + 1) := by
  induction saved generalizing output state with
  | nil => exact one (by initialize_step)
  | cons cell saved ih =>
      have h : Run (cfg (some .emit) state [] (cell :: saved) output)
          (cfg (some .emit) (some cell) [] saved (tag cell :: output)) 1 := one (by initialize_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (tag cell :: output) (some cell))

private def run (input : List Query) :
    Run (cfg (some .copy) none input [] [])
      (cfg none none [] [] (input.map tag ++ [])) (2 * input.length + 2) := by
  have hc := copy_run input [] none
  have he := emit_run input.reverse [] none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hc he
  convert seq hc he using 1 <;> first | simp only [List.append_nil] | omega

private theorem init_eq (input : List Query) :
    initList computer input = cfg (some .copy) none input [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none none [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

end PositiveScanInitializationMachine

/-- Start the complete grid with empty output in `2s+2` finite-machine steps,
including both exhaustion checks and canonical halt. -/
def positiveScanInitialization_outputsInTime (query : CountedPositiveSections.Value) :
    TM2OutputsInTime PositiveScanInitializationMachine.computer
      (CountedPositiveSections.finEncoding.encode query)
      (some (PositiveCandidateQueries.inputFinEncoding.encode (PositiveScanInitialization.seed query)))
      (2 * (CountedPositiveSections.finEncoding.encode query).length + 2) := by
  rw [TM2OutputsInTime, PositiveScanInitializationMachine.init_eq]
  simp only [Option.map_some]
  rw [PositiveScanInitializationMachine.halt_eq]
  simpa [PositiveCandidateQueries.inputFinEncoding, PositiveCandidateQueries.retainedFinEncoding,
    PositiveScanInitialization.seed, PositiveAdvance.seed, ScopeExtraction.endpointsFinEncoding, finEncodingNatBool,
    encodingNatBool, encodeNat, encodeNum, PositiveRows.outputFinEncoding,
    PositiveRows.outputEncode, List.map_map, Function.comp_def,
    PositiveScanInitializationMachine.tag] using!
      PositiveScanInitializationMachine.run (CountedPositiveSections.finEncoding.encode query)

noncomputable def positiveScanInitializationComputableInPolyTime :
    @TM2ComputableInPolyTime CountedPositiveSections.Value PositiveCandidateQueries.Input
      CountedPositiveSections.finEncoding PositiveCandidateQueries.inputFinEncoding PositiveScanInitialization.seed where
  tm := PositiveScanInitializationMachine.computer
  inputAlphabet := Equiv.refl PositiveScanInitializationMachine.Query
  outputAlphabet := Equiv.refl PositiveScanInitializationMachine.Output
  time := 2 * Polynomial.X + 2
  outputsFun query := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using positiveScanInitialization_outputsInTime query

/-- The initial positive state is constructed from the actual Boolean compiler input;
no ranked sections or scan counters are supplied externally. -/
noncomputable def runtimeCompilerPositiveScanInitializationComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem PositiveCandidateQueries.Input
      RuntimeCompilerInput.finEncoding PositiveCandidateQueries.inputFinEncoding
      (fun C => PositiveScanInitialization.seed (CountedPositiveSections.ofRuntimeSystem C)) := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerCountedPositiveSectionsComputableInPolyTime
    positiveScanInitializationComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by simpa only [Function.comp_def] using composed.outputsFun C }

example : PositiveScanInitialization.seed (((([], 0), 0), []), ([], 0)) =
    ((0, 0), (((([], 0), 0), []), ([], 0)), []) := rfl
example : PositiveScanInitialization.seed
    (((([(0, 1), (0, 1)], 2), 3), [[], [0, 2]]), ([(0, 2)], 1000000)) =
    ((0, 0), (((([(0, 1), (0, 1)], 2), 3), [[], [0, 2]]), ([(0, 2)], 1000000)), []) := rfl

#print axioms runtimeCompilerPositiveScanInitializationComputableInPolyTime
#print axioms PositiveScanInitialization.output_length
#print axioms PositiveScanInitialization.retained_eq
#print axioms PositiveScanInitialization.invariant
#print axioms positiveScanInitialization_outputsInTime
#print axioms positiveScanInitializationComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
