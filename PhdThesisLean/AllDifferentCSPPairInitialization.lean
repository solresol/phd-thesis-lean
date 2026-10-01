import PhdThesisLean.AllDifferentCSPPairTest

/-!
# Initialize the bounded candidate-pair scan

Retain the complete ranked domains, unary variable bound and counted scopes,
with binary endpoints zero and an empty emitted-edge list. Both zero words
and the empty list have empty encodings; only the tags change. The finite
machine preserves source order and clears every scratch stack.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PairInitialization

def seed (value : BoundedRelabelledSections.Value) : PairQueries.Input := ((0, 0), value, [])

theorem retained_eq (value : BoundedRelabelledSections.Value) : (seed value).2.1 = value := rfl

theorem output_length (value : BoundedRelabelledSections.Value) :
    (PairQueries.inputFinEncoding.encode (seed value)).length =
      (BoundedRelabelledSections.finEncoding.encode value).length := by
  simp [PairQueries.input_length, seed, ScopeExtraction.endpointsFinEncoding,
    finEncodingNatBool, encodingNatBool, encodeNat, encodeNum, NegativeRows.inputEncode,
    NegativeRows.pairRows, DomainFieldSection.rowPayloadEncode, LeanNPHardness.CountedNatRows.rowFields,
    SourceOrderRawFields.encode]

/-- A zero variable count has no candidate, even if malformed scopes mention indices. -/
theorem zero_edges (value : BoundedRelabelledSections.Value) (h : value.1.2 = 0) :
    BoundedRelabelledSections.edges value = [] := by
  simp [BoundedRelabelledSections.edges, PrimalEdgeEnumeration.enumerate,
    PrimalEdgeEnumeration.candidates, h]

end PairInitialization

namespace PairInitializationMachine

abbrev Query := Sum (Sum (Option Bool) Bool) (Option Bool)
abbrev Output := PairQueriesMachine.Input

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
        (.push .saved (fun cell => cell.getD (.inr none)) <| .goto fun _ => .copy)
        (.goto fun _ => .emit)
  | .emit => .pop .saved (fun _ cell => cell) <|
      .branch Option.isSome
        (.push .output (fun cell => tag (cell.getD (.inr none))) <| .goto fun _ => .emit)
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
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

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

end PairInitializationMachine

/-- Start the complete grid with empty output in `2s+2` finite-machine steps,
including both exhaustion checks and canonical halt. -/
def pairInitialization_outputsInTime (query : BoundedRelabelledSections.Value) :
    TM2OutputsInTime PairInitializationMachine.computer
      (BoundedRelabelledSections.finEncoding.encode query)
      (some (PairQueries.inputFinEncoding.encode (PairInitialization.seed query)))
      (2 * (BoundedRelabelledSections.finEncoding.encode query).length + 2) := by
  rw [TM2OutputsInTime, PairInitializationMachine.init_eq]
  simp only [Option.map_some]
  rw [PairInitializationMachine.halt_eq]
  simpa [PairQueries.inputFinEncoding, PairQueries.retainedFinEncoding,
    PairInitialization.seed, ScopeExtraction.endpointsFinEncoding, finEncodingNatBool,
    encodingNatBool, encodeNat, encodeNum, NegativeRows.inputFinEncoding, NegativeRows.inputEncode,
    NegativeRows.pairRows, DomainFieldSection.rowPayloadEncode, LeanNPHardness.CountedNatRows.rowFields,
    SourceOrderRawFields.encode, List.map_map,
    Function.comp_def, PairInitializationMachine.tag] using
      PairInitializationMachine.run (BoundedRelabelledSections.finEncoding.encode query)

noncomputable def pairInitializationComputableInPolyTime :
    @TM2ComputableInPolyTime BoundedRelabelledSections.Value PairQueries.Input
      BoundedRelabelledSections.finEncoding PairQueries.inputFinEncoding PairInitialization.seed where
  tm := PairInitializationMachine.computer
  inputAlphabet := Equiv.refl PairInitializationMachine.Query
  outputAlphabet := Equiv.refl PairInitializationMachine.Output
  time := 2 * Polynomial.X + 2
  outputsFun query := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using pairInitialization_outputsInTime query

/-- The initial pair state is constructed from the actual Boolean compiler input;
no ranked sections or scan counters are supplied externally. -/
noncomputable def runtimeCompilerPairInitializationComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem PairQueries.Input
      RuntimeCompilerInput.finEncoding PairQueries.inputFinEncoding
      (fun C => PairInitialization.seed (BoundedRelabelledSections.ofRuntimeSystem C)) := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerBoundedRelabelledSectionsComputableInPolyTime
    pairInitializationComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by simpa only [Function.comp_def] using composed.outputsFun C }

example : PairInitialization.seed (([], 0), []) = ((0, 0), (([], 0), []), []) := rfl
example : PairInitialization.seed (([(0, 1)], 1), [[], [0, 0]]) =
    ((0, 0), (([(0, 1)], 1), [[], [0, 0]]), []) := rfl

#print axioms runtimeCompilerPairInitializationComputableInPolyTime
#print axioms PairInitialization.output_length
#print axioms PairInitialization.retained_eq
#print axioms PairInitialization.zero_edges
#print axioms pairInitialization_outputsInTime
#print axioms pairInitializationComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
