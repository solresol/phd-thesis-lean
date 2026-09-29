import PhdThesisLean.AllDifferentCSPScopeLoop

/-!
# Initialize and run a complete adjacency query

Construct a false accumulator from the original serialized endpoints and
counted scope section, then compose the checked repeated scope dispatcher.
The query is not supplied with a result bit or externally split scopes.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace ScopeInitialization

def seed (query : ScopeRouting.Remaining) : ScopeIteration.Output := (false, query)

theorem output_length (query : ScopeRouting.Remaining) :
    (ScopeIteration.outputFinEncoding.encode (seed query)).length =
      (ScopeExtraction.remainingFinEncoding.encode query).length + 1 := by
  simp [ScopeTest.outputFinEncoding, seed, finEncodingBoolBool, encodeBool]

theorem finish_initialize (query : ScopeRouting.Remaining) :
    ScopeLoop.result (seed query) =
      PrimalEdgeEnumeration.adjacent query.2 query.1.1 query.1.2 :=
  ScopeIteration.finish_false_eq_adjacent _ _

end ScopeInitialization

namespace ScopeInitializationMachine

abbrev Query := ScopeAccumulatorMachine.Remaining
abbrev Output := Sum Bool Query

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
        (.push .output (fun cell => .inr (cell.getD (.inr none))) <| .goto fun _ => .emit)
        (.push .output (fun _ => .inl false) <| .load (fun _ => none) .halt)

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
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, Function.update]
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
      (cfg none none [] [] (.inl false :: (saved.reverse.map Sum.inr ++ output))) (saved.length + 1) := by
  induction saved generalizing output state with
  | nil => exact one (by initialize_step)
  | cons cell saved ih =>
      have h : Run (cfg (some .emit) state [] (cell :: saved) output)
          (cfg (some .emit) (some cell) [] saved (.inr cell :: output)) 1 := one (by initialize_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (.inr cell :: output) (some cell))

private def run (input : List Query) :
    Run (cfg (some .copy) none input [] [])
      (cfg none none [] [] (.inl false :: input.map Sum.inr)) (2 * input.length + 2) := by
  have hc := copy_run input [] none
  have he := emit_run input.reverse [] none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hc he
  convert seq hc he using 1
  omega

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

end ScopeInitializationMachine

/-- Retain the full query and prepend its false accumulator in `2s+2` steps. -/
def scopeInitialization_outputsInTime (query : ScopeRouting.Remaining) :
    TM2OutputsInTime ScopeInitializationMachine.computer
      (ScopeExtraction.remainingFinEncoding.encode query)
      (some (ScopeIteration.outputFinEncoding.encode (ScopeInitialization.seed query)))
      (2 * (ScopeExtraction.remainingFinEncoding.encode query).length + 2) := by
  rw [TM2OutputsInTime, ScopeInitializationMachine.init_eq]
  simp only [Option.map_some]
  rw [ScopeInitializationMachine.halt_eq]
  simpa [ScopeTest.outputFinEncoding, ScopeInitialization.seed, finEncodingBoolBool, encodeBool] using
      ScopeInitializationMachine.run (ScopeExtraction.remainingFinEncoding.encode query)

noncomputable def scopeInitializationComputableInPolyTime :
    @TM2ComputableInPolyTime ScopeRouting.Remaining ScopeIteration.Output
      ScopeExtraction.remainingFinEncoding ScopeIteration.outputFinEncoding ScopeInitialization.seed where
  tm := ScopeInitializationMachine.computer
  inputAlphabet := Equiv.refl ScopeInitializationMachine.Query
  outputAlphabet := Equiv.refl ScopeInitializationMachine.Output
  time := 2 * Polynomial.X + 2
  outputsFun query := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using scopeInitialization_outputsInTime query

/-- Decide adjacency from the complete serialized endpoint/counted-scope query.
Initialization, every scope test, every transfer and final cleanup are included. -/
noncomputable def scopeAdjacencyComputableInPolyTime :
    @TM2ComputableInPolyTime ScopeRouting.Remaining Bool
      ScopeExtraction.remainingFinEncoding finEncodingBoolBool
      (fun query => PrimalEdgeEnumeration.adjacent query.2 query.1.1 query.1.2) := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    scopeInitializationComputableInPolyTime scopeLoopComputableInPolyTime
  exact { composed with
    outputsFun := fun query => by
      simpa only [Function.comp_def, ScopeInitialization.finish_initialize] using
        composed.outputsFun query }

/-- Both binary endpoints and the entire counted scope section fit within twice
an intermediate's wire length when its unary variable tally bounds the pair. -/
theorem scopeAdjacency_query_length_le (value : BoundedRelabelledSections.Value) (i j : ℕ)
    (hi : i < value.1.2) (hj : j < value.1.2) :
    (ScopeExtraction.remainingFinEncoding.encode ((i, j), value.2)).length ≤
      2 * (BoundedRelabelledSections.finEncoding.encode value).length := by
  have left := (BinaryNatLists.encodeNat_length_le i).trans hi.le
  have right := (BinaryNatLists.encodeNat_length_le j).trans hj.le
  rw [BoundedRelabelledSections.encode_length]
  simp only [ScopeExtraction.remainingFinEncoding, ScopeExtraction.endpointsFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length, finEncodingNatBool,
    encodingNatBool, DomainFieldSection.rowPayloadFinEncoding]
  omega

/-- A uniform polynomial bound for each future bounded-pair scan call, including
traversal of the entire scope section. Query construction remains a separate pass. -/
theorem scopeAdjacency_steps_le (value : BoundedRelabelledSections.Value) (i j : ℕ)
    (hi : i < value.1.2) (hj : j < value.1.2) :
    (scopeAdjacencyComputableInPolyTime.outputsFun ((i, j), value.2)).steps ≤
      scopeAdjacencyComputableInPolyTime.time.eval
        (2 * (BoundedRelabelledSections.finEncoding.encode value).length) := by
  exact (scopeAdjacencyComputableInPolyTime.outputsFun ((i, j), value.2)).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
      (scopeAdjacency_query_length_le value i j hi hj))

example : ScopeLoop.result (ScopeInitialization.seed ((0, 1), [[], [0], [1], []])) = false := by decide
example : ScopeLoop.result (ScopeInitialization.seed ((0, 1000000),
    [[], [0], [1000000, 0, 0], []])) = true := by decide
example : ScopeLoop.result (ScopeInitialization.seed ((0, 0), [])) = false := rfl
example : ScopeLoop.result (ScopeInitialization.seed ((0, 0), [[], []])) = false := by decide
example : ScopeLoop.result (ScopeInitialization.seed ((0, 0), [[0]])) = true := by decide

#print axioms ScopeInitialization.output_length
#print axioms ScopeInitialization.finish_initialize
#print axioms scopeInitialization_outputsInTime
#print axioms scopeInitializationComputableInPolyTime
#print axioms scopeAdjacencyComputableInPolyTime
#print axioms scopeAdjacency_query_length_le
#print axioms scopeAdjacency_steps_le

end PhdThesisLean.AllDifferentCSPMachine
