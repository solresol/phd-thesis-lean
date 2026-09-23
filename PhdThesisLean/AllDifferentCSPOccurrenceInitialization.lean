import PhdThesisLean.AllDifferentCSPOccurrenceLoop

/-!
# Initialize the complete occurrence traversal

Tag the retained occurrences and symbols as the source of a traversal with
an empty output accumulator. The two-pass finite machine preserves order,
uses exactly the checked state encoding, and charges copying and cleanup.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace OccurrenceInitialization

def seed (query : DomainSymbolExtraction.Value) : OccurrenceIteration.State := (query, [])

theorem output_length (query : DomainSymbolExtraction.Value) :
    (OccurrenceIteration.stateFinEncoding.encode (seed query)).length =
      (DomainSymbolExtraction.finEncoding.encode query).length :=
  OccurrenceIteration.seed_length query

theorem finish_initialize (query : DomainSymbolExtraction.Value) :
    OccurrenceLoop.result (seed query) = query.1.map
      (fun occurrence => (occurrence.1, DomainSymbols.rank query.2 occurrence.2)) := by
  simp [OccurrenceLoop.result, seed, OccurrenceIteration.finish_eq_append_map]

end OccurrenceInitialization

namespace OccurrenceInitializationMachine

abbrev Query := Sum (Option Bool) (Option Bool)
abbrev Output := Sum Query (Option Bool)

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
        (.push .saved (fun cell => cell.getD (.inl none)) <| .goto fun _ => .copy)
        (.goto fun _ => .emit)
  | .emit => .pop .saved (fun _ cell => cell) <|
      .branch Option.isSome
        (.push .output (fun cell => .inl (cell.getD (.inl none))) <| .goto fun _ => .emit)
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
      (cfg none none [] [] (saved.reverse.map Sum.inl ++ output)) (saved.length + 1) := by
  induction saved generalizing output state with
  | nil => exact one (by initialize_step)
  | cons cell saved ih =>
      have h : Run (cfg (some .emit) state [] (cell :: saved) output)
          (cfg (some .emit) (some cell) [] saved (.inl cell :: output)) 1 := one (by initialize_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (.inl cell :: output) (some cell))

private def run (input : List Query) :
    Run (cfg (some .copy) none input [] [])
      (cfg none none [] [] (input.map Sum.inl ++ [])) (2 * input.length + 2) := by
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

end OccurrenceInitializationMachine

/-- Tag the complete occurrence/symbol wire for an empty accumulator in
at most `2s+2` finite-machine steps, preserving its exact length. -/
def occurrenceInitialization_outputsInTime (query : DomainSymbolExtraction.Value) :
    TM2OutputsInTime OccurrenceInitializationMachine.computer
      (DomainSymbolExtraction.finEncoding.encode query)
      (some (OccurrenceIteration.stateFinEncoding.encode (OccurrenceInitialization.seed query)))
      (2 * (DomainSymbolExtraction.finEncoding.encode query).length + 2) := by
  rw [TM2OutputsInTime, OccurrenceInitializationMachine.init_eq]
  simp only [Option.map_some]
  rw [OccurrenceInitializationMachine.halt_eq]
  simpa [OccurrenceAccumulator.outputFinEncoding, OccurrenceInitialization.seed,
    DomainFieldRow.outputFinEncoding, DomainFieldRow.outputEncode] using
      OccurrenceInitializationMachine.run (DomainSymbolExtraction.finEncoding.encode query)

noncomputable def occurrenceInitializationComputableInPolyTime :
    @TM2ComputableInPolyTime DomainSymbolExtraction.Value OccurrenceIteration.State
      DomainSymbolExtraction.finEncoding OccurrenceIteration.stateFinEncoding OccurrenceInitialization.seed where
  tm := OccurrenceInitializationMachine.computer
  inputAlphabet := Equiv.refl OccurrenceInitializationMachine.Query
  outputAlphabet := Equiv.refl OccurrenceInitializationMachine.Output
  time := 2 * Polynomial.X + 2
  outputsFun query := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using occurrenceInitialization_outputsInTime query

#print axioms OccurrenceInitialization.output_length
#print axioms OccurrenceInitialization.finish_initialize
#print axioms occurrenceInitialization_outputsInTime
#print axioms occurrenceInitializationComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
