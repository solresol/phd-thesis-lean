import PhdThesisLean.AllDifferentCSPRankIteration

/-!
# Initialize the canonical-rank tally

Copy the exact serialized target/symbol query and append a unary tally of one.
The machine charges both order-preserving passes, the appended cell, and halt,
including the completely empty query (target zero and no symbols).
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace RankInitialization

def seed (query : DomainSymbolMembership.Input) : RankAccumulator.Output := (query, 1)

theorem output_length (query : DomainSymbolMembership.Input) :
    (RankAccumulator.outputFinEncoding.encode (seed query)).length =
      (DomainSymbolMembership.finEncoding.encode query).length + 1 := by
  simp [RankAccumulator.outputFinEncoding, seed, unaryFinEncodingNat,
    unaryEncodeNat_eq_replicate_true]

theorem finish_initialize (query : DomainSymbolMembership.Input) :
    RankIteration.finish (seed query).1.1 (seed query).1.2 (seed query).2 =
      DomainSymbols.rank query.2 query.1 := RankIteration.finish_one_eq_rank _ _

end RankInitialization

namespace RankInitializationMachine

abbrev Query := Sum Bool (Option Bool)
abbrev Output := Sum Query Bool

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
        (.push .saved (fun cell => cell.getD (.inl false)) <| .goto fun _ => .copy)
        (.push .output (fun _ => .inr true) <| .goto fun _ => .emit)
  | .emit => .pop .saved (fun _ cell => cell) <|
      .branch Option.isSome
        (.push .output (fun cell => .inl (cell.getD (.inl false))) <| .goto fun _ => .emit)
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
      (cfg (some .emit) none [] (input.reverse ++ saved) [.inr true]) (input.length + 1) := by
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
      (cfg none none [] [] (input.map Sum.inl ++ [.inr true])) (2 * input.length + 2) := by
  have hc := copy_run input [] none
  have he := emit_run input.reverse [.inr true] none
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

end RankInitializationMachine

/-- Starting from the complete query, retain every bit and append the initial
one-based tally in at most `2s+2` finite-machine steps. -/
def rankInitialization_outputsInTime (query : DomainSymbolMembership.Input) :
    TM2OutputsInTime RankInitializationMachine.computer
      (DomainSymbolMembership.finEncoding.encode query)
      (some (RankAccumulator.outputFinEncoding.encode (RankInitialization.seed query)))
      (2 * (DomainSymbolMembership.finEncoding.encode query).length + 2) := by
  rw [TM2OutputsInTime, RankInitializationMachine.init_eq]
  simp only [Option.map_some]
  rw [RankInitializationMachine.halt_eq]
  simpa [RankAccumulator.outputFinEncoding, RankInitialization.seed,
    unaryFinEncodingNat, unaryEncodeNat] using
      RankInitializationMachine.run (DomainSymbolMembership.finEncoding.encode query)

noncomputable def rankInitializationComputableInPolyTime :
    @TM2ComputableInPolyTime DomainSymbolMembership.Input RankAccumulator.Output
      DomainSymbolMembership.finEncoding RankAccumulator.outputFinEncoding RankInitialization.seed where
  tm := RankInitializationMachine.computer
  inputAlphabet := Equiv.refl RankInitializationMachine.Query
  outputAlphabet := Equiv.refl RankInitializationMachine.Output
  time := 2 * Polynomial.X + 2
  outputsFun query := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using rankInitialization_outputsInTime query

#print axioms RankInitialization.output_length
#print axioms RankInitialization.finish_initialize
#print axioms rankInitialization_outputsInTime
#print axioms rankInitializationComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
