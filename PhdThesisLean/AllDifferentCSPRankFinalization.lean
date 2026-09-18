import PhdThesisLean.AllDifferentCSPRankControl

/-!
# Return the final unary rank tally

Discard the exhausted query and emit its unary accumulator. The machine also
projects a tally from an arbitrary state; only an empty symbol list justifies
identifying that tally with the result of the recursive rank computation.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open LeanNPHardness.MachineComposition

namespace RankFinalization

def result (input : RankControl.Input) : ℕ := input.2

theorem result_eq_finish_of_empty (input : RankControl.Input)
    (empty : (RankControl.inspect input).1 = false) :
    result input = RankIteration.finish input.1.1 input.1.2 input.2 := by
  rcases input with ⟨⟨target, symbols⟩, count⟩
  cases symbols with
  | nil => rfl
  | cons symbol symbols => simp [RankControl.inspect] at empty

theorem output_length_le (input : RankControl.Input) :
    (unaryFinEncodingNat.encode (result input)).length ≤ (RankControl.inputFinEncoding.encode input).length := by
  simp [result, RankAccumulator.outputFinEncoding]

end RankFinalization

namespace RankFinalizationMachine

abbrev Wire := RankControlMachine.Wire

inductive Stack
  | input | output
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Wire | .output => Bool

abbrev State := Option Wire

def program (_ : Unit) : TM2.Stmt Alphabet Unit State :=
  .pop .input (fun _ cell => cell) <|
    .branch Option.isSome
      (.branch (fun cell => (cell.bind Sum.getRight?).isSome)
        (.push .output (fun cell => (cell.bind Sum.getRight?).getD false) <| .goto fun _ => ())
        (.goto fun _ => ()))
      (.load (fun _ => none) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Unit
  main := ()
  σ := State
  initialState := none
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input : List Wire) (output : List Bool) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .output => output

private def cfg (label : Option Unit) (state : State) (input : List Wire)
    (output : List Bool) : computer.Cfg := ⟨label, state, stackContents input output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "finalize_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def run (input : List Wire) (output : List Bool) (state : State) :
    Run (cfg (some ()) state input output)
      (cfg none none [] ((input.filterMap Sum.getRight?).reverse ++ output)) (input.length + 1) := by
  induction input generalizing output state with
  | nil => exact one (by finalize_step)
  | cons cell input ih =>
      cases cell with
      | inl query =>
          have h : Run (cfg (some ()) state (.inl query :: input) output)
              (cfg (some ()) (some (.inl query)) input output) 1 := one (by finalize_step)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            seq h (ih output (some (.inl query)))
      | inr bit =>
          have h : Run (cfg (some ()) state (.inr bit :: input) output)
              (cfg (some ()) (some (.inr bit)) input (bit :: output)) 1 := one (by finalize_step)
          simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using seq h (ih (bit :: output) (some (.inr bit)))

private theorem init_eq (input : List Wire) :
    initList computer input = cfg (some ()) none input [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Bool) :
    haltList computer output = cfg none none [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

end RankFinalizationMachine

/-- Return the accumulator and clear the query in at most `s+1` steps for the
complete state encoding length `s`. -/
def rankFinalization_outputsInTime (input : RankControl.Input) :
    TM2OutputsInTime RankFinalizationMachine.computer (RankControl.inputFinEncoding.encode input)
      (some (unaryFinEncodingNat.encode (RankFinalization.result input)))
      ((RankControl.inputFinEncoding.encode input).length + 1) := by
  rw [TM2OutputsInTime, RankFinalizationMachine.init_eq]
  simp only [Option.map_some]
  rw [RankFinalizationMachine.halt_eq]
  have discard : (DomainSymbolMembership.finEncoding.encode input.1).filterMap
      (fun _ => (none : Option Bool)) = [] := by simp
  simpa [RankAccumulator.outputFinEncoding, RankFinalization.result, unaryFinEncodingNat,
    unaryEncodeNat_eq_replicate_true, List.filterMap_map, Function.comp_def, discard] using
      RankFinalizationMachine.run (RankControl.inputFinEncoding.encode input) [] none

noncomputable def rankFinalizationComputableInPolyTime :
    @TM2ComputableInPolyTime RankControl.Input ℕ RankControl.inputFinEncoding unaryFinEncodingNat
      RankFinalization.result where
  tm := RankFinalizationMachine.computer
  inputAlphabet := Equiv.refl RankFinalizationMachine.Wire
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_X] using rankFinalization_outputsInTime input

#print axioms RankFinalization.result_eq_finish_of_empty
#print axioms RankFinalization.output_length_le
#print axioms rankFinalization_outputsInTime
#print axioms rankFinalizationComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
