import PhdThesisLean.AllDifferentCSPPositiveInitialization

/-!
# Construct a positive-membership query and retain the complete scan state

Copy the candidate's binary index and rank and the exact counted occurrence
stream. Preserve both unary bounds, scopes, negative rows, common binary
weight and previously emitted positive rows. The finite routing pass restores
source order and clears all scratch stacks; no split query is supplied by the
caller.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PositiveCandidateQueries

abbrev Input := (ℕ × ℕ) × (CountedPositiveSections.Value × List PositiveBlock.Value)
abbrev Output := PositiveMembership.Input × Input

def retainedFinEncoding : FinEncoding (CountedPositiveSections.Value × List PositiveBlock.Value) :=
  LeanNPHardness.PairEncoding.finEncoding CountedPositiveSections.finEncoding
    PositiveRows.outputFinEncoding

def inputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding ScopeExtraction.endpointsFinEncoding retainedFinEncoding

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding PositiveMembership.finEncoding inputFinEncoding

def query (input : Input) : PositiveMembership.Input := (input.1, input.2.1.1.1.1.1)

def prepare (input : Input) : Output := (query input, input)

theorem input_length (input : Input) :
    (inputFinEncoding.encode input).length =
      (ScopeExtraction.endpointsFinEncoding.encode input.1).length +
        (CountedPositiveSections.finEncoding.encode input.2.1).length +
        (PositiveRows.outputEncode input.2.2).length := by
  simp [inputFinEncoding, retainedFinEncoding, PositiveRows.outputFinEncoding, Nat.add_assoc]

/-- Exactly one full candidate/occurrence copy is added. -/
theorem output_length (input : Input) :
    (outputFinEncoding.encode (prepare input)).length =
      (PositiveMembership.finEncoding.encode (query input)).length +
        (inputFinEncoding.encode input).length := by
  simp [outputFinEncoding, prepare]

theorem query_length_le (input : Input) :
    (PositiveMembership.finEncoding.encode (query input)).length ≤
      (inputFinEncoding.encode input).length := by
  simp [PositiveMembership.finEncoding, query, inputFinEncoding, retainedFinEncoding,
    CountedPositiveSections.finEncoding, CountedPositiveSections.sectionsFinEncoding,
    CountedPositiveSections.domainsFinEncoding, OccurrenceCount.finEncoding]

theorem output_length_le (input : Input) :
    (outputFinEncoding.encode (prepare input)).length ≤
      2 * (inputFinEncoding.encode input).length := by
  rw [output_length]
  have h := query_length_le input
  omega

theorem retained_eq (input : Input) : (prepare input).2 = input := rfl

end PositiveCandidateQueries

namespace PositiveCandidateQueriesMachine

abbrev Endpoint := Sum Bool Bool
abbrev Counted := Sum (Sum (Sum (Sum (Option Bool) Bool) Bool) (Option Bool))
  (Sum (Option Bool) (Option Bool))
abbrev Input := Sum Endpoint (Sum Counted (Option Bool))
abbrev Query := Sum Endpoint (Option Bool)
abbrev Output := Sum Query Input
abbrev State := Option Input × Option Output

inductive Stack
  | input | query | retained | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | emitRetained | emitQuery
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input | _ => Output

/-- Tags select only candidate bits and the ranked occurrence section. -/
def queryCell : Input → Option Output
  | .inl endpoint => some (.inl (.inl endpoint))
  | .inr (.inl (.inl (.inl (.inl (.inl occurrence))))) => some (.inl (.inr occurrence))
  | _ => none

private def observe (_ : State) (cell : Option Input) : State := (cell, none)
private def remember (_ : State) (cell : Option Output) : State := (none, cell)
private def cell (s : State) : Input := s.1.getD (.inr (.inr none))
private def out (s : State) : Output := s.2.getD (.inl (.inr none))

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch (fun s => s.1.isSome)
      (.push .retained (fun s => .inr (cell s)) <|
        .branch (fun s => (queryCell (cell s)).isSome)
          (.push .query (fun s => (queryCell (cell s)).getD (.inl (.inr none))) <|
            .goto fun _ => .scan)
          (.goto fun _ => .scan))
      (.goto fun _ => .emitRetained)
  | .emitRetained => .pop .retained remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitRetained)
      (.goto fun _ => .emitQuery)
  | .emitQuery => .pop .query remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitQuery)
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

private def stackContents (input : List Input) (query retained output : List Output) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .query => query | .retained => retained | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (query retained output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input query retained output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "positive_queries_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe,
    remember, cell, out, queryCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Input) (query retained output : List Output) (state : State) :
    Run (cfg (some .scan) state input query retained output)
      (cfg (some .emitRetained) (none, none) []
        ((input.filterMap queryCell).reverse ++ query)
        ((input.map Sum.inr).reverse ++ retained) output) (input.length + 1) := by
  induction input generalizing query retained state with
  | nil => exact one (by positive_queries_step)
  | cons bit input ih =>
      have step : Run (cfg (some .scan) state (bit :: input) query retained output)
          (cfg (some .scan) (some bit, none) input
            ((queryCell bit).toList ++ query) (.inr bit :: retained) output) 1 := by
        apply one
        rcases bit with endpoint | (((((occurrence | count) | variableCount) | scope) | weight) | row)
          <;> positive_queries_step
      have tail := ih ((queryCell bit).toList ++ query) (.inr bit :: retained) (some bit, none)
      rcases bit with endpoint | (((((occurrence | count) | variableCount) | scope) | weight) | row)
        <;> simpa [queryCell, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq step tail

private def retained_run (query retained output : List Output) (state : State) :
    Run (cfg (some .emitRetained) state [] query retained output)
      (cfg (some .emitQuery) (none, none) [] query [] (retained.reverse ++ output))
      (retained.length + 1) := by
  induction retained generalizing output state with
  | nil => exact one (by positive_queries_step)
  | cons bit retained ih =>
      have h : Run (cfg (some .emitRetained) state [] query (bit :: retained) output)
          (cfg (some .emitRetained) (none, some bit) [] query retained (bit :: output)) 1 :=
        one (by positive_queries_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (bit :: output) (none, some bit))

private def query_run (query output : List Output) (state : State) :
    Run (cfg (some .emitQuery) state [] query [] output)
      (cfg none (none, none) [] [] [] (query.reverse ++ output)) (query.length + 1) := by
  induction query generalizing output state with
  | nil => exact one (by positive_queries_step)
  | cons bit query ih =>
      have h : Run (cfg (some .emitQuery) state [] (bit :: query) [] output)
          (cfg (some .emitQuery) (none, some bit) [] query [] (bit :: output)) 1 :=
        one (by positive_queries_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (bit :: output) (none, some bit))

private def run (input : List Input) :
    Run (cfg (some .scan) (none, none) input [] [] [])
      (cfg none (none, none) [] [] []
        (input.filterMap queryCell ++ input.map Sum.inr)) (3 * input.length + 3) := by
  have scan := scan_run input [] [] [] (none, none)
  have retained := retained_run (input.filterMap queryCell).reverse
    (input.map Sum.inr).reverse [] (none, none)
  have query := query_run (input.filterMap queryCell).reverse (input.map Sum.inr) (none, none)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse,
    List.length_map] at scan retained query
  have composed := seq (seq scan retained) query
  apply evalsToInTimeMono composed
  have h := List.length_filterMap_le queryCell input
  omega

private theorem init_eq (input : List Input) :
    initList computer input = cfg (some .scan) (none, none) input [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none (none, none) [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem routed_encode (input : PositiveCandidateQueries.Input) :
    (PositiveCandidateQueries.inputFinEncoding.encode input).filterMap queryCell ++
      (PositiveCandidateQueries.inputFinEncoding.encode input).map Sum.inr =
      PositiveCandidateQueries.outputFinEncoding.encode (PositiveCandidateQueries.prepare input) := by
  have discard {α β : Type} (bits : List α) :
      bits.filterMap (fun _ => (none : Option β)) = [] := by simp
  simp [PositiveCandidateQueries.outputFinEncoding, PositiveCandidateQueries.prepare, PositiveCandidateQueries.query,
    PositiveCandidateQueries.inputFinEncoding, PositiveCandidateQueries.retainedFinEncoding,
    PositiveMembership.finEncoding, CountedPositiveSections.finEncoding,
    CountedPositiveSections.sectionsFinEncoding, CountedPositiveSections.domainsFinEncoding,
    OccurrenceCount.finEncoding, LeanNPHardness.PairEncoding.finEncoding,
    List.filterMap_map, Function.comp_def, queryCell,
    List.map_append, List.map_map, List.append_assoc, discard]

end PositiveCandidateQueriesMachine

/-- Construct the exact membership query and retain every input field in `3s+3` steps. -/
def positiveCandidateQueries_outputsInTime (input : PositiveCandidateQueries.Input) :
    TM2OutputsInTime PositiveCandidateQueriesMachine.computer (PositiveCandidateQueries.inputFinEncoding.encode input)
      (some (PositiveCandidateQueries.outputFinEncoding.encode (PositiveCandidateQueries.prepare input)))
      (3 * (PositiveCandidateQueries.inputFinEncoding.encode input).length + 3) := by
  rw [TM2OutputsInTime, PositiveCandidateQueriesMachine.init_eq]
  simp only [Option.map_some]
  rw [PositiveCandidateQueriesMachine.halt_eq, ← PositiveCandidateQueriesMachine.routed_encode]
  exact PositiveCandidateQueriesMachine.run _

noncomputable def positiveCandidateQueriesComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveCandidateQueries.Input PositiveCandidateQueries.Output
      PositiveCandidateQueries.inputFinEncoding PositiveCandidateQueries.outputFinEncoding PositiveCandidateQueries.prepare where
  tm := PositiveCandidateQueriesMachine.computer
  inputAlphabet := Equiv.refl PositiveCandidateQueriesMachine.Input
  outputAlphabet := Equiv.refl PositiveCandidateQueriesMachine.Output
  time := 3 * Polynomial.X + 3
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_X] using positiveCandidateQueries_outputsInTime input

#print axioms PositiveCandidateQueries.input_length
#print axioms PositiveCandidateQueries.output_length
#print axioms PositiveCandidateQueries.query_length_le
#print axioms PositiveCandidateQueries.output_length_le
#print axioms PositiveCandidateQueries.retained_eq
#print axioms positiveCandidateQueries_outputsInTime
#print axioms positiveCandidateQueriesComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
