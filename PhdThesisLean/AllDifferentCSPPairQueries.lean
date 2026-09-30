import PhdThesisLean.AllDifferentCSPScopeInitialization

/-!
# Construct candidate-pair queries while retaining the complete scan state

Copy the binary endpoints for strict comparison and for the complete counted
scope query. Retain the original endpoints, ranked domain occurrences, unary
variable bound, full scopes and accumulated edge rows. The finite routing pass
charges every copy, restores source order and clears every scratch stack.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PairQueries

/-- Current endpoints, immutable bounded sections, and previously emitted edges. -/
abbrev Input := (ℕ × ℕ) × (BoundedRelabelledSections.Value × List (ℕ × ℕ))
abbrev Queries := (ℕ × ℕ) × ScopeRouting.Remaining
abbrev Output := Queries × Input

def retainedFinEncoding : FinEncoding (BoundedRelabelledSections.Value × List (ℕ × ℕ)) :=
  LeanNPHardness.PairEncoding.finEncoding BoundedRelabelledSections.finEncoding
    NegativeRows.inputFinEncoding

def inputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding ScopeExtraction.endpointsFinEncoding retainedFinEncoding

def queriesFinEncoding : FinEncoding Queries :=
  LeanNPHardness.PairEncoding.finEncoding DomainSymbolComparison.finEncoding
    ScopeExtraction.remainingFinEncoding

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding queriesFinEncoding inputFinEncoding

def queries (input : Input) : Queries := (input.1, (input.1, input.2.1.2))

def prepare (input : Input) : Output := (queries input, input)

/-- Every endpoint bit, domain/scoped field, unary mark and emitted edge is charged. -/
theorem input_length (input : Input) :
    (inputFinEncoding.encode input).length =
      (ScopeExtraction.endpointsFinEncoding.encode input.1).length +
        (BoundedRelabelledSections.finEncoding.encode input.2.1).length +
        (NegativeRows.inputEncode input.2.2).length := by
  simp [inputFinEncoding, retainedFinEncoding, NegativeRows.inputFinEncoding, Nat.add_assoc]

/-- Preparation adds two endpoint copies and one complete scope-section copy. -/
theorem output_length (input : Input) :
    (outputFinEncoding.encode (prepare input)).length =
      (inputFinEncoding.encode input).length +
        2 * (ScopeExtraction.endpointsFinEncoding.encode input.1).length +
        (ScopeFieldSection.rowPayloadFinEncoding.encode input.2.1.2).length := by
  simp [outputFinEncoding, prepare, queriesFinEncoding, queries,
    ScopeExtraction.remainingFinEncoding, ScopeExtraction.endpointsFinEncoding,
    DomainSymbolComparison.finEncoding]
  omega

theorem output_length_le (input : Input) :
    (outputFinEncoding.encode (prepare input)).length ≤
      3 * (inputFinEncoding.encode input).length := by
  have hs : (ScopeFieldSection.rowPayloadFinEncoding.encode input.2.1.2).length ≤
      (BoundedRelabelledSections.finEncoding.encode input.2.1).length := by
    simp [BoundedRelabelledSections.finEncoding]
  rw [output_length, input_length]
  omega

theorem retained_eq (input : Input) : (prepare input).2 = input := rfl

end PairQueries

namespace PairQueriesMachine

abbrev Endpoint := Sum Bool Bool
abbrev Query := Sum Endpoint (Option Bool)
abbrev Bounded := Sum (Sum (Option Bool) Bool) (Option Bool)
abbrev Input := Sum Endpoint (Sum Bounded (Option Bool))
abbrev Output := Sum (Sum Endpoint Query) Input
abbrev State := Option Input × Option Output

inductive Stack
  | input | comparison | adjacency | retained | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | emitRetained | emitAdjacency | emitComparison
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input | _ => Output

def comparisonCell : Input → Option Output
  | .inl endpoint => some (.inl (.inl endpoint))
  | _ => none

def adjacencyCell : Input → Option Output
  | .inl endpoint => some (.inl (.inr (.inl endpoint)))
  | .inr (.inl (.inr scope)) => some (.inl (.inr (.inr scope)))
  | _ => none

private def observe (_ : State) (cell : Option Input) : State := (cell, none)
private def remember (_ : State) (cell : Option Output) : State := (none, cell)
private def cell (s : State) : Input := s.1.getD (.inr (.inr none))
private def out (s : State) : Output := s.2.getD (.inr (.inr (.inr none)))

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch (fun s => s.1.isSome)
      (.push .retained (fun s => .inr (cell s)) <|
        .branch (fun s => (comparisonCell (cell s)).isSome)
          (.push .comparison (fun s => (comparisonCell (cell s)).getD (.inl (.inl (.inl false)))) <|
            .push .adjacency (fun s => (adjacencyCell (cell s)).getD (.inl (.inr (.inr none)))) <|
              .goto fun _ => .scan)
          (.branch (fun s => (adjacencyCell (cell s)).isSome)
            (.push .adjacency (fun s => (adjacencyCell (cell s)).getD (.inl (.inr (.inr none)))) <|
              .goto fun _ => .scan)
            (.goto fun _ => .scan)))
      (.goto fun _ => .emitRetained)
  | .emitRetained => .pop .retained remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitRetained)
      (.goto fun _ => .emitAdjacency)
  | .emitAdjacency => .pop .adjacency remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitAdjacency)
      (.goto fun _ => .emitComparison)
  | .emitComparison => .pop .comparison remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitComparison)
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

private def stackContents (input : List Input) (comparison adjacency retained output : List Output) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .comparison => comparison | .adjacency => adjacency
  | .retained => retained | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (comparison adjacency retained output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input comparison adjacency retained output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "pair_queries_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe,
    remember, cell, out, comparisonCell, adjacencyCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Input) (comparison adjacency retained output : List Output)
    (state : State) :
    Run (cfg (some .scan) state input comparison adjacency retained output)
      (cfg (some .emitRetained) (none, none) []
        ((input.filterMap comparisonCell).reverse ++ comparison)
        ((input.filterMap adjacencyCell).reverse ++ adjacency)
        ((input.map Sum.inr).reverse ++ retained) output) (input.length + 1) := by
  induction input generalizing comparison adjacency retained state with
  | nil => exact one (by pair_queries_step)
  | cons bit input ih =>
      have step : Run (cfg (some .scan) state (bit :: input) comparison adjacency retained output)
          (cfg (some .scan) (some bit, none) input
            ((comparisonCell bit).toList ++ comparison)
            ((adjacencyCell bit).toList ++ adjacency) (.inr bit :: retained) output) 1 := by
        apply one
        rcases bit with endpoint | (domains | edge)
        · pair_queries_step
        · rcases domains with domains | scope <;> pair_queries_step
        · pair_queries_step
      have tail := ih ((comparisonCell bit).toList ++ comparison)
        ((adjacencyCell bit).toList ++ adjacency) (.inr bit :: retained) (some bit, none)
      rcases bit with endpoint | (domains | edge)
      · simpa [comparisonCell, adjacencyCell, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq step tail
      · rcases domains with domains | scope <;>
          simpa [comparisonCell, adjacencyCell, List.reverse_cons, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq step tail
      · simpa [comparisonCell, adjacencyCell, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq step tail

private def retained_run (comparison adjacency retained output : List Output) (state : State) :
    Run (cfg (some .emitRetained) state [] comparison adjacency retained output)
      (cfg (some .emitAdjacency) (none, none) [] comparison adjacency [] (retained.reverse ++ output))
      (retained.length + 1) := by
  induction retained generalizing output state with
  | nil => exact one (by pair_queries_step)
  | cons bit retained ih =>
      have h : Run (cfg (some .emitRetained) state [] comparison adjacency (bit :: retained) output)
          (cfg (some .emitRetained) (none, some bit) [] comparison adjacency retained (bit :: output)) 1 :=
        one (by pair_queries_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (bit :: output) (none, some bit))

private def adjacency_run (comparison adjacency output : List Output) (state : State) :
    Run (cfg (some .emitAdjacency) state [] comparison adjacency [] output)
      (cfg (some .emitComparison) (none, none) [] comparison [] [] (adjacency.reverse ++ output))
      (adjacency.length + 1) := by
  induction adjacency generalizing output state with
  | nil => exact one (by pair_queries_step)
  | cons bit adjacency ih =>
      have h : Run (cfg (some .emitAdjacency) state [] comparison (bit :: adjacency) [] output)
          (cfg (some .emitAdjacency) (none, some bit) [] comparison adjacency [] (bit :: output)) 1 :=
        one (by pair_queries_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (bit :: output) (none, some bit))

private def comparison_run (comparison output : List Output) (state : State) :
    Run (cfg (some .emitComparison) state [] comparison [] [] output)
      (cfg none (none, none) [] [] [] [] (comparison.reverse ++ output))
      (comparison.length + 1) := by
  induction comparison generalizing output state with
  | nil => exact one (by pair_queries_step)
  | cons bit comparison ih =>
      have h : Run (cfg (some .emitComparison) state [] (bit :: comparison) [] [] output)
          (cfg (some .emitComparison) (none, some bit) [] comparison [] [] (bit :: output)) 1 :=
        one (by pair_queries_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (bit :: output) (none, some bit))

private def run (input : List Input) :
    Run (cfg (some .scan) (none, none) input [] [] [] [])
      (cfg none (none, none) [] [] [] []
        (input.filterMap comparisonCell ++ input.filterMap adjacencyCell ++ input.map Sum.inr))
      (4 * input.length + 4) := by
  have scan := scan_run input [] [] [] [] (none, none)
  have retained := retained_run (input.filterMap comparisonCell).reverse
    (input.filterMap adjacencyCell).reverse (input.map Sum.inr).reverse [] (none, none)
  have adjacency := adjacency_run (input.filterMap comparisonCell).reverse
    (input.filterMap adjacencyCell).reverse (input.map Sum.inr) (none, none)
  have comparison := comparison_run (input.filterMap comparisonCell).reverse
    (input.filterMap adjacencyCell ++ input.map Sum.inr) (none, none)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse,
    List.length_map] at scan retained adjacency comparison
  have composed := seq (seq (seq scan retained) adjacency) comparison
  apply evalsToInTimeMono (by simpa only [List.append_assoc] using composed)
  have hc := List.length_filterMap_le comparisonCell input
  have ha := List.length_filterMap_le adjacencyCell input
  omega

private theorem init_eq (input : List Input) :
    initList computer input = cfg (some .scan) (none, none) input [] [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none (none, none) [] [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem routed_encode (input : PairQueries.Input) :
    (PairQueries.inputFinEncoding.encode input).filterMap comparisonCell ++
      (PairQueries.inputFinEncoding.encode input).filterMap adjacencyCell ++
      (PairQueries.inputFinEncoding.encode input).map Sum.inr =
      PairQueries.outputFinEncoding.encode (PairQueries.prepare input) := by
  have discard {α β : Type} (bits : List α) :
      bits.filterMap (fun _ => (none : Option β)) = [] := by simp
  simp [PairQueries.outputFinEncoding, PairQueries.prepare, PairQueries.queriesFinEncoding,
    PairQueries.queries, PairQueries.inputFinEncoding, PairQueries.retainedFinEncoding,
    ScopeExtraction.endpointsFinEncoding, ScopeExtraction.remainingFinEncoding,
    DomainSymbolComparison.finEncoding, BoundedRelabelledSections.finEncoding,
    LeanNPHardness.PairEncoding.finEncoding, List.filterMap_map, Function.comp_def,
    comparisonCell, adjacencyCell, List.map_append, List.map_map, List.append_assoc, discard]

end PairQueriesMachine

/-- Construct both candidate tests and retain the full state in `4s+4` steps. -/
def pairQueries_outputsInTime (input : PairQueries.Input) :
    TM2OutputsInTime PairQueriesMachine.computer (PairQueries.inputFinEncoding.encode input)
      (some (PairQueries.outputFinEncoding.encode (PairQueries.prepare input)))
      (4 * (PairQueries.inputFinEncoding.encode input).length + 4) := by
  rw [TM2OutputsInTime, PairQueriesMachine.init_eq]
  simp only [Option.map_some]
  rw [PairQueriesMachine.halt_eq, ← PairQueriesMachine.routed_encode]
  exact PairQueriesMachine.run _

noncomputable def pairQueriesComputableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Input PairQueries.Output
      PairQueries.inputFinEncoding PairQueries.outputFinEncoding PairQueries.prepare where
  tm := PairQueriesMachine.computer
  inputAlphabet := Equiv.refl PairQueriesMachine.Input
  outputAlphabet := Equiv.refl PairQueriesMachine.Output
  time := 4 * Polynomial.X + 4
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_X] using pairQueries_outputsInTime input

#print axioms PairQueries.input_length
#print axioms PairQueries.output_length
#print axioms PairQueries.output_length_le
#print axioms PairQueries.retained_eq
#print axioms pairQueries_outputsInTime
#print axioms pairQueriesComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
