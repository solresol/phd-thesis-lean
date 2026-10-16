import PhdThesisLean.AllDifferentCSPPositiveBound

/-!
# Finite bound tests for the rectangular positive scan

Compare the candidate index with the variable count for exhaustion, and the
rank with the occurrence count for continuation. Both bounds are constructed
from their retained unary headers; all other state survives unchanged.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PositiveControl

abbrev Query := DomainSymbolComparison.Input × PositiveCandidateQueries.Input

def queryFinEncoding : FinEncoding Query :=
  LeanNPHardness.PairEncoding.finEncoding DomainSymbolComparison.finEncoding
    PositiveCandidateQueries.inputFinEncoding

def route (inner : Bool) (input : PositiveBound.Output) : Query :=
  ((if inner then input.2.1.2 else input.2.1.1, input.1), input.2)

def active (state : PositiveCandidateQueries.Input) : Bool := decide (state.1.1 < state.2.1.1.1.2)
def continues (state : PositiveCandidateQueries.Input) : Bool := decide (state.1.2 < state.2.1.1.1.1.2)
def evaluate (inner : Bool) (state : PositiveCandidateQueries.Input) : PositiveCandidateTest.Output :=
  (if inner then continues state else active state, state)

theorem retained_eq (inner : Bool) (state : PositiveCandidateQueries.Input) :
    (evaluate inner state).2 = state := rfl

theorem output_length (inner : Bool) (state : PositiveCandidateQueries.Input) :
    (PositiveCandidateTest.outputFinEncoding.encode (evaluate inner state)).length =
      (PositiveCandidateQueries.inputFinEncoding.encode state).length + 1 := by
  simp [PositiveCandidateTest.outputFinEncoding, evaluate, finEncodingBoolBool, encodeBool, Nat.add_comm]

/-- The two computed decisions select precisely the established rectangular recurrence. -/
theorem advance_eq (state : PositiveCandidateQueries.Input) :
    PositiveAdvance.advance state =
      if (evaluate false state).1 then
        if (evaluate true state).1 then PositiveCounters.inner (PositiveCandidateFilter.filter state)
        else PositiveCounters.outer (PositiveCandidateFilter.filter state)
      else state := by
  simp [evaluate, active, continues, PositiveAdvance.advance, PositiveCounters.step_eq]

/-- Exactly the rectangular number of active cycles, including empty sections. -/
theorem run_active_iff (value : CountedPositiveSections.Value) (k : ℕ) :
    (evaluate false (PositiveAdvance.run value k)).1 = true ↔ k < PositiveAdvance.gridSize value := by
  simpa [evaluate, active, PositiveAdvance.run_retained] using PositiveAdvance.run_active_iff value k

theorem exhausted (value : CountedPositiveSections.Value) (rows : List PositiveBlock.Value) :
    evaluate false ((value.1.1.2, 0), value, rows) =
      (false, (value.1.1.2, 0), value, rows) := by
  simp [evaluate, active]

example : evaluate false ((0, 0), (((([], 0), 0), []), ([], 0)), []) =
    (false, (0, 0), (((([], 0), 0), []), ([], 0)), []) := rfl
example : evaluate false ((0, 0), (((([], 0), 1), []), ([], 0)), []) =
    (true, (0, 0), (((([], 0), 1), []), ([], 0)), []) := rfl
example : evaluate true ((0, 0), (((([], 0), 1), []), ([], 0)), []) =
    (false, (0, 0), (((([], 0), 1), []), ([], 0)), []) := rfl
example : evaluate true ((2, 7), (((([], 8), 3), [[]]), ([], 1000000)), [((0, 1), 1000000)]) =
    (true, (2, 7), (((([], 8), 3), [[]]), ([], 1000000)), [((0, 1), 1000000)]) := rfl
example : evaluate true ((2, 8), (((([], 8), 3), [[]]), ([], 0)), []) =
    (false, (2, 8), (((([], 8), 3), [[]]), ([], 0)), []) := rfl
example : evaluate true ((0, 1000000), (((([], 2), 3), []), ([], 0)), []) =
    (false, (0, 1000000), (((([], 2), 3), []), ([], 0)), []) := rfl

end PositiveControl

namespace PositiveControlRoutingMachine

abbrev Input := Sum (Option Bool) PositiveCandidateQueriesMachine.Input
abbrev Output := Sum (Sum Bool Bool) PositiveCandidateQueriesMachine.Input
abbrev State := Option Input × Option Output

inductive Stack
  | input | bound | reversed | query | retained | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | restore | emitRetained | emitBound | emitQuery
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input | _ => Output

def boundCell : Input → Option Output
  | .inl (some bit) => some (.inl (.inr bit))
  | _ => none

def queryCell (inner : Bool) : Input → Option Output
  | .inr (.inl (.inl bit)) => if inner then none else some (.inl (.inl bit))
  | .inr (.inl (.inr bit)) => if inner then some (.inl (.inl bit)) else none
  | _ => none

def retainedCell : Input → Option Output
  | .inr cell => some (.inr cell)
  | _ => none

private def observe (_ : State) (cell : Option Input) : State := (cell, none)
private def remember (_ : State) (cell : Option Output) : State := (none, cell)
private def cell (s : State) : Input := s.1.getD (.inl none)
private def out (s : State) : Output := s.2.getD (.inl (.inl false))

variable (inner : Bool)

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch (fun s => s.1.isSome)
      (.branch (fun s => (retainedCell (cell s)).isSome)
        (.push .retained (fun s => (retainedCell (cell s)).getD (.inl (.inl false))) <|
          .branch (fun s => (queryCell inner (cell s)).isSome)
            (.push .query (fun s => (queryCell inner (cell s)).getD (.inl (.inl false))) <|
              .goto fun _ => .scan)
            (.goto fun _ => .scan))
        (.branch (fun s => (boundCell (cell s)).isSome)
          (.push .bound (fun s => (boundCell (cell s)).getD (.inl (.inr false))) <|
            .goto fun _ => .scan)
          (.goto fun _ => .scan)))
      (.goto fun _ => .restore)
  | .restore => .pop .bound remember <| .branch (fun s => s.2.isSome)
      (.push .reversed out <| .goto fun _ => .restore)
      (.goto fun _ => .emitRetained)
  | .emitRetained => .pop .retained remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitRetained)
      (.goto fun _ => .emitBound)
  | .emitBound => .pop .reversed remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitBound)
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
  m := program inner

private def stackContents (input : List Input) (bound reversed query retained output : List Output) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .bound => bound | .reversed => reversed
  | .query => query | .retained => retained | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (bound reversed query retained output : List Output) : (computer inner).Cfg :=
  ⟨label, state, stackContents input bound reversed query retained output⟩

private abbrev Run (a b : (computer inner).Cfg) (time : ℕ) :=
  EvalsToInTime (computer inner).step a (some b) time
private def one {a b : (computer inner).Cfg} (h : (computer inner).step a = some b) : Run inner a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using! h, steps_le_m := le_rfl }
private def seq {a b c : (computer inner).Cfg} {m n : ℕ}
    (h : Run inner a b m) (h' : Run inner b c n) : Run inner a c (m + n) := by
  simpa [Nat.add_comm] using! EvalsToInTime.trans (computer inner).step m n a b (some c) h h'

local macro "positive_control_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe,
    remember, cell, out, boundCell, queryCell, retainedCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Input) (bound query retained output : List Output) (state : State) :
    Run inner (cfg inner (some .scan) state input bound [] query retained output)
      (cfg inner (some .restore) (none, none) []
        ((input.filterMap boundCell).reverse ++ bound) []
        ((input.filterMap (queryCell inner)).reverse ++ query)
        ((input.filterMap retainedCell).reverse ++ retained) output) (input.length + 1) := by
  induction input generalizing bound query retained state with
  | nil => exact one inner (by positive_control_step)
  | cons bit input ih =>
      have step : Run inner (cfg inner (some .scan) state (bit :: input) bound [] query retained output)
          (cfg inner (some .scan) (some bit, none) input
            ((boundCell bit).toList ++ bound) [] ((queryCell inner bit).toList ++ query)
            ((retainedCell bit).toList ++ retained) output) 1 := by
        apply one inner
        rcases bit with (_ | b) | ((b | b) | rest) <;> cases inner <;> positive_control_step
      have tail := ih ((boundCell bit).toList ++ bound) ((queryCell inner bit).toList ++ query)
        ((retainedCell bit).toList ++ retained) (some bit, none)
      rcases bit with (_ | b) | ((b | b) | rest) <;> cases inner <;>
        simpa [boundCell, queryCell, retainedCell, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq _ step tail

private def restore_run (bound reversed query retained output : List Output) (state : State) :
    Run inner (cfg inner (some .restore) state [] bound reversed query retained output)
      (cfg inner (some .emitRetained) (none, none) [] []
        (bound.reverse ++ reversed) query retained output) (bound.length + 1) := by
  induction bound generalizing reversed state with
  | nil => exact one inner (by positive_control_step)
  | cons bit bound ih =>
      have h : Run inner (cfg inner (some .restore) state [] (bit :: bound) reversed query retained output)
          (cfg inner (some .restore) (none, some bit) [] bound (bit :: reversed) query retained output) 1 :=
        one inner (by positive_control_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq inner h (ih (bit :: reversed) (none, some bit))

private def retained_run (reversed query retained output : List Output) (state : State) :
    Run inner (cfg inner (some .emitRetained) state [] [] reversed query retained output)
      (cfg inner (some .emitBound) (none, none) [] [] reversed query [] (retained.reverse ++ output)) (retained.length + 1) := by
  induction retained generalizing output state with
  | nil => exact one inner (by positive_control_step)
  | cons bit retained ih =>
      have h : Run inner (cfg inner (some .emitRetained) state [] [] reversed query (bit :: retained) output)
          (cfg inner (some .emitRetained) (none, some bit) [] [] reversed query retained (bit :: output)) 1 :=
        one inner (by positive_control_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq inner h (ih (bit :: output) (none, some bit))

private def bound_run (reversed query output : List Output) (state : State) :
    Run inner (cfg inner (some .emitBound) state [] [] reversed query [] output)
      (cfg inner (some .emitQuery) (none, none) [] [] [] query [] (reversed.reverse ++ output)) (reversed.length + 1) := by
  induction reversed generalizing output state with
  | nil => exact one inner (by positive_control_step)
  | cons bit reversed ih =>
      have h : Run inner (cfg inner (some .emitBound) state [] [] (bit :: reversed) query [] output)
          (cfg inner (some .emitBound) (none, some bit) [] [] reversed query [] (bit :: output)) 1 :=
        one inner (by positive_control_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq inner h (ih (bit :: output) (none, some bit))

private def query_run (query output : List Output) (state : State) :
    Run inner (cfg inner (some .emitQuery) state [] [] [] query [] output)
      (cfg inner (none) (none, none) [] [] [] [] [] (query.reverse ++ output)) (query.length + 1) := by
  induction query generalizing output state with
  | nil => exact one inner (by positive_control_step)
  | cons bit query ih =>
      have h : Run inner (cfg inner (some .emitQuery) state [] [] [] (bit :: query) [] output)
          (cfg inner (some .emitQuery) (none, some bit) [] [] [] query [] (bit :: output)) 1 :=
        one inner (by positive_control_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq inner h (ih (bit :: output) (none, some bit))

private def run (input : List Input) :
    Run inner (cfg inner (some .scan) (none, none) input [] [] [] [] [])
      (cfg inner none (none, none) [] [] [] [] []
        (input.filterMap (queryCell inner) ++ (input.filterMap boundCell).reverse ++
          input.filterMap retainedCell)) (5 * input.length + 5) := by
  have hs := scan_run inner input [] [] [] [] (none, none)
  have hr := restore_run inner (input.filterMap boundCell).reverse []
    (input.filterMap (queryCell inner)).reverse (input.filterMap retainedCell).reverse [] (none, none)
  have ht := retained_run inner (input.filterMap boundCell)
    (input.filterMap (queryCell inner)).reverse (input.filterMap retainedCell).reverse [] (none, none)
  have hb := bound_run inner (input.filterMap boundCell)
    (input.filterMap (queryCell inner)).reverse (input.filterMap retainedCell) (none, none)
  have hq := query_run inner (input.filterMap (queryCell inner)).reverse
    ((input.filterMap boundCell).reverse ++ input.filterMap retainedCell) (none, none)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hs hr ht hb hq
  apply evalsToInTimeMono (by
    simpa only [List.append_assoc] using seq inner (seq inner (seq inner (seq inner hs hr) ht) hb) hq)
  have b := List.length_filterMap_le boundCell input
  have q := List.length_filterMap_le (queryCell inner) input
  have r := List.length_filterMap_le retainedCell input
  omega

private theorem init_eq (input : List Input) :
    initList (computer inner) input = cfg inner (some .scan) (none, none) input [] [] [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList (computer inner) output = cfg inner none (none, none) [] [] [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem routed_encode (input : PositiveBound.Output) :
    (PositiveBound.binaryFinEncoding.encode input).filterMap (queryCell inner) ++
      ((PositiveBound.binaryFinEncoding.encode input).filterMap boundCell).reverse ++
      (PositiveBound.binaryFinEncoding.encode input).filterMap retainedCell =
      PositiveControl.queryFinEncoding.encode (PositiveControl.route inner input) := by
  have discard {α β : Type} (bits : List α) :
      bits.filterMap (fun _ => (none : Option β)) = [] := by simp
  cases inner <;>
    simp [PositiveBound.binaryFinEncoding, UnaryBoundEncoding.outputFinEncoding,
      PositiveControl.queryFinEncoding, PositiveControl.route, PositiveCandidateQueries.inputFinEncoding,
      ScopeExtraction.endpointsFinEncoding, DomainSymbolComparison.finEncoding,
      LeanNPHardness.PairEncoding.finEncoding, RawNatList.segment,
      finEncodingNatBool, List.filterMap_map, Function.comp_def,
      boundCell, queryCell, retainedCell, List.map_append, List.map_map,
      List.map_reverse, List.append_assoc, discard]

end PositiveControlRoutingMachine

/-- Route one endpoint and the internally computed bound into canonical binary
comparison order, retaining all original state and clearing every work stack. -/
def positiveControlRoute_outputsInTime (inner : Bool) (input : PositiveBound.Output) :
    TM2OutputsInTime (PositiveControlRoutingMachine.computer inner)
      (PositiveBound.binaryFinEncoding.encode input)
      (some (PositiveControl.queryFinEncoding.encode (PositiveControl.route inner input)))
      (5 * (PositiveBound.binaryFinEncoding.encode input).length + 5) := by
  rw [TM2OutputsInTime, PositiveControlRoutingMachine.init_eq]
  simp only [Option.map_some]
  rw [PositiveControlRoutingMachine.halt_eq, ← PositiveControlRoutingMachine.routed_encode]
  exact PositiveControlRoutingMachine.run _ _

noncomputable def positiveControlRouteComputableInPolyTime (inner : Bool) :
    @TM2ComputableInPolyTime PositiveBound.Output PositiveControl.Query
      PositiveBound.binaryFinEncoding PositiveControl.queryFinEncoding (PositiveControl.route inner) where
  tm := PositiveControlRoutingMachine.computer inner
  inputAlphabet := Equiv.refl PositiveControlRoutingMachine.Input
  outputAlphabet := Equiv.refl PositiveControlRoutingMachine.Output
  time := 5 * Polynomial.X + 5
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_X] using positiveControlRoute_outputsInTime inner input

/-- Determine exhaustion from the original wire, computing the bound internally. -/
noncomputable def positiveActiveComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveCandidateQueries.Input PositiveCandidateTest.Output
      PositiveCandidateQueries.inputFinEncoding PositiveCandidateTest.outputFinEncoding (PositiveControl.evaluate false) := by
  let routed := compositionComputableInPolyTime _ _ _ _ _ (positiveBoundComputableInPolyTime false)
    (positiveControlRouteComputableInPolyTime false)
  let compare := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    DomainSymbolComparison.finEncoding finEncodingBoolBool PositiveCandidateQueries.inputFinEncoding
    DomainSymbolComparison.less domainSymbolLessComputableInPolyTime
  exact compositionComputableInPolyTime _ _ _ _ _ routed compare

/-- Determine whether to increment the inner endpoint: copying, bound construction
and strict comparison are all inside the checked composition. -/
noncomputable def positiveContinuesComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveCandidateQueries.Input PositiveCandidateTest.Output
      PositiveCandidateQueries.inputFinEncoding PositiveCandidateTest.outputFinEncoding (PositiveControl.evaluate true) := by
  let routed := compositionComputableInPolyTime _ _ _ _ _ (positiveBoundComputableInPolyTime true)
    (positiveControlRouteComputableInPolyTime true)
  let compare := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    DomainSymbolComparison.finEncoding finEncodingBoolBool PositiveCandidateQueries.inputFinEncoding
    DomainSymbolComparison.less domainSymbolLessComputableInPolyTime
  exact compositionComputableInPolyTime _ _ _ _ _ routed compare

/-- Full exhaustion tests have a uniform polynomial bound in the original
retained-section length, without an externally supplied reached-state invariant. -/
theorem positiveActive_iterate_steps_le (value : CountedPositiveSections.Value) (k : ℕ) :
    (positiveActiveComputableInPolyTime.outputsFun (PositiveAdvance.run value k)).steps ≤
      positiveActiveComputableInPolyTime.time.eval
        (16 * ((CountedPositiveSections.finEncoding.encode value).length + 1) ^ 3) :=
  (positiveActiveComputableInPolyTime.outputsFun _).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
      (PositiveAdvance.run_length_le_cubic value k))

/-- The continuation test includes the selected bound construction, comparison,
query copying, transfers and cleanup at every reached state. -/
theorem positiveContinues_iterate_steps_le (value : CountedPositiveSections.Value) (k : ℕ) :
    (positiveContinuesComputableInPolyTime.outputsFun (PositiveAdvance.run value k)).steps ≤
      positiveContinuesComputableInPolyTime.time.eval
        (16 * ((CountedPositiveSections.finEncoding.encode value).length + 1) ^ 3) :=
  (positiveContinuesComputableInPolyTime.outputsFun _).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
      (PositiveAdvance.run_length_le_cubic value k))

#print axioms PositiveControl.retained_eq
#print axioms PositiveControl.output_length
#print axioms PositiveControl.advance_eq
#print axioms PositiveControl.run_active_iff
#print axioms PositiveControl.exhausted
#print axioms positiveControlRoute_outputsInTime
#print axioms positiveActiveComputableInPolyTime
#print axioms positiveContinuesComputableInPolyTime
#print axioms positiveActive_iterate_steps_le
#print axioms positiveContinues_iterate_steps_le

end PhdThesisLean.AllDifferentCSPMachine
