import PhdThesisLean.AllDifferentCSPPositiveRouting
import PhdThesisLean.AllDifferentCSPScopeCooccurrence

/-!
# Compare both coordinates of one ranked occurrence

A finite parser separates the checked `[0,index,rank]` payload and constructs
one singleton membership query for each coordinate. The existing membership
machine uses the upstream query-preserving binary equality kernel. Conjoin
these two exact equalities using the checked finite Boolean machine.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PositiveQueries

abbrev Output := DomainSymbolMembership.Input × DomainSymbolMembership.Input

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding DomainSymbolMembership.finEncoding
    DomainSymbolMembership.finEncoding

def prepare (input : PositivePairQuery.Input) : Output :=
  ((input.1.1, [input.2.1]), (input.1.2, [input.2.2]))

/-- Each coordinate has its own singleton, so an index can never match a rank. -/
theorem equal_eq (input : PositivePairQuery.Input) :
    PositivePairQuery.equal input =
      (DomainSymbolMembership.contains (prepare input).1 &&
        DomainSymbolMembership.contains (prepare input).2) := by
  simp [PositivePairQuery.equal, DomainSymbolMembership.contains, prepare]

/-- The zero-tag delimiter is removed; all four binary words remain. -/
theorem output_length_balance (input : PositivePairQuery.Input) :
    (outputFinEncoding.encode (prepare input)).length + 1 =
      (PositivePairQuery.finEncoding.encode input).length := by
  rw [PositivePairQuery.input_length]
  simp [outputFinEncoding, prepare, DomainSymbolMembership.finEncoding,
    SourceOrderRawFields.finEncoding, SourceOrderRawFields.encode,
    finEncodingNatBool, encodingNatBool]
  omega

end PositiveQueries

namespace PositiveQueryMachine

abbrev Input := Sum (Sum Bool Bool) (Option Bool)
abbrev Query := Sum Bool (Option Bool)
abbrev Output := Sum Query Query
inductive Phase
  | start | tag | index | rank
  deriving DecidableEq, Fintype

abbrev State := Phase × (Option Input × Option Output)
def initialState : State := (.start, none, none)

def advance : Phase → Input → Phase
  | phase, .inl _ => phase
  | phase, .inr (some _) => phase
  | .start, .inr none => .tag
  | .tag, .inr none => .index
  | .index, .inr none => .rank
  | .rank, .inr none => .rank

inductive Stack
  | input | left | right | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | emitRight | emitLeft
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input | _ => Output

def leftCell (phase : Phase) : Input → Option Output
  | .inl (.inl bit) => some (.inl (.inl bit))
  | .inl (.inr _) => none
  | .inr cell => if phase = .index then some (.inl (.inr cell)) else none

def rightCell (phase : Phase) : Input → Option Output
  | .inl (.inl _) => none
  | .inl (.inr bit) => some (.inr (.inl bit))
  | .inr cell => if phase = .rank then some (.inr (.inr cell)) else none

def leftCells (phase : Phase) : List Input → List Output
  | [] => []
  | cell :: rest =>
      (leftCell (advance phase cell) cell).toList ++ leftCells (advance phase cell) rest

def rightCells (phase : Phase) : List Input → List Output
  | [] => []
  | cell :: rest =>
      (rightCell (advance phase cell) cell).toList ++ rightCells (advance phase cell) rest

private def observe (s : State) (cell : Option Input) : State :=
  (cell.elim s.1 (advance s.1), cell, none)
private def remember (_ : State) (cell : Option Output) : State := (.start, none, cell)
private def cell (s : State) : Input := s.2.1.getD (.inr none)
private def out (s : State) : Output := s.2.2.getD (.inr (.inr none))

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch (fun s => s.2.1.isSome)
      (.branch (fun s => (leftCell s.1 (cell s)).isSome)
        (.push .left (fun s => (leftCell s.1 (cell s)).getD (.inl (.inr none))) <|
          .goto fun _ => .scan)
        (.branch (fun s => (rightCell s.1 (cell s)).isSome)
          (.push .right (fun s => (rightCell s.1 (cell s)).getD (.inr (.inr none))) <|
            .goto fun _ => .scan)
          (.goto fun _ => .scan)))
      (.load (fun _ => initialState) <| .goto fun _ => .emitRight)
  | .emitRight => .pop .right remember <| .branch (fun s => s.2.2.isSome)
      (.push .output out <| .goto fun _ => .emitRight)
      (.load (fun _ => initialState) <| .goto fun _ => .emitLeft)
  | .emitLeft => .pop .left remember <| .branch (fun s => s.2.2.isSome)
      (.push .output out <| .goto fun _ => .emitLeft)
      (.load (fun _ => initialState) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := initialState
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input : List Input) (left right output : List Output) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .left => left | .right => right | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (left right output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input left right output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "positive_query_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe,
    remember, cell, out, leftCell, rightCell, advance, initialState, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Input) (left right output : List Output) (state : State) :
    Run (cfg (some .scan) state input left right output)
      (cfg (some .emitRight) initialState []
        ((leftCells state.1 input).reverse ++ left)
        ((rightCells state.1 input).reverse ++ right) output) (input.length + 1) := by
  induction input generalizing left right state with
  | nil => exact one (by positive_query_step)
  | cons bit input ih =>
      let phase := advance state.1 bit
      have h : Run (cfg (some .scan) state (bit :: input) left right output)
          (cfg (some .scan) (phase, some bit, none) input
            ((leftCell phase bit).toList ++ left)
            ((rightCell phase bit).toList ++ right) output) 1 := by
        apply one
        dsimp only [phase]
        rcases state with ⟨currentPhase, old, prior⟩
        cases currentPhase <;> cases bit with
        | inl bit => cases bit <;> positive_query_step
        | inr raw => cases raw <;> positive_query_step
      have reverseOption (x : Option Output) : x.toList.reverse = x.toList := by
        cases x <;> rfl
      simpa [leftCells, rightCells, phase, List.reverse_append, reverseOption,
        List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih _ _ _)

private def right_run (left right output : List Output) (state : State) :
    Run (cfg (some .emitRight) state [] left right output)
      (cfg (some .emitLeft) initialState [] left [] (right.reverse ++ output))
      (right.length + 1) := by
  induction right generalizing output state with
  | nil => exact one (by positive_query_step)
  | cons bit right ih =>
      have h : Run (cfg (some .emitRight) state [] left (bit :: right) output)
          (cfg (some .emitRight) (.start, none, some bit) [] left right (bit :: output)) 1 :=
        one (by positive_query_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih _ _)

private def left_run (left output : List Output) (state : State) :
    Run (cfg (some .emitLeft) state [] left [] output)
      (cfg none initialState [] [] [] (left.reverse ++ output)) (left.length + 1) := by
  induction left generalizing output state with
  | nil => exact one (by positive_query_step)
  | cons bit left ih =>
      have h : Run (cfg (some .emitLeft) state [] (bit :: left) [] output)
          (cfg (some .emitLeft) (.start, none, some bit) [] left [] (bit :: output)) 1 :=
        one (by positive_query_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih _ _)

private theorem routed_length_le (phase : Phase) (input : List Input) :
    (leftCells phase input).length ≤ input.length ∧
      (rightCells phase input).length ≤ input.length := by
  induction input generalizing phase with
  | nil => simp [leftCells, rightCells]
  | cons bit input ih =>
      have h := ih (advance phase bit)
      have hl : (leftCell (advance phase bit) bit).toList.length ≤ 1 := by
        cases leftCell (advance phase bit) bit <;> simp
      have hr : (rightCell (advance phase bit) bit).toList.length ≤ 1 := by
        cases rightCell (advance phase bit) bit <;> simp
      simp only [leftCells, rightCells, List.length_append, List.length_cons]
      omega

/-- Restore both singleton-query wires and clear all work stacks. -/
private def run (input : List Input) :
    Run (cfg (some .scan) initialState input [] [] [])
      (cfg none initialState [] [] []
        (leftCells .start input ++ rightCells .start input)) (3 * input.length + 3) := by
  have scan := scan_run input [] [] [] initialState
  simp only [initialState, List.append_nil] at scan
  have right := right_run (leftCells .start input).reverse
    (rightCells .start input).reverse [] initialState
  have left := left_run (leftCells .start input).reverse
    (rightCells .start input) initialState
  simp only [List.reverse_reverse, List.append_nil] at right left
  have composed := seq (seq scan right) left
  apply evalsToInTimeMono composed
  simp only [List.length_reverse]
  have h := routed_length_le .start input
  omega

private theorem init_eq (input : List Input) :
    initList computer input = cfg (some .scan) initialState input [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none initialState [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem routed_prefix (phase : Phase) (bits : List Bool) (suffix : List Input)
    (inject : Bool → Input)
    (stable : ∀ b, advance phase (inject b) = phase) :
    leftCells phase (bits.map inject ++ suffix) =
        bits.flatMap (fun b => (leftCell phase (inject b)).toList) ++ leftCells phase suffix ∧
    rightCells phase (bits.map inject ++ suffix) =
        bits.flatMap (fun b => (rightCell phase (inject b)).toList) ++ rightCells phase suffix := by
  induction bits with
  | nil => simp
  | cons b bits ih =>
      simp only [List.map_cons, List.cons_append, leftCells, rightCells, stable,
        List.flatMap_cons, ih.1, ih.2, List.append_assoc, and_self]

/-- Delimiters distinguish zero fields and keep the two coordinates separate. -/
private theorem routed_encode (input : PositivePairQuery.Input) :
    leftCells .start (PositivePairQuery.finEncoding.encode input) ++
      rightCells .start (PositivePairQuery.finEncoding.encode input) =
      PositiveQueries.outputFinEncoding.encode (PositiveQueries.prepare input) := by
  have hz : encodeNat 0 = [] := by
    change encodeNum (Num.ofNat' 0) = []
    rw [Num.ofNat'_zero]
    rfl
  have leftPrefix (p : Phase) (bits : List Bool) (rest : List Input) :=
    routed_prefix p bits rest (fun b => .inl (.inl b)) (by intro b; rfl)
  have rightPrefix (p : Phase) (bits : List Bool) (rest : List Input) :=
    routed_prefix p bits rest (fun b => .inl (.inr b)) (by intro b; rfl)
  have rawPrefix (p : Phase) (bits : List Bool) (rest : List Input) :=
    routed_prefix p bits rest (fun b => .inr (some b)) (by intro b; rfl)
  have rawOnly (p : Phase) (bits : List Bool) := rawPrefix p bits []
  simp only [List.append_nil, leftCells, rightCells] at rawOnly
  have flatNil {α β : Type} (xs : List α) : xs.flatMap (fun _ => ([] : List β)) = [] := by
    induction xs <;> simp_all
  have flatSingleton {α β : Type} (xs : List α) (f : α → β) :
      xs.flatMap (fun x => [f x]) = xs.map f := by
    induction xs <;> simp_all
  simp [PositivePairQuery.finEncoding, ScopeExtraction.endpointsFinEncoding,
    PositiveOccurrenceHead.recordFinEncoding, PositiveQueries.outputFinEncoding,
    PositiveQueries.prepare, DomainSymbolMembership.finEncoding,
    SourceOrderRawFields.finEncoding, LeanNPHardness.PairEncoding.finEncoding,
    finEncodingNatBool, encodingNatBool, SourceOrderRawFields.encode, hz,
    List.map_append, List.map_map, Function.comp_def, List.append_assoc,
    (leftPrefix _ _ _).1, (leftPrefix _ _ _).2,
    (rightPrefix _ _ _).1, (rightPrefix _ _ _).2,
    (rawPrefix _ _ _).1, (rawPrefix _ _ _).2,
    (rawOnly _ _).1, (rawOnly _ _).2, flatNil, flatSingleton,
    leftCells, rightCells, leftCell, rightCell, advance]

end PositiveQueryMachine

/-- Prepare both binary equalities in `3s+3` finite-machine steps. -/
def positiveQueries_outputsInTime (input : PositivePairQuery.Input) :
    TM2OutputsInTime PositiveQueryMachine.computer (PositivePairQuery.finEncoding.encode input)
      (some (PositiveQueries.outputFinEncoding.encode (PositiveQueries.prepare input)))
      (3 * (PositivePairQuery.finEncoding.encode input).length + 3) := by
  rw [TM2OutputsInTime, PositiveQueryMachine.init_eq]
  simp only [Option.map_some]
  rw [PositiveQueryMachine.halt_eq, ← PositiveQueryMachine.routed_encode]
  exact PositiveQueryMachine.run _

noncomputable def positiveQueriesComputableInPolyTime :
    @TM2ComputableInPolyTime PositivePairQuery.Input PositiveQueries.Output
      PositivePairQuery.finEncoding PositiveQueries.outputFinEncoding PositiveQueries.prepare where
  tm := PositiveQueryMachine.computer
  inputAlphabet := Equiv.refl PositiveQueryMachine.Input
  outputAlphabet := Equiv.refl PositiveQueryMachine.Output
  time := 3 * Polynomial.X + 3
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_X] using positiveQueries_outputsInTime input

/-- Both coordinate comparisons and their conjunction execute internally,
including parsing, transfers, all binary cells and scratch cleanup. -/
noncomputable def positivePairMatchComputableInPolyTime :
    @TM2ComputableInPolyTime PositivePairQuery.Input Bool
      PositivePairQuery.finEncoding finEncodingBoolBool PositivePairQuery.equal := by
  let membership := DomainSymbolMembership.finEncoding
  let first := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    membership finEncodingBoolBool membership
    DomainSymbolMembership.contains domainSymbolMembershipComputableInPolyTime
  let second := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    finEncodingBoolBool membership finEncodingBoolBool
    DomainSymbolMembership.contains domainSymbolMembershipComputableInPolyTime
  let prepared := compositionComputableInPolyTime _ _ _ _ _
    positiveQueriesComputableInPolyTime first
  let tested := compositionComputableInPolyTime _ _ _ _ _ prepared second
  let composed := compositionComputableInPolyTime _ _ _ _ _ tested
    ScopeConjunctionMachine.computableInPolyTime
  exact { composed with
    outputsFun := fun input => by
      simpa only [Function.comp_def, PositiveQueries.equal_eq]
        using composed.outputsFun input }

example : PositivePairQuery.equal ((0, 0), (0, 0)) = true := by decide
example : PositivePairQuery.equal ((0, 1), (1, 0)) = false := by decide
example : PositivePairQuery.equal ((7, 1000000), (7, 1000000)) = true := by decide
example : PositivePairQuery.equal ((7, 1000000), (7, 1000001)) = false := by decide

#print axioms PositiveQueries.equal_eq
#print axioms PositiveQueries.output_length_balance
#print axioms positiveQueries_outputsInTime
#print axioms positiveQueriesComputableInPolyTime
#print axioms positivePairMatchComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
