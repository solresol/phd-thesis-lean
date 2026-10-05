import PhdThesisLean.AllDifferentCSPPairAdvance

/-!
# Conditionally append the tested edge while retaining the scan state

The finite machine consumes the computed answer bit and appends the exact
counted `[2,i,j]` edge row only when accepted. Endpoint words, ranked domains,
unary variable bound, scopes and old edges survive in source order. Counter
advancement and selection are composed in `AllDifferentCSPPairDispatch`;
repeated dispatch remains a separate obligation.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PairEmit

def emit (tested : PairTest.Output) : PairQueries.Input :=
  (tested.2.1, tested.2.2.1,
    if tested.1 then tested.2.2.2 ++ [tested.2.1] else tested.2.2.2)

theorem retained_eq (tested : PairTest.Output) :
    (emit tested).1 = tested.2.1 ∧ (emit tested).2.1 = tested.2.2.1 := ⟨rfl, rfl⟩

/-- Emission supplies precisely the retained sections and rows of the abstract step. -/
theorem afterTest_eq (tested : PairTest.Output) :
    PairAdvance.afterTest tested =
      (PairAdvance.nextPair tested.2.2.1.1.2 (emit tested).1, (emit tested).2) := rfl

theorem edge_encode_append (edges more : List (ℕ × ℕ)) :
    NegativeRows.inputEncode (edges ++ more) =
      NegativeRows.inputEncode edges ++ NegativeRows.inputEncode more := by
  simp [NegativeRows.inputEncode, NegativeRows.pairRows, DomainFieldSection.rowPayloadEncode,
    LeanNPHardness.CountedNatRows.rowFields, SourceOrderRawFields.encode, List.flatMap_append]

theorem output_length (tested : PairTest.Output) :
    (PairQueries.inputFinEncoding.encode (emit tested)).length =
      (PairQueries.inputFinEncoding.encode tested.2).length +
        if tested.1 then 5 + (encodeNat tested.2.1.1).length +
          (encodeNat tested.2.1.2).length else 0 := by
  rw [PairQueries.input_length, PairQueries.input_length]
  cases h : tested.1 <;>
    simp [emit, h, edge_encode_append, NegativeRows.inputEncode_cons_length, Nat.add_assoc]

/-- The removed answer and all five row framing cells are included in the bound. -/
theorem output_length_le (tested : PairTest.Output) :
    (PairQueries.inputFinEncoding.encode (emit tested)).length ≤
      2 * (PairTest.outputFinEncoding.encode tested).length + 5 := by
  have hi := PairQueries.input_length tested.2
  simp only [ScopeExtraction.endpointsFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length,
    finEncodingNatBool, encodingNatBool] at hi
  have hs : (PairTest.outputFinEncoding.encode tested).length =
      (PairQueries.inputFinEncoding.encode tested.2).length + 1 := by
    simp [PairTest.outputFinEncoding, finEncodingBoolBool, encodeBool, Nat.add_comm]
  rw [output_length]
  split <;> omega

example : emit (false, (0, 0), (([], 0), []), []) =
    ((0, 0), (([], 0), []), []) := rfl
example : emit (true, (0, 8), (([], 9), [[], [0, 8]]), [(0, 1)]) =
    ((0, 8), (([], 9), [[], [0, 8]]), [(0, 1), (0, 8)]) := rfl

end PairEmit

namespace PairEmitMachine

abbrev Output := PairQueriesMachine.Input
abbrev Input := Sum Bool Output
abbrev State := Option Input

inductive Stack
  | input | first | second | saved | output
  deriving DecidableEq, Fintype

inductive Label
  | start | scan (accept : Bool) | emitSecond (accept : Bool)
  | emitFirst (accept : Bool) | emitSaved
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input | .first | .second => Bool | _ => Output

def firstBit : Output → Option Bool
  | .inl (.inl b) => some b | _ => none

def secondBit : Output → Option Bool
  | .inl (.inr b) => some b | _ => none

def edgeCell (cell : Option Bool) : Output := .inr (.inr cell)

def edgeBlock (first second : List Bool) : List Output :=
  [edgeCell none, edgeCell (some false), edgeCell (some true), edgeCell none] ++
    first.map (fun b => edgeCell (some b)) ++ [edgeCell none] ++
      second.map (fun b => edgeCell (some b))

private def observe (_ : State) (cell : Option Input) : State := cell
private def remember (_ : State) (cell : Option Output) : State := cell.map Sum.inr
private def rememberBit (_ : State) (cell : Option Bool) : State := cell.map Sum.inl
private def cell : State → Output | some (.inr c) => c | _ => .inr (.inr none)
private def bit : State → Bool | some (.inl b) => b | _ => false

def program : Label → TM2.Stmt Alphabet Label State
  | .start => .pop .input observe <| .goto fun s => .scan (bit s)
  | .scan accept => .pop .input observe <| .branch Option.isSome
      (.push .saved cell <|
        .branch (fun s => (firstBit (cell s)).isSome)
          (.push .first (fun s => (firstBit (cell s)).getD false) <|
            .goto fun _ => .scan accept)
          (.branch (fun s => (secondBit (cell s)).isSome)
            (.push .second (fun s => (secondBit (cell s)).getD false) <|
              .goto fun _ => .scan accept)
            (.goto fun _ => .scan accept)))
      (.goto fun _ => .emitSecond accept)
  | .emitSecond accept => .pop .second rememberBit <| .branch Option.isSome
      (.branch (fun _ => accept)
        (.push .output (fun s => edgeCell (some (bit s))) <|
          .goto fun _ => .emitSecond accept)
        (.goto fun _ => .emitSecond accept))
      (.branch (fun _ => accept)
        (.push .output (fun _ => edgeCell none) <| .goto fun _ => .emitFirst accept)
        (.goto fun _ => .emitFirst accept))
  | .emitFirst accept => .pop .first rememberBit <| .branch Option.isSome
      (.branch (fun _ => accept)
        (.push .output (fun s => edgeCell (some (bit s))) <|
          .goto fun _ => .emitFirst accept)
        (.goto fun _ => .emitFirst accept))
      (.branch (fun _ => accept)
        (.push .output (fun _ => edgeCell none) <|
          .push .output (fun _ => edgeCell (some true)) <|
          .push .output (fun _ => edgeCell (some false)) <|
          .push .output (fun _ => edgeCell none) <| .goto fun _ => .emitSaved)
        (.goto fun _ => .emitSaved))
  | .emitSaved => .pop .saved remember <| .branch Option.isSome
      (.push .output cell <| .goto fun _ => .emitSaved)
      (.load (fun _ => none) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .start
  σ := State
  initialState := none
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input : List Input) (first second : List Bool)
    (saved output : List Output) : (k : Stack) → List (Alphabet k)
  | .input => input | .first => first | .second => second
  | .saved => saved | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (first second : List Bool) (saved output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input first second saved output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "pair_emit_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe,
    remember, rememberBit, cell, bit, firstBit, secondBit, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Output) (first second : List Bool)
    (saved output : List Output) (state : State) (accept : Bool) :
    Run (cfg (some (.scan accept)) state (input.map Sum.inr) first second saved output)
      (cfg (some (.emitSecond accept)) none []
        ((input.filterMap firstBit).reverse ++ first)
        ((input.filterMap secondBit).reverse ++ second)
        (input.reverse ++ saved) output) (input.length + 1) := by
  induction input generalizing first second saved state with
  | nil => exact one (by pair_emit_step)
  | cons c input ih =>
      have step : Run
          (cfg (some (.scan accept)) state ((c :: input).map Sum.inr) first second saved output)
          (cfg (some (.scan accept)) (some (.inr c)) (input.map Sum.inr)
            ((firstBit c).toList ++ first) ((secondBit c).toList ++ second)
            (c :: saved) output) 1 := by
        apply one
        rcases c with (b | b) | rest <;> pair_emit_step
      have tail := ih ((firstBit c).toList ++ first) ((secondBit c).toList ++ second)
        (c :: saved) (some (.inr c))
      rcases c with (b | b) | rest <;>
        simpa [firstBit, secondBit, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq step tail

private def second_run (first second : List Bool) (saved output : List Output)
    (state : State) (accept : Bool) :
    Run (cfg (some (.emitSecond accept)) state [] first second saved output)
      (cfg (some (.emitFirst accept)) none [] first [] saved
        ((if accept then [edgeCell none] ++ second.reverse.map (fun b => edgeCell (some b))
          else []) ++ output)) (second.length + 1) := by
  induction second generalizing output state with
  | nil => cases accept <;> exact one (by pair_emit_step)
  | cons b second ih =>
      have step : Run (cfg (some (.emitSecond accept)) state [] first (b :: second) saved output)
          (cfg (some (.emitSecond accept)) (some (.inl b)) [] first second saved
            ((if accept then [edgeCell (some b)] else []) ++ output)) 1 := by
        cases accept <;> exact one (by pair_emit_step)
      have tail := ih ((if accept then [edgeCell (some b)] else []) ++ output) (some (.inl b))
      cases accept <;>
        simpa [List.reverse_cons, List.map_append, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq step tail

private def first_run (first : List Bool) (saved output : List Output)
    (state : State) (accept : Bool) :
    Run (cfg (some (.emitFirst accept)) state [] first [] saved output)
      (cfg (some .emitSaved) none [] [] [] saved
        ((if accept then [edgeCell none, edgeCell (some false), edgeCell (some true), edgeCell none] ++
            first.reverse.map (fun b => edgeCell (some b)) else []) ++ output))
      (first.length + 1) := by
  induction first generalizing output state with
  | nil => cases accept <;> exact one (by pair_emit_step)
  | cons b first ih =>
      have step : Run (cfg (some (.emitFirst accept)) state [] (b :: first) [] saved output)
          (cfg (some (.emitFirst accept)) (some (.inl b)) [] first [] saved
            ((if accept then [edgeCell (some b)] else []) ++ output)) 1 := by
        cases accept <;> exact one (by pair_emit_step)
      have tail := ih ((if accept then [edgeCell (some b)] else []) ++ output) (some (.inl b))
      cases accept <;>
        simpa [List.reverse_cons, List.map_append, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq step tail

private def saved_run (saved output : List Output) (state : State) :
    Run (cfg (some .emitSaved) state [] [] [] saved output)
      (cfg none none [] [] [] [] (saved.reverse ++ output)) (saved.length + 1) := by
  induction saved generalizing output state with
  | nil => exact one (by pair_emit_step)
  | cons c saved ih =>
      have step : Run (cfg (some .emitSaved) state [] [] [] (c :: saved) output)
          (cfg (some .emitSaved) (some (.inr c)) [] [] [] saved (c :: output)) 1 :=
        one (by pair_emit_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq step (ih (c :: output) (some (.inr c)))

private def run (accept : Bool) (input : List Output) :
    Run (cfg (some .start) none (.inl accept :: input.map Sum.inr) [] [] [] [])
      (cfg none none [] [] [] [] (input ++
        if accept then edgeBlock (input.filterMap firstBit) (input.filterMap secondBit) else []))
      (4 * (input.length + 1) + 5) := by
  have start : Run (cfg (some .start) none (.inl accept :: input.map Sum.inr) [] [] [] [])
      (cfg (some (.scan accept)) (some (.inl accept)) (input.map Sum.inr) [] [] [] []) 1 :=
    one (by pair_emit_step)
  have scan := scan_run input [] [] [] [] (some (.inl accept)) accept
  have second := second_run (input.filterMap firstBit).reverse
    (input.filterMap secondBit).reverse input.reverse [] none accept
  have first := first_run (input.filterMap firstBit).reverse input.reverse
    (if accept then [edgeCell none] ++ (input.filterMap secondBit).map (fun b => edgeCell (some b))
      else []) none accept
  have saved := saved_run input.reverse
    (if accept then edgeBlock (input.filterMap firstBit) (input.filterMap secondBit) else []) none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at scan second first saved
  have joined : Run _ _ _ := seq (seq (seq start scan) second) first
  have normalized : Run
      (cfg (some .start) none (.inl accept :: input.map Sum.inr) [] [] [] [])
      (cfg (some .emitSaved) none [] [] [] input.reverse
        (if accept then edgeBlock (input.filterMap firstBit) (input.filterMap secondBit) else []))
      (1 + (input.length + 1) + ((input.filterMap secondBit).length + 1) +
        ((input.filterMap firstBit).length + 1)) := by
    cases accept <;> simpa [edgeBlock, List.append_assoc] using joined
  have full := seq normalized saved
  apply evalsToInTimeMono full
  have hl := List.length_filterMap_le firstBit input
  have hr := List.length_filterMap_le secondBit input
  omega

private theorem init_eq (input : List Input) :
    initList computer input = cfg (some .start) none input [] [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none none [] [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem emitted_encode (tested : PairTest.Output) :
    List.append (α := Output) (PairQueries.inputFinEncoding.encode tested.2)
      (if tested.1 then edgeBlock
        ((PairQueries.inputFinEncoding.encode tested.2).filterMap firstBit)
        ((PairQueries.inputFinEncoding.encode tested.2).filterMap secondBit) else []) =
      PairQueries.inputFinEncoding.encode (PairEmit.emit tested) := by
  have discard {α β : Type} (xs : List α) :
      xs.filterMap (fun _ => (none : Option β)) = [] := by simp
  have two : encodeNat 2 = [false, true] := by
    unfold encodeNat
    change encodeNum (Num.ofNat' 2) = [false, true]
    rw [show (2 : ℕ) = Nat.bit false 1 by norm_num [Nat.bit], Num.ofNat'_bit,
      Num.ofNat'_one]
    rfl
  cases h : tested.1 <;>
    simp [PairEmit.emit, h, PairQueries.inputFinEncoding, PairQueries.retainedFinEncoding,
      ScopeExtraction.endpointsFinEncoding, LeanNPHardness.PairEncoding.finEncoding,
      NegativeRows.inputFinEncoding,
      List.filterMap_map, Function.comp_def, firstBit, secondBit,
      finEncodingNatBool, encodingNatBool, edgeBlock, edgeCell,
      NegativeRows.inputEncode, NegativeRows.pairRows, DomainFieldSection.rowPayloadEncode,
      LeanNPHardness.CountedNatRows.rowFields, SourceOrderRawFields.encode,
      two, discard, List.map_append, List.map_map, List.append_assoc]

end PairEmitMachine

/-- Full serialized conditional emission, including copying, framing and scratch cleanup. -/
def pairEmit_outputsInTime (tested : PairTest.Output) :
    TM2OutputsInTime PairEmitMachine.computer (PairTest.outputFinEncoding.encode tested)
      (some (PairQueries.inputFinEncoding.encode (PairEmit.emit tested)))
      (4 * (PairTest.outputFinEncoding.encode tested).length + 5) := by
  rw [TM2OutputsInTime, PairEmitMachine.init_eq]
  simp only [Option.map_some]
  rw [PairEmitMachine.halt_eq, ← PairEmitMachine.emitted_encode]
  simpa [PairTest.outputFinEncoding, LeanNPHardness.PairEncoding.finEncoding,
    finEncodingBoolBool, encodeBool] using
    PairEmitMachine.run tested.1 (PairQueries.inputFinEncoding.encode tested.2)

noncomputable def pairEmitComputableInPolyTime :
    @TM2ComputableInPolyTime PairTest.Output PairQueries.Input
      PairTest.outputFinEncoding PairQueries.inputFinEncoding PairEmit.emit where
  tm := PairEmitMachine.computer
  inputAlphabet := Equiv.refl PairEmitMachine.Input
  outputAlphabet := Equiv.refl PairEmitMachine.Output
  time := 4 * Polynomial.X + 5
  outputsFun tested := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_X] using pairEmit_outputsInTime tested

#print axioms PairEmit.retained_eq
#print axioms PairEmit.afterTest_eq
#print axioms PairEmit.output_length
#print axioms PairEmit.output_length_le
#print axioms pairEmit_outputsInTime
#print axioms pairEmitComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
