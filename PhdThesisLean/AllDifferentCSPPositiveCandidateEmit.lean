import PhdThesisLean.AllDifferentCSPPositiveCandidateTest

/-!
# Conditionally emit a positive row while retaining the complete scan state

The computed membership bit controls exact counted pinning-row emission.
The finite pass retains all source fields and old rows, copies both binary
coordinates, reverses the stored binary weight into row order, and clears
scratch storage. The bound counts wire-level work even on rejected candidates.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PositiveCandidateEmit

def row (input : PositiveCandidateQueries.Input) : PositiveBlock.Value :=
  (input.1, input.2.1.2.2)

def emit (tested : PositiveCandidateTest.Output) : PositiveCandidateQueries.Input :=
  (tested.2.1, tested.2.2.1,
    if tested.1 then tested.2.2.2 ++ [row tested.2] else tested.2.2.2)

theorem retained_eq (tested : PositiveCandidateTest.Output) :
    (emit tested).1 = tested.2.1 ∧ (emit tested).2.1 = tested.2.2.1 := ⟨rfl, rfl⟩

theorem rows_encode_append (rows more : List PositiveBlock.Value) :
    PositiveRows.outputEncode (rows ++ more) =
      PositiveRows.outputEncode rows ++ PositiveRows.outputEncode more := by
  simp [PositiveRows.outputEncode, List.flatMap_append]

/-- Every emitted coordinate and weight bit, plus eight structural cells. -/
theorem output_length (tested : PositiveCandidateTest.Output) :
    (PositiveCandidateQueries.inputFinEncoding.encode (emit tested)).length =
      (PositiveCandidateQueries.inputFinEncoding.encode tested.2).length +
        if tested.1 then (PositiveBlock.outputEncode (row tested.2)).length else 0 := by
  rw [PositiveCandidateQueries.input_length, PositiveCandidateQueries.input_length]
  cases h : tested.1 <;>
    simp [emit, h, PositiveRows.outputEncode, Nat.add_assoc]

/-- The existing source contains every copied bit, including the binary weight. -/
theorem output_length_le (tested : PositiveCandidateTest.Output) :
    (PositiveCandidateQueries.inputFinEncoding.encode (emit tested)).length ≤
      2 * (PositiveCandidateTest.outputFinEncoding.encode tested).length + 8 := by
  have hi : (encodeNat tested.2.1.1).length + (encodeNat tested.2.1.2).length +
      (encodeNat tested.2.2.1.2.2).length ≤
        (PositiveCandidateQueries.inputFinEncoding.encode tested.2).length := by
    simp [PositiveCandidateQueries.inputFinEncoding, PositiveCandidateQueries.retainedFinEncoding,
      ScopeExtraction.endpointsFinEncoding, CountedPositiveSections.finEncoding,
      PinningWeight.negativeFinEncoding, finEncodingNatBool, encodingNatBool,
      UnaryBoundEncoding.output_length]
    omega
  have hs : (PositiveCandidateTest.outputFinEncoding.encode tested).length =
      (PositiveCandidateQueries.inputFinEncoding.encode tested.2).length + 1 := by
    simp [PositiveCandidateTest.outputFinEncoding, finEncodingBoolBool, encodeBool, Nat.add_comm]
  rw [output_length, PositiveRows.block_length]
  dsimp only [row]
  split <;> omega

example : emit (false, (0, 0), (((([], 0), 0), []), ([], 0)), []) =
    ((0, 0), (((([], 0), 0), []), ([], 0)), []) := rfl
example : emit (true, (0, 8), (((([(0, 8)], 1), 1), [[], [0]]), ([], 1000000)),
    [((0, 2), 1000000)]) =
    ((0, 8), (((([(0, 8)], 1), 1), [[], [0]]), ([], 1000000)),
      [((0, 2), 1000000), ((0, 8), 1000000)]) := rfl

end PositiveCandidateEmit

namespace PositiveCandidateEmitMachine

abbrev Output := PositiveCandidateQueriesMachine.Input
abbrev Input := Sum Bool Output
abbrev State := Option Input

inductive Stack
  | input | first | second | weight | reversed | saved | output
  deriving DecidableEq, Fintype

inductive Label
  | start | scan (accept : Bool) | reverseWeight (accept : Bool)
  | emitWeight (accept : Bool) | emitSecond (accept : Bool)
  | emitFirst (accept : Bool) | emitSaved
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input | .first | .second => Bool
  | .weight | .reversed => Option Bool | _ => Output

def firstBit : Output → Option Bool
  | .inl (.inl b) => some b | _ => none

def secondBit : Output → Option Bool
  | .inl (.inr b) => some b | _ => none

def weightCell : Output → Option (Option Bool)
  | .inr (.inl (.inr (.inr raw))) => some raw | _ => none

def rowCell (cell : Option Bool) : Output := .inr (.inr cell)

def rowBlock (first second : List Bool) (weight : List (Option Bool)) : List Output :=
  (PositiveBlock.headerPrefix ++ [none]).map rowCell ++
    first.map (fun b => rowCell (some b)) ++ [rowCell none] ++
      second.map (fun b => rowCell (some b)) ++ weight.reverse.map rowCell

private def observe (_ : State) (cell : Option Input) : State := cell
private def remember (_ : State) (cell : Option Output) : State := cell.map Sum.inr
private def rememberBit (_ : State) (cell : Option Bool) : State := cell.map Sum.inl
private def rememberRaw (_ : State) (cell : Option (Option Bool)) : State :=
  cell.map (fun raw => .inr (rowCell raw))
private def raw : State → Option Bool
  | some (.inr (.inr (.inr value))) => value | _ => none
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
            (.branch (fun s => (weightCell (cell s)).isSome)
              (.push .weight (fun s => (weightCell (cell s)).getD none) <|
                .goto fun _ => .scan accept)
              (.goto fun _ => .scan accept))))
      (.goto fun _ => .reverseWeight accept)
  | .reverseWeight accept => .pop .weight rememberRaw <| .branch Option.isSome
      (.push .reversed raw <| .goto fun _ => .reverseWeight accept)
      (.goto fun _ => .emitWeight accept)
  | .emitWeight accept => .pop .reversed rememberRaw <| .branch Option.isSome
      (.branch (fun _ => accept)
        (.push .output (fun s => rowCell (raw s)) <| .goto fun _ => .emitWeight accept)
        (.goto fun _ => .emitWeight accept))
      (.goto fun _ => .emitSecond accept)
  | .emitSecond accept => .pop .second rememberBit <| .branch Option.isSome
      (.branch (fun _ => accept)
        (.push .output (fun s => rowCell (some (bit s))) <|
          .goto fun _ => .emitSecond accept)
        (.goto fun _ => .emitSecond accept))
      (.branch (fun _ => accept)
        (.push .output (fun _ => rowCell none) <| .goto fun _ => .emitFirst accept)
        (.goto fun _ => .emitFirst accept))
  | .emitFirst accept => .pop .first rememberBit <| .branch Option.isSome
      (.branch (fun _ => accept)
        (.push .output (fun s => rowCell (some (bit s))) <|
          .goto fun _ => .emitFirst accept)
        (.goto fun _ => .emitFirst accept))
      (.branch (fun _ => accept)
        (.push .output (fun _ => rowCell none) <|
          .push .output (fun _ => rowCell none) <|
          .push .output (fun _ => rowCell (some true)) <|
          .push .output (fun _ => rowCell (some false)) <|
          .push .output (fun _ => rowCell (some false)) <|
          .push .output (fun _ => rowCell none) <| .goto fun _ => .emitSaved)
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
    (weight reversed : List (Option Bool)) (saved output : List Output) : (k : Stack) → List (Alphabet k)
  | .input => input | .first => first | .second => second
  | .weight => weight | .reversed => reversed | .saved => saved | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (first second : List Bool) (weight reversed : List (Option Bool))
    (saved output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input first second weight reversed saved output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using! h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using! EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "positive_emit_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe,
    remember, rememberBit, rememberRaw, raw, cell, bit, firstBit, secondBit, weightCell, rowCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Output) (first second : List Bool)
    (weight : List (Option Bool)) (saved output : List Output) (state : State) (accept : Bool) :
    Run (cfg (some (.scan accept)) state (input.map Sum.inr) first second weight [] saved output)
      (cfg (some (.reverseWeight accept)) none []
        ((input.filterMap firstBit).reverse ++ first)
        ((input.filterMap secondBit).reverse ++ second)
        ((input.filterMap weightCell).reverse ++ weight) []
        (input.reverse ++ saved) output) (input.length + 1) := by
  induction input generalizing first second weight saved state with
  | nil => exact one (by positive_emit_step)
  | cons c input ih =>
      have step : Run
          (cfg (some (.scan accept)) state ((c :: input).map Sum.inr) first second weight [] saved output)
          (cfg (some (.scan accept)) (some (.inr c)) (input.map Sum.inr)
            ((firstBit c).toList ++ first) ((secondBit c).toList ++ second)
            ((weightCell c).toList ++ weight) [] (c :: saved) output) 1 := by
        apply one
        rcases c with (b | b) | ((sections | (negative | w)) | row) <;> positive_emit_step
      have tail := ih ((firstBit c).toList ++ first) ((secondBit c).toList ++ second)
        ((weightCell c).toList ++ weight) (c :: saved) (some (.inr c))
      rcases c with (b | b) | ((sections | (negative | w)) | row) <;>
        simpa [firstBit, secondBit, weightCell, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq step tail

private def reverse_run (first second : List Bool) (weight reversed : List (Option Bool))
    (saved output : List Output) (state : State) (accept : Bool) :
    Run (cfg (some (.reverseWeight accept)) state [] first second weight reversed saved output)
      (cfg (some (.emitWeight accept)) none [] first second []
        (weight.reverse ++ reversed) saved output) (weight.length + 1) := by
  induction weight generalizing reversed state with
  | nil => exact one (by positive_emit_step)
  | cons w weight ih =>
      have step : Run
          (cfg (some (.reverseWeight accept)) state [] first second (w :: weight) reversed saved output)
          (cfg (some (.reverseWeight accept)) (some (.inr (rowCell w))) [] first second weight
            (w :: reversed) saved output) 1 := one (by positive_emit_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq step (ih (w :: reversed) (some (.inr (rowCell w))))

private def weight_run (first second : List Bool) (weight : List (Option Bool))
    (saved output : List Output) (state : State) (accept : Bool) :
    Run (cfg (some (.emitWeight accept)) state [] first second [] weight saved output)
      (cfg (some (.emitSecond accept)) none [] first second [] [] saved
        ((if accept then weight.reverse.map rowCell else []) ++ output)) (weight.length + 1) := by
  induction weight generalizing output state with
  | nil => cases accept <;> exact one (by positive_emit_step)
  | cons w weight ih =>
      have step : Run
          (cfg (some (.emitWeight accept)) state [] first second [] (w :: weight) saved output)
          (cfg (some (.emitWeight accept)) (some (.inr (rowCell w))) [] first second [] weight saved
            ((if accept then [rowCell w] else []) ++ output)) 1 := by
        cases accept <;> exact one (by positive_emit_step)
      have tail := ih ((if accept then [rowCell w] else []) ++ output) (some (.inr (rowCell w)))
      cases accept <;> simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq step tail

private def second_run (first second : List Bool) (saved output : List Output)
    (state : State) (accept : Bool) :
    Run (cfg (some (.emitSecond accept)) state [] first second [] [] saved output)
      (cfg (some (.emitFirst accept)) none [] first [] [] [] saved
        ((if accept then [rowCell none] ++ second.reverse.map (fun b => rowCell (some b))
          else []) ++ output)) (second.length + 1) := by
  induction second generalizing output state with
  | nil => cases accept <;> exact one (by positive_emit_step)
  | cons b second ih =>
      have step : Run (cfg (some (.emitSecond accept)) state [] first (b :: second) [] [] saved output)
          (cfg (some (.emitSecond accept)) (some (.inl b)) [] first second [] [] saved
            ((if accept then [rowCell (some b)] else []) ++ output)) 1 := by
        cases accept <;> exact one (by positive_emit_step)
      have tail := ih ((if accept then [rowCell (some b)] else []) ++ output) (some (.inl b))
      cases accept <;>
        simpa [List.reverse_cons, List.map_append, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq step tail

private def first_run (first : List Bool) (saved output : List Output)
    (state : State) (accept : Bool) :
    Run (cfg (some (.emitFirst accept)) state [] first [] [] [] saved output)
      (cfg (some .emitSaved) none [] [] [] [] [] saved
        ((if accept then (PositiveBlock.headerPrefix ++ [none]).map rowCell ++
            first.reverse.map (fun b => rowCell (some b)) else []) ++ output))
      (first.length + 1) := by
  induction first generalizing output state with
  | nil => cases accept <;> exact one (by positive_emit_step)
  | cons b first ih =>
      have step : Run (cfg (some (.emitFirst accept)) state [] (b :: first) [] [] [] saved output)
          (cfg (some (.emitFirst accept)) (some (.inl b)) [] first [] [] [] saved
            ((if accept then [rowCell (some b)] else []) ++ output)) 1 := by
        cases accept <;> exact one (by positive_emit_step)
      have tail := ih ((if accept then [rowCell (some b)] else []) ++ output) (some (.inl b))
      cases accept <;>
        simpa [List.reverse_cons, List.map_append, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq step tail

private def saved_run (saved output : List Output) (state : State) :
    Run (cfg (some .emitSaved) state [] [] [] [] [] saved output)
      (cfg none none [] [] [] [] [] [] (saved.reverse ++ output)) (saved.length + 1) := by
  induction saved generalizing output state with
  | nil => exact one (by positive_emit_step)
  | cons c saved ih =>
      have step : Run (cfg (some .emitSaved) state [] [] [] [] [] (c :: saved) output)
          (cfg (some .emitSaved) (some (.inr c)) [] [] [] [] [] saved (c :: output)) 1 :=
        one (by positive_emit_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq step (ih (c :: output) (some (.inr c)))

private def run (accept : Bool) (input : List Output) :
    Run (cfg (some .start) none (.inl accept :: input.map Sum.inr) [] [] [] [] [] [])
      (cfg none none [] [] [] [] [] [] (input ++
        if accept then rowBlock (input.filterMap firstBit) (input.filterMap secondBit)
          (input.filterMap weightCell) else []))
      (6 * (input.length + 1) + 7) := by
  have start : Run (cfg (some .start) none (.inl accept :: input.map Sum.inr) [] [] [] [] [] [])
      (cfg (some (.scan accept)) (some (.inl accept)) (input.map Sum.inr) [] [] [] [] [] []) 1 :=
    one (by positive_emit_step)
  have scan := scan_run input [] [] [] [] [] (some (.inl accept)) accept
  have reverse := reverse_run (input.filterMap firstBit).reverse (input.filterMap secondBit).reverse
    (input.filterMap weightCell).reverse [] input.reverse [] none accept
  have weight := weight_run (input.filterMap firstBit).reverse (input.filterMap secondBit).reverse
    (input.filterMap weightCell) input.reverse [] none accept
  have second := second_run (input.filterMap firstBit).reverse
    (input.filterMap secondBit).reverse input.reverse
    (if accept then (input.filterMap weightCell).reverse.map rowCell else []) none accept
  have first := first_run (input.filterMap firstBit).reverse input.reverse
    ((if accept then [rowCell none] ++ (input.filterMap secondBit).map (fun b => rowCell (some b))
      else []) ++ (if accept then (input.filterMap weightCell).reverse.map rowCell else [])) none accept
  have saved := saved_run input.reverse
    (if accept then rowBlock (input.filterMap firstBit) (input.filterMap secondBit)
      (input.filterMap weightCell) else []) none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at scan reverse weight second first saved
  have joined := seq (seq (seq (seq (seq start scan) reverse) weight) second) first
  have normalized : Run
      (cfg (some .start) none (.inl accept :: input.map Sum.inr) [] [] [] [] [] [])
      (cfg (some .emitSaved) none [] [] [] [] [] input.reverse
        (if accept then rowBlock (input.filterMap firstBit) (input.filterMap secondBit)
          (input.filterMap weightCell) else []))
      (1 + (input.length + 1) + ((input.filterMap weightCell).length + 1) +
        ((input.filterMap weightCell).length + 1) + ((input.filterMap secondBit).length + 1) +
        ((input.filterMap firstBit).length + 1)) := by
    cases accept <;> simpa [rowBlock, List.append_assoc] using joined
  have full := seq normalized saved
  apply evalsToInTimeMono full
  have hl := List.length_filterMap_le firstBit input
  have hr := List.length_filterMap_le secondBit input
  have hw := List.length_filterMap_le weightCell input
  omega

private theorem init_eq (input : List Input) :
    initList computer input = cfg (some .start) none input [] [] [] [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none none [] [] [] [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem emitted_encode (tested : PositiveCandidateTest.Output) :
    List.append (α := Output) (PositiveCandidateQueries.inputFinEncoding.encode tested.2)
      (if tested.1 then rowBlock
        ((PositiveCandidateQueries.inputFinEncoding.encode tested.2).filterMap firstBit)
        ((PositiveCandidateQueries.inputFinEncoding.encode tested.2).filterMap secondBit)
        ((PositiveCandidateQueries.inputFinEncoding.encode tested.2).filterMap weightCell) else []) =
      PositiveCandidateQueries.inputFinEncoding.encode (PositiveCandidateEmit.emit tested) := by
  have discard {α β : Type} (xs : List α) :
      xs.filterMap (fun _ => (none : Option β)) = [] := by simp
  cases h : tested.1 <;>
    simp [PositiveCandidateEmit.emit, PositiveCandidateEmit.row, h,
      PositiveCandidateQueries.inputFinEncoding, PositiveCandidateQueries.retainedFinEncoding,
      CountedPositiveSections.finEncoding, PinningWeight.negativeFinEncoding,
      ScopeExtraction.endpointsFinEncoding, LeanNPHardness.PairEncoding.finEncoding,
      PositiveRows.outputFinEncoding,
      List.filterMap_map, Function.comp_def, firstBit, secondBit, weightCell,
      finEncodingNatBool, encodingNatBool, rowBlock, rowCell,
      PositiveRows.outputEncode, PositiveBlock.outputEncode_eq_prefix,
      PositiveBlock.inputEncode, SourceOrderRawFields.encode,
      UnaryBoundEncoding.outputFinEncoding, RawNatList.segment,
      discard, List.map_append, List.map_map, List.map_reverse, List.reverse_append,
      List.append_assoc]

end PositiveCandidateEmitMachine

/-- Full serialized conditional emission, including copying, framing and scratch cleanup. -/
def positiveCandidateEmit_outputsInTime (tested : PositiveCandidateTest.Output) :
    TM2OutputsInTime PositiveCandidateEmitMachine.computer (PositiveCandidateTest.outputFinEncoding.encode tested)
      (some (PositiveCandidateQueries.inputFinEncoding.encode (PositiveCandidateEmit.emit tested)))
      (6 * (PositiveCandidateTest.outputFinEncoding.encode tested).length + 7) := by
  rw [TM2OutputsInTime, PositiveCandidateEmitMachine.init_eq]
  simp only [Option.map_some]
  rw [PositiveCandidateEmitMachine.halt_eq, ← PositiveCandidateEmitMachine.emitted_encode]
  simpa [PositiveCandidateTest.outputFinEncoding, LeanNPHardness.PairEncoding.finEncoding,
    finEncodingBoolBool, encodeBool] using!
    PositiveCandidateEmitMachine.run tested.1 (PositiveCandidateQueries.inputFinEncoding.encode tested.2)

noncomputable def positiveCandidateEmitComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveCandidateTest.Output PositiveCandidateQueries.Input
      PositiveCandidateTest.outputFinEncoding PositiveCandidateQueries.inputFinEncoding PositiveCandidateEmit.emit where
  tm := PositiveCandidateEmitMachine.computer
  inputAlphabet := Equiv.refl PositiveCandidateEmitMachine.Input
  outputAlphabet := Equiv.refl PositiveCandidateEmitMachine.Output
  time := 6 * Polynomial.X + 7
  outputsFun tested := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_X] using positiveCandidateEmit_outputsInTime tested

#print axioms PositiveCandidateEmit.retained_eq
#print axioms PositiveCandidateEmit.output_length
#print axioms PositiveCandidateEmit.output_length_le
#print axioms positiveCandidateEmit_outputsInTime
#print axioms positiveCandidateEmitComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
