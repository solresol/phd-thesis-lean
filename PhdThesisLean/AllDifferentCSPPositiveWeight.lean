import PhdThesisLean.AllDifferentCSPOccurrenceCount

/-!
# Stage and retain the common binary weight for one positive row

The input uses the existing binary endpoint encoding and the exact reversed
raw weight field produced by the graph compiler. A finite routing machine
copies that weight, restores its source order for the row, inserts the two
endpoint delimiters and retains the original weight field for the next row.
The checked local positive emitter then adds the row header. Pair selection
and repeated emission remain separate obligations.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PositiveWeight

abbrev Input := PositiveBlock.Value
abbrev Output := PositiveBlock.Value × ℕ

def inputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding ScopeExtraction.endpointsFinEncoding
    UnaryBoundEncoding.outputFinEncoding

def preparedFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding PositiveBlock.inputFinEncoding
    UnaryBoundEncoding.outputFinEncoding

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding PositiveBlock.outputFinEncoding
    UnaryBoundEncoding.outputFinEncoding

def prepare (value : Input) : Output := (value, value.2)

theorem retained_weight (value : Input) : (prepare value).2 = value.2 := rfl

theorem input_length (value : Input) :
    (inputFinEncoding.encode value).length =
      (encodeNat value.1.1).length + (encodeNat value.1.2).length +
        (encodeNat value.2).length + 1 := by
  simp [inputFinEncoding, ScopeExtraction.endpointsFinEncoding,
    finEncodingNatBool, encodingNatBool, UnaryBoundEncoding.output_length, Nat.add_assoc]

/-- All copied weight bits and its delimiter are charged, plus both endpoint delimiters. -/
theorem prepared_length (value : Input) :
    (preparedFinEncoding.encode (prepare value)).length =
      (inputFinEncoding.encode value).length + (encodeNat value.2).length + 3 := by
  simp [preparedFinEncoding, prepare, PositiveBlock.inputFinEncoding,
    PositiveBlock.inputEncode, SourceOrderRawFields.encode, UnaryBoundEncoding.output_length,
    input_length]
  omega

theorem output_length_le (value : Input) :
    (outputFinEncoding.encode (prepare value)).length ≤
      2 * (inputFinEncoding.encode value).length + 7 := by
  have hp := prepared_length value
  have hi := input_length value
  have ho : (outputFinEncoding.encode (prepare value)).length =
      (preparedFinEncoding.encode (prepare value)).length + 5 := by
    simp [outputFinEncoding, preparedFinEncoding, prepare,
      PositiveBlock.inputFinEncoding, PositiveBlock.outputFinEncoding,
      PositiveBlock.outputEncode_length, Nat.add_assoc, Nat.add_comm]
  omega

/-- The emitted component is precisely the existing counted positive residual row. -/
theorem row_encode (value : Input) :
    outputFinEncoding.encode (prepare value) =
      (DomainFieldSection.rowPayloadEncode
        [(RuntimeResidualRow.pin value.1.1 value.1.2 value.2).toNatList]).map Sum.inl ++
        (UnaryBoundEncoding.outputFinEncoding.encode value.2).map Sum.inr := by
  simp only [outputFinEncoding, prepare, LeanNPHardness.PairEncoding.finEncoding,
    PositiveBlock.outputFinEncoding, PositiveBlock.outputEncode_eq_row]

/-- A scan query includes every endpoint and weight bit and fits in the retained wire. -/
theorem input_length_le_sections (sections : CountedPositiveSections.Value) (index rank : ℕ)
    (hi : index < sections.1.1.2) (hr : rank ≤ sections.1.1.1.2) :
    (inputFinEncoding.encode ((index, rank), sections.2.2)).length ≤
      (CountedPositiveSections.finEncoding.encode sections).length := by
  have hi' := (BinaryNatLists.encodeNat_length_le index).trans hi.le
  have hr' := (BinaryNatLists.encodeNat_length_le rank).trans hr
  rw [input_length]
  simp only [CountedPositiveSections.finEncoding, CountedPositiveSections.sectionsFinEncoding,
    CountedPositiveSections.domainsFinEncoding, OccurrenceCount.finEncoding,
    PinningWeight.negativeFinEncoding, LeanNPHardness.PairEncoding.finEncoding_encode_length,
    UnaryBoundEncoding.output_length, unaryFinEncodingNat, unaryEncodeNat_eq_replicate_true,
    List.length_replicate]
  omega

example : prepare ((0, 0), 0) = (((0, 0), 0), 0) := rfl
example : prepare ((2, 3), 4) = (((2, 3), 4), 4) := rfl

end PositiveWeight

namespace PositiveWeightMachine

abbrev Input := Sum (Sum Bool Bool) (Option Bool)
abbrev Output := Sum (Option Bool) (Option Bool)

inductive Stack
  | input | first | second | weight | output
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input | .first | .second => Bool | .weight => Option Bool | .output => Output

inductive Label
  | scan | retainWeight | emitWeight | emitSecond | emitFirst
  deriving DecidableEq, Fintype

structure State where
  cell : Option Input
  raw : Option (Option Bool)
  bit : Option Bool
  deriving DecidableEq, Fintype

def initialState : State := ⟨none, none, none⟩
private def readInput (_ : State) (cell : Option Input) : State := ⟨cell, none, none⟩
private def readRaw (_ : State) (raw : Option (Option Bool)) : State := ⟨none, raw, none⟩
private def readBit (_ : State) (bit : Option Bool) : State := ⟨none, none, bit⟩

def firstBit : Input → Option Bool
  | .inl (.inl bit) => some bit | _ => none
def secondBit : Input → Option Bool
  | .inl (.inr bit) => some bit | _ => none
def weightCell : Input → Option (Option Bool)
  | .inr cell => some cell | _ => none
private def cell (s : State) : Input := s.cell.getD (.inr none)

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input readInput <| .branch (fun s => s.cell.isSome)
      (.branch (fun s => (firstBit (cell s)).isSome)
        (.push .first (fun s => (firstBit (cell s)).getD false) <| .goto fun _ => .scan)
        (.branch (fun s => (secondBit (cell s)).isSome)
          (.push .second (fun s => (secondBit (cell s)).getD false) <| .goto fun _ => .scan)
          (.push .weight (fun s => (weightCell (cell s)).getD none) <| .goto fun _ => .scan)))
      (.goto fun _ => .retainWeight)
  | .retainWeight => .pop .weight readRaw <| .branch (fun s => s.raw.isSome)
      (.push .input (fun s => .inr (s.raw.getD none)) <|
        .push .output (fun s => .inr (s.raw.getD none)) <| .goto fun _ => .retainWeight)
      (.goto fun _ => .emitWeight)
  | .emitWeight => .pop .input readInput <| .branch (fun s => s.cell.isSome)
      (.push .output (fun s => .inl ((weightCell (cell s)).getD none)) <|
        .goto fun _ => .emitWeight)
      (.goto fun _ => .emitSecond)
  | .emitSecond => .pop .second readBit <| .branch (fun s => s.bit.isSome)
      (.push .output (fun s => .inl (some (s.bit.getD false))) <| .goto fun _ => .emitSecond)
      (.push .output (fun _ => .inl none) <| .goto fun _ => .emitFirst)
  | .emitFirst => .pop .first readBit <| .branch (fun s => s.bit.isSome)
      (.push .output (fun s => .inl (some (s.bit.getD false))) <| .goto fun _ => .emitFirst)
      (.push .output (fun _ => .inl none) <| .load (fun _ => initialState) .halt)

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

private def stackContents (input : List Input) (first second : List Bool)
    (weight : List (Option Bool)) (output : List Output) : (k : Stack) → List (Alphabet k)
  | .input => input | .first => first | .second => second | .weight => weight | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (first second : List Bool) (weight : List (Option Bool)) (output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input first second weight output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "weight_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, Function.update,
    readInput, readRaw, readBit, cell, firstBit, secondBit, weightCell, initialState]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Input) (first second : List Bool)
    (weight : List (Option Bool)) (state : State) :
    Run (cfg (some .scan) state input first second weight [])
      (cfg (some .retainWeight) initialState []
        ((input.filterMap firstBit).reverse ++ first)
        ((input.filterMap secondBit).reverse ++ second)
        ((input.filterMap weightCell).reverse ++ weight) []) (input.length + 1) := by
  induction input generalizing first second weight state with
  | nil => exact one (by weight_step)
  | cons symbol input ih =>
    cases symbol with
    | inl endpoint =>
      cases endpoint with
      | inl bit =>
        have h : Run (cfg (some .scan) state (.inl (.inl bit) :: input) first second weight [])
            (cfg (some .scan) ⟨some (.inl (.inl bit)), none, none⟩ input
              (bit :: first) second weight []) 1 := one (by weight_step)
        simpa [firstBit, secondBit, weightCell, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih _ _ _ _)
      | inr bit =>
        have h : Run (cfg (some .scan) state (.inl (.inr bit) :: input) first second weight [])
            (cfg (some .scan) ⟨some (.inl (.inr bit)), none, none⟩ input
              first (bit :: second) weight []) 1 := one (by weight_step)
        simpa [firstBit, secondBit, weightCell, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih _ _ _ _)
    | inr raw =>
      have h : Run (cfg (some .scan) state (.inr raw :: input) first second weight [])
          (cfg (some .scan) ⟨some (.inr raw), none, none⟩ input
            first second (raw :: weight) []) 1 := one (by weight_step)
      simpa [firstBit, secondBit, weightCell, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih _ _ _ _)

private def retain_run (weight : List (Option Bool)) (input : List Input)
    (first second : List Bool) (output : List Output) (state : State) :
    Run (cfg (some .retainWeight) state input first second weight output)
      (cfg (some .emitWeight) initialState (weight.reverse.map Sum.inr ++ input)
        first second [] (weight.reverse.map Sum.inr ++ output)) (weight.length + 1) := by
  induction weight generalizing input output state with
  | nil => exact one (by weight_step)
  | cons raw weight ih =>
    have h : Run (cfg (some .retainWeight) state input first second (raw :: weight) output)
        (cfg (some .retainWeight) ⟨none, some raw, none⟩ (.inr raw :: input)
          first second weight (.inr raw :: output)) 1 := one (by weight_step)
    simpa [List.reverse_cons, List.map_append, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih _ _ _)

private def weight_run (weight : List (Option Bool)) (first second : List Bool)
    (output : List Output) (state : State) :
    Run (cfg (some .emitWeight) state (weight.map Sum.inr) first second [] output)
      (cfg (some .emitSecond) initialState [] first second []
        (weight.reverse.map Sum.inl ++ output)) (weight.length + 1) := by
  induction weight generalizing output state with
  | nil => exact one (by weight_step)
  | cons raw weight ih =>
    have h : Run (cfg (some .emitWeight) state ((raw :: weight).map Sum.inr) first second [] output)
        (cfg (some .emitWeight) ⟨some (.inr raw), none, none⟩ (weight.map Sum.inr)
          first second [] (.inl raw :: output)) 1 := one (by weight_step)
    simpa [List.reverse_cons, List.map_append, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih _ _)

private def second_run (second first : List Bool) (output : List Output) (state : State) :
    Run (cfg (some .emitSecond) state [] first second [] output)
      (cfg (some .emitFirst) initialState [] first [] []
        (.inl none :: (second.reverse.map fun bit => .inl (some bit)) ++ output))
      (second.length + 1) := by
  induction second generalizing output state with
  | nil => exact one (by weight_step)
  | cons bit second ih =>
    have h : Run (cfg (some .emitSecond) state [] first (bit :: second) [] output)
        (cfg (some .emitSecond) ⟨none, none, some bit⟩ [] first second []
          (.inl (some bit) :: output)) 1 := one (by weight_step)
    simpa [List.reverse_cons, List.map_append, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih _ _)

private def first_run (first : List Bool) (output : List Output) (state : State) :
    Run (cfg (some .emitFirst) state [] first [] [] output)
      (cfg none initialState [] [] [] []
        (.inl none :: (first.reverse.map fun bit => .inl (some bit)) ++ output))
      (first.length + 1) := by
  induction first generalizing output state with
  | nil => exact one (by weight_step)
  | cons bit first ih =>
    have h : Run (cfg (some .emitFirst) state [] (bit :: first) [] [] output)
        (cfg (some .emitFirst) ⟨none, none, some bit⟩ [] first [] []
          (.inl (some bit) :: output)) 1 := one (by weight_step)
    simpa [List.reverse_cons, List.map_append, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih _ _)

private def wire (first second : List Bool) (weight : List (Option Bool)) : List Input :=
  first.map (fun bit => .inl (.inl bit)) ++
    second.map (fun bit => .inl (.inr bit)) ++ weight.map Sum.inr

private def result (first second : List Bool) (weight : List (Option Bool)) : List Output :=
  .inl none :: first.map (fun bit => .inl (some bit)) ++
    .inl none :: second.map (fun bit => .inl (some bit)) ++
      weight.reverse.map Sum.inl ++ weight.map Sum.inr

private def run (first second : List Bool) (weight : List (Option Bool)) :
    Run (cfg (some .scan) initialState (wire first second weight) [] [] [] [])
      (cfg none initialState [] [] [] [] (result first second weight))
      (2 * first.length + 2 * second.length + 3 * weight.length + 5) := by
  have empty_map {α β : Type} (xs : List α) :
      xs.filterMap (fun _ => (none : Option β)) = [] := by simp
  have hs := scan_run (wire first second weight) [] [] [] initialState
  simp [wire, firstBit, secondBit, weightCell, List.filterMap_map, Function.comp_def,
    empty_map] at hs
  have hr := retain_run weight.reverse [] first.reverse second.reverse [] initialState
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hr
  have hw := weight_run weight first.reverse second.reverse (weight.map Sum.inr) initialState
  have h₂ := second_run second.reverse first.reverse
    (weight.reverse.map Sum.inl ++ weight.map Sum.inr) initialState
  have h₁ := first_run first.reverse
    (.inl none :: second.map (fun bit => .inl (some bit)) ++
      weight.reverse.map Sum.inl ++ weight.map Sum.inr) initialState
  simp only [List.reverse_reverse, List.length_reverse, List.append_assoc] at h₂ h₁
  convert seq (seq (seq (seq hs hr) hw) h₂) h₁ using 1 <;>
    first | omega | simp [result, wire, List.append_assoc]

private theorem init_eq (input : List Input) :
    initList computer input = cfg (some .scan) initialState input [] [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none initialState [] [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

end PositiveWeightMachine

/-- Finite weight copying and field preparation, including restoration and cleanup. -/
def positiveWeightPrepare_outputsInTime (value : PositiveWeight.Input) :
    TM2OutputsInTime PositiveWeightMachine.computer (PositiveWeight.inputFinEncoding.encode value)
      (some (PositiveWeight.preparedFinEncoding.encode (PositiveWeight.prepare value)))
      (3 * (PositiveWeight.inputFinEncoding.encode value).length + 5) := by
  rw [TM2OutputsInTime, PositiveWeightMachine.init_eq]
  simp only [Option.map_some, PositiveWeightMachine.halt_eq]
  have h := PositiveWeightMachine.run (encodeNat value.1.1) (encodeNat value.1.2)
    (UnaryBoundEncoding.outputFinEncoding.encode value.2)
  have hw : (PositiveWeight.inputFinEncoding.encode value) =
      PositiveWeightMachine.wire (encodeNat value.1.1) (encodeNat value.1.2)
        (UnaryBoundEncoding.outputFinEncoding.encode value.2) := by
    simp [PositiveWeight.inputFinEncoding, ScopeExtraction.endpointsFinEncoding,
      finEncodingNatBool, encodingNatBool, PositiveWeightMachine.wire,
      List.map_append, List.map_map, Function.comp_def]
  have ho : PositiveWeight.preparedFinEncoding.encode (PositiveWeight.prepare value) =
      PositiveWeightMachine.result (encodeNat value.1.1) (encodeNat value.1.2)
        (UnaryBoundEncoding.outputFinEncoding.encode value.2) := by
    simp [PositiveWeight.preparedFinEncoding, PositiveWeight.prepare,
      PositiveBlock.inputFinEncoding, PositiveBlock.inputEncode, SourceOrderRawFields.encode,
      UnaryBoundEncoding.outputFinEncoding, RawNatList.segment, PositiveWeightMachine.result,
      List.map_append, List.map_map, Function.comp_def, List.reverse_append, List.map_reverse,
      List.append_assoc]
  rw [hw, ho]
  apply evalsToInTimeMono h
  simp [PositiveWeightMachine.wire]
  omega

noncomputable def positiveWeightPrepareComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveWeight.Input PositiveWeight.Output
      PositiveWeight.inputFinEncoding PositiveWeight.preparedFinEncoding PositiveWeight.prepare where
  tm := PositiveWeightMachine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 5
  outputsFun value := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using positiveWeightPrepare_outputsInTime value

/-- Emit the exact positive row and retain the graph compiler's binary weight. -/
noncomputable def positiveRowWithWeightComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveWeight.Input PositiveWeight.Output
      PositiveWeight.inputFinEncoding PositiveWeight.outputFinEncoding PositiveWeight.prepare := by
  let emit := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    PositiveBlock.inputFinEncoding PositiveBlock.outputFinEncoding
    UnaryBoundEncoding.outputFinEncoding id positiveBlockComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _
    positiveWeightPrepareComputableInPolyTime emit
  exact { composed with
    outputsFun := fun value => by simpa only [Function.comp_def, id_eq] using composed.outputsFun value }

/-- Uniform complete-call cost for a bounded candidate in the positive scan. -/
theorem positiveRowWithWeight_steps_le (sections : CountedPositiveSections.Value) (index rank : ℕ)
    (hi : index < sections.1.1.2) (hr : rank ≤ sections.1.1.1.2) :
    (positiveRowWithWeightComputableInPolyTime.outputsFun ((index, rank), sections.2.2)).steps ≤
      positiveRowWithWeightComputableInPolyTime.time.eval
        (CountedPositiveSections.finEncoding.encode sections).length := by
  exact (positiveRowWithWeightComputableInPolyTime.outputsFun
    ((index, rank), sections.2.2)).steps_le_m.trans
      (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
        (PositiveWeight.input_length_le_sections sections index rank hi hr))

#print axioms PositiveWeight.output_length_le
#print axioms PositiveWeight.row_encode
#print axioms PositiveWeight.input_length_le_sections
#print axioms positiveWeightPrepare_outputsInTime
#print axioms positiveWeightPrepareComputableInPolyTime
#print axioms positiveRowWithWeightComputableInPolyTime
#print axioms positiveRowWithWeight_steps_le

end PhdThesisLean.AllDifferentCSPMachine
