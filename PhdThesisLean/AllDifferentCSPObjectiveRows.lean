import PhdThesisLean.AllDifferentCSPPositiveScanLoop

/-!
# Assemble the complete ordered residual rows

A finite routing pass retains the unary variable count and concatenates positive
rows before negative rows, exactly as in the semantic compiler. All scan
counters, ranked domains, scopes and the separate weight copy are consumed.
Each retained bit is transferred once; no arithmetic is hidden in a step.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace ObjectiveRows

/-- All row arities and tags are checked by the shared counted-row parser. -/
def encode (rows : List RuntimeResidualRow) : List (Option Bool) :=
  DomainFieldSection.rowPayloadEncode (rows.map RuntimeResidualRow.toNatList)

def decode (wire : List (Option Bool)) : Option (List RuntimeResidualRow) := do
  let rows ← DomainFieldSection.rowPayloadDecode wire
  rows.mapM RuntimeResidualRow.ofNatList

@[simp]
theorem decode_encode (rows : List RuntimeResidualRow) : decode (encode rows) = some rows := by
  unfold decode encode
  rw [DomainFieldSection.rowPayloadDecode_encode]
  change (rows.map RuntimeResidualRow.toNatList).mapM RuntimeResidualRow.ofNatList = some rows
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, List.mapM_cons, RuntimeResidualRow.ofNatList_toNatList, ih]
      rfl

def finEncoding : FinEncoding (List RuntimeResidualRow) where
  Γ := Option Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

@[simp]
theorem encode_append (left right : List RuntimeResidualRow) :
    encode (left ++ right) = encode left ++ encode right := by
  simp [encode, DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
    SourceOrderRawFields.encode]

abbrev Value := ℕ × List RuntimeResidualRow

def countedFinEncoding : FinEncoding Value :=
  LeanNPHardness.PairEncoding.finEncoding unaryFinEncodingNat finEncoding

/-- Positive pinning rows precede every negative edge row. -/
def assemble (input : PositiveCandidateQueries.Input) : Value :=
  (input.2.1.1.1.2, input.2.2.map PositiveRows.row ++ NegativeRows.rows input.2.1.2.1)

def ofRuntimeSystem (C : RuntimeSystem) : Value :=
  (C.domains.length, (compileUsingDomainEntryBound C).rows)

theorem assemble_result (C : RuntimeSystem) :
    assemble (PositiveScanLoop.result (CountedPositiveSections.ofRuntimeSystem C)) =
      ofRuntimeSystem C := by
  apply Prod.ext
  · rfl
  · change (PositiveScanLoop.result (CountedPositiveSections.ofRuntimeSystem C)).2.2.map
      PositiveRows.row ++ NegativeRows.rows (PrimalEdgeEnumeration.ofRuntimeSystem C) = _
    rw [PositiveScanLoop.result_ofRuntimeSystem, NegativeRows.rows_enumerate_eq]
    simp [ofRuntimeSystem, compileUsingDomainEntryBound, RuntimeObjective.ofCompiled,
      AllDifferentCSP.ExplicitSystem.compileObjectiveAt,
      AllDifferentCSP.ExplicitSystem.compileObjective]

theorem encode_assemble (input : PositiveCandidateQueries.Input) :
    countedFinEncoding.encode (assemble input) =
      (unaryEncodeNat input.2.1.1.1.2).map Sum.inl ++
      (PositiveRows.outputEncode input.2.2).map Sum.inr ++
      (NegativeRows.outputEncode input.2.1.2.1).map Sum.inr := by
  simp only [countedFinEncoding, LeanNPHardness.PairEncoding.finEncoding,
    finEncoding, unaryFinEncodingNat, assemble]
  rw [encode_append]
  simp only [encode, ← PositiveRows.outputEncode_eq_rows, ← NegativeRows.outputEncode_eq_rows,
    List.map_append, List.append_assoc]

/-- This includes the retained variable header and both complete row streams. -/
theorem output_length (input : PositiveCandidateQueries.Input) :
    (countedFinEncoding.encode (assemble input)).length =
      input.2.1.1.1.2 + (PositiveRows.outputEncode input.2.2).length +
        (NegativeRows.outputEncode input.2.1.2.1).length := by
  rw [encode_assemble]
  simp [unaryEncodeNat_eq_replicate_true, Nat.add_assoc]

example : assemble ((9, 7), (((([], 0), 3), [[]]), ([(0, 2)], 4)),
    [((0, 1), 4), ((2, 1), 4)]) =
      (3, [.pin 0 1 4, .pin 2 1 4, .unequal 0 2]) := rfl
example : assemble ((0, 0), (((([], 0), 5), []), ([], 1)), []) = (5, []) := rfl
example : decode (DomainFieldSection.rowPayloadEncode [[0, 1, 2]]) = none := by
  simp [decode, RuntimeResidualRow.ofNatList]
example : decode (encode [.pin 0 1000000 999999, .unequal 0 7]) =
    some [.pin 0 1000000 999999, .unequal 0 7] := decode_encode _

end ObjectiveRows

namespace ObjectiveRowsMachine

abbrev Input := PositiveCandidateQueriesMachine.Input
abbrev Output := Sum Bool (Option Bool)
abbrev State := Option Input × Option Output

inductive Stack
  | input | count | positive | negative | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | emitNegative | emitPositive | emitCount
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input | _ => Output

/-- Select only the original unary variable count. -/
def countCell : Input → Option Output
  | .inr (.inl (.inl (.inl (.inr bit)))) => some (.inl bit)
  | _ => none

def positiveCell : Input → Option Output
  | .inr (.inr cell) => some (.inr cell)
  | _ => none

def negativeCell : Input → Option Output
  | .inr (.inl (.inr (.inl cell))) => some (.inr cell)
  | _ => none

private def observe (_ : State) (cell : Option Input) : State := (cell, none)
private def remember (_ : State) (cell : Option Output) : State := (none, cell)
private def held (s : State) : Input := s.1.getD (.inr (.inr none))
private def out (s : State) : Output := s.2.getD (.inr none)

private def save (select : Input → Option Output) (stack : Stack)
    (h : Alphabet stack = Output) (next : TM2.Stmt Alphabet Label State) :
    TM2.Stmt Alphabet Label State :=
  .branch (fun s => (select (held s)).isSome)
    (.push stack (fun s => h.symm ▸ (select (held s)).getD (.inr none)) next) next

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch (fun s => s.1.isSome)
      (save countCell .count rfl <| save positiveCell .positive rfl <|
        save negativeCell .negative rfl <| .goto fun _ => .scan)
      (.goto fun _ => .emitNegative)
  | .emitNegative => .pop .negative remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitNegative)
      (.goto fun _ => .emitPositive)
  | .emitPositive => .pop .positive remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitPositive)
      (.goto fun _ => .emitCount)
  | .emitCount => .pop .count remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitCount)
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

private def stackContents (input : List Input) (count positive negative output : List Output) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .count => count | .positive => positive
  | .negative => negative | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (count positive negative output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input count positive negative output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using! h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using! EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "rows_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe, remember,
    held, out, save, countCell, positiveCell, negativeCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Input) (count positive negative output : List Output) (state : State) :
    Run (cfg (some .scan) state input count positive negative output)
      (cfg (some .emitNegative) (none, none) []
        ((input.filterMap countCell).reverse ++ count)
        ((input.filterMap positiveCell).reverse ++ positive)
        ((input.filterMap negativeCell).reverse ++ negative) output) (input.length + 1) := by
  induction input generalizing count positive negative state with
  | nil => exact one (by rows_step)
  | cons cell input ih =>
      have step : Run (cfg (some .scan) state (cell :: input) count positive negative output)
          (cfg (some .scan) (some cell, none) input
            ((countCell cell).toList ++ count) ((positiveCell cell).toList ++ positive)
            ((negativeCell cell).toList ++ negative) output) 1 := by
        apply one
        rcases cell with (a | (((((b | c) | d) | e) | (f | g)) | h)) <;> rows_step
      have run := seq step (ih ((countCell cell).toList ++ count) ((positiveCell cell).toList ++ positive)
        ((negativeCell cell).toList ++ negative) (some cell, none))
      cases hc : countCell cell <;> cases hp : positiveCell cell <;> cases hn : negativeCell cell <;>
        simpa [List.filterMap_cons, hc, hp, hn, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

private def emitNegative_run (negative output count positive : List Output) (state : State) :
    Run (cfg (some .emitNegative) state [] count positive negative output)
      (cfg (some .emitPositive) (none, none) [] count positive [] (negative.reverse ++ output))
      (negative.length + 1) := by
  induction negative generalizing output state with
  | nil => exact one (by rows_step)
  | cons cell negative ih =>
      have step : Run (cfg (some .emitNegative) state [] count positive (cell :: negative) output)
          (cfg (some .emitNegative) (none, some cell) [] count positive negative (cell :: output)) 1 :=
        one (by rows_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq step (ih (cell :: output) (none, some cell))

private def emitPositive_run (positive output count : List Output) (state : State) :
    Run (cfg (some .emitPositive) state [] count positive [] output)
      (cfg (some .emitCount) (none, none) [] count [] [] (positive.reverse ++ output))
      (positive.length + 1) := by
  induction positive generalizing output state with
  | nil => exact one (by rows_step)
  | cons cell positive ih =>
      have step : Run (cfg (some .emitPositive) state [] count (cell :: positive) [] output)
          (cfg (some .emitPositive) (none, some cell) [] count positive [] (cell :: output)) 1 :=
        one (by rows_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq step (ih (cell :: output) (none, some cell))

private def emitCount_run (count output : List Output) (state : State) :
    Run (cfg (some .emitCount) state [] count [] [] output)
      (cfg none (none, none) [] [] [] [] (count.reverse ++ output)) (count.length + 1) := by
  induction count generalizing output state with
  | nil => exact one (by rows_step)
  | cons cell count ih =>
      have step : Run (cfg (some .emitCount) state [] (cell :: count) [] [] output)
          (cfg (some .emitCount) (none, some cell) [] count [] [] (cell :: output)) 1 := one (by rows_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq step (ih (cell :: output) (none, some cell))

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

private theorem select_count (input : PositiveCandidateQueries.Input) :
    (PositiveCandidateQueries.inputFinEncoding.encode input).filterMap countCell =
      (unaryEncodeNat input.2.1.1.1.2).map Sum.inl := by
  simp [PositiveCandidateQueries.inputFinEncoding, PositiveCandidateQueries.retainedFinEncoding,
    CountedPositiveSections.finEncoding, CountedPositiveSections.sectionsFinEncoding,
    CountedPositiveSections.domainsFinEncoding, OccurrenceCount.finEncoding,
    PinningWeight.negativeFinEncoding, LeanNPHardness.PairEncoding.finEncoding,
    List.filterMap_map, Function.comp_def, countCell, unaryFinEncodingNat]

private theorem select_positive (input : PositiveCandidateQueries.Input) :
    (PositiveCandidateQueries.inputFinEncoding.encode input).filterMap positiveCell =
      (PositiveRows.outputEncode input.2.2).map Sum.inr := by
  simp [PositiveCandidateQueries.inputFinEncoding, PositiveCandidateQueries.retainedFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding, PositiveRows.outputFinEncoding,
    List.filterMap_map, Function.comp_def, positiveCell]

private theorem select_negative (input : PositiveCandidateQueries.Input) :
    (PositiveCandidateQueries.inputFinEncoding.encode input).filterMap negativeCell =
      (NegativeRows.outputEncode input.2.1.2.1).map Sum.inr := by
  simp [PositiveCandidateQueries.inputFinEncoding, PositiveCandidateQueries.retainedFinEncoding,
    CountedPositiveSections.finEncoding, PinningWeight.negativeFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding, NegativeRows.outputFinEncoding,
    List.filterMap_map, Function.comp_def, negativeCell]

theorem output_length_le (input : PositiveCandidateQueries.Input) :
    (ObjectiveRows.countedFinEncoding.encode (ObjectiveRows.assemble input)).length ≤
      (PositiveCandidateQueries.inputFinEncoding.encode input).length := by
  rw [ObjectiveRows.output_length]
  simp [PositiveCandidateQueries.inputFinEncoding, PositiveCandidateQueries.retainedFinEncoding,
    CountedPositiveSections.finEncoding, CountedPositiveSections.sectionsFinEncoding,
    CountedPositiveSections.domainsFinEncoding, OccurrenceCount.finEncoding,
    PinningWeight.negativeFinEncoding, PositiveRows.outputFinEncoding, NegativeRows.outputFinEncoding,
    unaryFinEncodingNat, unaryEncodeNat_eq_replicate_true]
  omega

/-- Exact output, with all non-output stacks cleared, in at most `2s+4` steps. -/
def outputsInTime (input : PositiveCandidateQueries.Input) :
    TM2OutputsInTime computer (PositiveCandidateQueries.inputFinEncoding.encode input)
      (some (ObjectiveRows.countedFinEncoding.encode (ObjectiveRows.assemble input)))
      (2 * (PositiveCandidateQueries.inputFinEncoding.encode input).length + 4) := by
  let wire := PositiveCandidateQueries.inputFinEncoding.encode input
  have hs := scan_run wire [] [] [] [] (none, none)
  have hn := emitNegative_run (wire.filterMap negativeCell).reverse []
    (wire.filterMap countCell).reverse (wire.filterMap positiveCell).reverse (none, none)
  have hp := emitPositive_run (wire.filterMap positiveCell).reverse
    (wire.filterMap negativeCell) (wire.filterMap countCell).reverse (none, none)
  have hc := emitCount_run (wire.filterMap countCell).reverse
    (wire.filterMap positiveCell ++ wire.filterMap negativeCell) (none, none)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hs hn hp hc
  have run := seq (seq (seq hs hn) hp) hc
  dsimp only [wire] at run
  rw [select_count, select_positive, select_negative] at run
  rw [TM2OutputsInTime, init_eq]
  simp only [Option.map_some, halt_eq]
  rw [ObjectiveRows.encode_assemble, List.append_assoc]
  apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono run
  have h := output_length_le input
  rw [ObjectiveRows.output_length] at h
  simp only [List.length_map, unaryEncodeNat_eq_replicate_true, List.length_replicate]
  omega

end ObjectiveRowsMachine

/-- Collect both already-emitted row streams and retain the original variable count. -/
noncomputable def objectiveRowsComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveCandidateQueries.Input ObjectiveRows.Value
      PositiveCandidateQueries.inputFinEncoding ObjectiveRows.countedFinEncoding ObjectiveRows.assemble where
  tm := ObjectiveRowsMachine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 4
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using ObjectiveRowsMachine.outputsInTime input

/-- Actual Boolean compiler input to the exact complete semantic residual-row list. -/
noncomputable def runtimeCompilerObjectiveRowsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem ObjectiveRows.Value
      RuntimeCompilerInput.finEncoding ObjectiveRows.countedFinEncoding ObjectiveRows.ofRuntimeSystem := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerPositiveEnumerationComputableInPolyTime objectiveRowsComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa only [Function.comp_def, ObjectiveRows.assemble_result] using composed.outputsFun C }

theorem ObjectiveRows.result_length_le_cubic (value : CountedPositiveSections.Value) :
    (ObjectiveRows.countedFinEncoding.encode (ObjectiveRows.assemble (PositiveScanLoop.result value))).length ≤
      16 * ((CountedPositiveSections.finEncoding.encode value).length + 1) ^ 3 :=
  (ObjectiveRowsMachine.output_length_le _).trans (PositiveScanLoop.result_length_le_cubic value)

#print axioms ObjectiveRows.decode_encode
#print axioms ObjectiveRows.assemble_result
#print axioms ObjectiveRows.encode_assemble
#print axioms ObjectiveRowsMachine.output_length_le
#print axioms ObjectiveRowsMachine.outputsInTime
#print axioms objectiveRowsComputableInPolyTime
#print axioms runtimeCompilerObjectiveRowsComputableInPolyTime
#print axioms ObjectiveRows.result_length_le_cubic

end PhdThesisLean.AllDifferentCSPMachine
