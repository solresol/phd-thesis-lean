import PhdThesisLean.AllDifferentCSPOccurrenceStep

/-!
# Append a relabelled occurrence to the retained output

The finite machine moves one emitted record after the previously emitted
records, preserving their order and the entire next occurrence/symbol source.
It only routes existing finite-alphabet cells; all copies, order restoration,
and work-stack cleanup are included in its linear time bound.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace OccurrenceAccumulator

abbrev Input := OccurrenceEmit.Output × List (ℕ × ℕ)
abbrev Output := DomainSymbolExtraction.Value × List (ℕ × ℕ)

def inputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding OccurrenceEmit.outputFinEncoding
    DomainFieldRow.outputFinEncoding

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding DomainSymbolExtraction.finEncoding
    DomainFieldRow.outputFinEncoding

/-- Preserve the source and append the new record in original occurrence order. -/
def appendRecord (input : Input) : Output := (input.1.2, input.2 ++ [input.1.1])

theorem output_length (input : Input) :
    (outputFinEncoding.encode (appendRecord input)).length =
      (inputFinEncoding.encode input).length := by
  simp [outputFinEncoding, inputFinEncoding, appendRecord, OccurrenceEmit.outputFinEncoding,
    DomainFieldRow.outputFinEncoding, DomainFieldRow.outputEncode,
    DomainOccurrenceFieldBlock.outputFinEncoding, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end OccurrenceAccumulator

namespace OccurrenceAccumulatorMachine

abbrev Raw := Option Bool
abbrev Source := Sum Raw Raw
abbrev Input := Sum (Sum Raw Source) Raw
abbrev Output := Sum Source Raw
abbrev State := Option Input × Option Output

inductive Stack
  | input | record | source | accum | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | emitRecord | emitAccum | emitSource
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input | _ => Output

def recordCell : Input → Option Output
  | .inl (.inl bit) => some (.inr bit) | _ => none

def sourceCell : Input → Option Output
  | .inl (.inr bit) => some (.inl bit) | _ => none

def accumCell : Input → Option Output
  | .inr bit => some (.inr bit) | _ => none

private def observe (_ : State) (bit : Option Input) : State := (bit, none)
private def observeOutput (_ : State) (bit : Option Output) : State := (none, bit)
private def cell (s : State) : Input := s.1.getD (.inr none)
private def out (s : State) : Output := s.2.getD (.inr none)

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch (fun s => s.1.isSome)
      (.branch (fun s => (recordCell (cell s)).isSome)
        (.push .record (fun s => (recordCell (cell s)).getD (.inr none)) <| .goto fun _ => .scan)
        (.branch (fun s => (sourceCell (cell s)).isSome)
          (.push .source (fun s => (sourceCell (cell s)).getD (.inr none)) <| .goto fun _ => .scan)
          (.push .accum (fun s => (accumCell (cell s)).getD (.inr none)) <| .goto fun _ => .scan)))
      (.goto fun _ => .emitRecord)
  | .emitRecord => .pop .record observeOutput <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitRecord)
      (.goto fun _ => .emitAccum)
  | .emitAccum => .pop .accum observeOutput <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitAccum)
      (.goto fun _ => .emitSource)
  | .emitSource => .pop .source observeOutput <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitSource)
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

private def stackContents (input : List Input) (record source accum output : List Output) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .record => record | .source => source | .accum => accum | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (record source accum output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input record source accum output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "accum_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe,
    observeOutput, cell, out, recordCell, sourceCell, accumCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Input) (record source accum output : List Output) (state : State) :
    Run (cfg (some .scan) state input record source accum output)
      (cfg (some .emitRecord) (none, none) []
        ((input.filterMap recordCell).reverse ++ record)
        ((input.filterMap sourceCell).reverse ++ source)
        ((input.filterMap accumCell).reverse ++ accum) output) (input.length + 1) := by
  induction input generalizing record source accum state with
  | nil => exact one (by accum_step)
  | cons bit input ih =>
      cases bit with
      | inl bit =>
          cases bit with
          | inl bit =>
              have h : Run (cfg (some .scan) state (.inl (.inl bit) :: input) record source accum output)
                  (cfg (some .scan) (some (.inl (.inl bit)), none) input (.inr bit :: record) source accum output) 1 :=
                one (by accum_step)
              simpa [recordCell, sourceCell, accumCell, List.reverse_cons, List.append_assoc,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih _ _ _ _)
          | inr bit =>
              have h : Run (cfg (some .scan) state (.inl (.inr bit) :: input) record source accum output)
                  (cfg (some .scan) (some (.inl (.inr bit)), none) input record (.inl bit :: source) accum output) 1 :=
                one (by accum_step)
              simpa [recordCell, sourceCell, accumCell, List.reverse_cons, List.append_assoc,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih _ _ _ _)
      | inr bit =>
          have h : Run (cfg (some .scan) state (.inr bit :: input) record source accum output)
              (cfg (some .scan) (some (.inr bit), none) input record source (.inr bit :: accum) output) 1 :=
            one (by accum_step)
          simpa [recordCell, sourceCell, accumCell, List.reverse_cons, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih _ _ _ _)

private def emitRecord_run (record source accum output : List Output) (state : State) :
    Run (cfg (some .emitRecord) state [] record source accum output)
      (cfg (some .emitAccum) (none, none) [] [] source accum (record.reverse ++ output))
      (record.length + 1) := by
  induction record generalizing output state with
  | nil => exact one (by accum_step)
  | cons bit record ih =>
      have h : Run (cfg (some .emitRecord) state [] (bit :: record) source accum output)
          (cfg (some .emitRecord) (none, some bit) [] record source accum (bit :: output)) 1 :=
        one (by accum_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih _ _)

private def emitAccum_run (source accum output : List Output) (state : State) :
    Run (cfg (some .emitAccum) state [] [] source accum output)
      (cfg (some .emitSource) (none, none) [] [] source [] (accum.reverse ++ output))
      (accum.length + 1) := by
  induction accum generalizing output state with
  | nil => exact one (by accum_step)
  | cons bit accum ih =>
      have h : Run (cfg (some .emitAccum) state [] [] source (bit :: accum) output)
          (cfg (some .emitAccum) (none, some bit) [] [] source accum (bit :: output)) 1 :=
        one (by accum_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih _ _)

private def emitSource_run (source output : List Output) (state : State) :
    Run (cfg (some .emitSource) state [] [] source [] output)
      (cfg none (none, none) [] [] [] [] (source.reverse ++ output))
      (source.length + 1) := by
  induction source generalizing output state with
  | nil => exact one (by accum_step)
  | cons bit source ih =>
      have h : Run (cfg (some .emitSource) state [] [] (bit :: source) [] output)
          (cfg (some .emitSource) (none, some bit) [] [] source [] (bit :: output)) 1 :=
        one (by accum_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih _ _)

private theorem partition_length (input : List Input) :
    (input.filterMap recordCell).length + (input.filterMap sourceCell).length +
      (input.filterMap accumCell).length = input.length := by
  induction input with
  | nil => rfl
  | cons bit input ih =>
      cases bit with
      | inl bit => cases bit <;> simp [recordCell, sourceCell, accumCell] <;> omega
      | inr bit => simp [recordCell, sourceCell, accumCell]; omega

private def run (input : List Input) :
    Run (cfg (some .scan) (none, none) input [] [] [] [])
      (cfg none (none, none) [] [] [] []
        (input.filterMap sourceCell ++ input.filterMap accumCell ++ input.filterMap recordCell))
      (2 * input.length + 4) := by
  have hs := scan_run input [] [] [] [] (none, none)
  have hr := emitRecord_run (input.filterMap recordCell).reverse
    (input.filterMap sourceCell).reverse (input.filterMap accumCell).reverse [] (none, none)
  have ha := emitAccum_run (input.filterMap sourceCell).reverse
    (input.filterMap accumCell).reverse (input.filterMap recordCell) (none, none)
  have hf := emitSource_run (input.filterMap sourceCell).reverse
    (input.filterMap accumCell ++ input.filterMap recordCell) (none, none)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hs hr ha hf
  have partition := partition_length input
  convert seq hs (seq hr (seq ha hf)) using 1
  · simp [List.append_assoc]
  · omega

private theorem input_eq (input : List Input) :
    initList computer input = cfg (some .scan) (none, none) input [] [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem output_eq (output : List Output) :
    haltList computer output = cfg none (none, none) [] [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

end OccurrenceAccumulatorMachine

/-- Append one record after the prior output and preserve the next source in
`2s+4` actual finite-machine steps, clearing every non-output stack. -/
def occurrenceAccumulator_outputsInTime (input : OccurrenceAccumulator.Input) :
    TM2OutputsInTime OccurrenceAccumulatorMachine.computer
      (OccurrenceAccumulator.inputFinEncoding.encode input)
      (some (OccurrenceAccumulator.outputFinEncoding.encode (OccurrenceAccumulator.appendRecord input)))
      (2 * (OccurrenceAccumulator.inputFinEncoding.encode input).length + 4) := by
  rw [TM2OutputsInTime, OccurrenceAccumulatorMachine.input_eq]
  simp only [Option.map_some]
  rw [OccurrenceAccumulatorMachine.output_eq]
  have discard {α : Type} (xs : List α) :
      xs.filterMap (fun _ => (none : Option OccurrenceAccumulatorMachine.Output)) = [] := by simp
  have h := OccurrenceAccumulatorMachine.run (OccurrenceAccumulator.inputFinEncoding.encode input)
  simpa [OccurrenceAccumulator.inputFinEncoding, OccurrenceAccumulator.outputFinEncoding,
    OccurrenceAccumulator.appendRecord, OccurrenceEmit.outputFinEncoding,
    DomainFieldRow.outputFinEncoding, DomainFieldRow.outputEncode,
    DomainOccurrenceFieldBlock.outputFinEncoding, OccurrenceAccumulatorMachine.recordCell,
    OccurrenceAccumulatorMachine.sourceCell, OccurrenceAccumulatorMachine.accumCell,
    List.filterMap_map, Function.comp_def, List.append_assoc, discard] using h

noncomputable def occurrenceAccumulatorComputableInPolyTime :
    @TM2ComputableInPolyTime OccurrenceAccumulator.Input OccurrenceAccumulator.Output
      OccurrenceAccumulator.inputFinEncoding OccurrenceAccumulator.outputFinEncoding
      OccurrenceAccumulator.appendRecord where
  tm := OccurrenceAccumulatorMachine.computer
  inputAlphabet := Equiv.refl OccurrenceAccumulatorMachine.Input
  outputAlphabet := Equiv.refl OccurrenceAccumulatorMachine.Output
  time := 2 * Polynomial.X + 4
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using occurrenceAccumulator_outputsInTime input

#print axioms OccurrenceAccumulator.output_length
#print axioms occurrenceAccumulator_outputsInTime
#print axioms occurrenceAccumulatorComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
