import PhdThesisLean.AllDifferentCSPObjectiveHeader
import PhdThesisLean.AllDifferentCSPObjectiveEncoding

/-!
# Attach the computed binary header and serialize the complete objective

The binary prime and variable fields arrive reversed, as required by the
existing counter. This finite pass restores their source order, prefixes the
header arity, and appends every residual row unchanged. The checked serializer
then computes the outer row count and frames the exact Boolean output.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace ObjectiveHeader

def assemble (value : Value) : RuntimeObjective := ⟨value.2.1, value.1, value.2.2⟩

theorem assemble_ofRuntimeSystem (C : RuntimeSystem) :
    assemble (ofRuntimeSystem C) = compileUsingDomainEntryBound C := rfl

private theorem arity_eq : SourceOrderRawFields.encode [2] = [none, some false, some true] := rfl

private theorem arity_length : (SourceOrderRawFields.encode [2]).length = 3 := rfl

/-- The field reversal includes each field's delimiter. -/
theorem payload_assemble (value : Value) :
    ObjectiveEncoding.payloadEncode (assemble value) =
      SourceOrderRawFields.encode [2] ++
        (RawNatList.segment (encodeNat value.2.1)).reverse ++
        (RawNatList.segment (encodeNat value.1)).reverse ++
        ObjectiveRows.encode value.2.2 := by
  simp [ObjectiveEncoding.payloadEncode, assemble, RuntimeObjective.toNatLists,
    DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
    SourceOrderRawFields.encode, RawNatList.segment, ObjectiveRows.encode, List.reverse_append, List.map_reverse,
    List.append_assoc]

theorem payload_length (value : Value) :
    (ObjectiveEncoding.payloadEncode (assemble value)).length =
      (finEncoding.encode value).length + 3 := by
  rw [payload_assemble, encoded_length]
  simp only [List.length_append, List.length_reverse, RawNatList.segment, List.length_map,
    List.length_singleton, arity_length]
  omega

end ObjectiveHeader

namespace ObjectiveAssemblyMachine

abbrev Cell := Option Bool
abbrev Input := Sum Cell (Sum Cell Cell)
abbrev State := Option Input × Option Cell

inductive Stack
  | input | header | work | rows | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | emitRows | reverseHeader | emitHeader
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input | _ => Cell

def headerCell : Input → Option Cell
  | .inl cell | .inr (.inl cell) => some cell
  | _ => none

def rowCell : Input → Option Cell
  | .inr (.inr cell) => some cell
  | _ => none

private def observe (_ : State) (cell : Option Input) : State := (cell, none)
private def remember (_ : State) (cell : Option Cell) : State := (none, cell)
private def held (s : State) : Input := s.1.getD (.inl none)
private def out (s : State) : Cell := s.2.getD none

/-- Reverse the two binary fields together, restore rows, then add arity two. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch (fun s => s.1.isSome)
      (.branch (fun s => (headerCell (held s)).isSome)
        (.push .header (fun s => (headerCell (held s)).getD none) <| .goto fun _ => .scan)
        (.push .rows (fun s => (rowCell (held s)).getD none) <| .goto fun _ => .scan))
      (.goto fun _ => .emitRows)
  | .emitRows => .pop .rows remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitRows)
      (.goto fun _ => .reverseHeader)
  | .reverseHeader => .pop .header remember <| .branch (fun s => s.2.isSome)
      (.push .work out <| .goto fun _ => .reverseHeader)
      (.goto fun _ => .emitHeader)
  | .emitHeader => .pop .work remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitHeader)
      (.push .output (fun _ => some true) <| .push .output (fun _ => some false) <|
        .push .output (fun _ => none) <| .load (fun _ => (none, none)) .halt)

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

private def stackContents (input : List Input) (header work rows output : List Cell) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .header => header | .work => work | .rows => rows | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (header work rows output : List Cell) : computer.Cfg :=
  ⟨label, state, stackContents input header work rows output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using! h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using! EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "assembly_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe, remember,
    held, out, headerCell, rowCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Input) (header work rows output : List Cell) (state : State) :
    Run (cfg (some .scan) state input header work rows output)
      (cfg (some .emitRows) (none, none) []
        ((input.filterMap headerCell).reverse ++ header) work
        ((input.filterMap rowCell).reverse ++ rows) output) (input.length + 1) := by
  induction input generalizing header rows state with
  | nil => exact one (by assembly_step)
  | cons cell input ih =>
      have step : Run (cfg (some .scan) state (cell :: input) header work rows output)
          (cfg (some .scan) (some cell, none) input
            ((headerCell cell).toList ++ header) work ((rowCell cell).toList ++ rows) output) 1 := by
        apply one
        rcases cell with (a | (b | c)) <;> assembly_step
      have run := seq step (ih ((headerCell cell).toList ++ header)
        ((rowCell cell).toList ++ rows) (some cell, none))
      rcases cell with (a | (b | c)) <;>
        simpa [headerCell, rowCell, List.reverse_cons, List.append_assoc, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using run

private def rows_run (rows output header work : List Cell) (state : State) :
    Run (cfg (some .emitRows) state [] header work rows output)
      (cfg (some .reverseHeader) (none, none) [] header work [] (rows.reverse ++ output))
      (rows.length + 1) := by
  induction rows generalizing output state with
  | nil => exact one (by assembly_step)
  | cons cell rows ih =>
      have step : Run (cfg (some .emitRows) state [] header work (cell :: rows) output)
          (cfg (some .emitRows) (none, some cell) [] header work rows (cell :: output)) 1 :=
        one (by assembly_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq step (ih (cell :: output) (none, some cell))

private def reverse_run (header work output : List Cell) (state : State) :
    Run (cfg (some .reverseHeader) state [] header work [] output)
      (cfg (some .emitHeader) (none, none) [] [] (header.reverse ++ work) [] output)
      (header.length + 1) := by
  induction header generalizing work state with
  | nil => exact one (by assembly_step)
  | cons cell header ih =>
      have step : Run (cfg (some .reverseHeader) state [] (cell :: header) work [] output)
          (cfg (some .reverseHeader) (none, some cell) [] header (cell :: work) [] output) 1 :=
        one (by assembly_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq step (ih (cell :: work) (none, some cell))

private def header_run (work output : List Cell) (state : State) :
    Run (cfg (some .emitHeader) state [] [] work [] output)
      (cfg none (none, none) [] [] [] []
        (SourceOrderRawFields.encode [2] ++ work.reverse ++ output)) (work.length + 1) := by
  induction work generalizing output state with
  | nil => apply one; rw [ObjectiveHeader.arity_eq]; assembly_step
  | cons cell work ih =>
      have step : Run (cfg (some .emitHeader) state [] [] (cell :: work) [] output)
          (cfg (some .emitHeader) (none, some cell) [] [] work [] (cell :: output)) 1 :=
        one (by assembly_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq step (ih (cell :: output) (none, some cell))

private theorem header_filter (value : ObjectiveHeader.Value) :
    (ObjectiveHeader.finEncoding.encode value).filterMap headerCell =
      RawNatList.segment (encodeNat value.1) ++
        RawNatList.segment (encodeNat value.2.1) := by
  simp [ObjectiveHeader.finEncoding, ObjectiveHeader.rowsFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding, List.filterMap_map, Function.comp_def, headerCell, UnaryBoundEncoding.outputFinEncoding]

private theorem rows_filter (value : ObjectiveHeader.Value) :
    (ObjectiveHeader.finEncoding.encode value).filterMap rowCell = ObjectiveRows.encode value.2.2 := by
  simp [ObjectiveHeader.finEncoding, ObjectiveHeader.rowsFinEncoding, ObjectiveRows.finEncoding,
    LeanNPHardness.PairEncoding.finEncoding, List.filterMap_map, Function.comp_def, rowCell]

/-- All field reversals, row transfers, the arity prefix and cleanup are charged. -/
def outputsInTime (value : ObjectiveHeader.Value) :
    TM2OutputsInTime computer (ObjectiveHeader.finEncoding.encode value)
      (some (ObjectiveEncoding.payloadEncode (ObjectiveHeader.assemble value)))
      (3 * (ObjectiveHeader.finEncoding.encode value).length + 4) := by
  let wire := ObjectiveHeader.finEncoding.encode value
  have hs := scan_run wire [] [] [] [] (none, none)
  have hr := rows_run (wire.filterMap rowCell).reverse [] (wire.filterMap headerCell).reverse [] (none, none)
  have hv := reverse_run (wire.filterMap headerCell).reverse [] (wire.filterMap rowCell) (none, none)
  have hh := header_run (wire.filterMap headerCell) (wire.filterMap rowCell) (none, none)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hs hr hv
  have run := seq (seq (seq hs hr) hv) hh
  have hi : initList computer wire = cfg (some .scan) (none, none) wire [] [] [] [] := by
    simp only [initList, computer, cfg]
    congr 1
    funext k
    cases k <;> rfl
  have ho : haltList computer (ObjectiveEncoding.payloadEncode (ObjectiveHeader.assemble value)) =
      cfg none (none, none) [] [] [] [] (ObjectiveEncoding.payloadEncode (ObjectiveHeader.assemble value)) := by
    simp only [haltList, computer, cfg]
    congr 1
    funext k
    cases k <;> rfl
  have hout : SourceOrderRawFields.encode [2] ++ (wire.filterMap headerCell).reverse ++
      wire.filterMap rowCell = ObjectiveEncoding.payloadEncode (ObjectiveHeader.assemble value) := by
    dsimp only [wire]
    rw [header_filter, rows_filter, ObjectiveHeader.payload_assemble, List.reverse_append]
    simp only [List.append_assoc]
  rw [hout] at run
  rw [TM2OutputsInTime, hi]
  simp only [Option.map_some, ho]
  apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono run
  have hheader := List.length_filterMap_le headerCell wire
  have hrows := List.length_filterMap_le rowCell wire
  have hsum : (wire.filterMap headerCell).length + (wire.filterMap rowCell).length = wire.length := by
    dsimp only [wire]
    rw [header_filter, rows_filter, ObjectiveHeader.encoded_length]
    simp [RawNatList.segment, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  dsimp only [wire] at *
  omega

end ObjectiveAssemblyMachine

/-- The exact full objective payload, including its computed variable/prime header. -/
noncomputable def objectiveAssemblyComputableInPolyTime :
    @TM2ComputableInPolyTime ObjectiveHeader.Value RuntimeObjective
      ObjectiveHeader.finEncoding ObjectiveEncoding.payloadFinEncoding ObjectiveHeader.assemble where
  tm := ObjectiveAssemblyMachine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 4
  outputsFun value := by
    simpa [Equiv.refl, ObjectiveEncoding.payloadFinEncoding, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X] using
      ObjectiveAssemblyMachine.outputsInTime value

/-- Complete compilation from actual Boolean input to actual Boolean objective output. -/
noncomputable def runtimeCompilerComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem RuntimeObjective
      RuntimeCompilerInput.finEncoding RuntimeObjective.finEncoding compileUsingDomainEntryBound := by
  let payload := compositionComputableInPolyTime _ _ _ _ _
    ObjectiveHeader.runtimeCompilerComputableInPolyTime objectiveAssemblyComputableInPolyTime
  let complete := compositionComputableInPolyTime _ _ _ _ _ payload ObjectiveEncoding.computableInPolyTime
  exact { complete with
    outputsFun := fun C => by
      simpa only [Function.comp_def, id_eq, ObjectiveHeader.assemble_ofRuntimeSystem] using complete.outputsFun C }

example : ObjectiveHeader.assemble (2, 0, []) = ⟨0, 2, []⟩ := rfl
example : ObjectiveHeader.assemble (7, 3, [.pin 0 1 4, .unequal 0 2]) =
    ⟨3, 7, [.pin 0 1 4, .unequal 0 2]⟩ := rfl

#print axioms ObjectiveHeader.assemble_ofRuntimeSystem
#print axioms ObjectiveHeader.payload_assemble
#print axioms ObjectiveHeader.payload_length
#print axioms ObjectiveAssemblyMachine.outputsInTime
#print axioms objectiveAssemblyComputableInPolyTime
#print axioms runtimeCompilerComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
