import PhdThesisLean.AllDifferentCSPEdgeCount

/-!
# Compute the exact binary pinning weight while retaining compiler sections

Append one unary mark to the internally counted edges, route those marks into
the existing binary-header machine, and compose the checked negative-row pass.
Every data transfer and binary carry is included in the machine witnesses.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PinningWeight

def preparedFinEncoding : FinEncoding EdgeCount.Value :=
  LeanNPHardness.PairEncoding.finEncoding NegativeRows.inputFinEncoding
    UnaryBoundEncoding.inputFinEncoding

def binaryFinEncoding : FinEncoding EdgeCount.Value :=
  LeanNPHardness.PairEncoding.finEncoding NegativeRows.inputFinEncoding
    UnaryBoundEncoding.outputFinEncoding

def negativeFinEncoding : FinEncoding EdgeCount.Value :=
  LeanNPHardness.PairEncoding.finEncoding NegativeRows.outputFinEncoding
    UnaryBoundEncoding.outputFinEncoding

def increment (value : EdgeCount.Value) : EdgeCount.Value := (value.1, value.2 + 1)

def retain (edges : List (ℕ × ℕ)) : EdgeCount.Value := (edges, edges.length + 1)

/-- Every binary weight bit, its delimiter, and all edge cells are included. -/
theorem binary_length (edges : List (ℕ × ℕ)) :
    (binaryFinEncoding.encode (retain edges)).length =
      (NegativeRows.inputEncode edges).length + (encodeNat (edges.length + 1)).length + 1 := by
  simp [binaryFinEncoding, retain, NegativeRows.inputFinEncoding, UnaryBoundEncoding.output_length, Nat.add_assoc]

theorem binary_length_le (edges : List (ℕ × ℕ)) :
    (binaryFinEncoding.encode (retain edges)).length ≤
      2 * (NegativeRows.inputEncode edges).length + 2 := by
  rw [binary_length]
  have h := EdgeCount.count_le_input_length edges
  have hb := BinaryNatLists.encodeNat_length_le (edges.length + 1)
  omega

theorem weight_eq (C : RuntimeSystem) :
    (retain (PrimalEdgeEnumeration.ofRuntimeSystem C)).2 = C.toExplicitSystem.pinningWeight :=
  (NegativeRows.pinningWeight_eq_edgeCount C).symm

example : retain [] = ([], 1) := rfl
example : retain [(0, 1), (1, 2), (2, 3)] = ([(0, 1), (1, 2), (2, 3)], 4) := rfl

end PinningWeight

namespace PinningWeightMachine

abbrev Query := Sum (Option Bool) Bool
abbrev Output := Sum (Option Bool) StructuralBinaryHeaderMachine.Tagged

/-- Keep endpoints on the left and route unary marks to the binary counter. -/
def lift : Query → Output
  | .inl cell => .inl cell
  | .inr bit => .inr (.inr bit)

inductive Stack
  | input | saved | output
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input | .saved => Query | .output => Output

inductive Label
  | copy | emit
  deriving DecidableEq, Fintype

abbrev State := Option Query

def program : Label → TM2.Stmt Alphabet Label State
  | .copy => .pop .input (fun _ cell => cell) <|
      .branch Option.isSome
        (.push .saved (fun cell => cell.getD (.inl none)) <| .goto fun _ => .copy)
        (.push .output (fun _ => .inr (.inr true)) <| .goto fun _ => .emit)
  | .emit => .pop .saved (fun _ cell => cell) <|
      .branch Option.isSome
        (.push .output (fun cell => lift (cell.getD (.inl none))) <| .goto fun _ => .emit)
        (.load (fun _ => none) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .copy
  σ := State
  initialState := none
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input saved : List Query) (output : List Output) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .saved => saved | .output => output

private def cfg (label : Option Label) (state : State) (input saved : List Query)
    (output : List Output) : computer.Cfg := ⟨label, state, stackContents input saved output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "weight_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def copy_run (input saved : List Query) (state : State) :
    Run (cfg (some .copy) state input saved [])
      (cfg (some .emit) none [] (input.reverse ++ saved) [.inr (.inr true)]) (input.length + 1) := by
  induction input generalizing saved state with
  | nil => exact one (by weight_step)
  | cons cell input ih =>
      have h : Run (cfg (some .copy) state (cell :: input) saved [])
          (cfg (some .copy) (some cell) input (cell :: saved) []) 1 := one (by weight_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (cell :: saved) (some cell))

private def emit_run (saved : List Query) (output : List Output) (state : State) :
    Run (cfg (some .emit) state [] saved output)
      (cfg none none [] [] (saved.reverse.map lift ++ output)) (saved.length + 1) := by
  induction saved generalizing output state with
  | nil => exact one (by weight_step)
  | cons cell saved ih =>
      have h : Run (cfg (some .emit) state [] (cell :: saved) output)
          (cfg (some .emit) (some cell) [] saved (lift cell :: output)) 1 := one (by weight_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (lift cell :: output) (some cell))

private def run (input : List Query) :
    Run (cfg (some .copy) none input [] [])
      (cfg none none [] [] (input.map lift ++ [.inr (.inr true)])) (2 * input.length + 2) := by
  have hc := copy_run input [] none
  have he := emit_run input.reverse [.inr (.inr true)] none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hc he
  convert seq hc he using 1
  omega

private theorem init_eq (input : List Query) :
    initList computer input = cfg (some .copy) none input [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none none [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

end PinningWeightMachine

theorem PinningWeight.prepared_encode (value : EdgeCount.Value) :
    preparedFinEncoding.encode (increment value) =
      (EdgeCount.finEncoding.encode value).map PinningWeightMachine.lift ++ [.inr (.inr true)] := by
  simp [preparedFinEncoding, increment, EdgeCount.finEncoding,
    UnaryBoundEncoding.inputFinEncoding, unaryFinEncodingNat,
    unaryEncodeNat_eq_replicate_true, List.map_map, Function.comp_def,
    PinningWeightMachine.lift, List.replicate_succ', List.append_assoc]

/-- Retain all edge cells and append the extra mark in exactly `2s+2` steps. -/
def pinningWeightPrepare_outputsInTime (value : EdgeCount.Value) :
    TM2OutputsInTime PinningWeightMachine.computer (EdgeCount.finEncoding.encode value)
      (some (PinningWeight.preparedFinEncoding.encode (PinningWeight.increment value)))
      (2 * (EdgeCount.finEncoding.encode value).length + 2) := by
  rw [TM2OutputsInTime, PinningWeightMachine.init_eq]
  simp only [Option.map_some, PinningWeightMachine.halt_eq, PinningWeight.prepared_encode]
  exact PinningWeightMachine.run _

noncomputable def pinningWeightPrepareComputableInPolyTime :
    @TM2ComputableInPolyTime EdgeCount.Value EdgeCount.Value EdgeCount.finEncoding
      PinningWeight.preparedFinEncoding PinningWeight.increment where
  tm := PinningWeightMachine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun value := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using pinningWeightPrepare_outputsInTime value

/-- Convert the computed edge tally plus one to its exact binary field. -/
noncomputable def pinningWeightBinaryComputableInPolyTime :
    @TM2ComputableInPolyTime EdgeCount.Value EdgeCount.Value EdgeCount.finEncoding
      PinningWeight.binaryFinEncoding PinningWeight.increment := by
  let binary := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    NegativeRows.inputFinEncoding UnaryBoundEncoding.inputFinEncoding
    UnaryBoundEncoding.outputFinEncoding id unaryBoundComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _
    pinningWeightPrepareComputableInPolyTime binary
  exact { composed with
    outputsFun := fun value => by simpa only [Function.comp_def, id_eq] using composed.outputsFun value }

/-- No count is supplied by the caller: count the edge rows before binary conversion. -/
noncomputable def pinningWeightComputableInPolyTime :
    @TM2ComputableInPolyTime (List (ℕ × ℕ)) EdgeCount.Value NegativeRows.inputFinEncoding
      PinningWeight.binaryFinEncoding PinningWeight.retain :=
  compositionComputableInPolyTime _ _ _ _ _ EdgeCount.computableInPolyTime
    pinningWeightBinaryComputableInPolyTime

/-- Emit the exact negative rows while retaining the binary pinning field. -/
noncomputable def negativeRowsWithWeightComputableInPolyTime :
    @TM2ComputableInPolyTime (List (ℕ × ℕ)) EdgeCount.Value NegativeRows.inputFinEncoding
      PinningWeight.negativeFinEncoding PinningWeight.retain := by
  let emit := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    NegativeRows.inputFinEncoding NegativeRows.outputFinEncoding
    UnaryBoundEncoding.outputFinEncoding id negativeRowsComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _ pinningWeightComputableInPolyTime emit
  exact { composed with
    outputsFun := fun edges => by simpa only [Function.comp_def, id_eq] using composed.outputsFun edges }

namespace WeightedGraphSections

abbrev Value := CountedGraphSections.Value

def finEncoding : FinEncoding Value :=
  LeanNPHardness.PairEncoding.finEncoding BoundedRelabelledSections.finEncoding
    PinningWeight.negativeFinEncoding

def ofRuntimeSystem (C : RuntimeSystem) : Value :=
  (BoundedRelabelledSections.ofRuntimeSystem C,
    PinningWeight.retain (PrimalEdgeEnumeration.ofRuntimeSystem C))

/-- The weight is precisely the semantic compiler's weight; no caller invariant. -/
theorem weight_eq (C : RuntimeSystem) :
    (ofRuntimeSystem C).2.2 = C.toExplicitSystem.pinningWeight := PinningWeight.weight_eq C

/-- Exact negative-row and binary-weight wire, retaining all ranked sections. -/
theorem encode_eq (C : RuntimeSystem) :
    finEncoding.encode (ofRuntimeSystem C) =
      (BoundedRelabelledSections.finEncoding.encode
        (BoundedRelabelledSections.ofRuntimeSystem C)).map Sum.inl ++
      ((DomainFieldSection.rowPayloadEncode
        ((C.toExplicitSystem.unequalRows.map RuntimeResidualRow.ofResidualRow).map
          RuntimeResidualRow.toNatList)).map Sum.inl ++
        (UnaryBoundEncoding.outputFinEncoding.encode C.toExplicitSystem.pinningWeight).map Sum.inr).map Sum.inr := by
  simp only [finEncoding, ofRuntimeSystem, PinningWeight.negativeFinEncoding,
    PinningWeight.retain, LeanNPHardness.PairEncoding.finEncoding, NegativeRows.outputFinEncoding,
    NegativeRows.outputEncode_enumerate_eq, NegativeRows.pinningWeight_eq_edgeCount]

/-- Complete raw output size, including retained sections, rows and weight. -/
theorem encode_length (value : BoundedRelabelledSections.Value) (edges : List (ℕ × ℕ)) :
    (finEncoding.encode (value, PinningWeight.retain edges)).length =
      (GraphSections.negativeFinEncoding.encode (value, edges)).length +
        (encodeNat (edges.length + 1)).length + 1 := by
  simp [finEncoding, PinningWeight.negativeFinEncoding, PinningWeight.retain,
    GraphSections.negative_length, UnaryBoundEncoding.output_length,
    NegativeRows.outputFinEncoding, Nat.add_assoc]

/-- The whole result stays cubic in the complete retained-section bit length. -/
theorem encode_length_le_cubic (value : BoundedRelabelledSections.Value) :
    (finEncoding.encode (value, PinningWeight.retain
      (BoundedRelabelledSections.edges value))).length ≤
      11 * ((BoundedRelabelledSections.finEncoding.encode value).length + 1) ^ 3 + 2 := by
  rw [encode_length]
  have hg := GraphSections.negative_length_le_cubic value
  have hb := BinaryNatLists.encodeNat_length_le
    ((BoundedRelabelledSections.edges value).length + 1)
  have he := PrimalEdgeEnumeration.enumerate_length_le value.1.2 value.2
  have hn := Nat.pow_le_pow_left (BoundedRelabelledSections.variableCount_le_encode_length value) 2
  have hc : (BoundedRelabelledSections.finEncoding.encode value).length ^ 2 ≤
      ((BoundedRelabelledSections.finEncoding.encode value).length + 1) ^ 3 := by
    exact (Nat.pow_le_pow_left (Nat.le_succ _) 2).trans
      (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3))
  dsimp only [BoundedRelabelledSections.edges] at *
  omega

example : (ofRuntimeSystem ⟨[], []⟩).2.2 = 1 := by decide
example : (ofRuntimeSystem ⟨[[100, 7], [], [100, 7, 100]], [[2, 0, 2], [0, 2]]⟩).2.2 = 2 := by
  decide
example : (ofRuntimeSystem ⟨[[], [], []], [[0, 1, 2], [2, 1, 0]]⟩).2.2 = 4 := by decide

end WeightedGraphSections

/-- Actual Boolean compiler input to ranked sections, exact negative rows and
an internally computed binary pinning weight. The whole composition is charged. -/
noncomputable def runtimeCompilerWeightedNegativeSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem WeightedGraphSections.Value
      RuntimeCompilerInput.finEncoding WeightedGraphSections.finEncoding
      WeightedGraphSections.ofRuntimeSystem := by
  let weight := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    BoundedRelabelledSections.finEncoding NegativeRows.inputFinEncoding
    PinningWeight.negativeFinEncoding PinningWeight.retain negativeRowsWithWeightComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerGraphSectionsComputableInPolyTime weight
  exact { composed with
    outputsFun := fun C => by simpa only [Function.comp_def, WeightedGraphSections.ofRuntimeSystem,
      GraphSections.ofRuntimeSystem] using composed.outputsFun C }

#print axioms PinningWeight.binary_length_le
#print axioms PinningWeight.weight_eq
#print axioms pinningWeightPrepare_outputsInTime
#print axioms pinningWeightBinaryComputableInPolyTime
#print axioms pinningWeightComputableInPolyTime
#print axioms negativeRowsWithWeightComputableInPolyTime
#print axioms WeightedGraphSections.encode_length_le_cubic
#print axioms WeightedGraphSections.encode_eq
#print axioms runtimeCompilerWeightedNegativeSectionsComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
