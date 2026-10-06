import PhdThesisLean.AllDifferentCSPPairLoop

/-!
# Retain completed graph sections and emit exact negative residual rows

A finite projection removes the exhausted scan counters and keeps both the
ranked sections and ordered edge stream. The checked pair-right adapter runs
the existing negative-row emitter on that stream, retaining every section.
The full composition starts from the actual Boolean compiler input.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PairFinalizationMachine

abbrev Wire := Sum PairQueriesMachine.Bounded (Option Bool)
abbrev Input := PairQueriesMachine.Input
abbrev State := Option Input × Option Wire

inductive Stack
  | input | saved | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | emit
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input
  | _ => Wire

private def observe (_ : State) (bit : Option Input) : State := (bit, none)
private def remember (_ : State) (bit : Option Wire) : State := (none, bit)
private def retained (s : State) : Option Wire := s.1.bind Sum.getRight?
private def cell (s : State) : Wire := (retained s).getD (.inr none)
private def savedCell (s : State) : Wire := s.2.getD (.inr none)

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch (fun s => s.1.isSome)
      (.branch (fun s => (retained s).isSome)
        (.push .saved cell <| .goto fun _ => .scan)
        (.goto fun _ => .scan))
      (.goto fun _ => .emit)
  | .emit => .pop .saved remember <| .branch (fun s => s.2.isSome)
      (.push .output savedCell <| .goto fun _ => .emit)
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

private def stackContents (input : List Input) (saved output : List Wire) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .saved => saved | .output => output

private def cfg (label : Option Label) (state : State)
    (input : List Input) (saved output : List Wire) : computer.Cfg :=
  ⟨label, state, stackContents input saved output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) :=
  EvalsToInTime computer.step a (some b) time

private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }

private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "finalize_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, observe, remember,
    retained, cell, savedCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Input) (saved output : List Wire) (state : State) :
    Run (cfg (some .scan) state input saved output)
      (cfg (some .emit) (none, none) []
        ((input.filterMap Sum.getRight?).reverse ++ saved) output) (input.length + 1) := by
  induction input generalizing saved state with
  | nil => exact one (by finalize_step)
  | cons bit input ih =>
      cases bit with
      | inl bit =>
          have h : Run (cfg (some .scan) state (.inl bit :: input) saved output)
              (cfg (some .scan) (some (.inl bit), none) input saved output) 1 :=
            one (by finalize_step)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            seq h (ih saved (some (.inl bit), none))
      | inr bit =>
          have h : Run (cfg (some .scan) state (.inr bit :: input) saved output)
              (cfg (some .scan) (some (.inr bit), none) input (bit :: saved) output) 1 :=
            one (by finalize_step)
          simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using seq h (ih (bit :: saved) (some (.inr bit), none))

private def emit_run (saved output : List Wire) (state : State) :
    Run (cfg (some .emit) state [] saved output)
      (cfg none (none, none) [] [] (saved.reverse ++ output)) (saved.length + 1) := by
  induction saved generalizing output state with
  | nil => exact one (by finalize_step)
  | cons bit saved ih =>
      have h : Run (cfg (some .emit) state [] (bit :: saved) output)
          (cfg (some .emit) (none, some bit) [] saved (bit :: output)) 1 := one (by finalize_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (bit :: output) (none, some bit))

private theorem init_eq (input : List Input) :
    initList computer input = cfg (some .scan) (none, none) input [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Wire) :
    haltList computer output = cfg none (none, none) [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

def outputsInTime (input : PairQueries.Input) :
    TM2OutputsInTime computer (PairQueries.inputFinEncoding.encode input)
      (some (PairQueries.retainedFinEncoding.encode input.2))
      (2 * (PairQueries.inputFinEncoding.encode input).length + 2) := by
  have hs := scan_run (PairQueries.inputFinEncoding.encode input) [] [] (none, none)
  have he := emit_run ((PairQueries.inputFinEncoding.encode input).filterMap Sum.getRight?).reverse
    [] (none, none)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hs he
  have selected : (PairQueries.inputFinEncoding.encode input).filterMap Sum.getRight? =
      PairQueries.retainedFinEncoding.encode input.2 := by
    simp [PairQueries.inputFinEncoding, LeanNPHardness.PairEncoding.finEncoding,
      List.filterMap_map, Function.comp_def]
  have run := seq hs he
  rw [selected] at run
  rw [TM2OutputsInTime, init_eq]
  simp only [Option.map_some, halt_eq]
  apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono run
  have h := List.length_filterMap_le Sum.getRight? (PairQueries.inputFinEncoding.encode input)
  rw [selected] at h
  omega

end PairFinalizationMachine

/-- Remove only scan counters, retaining the complete sections and edge list. -/
noncomputable def pairFinalizationComputableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Input
      (BoundedRelabelledSections.Value × List (ℕ × ℕ))
      PairQueries.inputFinEncoding PairQueries.retainedFinEncoding Prod.snd where
  tm := PairFinalizationMachine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X] using PairFinalizationMachine.outputsInTime input

namespace GraphSections

abbrev Value := BoundedRelabelledSections.Value × List (ℕ × ℕ)

def ofRuntimeSystem (C : RuntimeSystem) : Value :=
  (BoundedRelabelledSections.ofRuntimeSystem C, PrimalEdgeEnumeration.ofRuntimeSystem C)

def negativeFinEncoding : FinEncoding Value :=
  LeanNPHardness.PairEncoding.finEncoding BoundedRelabelledSections.finEncoding
    NegativeRows.outputFinEncoding

/-- Complete output size includes every retained section as well as every row. -/
theorem negative_length (value : BoundedRelabelledSections.Value) (edges : List (ℕ × ℕ)) :
    (negativeFinEncoding.encode (value, edges)).length =
      (BoundedRelabelledSections.finEncoding.encode value).length +
        (NegativeRows.outputEncode edges).length := by
  simp [negativeFinEncoding, NegativeRows.outputFinEncoding]

/-- The whole paired result is cubic in the retained-section input length. -/
theorem negative_length_le_cubic (value : BoundedRelabelledSections.Value) :
    (negativeFinEncoding.encode (value, BoundedRelabelledSections.edges value)).length ≤
      10 * ((BoundedRelabelledSections.finEncoding.encode value).length + 1) ^ 3 := by
  rw [negative_length]
  have rows := BoundedRelabelledSections.negativeRows_length_le_cubic value
  have size : (BoundedRelabelledSections.finEncoding.encode value).length ≤
      ((BoundedRelabelledSections.finEncoding.encode value).length + 1) ^ 3 :=
    (Nat.le_succ _).trans (Nat.le_pow (by decide))
  omega

/-- The graph section retains exactly the ranked input sections and semantic
ordered primal graph after projection. -/
theorem result_eq (C : RuntimeSystem) :
    (PairLoop.result (BoundedRelabelledSections.ofRuntimeSystem C)).2 = ofRuntimeSystem C := rfl

/-- The right-hand wire is exactly the semantic compiler's negative rows. -/
theorem negative_encode (C : RuntimeSystem) :
    negativeFinEncoding.encode (ofRuntimeSystem C) =
      (BoundedRelabelledSections.finEncoding.encode
        (BoundedRelabelledSections.ofRuntimeSystem C)).map Sum.inl ++
      (DomainFieldSection.rowPayloadEncode
        ((C.toExplicitSystem.unequalRows.map RuntimeResidualRow.ofResidualRow).map
          RuntimeResidualRow.toNatList)).map Sum.inr := by
  simp only [negativeFinEncoding, ofRuntimeSystem, LeanNPHardness.PairEncoding.finEncoding,
    NegativeRows.outputFinEncoding, NegativeRows.outputEncode_enumerate_eq]

end GraphSections

/-- Actual compiler input to ranked sections and the exact ordered graph. -/
noncomputable def runtimeCompilerGraphSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem GraphSections.Value
      RuntimeCompilerInput.finEncoding PairQueries.retainedFinEncoding
      GraphSections.ofRuntimeSystem := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerPairEnumerationComputableInPolyTime pairFinalizationComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa only [Function.comp_def, GraphSections.result_eq] using composed.outputsFun C }

/-- Emit all negative rows while retaining ranked sections for positive rows. -/
noncomputable def runtimeCompilerNegativeSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem GraphSections.Value
      RuntimeCompilerInput.finEncoding GraphSections.negativeFinEncoding
      GraphSections.ofRuntimeSystem := by
  let emit := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    BoundedRelabelledSections.finEncoding NegativeRows.inputFinEncoding
    NegativeRows.outputFinEncoding id negativeRowsComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerGraphSectionsComputableInPolyTime emit
  exact { composed with
    outputsFun := fun C => by simpa only [Function.comp_def, id_eq] using composed.outputsFun C }

#print axioms PairFinalizationMachine.outputsInTime
#print axioms pairFinalizationComputableInPolyTime
#print axioms GraphSections.negative_length_le_cubic
#print axioms GraphSections.negative_encode
#print axioms runtimeCompilerGraphSectionsComputableInPolyTime
#print axioms runtimeCompilerNegativeSectionsComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
