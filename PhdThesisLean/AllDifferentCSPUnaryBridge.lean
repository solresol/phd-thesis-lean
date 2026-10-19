import PhdThesisLean.AllDifferentCSPBinaryHeader

/-!
# Bridge the unary alphabets used by prime selection and binary counting

Prime selection uses plain Boolean unary words; the existing binary counter
uses tagged unary words. This finite cell-map machine changes the tags without
changing word order or length, so the two checked arithmetic machines compose.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding unaryFinEncodingNat TM2ComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open PhdThesisLean.AllDifferentCSP.ExplicitSystem
open LeanNPHardness.MachineComposition

namespace UnaryBridgeMachine

variable {Γ Δ : Type} [Fintype Γ] (defaultCell : Γ) (mapCell : Γ → Δ)

inductive Stack
  | input | saved | output
  deriving DecidableEq, Fintype

inductive Label
  | copy | emit
  deriving DecidableEq, Fintype

abbrev Alphabet (Γ Δ : Type) : Stack → Type
  | .input | .saved => Γ | .output => Δ

def program : Label → TM2.Stmt (Alphabet Γ Δ) Label (Option Γ)
  | .copy => .pop .input (fun _ cell => cell) <| .branch Option.isSome
      (.push .saved (fun cell => cell.getD defaultCell) <| .goto fun _ => .copy)
      (.goto fun _ => .emit)
  | .emit => .pop .saved (fun _ cell => cell) <| .branch Option.isSome
      (.push .output (fun cell => mapCell (cell.getD defaultCell)) <| .goto fun _ => .emit)
      (.load (fun _ => none) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet Γ Δ
  Λ := Label
  main := .copy
  σ := Option Γ
  initialState := none
  Γk₀Fin := inferInstance
  m := program defaultCell mapCell

private def stackContents (input saved : List Γ) (output : List Δ) :
    (k : Stack) → List (Alphabet Γ Δ k)
  | .input => input | .saved => saved | .output => output

private def cfg (label : Option Label) (state : Option Γ)
    (input saved : List Γ) (output : List Δ) : (computer defaultCell mapCell).Cfg :=
  ⟨label, state, stackContents input saved output⟩

private abbrev Run (a b : (computer defaultCell mapCell).Cfg) (time : ℕ) :=
  EvalsToInTime (computer defaultCell mapCell).step a (some b) time

private def one {a b : (computer defaultCell mapCell).Cfg}
    (h : (computer defaultCell mapCell).step a = some b) : Run defaultCell mapCell a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using! h, steps_le_m := le_rfl }

private def seq {a b c : (computer defaultCell mapCell).Cfg} {m n : ℕ}
    (h : Run defaultCell mapCell a b m) (h' : Run defaultCell mapCell b c n) :
    Run defaultCell mapCell a c (m + n) := by
  simpa [Nat.add_comm] using!
    EvalsToInTime.trans (computer defaultCell mapCell).step m n a b (some c) h h'

local macro "bridge_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def copy_run (input saved : List Γ) (output : List Δ) (state : Option Γ) :
    Run defaultCell mapCell (cfg defaultCell mapCell (some .copy) state input saved output)
      (cfg defaultCell mapCell (some .emit) none [] (input.reverse ++ saved) output)
      (input.length + 1) := by
  induction input generalizing saved state with
  | nil => exact one _ _ (by bridge_step)
  | cons cell input ih =>
      have step : Run defaultCell mapCell
          (cfg defaultCell mapCell (some .copy) state (cell :: input) saved output)
          (cfg defaultCell mapCell (some .copy) (some cell) input (cell :: saved) output) 1 :=
        one _ _ (by bridge_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq _ _ step (ih (cell :: saved) (some cell))

private def emit_run (saved : List Γ) (output : List Δ) (state : Option Γ) :
    Run defaultCell mapCell (cfg defaultCell mapCell (some .emit) state [] saved output)
      (cfg defaultCell mapCell none none [] [] (saved.reverse.map mapCell ++ output))
      (saved.length + 1) := by
  induction saved generalizing output state with
  | nil => exact one _ _ (by bridge_step)
  | cons cell saved ih =>
      have step : Run defaultCell mapCell
          (cfg defaultCell mapCell (some .emit) state [] (cell :: saved) output)
          (cfg defaultCell mapCell (some .emit) (some cell) [] saved (mapCell cell :: output)) 1 :=
        one _ _ (by bridge_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq _ _ step (ih (mapCell cell :: output) (some cell))

/-- Every input cell is read twice; all scratch is empty at halt. -/
def outputsInTime (input : List Γ) :
    TM2OutputsInTime (computer defaultCell mapCell) input (some (input.map mapCell))
      (2 * input.length + 2) := by
  have copied := copy_run defaultCell mapCell input [] [] none
  simp only [List.append_nil] at copied
  have run := seq _ _ copied (emit_run defaultCell mapCell input.reverse [] none)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at run
  have hi : initList (computer defaultCell mapCell) input =
      cfg defaultCell mapCell (some .copy) none input [] [] := by
    simp only [initList, computer, cfg]
    congr 1
    funext k
    cases k <;> rfl
  have ho : haltList (computer defaultCell mapCell) (input.map mapCell) =
      cfg defaultCell mapCell none none [] [] (input.map mapCell) := by
    simp only [haltList, computer, cfg]
    congr 1
    funext k
    cases k <;> rfl
  rw [TM2OutputsInTime, hi]
  simpa [ho, Nat.mul_succ, Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! run

end UnaryBridgeMachine

private def untag : StructuralBinaryHeaderMachine.Tagged → Bool
  | .inl _ => false | .inr bit => bit

/-- Remove the counter's unary tag before invoking plain unary prime selection. -/
noncomputable def unaryUntagComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ ℕ UnaryBoundEncoding.inputFinEncoding unaryFinEncodingNat id where
  tm := UnaryBridgeMachine.computer (Sum.inr false : StructuralBinaryHeaderMachine.Tagged)
    untag
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun n := by
    simpa [Equiv.refl, UnaryBoundEncoding.inputFinEncoding, unaryFinEncodingNat,
      List.map_map, Function.comp_def, untag, unaryEncodeNat_eq_replicate_true, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X] using
      UnaryBridgeMachine.outputsInTime (Sum.inr false : StructuralBinaryHeaderMachine.Tagged)
        untag
        (UnaryBoundEncoding.inputFinEncoding.encode n)

/-- Restore the counter's unary tag after prime selection. -/
noncomputable def unaryTagComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ ℕ unaryFinEncodingNat UnaryBoundEncoding.inputFinEncoding id where
  tm := UnaryBridgeMachine.computer false (Sum.inr : Bool → StructuralBinaryHeaderMachine.Tagged)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun n := by
    simpa [Equiv.refl, UnaryBoundEncoding.inputFinEncoding, unaryFinEncodingNat,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X] using
      UnaryBridgeMachine.outputsInTime false (Sum.inr : Bool → StructuralBinaryHeaderMachine.Tagged)
        (unaryFinEncodingNat.encode n)

/-- The selected prime in the existing binary-field encoding, with every adapter charged. -/
noncomputable def selectedPrimeBinaryComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ ℕ UnaryBoundEncoding.inputFinEncoding
      UnaryBoundEncoding.outputFinEncoding selectPrimeAbove := by
  let select := compositionComputableInPolyTime _ _ _ _ _
    unaryUntagComputableInPolyTime selectedPrimeComputableInPolyTime
  let tag := compositionComputableInPolyTime _ _ _ _ _ select unaryTagComputableInPolyTime
  let binary := compositionComputableInPolyTime _ _ _ _ _ tag unaryBoundComputableInPolyTime
  exact { binary with
    outputsFun := fun n => by simpa only [Function.comp_def, id_eq] using binary.outputsFun n }

/-- Plain unary variable count to the same binary-field encoding. -/
noncomputable def plainUnaryBinaryComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ ℕ unaryFinEncodingNat UnaryBoundEncoding.outputFinEncoding id := by
  let binary := compositionComputableInPolyTime _ _ _ _ _
    unaryTagComputableInPolyTime unaryBoundComputableInPolyTime
  exact { binary with
    outputsFun := fun n => by simpa only [Function.comp_def, id_eq] using binary.outputsFun n }

#print axioms UnaryBridgeMachine.outputsInTime
#print axioms unaryUntagComputableInPolyTime
#print axioms unaryTagComputableInPolyTime
#print axioms selectedPrimeBinaryComputableInPolyTime
#print axioms plainUnaryBinaryComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
