import PhdThesisLean.AllDifferentCSPPositiveScanInitialization
import PhdThesisLean.AllDifferentCSPBinaryHeader

/-!
# Compute either rectangular bound from the complete positive state

Select the unary occurrence count for inner continuation, or the unary variable
count for exhaustion. Convert that selected count to binary with the imported
checked counter, retaining the candidate, both bounds, all sections and rows.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PositiveBound

def bound (inner : Bool) (input : PositiveCandidateQueries.Input) : ℕ :=
  if inner then input.2.1.1.1.1.2 else input.2.1.1.1.2

variable (inner : Bool)

abbrev Output := ℕ × PositiveCandidateQueries.Input

def unaryFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding UnaryBoundEncoding.inputFinEncoding
    PositiveCandidateQueries.inputFinEncoding

def binaryFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding UnaryBoundEncoding.outputFinEncoding
    PositiveCandidateQueries.inputFinEncoding

def prepare (input : PositiveCandidateQueries.Input) : Output := (bound inner input, input)

theorem retained_eq (input : PositiveCandidateQueries.Input) : (prepare inner input).2 = input := rfl

theorem unary_length (input : PositiveCandidateQueries.Input) :
    (unaryFinEncoding.encode (prepare inner input)).length =
      bound inner input + (PositiveCandidateQueries.inputFinEncoding.encode input).length := by
  simp [unaryFinEncoding, prepare, UnaryBoundEncoding.input_length]

theorem bound_le_length (input : PositiveCandidateQueries.Input) :
    bound inner input ≤ (PositiveCandidateQueries.inputFinEncoding.encode input).length := by
  have hn := CountedPositiveSections.variableCount_le_encode_length input.2.1
  have hq := CountedPositiveSections.count_le_encode_length input.2.1
  rw [PositiveCandidateQueries.input_length]
  unfold bound
  split <;> omega

theorem binary_length (input : PositiveCandidateQueries.Input) :
    (binaryFinEncoding.encode (prepare inner input)).length =
      (encodeNat (bound inner input)).length + 1 +
        (PositiveCandidateQueries.inputFinEncoding.encode input).length := by
  simp [binaryFinEncoding, prepare, UnaryBoundEncoding.output_length]

theorem binary_length_le (input : PositiveCandidateQueries.Input) :
    (binaryFinEncoding.encode (prepare inner input)).length ≤
      2 * (PositiveCandidateQueries.inputFinEncoding.encode input).length + 1 := by
  rw [binary_length]
  have h := BinaryNatLists.encodeNat_length_le (bound inner input)
  have hn := bound_le_length inner input
  omega

end PositiveBound

namespace PositiveBoundMachine

abbrev Input := PositiveCandidateQueriesMachine.Input
abbrev Output := Sum StructuralBinaryHeaderMachine.Tagged Input
abbrev State := Option Input × Option Output

inductive Stack
  | input | bound | retained | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | emitRetained | emitBound
  deriving DecidableEq, Fintype

variable (inner : Bool)

abbrev Alphabet : Stack → Type
  | .input => Input | _ => Output

def boundCell : Input → Option Output
  | .inr (.inl (.inl (.inl (.inl (.inr bit))))) =>
      if inner then some (.inl (.inr bit)) else none
  | .inr (.inl (.inl (.inl (.inr bit)))) =>
      if inner then none else some (.inl (.inr bit))
  | _ => none

private def observe (_ : State) (cell : Option Input) : State := (cell, none)
private def remember (_ : State) (cell : Option Output) : State := (none, cell)
private def cell (s : State) : Input := s.1.getD (.inr (.inr none))
private def out (s : State) : Output := s.2.getD (.inr (.inr (.inr none)))

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch (fun s => s.1.isSome)
      (.push .retained (fun s => .inr (cell s)) <|
        .branch (fun s => (boundCell inner (cell s)).isSome)
          (.push .bound (fun s => (boundCell inner (cell s)).getD (.inl (.inr false))) <|
            .goto fun _ => .scan)
          (.goto fun _ => .scan))
      (.goto fun _ => .emitRetained)
  | .emitRetained => .pop .retained remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitRetained)
      (.goto fun _ => .emitBound)
  | .emitBound => .pop .bound remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitBound)
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
  m := program inner

private def stackContents (input : List Input) (bound retained output : List Output) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .bound => bound | .retained => retained | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (bound retained output : List Output) : (computer inner).Cfg :=
  ⟨label, state, stackContents input bound retained output⟩

private abbrev Run (a b : (computer inner).Cfg) (time : ℕ) := EvalsToInTime (computer inner).step a (some b) time
private def one {a b : (computer inner).Cfg} (h : (computer inner).step a = some b) : Run inner a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using! h, steps_le_m := le_rfl }
private def seq {a b c : (computer inner).Cfg} {m n : ℕ}
    (h : Run inner a b m) (h' : Run inner b c n) : Run inner a c (m + n) := by
  simpa [Nat.add_comm] using! EvalsToInTime.trans (computer inner).step m n a b (some c) h h'

local macro "positive_bound_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe,
    remember, cell, out, boundCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Input) (bound retained output : List Output) (state : State) :
    Run inner (cfg inner (some .scan) state input bound retained output)
      (cfg inner (some .emitRetained) (none, none) []
        ((input.filterMap (boundCell inner)).reverse ++ bound)
        ((input.map Sum.inr).reverse ++ retained) output) (input.length + 1) := by
  induction input generalizing bound retained state with
  | nil => exact one inner (by positive_bound_step)
  | cons bit input ih =>
      have step : Run inner (cfg inner (some .scan) state (bit :: input) bound retained output)
          (cfg inner (some .scan) (some bit, none) input
            ((boundCell inner bit).toList ++ bound) (.inr bit :: retained) output) 1 := by
        apply one inner
        rcases bit with endpoint | (((((occurrence | count) | variableCount) | scope) | weight) | row) <;> cases inner <;> positive_bound_step
      have tail := ih ((boundCell inner bit).toList ++ bound) (.inr bit :: retained) (some bit, none)
      rcases bit with endpoint | (((((occurrence | count) | variableCount) | scope) | weight) | row) <;> cases inner <;>
        simpa [boundCell, List.reverse_cons, List.append_assoc, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using seq _ step tail

private def retained_run (bound retained output : List Output) (state : State) :
    Run inner (cfg inner (some .emitRetained) state [] bound retained output)
      (cfg inner (some .emitBound) (none, none) [] bound [] (retained.reverse ++ output))
      (retained.length + 1) := by
  induction retained generalizing output state with
  | nil => exact one inner (by positive_bound_step)
  | cons bit retained ih =>
      have h : Run inner (cfg inner (some .emitRetained) state [] bound (bit :: retained) output)
          (cfg inner (some .emitRetained) (none, some bit) [] bound retained (bit :: output)) 1 :=
        one inner (by positive_bound_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq inner h (ih (bit :: output) (none, some bit))

private def bound_run (bound output : List Output) (state : State) :
    Run inner (cfg inner (some .emitBound) state [] bound [] output)
      (cfg inner none (none, none) [] [] [] (bound.reverse ++ output)) (bound.length + 1) := by
  induction bound generalizing output state with
  | nil => exact one inner (by positive_bound_step)
  | cons bit bound ih =>
      have h : Run inner (cfg inner (some .emitBound) state [] (bit :: bound) [] output)
          (cfg inner (some .emitBound) (none, some bit) [] bound [] (bit :: output)) 1 :=
        one inner (by positive_bound_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq inner h (ih (bit :: output) (none, some bit))

private def run (input : List Input) :
    Run inner (cfg inner (some .scan) (none, none) input [] [] [])
      (cfg inner none (none, none) [] [] []
        (input.filterMap (boundCell inner) ++ input.map Sum.inr)) (3 * input.length + 3) := by
  have hs := scan_run inner input [] [] [] (none, none)
  have hr := retained_run inner (input.filterMap (boundCell inner)).reverse (input.map Sum.inr).reverse [] (none, none)
  have hb := bound_run inner (input.filterMap (boundCell inner)).reverse (input.map Sum.inr) (none, none)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse, List.length_map] at hs hr hb
  apply evalsToInTimeMono (seq inner (seq inner hs hr) hb)
  have h := List.length_filterMap_le (boundCell inner) input
  omega

private theorem init_eq (input : List Input) :
    initList (computer inner) input = cfg inner (some .scan) (none, none) input [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList (computer inner) output = cfg inner none (none, none) [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem routed_encode (input : PositiveCandidateQueries.Input) :
    (PositiveCandidateQueries.inputFinEncoding.encode input).filterMap (boundCell inner) ++
      (PositiveCandidateQueries.inputFinEncoding.encode input).map Sum.inr =
      PositiveBound.unaryFinEncoding.encode (PositiveBound.prepare inner input) := by
  have discard {α β : Type} (bits : List α) :
      bits.filterMap (fun _ => (none : Option β)) = [] := by simp
  cases inner <;> simp [PositiveBound.unaryFinEncoding, PositiveBound.prepare, PositiveBound.bound, UnaryBoundEncoding.inputFinEncoding,
    PositiveCandidateQueries.inputFinEncoding, PositiveCandidateQueries.retainedFinEncoding,
    ScopeExtraction.endpointsFinEncoding, CountedPositiveSections.finEncoding,
    CountedPositiveSections.sectionsFinEncoding, CountedPositiveSections.domainsFinEncoding,
    OccurrenceCount.finEncoding, LeanNPHardness.PairEncoding.finEncoding,
    List.filterMap_map, Function.comp_def, boundCell, List.map_append, List.map_map, discard,
    unaryFinEncodingNat]

end PositiveBoundMachine

variable (inner : Bool)

/-- Copy the actual unary bound, retaining every original state cell in order. -/
def positiveBoundPrepare_outputsInTime (input : PositiveCandidateQueries.Input) :
    TM2OutputsInTime (PositiveBoundMachine.computer inner) (PositiveCandidateQueries.inputFinEncoding.encode input)
      (some (PositiveBound.unaryFinEncoding.encode (PositiveBound.prepare inner input)))
      (3 * (PositiveCandidateQueries.inputFinEncoding.encode input).length + 3) := by
  rw [TM2OutputsInTime, PositiveBoundMachine.init_eq]
  simp only [Option.map_some]
  rw [PositiveBoundMachine.halt_eq, ← PositiveBoundMachine.routed_encode]
  exact PositiveBoundMachine.run inner _

noncomputable def positiveBoundPrepareComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveCandidateQueries.Input PositiveBound.Output
      PositiveCandidateQueries.inputFinEncoding PositiveBound.unaryFinEncoding (PositiveBound.prepare inner) where
  tm := PositiveBoundMachine.computer inner
  inputAlphabet := Equiv.refl PositiveBoundMachine.Input
  outputAlphabet := Equiv.refl PositiveBoundMachine.Output
  time := 3 * Polynomial.X + 3
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_X] using positiveBoundPrepare_outputsInTime inner input

/-- The unary-to-binary count, all copies and transfers, and scratch cleanup
are performed by checked finite machines from the original serialized state. -/
noncomputable def positiveBoundComputableInPolyTime :
    @TM2ComputableInPolyTime PositiveCandidateQueries.Input PositiveBound.Output
      PositiveCandidateQueries.inputFinEncoding PositiveBound.binaryFinEncoding (PositiveBound.prepare inner) := by
  let count := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    UnaryBoundEncoding.inputFinEncoding UnaryBoundEncoding.outputFinEncoding
    PositiveCandidateQueries.inputFinEncoding id unaryBoundComputableInPolyTime
  exact compositionComputableInPolyTime _ _ _ _ _ (positiveBoundPrepareComputableInPolyTime inner) count

#print axioms PositiveBound.retained_eq
#print axioms PositiveBound.unary_length
#print axioms PositiveBound.bound_le_length
#print axioms PositiveBound.binary_length
#print axioms PositiveBound.binary_length_le
#print axioms positiveBoundPrepare_outputsInTime
#print axioms positiveBoundComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
