import PhdThesisLean.AllDifferentCSPPairStepBranches
import PhdThesisLean.AllDifferentCSPBinaryHeader

/-!
# Compute a binary variable bound while retaining the complete pair-scan state

Copy the unary count already present in the checked state, then reuse the
structural-header counting machine. Endpoints, domains, unary count, scopes
and accumulated edges all survive. The binary bound is computed internally.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace PairBound

abbrev Output := ℕ × PairQueries.Input

def unaryFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding UnaryBoundEncoding.inputFinEncoding
    PairQueries.inputFinEncoding

def binaryFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding UnaryBoundEncoding.outputFinEncoding
    PairQueries.inputFinEncoding

def prepare (input : PairQueries.Input) : Output := (input.2.1.1.2, input)

theorem retained_eq (input : PairQueries.Input) : (prepare input).2 = input := rfl

theorem unary_length (input : PairQueries.Input) :
    (unaryFinEncoding.encode (prepare input)).length =
      input.2.1.1.2 + (PairQueries.inputFinEncoding.encode input).length := by
  simp [unaryFinEncoding, prepare, UnaryBoundEncoding.input_length]

theorem bound_le_length (input : PairQueries.Input) :
    input.2.1.1.2 ≤ (PairQueries.inputFinEncoding.encode input).length := by
  have h := BoundedRelabelledSections.variableCount_le_encode_length input.2.1
  rw [PairQueries.input_length]
  omega

theorem binary_length (input : PairQueries.Input) :
    (binaryFinEncoding.encode (prepare input)).length =
      (encodeNat input.2.1.1.2).length + 1 +
        (PairQueries.inputFinEncoding.encode input).length := by
  simp [binaryFinEncoding, prepare, UnaryBoundEncoding.output_length]

theorem binary_length_le (input : PairQueries.Input) :
    (binaryFinEncoding.encode (prepare input)).length ≤
      2 * (PairQueries.inputFinEncoding.encode input).length + 1 := by
  rw [binary_length]
  have h := BinaryNatLists.encodeNat_length_le input.2.1.1.2
  have hn := bound_le_length input
  omega

end PairBound

namespace PairBoundMachine

abbrev Input := PairQueriesMachine.Input
abbrev Output := Sum StructuralBinaryHeaderMachine.Tagged Input
abbrev State := Option Input × Option Output

inductive Stack
  | input | bound | retained | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | emitRetained | emitBound
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input | _ => Output

def boundCell : Input → Option Output
  | .inr (.inl (.inl (.inr bit))) => some (.inl (.inr bit))
  | _ => none

private def observe (_ : State) (cell : Option Input) : State := (cell, none)
private def remember (_ : State) (cell : Option Output) : State := (none, cell)
private def cell (s : State) : Input := s.1.getD (.inr (.inr none))
private def out (s : State) : Output := s.2.getD (.inr (.inr (.inr none)))

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch (fun s => s.1.isSome)
      (.push .retained (fun s => .inr (cell s)) <|
        .branch (fun s => (boundCell (cell s)).isSome)
          (.push .bound (fun s => (boundCell (cell s)).getD (.inl (.inr false))) <|
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
  m := program

private def stackContents (input : List Input) (bound retained output : List Output) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .bound => bound | .retained => retained | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (bound retained output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input bound retained output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "pair_bound_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe,
    remember, cell, out, boundCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Input) (bound retained output : List Output) (state : State) :
    Run (cfg (some .scan) state input bound retained output)
      (cfg (some .emitRetained) (none, none) []
        ((input.filterMap boundCell).reverse ++ bound)
        ((input.map Sum.inr).reverse ++ retained) output) (input.length + 1) := by
  induction input generalizing bound retained state with
  | nil => exact one (by pair_bound_step)
  | cons bit input ih =>
      have step : Run (cfg (some .scan) state (bit :: input) bound retained output)
          (cfg (some .scan) (some bit, none) input
            ((boundCell bit).toList ++ bound) (.inr bit :: retained) output) 1 := by
        apply one
        rcases bit with endpoint | (((domain | tally) | scope) | edge) <;> pair_bound_step
      have tail := ih ((boundCell bit).toList ++ bound) (.inr bit :: retained) (some bit, none)
      rcases bit with endpoint | (((domain | tally) | scope) | edge) <;>
        simpa [boundCell, List.reverse_cons, List.append_assoc, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using seq step tail

private def retained_run (bound retained output : List Output) (state : State) :
    Run (cfg (some .emitRetained) state [] bound retained output)
      (cfg (some .emitBound) (none, none) [] bound [] (retained.reverse ++ output))
      (retained.length + 1) := by
  induction retained generalizing output state with
  | nil => exact one (by pair_bound_step)
  | cons bit retained ih =>
      have h : Run (cfg (some .emitRetained) state [] bound (bit :: retained) output)
          (cfg (some .emitRetained) (none, some bit) [] bound retained (bit :: output)) 1 :=
        one (by pair_bound_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (bit :: output) (none, some bit))

private def bound_run (bound output : List Output) (state : State) :
    Run (cfg (some .emitBound) state [] bound [] output)
      (cfg none (none, none) [] [] [] (bound.reverse ++ output)) (bound.length + 1) := by
  induction bound generalizing output state with
  | nil => exact one (by pair_bound_step)
  | cons bit bound ih =>
      have h : Run (cfg (some .emitBound) state [] (bit :: bound) [] output)
          (cfg (some .emitBound) (none, some bit) [] bound [] (bit :: output)) 1 :=
        one (by pair_bound_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (bit :: output) (none, some bit))

private def run (input : List Input) :
    Run (cfg (some .scan) (none, none) input [] [] [])
      (cfg none (none, none) [] [] []
        (input.filterMap boundCell ++ input.map Sum.inr)) (3 * input.length + 3) := by
  have hs := scan_run input [] [] [] (none, none)
  have hr := retained_run (input.filterMap boundCell).reverse (input.map Sum.inr).reverse [] (none, none)
  have hb := bound_run (input.filterMap boundCell).reverse (input.map Sum.inr) (none, none)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse, List.length_map] at hs hr hb
  apply evalsToInTimeMono (seq (seq hs hr) hb)
  have h := List.length_filterMap_le boundCell input
  omega

private theorem init_eq (input : List Input) :
    initList computer input = cfg (some .scan) (none, none) input [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none (none, none) [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem routed_encode (input : PairQueries.Input) :
    (PairQueries.inputFinEncoding.encode input).filterMap boundCell ++
      (PairQueries.inputFinEncoding.encode input).map Sum.inr =
      PairBound.unaryFinEncoding.encode (PairBound.prepare input) := by
  have discard {α β : Type} (bits : List α) :
      bits.filterMap (fun _ => (none : Option β)) = [] := by simp
  simp [PairBound.unaryFinEncoding, PairBound.prepare, UnaryBoundEncoding.inputFinEncoding,
    PairQueries.inputFinEncoding, PairQueries.retainedFinEncoding,
    ScopeExtraction.endpointsFinEncoding, BoundedRelabelledSections.finEncoding,
    BoundedRelabelledSections.domainsFinEncoding, LeanNPHardness.PairEncoding.finEncoding,
    List.filterMap_map, Function.comp_def, boundCell, List.map_append, List.map_map, discard,
    unaryFinEncodingNat]

end PairBoundMachine

/-- Copy the actual unary bound, retaining every original state cell in order. -/
def pairBoundPrepare_outputsInTime (input : PairQueries.Input) :
    TM2OutputsInTime PairBoundMachine.computer (PairQueries.inputFinEncoding.encode input)
      (some (PairBound.unaryFinEncoding.encode (PairBound.prepare input)))
      (3 * (PairQueries.inputFinEncoding.encode input).length + 3) := by
  rw [TM2OutputsInTime, PairBoundMachine.init_eq]
  simp only [Option.map_some]
  rw [PairBoundMachine.halt_eq, ← PairBoundMachine.routed_encode]
  exact PairBoundMachine.run _

noncomputable def pairBoundPrepareComputableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Input PairBound.Output
      PairQueries.inputFinEncoding PairBound.unaryFinEncoding PairBound.prepare where
  tm := PairBoundMachine.computer
  inputAlphabet := Equiv.refl PairBoundMachine.Input
  outputAlphabet := Equiv.refl PairBoundMachine.Output
  time := 3 * Polynomial.X + 3
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_X] using pairBoundPrepare_outputsInTime input

/-- The unary-to-binary count, all copies and transfers, and scratch cleanup
are performed by checked finite machines from the original serialized state. -/
noncomputable def pairBoundComputableInPolyTime :
    @TM2ComputableInPolyTime PairQueries.Input PairBound.Output
      PairQueries.inputFinEncoding PairBound.binaryFinEncoding PairBound.prepare := by
  let count := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    UnaryBoundEncoding.inputFinEncoding UnaryBoundEncoding.outputFinEncoding
    PairQueries.inputFinEncoding id unaryBoundComputableInPolyTime
  exact compositionComputableInPolyTime _ _ _ _ _ pairBoundPrepareComputableInPolyTime count

#print axioms PairBound.retained_eq
#print axioms PairBound.binary_length
#print axioms PairBound.binary_length_le
#print axioms pairBoundPrepare_outputsInTime
#print axioms pairBoundComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
