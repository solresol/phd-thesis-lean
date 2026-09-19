import PhdThesisLean.AllDifferentCSPRankPredicates

/-!
# Update the unary rank accumulator and retain the next query

The two checked predicate bits contribute one exactly when the symbol is
smaller and absent from its tail. This finite machine consumes both bits,
copies the complete remaining query, and conditionally adds one unary cell.
Its linear bound includes every transfer and clears all work stacks.
`AllDifferentCSPRankLoop` composes the repeated driver; the full CSP corollary
still requires composition across all compiler sections.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace RankAccumulator

abbrev Input := RankPredicates.Output × ℕ
abbrev Output := DomainSymbolMembership.Input × ℕ

def inputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding RankPredicates.outputFinEncoding unaryFinEncodingNat

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding DomainSymbolMembership.finEncoding unaryFinEncodingNat

def update (input : Input) : Output :=
  (input.1.2.2, input.2 + if input.1.2.1 && !input.1.1 then 1 else 0)

theorem input_length (input : Input) :
    (inputFinEncoding.encode input).length =
      (DomainSymbolMembership.finEncoding.encode input.1.2.2).length + input.2 + 2 := by
  simp [inputFinEncoding, RankPredicates.outputFinEncoding, finEncodingBoolBool,
    encodeBool, unaryFinEncodingNat, unaryEncodeNat_eq_replicate_true]

theorem output_length (input : Input) :
    (outputFinEncoding.encode (update input)).length =
      (DomainSymbolMembership.finEncoding.encode input.1.2.2).length + input.2 +
        if input.1.2.1 && !input.1.1 then 1 else 0 := by
  simp [outputFinEncoding, update, unaryFinEncodingNat, unaryEncodeNat_eq_replicate_true, Nat.add_assoc]

end RankAccumulator

namespace RankAccumulatorMachine

abbrev Query := Sum Bool (Option Bool)
abbrev Input := Sum (Sum Bool (Sum Bool Query)) Bool
abbrev Output := Sum Query Bool

inductive Stack
  | input | saved | output
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input | .saved => Query | .output => Output

inductive Label
  | membership | comparison (seen : Bool) | copy | emit
  deriving DecidableEq, Fintype

abbrev State := Option Input × Option Query

def initialState : State := (none, none)
private def observe (_ : State) (cell : Option Input) : State := (cell, none)
private def remember (_ : State) (cell : Option Query) : State := (none, cell)
private def memberBit (s : State) := (s.1.bind Sum.getLeft?).bind Sum.getLeft?
private def smallerBit (s : State) := ((s.1.bind Sum.getLeft?).bind Sum.getRight?).bind Sum.getLeft?
private def queryCell (s : State) := ((s.1.bind Sum.getLeft?).bind Sum.getRight?).bind Sum.getRight?
private def unaryCell (s : State) := s.1.bind Sum.getRight?

def program : Label → TM2.Stmt Alphabet Label State
  | .membership => .pop .input observe <| .goto fun s => .comparison ((memberBit s).getD false)
  | .comparison seen => .pop .input observe <|
      .branch (fun s => (smallerBit s).getD false && !seen)
        (.push .output (fun _ => .inr true) <| .load (fun _ => initialState) <| .goto fun _ => .copy)
        (.load (fun _ => initialState) <| .goto fun _ => .copy)
  | .copy => .pop .input observe <|
      .branch (fun s => (queryCell s).isSome)
        (.push .saved (fun s => (queryCell s).getD (.inl false)) <| .goto fun _ => .copy)
        (.branch (fun s => (unaryCell s).isSome)
          (.push .output (fun s => .inr ((unaryCell s).getD false)) <| .goto fun _ => .copy)
          (.load (fun _ => initialState) <| .goto fun _ => .emit))
  | .emit => .pop .saved remember <|
      .branch (fun s => s.2.isSome)
        (.push .output (fun s => .inl (s.2.getD (.inl false))) <| .goto fun _ => .emit)
        (.load (fun _ => initialState) <| .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .membership
  σ := State
  initialState := initialState
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input : List Input) (saved : List Query) (output : List Output) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .saved => saved | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (saved : List Query) (output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input saved output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "accumulator_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, initialState,
    observe, remember, memberBit, smallerBit, queryCell, unaryCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def bits_run (seen smaller : Bool) (rest : List Input) :
    Run (cfg (some .membership) initialState
        (.inl (.inl seen) :: .inl (.inr (.inl smaller)) :: rest) [] [])
      (cfg (some .copy) initialState rest []
        ((unaryEncodeNat (if smaller && !seen then 1 else 0)).map Sum.inr)) 2 := by
  have hm : Run (cfg (some .membership) initialState
      (.inl (.inl seen) :: .inl (.inr (.inl smaller)) :: rest) [] [])
      (cfg (some (.comparison seen)) (some (.inl (.inl seen)), none)
        (.inl (.inr (.inl smaller)) :: rest) [] []) 1 := one (by accumulator_step)
  have hc : Run (cfg (some (.comparison seen)) (some (.inl (.inl seen)), none)
      (.inl (.inr (.inl smaller)) :: rest) [] [])
      (cfg (some .copy) initialState rest []
        ((unaryEncodeNat (if smaller && !seen then 1 else 0)).map Sum.inr)) 1 := by
    apply one
    cases seen <;> cases smaller <;> simp only [Bool.not_true, Bool.not_false,
      Bool.and_true, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte, unaryEncodeNat, List.map_cons, List.map_nil] <;> accumulator_step
  exact seq hm hc

private def unary_run (count added : ℕ) (saved : List Query) (state : State) :
    Run (cfg (some .copy) state ((unaryEncodeNat count).map Sum.inr) saved
        ((unaryEncodeNat added).map Sum.inr))
      (cfg (some .emit) initialState [] saved ((unaryEncodeNat (count + added)).map Sum.inr))
      (count + 1) := by
  induction count generalizing added state with
  | zero => exact one (by simp only [unaryEncodeNat]; accumulator_step)
  | succ count ih =>
      have h : Run (cfg (some .copy) state ((unaryEncodeNat (count + 1)).map Sum.inr) saved
          ((unaryEncodeNat added).map Sum.inr))
          (cfg (some .copy) (some (.inr true), none) ((unaryEncodeNat count).map Sum.inr) saved
            ((unaryEncodeNat (added + 1)).map Sum.inr)) 1 := one (by
        simp only [unaryEncodeNat, List.map_cons]
        accumulator_step)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (added + 1) (some (.inr true), none))

private def query_run (query : List Query) (count added : ℕ)
    (saved : List Query) (state : State) :
    Run (cfg (some .copy) state
        (query.map (fun q => .inl (.inr (.inr q))) ++ (unaryEncodeNat count).map Sum.inr)
        saved ((unaryEncodeNat added).map Sum.inr))
      (cfg (some .emit) initialState [] (query.reverse ++ saved)
        ((unaryEncodeNat (count + added)).map Sum.inr))
      (query.length + count + 1) := by
  induction query generalizing saved state with
  | nil => simpa using unary_run count added saved state
  | cons cell query ih =>
      have h : Run (cfg (some .copy) state
          ((cell :: query).map (fun q => .inl (.inr (.inr q))) ++ (unaryEncodeNat count).map Sum.inr)
          saved ((unaryEncodeNat added).map Sum.inr))
          (cfg (some .copy) (some (.inl (.inr (.inr cell))), none)
            (query.map (fun q => .inl (.inr (.inr q))) ++ (unaryEncodeNat count).map Sum.inr)
            (cell :: saved) ((unaryEncodeNat added).map Sum.inr)) 1 := one (by accumulator_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (cell :: saved) (some (.inl (.inr (.inr cell))), none))

private def emit_run (saved : List Query) (output : List Output) (state : State) :
    Run (cfg (some .emit) state [] saved output)
      (cfg none initialState [] [] (saved.reverse.map Sum.inl ++ output)) (saved.length + 1) := by
  induction saved generalizing output state with
  | nil => exact one (by accumulator_step)
  | cons cell saved ih =>
      have h : Run (cfg (some .emit) state [] (cell :: saved) output)
          (cfg (some .emit) (none, some cell) [] saved (.inl cell :: output)) 1 :=
        one (by accumulator_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (.inl cell :: output) (none, some cell))

private def run (input : RankAccumulator.Input) :
    Run (cfg (some .membership) initialState (RankAccumulator.inputFinEncoding.encode input) [] [])
      (cfg none initialState [] [] (RankAccumulator.outputFinEncoding.encode (RankAccumulator.update input)))
      (2 * (DomainSymbolMembership.finEncoding.encode input.1.2.2).length + input.2 + 4) := by
  let query := DomainSymbolMembership.finEncoding.encode input.1.2.2
  let added := if input.1.2.1 && !input.1.1 then 1 else 0
  have hb := bits_run input.1.1 input.1.2.1
    (query.map (fun q => .inl (.inr (.inr q))) ++ (unaryEncodeNat input.2).map Sum.inr)
  have hq := query_run query input.2 added [] initialState
  have he := emit_run query.reverse ((unaryEncodeNat (input.2 + added)).map Sum.inr) initialState
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hq he
  convert seq (seq hb hq) he using 1
  · simp [RankAccumulator.inputFinEncoding, RankPredicates.outputFinEncoding,
      finEncodingBoolBool, encodeBool, unaryFinEncodingNat,
      List.map_map, Function.comp_def, query]
  · dsimp [query]
    omega

private theorem init_eq (input : List Input) :
    initList computer input = cfg (some .membership) initialState input [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none initialState [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

end RankAccumulatorMachine

/-- Consume both predicate bits, conditionally increment the unary accumulator,
and retain the exact query in at most twice the complete input wire length. -/
def rankAccumulator_outputsInTime (input : RankAccumulator.Input) :
    TM2OutputsInTime RankAccumulatorMachine.computer (RankAccumulator.inputFinEncoding.encode input)
      (some (RankAccumulator.outputFinEncoding.encode (RankAccumulator.update input)))
      (2 * (RankAccumulator.inputFinEncoding.encode input).length) := by
  rw [TM2OutputsInTime, RankAccumulatorMachine.init_eq]
  simp only [Option.map_some]
  rw [RankAccumulatorMachine.halt_eq]
  have h := RankAccumulatorMachine.run input
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  rw [RankAccumulator.input_length]
  omega

noncomputable def rankAccumulatorComputableInPolyTime :
    @TM2ComputableInPolyTime RankAccumulator.Input RankAccumulator.Output
      RankAccumulator.inputFinEncoding RankAccumulator.outputFinEncoding RankAccumulator.update where
  tm := RankAccumulatorMachine.computer
  inputAlphabet := Equiv.refl RankAccumulatorMachine.Input
  outputAlphabet := Equiv.refl RankAccumulatorMachine.Output
  time := 2 * Polynomial.X
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using rankAccumulator_outputsInTime input

#print axioms RankAccumulator.input_length
#print axioms RankAccumulator.output_length
#print axioms rankAccumulator_outputsInTime
#print axioms rankAccumulatorComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
