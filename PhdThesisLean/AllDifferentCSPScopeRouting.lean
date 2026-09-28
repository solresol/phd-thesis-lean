import PhdThesisLean.AllDifferentCSPScopeExtraction

/-!
# Route an extracted scope query while retaining its continuation

The finite pass duplicates the two binary endpoints, sends the extracted head
to the one-scope predicate, and retains the exact unprocessed counted scopes.
Every copy and restoration step is charged to the actual encoded input length.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace ScopeRouting

abbrev Input := ScopeExtraction.Input
abbrev Remaining := (ℕ × ℕ) × List (List ℕ)
abbrev Output := ScopeQueries.Input × Remaining

abbrev inputFinEncoding : FinEncoding Input := ScopeExtraction.outputFinEncoding

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding ScopeQueries.inputFinEncoding
    ScopeExtraction.remainingFinEncoding

/-- The query and the retained tail use exactly the same two endpoints. -/
def prepare (input : Input) : Output :=
  (ScopeExtraction.query input, ScopeExtraction.remaining input)

/-- Exactly one extra copy of each binary endpoint is added. -/
theorem output_length (input : Input) :
    (outputFinEncoding.encode (prepare input)).length =
      (inputFinEncoding.encode input).length +
        (ScopeExtraction.endpointsFinEncoding.encode input.1).length := by
  simp [outputFinEncoding, prepare, ScopeExtraction.query,
    ScopeExtraction.remaining, ScopeExtraction.outputFinEncoding,
    ScopeExtraction.payloadFinEncoding, ScopeExtraction.remainingFinEncoding,
    ScopeQueries.inputFinEncoding, ScopeExtraction.endpointsFinEncoding,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem output_length_le (input : Input) :
    (outputFinEncoding.encode (prepare input)).length ≤
      2 * (inputFinEncoding.encode input).length := by
  rw [output_length]
  have h : (ScopeExtraction.endpointsFinEncoding.encode input.1).length ≤
      (inputFinEncoding.encode input).length := by
    simp [ScopeExtraction.outputFinEncoding]
  omega

end ScopeRouting

namespace ScopeRoutingMachine

abbrev Input := Sum (Sum Bool Bool) (Sum (Option Bool) (Option Bool))
abbrev Query := Sum (Sum Bool Bool) (Option Bool)
abbrev Output := Sum Query Query
abbrev State := Option Input × Option Output

inductive Stack
  | input | left | right | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | emitRight | emitLeft
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input | _ => Output

def leftCell : Input → Option Output
  | .inl endpoint => some (.inl (.inl endpoint))
  | .inr (.inl cell) => some (.inl (.inr cell))
  | .inr (.inr _) => none

def rightCell : Input → Option Output
  | .inl endpoint => some (.inr (.inl endpoint))
  | .inr (.inl _) => none
  | .inr (.inr cell) => some (.inr (.inr cell))

private def observe (_ : State) (cell : Option Input) : State := (cell, none)
private def remember (_ : State) (cell : Option Output) : State := (none, cell)
private def cell (s : State) : Input := s.1.getD (.inr (.inr none))
private def out (s : State) : Output := s.2.getD (.inr (.inr none))

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch (fun s => s.1.isSome)
      (.branch (fun s => (leftCell (cell s)).isSome)
        (.push .left (fun s => (leftCell (cell s)).getD (.inl (.inr none))) <|
          .branch (fun s => (rightCell (cell s)).isSome)
            (.push .right (fun s => (rightCell (cell s)).getD (.inr (.inr none))) <|
              .goto fun _ => .scan)
            (.goto fun _ => .scan))
        (.push .right (fun s => (rightCell (cell s)).getD (.inr (.inr none))) <|
          .goto fun _ => .scan))
      (.goto fun _ => .emitRight)
  | .emitRight => .pop .right remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitRight)
      (.goto fun _ => .emitLeft)
  | .emitLeft => .pop .left remember <| .branch (fun s => s.2.isSome)
      (.push .output out <| .goto fun _ => .emitLeft)
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

private def stackContents (input : List Input) (left right output : List Output) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .left => left | .right => right | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (left right output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input left right output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "scope_routing_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe,
    remember, cell, out, leftCell, rightCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (input : List Input) (left right output : List Output) (state : State) :
    Run (cfg (some .scan) state input left right output)
      (cfg (some .emitRight) (none, none) []
        ((input.filterMap leftCell).reverse ++ left)
        ((input.filterMap rightCell).reverse ++ right) output) (input.length + 1) := by
  induction input generalizing left right state with
  | nil => exact one (by scope_routing_step)
  | cons bit input ih =>
      cases bit with
      | inl endpoint =>
          have h : Run (cfg (some .scan) state (.inl endpoint :: input) left right output)
              (cfg (some .scan) (some (.inl endpoint), none) input
                (.inl (.inl endpoint) :: left) (.inr (.inl endpoint) :: right) output) 1 :=
            one (by scope_routing_step)
          simpa [leftCell, rightCell, List.reverse_cons, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih _ _ _)
      | inr branch =>
          cases branch with
          | inl bit =>
              have h : Run (cfg (some .scan) state (.inr (.inl bit) :: input) left right output)
                  (cfg (some .scan) (some (.inr (.inl bit)), none) input
                    (.inl (.inr bit) :: left) right output) 1 := one (by scope_routing_step)
              simpa [leftCell, rightCell, List.reverse_cons, List.append_assoc,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih _ _ _)
          | inr bit =>
              have h : Run (cfg (some .scan) state (.inr (.inr bit) :: input) left right output)
                  (cfg (some .scan) (some (.inr (.inr bit)), none) input
                    left (.inr (.inr bit) :: right) output) 1 := one (by scope_routing_step)
              simpa [leftCell, rightCell, List.reverse_cons, List.append_assoc,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih _ _ _)

private def right_run (left right output : List Output) (state : State) :
    Run (cfg (some .emitRight) state [] left right output)
      (cfg (some .emitLeft) (none, none) [] left [] (right.reverse ++ output))
      (right.length + 1) := by
  induction right generalizing output state with
  | nil => exact one (by scope_routing_step)
  | cons bit right ih =>
      have h : Run (cfg (some .emitRight) state [] left (bit :: right) output)
          (cfg (some .emitRight) (none, some bit) [] left right (bit :: output)) 1 :=
        one (by scope_routing_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih _ _)

private def left_run (left output : List Output) (state : State) :
    Run (cfg (some .emitLeft) state [] left [] output)
      (cfg none (none, none) [] [] [] (left.reverse ++ output)) (left.length + 1) := by
  induction left generalizing output state with
  | nil => exact one (by scope_routing_step)
  | cons bit left ih =>
      have h : Run (cfg (some .emitLeft) state [] (bit :: left) [] output)
          (cfg (some .emitLeft) (none, some bit) [] left [] (bit :: output)) 1 :=
        one (by scope_routing_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih _ _)

/-- Routing preserves the query and continuation order and clears both work stacks. -/
private def run (input : List Input) :
    Run (cfg (some .scan) (none, none) input [] [] [])
      (cfg none (none, none) [] [] []
        (input.filterMap leftCell ++ input.filterMap rightCell)) (3 * input.length + 3) := by
  have scan := scan_run input [] [] [] (none, none)
  simp only [List.append_nil] at scan
  have right := right_run (input.filterMap leftCell).reverse
    (input.filterMap rightCell).reverse [] (none, none)
  have left := left_run (input.filterMap leftCell).reverse
    (input.filterMap rightCell) (none, none)
  simp only [List.reverse_reverse, List.append_nil] at right left
  have composed := seq (seq scan right) left
  apply evalsToInTimeMono composed
  simp only [List.length_reverse]
  have hl := List.length_filterMap_le leftCell input
  have hr := List.length_filterMap_le rightCell input
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

/-- Both endpoint copies, the intact head, and the exact tail are routed in order. -/
private theorem routed_encode (input : ScopeRouting.Input) :
    (ScopeRouting.inputFinEncoding.encode input).filterMap leftCell ++
      (ScopeRouting.inputFinEncoding.encode input).filterMap rightCell =
      ScopeRouting.outputFinEncoding.encode (ScopeRouting.prepare input) := by
  have discard {α β : Type} (bits : List α) :
      bits.filterMap (fun _ => (none : Option β)) = [] := by simp
  simp [ScopeRouting.outputFinEncoding, ScopeRouting.prepare,
    ScopeExtraction.outputFinEncoding, ScopeExtraction.payloadFinEncoding,
    ScopeExtraction.endpointsFinEncoding, ScopeExtraction.remainingFinEncoding,
    ScopeExtraction.query, ScopeExtraction.remaining, ScopeQueries.inputFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding, List.filterMap_map, Function.comp_def,
    leftCell, rightCell, List.map_append, List.map_map, List.append_assoc, discard]

end ScopeRoutingMachine

/-- Construct the query and continuation in at most `3s+3` finite-machine steps, including
endpoint duplication, every head/tail cell and final cleanup. -/
def scopeRouting_outputsInTime (input : ScopeRouting.Input) :
    TM2OutputsInTime ScopeRoutingMachine.computer (ScopeRouting.inputFinEncoding.encode input)
      (some (ScopeRouting.outputFinEncoding.encode (ScopeRouting.prepare input)))
      (3 * (ScopeRouting.inputFinEncoding.encode input).length + 3) := by
  rw [TM2OutputsInTime, ScopeRoutingMachine.init_eq]
  simp only [Option.map_some]
  rw [ScopeRoutingMachine.halt_eq, ← ScopeRoutingMachine.routed_encode]
  exact ScopeRoutingMachine.run _

noncomputable def scopeRoutingComputableInPolyTime :
    @TM2ComputableInPolyTime ScopeRouting.Input ScopeRouting.Output
      ScopeRouting.inputFinEncoding ScopeRouting.outputFinEncoding ScopeRouting.prepare where
  tm := ScopeRoutingMachine.computer
  inputAlphabet := Equiv.refl ScopeRoutingMachine.Input
  outputAlphabet := Equiv.refl ScopeRoutingMachine.Output
  time := 3 * Polynomial.X + 3
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_X] using scopeRouting_outputsInTime input

#print axioms ScopeRouting.output_length
#print axioms ScopeRouting.output_length_le
#print axioms scopeRouting_outputsInTime
#print axioms scopeRoutingComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
