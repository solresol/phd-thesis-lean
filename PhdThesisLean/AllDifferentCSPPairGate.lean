import PhdThesisLean.AllDifferentCSPPairControl

/-!
# Conditional calls on the retained pair-scan state

The finite controller inspects the tagged Boolean, invokes the supplied checked
state transformer only on the selected answer, and otherwise returns the exact
input. Both paths restore wire order and clear all scratch stacks. This local
controller uses the existing composition runtime and finite-machine interfaces.
-/

namespace PhdThesisLean.AllDifferentCSPMachine.PairGateMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

noncomputable section

variable {f : PairTest.Output → PairTest.Output}
  (body : @TM2ComputableInPolyTime PairTest.Output PairTest.Output
    PairTest.outputFinEncoding PairTest.outputFinEncoding f) (selected : Bool)

abbrev Wire := Sum Bool PairQueriesMachine.Input

/-- Only the actual leading answer cell body selects the call. -/
def sourceCell : Wire → Bool
  | .inl answer => answer == selected
  | _ => false

theorem source_present (input : PairTest.Output) :
    (PairTest.outputFinEncoding.encode input).any (sourceCell selected) =
      (input.1 == selected) := by
  simp [PairTest.outputFinEncoding, LeanNPHardness.PairEncoding.finEncoding,
    finEncodingBoolBool, encodeBool, List.any_map, Function.comp_def, sourceCell]

inductive External
  | input | saved | output
  deriving DecidableEq, Fintype

abbrev Stack := body.tm.K ⊕ External
abbrev Alphabet : (Stack body) → Type
  | .inl k => body.tm.Γ k
  | .inr .input | .inr .saved => Wire
  | .inr .output => Wire

inductive Control
  | scan | fill | collect | finish
  deriving DecidableEq, Fintype

abbrev Label := body.tm.Λ ⊕ Control
abbrev State := body.tm.σ × Bool × Option Wire

instance : Fintype body.tm.K := body.tm.kFin
instance : Fintype body.tm.Λ := body.tm.ΛFin
instance : Fintype body.tm.σ := body.tm.σFin

def initialState : (State body) := (body.tm.initialState, false, none)

private def observe (s : (State body)) (symbol : Option Wire) : (State body) := (s.1, s.2.1, symbol)
private def cell (s : (State body)) : Wire := s.2.2.getD (.inl false)

/-- The local call embedding changes only stack addresses and control. A body
halt returns to collection without executing a further body step. -/
def lift : TM2.Stmt body.tm.Γ body.tm.Λ body.tm.σ → TM2.Stmt (Alphabet body) (Label body) (State body)
  | .push k write next => .push (.inl k) (fun s => write s.1) (lift next)
  | .peek k read next => .peek (.inl k) (fun s bit => (read s.1 bit, s.2)) (lift next)
  | .pop k read next => .pop (.inl k) (fun s bit => (read s.1 bit, s.2)) (lift next)
  | .load update next => .load (fun s => (update s.1, s.2)) (lift next)
  | .branch test yes no => .branch (fun s => test s.1) (lift yes) (lift no)
  | .goto next => .goto (fun s => .inl (next s.1))
  | .halt => .goto (fun _ => .inr .collect)

def program : (Label body) → TM2.Stmt (Alphabet body) (Label body) (State body)
  | .inl label => lift body (body.tm.m label)
  | .inr .scan => .pop (.inr .input) (observe body) <|
      .branch (fun s => s.2.2.isSome)
        (.push (.inr .saved) (cell body) <|
          .load (fun s => (s.1, s.2.1 || sourceCell selected (cell body s), s.2.2)) <|
          .goto fun _ => .inr .scan)
        (.branch (fun s => s.2.1)
          (.goto fun _ => .inr .fill) (.goto fun _ => .inr .finish))
  | .inr .fill => .pop (.inr .saved) (observe body) <|
      .branch (fun s => s.2.2.isSome)
        (.push (.inl body.tm.k₀) (fun s => body.inputAlphabet.symm (cell body s)) <|
          .goto fun _ => .inr .fill)
        (.load (fun _ => (initialState body)) <| .goto fun _ => .inl body.tm.main)
  | .inr .collect => .pop (.inl body.tm.k₁)
      (fun s bit => observe body s (bit.map body.outputAlphabet)) <|
      .branch (fun s => s.2.2.isSome)
        (.push (.inr .saved) (cell body) <| .goto fun _ => .inr .collect)
        (.goto fun _ => .inr .finish)
  | .inr .finish => .pop (.inr .saved) (observe body) <|
      .branch (fun s => s.2.2.isSome)
        (.push (.inr .output) (cell body) <| .goto fun _ => .inr .finish)
        (.load (fun _ => (initialState body)) .halt)

def computer : FinTM2 where
  K := (Stack body)
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := (Alphabet body)
  Λ := (Label body)
  main := .inr .scan
  σ := (State body)
  initialState := (initialState body)
  Γk₀Fin := inferInstance
  m := (program body selected)

def stackContents (input saved : List Wire) (output : List Wire)
    (contents : (k : body.tm.K) → List (body.tm.Γ k)) : (k : (Stack body)) → List ((Alphabet body) k)
  | .inl k => contents k
  | .inr .input => input
  | .inr .saved => saved
  | .inr .output => output

def cfg (label : Option (Label body)) (state : (State body)) (input saved : List Wire)
    (output : List Wire) (contents : (k : body.tm.K) → List (body.tm.Γ k)) : (computer body selected).Cfg :=
  ⟨label, state, (stackContents body) input saved output contents⟩

def empty : (k : body.tm.K) → List (body.tm.Γ k) := fun _ => []

def single (k : body.tm.K) (bits : List (body.tm.Γ k)) := Function.update (empty body) k bits

def ready (input : PairTest.Output) : (computer body selected).Cfg :=
  cfg body selected (some (.inr .scan)) (initialState body) (PairTest.outputFinEncoding.encode input) [] [] (empty body)

def done (answer : PairTest.Output) : (computer body selected).Cfg :=
  cfg body selected none (initialState body) [] [] (PairTest.outputFinEncoding.encode answer) (empty body)

abbrev Run (a b : (computer body selected).Cfg) (time : ℕ) := EvalsToInTime (computer body selected).step a (some b) time

private def one {a b : (computer body selected).Cfg} (h : (computer body selected).step a = some b) : Run body selected a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }

def seq {a b c : (computer body selected).Cfg} {m n : ℕ}
    (h : Run body selected a b m) (h' : Run body selected b c n) : Run body selected a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans (computer body selected).step m n a b (some c) h h'

private def embed (config : body.tm.Cfg) : (computer body selected).Cfg :=
  cfg body selected (some (config.l.elim (.inr .collect) Sum.inl)) (config.var, false, none) [] [] [] config.stk

private theorem stackContents_update (input saved : List Wire) (output : List Wire)
    (contents : (k : body.tm.K) → List (body.tm.Γ k)) (k : body.tm.K) (value : List (body.tm.Γ k)) :
    (stackContents body) input saved output (Function.update contents k value) =
      Function.update ((stackContents body) input saved output contents) (.inl k) value := by
  funext index
  cases index with
  | inr index => cases index <;> simp [stackContents]
  | inl index =>
      by_cases h : index = k
      · subst index; simp [stackContents]
      · simp [stackContents, Function.update, h]

private theorem lift_stepAux (stmt : TM2.Stmt body.tm.Γ body.tm.Λ body.tm.σ)
    (state : body.tm.σ) (contents : (k : body.tm.K) → List (body.tm.Γ k)) :
    TM2.stepAux (lift body stmt) (state, false, none) ((stackContents body) [] [] [] contents) =
      (embed body selected) (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [lift, TM2.stepAux]
      rw [← (stackContents_update body)]
      exact ih _ _
  | peek k read next ih => simpa only [lift, TM2.stepAux, stackContents] using ih _ _
  | pop k read next ih =>
      simp only [lift, TM2.stepAux, stackContents]
      rw [← (stackContents_update body)]
      exact ih _ _
  | load update next ih => simpa only [lift, TM2.stepAux] using ih _ _
  | branch test yes no iy ino =>
      cases h : test state <;> simp only [lift, TM2.stepAux, h, cond_false, cond_true]
      · exact ino _ _
      · exact iy _ _
  | goto next => rfl
  | halt => rfl

private theorem body_step (config : body.tm.Cfg) (h : config.l ≠ none) :
    (computer body selected).step ((embed body selected) config) = (body.tm.step config).map (embed body selected) := by
  rcases config with ⟨label, state, contents⟩
  cases label with
  | none => simp at h
  | some label =>
      simp only [computer, FinTM2.step, embed, cfg, program, Option.elim_some,
        TM2.step, Option.map_some]
      congr 1
      exact (lift_stepAux body selected) (body.tm.m label) state contents

private theorem body_iterate (n : ℕ) (start finish : body.tm.Cfg)
    (h : (fun c => c.bind body.tm.step)^[n] (some start) = some finish) :
    (fun c => c.bind (computer body selected).step)^[n] (some ((embed body selected) start)) = some ((embed body selected) finish) := by
  induction n generalizing start with
  | zero => simpa using congrArg (Option.map (embed body selected)) h
  | succ n ih =>
      have hn : (fun c => c.bind body.tm.step)^[n] none = none :=
        Function.iterate_fixed (by rfl) n
      rw [Function.iterate_succ_apply] at h ⊢
      change (fun c => c.bind body.tm.step)^[n] (body.tm.step start) = some finish at h
      change (fun c => c.bind (computer body selected).step)^[n] ((computer body selected).step ((embed body selected) start)) = _
      have hl : start.l ≠ none := by
        intro hl
        have hs : body.tm.step start = none := by
          rcases start with ⟨label, state, contents⟩
          change label = none at hl
          subst label
          rfl
        rw [hs, hn] at h
        contradiction
      rw [(body_step body selected) start hl]
      cases hs : body.tm.step start with
      | none => rw [hs, hn] at h; contradiction
      | some mid =>
          simp only [Option.map_some]
          exact ih mid (by rw [hs] at h; exact h)

private theorem single_eq (k : body.tm.K) (bits : List (body.tm.Γ k)) :
    single body k bits = fun j => if h : j = k then (by rw [h]; exact bits) else [] := by
  funext j
  by_cases h : j = k
  · subst j; simp [single]
  · simp [single, empty, Function.update, h]

/-- The already checked state transformer runs inside the conditional call unchanged,
then returns with every body work stack (empty body). -/
def body_run (input : PairTest.Output) :
    Run body selected
      (cfg body selected (some (.inl body.tm.main))
        (initialState body) [] [] []
        (single body body.tm.k₀ ((PairTest.outputFinEncoding.encode input).map body.inputAlphabet.symm)))
      (cfg body selected (some (.inr .collect))
        (initialState body) [] [] []
        (single body body.tm.k₁ ((PairTest.outputFinEncoding.encode (f input)).map body.outputAlphabet.symm)))
      (body.time.eval (PairTest.outputFinEncoding.encode input).length) where
  steps := (body.outputsFun input).steps
  evals_in_steps := by
    have h := body_iterate body selected _ _ _ (body.outputsFun input).evals_in_steps
    simpa only [embed, initList, haltList, single_eq, initialState,
      Option.elim_some, Option.elim_none] using h
  steps_le_m := (body.outputsFun input).steps_le_m

local macro "gate_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, initialState,
    observe, cell, empty, Function.update]
   <;> first | rfl | (funext k; cases k with
     | inl k => rfl
     | inr k => cases k <;> rfl)))

private def scan_run (input saved : List Wire) (seen : Bool) (last : Option Wire) :
    Run body selected
      (cfg body selected (some (.inr .scan))
        (body.tm.initialState, seen, last) input saved [] (empty body))
      (cfg body selected (some (.inr (if seen || input.any (sourceCell selected) then .fill else .finish)))
        (body.tm.initialState, seen || input.any (sourceCell selected), none)
        [] (input.reverse ++ saved) [] (empty body)) (input.length + 1) := by
  induction input generalizing saved seen last with
  | nil => cases seen <;> exact one body selected (by gate_step)
  | cons bit input ih =>
      have h : Run body selected
          (cfg body selected (some (.inr .scan))
        (body.tm.initialState, seen, last) (bit :: input) saved [] (empty body))
          (cfg body selected (some (.inr .scan))
        (body.tm.initialState, seen || sourceCell selected bit, some bit)
            input (bit :: saved) [] (empty body)) 1 := one body selected (by gate_step)
      simpa only [List.any_cons, List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append, Bool.or_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          seq body selected h (ih (bit :: saved) (seen || sourceCell selected bit) (some bit))

private theorem single_nil (k : body.tm.K) : single body k [] = (empty body) := by
  exact Function.update_eq_self k (empty body)

private def fill_run (saved : List Wire) (bits : List (body.tm.Γ body.tm.k₀))
    (seen : Bool) (last : Option Wire) :
    Run body selected
      (cfg body selected (some (.inr .fill))
        (body.tm.initialState, seen, last) [] saved []
        (single body body.tm.k₀ bits))
      (cfg body selected (some (.inl body.tm.main))
        (initialState body) [] [] []
        (single body body.tm.k₀ (saved.reverse.map body.inputAlphabet.symm ++ bits)))
      (saved.length + 1) := by
  induction saved generalizing bits last with
  | nil => exact one body selected (by gate_step)
  | cons bit saved ih =>
      have h : Run body selected
          (cfg body selected (some (.inr .fill))
        (body.tm.initialState, seen, last) [] (bit :: saved) []
            (single body body.tm.k₀ bits))
          (cfg body selected (some (.inr .fill))
        (body.tm.initialState, seen, some bit) [] saved []
            (single body body.tm.k₀ (body.inputAlphabet.symm bit :: bits))) 1 := by
        apply one body selected
        simp only [computer, FinTM2.step, TM2.step, cfg, program, TM2.stepAux, stackContents,
          observe, cell, List.head?_cons, List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
        congr 2
        funext k
        cases k with
        | inl k =>
            by_cases hk : k = body.tm.k₀
            · subst k; simp [single, stackContents]
            · simp [single, stackContents, Function.update, hk]
        | inr k => cases k <;> simp [stackContents]
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
          seq body selected h (ih (body.inputAlphabet.symm bit :: bits) (some bit))

private def collect_run (bits : List (body.tm.Γ body.tm.k₁)) (saved : List Wire) (last : Option Wire) :
    Run body selected
      (cfg body selected (some (.inr .collect))
        (body.tm.initialState, false, last) [] saved []
        (single body body.tm.k₁ bits))
      (cfg body selected (some (.inr .finish))
        (body.tm.initialState, false, none) []
        (List.append (α := Wire) (bits.reverse.map body.outputAlphabet) saved) [] (empty body)) (bits.length + 1) := by
  induction bits generalizing saved last with
  | nil =>
      rw [(single_nil body)]
      exact one body selected (by gate_step)
  | cons bit bits ih =>
      have h : Run body selected
          (cfg body selected (some (.inr .collect))
        (body.tm.initialState, false, last) [] saved []
            (single body body.tm.k₁ (bit :: bits)))
          (cfg body selected (some (.inr .collect))
        (body.tm.initialState, false, some (body.outputAlphabet bit))
            [] (body.outputAlphabet bit :: saved) [] (single body body.tm.k₁ bits)) 1 := by
        apply one body selected
        simp only [computer, FinTM2.step, TM2.step, cfg, program, TM2.stepAux, stackContents,
          single, Function.update_self, List.head?_cons, List.tail_cons, Option.map_some,
          observe, cell, List.head?_cons, List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
        congr 2
        funext k
        cases k with
        | inl k =>
            by_cases hk : k = body.tm.k₁
            · subst k; simp [stackContents]
            · simp [stackContents, Function.update, hk]
        | inr k => cases k <;> simp [stackContents]
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq body selected h (ih (body.outputAlphabet bit :: saved) (some (body.outputAlphabet bit)))

private def finish_run (saved output : List Wire) (seen : Bool) (last : Option Wire) :
    Run body selected
      (cfg body selected (some (.inr .finish))
        (body.tm.initialState, seen, last) [] saved output (empty body))
      (cfg body selected none (initialState body) [] [] (saved.reverse ++ output) (empty body)) (saved.length + 1) := by
  induction saved generalizing output last with
  | nil => exact one body selected (by gate_step)
  | cons bit saved ih =>
      have h : Run body selected
          (cfg body selected (some (.inr .finish))
        (body.tm.initialState, seen, last) [] (bit :: saved) output (empty body))
          (cfg body selected (some (.inr .finish))
        (body.tm.initialState, seen, some bit) [] saved (bit :: output) (empty body)) 1 :=
        one body selected (by gate_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq body selected h (ih (bit :: output) (some bit))
/-- A selected call loads every original cell in order. -/
def enter_run (input : PairTest.Output) (h : input.1 = selected) :
    Run body selected (ready body selected input)
      (cfg body selected (some (.inl body.tm.main))
        (initialState body) [] [] []
        (single body body.tm.k₀ ((PairTest.outputFinEncoding.encode input).map body.inputAlphabet.symm)))
      (2 * (PairTest.outputFinEncoding.encode input).length + 2) := by
  have hs := scan_run body selected (PairTest.outputFinEncoding.encode input) [] false none
  rw [source_present] at hs
  simp only [h, beq_self_eq_true, Bool.false_or, ite_true, List.append_nil] at hs
  have hf := fill_run body selected (PairTest.outputFinEncoding.encode input).reverse [] true none
  simp only [single_nil, List.reverse_reverse, List.append_nil, List.length_reverse] at hf
  convert seq body selected hs hf using 1
  omega

/-- Collection and output both empty their scratch stacks. -/
def return_run (output : PairTest.Output) :
    Run body selected
      (cfg body selected (some (.inr .collect))
        (initialState body) [] [] []
        (single body body.tm.k₁ ((PairTest.outputFinEncoding.encode output).map body.outputAlphabet.symm)))
      (done body selected output) (2 * (PairTest.outputFinEncoding.encode output).length + 2) := by
  have hc := collect_run body selected
    ((PairTest.outputFinEncoding.encode output).map body.outputAlphabet.symm) [] none
  simp only [← List.map_reverse, List.map_map, Equiv.apply_symm_apply, Function.comp_def,
    List.map_id_fun', List.append_eq, List.append_nil, List.length_map] at hc
  have hf := finish_run body selected (PairTest.outputFinEncoding.encode output).reverse [] false none
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hf
  convert seq body selected hc hf using 1
  omega

/-- An unselected body is never entered; its stacks stay empty. -/
def skip_run (input : PairTest.Output) (h : input.1 ≠ selected) :
    Run body selected (ready body selected input) (done body selected input)
      (2 * (PairTest.outputFinEncoding.encode input).length + 2) := by
  have hs := scan_run body selected (PairTest.outputFinEncoding.encode input) [] false none
  rw [source_present] at hs
  have hb : (input.1 == selected) = false := beq_eq_false_iff_ne.mpr h
  simp only [hb, Bool.false_or, List.append_nil] at hs
  have hf := finish_run body selected (PairTest.outputFinEncoding.encode input).reverse [] false none
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hf
  convert seq body selected hs hf using 1
  omega

/-- Full invocation, including deciding the branch and all four transfers. -/
def call_run (input : PairTest.Output) (h : input.1 = selected) :
    Run body selected (ready body selected input) (done body selected (f input))
      (body.time.eval (PairTest.outputFinEncoding.encode input).length +
        2 * (PairTest.outputFinEncoding.encode input).length +
        2 * (PairTest.outputFinEncoding.encode (f input)).length + 4) := by
  convert seq body selected (seq body selected (enter_run body selected input h)
    (body_run body selected input)) (return_run body selected (f input)) using 1
  omega

theorem ready_eq_initList (input : PairTest.Output) :
    ready body selected input = initList (computer body selected)
      (PairTest.outputFinEncoding.encode input) := by
  simp only [ready, initList, computer, cfg, initialState]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

theorem done_eq_haltList (output : PairTest.Output) :
    done body selected output = haltList (computer body selected)
      (PairTest.outputFinEncoding.encode output) := by
  simp only [done, haltList, computer, cfg, initialState]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

/-- The output-size bound comes from the existing generic finite-program bound. -/
def time : Polynomial ℕ := body.time + 2 * Polynomial.X +
  2 * outputSizePolynomial PairTest.outputFinEncoding PairTest.outputFinEncoding f body + 4

def outputsInTime (input : PairTest.Output) :
    TM2OutputsInTime (computer body selected) (PairTest.outputFinEncoding.encode input)
      (some (PairTest.outputFinEncoding.encode (if input.1 = selected then f input else input)))
      ((time body).eval (PairTest.outputFinEncoding.encode input).length) := by
  rw [TM2OutputsInTime]
  simp only [Option.map_some, ← ready_eq_initList, ← done_eq_haltList]
  by_cases h : input.1 = selected
  · rw [if_pos h]
    apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (call_run body selected input h)
    have size := LeanNPHardness.MachineRuntime.computableInPolyTime_output_length_le
      PairTest.outputFinEncoding PairTest.outputFinEncoding f body input
    simp only [time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, outputSizePolynomial_eval]
    omega
  · rw [if_neg h]
    apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (skip_run body selected input h)
    simp only [time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    omega

/-- A polynomial-time conditional call on the exact Boolean/pair-state wire. -/
def computableInPolyTime :
    @TM2ComputableInPolyTime PairTest.Output PairTest.Output
      PairTest.outputFinEncoding PairTest.outputFinEncoding
      (fun input => if input.1 = selected then f input else input) where
  tm := computer body selected
  inputAlphabet := Equiv.refl Wire
  outputAlphabet := Equiv.refl Wire
  time := time body
  outputsFun input := by simpa [Equiv.refl] using outputsInTime body selected input

#print axioms source_present
#print axioms skip_run
#print axioms call_run
#print axioms outputsInTime
#print axioms computableInPolyTime

end

end PhdThesisLean.AllDifferentCSPMachine.PairGateMachine
