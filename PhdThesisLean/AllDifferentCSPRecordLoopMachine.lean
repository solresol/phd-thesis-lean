import PhdThesisLean.AllDifferentCSPScopeAccumulator

/-!
# Shared finite dispatcher for counted CSP records

Factored from the checked scope loop. Both scopes and ranked occurrences use
this exact tagged alphabet: an answer bit, two query fields, and counted record
cells. The controller is parameterized by its checked iteration machine; it
adds no assumptions about record semantics. Scan, call, return and cleanup are
proved once and reused by both traversals.
-/

namespace PhdThesisLean.AllDifferentCSPMachine.RecordLoopMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

abbrev Wire := ScopeAccumulatorMachine.Output

def sourceCell : Wire → Bool
  | .inr (.inr _) => true
  | _ => false

structure Body where
  tm : FinTM2
  inputAlphabet : tm.Γ tm.k₀ ≃ Wire
  outputAlphabet : tm.Γ tm.k₁ ≃ Wire

variable {body : Body}

inductive External
  | input | saved | output
  deriving DecidableEq, Fintype

abbrev Stack := body.tm.K ⊕ External
abbrev Alphabet : (Stack (body := body)) → Type
  | .inl k => body.tm.Γ k
  | .inr .input | .inr .saved => Wire
  | .inr .output => Bool

inductive Control
  | scan | fill | collect | restore | finish
  deriving DecidableEq, Fintype

abbrev Label := body.tm.Λ ⊕ Control
abbrev State := body.tm.σ × Bool × Option Wire

instance : Fintype body.tm.K := body.tm.kFin
instance : Fintype body.tm.Λ := body.tm.ΛFin
instance : Fintype body.tm.σ := body.tm.σFin

def initialState : (State (body := body)) := (body.tm.initialState, false, none)

private def observe (s : (State (body := body))) (cell : Option Wire) : (State (body := body)) := (s.1, s.2.1, cell)
private def cell (s : (State (body := body))) : Wire := s.2.2.getD (.inl false)

/-- The local call embedding changes only stack addresses and control. A body
halt returns to collection without executing a further body step. -/
def lift : TM2.Stmt body.tm.Γ body.tm.Λ body.tm.σ → TM2.Stmt (Alphabet (body := body)) (Label (body := body)) (State (body := body))
  | .push k write next => .push (.inl k) (fun s => write s.1) (lift next)
  | .peek k read next => .peek (.inl k) (fun s bit => (read s.1 bit, s.2)) (lift next)
  | .pop k read next => .pop (.inl k) (fun s bit => (read s.1 bit, s.2)) (lift next)
  | .load update next => .load (fun s => (update s.1, s.2)) (lift next)
  | .branch test yes no => .branch (fun s => test s.1) (lift yes) (lift no)
  | .goto next => .goto (fun s => .inl (next s.1))
  | .halt => .goto (fun _ => .inr .collect)

def program : (Label (body := body)) → TM2.Stmt (Alphabet (body := body)) (Label (body := body)) (State (body := body))
  | .inl label => lift (body.tm.m label)
  | .inr .scan => .pop (.inr .input) observe <|
      .branch (fun s => s.2.2.isSome)
        (.push (.inr .saved) cell <|
          .load (fun s => (s.1, s.2.1 || sourceCell (cell s), s.2.2)) <|
          .goto fun _ => .inr .scan)
        (.branch (fun s => s.2.1)
          (.goto fun _ => .inr .fill) (.goto fun _ => .inr .finish))
  | .inr .fill => .pop (.inr .saved) observe <|
      .branch (fun s => s.2.2.isSome)
        (.push (.inl body.tm.k₀) (fun s => body.inputAlphabet.symm (cell s)) <|
          .goto fun _ => .inr .fill)
        (.load (fun _ => initialState) <| .goto fun _ => .inl body.tm.main)
  | .inr .collect => .pop (.inl body.tm.k₁)
      (fun s bit => observe s (bit.map body.outputAlphabet)) <|
      .branch (fun s => s.2.2.isSome)
        (.push (.inr .saved) cell <| .goto fun _ => .inr .collect)
        (.goto fun _ => .inr .restore)
  | .inr .restore => .pop (.inr .saved) observe <|
      .branch (fun s => s.2.2.isSome)
        (.push (.inr .input) cell <| .goto fun _ => .inr .restore)
        (.load (fun _ => initialState) <| .goto fun _ => .inr .scan)
  | .inr .finish => .pop (.inr .saved) observe <|
      .branch (fun s => s.2.2.isSome)
        (.branch (fun s => (cell s).getLeft?.isSome)
          (.push (.inr .output) (fun s => (cell s).getLeft?.getD false) <|
            .goto fun _ => .inr .finish)
          (.goto fun _ => .inr .finish))
        (.load (fun _ => initialState) .halt)

def computer : FinTM2 where
  K := (Stack (body := body))
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := (Alphabet (body := body))
  Λ := (Label (body := body))
  main := .inr .scan
  σ := (State (body := body))
  initialState := initialState
  Γk₀Fin := inferInstance
  m := program

def stackContents (input saved : List Wire) (output : List Bool)
    (contents : (k : body.tm.K) → List (body.tm.Γ k)) : (k : (Stack (body := body))) → List ((Alphabet (body := body)) k)
  | .inl k => contents k
  | .inr .input => input
  | .inr .saved => saved
  | .inr .output => output

def cfg (label : Option (Label (body := body))) (state : (State (body := body))) (input saved : List Wire)
    (output : List Bool) (contents : (k : body.tm.K) → List (body.tm.Γ k)) : (computer (body := body)).Cfg :=
  ⟨label, state, stackContents input saved output contents⟩

def empty : (k : body.tm.K) → List (body.tm.Γ k) := fun _ => []

def single (k : body.tm.K) (bits : List (body.tm.Γ k)) := Function.update empty k bits

def ready (input : List Wire) : (computer (body := body)).Cfg :=
  cfg (some (.inr .scan)) initialState input [] [] empty

def done (answer : Bool) : (computer (body := body)).Cfg :=
  cfg none initialState [] [] (finEncodingBoolBool.encode answer) empty

abbrev Run (a b : (computer (body := body)).Cfg) (time : ℕ) := EvalsToInTime (computer (body := body)).step a (some b) time

private def one {a b : (computer (body := body)).Cfg} (h : (computer (body := body)).step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }

def seq {a b c : (computer (body := body)).Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans (computer (body := body)).step m n a b (some c) h h'

private def embed (config : body.tm.Cfg) : (computer (body := body)).Cfg :=
  cfg (some (config.l.elim (.inr .collect) Sum.inl)) (config.var, false, none) [] [] [] config.stk

private theorem stackContents_update (input saved : List Wire) (output : List Bool)
    (contents : (k : body.tm.K) → List (body.tm.Γ k)) (k : body.tm.K) (value : List (body.tm.Γ k)) :
    stackContents input saved output (Function.update contents k value) =
      Function.update (stackContents input saved output contents) (.inl k) value := by
  funext index
  cases index with
  | inr index => cases index <;> simp [stackContents]
  | inl index =>
      by_cases h : index = k
      · subst index; simp [stackContents]
      · simp [stackContents, Function.update, h]

private theorem lift_stepAux (stmt : TM2.Stmt body.tm.Γ body.tm.Λ body.tm.σ)
    (state : body.tm.σ) (contents : (k : body.tm.K) → List (body.tm.Γ k)) :
    TM2.stepAux (lift stmt) (state, false, none) (stackContents [] [] [] contents) =
      embed (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [lift, TM2.stepAux]
      rw [← stackContents_update]
      exact ih _ _
  | peek k read next ih => simpa only [lift, TM2.stepAux, stackContents] using ih _ _
  | pop k read next ih =>
      simp only [lift, TM2.stepAux, stackContents]
      rw [← stackContents_update]
      exact ih _ _
  | load update next ih => simpa only [lift, TM2.stepAux] using ih _ _
  | branch test yes no iy ino =>
      cases h : test state <;> simp only [lift, TM2.stepAux, h, cond_false, cond_true]
      · exact ino _ _
      · exact iy _ _
  | goto next => rfl
  | halt => rfl

private theorem body_step (config : body.tm.Cfg) (h : config.l ≠ none) :
    (computer (body := body)).step (embed config) = (body.tm.step config).map embed := by
  rcases config with ⟨label, state, contents⟩
  cases label with
  | none => simp at h
  | some label =>
      simp only [computer, FinTM2.step, embed, cfg, program, Option.elim_some,
        TM2.step, Option.map_some]
      congr 1
      exact lift_stepAux (body.tm.m label) state contents

private theorem body_iterate (n : ℕ) (start finish : body.tm.Cfg)
    (h : (fun c => c.bind body.tm.step)^[n] (some start) = some finish) :
    (fun c => c.bind (computer (body := body)).step)^[n] (some (embed start)) = some (embed finish) := by
  induction n generalizing start with
  | zero => simpa using congrArg (Option.map embed) h
  | succ n ih =>
      have hn : (fun c => c.bind body.tm.step)^[n] none = none :=
        Function.iterate_fixed (by rfl) n
      rw [Function.iterate_succ_apply] at h ⊢
      change (fun c => c.bind body.tm.step)^[n] (body.tm.step start) = some finish at h
      change (fun c => c.bind (computer (body := body)).step)^[n] ((computer (body := body)).step (embed start)) = _
      have hl : start.l ≠ none := by
        intro hl
        have hs : body.tm.step start = none := by
          rcases start with ⟨label, state, contents⟩
          change label = none at hl
          subst label
          rfl
        rw [hs, hn] at h
        contradiction
      rw [body_step start hl]
      cases hs : body.tm.step start with
      | none => rw [hs, hn] at h; contradiction
      | some mid =>
          simp only [Option.map_some]
          exact ih mid (by rw [hs] at h; exact h)

private theorem single_eq (k : body.tm.K) (bits : List (body.tm.Γ k)) :
    single k bits = fun j => if h : j = k then (by rw [h]; exact bits) else [] := by
  funext j
  by_cases h : j = k
  · subst j; simp [single]
  · simp [single, empty, Function.update, h]

/-- Lift a complete checked component execution, preserving its exact bound. -/
def body_run (input output : List Wire) (time : ℕ)
    (run : TM2OutputsInTime body.tm (input.map body.inputAlphabet.symm)
      (some (output.map body.outputAlphabet.symm)) time) :
    Run (cfg (some (.inl body.tm.main)) initialState [] [] []
        (single body.tm.k₀ (input.map body.inputAlphabet.symm)))
      (cfg (some (.inr .collect)) initialState [] [] []
        (single body.tm.k₁ (output.map body.outputAlphabet.symm))) time where
  steps := run.steps
  evals_in_steps := by
    have h := body_iterate _ _ _ run.evals_in_steps
    simpa only [embed, initList, haltList, single_eq, initialState,
      Option.elim_some, Option.elim_none] using h
  steps_le_m := run.steps_le_m

local macro "loop_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, initialState,
    observe, cell, empty, Function.update]
   <;> first | rfl | (funext k; cases k with
     | inl k => rfl
     | inr k => cases k <;> rfl)))

private def scan_run (input saved : List Wire) (seen : Bool) (last : Option Wire) :
    Run (cfg (some (.inr .scan)) (body.tm.initialState, seen, last) input saved [] empty)
      (cfg (some (.inr (if seen || input.any sourceCell then .fill else .finish)))
        (body.tm.initialState, seen || input.any sourceCell, none)
        [] (input.reverse ++ saved) [] empty) (input.length + 1) := by
  induction input generalizing saved seen last with
  | nil => cases seen <;> exact one (by loop_step)
  | cons bit input ih =>
      have h : Run (cfg (some (.inr .scan)) (body.tm.initialState, seen, last) (bit :: input) saved [] empty)
          (cfg (some (.inr .scan)) (body.tm.initialState, seen || sourceCell bit, some bit)
            input (bit :: saved) [] empty) 1 := one (by loop_step)
      simpa only [List.any_cons, List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append, Bool.or_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          seq h (ih (bit :: saved) (seen || sourceCell bit) (some bit))

private theorem single_nil (k : body.tm.K) : single k [] = empty := by
  exact Function.update_eq_self k empty

private def fill_run (saved : List Wire) (bits : List (body.tm.Γ body.tm.k₀))
    (seen : Bool) (last : Option Wire) :
    Run (cfg (some (.inr .fill)) (body.tm.initialState, seen, last) [] saved [] (single body.tm.k₀ bits))
      (cfg (some (.inl body.tm.main)) initialState [] [] []
        (single body.tm.k₀ (saved.reverse.map body.inputAlphabet.symm ++ bits)))
      (saved.length + 1) := by
  induction saved generalizing bits last with
  | nil => exact one (by loop_step)
  | cons bit saved ih =>
      have h : Run (cfg (some (.inr .fill)) (body.tm.initialState, seen, last) [] (bit :: saved) []
            (single body.tm.k₀ bits))
          (cfg (some (.inr .fill)) (body.tm.initialState, seen, some bit) [] saved []
            (single body.tm.k₀ (body.inputAlphabet.symm bit :: bits))) 1 := by
        apply one
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
          seq h (ih (body.inputAlphabet.symm bit :: bits) (some bit))

private def collect_run (bits : List (body.tm.Γ body.tm.k₁)) (saved : List Wire) (last : Option Wire) :
    Run (cfg (some (.inr .collect)) (body.tm.initialState, false, last) [] saved [] (single body.tm.k₁ bits))
      (cfg (some (.inr .restore)) (body.tm.initialState, false, none) []
        (List.append (α := Wire) (bits.reverse.map body.outputAlphabet) saved) [] empty) (bits.length + 1) := by
  induction bits generalizing saved last with
  | nil =>
      rw [single_nil]
      exact one (by loop_step)
  | cons bit bits ih =>
      have h : Run (cfg (some (.inr .collect)) (body.tm.initialState, false, last) [] saved []
            (single body.tm.k₁ (bit :: bits)))
          (cfg (some (.inr .collect)) (body.tm.initialState, false, some (body.outputAlphabet bit))
            [] (body.outputAlphabet bit :: saved) [] (single body.tm.k₁ bits)) 1 := by
        apply one
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
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (body.outputAlphabet bit :: saved) (some (body.outputAlphabet bit)))

private def restore_run (saved input : List Wire) (last : Option Wire) :
    Run (cfg (some (.inr .restore)) (body.tm.initialState, false, last) input saved [] empty)
      (cfg (some (.inr .scan)) initialState (saved.reverse ++ input) [] [] empty) (saved.length + 1) := by
  induction saved generalizing input last with
  | nil => exact one (by loop_step)
  | cons bit saved ih =>
      have h : Run (cfg (some (.inr .restore)) (body.tm.initialState, false, last) input (bit :: saved) [] empty)
          (cfg (some (.inr .restore)) (body.tm.initialState, false, some bit) (bit :: input) saved [] empty) 1 :=
        one (by loop_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (bit :: input) (some bit))

private def finish_run (saved : List Wire) (output : List Bool) (last : Option Wire) :
    Run (cfg (some (.inr .finish)) (body.tm.initialState, false, last) [] saved output empty)
      (cfg none initialState [] [] ((saved.filterMap Sum.getLeft?).reverse ++ output) empty)
      (saved.length + 1) := by
  induction saved generalizing output last with
  | nil => exact one (by loop_step)
  | cons bit saved ih =>
      cases bit with
      | inl bit =>
          have h : Run (cfg (some (.inr .finish)) (body.tm.initialState, false, last) [] (.inl bit :: saved) output empty)
              (cfg (some (.inr .finish)) (body.tm.initialState, false, some (.inl bit)) [] saved (bit :: output) empty) 1 :=
            one (by loop_step)
          simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using seq h (ih (bit :: output) (some (.inl bit)))
      | inr query =>
          have h : Run (cfg (some (.inr .finish)) (body.tm.initialState, false, last) [] (.inr query :: saved) output empty)
              (cfg (some (.inr .finish)) (body.tm.initialState, false, some (.inr query)) [] saved output empty) 1 :=
            one (by loop_step)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih output (some (.inr query)))

/-- Preserve and load a complete state containing another counted record. -/
def enter_run (input : List Wire) (present : input.any sourceCell = true) :
    Run (ready input)
      (cfg (some (.inl body.tm.main)) initialState [] [] []
        (single body.tm.k₀ (input.map body.inputAlphabet.symm)))
      (2 * input.length + 2) := by
  have hs := scan_run (body := body) input [] false none
  simp only [present, Bool.false_or, ite_true, List.append_nil] at hs
  have hf := fill_run (body := body) input.reverse [] true none
  simp only [single_nil, List.reverse_reverse, List.append_nil, List.length_reverse] at hf
  convert seq hs hf using 1
  omega

/-- Restore the exact output order and clear all component work stacks. -/
def return_run (output : List Wire) :
    Run (cfg (some (.inr .collect)) initialState [] [] []
        (single body.tm.k₁ (output.map body.outputAlphabet.symm)))
      (ready output) (2 * output.length + 2) := by
  have hc := collect_run (output.map body.outputAlphabet.symm) [] none
  simp only [← List.map_reverse, List.map_map, Equiv.apply_symm_apply, Function.comp_def,
    List.map_id_fun', List.append_eq, List.append_nil, List.length_map] at hc
  have hr := restore_run (body := body) output.reverse [] none
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hr
  convert seq hc hr using 1
  omega

/-- Dispatch, checked body execution and return, with every transfer counted. -/
def iteration_cycle (input output : List Wire) (time : ℕ)
    (present : input.any sourceCell = true)
    (run : TM2OutputsInTime body.tm (input.map body.inputAlphabet.symm)
      (some (output.map body.outputAlphabet.symm)) time) :
    Run (body := body) (ready input) (ready output) (time + 2 * input.length + 2 * output.length + 4) := by
  have h := seq (enter_run (body := body) input present) (seq (body_run input output time run) (return_run (body := body) output))
  convert h using 1
  omega

/-- On exhaustion discard the query and return exactly the accumulated bit. -/
def exit_run (input : List Wire) (answer : Bool)
    (absent : input.any sourceCell = false)
    (result : input.filterMap Sum.getLeft? = finEncodingBoolBool.encode answer) :
    Run (body := body) (ready input) (done answer) (2 * input.length + 2) := by
  have hs := scan_run (body := body) input [] false none
  simp only [absent, Bool.false_or, Bool.false_eq_true, ite_false, List.append_nil] at hs
  have hf := finish_run (body := body) input.reverse [] none
  simp only [List.filterMap_reverse, List.reverse_reverse, List.append_nil, List.length_reverse,
    result] at hf
  convert seq hs hf using 1
  omega

theorem ready_eq_initList (input : List Wire) :
    ready input = initList (computer (body := body)) input := by
  simp only [ready, initList, computer, cfg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

theorem done_eq_haltList (answer : Bool) : done answer = haltList (computer (body := body)) (finEncodingBoolBool.encode answer) := by
  simp only [done, haltList, computer, cfg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

#print axioms body_run
#print axioms iteration_cycle
#print axioms exit_run

end PhdThesisLean.AllDifferentCSPMachine.RecordLoopMachine
