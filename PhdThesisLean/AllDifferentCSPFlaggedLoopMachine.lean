import PhdThesisLean.AllDifferentCSPPairGate

/-!
# Shared finite controller for Boolean-tagged loops

The retained encoding and checked body are parameters, shared by both CSP scans.
A tagged, machine-computed active bit selects each complete dispatch. The body
advances one candidate and computes the next active bit. On exhaustion the
controller removes that bit and returns the complete terminal state. All body
calls, ordered transfers, final scans and scratch cleanup are charged.
-/

namespace PhdThesisLean.AllDifferentCSPMachine.FlaggedLoopMachine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

noncomputable section

variable {α : Type} {encoding : FinEncoding α} [Inhabited encoding.Γ]
  {step : Bool × α → Bool × α}
  {body : @TM2ComputableInPolyTime (Bool × α) (Bool × α)
    (PairGateMachine.flagEncoding encoding) (PairGateMachine.flagEncoding encoding) step}

instance : Fintype encoding.Γ := encoding.ΓFin

abbrev Wire (encoding : FinEncoding α) := Sum Bool encoding.Γ

def sourceCell : (Wire encoding) → Bool
  | .inl answer => answer
  | _ => false

/-- Only the computed answer selects another call, regardless of payload bits. -/
theorem source_present (input : (Bool × α)) :
    ((PairGateMachine.flagEncoding encoding).encode input).any sourceCell = input.1 := by
  simp [PairGateMachine.flagEncoding, LeanNPHardness.PairEncoding.finEncoding,
    finEncodingBoolBool, encodeBool, List.any_map, Function.comp_def, sourceCell]

inductive External
  | input | saved | output
  deriving DecidableEq, Fintype

abbrev Stack := body.tm.K ⊕ External
abbrev Alphabet : (Stack (body := body)) → Type
  | .inl k => body.tm.Γ k
  | .inr .input | .inr .saved => (Wire encoding)
  | .inr .output => encoding.Γ

inductive Control
  | scan | fill | collect | restore | finish
  deriving DecidableEq, Fintype

abbrev Label := body.tm.Λ ⊕ Control
abbrev State := body.tm.σ × Bool × Option (Wire encoding)

instance : Fintype body.tm.K := body.tm.kFin
instance : Fintype body.tm.Λ := body.tm.ΛFin
instance : Fintype body.tm.σ := body.tm.σFin

def initialState : (State (body := body)) := (body.tm.initialState, false, none)

private def observe (s : State (body := body)) (symbol : Option (Wire encoding)) :
    State (body := body) := (s.1, s.2.1, symbol)
private def cell (s : (State (body := body))) : (Wire encoding) := s.2.2.getD (.inl false)

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
  | .inl label => (lift (body := body)) (body.tm.m label)
  | .inr .scan => .pop (.inr .input) (observe (body := body)) <|
      .branch (fun s => s.2.2.isSome)
        (.push (.inr .saved) (cell (body := body)) <|
          .load (fun s => (s.1, s.2.1 || sourceCell ((cell (body := body)) s), s.2.2)) <|
          .goto fun _ => .inr .scan)
        (.branch (fun s => s.2.1)
          (.goto fun _ => .inr .fill) (.goto fun _ => .inr .finish))
  | .inr .fill => .pop (.inr .saved) (observe (body := body)) <|
      .branch (fun s => s.2.2.isSome)
        (.push (.inl body.tm.k₀) (fun s => body.inputAlphabet.symm ((cell (body := body)) s)) <|
          .goto fun _ => .inr .fill)
        (.load (fun _ => (initialState (body := body))) <| .goto fun _ => .inl body.tm.main)
  | .inr .collect => .pop (.inl body.tm.k₁)
      (fun s bit => (observe (body := body)) s (bit.map body.outputAlphabet)) <|
      .branch (fun s => s.2.2.isSome)
        (.push (.inr .saved) (cell (body := body)) <| .goto fun _ => .inr .collect)
        (.goto fun _ => .inr .restore)
  | .inr .restore => .pop (.inr .saved) (observe (body := body)) <|
      .branch (fun s => s.2.2.isSome)
        (.push (.inr .input) (cell (body := body)) <| .goto fun _ => .inr .restore)
        (.load (fun _ => (initialState (body := body))) <| .goto fun _ => .inr .scan)
  | .inr .finish => .pop (.inr .saved) (observe (body := body)) <|
      .branch (fun s => s.2.2.isSome)
        (.branch (fun s => ((cell (body := body)) s).getRight?.isSome)
          (.push (.inr .output) (fun s => ((cell (body := body)) s).getRight?.getD default) <|
            .goto fun _ => .inr .finish)
          (.goto fun _ => .inr .finish))
        (.load (fun _ => (initialState (body := body))) .halt)

def computer : FinTM2 where
  K := (Stack (body := body))
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := (Alphabet (body := body))
  Λ := (Label (body := body))
  main := .inr .scan
  σ := (State (body := body))
  initialState := (initialState (body := body))
  Γk₀Fin := inferInstance
  m := (program (body := body))

def stackContents (input saved : List (Wire encoding)) (output : List encoding.Γ)
    (contents : (k : body.tm.K) → List (body.tm.Γ k)) : (k : (Stack (body := body))) → List ((Alphabet (body := body)) k)
  | .inl k => contents k
  | .inr .input => input
  | .inr .saved => saved
  | .inr .output => output

def cfg (label : Option (Label (body := body))) (state : (State (body := body))) (input saved : List (Wire encoding))
    (output : List encoding.Γ) (contents : (k : body.tm.K) → List (body.tm.Γ k)) : (computer (body := body)).Cfg :=
  ⟨label, state, (stackContents (body := body)) input saved output contents⟩

def empty : (k : body.tm.K) → List (body.tm.Γ k) := fun _ => []

def single (k : body.tm.K) (bits : List (body.tm.Γ k)) := Function.update (empty (body := body)) k bits

def ready (input : (Bool × α)) : (computer (body := body)).Cfg :=
  (cfg (body := body)) (some (.inr .scan)) (initialState (body := body)) ((PairGateMachine.flagEncoding encoding).encode input) [] [] (empty (body := body))

def done (state : α) : (computer (body := body)).Cfg :=
  (cfg (body := body)) none (initialState (body := body)) [] [] (encoding.encode state) (empty (body := body))

abbrev Run (a b : (computer (body := body)).Cfg) (time : ℕ) := EvalsToInTime (computer (body := body)).step a (some b) time

private def one {a b : (computer (body := body)).Cfg} (h : (computer (body := body)).step a = some b) : (Run (body := body)) a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using! h, steps_le_m := le_rfl }

def seq {a b c : (computer (body := body)).Cfg} {m n : ℕ}
    (h : (Run (body := body)) a b m) (h' : (Run (body := body)) b c n) : (Run (body := body)) a c (m + n) := by
  simpa [Nat.add_comm] using! EvalsToInTime.trans (computer (body := body)).step m n a b (some c) h h'

private def embed (config : body.tm.Cfg) : (computer (body := body)).Cfg :=
  (cfg (body := body)) (some (config.l.elim (.inr .collect) Sum.inl)) (config.var, false, none) [] [] [] config.stk

omit [Inhabited encoding.Γ] in
private theorem stackContents_update (input saved : List (Wire encoding)) (output : List encoding.Γ)
    (contents : (k : body.tm.K) → List (body.tm.Γ k)) (k : body.tm.K) (value : List (body.tm.Γ k)) :
    (stackContents (body := body)) input saved output (Function.update contents k value) =
      Function.update ((stackContents (body := body)) input saved output contents) (.inl k) value := by
  funext index
  cases index with
  | inr index => cases index <;> simp [stackContents]
  | inl index =>
      by_cases h : index = k
      · subst index; simp [stackContents]
      · simp [stackContents, Function.update, h]

private theorem lift_stepAux (stmt : TM2.Stmt body.tm.Γ body.tm.Λ body.tm.σ)
    (state : body.tm.σ) (contents : (k : body.tm.K) → List (body.tm.Γ k)) :
    TM2.stepAux ((lift (body := body)) stmt) (state, false, none) ((stackContents (body := body)) [] [] [] contents) =
      (embed (body := body)) (TM2.stepAux stmt state contents) := by
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
      cases h : test state <;> simp only [lift, TM2.stepAux, h, Bool.cond_false, Bool.cond_true]
      · exact ino _ _
      · exact iy _ _
  | goto next => rfl
  | halt => rfl

private theorem body_step (config : body.tm.Cfg) (h : config.l ≠ none) :
    (computer (body := body)).step ((embed (body := body)) config) = (body.tm.step config).map (embed (body := body)) := by
  rcases config with ⟨label, state, contents⟩
  cases label with
  | none => simp at h
  | some label =>
      simp only [computer, FinTM2.step, embed, cfg, program, Option.elim_some,
        TM2.step, Option.map_some]
      congr 1
      exact (lift_stepAux (body := body)) (body.tm.m label) state contents

private theorem body_iterate (n : ℕ) (start finish : body.tm.Cfg)
    (h : (fun c => c.bind body.tm.step)^[n] (some start) = some finish) :
    (fun c => c.bind (computer (body := body)).step)^[n] (some ((embed (body := body)) start)) = some ((embed (body := body)) finish) := by
  induction n generalizing start with
  | zero => simpa using congrArg (Option.map (embed (body := body))) h
  | succ n ih =>
      have hn : (fun c => c.bind body.tm.step)^[n] none = none :=
        Function.iterate_fixed (by rfl) n
      rw [Function.iterate_succ_apply] at h ⊢
      change (fun c => c.bind body.tm.step)^[n] (body.tm.step start) = some finish at h
      change (fun c => c.bind (computer (body := body)).step)^[n] ((computer (body := body)).step ((embed (body := body)) start)) = _
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

omit [Inhabited encoding.Γ] in
private theorem single_eq (k : body.tm.K) (bits : List (body.tm.Γ k)) :
    (single (body := body)) k bits = fun j => if h : j = k then (by rw [h]; exact bits) else [] := by
  funext j
  by_cases h : j = k
  · subst j; simp [single]
  · simp [single, empty, Function.update, h]

/-- The already checked complete iteration runs inside the loop unchanged,
then returns with every body work stack empty. -/
def body_run (input : (Bool × α)) :
    (Run (body := body)) ((cfg (body := body)) (some (.inl body.tm.main)) (initialState (body := body)) [] [] []
        ((single (body := body)) body.tm.k₀ (((PairGateMachine.flagEncoding encoding).encode input).map body.inputAlphabet.symm)))
      ((cfg (body := body)) (some (.inr .collect)) (initialState (body := body)) [] [] []
        ((single (body := body)) body.tm.k₁ (((PairGateMachine.flagEncoding encoding).encode (step input)).map body.outputAlphabet.symm)))
      (body.time.eval ((PairGateMachine.flagEncoding encoding).encode input).length) where
  steps := (body.outputsFun input).steps
  evals_in_steps := by
    have h := (body_iterate (body := body)) _ _ _ (body.outputsFun input).evals_in_steps
    simpa only [embed, initList, haltList, single_eq, initialState,
      Option.elim_some, Option.elim_none] using! h
  steps_le_m := (body.outputsFun input).steps_le_m

local macro "loop_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, initialState,
    observe, cell, empty, Function.update]
   <;> first | rfl | (funext k; cases k with
     | inl k => rfl
     | inr k => cases k <;> rfl)))

private def scan_run (input saved : List (Wire encoding)) (seen : Bool) (last : Option (Wire encoding)) :
    (Run (body := body)) ((cfg (body := body)) (some (.inr .scan)) (body.tm.initialState, seen, last) input saved [] (empty (body := body)))
      ((cfg (body := body)) (some (.inr (if seen || input.any sourceCell then .fill else .finish)))
        (body.tm.initialState, seen || input.any sourceCell, none)
        [] (input.reverse ++ saved) [] (empty (body := body))) (input.length + 1) := by
  induction input generalizing saved seen last with
  | nil => cases seen <;> exact (one (body := body)) (by loop_step)
  | cons bit input ih =>
      have h : (Run (body := body)) ((cfg (body := body)) (some (.inr .scan)) (body.tm.initialState, seen, last) (bit :: input) saved [] (empty (body := body)))
          ((cfg (body := body)) (some (.inr .scan)) (body.tm.initialState, seen || sourceCell bit, some bit)
            input (bit :: saved) [] (empty (body := body))) 1 := (one (body := body)) (by loop_step)
      simpa only [List.any_cons, List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append, Bool.or_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (seq (body := body)) h (ih (bit :: saved) (seen || sourceCell bit) (some bit))

omit [Inhabited encoding.Γ] in
private theorem single_nil (k : body.tm.K) : (single (body := body)) k [] = (empty (body := body)) := by
  exact Function.update_eq_self k (empty (body := body))

private def fill_run (saved : List (Wire encoding)) (bits : List (body.tm.Γ body.tm.k₀))
    (seen : Bool) (last : Option (Wire encoding)) :
    (Run (body := body)) ((cfg (body := body)) (some (.inr .fill)) (body.tm.initialState, seen, last) [] saved [] ((single (body := body)) body.tm.k₀ bits))
      ((cfg (body := body)) (some (.inl body.tm.main)) (initialState (body := body)) [] [] []
        ((single (body := body)) body.tm.k₀ (saved.reverse.map body.inputAlphabet.symm ++ bits)))
      (saved.length + 1) := by
  induction saved generalizing bits last with
  | nil => exact (one (body := body)) (by loop_step)
  | cons bit saved ih =>
      have h : (Run (body := body)) ((cfg (body := body)) (some (.inr .fill)) (body.tm.initialState, seen, last) [] (bit :: saved) []
            ((single (body := body)) body.tm.k₀ bits))
          ((cfg (body := body)) (some (.inr .fill)) (body.tm.initialState, seen, some bit) [] saved []
            ((single (body := body)) body.tm.k₀ (body.inputAlphabet.symm bit :: bits))) 1 := by
        apply (one (body := body))
        simp only [computer, FinTM2.step, TM2.step, cfg, program, TM2.stepAux, stackContents,
          observe, cell, List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
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
          (seq (body := body)) h (ih (body.inputAlphabet.symm bit :: bits) (some bit))

private def collect_run (bits : List (body.tm.Γ body.tm.k₁)) (saved : List (Wire encoding)) (last : Option (Wire encoding)) :
    (Run (body := body)) ((cfg (body := body)) (some (.inr .collect)) (body.tm.initialState, false, last) [] saved [] ((single (body := body)) body.tm.k₁ bits))
      ((cfg (body := body)) (some (.inr .restore)) (body.tm.initialState, false, none) []
        (List.append (α := (Wire encoding)) (bits.reverse.map body.outputAlphabet) saved) [] (empty (body := body))) (bits.length + 1) := by
  induction bits generalizing saved last with
  | nil =>
      rw [single_nil]
      exact (one (body := body)) (by loop_step)
  | cons bit bits ih =>
      have h : (Run (body := body)) ((cfg (body := body)) (some (.inr .collect)) (body.tm.initialState, false, last) [] saved []
            ((single (body := body)) body.tm.k₁ (bit :: bits)))
          ((cfg (body := body)) (some (.inr .collect)) (body.tm.initialState, false, some (body.outputAlphabet bit))
            [] (body.outputAlphabet bit :: saved) [] ((single (body := body)) body.tm.k₁ bits)) 1 := by
        apply (one (body := body))
        simp only [computer, FinTM2.step, TM2.step, cfg, program, TM2.stepAux, stackContents,
          single, Function.update_self, List.head?_cons, List.tail_cons, Option.map_some,
          observe, cell, List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
        congr 2
        funext k
        cases k with
        | inl k =>
            by_cases hk : k = body.tm.k₁
            · subst k; simp [stackContents]
            · simp [stackContents, Function.update, hk]
        | inr k => cases k <;> simp [stackContents]
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using (seq (body := body)) h (ih (body.outputAlphabet bit :: saved) (some (body.outputAlphabet bit)))

private def restore_run (saved input : List (Wire encoding)) (last : Option (Wire encoding)) :
    (Run (body := body)) ((cfg (body := body)) (some (.inr .restore)) (body.tm.initialState, false, last) input saved [] (empty (body := body)))
      ((cfg (body := body)) (some (.inr .scan)) (initialState (body := body)) (saved.reverse ++ input) [] [] (empty (body := body))) (saved.length + 1) := by
  induction saved generalizing input last with
  | nil => exact (one (body := body)) (by loop_step)
  | cons bit saved ih =>
      have h : (Run (body := body)) ((cfg (body := body)) (some (.inr .restore)) (body.tm.initialState, false, last) input (bit :: saved) [] (empty (body := body)))
          ((cfg (body := body)) (some (.inr .restore)) (body.tm.initialState, false, some bit) (bit :: input) saved [] (empty (body := body))) 1 :=
        (one (body := body)) (by loop_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using (seq (body := body)) h (ih (bit :: input) (some bit))

private def finish_run (saved : List (Wire encoding)) (output : List encoding.Γ) (last : Option (Wire encoding)) :
    (Run (body := body)) ((cfg (body := body)) (some (.inr .finish)) (body.tm.initialState, false, last) [] saved output (empty (body := body)))
      ((cfg (body := body)) none (initialState (body := body)) [] [] ((saved.filterMap Sum.getRight?).reverse ++ output) (empty (body := body)))
      (saved.length + 1) := by
  induction saved generalizing output last with
  | nil => exact (one (body := body)) (by loop_step)
  | cons bit saved ih =>
      cases bit with
      | inr bit =>
          have h : (Run (body := body)) ((cfg (body := body)) (some (.inr .finish)) (body.tm.initialState, false, last) [] (.inr bit :: saved) output (empty (body := body)))
              ((cfg (body := body)) (some (.inr .finish)) (body.tm.initialState, false, some (.inr bit)) [] saved (bit :: output) (empty (body := body))) 1 :=
            (one (body := body)) (by loop_step)
          simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using (seq (body := body)) h (ih (bit :: output) (some (.inr bit)))
      | inl query =>
          have h : (Run (body := body)) ((cfg (body := body)) (some (.inr .finish)) (body.tm.initialState, false, last) [] (.inl query :: saved) output (empty (body := body)))
              ((cfg (body := body)) (some (.inr .finish)) (body.tm.initialState, false, some (.inl query)) [] saved output (empty (body := body))) 1 :=
            (one (body := body)) (by loop_step)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (seq (body := body)) h (ih output (some (.inl query)))

/-- Inspect the active answer and load the complete body input in order. -/
def enter_run (state : α) :
    (Run (body := body)) ((ready (body := body)) (true, state))
      ((cfg (body := body)) (some (.inl body.tm.main)) (initialState (body := body)) [] [] []
        ((single (body := body)) body.tm.k₀ (((PairGateMachine.flagEncoding encoding).encode (true, state)).map body.inputAlphabet.symm)))
      (2 * ((PairGateMachine.flagEncoding encoding).encode (true, state)).length + 2) := by
  have hs := (scan_run (body := body)) ((PairGateMachine.flagEncoding encoding).encode (true, state)) [] false none
  rw [source_present] at hs
  simp only [Bool.false_or, ite_true, List.append_nil] at hs
  have hf := (fill_run (body := body)) ((PairGateMachine.flagEncoding encoding).encode (true, state)).reverse [] true none
  simp only [single_nil, List.reverse_reverse, List.append_nil, List.length_reverse] at hf
  convert (seq (body := body)) hs hf using 1
  all_goals first | omega | rfl

/-- Return the body's complete output to the next scan, preserving order and
clearing the body output and scratch stacks. -/
def return_run (output : (Bool × α)) :
    (Run (body := body)) ((cfg (body := body)) (some (.inr .collect)) (initialState (body := body)) [] [] []
        ((single (body := body)) body.tm.k₁ (((PairGateMachine.flagEncoding encoding).encode output).map body.outputAlphabet.symm)))
      ((ready (body := body)) output) (2 * ((PairGateMachine.flagEncoding encoding).encode output).length + 2) := by
  have hc := (collect_run (body := body)) (((PairGateMachine.flagEncoding encoding).encode output).map body.outputAlphabet.symm) [] none
  simp only [← List.map_reverse, List.map_map, Equiv.apply_symm_apply, Function.comp_def,
    List.map_id_fun', List.append_eq, List.append_nil, List.length_map] at hc
  have hr := (restore_run (body := body)) ((PairGateMachine.flagEncoding encoding).encode output).reverse [] none
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hr
  convert (seq (body := body)) hc hr using 1
  all_goals first | omega | rfl

/-- One cycle includes the full dispatch and recomputation of active control. -/
def iteration_cycle (state : α) :
    (Run (body := body)) ((ready (body := body)) (true, state)) ((ready (body := body)) (step (true, state)))
      (body.time.eval ((PairGateMachine.flagEncoding encoding).encode (true, state)).length +
        2 * ((PairGateMachine.flagEncoding encoding).encode (true, state)).length +
        2 * ((PairGateMachine.flagEncoding encoding).encode (step (true, state))).length + 4) := by
  have h := (seq (body := body)) ((enter_run (body := body)) state)
    ((seq (body := body)) ((body_run (body := body)) (true, state)) ((return_run (body := body)) (step (true, state))))
  convert h using 1
  omega

/-- Exhaustion removes the answer and preserves every terminal state cell. -/
def exit_run (state : α) :
    (Run (body := body)) ((ready (body := body)) (false, state)) ((done (body := body)) state)
      (2 * ((PairGateMachine.flagEncoding encoding).encode (false, state)).length + 2) := by
  have hs := (scan_run (body := body)) ((PairGateMachine.flagEncoding encoding).encode (false, state)) [] false none
  rw [source_present] at hs
  simp only [Bool.false_or, Bool.false_eq_true, ite_false, List.append_nil] at hs
  have hf := (finish_run (body := body)) ((PairGateMachine.flagEncoding encoding).encode (false, state)).reverse [] none
  simp only [List.filterMap_reverse, List.reverse_reverse, List.append_nil, List.length_reverse] at hf
  have wire : ((PairGateMachine.flagEncoding encoding).encode (false, state)).filterMap Sum.getRight? =
      encoding.encode state := by
    simp [PairGateMachine.flagEncoding, LeanNPHardness.PairEncoding.finEncoding,
      finEncodingBoolBool, encodeBool, List.filterMap_map]
  rw [wire] at hf
  convert (seq (body := body)) hs hf using 1
  all_goals first | omega | rfl

theorem ready_eq_initList (input : (Bool × α)) :
    (ready (body := body)) input = initList (computer (body := body)) ((PairGateMachine.flagEncoding encoding).encode input) := by
  simp only [ready, initList, computer, cfg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

theorem done_eq_haltList (state : α) : (done (body := body)) state = haltList (computer (body := body)) (encoding.encode state) := by
  simp only [done, haltList, computer, cfg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

#print axioms source_present
#print axioms iteration_cycle
#print axioms exit_run

end

end PhdThesisLean.AllDifferentCSPMachine.FlaggedLoopMachine
