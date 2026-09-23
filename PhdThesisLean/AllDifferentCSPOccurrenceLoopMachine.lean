import PhdThesisLean.AllDifferentCSPOccurrenceIteration

/-!
# Finite control for complete occurrence relabelling

The dispatcher scans for remaining occurrence cells, loads the checked rank,
binary-emission and accumulation body, and returns its complete output to the
next scan. On exhaustion it discards the retained symbol list and returns all
accumulated binary records in order. Zero-valued fields have delimiters, so
empty input is distinguished from an occurrence with two zero fields.
-/

namespace PhdThesisLean.AllDifferentCSPMachine.OccurrenceLoopMachine

open Computability Turing
open LeanNPHardness.MachineComposition

noncomputable section

def body := occurrenceIterationComputableInPolyTime
abbrev Wire := Sum (Sum (Option Bool) (Option Bool)) (Option Bool)

def sourceCell : Wire → Bool
  | .inl (.inl _) => true
  | _ => false

theorem source_present (input : OccurrenceIteration.State) :
    (OccurrenceIteration.stateFinEncoding.encode input).any sourceCell = !input.1.1.isEmpty := by
  rcases input with ⟨⟨occurrences, symbols⟩, accum⟩
  cases occurrences <;>
    simp [OccurrenceAccumulator.outputFinEncoding, DomainSymbolExtraction.finEncoding,
      DomainFieldRow.outputFinEncoding, DomainFieldRow.outputEncode,
      DomainOccurrenceFieldBlock.outputEncode_eq_prefix, DomainOccurrenceFieldBlock.headerPrefix,
      SourceOrderRawFields.finEncoding, List.any_map, List.map_map, Function.comp_def, sourceCell]

inductive External
  | input | saved | output
  deriving DecidableEq, Fintype

abbrev Stack := body.tm.K ⊕ External
abbrev Alphabet : Stack → Type
  | .inl k => body.tm.Γ k
  | .inr .input | .inr .saved => Wire
  | .inr .output => Option Bool

inductive Control
  | scan | fill | collect | restore | finish
  deriving DecidableEq, Fintype

abbrev Label := body.tm.Λ ⊕ Control
abbrev State := body.tm.σ × Bool × Option Wire

instance : Fintype body.tm.K := body.tm.kFin
instance : Fintype body.tm.Λ := body.tm.ΛFin
instance : Fintype body.tm.σ := body.tm.σFin

def initialState : State := (body.tm.initialState, false, none)

private def observe (s : State) (cell : Option Wire) : State := (s.1, s.2.1, cell)
private def cell (s : State) : Wire := s.2.2.getD (.inr none)

/-- The local call embedding changes only stack addresses and control. A body
halt returns to collection without executing a further body step. -/
def lift : TM2.Stmt body.tm.Γ body.tm.Λ body.tm.σ → TM2.Stmt Alphabet Label State
  | .push k write next => .push (.inl k) (fun s => write s.1) (lift next)
  | .peek k read next => .peek (.inl k) (fun s bit => (read s.1 bit, s.2)) (lift next)
  | .pop k read next => .pop (.inl k) (fun s bit => (read s.1 bit, s.2)) (lift next)
  | .load update next => .load (fun s => (update s.1, s.2)) (lift next)
  | .branch test yes no => .branch (fun s => test s.1) (lift yes) (lift no)
  | .goto next => .goto (fun s => .inl (next s.1))
  | .halt => .goto (fun _ => .inr .collect)

def program : Label → TM2.Stmt Alphabet Label State
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
        (.branch (fun s => (cell s).getRight?.isSome)
          (.push (.inr .output) (fun s => (cell s).getRight?.getD none) <|
            .goto fun _ => .inr .finish)
          (.goto fun _ => .inr .finish))
        (.load (fun _ => initialState) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := Alphabet
  Λ := Label
  main := .inr .scan
  σ := State
  initialState := initialState
  Γk₀Fin := inferInstance
  m := program

def stackContents (input saved : List Wire) (output : List (Option Bool))
    (contents : (k : body.tm.K) → List (body.tm.Γ k)) : (k : Stack) → List (Alphabet k)
  | .inl k => contents k
  | .inr .input => input
  | .inr .saved => saved
  | .inr .output => output

def cfg (label : Option Label) (state : State) (input saved : List Wire)
    (output : List (Option Bool)) (contents : (k : body.tm.K) → List (body.tm.Γ k)) : computer.Cfg :=
  ⟨label, state, stackContents input saved output contents⟩

def empty : (k : body.tm.K) → List (body.tm.Γ k) := fun _ => []

def single (k : body.tm.K) (bits : List (body.tm.Γ k)) := Function.update empty k bits

def ready (input : OccurrenceIteration.State) : computer.Cfg :=
  cfg (some (.inr .scan)) initialState (OccurrenceIteration.stateFinEncoding.encode input) [] [] empty

def done (records : List (ℕ × ℕ)) : computer.Cfg :=
  cfg none initialState [] [] (DomainFieldRow.outputEncode records) empty

abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time

private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }

def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

private def embed (config : body.tm.Cfg) : computer.Cfg :=
  cfg (some (config.l.elim (.inr .collect) Sum.inl)) (config.var, false, none) [] [] [] config.stk

private theorem stackContents_update (input saved : List Wire) (output : List (Option Bool))
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
    computer.step (embed config) = (body.tm.step config).map embed := by
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
    (fun c => c.bind computer.step)^[n] (some (embed start)) = some (embed finish) := by
  induction n generalizing start with
  | zero => simpa using congrArg (Option.map embed) h
  | succ n ih =>
      have hn : (fun c => c.bind body.tm.step)^[n] none = none :=
        Function.iterate_fixed (by rfl) n
      rw [Function.iterate_succ_apply] at h ⊢
      change (fun c => c.bind body.tm.step)^[n] (body.tm.step start) = some finish at h
      change (fun c => c.bind computer.step)^[n] (computer.step (embed start)) = _
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

/-- The already checked complete iteration runs inside the loop unchanged,
then returns with every body work stack empty. -/
def body_run (input : OccurrenceIteration.Input) :
    Run (cfg (some (.inl body.tm.main)) initialState [] [] []
        (single body.tm.k₀ ((OccurrenceIteration.inputFinEncoding.encode input).map body.inputAlphabet.symm)))
      (cfg (some (.inr .collect)) initialState [] [] []
        (single body.tm.k₁ ((OccurrenceIteration.stateFinEncoding.encode (OccurrenceIteration.step input)).map body.outputAlphabet.symm)))
      (body.time.eval (OccurrenceIteration.inputFinEncoding.encode input).length) where
  steps := (body.outputsFun input).steps
  evals_in_steps := by
    have h := body_iterate _ _ _ (body.outputsFun input).evals_in_steps
    simpa only [embed, initList, haltList, single_eq, initialState,
      Option.elim_some, Option.elim_none] using h
  steps_le_m := (body.outputsFun input).steps_le_m

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

private def finish_run (saved : List Wire) (output : List (Option Bool)) (last : Option Wire) :
    Run (cfg (some (.inr .finish)) (body.tm.initialState, false, last) [] saved output empty)
      (cfg none initialState [] [] ((saved.filterMap Sum.getRight?).reverse ++ output) empty)
      (saved.length + 1) := by
  induction saved generalizing output last with
  | nil => exact one (by loop_step)
  | cons bit saved ih =>
      cases bit with
      | inl query =>
          have h : Run (cfg (some (.inr .finish)) (body.tm.initialState, false, last) [] (.inl query :: saved) output empty)
              (cfg (some (.inr .finish)) (body.tm.initialState, false, some (.inl query)) [] saved output empty) 1 :=
            one (by loop_step)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih output (some (.inl query)))
      | inr bit =>
          have h : Run (cfg (some (.inr .finish)) (body.tm.initialState, false, last) [] (.inr bit :: saved) output empty)
              (cfg (some (.inr .finish)) (body.tm.initialState, false, some (.inr bit)) [] saved (bit :: output) empty) 1 :=
            one (by loop_step)
          simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using seq h (ih (bit :: output) (some (.inr bit)))

/-- Scan a nonempty serialized state and load the complete body input in order.
The source-field test is the checked test from `source_present`. -/
def enter_run (occurrence : ℕ × ℕ) (occurrences : List (ℕ × ℕ))
    (symbols : List ℕ) (accum : List (ℕ × ℕ)) :
    Run (ready ((occurrence :: occurrences, symbols), accum))
      (cfg (some (.inl body.tm.main)) initialState [] [] []
        (single body.tm.k₀ ((OccurrenceIteration.inputFinEncoding.encode
          ((occurrence, occurrences, symbols), accum)).map body.inputAlphabet.symm)))
      (2 * (OccurrenceIteration.stateFinEncoding.encode
        ((occurrence :: occurrences, symbols), accum)).length + 2) := by
  have hs := scan_run (OccurrenceIteration.stateFinEncoding.encode
    ((occurrence :: occurrences, symbols), accum)) [] false none
  rw [source_present] at hs
  simp only [List.isEmpty_cons, Bool.not_false, Bool.false_or,
    ite_true, List.append_nil] at hs
  have hf := fill_run (OccurrenceIteration.stateFinEncoding.encode
    ((occurrence :: occurrences, symbols), accum)).reverse [] true none
  simp only [single_nil, List.reverse_reverse, List.append_nil, List.length_reverse] at hf
  convert seq hs hf using 1
  omega

/-- Return the body's complete output to the next scan, preserving order and
clearing the body output and scratch stacks. -/
def return_run (output : OccurrenceIteration.State) :
    Run (cfg (some (.inr .collect)) initialState [] [] []
        (single body.tm.k₁ ((OccurrenceIteration.stateFinEncoding.encode output).map body.outputAlphabet.symm)))
      (ready output) (2 * (OccurrenceIteration.stateFinEncoding.encode output).length + 2) := by
  have hc := collect_run ((OccurrenceIteration.stateFinEncoding.encode output).map body.outputAlphabet.symm) [] none
  simp only [← List.map_reverse, List.map_map, Equiv.apply_symm_apply, Function.comp_def,
    List.map_id_fun', List.append_eq, List.append_nil, List.length_map] at hc
  have hr := restore_run (OccurrenceIteration.stateFinEncoding.encode output).reverse [] none
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hr
  convert seq hc hr using 1
  omega

/-- One actual loop cycle includes scan, loading, the entire checked iteration,
and both return transfers. The next state is ready for another finite scan. -/
def iteration_cycle (occurrence : ℕ × ℕ) (occurrences : List (ℕ × ℕ))
    (symbols : List ℕ) (accum : List (ℕ × ℕ)) :
    let input : OccurrenceIteration.Input := ((occurrence, occurrences, symbols), accum)
    Run (ready (OccurrenceIteration.source input)) (ready (OccurrenceIteration.step input))
      (body.time.eval (OccurrenceIteration.inputFinEncoding.encode input).length +
        2 * (OccurrenceIteration.inputFinEncoding.encode input).length +
        2 * (OccurrenceIteration.stateFinEncoding.encode (OccurrenceIteration.step input)).length + 4) := by
  dsimp only
  have h := seq (enter_run occurrence occurrences symbols accum)
    (seq (body_run ((occurrence, occurrences, symbols), accum))
      (return_run (OccurrenceIteration.step ((occurrence, occurrences, symbols), accum))))
  convert h using 1
  have wire : (OccurrenceIteration.stateFinEncoding.encode
      ((occurrence :: occurrences, symbols), accum)).length =
    (OccurrenceIteration.inputFinEncoding.encode ((occurrence, occurrences, symbols), accum)).length := rfl
  omega

/-- The exhausted branch returns exactly the accumulated records, including
empty output, and clears the retained symbols and every work stack. -/
def exit_run (symbols : List ℕ) (accum : List (ℕ × ℕ)) :
    Run (ready (([], symbols), accum)) (done accum)
      (2 * (OccurrenceIteration.stateFinEncoding.encode (([], symbols), accum)).length + 2) := by
  have hs := scan_run (OccurrenceIteration.stateFinEncoding.encode (([], symbols), accum)) [] false none
  rw [source_present] at hs
  simp only [List.isEmpty_nil, Bool.not_true, Bool.false_or, Bool.false_eq_true,
    ite_false, List.append_nil] at hs
  have hf := finish_run (OccurrenceIteration.stateFinEncoding.encode (([], symbols), accum)).reverse [] none
  simp only [List.filterMap_reverse, List.reverse_reverse, List.append_nil, List.length_reverse] at hf
  have discard : (DomainSymbolExtraction.finEncoding.encode ([], symbols)).filterMap
      (fun _ => (none : Option (Option Bool))) = [] := by simp
  have wire : (OccurrenceIteration.stateFinEncoding.encode (([], symbols), accum)).filterMap Sum.getRight? =
      DomainFieldRow.outputEncode accum := by
    simp [OccurrenceAccumulator.outputFinEncoding, DomainFieldRow.outputFinEncoding,
      List.filterMap_map, Function.comp_def, discard]
  rw [wire] at hf
  convert seq hs hf using 1
  omega

theorem ready_eq_initList (input : OccurrenceIteration.State) :
    ready input = initList computer (OccurrenceIteration.stateFinEncoding.encode input) := by
  simp only [ready, initList, computer, cfg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

theorem done_eq_haltList (records : List (ℕ × ℕ)) : done records = haltList computer (DomainFieldRow.outputEncode records) := by
  simp only [done, haltList, computer, cfg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

#print axioms source_present
#print axioms body_run
#print axioms iteration_cycle
#print axioms exit_run

end

end PhdThesisLean.AllDifferentCSPMachine.OccurrenceLoopMachine
