import PhdThesisLean.RationalSumEncoding

/-!
# A finite machine for repeated binary fraction addition

One delimited fraction is consumed per cycle. The remaining list is retained
on an external stack while the checked addition machine runs. The controller
charges loading, return transfers, delimiters, exhaustion and final output.
-/
namespace PhdThesisLean.RationalSum.Machine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open StateTransition
open RationalVerifierBounds
open LeanNPHardness.MachineComposition

set_option backward.isDefEq.respectTransparency false
noncomputable section

def body := RationalAddition.additionComputableInPolyTime
abbrev Wire := Option Bool
inductive External | input | saved | output deriving DecidableEq, Fintype
abbrev Stack := body.tm.K ⊕ External
abbrev Alphabet : Stack → Type
  | .inl k => body.tm.Γ k
  | .inr .input => Wire
  | .inr .saved | .inr .output => Bool
inductive Control | scan (first : Bool) | next | fill | collect | restore | finish
  deriving DecidableEq, Fintype
abbrev Label := body.tm.Λ ⊕ Control
abbrev State := body.tm.σ × Option Wire
instance : Fintype body.tm.K := body.tm.kFin
instance : Fintype body.tm.Λ := body.tm.ΛFin
instance : Fintype body.tm.σ := body.tm.σFin
def initialState : State := (body.tm.initialState, none)
private def observe (s : State) (cell : Option Wire) : State := (s.1, cell)
private def bit (s : State) : Bool := (s.2.getD none).getD false
private def reset : TM2.Stmt Alphabet Label State → TM2.Stmt Alphabet Label State :=
  .load (fun _ => initialState)

def lift : TM2.Stmt body.tm.Γ body.tm.Λ body.tm.σ → TM2.Stmt Alphabet Label State
  | .push k write next => .push (.inl k) (fun s => write s.1) (lift next)
  | .peek k read next => .peek (.inl k) (fun s b => (read s.1 b, s.2)) (lift next)
  | .pop k read next => .pop (.inl k) (fun s b => (read s.1 b, s.2)) (lift next)
  | .load update next => .load (fun s => (update s.1, s.2)) (lift next)
  | .branch test yes no => .branch (fun s => test s.1) (lift yes) (lift no)
  | .goto next => .goto (fun s => .inl (next s.1))
  | .halt => .goto (fun _ => .inr .collect)

def program : Label → TM2.Stmt Alphabet Label State
  | .inl label => lift (body.tm.m label)
  | .inr (.scan first) => .pop (.inr .input) observe <|
      .branch (fun s => (s.2.getD none).isSome)
        (.push (.inr .saved) bit <| reset <| .goto fun _ => .inr (.scan first))
        (reset <| .goto fun _ => .inr (if first then .next else .fill))
  | .inr .next => .peek (.inr .input) observe <|
      .branch (fun s => s.2.isSome)
        (reset <| .goto fun _ => .inr (.scan false))
        (reset <| .goto fun _ => .inr .finish)
  | .inr .fill => .pop (.inr .saved) (fun s b => observe s (b.map some)) <|
      .branch (fun s => s.2.isSome)
        (.push (.inl body.tm.k₀) (fun s => body.inputAlphabet.symm (bit s)) <|
          reset <| .goto fun _ => .inr .fill)
        (reset <| .goto fun _ => .inl body.tm.main)
  | .inr .collect => .pop (.inl body.tm.k₁)
      (fun s b => observe s (b.map (fun b => some (body.outputAlphabet b)))) <|
      .branch (fun s => s.2.isSome)
        (.push (.inr .saved) bit <| reset <| .goto fun _ => .inr .collect)
        (.push (.inr .input) (fun _ => none) <| reset <| .goto fun _ => .inr .restore)
  | .inr .restore => .pop (.inr .saved) (fun s b => observe s (b.map some)) <|
      .branch (fun s => s.2.isSome)
        (.push (.inr .input) (fun s => some (bit s)) <| reset <| .goto fun _ => .inr .restore)
        (reset <| .goto fun _ => .inr (.scan true))
  | .inr .finish => .pop (.inr .saved) (fun s b => observe s (b.map some)) <|
      .branch (fun s => s.2.isSome)
        (.push (.inr .output) bit <| reset <| .goto fun _ => .inr .finish)
        (reset .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := Alphabet
  Λ := Label
  main := .inr (.scan true)
  σ := State
  initialState := initialState
  Γk₀Fin := inferInstance
  m := program

def stackContents (input : List Wire) (saved output : List Bool)
    (contents : (k : body.tm.K) → List (body.tm.Γ k)) : (k : Stack) → List (Alphabet k)
  | .inl k => contents k
  | .inr .input => input
  | .inr .saved => saved
  | .inr .output => output
def cfg (label : Option Label) (state : State) (input : List Wire) (saved output : List Bool)
    (contents : (k : body.tm.K) → List (body.tm.Γ k)) : computer.Cfg :=
  ⟨label, state, stackContents input saved output contents⟩
def empty : (k : body.tm.K) → List (body.tm.Γ k) := fun _ => []
def single (k : body.tm.K) (bits : List (body.tm.Γ k)) := Function.update empty k bits
def ready (z : Fraction) (xs : List Fraction) : computer.Cfg :=
  cfg (some (.inr (.scan true))) initialState (encode (z, xs)) [] [] empty
def done (z : Fraction) : computer.Cfg := cfg none initialState [] [] z.encode empty
abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using! h, steps_le_m := le_rfl }
def seq {a b c : computer.Cfg} {m n : ℕ} (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using! EvalsToInTime.trans computer.step m n a b (some c) h h'

private def embed (tail : List Wire) (config : body.tm.Cfg) : computer.Cfg :=
  cfg (some (config.l.elim (.inr .collect) Sum.inl)) (config.var, none) tail [] [] config.stk

private theorem stackContents_update (input : List Wire) (saved output : List Bool)
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

private theorem lift_stepAux (tail : List Wire) (stmt : TM2.Stmt body.tm.Γ body.tm.Λ body.tm.σ)
    (state : body.tm.σ) (contents : (k : body.tm.K) → List (body.tm.Γ k)) :
    TM2.stepAux (lift stmt) (state, none) (stackContents tail [] [] contents) =
      embed tail (TM2.stepAux stmt state contents) := by
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

private theorem body_step (tail : List Wire) (config : body.tm.Cfg) (h : config.l ≠ none) :
    computer.step (embed tail config) = (body.tm.step config).map (embed tail) := by
  rcases config with ⟨label, state, contents⟩
  cases label with
  | none => simp at h
  | some label =>
      simp only [computer, FinTM2.step, embed, cfg, program, Option.elim_some,
        TM2.step, Option.map_some]
      congr 1
      exact lift_stepAux tail (body.tm.m label) state contents

private theorem body_iterate (tail : List Wire) (n : ℕ) (start finish : body.tm.Cfg)
    (h : (fun c => c.bind body.tm.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (embed tail start)) = some (embed tail finish) := by
  induction n generalizing start with
  | zero => simpa using congrArg (Option.map (embed tail)) h
  | succ n ih =>
      have hn : (fun c => c.bind body.tm.step)^[n] none = none :=
        Function.iterate_fixed (by rfl) n
      rw [Function.iterate_succ_apply] at h ⊢
      change (fun c => c.bind body.tm.step)^[n] (body.tm.step start) = some finish at h
      change (fun c => c.bind computer.step)^[n] (computer.step (embed tail start)) = _
      have hl : start.l ≠ none := by
        intro hl
        have hs : body.tm.step start = none := by
          rcases start with ⟨label, state, contents⟩
          change label = none at hl
          subst label
          rfl
        rw [hs, hn] at h
        contradiction
      rw [body_step tail start hl]
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


/-- The checked addition runs with the unprocessed list untouched. -/
def body_run (z x : Fraction) (tail : List Wire) :
    Run (cfg (some (.inl body.tm.main)) initialState tail [] []
        (single body.tm.k₀ ((z.encode ++ x.encode).map body.inputAlphabet.symm)))
      (cfg (some (.inr .collect)) initialState tail [] []
        (single body.tm.k₁ ((z.add x).encode.map body.outputAlphabet.symm)))
      (body.time.eval (z.encode.length + x.encode.length)) where
  steps := (body.outputsFun (z, x)).steps
  evals_in_steps := by
    have h := body_iterate tail _ _ _ (body.outputsFun (z, x)).evals_in_steps
    simpa only [embed, initList, haltList, single_eq, initialState,
      Option.elim_some, Option.elim_none, RationalArithmetic.encoding,
      RationalArithmetic.encode, RationalNorm.fractionEncoding] using! h
  steps_le_m := by simpa [RationalArithmetic.encoding, RationalArithmetic.encode] using
    (body.outputsFun (z, x)).steps_le_m

local macro "loop_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, initialState,
    observe, bit, reset, empty, Function.update, field]
   <;> first | rfl | (funext k; cases k with
     | inl k => simp [Function.update, stackContents, empty] <;> (intro h; cases h; rfl)
     | inr k => cases k <;> rfl)))

def scan_run (first : Bool) (bits saved : List Bool) (tail : List Wire) :
    Run (cfg (some (.inr (.scan first))) initialState
        (bits.map some ++ none :: tail) saved [] empty)
      (cfg (some (.inr (if first then .next else .fill))) initialState
        tail (bits.reverse ++ saved) [] empty) (bits.length + 1) := by
  induction bits generalizing saved with
  | nil => cases first <;> exact one (by loop_step)
  | cons b bits ih =>
      have h : Run (cfg (some (.inr (.scan first))) initialState
            ((some b :: bits.map some) ++ none :: tail) saved [] empty)
          (cfg (some (.inr (.scan first))) initialState
            (bits.map some ++ none :: tail) (b :: saved) [] empty) 1 := one (by loop_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (b :: saved))

private theorem single_nil (k : body.tm.K) : single k [] = empty :=
  Function.update_eq_self k empty

def fill_run (saved : List Bool) (tail : List Wire) (bits : List (body.tm.Γ body.tm.k₀)) :
    Run (cfg (some (.inr .fill)) initialState tail saved [] (single body.tm.k₀ bits))
      (cfg (some (.inl body.tm.main)) initialState tail [] []
        (single body.tm.k₀ (saved.reverse.map body.inputAlphabet.symm ++ bits)))
      (saved.length + 1) := by
  induction saved generalizing bits with
  | nil => exact one (by loop_step)
  | cons b saved ih =>
      have h : Run (cfg (some (.inr .fill)) initialState tail (b :: saved) []
            (single body.tm.k₀ bits))
          (cfg (some (.inr .fill)) initialState tail saved []
            (single body.tm.k₀ (body.inputAlphabet.symm b :: bits))) 1 := by
        apply one
        simp only [computer, FinTM2.step, TM2.step, cfg, program, TM2.stepAux, stackContents,
          observe, bit, reset, initialState, List.head?_cons, List.tail_cons, Option.map_some,
          Option.isSome_some, Bool.cond_true, Option.getD_some]
        congr 2
        funext k
        cases k with
        | inl k =>
            by_cases hk : k = body.tm.k₀
            · subst k; simp [single, stackContents]
            · simp [single, stackContents, Function.update, hk]
        | inr k => cases k <;> simp [stackContents]
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (body.inputAlphabet.symm b :: bits))

def collect_run (bits : List (body.tm.Γ body.tm.k₁)) (tail : List Wire) (saved : List Bool) :
    Run (cfg (some (.inr .collect)) initialState tail saved [] (single body.tm.k₁ bits))
      (cfg (some (.inr .restore)) initialState (none :: tail)
        (List.append (α := Bool) (bits.reverse.map body.outputAlphabet) saved) [] empty) (bits.length + 1) := by
  induction bits generalizing saved with
  | nil => rw [single_nil]; exact one (by loop_step)
  | cons b bits ih =>
      have h : Run (cfg (some (.inr .collect)) initialState tail saved [] (single body.tm.k₁ (b :: bits)))
          (cfg (some (.inr .collect)) initialState tail (body.outputAlphabet b :: saved) []
            (single body.tm.k₁ bits)) 1 := by
        apply one
        simp only [computer, FinTM2.step, TM2.step, cfg, program, TM2.stepAux, stackContents,
          single, Function.update_self, List.head?_cons, List.tail_cons, Option.map_some,
          observe, bit, reset, initialState, Option.isSome_some, Bool.cond_true, Option.getD_some]
        congr 2
        funext k
        cases k with
        | inl k =>
            by_cases hk : k = body.tm.k₁
            · subst k; simp [stackContents]
            · simp [stackContents, Function.update, hk]
        | inr k => cases k <;> simp [stackContents]
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (body.outputAlphabet b :: saved))

def restore_run (saved : List Bool) (tail : List Wire) :
    Run (cfg (some (.inr .restore)) initialState tail saved [] empty)
      (cfg (some (.inr (.scan true))) initialState (saved.reverse.map some ++ tail) [] [] empty)
      (saved.length + 1) := by
  induction saved generalizing tail with
  | nil => exact one (by loop_step)
  | cons b saved ih =>
      have h : Run (cfg (some (.inr .restore)) initialState tail (b :: saved) [] empty)
          (cfg (some (.inr .restore)) initialState (some b :: tail) saved [] empty) 1 :=
        one (by loop_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (some b :: tail))

def finish_run (saved output : List Bool) :
    Run (cfg (some (.inr .finish)) initialState [] saved output empty)
      (cfg none initialState [] [] (saved.reverse ++ output) empty) (saved.length + 1) := by
  induction saved generalizing output with
  | nil => exact one (by loop_step)
  | cons b saved ih =>
      have h : Run (cfg (some (.inr .finish)) initialState [] (b :: saved) output empty)
          (cfg (some (.inr .finish)) initialState [] saved (b :: output) empty) 1 :=
        one (by loop_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (b :: output))

def enter_run (z x : Fraction) (xs : List Fraction) :
    Run (ready z (x :: xs))
      (cfg (some (.inl body.tm.main)) initialState (fields xs) [] []
        (single body.tm.k₀ ((z.encode ++ x.encode).map body.inputAlphabet.symm)))
      (2 * (z.encode.length + x.encode.length) + 4) := by
  have ha := scan_run true z.encode [] (field x ++ fields xs)
  have hn : Run (cfg (some (.inr .next)) initialState (field x ++ fields xs) z.encode.reverse [] empty)
      (cfg (some (.inr (.scan false))) initialState (field x ++ fields xs) z.encode.reverse [] empty) 1 := by
    apply one
    loop_step
  have hb := scan_run false x.encode z.encode.reverse (fields xs)
  have hf := fill_run (x.encode.reverse ++ z.encode.reverse) (fields xs) []
  simp only [single_nil, List.reverse_append, List.reverse_reverse,
    List.append_nil, List.length_append, List.length_reverse] at ha hb hf
  simp only [field, List.append_assoc, List.singleton_append] at ha hn
  have h := seq ha (seq hn (seq hb hf))
  convert h using 1 <;> first | omega | simp [ready, encode, fields, field, List.append_assoc]

def return_run (z : Fraction) (xs : List Fraction) :
    Run (cfg (some (.inr .collect)) initialState (fields xs) [] []
        (single body.tm.k₁ (z.encode.map body.outputAlphabet.symm)))
      (ready z xs) (2 * z.encode.length + 2) := by
  have hc := collect_run (z.encode.map body.outputAlphabet.symm) (fields xs) []
  simp only [← List.map_reverse, List.map_map, Equiv.apply_symm_apply, Function.comp_def,
    List.map_id_fun', id_eq, List.append_eq, List.append_nil, List.length_map] at hc
  have hr := restore_run z.encode.reverse (none :: fields xs)
  simp only [List.reverse_reverse, List.length_reverse] at hr
  convert seq hc hr using 1 <;> first | omega | simp [ready, encode, field, List.append_assoc]

def iteration_cycle (z x : Fraction) (xs : List Fraction) :
    Run (ready z (x :: xs)) (ready (z.add x) xs)
      (body.time.eval (z.encode.length + x.encode.length) +
        2 * (z.encode.length + x.encode.length) + 2 * (z.add x).encode.length + 6) := by
  convert seq (enter_run z x xs) (seq (body_run z x (fields xs)) (return_run (z.add x) xs)) using 1
  omega

def exit_run (z : Fraction) : Run (ready z []) (done z) (2 * z.encode.length + 3) := by
  have hs := scan_run true z.encode [] []
  simp only [ite_true, List.append_nil] at hs
  have hn : Run (cfg (some (.inr .next)) initialState [] z.encode.reverse [] empty)
      (cfg (some (.inr .finish)) initialState [] z.encode.reverse [] empty) 1 := one (by loop_step)
  have hf := finish_run z.encode.reverse []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hf
  convert seq hs (seq hn hf) using 1 <;> first | rfl | omega | simp [ready, encode, fields, field]

theorem ready_eq_initList (z : Fraction) (xs : List Fraction) :
    ready z xs = initList computer (encode (z, xs)) := by
  simp only [ready, initList, computer, cfg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

theorem done_eq_haltList (z : Fraction) : done z = haltList computer z.encode := by
  simp only [done, haltList, computer, cfg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

end
end PhdThesisLean.RationalSum.Machine
