import PhdThesisLean.RationalDotProductEncoding

/-!
# Finite-machine traversal of paired rational columns

The controller loads each concatenated fraction pair into the proved
multiplication machine. The remaining source and reversed product prefix
survive every embedded transition. Exit reverses the output and emits the
fixed zero prefix required by exact summation. The traversal follows the
already checked norm-list controller, with a different source codec and body.
-/
namespace PhdThesisLean.RationalDotProduct.Machine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open StateTransition RationalVerifierBounds RationalSum
open LeanNPHardness.MachineComposition

set_option backward.isDefEq.respectTransparency false
noncomputable section

def body := RationalArithmetic.multiplicationComputableInPolyTime
abbrev Wire := Option Bool
inductive External | input | saved | accumulated | output deriving DecidableEq, Fintype
abbrev Stack := body.tm.K ⊕ External
abbrev Alphabet : Stack → Type
  | .inl k => body.tm.Γ k
  | .inr .saved => Bool
  | .inr .input | .inr .accumulated | .inr .output => Wire
inductive Control | next | scan | fill | collect | finish deriving DecidableEq, Fintype
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

/-- Push a fixed finite prefix in one finite control statement. -/
def pushPrefix (bits : List Wire) (next : TM2.Stmt Alphabet Label State) :
    TM2.Stmt Alphabet Label State :=
  bits.foldl (fun rest b => .push (.inr .output) (fun _ => b) rest) next

def program : Label → TM2.Stmt Alphabet Label State
  | .inl label => lift (body.tm.m label)
  | .inr .next => .peek (.inr .input) observe <|
      .branch (fun s => s.2.isSome)
        (reset <| .goto fun _ => .inr .scan)
        (reset <| .goto fun _ => .inr .finish)
  | .inr .scan => .pop (.inr .input) observe <|
      .branch (fun s => (s.2.getD none).isSome)
        (.push (.inr .saved) bit <| reset <| .goto fun _ => .inr .scan)
        (reset <| .goto fun _ => .inr .fill)
  | .inr .fill => .pop (.inr .saved) (fun s b => observe s (b.map some)) <|
      .branch (fun s => s.2.isSome)
        (.push (.inl body.tm.k₀) (fun s => body.inputAlphabet.symm (bit s)) <|
          reset <| .goto fun _ => .inr .fill)
        (reset <| .goto fun _ => .inl body.tm.main)
  | .inr .collect => .pop (.inl body.tm.k₁)
      (fun s b => observe s (b.map (fun b => some (body.outputAlphabet b)))) <|
      .branch (fun s => s.2.isSome)
        (.push (.inr .accumulated) (fun s => some (bit s)) <|
          reset <| .goto fun _ => .inr .collect)
        (.push (.inr .accumulated) (fun _ => none) <| reset <| .goto fun _ => .inr .next)
  | .inr .finish => .pop (.inr .accumulated) observe <|
      .branch (fun s => s.2.isSome)
        (.push (.inr .output) (fun s => s.2.getD none) <| reset <| .goto fun _ => .inr .finish)
        (pushPrefix (field Fraction.zero) (reset .halt))

def computer : FinTM2 where
  K := Stack
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := Alphabet
  Λ := Label
  main := .inr .next
  σ := State
  initialState := initialState
  Γk₀Fin := inferInstance
  m := program

def stackContents (input : List Wire) (saved : List Bool) (accumulated output : List Wire)
    (contents : (k : body.tm.K) → List (body.tm.Γ k)) : (k : Stack) → List (Alphabet k)
  | .inl k => contents k
  | .inr .input => input
  | .inr .saved => saved
  | .inr .accumulated => accumulated
  | .inr .output => output
def cfg (label : Option Label) (state : State) (input : List Wire) (saved : List Bool)
    (accumulated output : List Wire)
    (contents : (k : body.tm.K) → List (body.tm.Γ k)) : computer.Cfg :=
  ⟨label, state, stackContents input saved accumulated output contents⟩
def empty : (k : body.tm.K) → List (body.tm.Γ k) := fun _ => []
def single (k : body.tm.K) (bits : List (body.tm.Γ k)) := Function.update empty k bits
def ready (xs : List (Fraction × Fraction)) (acc : List Wire) : computer.Cfg :=
  cfg (some (.inr .next)) initialState (pairFields xs) [] acc [] empty
def done (bits : List Wire) : computer.Cfg := cfg none initialState [] [] [] bits empty
abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using! h, steps_le_m := le_rfl }
def seq {a b c : computer.Cfg} {m n : ℕ} (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using! EvalsToInTime.trans computer.step m n a b (some c) h h'

private def embed (tail acc : List Wire) (config : body.tm.Cfg) : computer.Cfg :=
  cfg (some (config.l.elim (.inr .collect) Sum.inl)) (config.var, none) tail [] acc [] config.stk

private theorem stackContents_update (input : List Wire) (saved : List Bool) (acc output : List Wire)
    (contents : (k : body.tm.K) → List (body.tm.Γ k)) (k : body.tm.K) (value : List (body.tm.Γ k)) :
    stackContents input saved acc output (Function.update contents k value) =
      Function.update (stackContents input saved acc output contents) (.inl k) value := by
  funext index
  cases index with
  | inr index => cases index <;> simp [stackContents]
  | inl index =>
      by_cases h : index = k
      · subst index; simp [stackContents]
      · simp [stackContents, Function.update, h]

private theorem lift_stepAux (tail acc : List Wire) (stmt : TM2.Stmt body.tm.Γ body.tm.Λ body.tm.σ)
    (state : body.tm.σ) (contents : (k : body.tm.K) → List (body.tm.Γ k)) :
    TM2.stepAux (lift stmt) (state, none) (stackContents tail [] acc [] contents) =
      embed tail acc (TM2.stepAux stmt state contents) := by
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

private theorem body_step (tail acc : List Wire) (config : body.tm.Cfg) (h : config.l ≠ none) :
    computer.step (embed tail acc config) = (body.tm.step config).map (embed tail acc) := by
  rcases config with ⟨label, state, contents⟩
  cases label with
  | none => simp at h
  | some label =>
      simp only [computer, FinTM2.step, embed, cfg, program, Option.elim_some,
        TM2.step, Option.map_some]
      congr 1
      exact lift_stepAux tail acc (body.tm.m label) state contents

private theorem body_iterate (tail acc : List Wire) (n : ℕ) (start finish : body.tm.Cfg)
    (h : (fun c => c.bind body.tm.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (embed tail acc start)) = some (embed tail acc finish) := by
  induction n generalizing start with
  | zero => simpa using congrArg (Option.map (embed tail acc)) h
  | succ n ih =>
      have hn : (fun c => c.bind body.tm.step)^[n] none = none :=
        Function.iterate_fixed (by rfl) n
      rw [Function.iterate_succ_apply] at h ⊢
      change (fun c => c.bind body.tm.step)^[n] (body.tm.step start) = some finish at h
      change (fun c => c.bind computer.step)^[n] (computer.step (embed tail acc start)) = _
      have hl : start.l ≠ none := by
        intro hl
        have hs : body.tm.step start = none := by
          rcases start with ⟨label, state, contents⟩
          change label = none at hl
          subst label
          rfl
        rw [hs, hn] at h
        contradiction
      rw [body_step tail acc start hl]
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


/-- The checked product runs with the unprocessed list untouched. -/
def body_run (x : Fraction × Fraction) (tail acc : List Wire) :
    Run (cfg (some (.inl body.tm.main)) initialState tail [] acc []
        (single body.tm.k₀ ((RationalArithmetic.encode x).map body.inputAlphabet.symm)))
      (cfg (some (.inr .collect)) initialState tail [] acc []
        (single body.tm.k₁ ((multiply x).encode.map body.outputAlphabet.symm)))
      (body.time.eval (RationalArithmetic.encode x).length) where
  steps := (body.outputsFun x).steps
  evals_in_steps := by
    have h := body_iterate tail acc _ _ _ (body.outputsFun x).evals_in_steps
    simpa only [embed, initList, haltList, single_eq, initialState,
      Option.elim_some, Option.elim_none, RationalArithmetic.encoding, RationalNorm.fractionEncoding, multiply] using! h
  steps_le_m := by simpa [RationalArithmetic.encoding] using
    (body.outputsFun x).steps_le_m

private theorem zero_encode : Fraction.zero.encode =
    [false, false, true, false, true] := rfl

local macro "loop_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, initialState,
    observe, bit, reset, empty, Function.update, zero_encode, field, pairField, pushPrefix]
   <;> first | rfl | (funext k; cases k with
     | inl k => simp [Function.update, stackContents, empty] <;> (intro h; cases h; rfl)
     | inr k => cases k <;> rfl)))

def scan_run (bits saved : List Bool) (tail acc : List Wire) :
    Run (cfg (some (.inr .scan)) initialState
        (bits.map some ++ none :: tail) saved acc [] empty)
      (cfg (some (.inr .fill)) initialState
        tail (bits.reverse ++ saved) acc [] empty) (bits.length + 1) := by
  induction bits generalizing saved with
  | nil => exact one (by loop_step)
  | cons b bits ih =>
      have h : Run (cfg (some (.inr .scan)) initialState
            ((some b :: bits.map some) ++ none :: tail) saved acc [] empty)
          (cfg (some (.inr .scan)) initialState
            (bits.map some ++ none :: tail) (b :: saved) acc [] empty) 1 := one (by loop_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (b :: saved))

private theorem single_nil (k : body.tm.K) : single k [] = empty :=
  Function.update_eq_self k empty

def fill_run (saved : List Bool) (tail acc : List Wire) (bits : List (body.tm.Γ body.tm.k₀)) :
    Run (cfg (some (.inr .fill)) initialState tail saved acc [] (single body.tm.k₀ bits))
      (cfg (some (.inl body.tm.main)) initialState tail [] acc []
        (single body.tm.k₀ (saved.reverse.map body.inputAlphabet.symm ++ bits)))
      (saved.length + 1) := by
  induction saved generalizing bits with
  | nil => exact one (by loop_step)
  | cons b saved ih =>
      have h : Run (cfg (some (.inr .fill)) initialState tail (b :: saved) acc []
            (single body.tm.k₀ bits))
          (cfg (some (.inr .fill)) initialState tail saved acc []
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

def collect_run (bits : List (body.tm.Γ body.tm.k₁)) (tail acc : List Wire) :
    Run (cfg (some (.inr .collect)) initialState tail [] acc [] (single body.tm.k₁ bits))
      (cfg (some (.inr .next)) initialState tail []
        (none :: List.append (α := Wire)
          (bits.reverse.map (fun b => some (body.outputAlphabet b))) acc) [] empty)
      (bits.length + 1) := by
  induction bits generalizing acc with
  | nil => rw [single_nil]; exact one (by loop_step)
  | cons b bits ih =>
      have h : Run (cfg (some (.inr .collect)) initialState tail [] acc [] (single body.tm.k₁ (b :: bits)))
          (cfg (some (.inr .collect)) initialState tail [] (some (body.outputAlphabet b) :: acc) []
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
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (some (body.outputAlphabet b) :: acc))

def finish_run (acc output : List Wire) :
    Run (cfg (some (.inr .finish)) initialState [] [] acc output empty)
      (done (field Fraction.zero ++ (acc.reverse ++ output))) (acc.length + 1) := by
  induction acc generalizing output with
  | nil => apply one; simp only [done]; loop_step
  | cons b acc ih =>
      have h : Run (cfg (some (.inr .finish)) initialState [] [] (b :: acc) output empty)
          (cfg (some (.inr .finish)) initialState [] [] acc (b :: output) empty) 1 :=
        one (by loop_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (b :: output))

def enter_run (x : Fraction × Fraction) (xs : List (Fraction × Fraction)) (acc : List Wire) :
    Run (ready (x :: xs) acc)
      (cfg (some (.inl body.tm.main)) initialState (pairFields xs) [] acc []
        (single body.tm.k₀ ((RationalArithmetic.encode x).map body.inputAlphabet.symm)))
      (2 * (RationalArithmetic.encode x).length + 3) := by
  have hn : Run (ready (x :: xs) acc)
      (cfg (some (.inr .scan)) initialState (pairField x ++ pairFields xs) [] acc [] empty) 1 := by
    apply one
    simp only [ready, pairFields, List.flatMap_cons]
    loop_step
  have hs := scan_run (RationalArithmetic.encode x) [] (pairFields xs) acc
  have hf := fill_run (RationalArithmetic.encode x).reverse (pairFields xs) acc []
  simp only [single_nil, List.reverse_reverse, List.append_nil, List.length_reverse] at hs hf
  simp only [pairField, List.append_assoc, List.singleton_append] at hn
  convert seq hn (seq hs hf) using 1; omega

def iteration_cycle (x : Fraction × Fraction) (xs : List (Fraction × Fraction)) (acc : List Wire) :
    Run (ready (x :: xs) acc) (ready xs ((field (multiply x)).reverse ++ acc))
      (body.time.eval (RationalArithmetic.encode x).length + 2 * (RationalArithmetic.encode x).length + (multiply x).encode.length + 4) := by
  have hc := collect_run ((multiply x).encode.map body.outputAlphabet.symm) (pairFields xs) acc
  simp only [← List.map_reverse, List.map_map, Equiv.apply_symm_apply,
    Function.comp_def, List.length_map] at hc
  convert seq (enter_run x xs acc) (seq (body_run x (pairFields xs) acc) hc) using 1 <;>
    first | omega | simp [ready, field, List.reverse_append, List.map_reverse]

def exit_run (acc : List Wire) :
    Run (ready [] acc) (done (field Fraction.zero ++ acc.reverse)) (acc.length + 2) := by
  have hn : Run (ready [] acc)
      (cfg (some (.inr .finish)) initialState [] [] acc [] empty) 1 := by
    apply one
    simp only [ready, pairFields, List.flatMap_nil]
    loop_step
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq hn (finish_run acc [])

theorem ready_eq_initList (xs : List (Fraction × Fraction)) :
    ready xs [] = initList computer (pairFields xs) := by
  simp only [ready, initList, computer, cfg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

theorem done_eq_haltList (bits : List Wire) : done bits = haltList computer bits := by
  simp only [done, haltList, computer, cfg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

end
end PhdThesisLean.RationalDotProduct.Machine
