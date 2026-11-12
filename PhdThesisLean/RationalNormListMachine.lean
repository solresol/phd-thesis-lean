import PhdThesisLean.RationalSum

/-!
# A finite machine for a runtime-length list of p-adic norms

Each source fraction is loaded into the existing binary norm machine. The
unprocessed tail and the reversed output prefix survive that call. At exit,
the output is reversed once and the fixed zero prefix for summation is emitted.
-/
namespace PhdThesisLean.RationalNormList.Machine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open StateTransition RationalVerifierBounds RationalSum
open LeanNPHardness.MachineComposition

set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def body := RationalNorm.computableInPolyTime p
abbrev Wire := Option Bool
inductive External | input | saved | accumulated | output deriving DecidableEq, Fintype
abbrev Stack := (body (p := p)).tm.K ⊕ External
abbrev Alphabet : (Stack (p := p)) → Type
  | .inl k => (body (p := p)).tm.Γ k
  | .inr .saved => Bool
  | .inr .input | .inr .accumulated | .inr .output => Wire
inductive Control | next | scan | fill | collect | finish deriving DecidableEq, Fintype
abbrev Label := (body (p := p)).tm.Λ ⊕ Control
abbrev State := (body (p := p)).tm.σ × Option Wire
instance : Fintype (body (p := p)).tm.K := (body (p := p)).tm.kFin
instance : Fintype (body (p := p)).tm.Λ := (body (p := p)).tm.ΛFin
instance : Fintype (body (p := p)).tm.σ := (body (p := p)).tm.σFin
def initialState : (State (p := p)) := ((body (p := p)).tm.initialState, none)
private def observe (s : (State (p := p))) (cell : Option Wire) : (State (p := p)) := (s.1, cell)
private def bit (s : (State (p := p))) : Bool := (s.2.getD none).getD false
private def reset : TM2.Stmt (Alphabet (p := p)) (Label (p := p)) (State (p := p)) → TM2.Stmt (Alphabet (p := p)) (Label (p := p)) (State (p := p)) :=
  .load (fun _ => (initialState (p := p)))

def lift : TM2.Stmt (body (p := p)).tm.Γ (body (p := p)).tm.Λ (body (p := p)).tm.σ → TM2.Stmt (Alphabet (p := p)) (Label (p := p)) (State (p := p))
  | .push k write next => .push (.inl k) (fun s => write s.1) (lift next)
  | .peek k read next => .peek (.inl k) (fun s b => (read s.1 b, s.2)) (lift next)
  | .pop k read next => .pop (.inl k) (fun s b => (read s.1 b, s.2)) (lift next)
  | .load update next => .load (fun s => (update s.1, s.2)) (lift next)
  | .branch test yes no => .branch (fun s => test s.1) (lift yes) (lift no)
  | .goto next => .goto (fun s => .inl (next s.1))
  | .halt => .goto (fun _ => .inr .collect)

/-- Push a fixed finite prefix in one finite control statement. -/
def pushPrefix (bits : List Wire) (next : TM2.Stmt (Alphabet (p := p)) (Label (p := p)) (State (p := p))) :
    TM2.Stmt (Alphabet (p := p)) (Label (p := p)) (State (p := p)) :=
  bits.foldl (fun rest b => .push (.inr .output) (fun _ => b) rest) next

def program : (Label (p := p)) → TM2.Stmt (Alphabet (p := p)) (Label (p := p)) (State (p := p))
  | .inl label => lift ((body (p := p)).tm.m label)
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
        (.push (.inl (body (p := p)).tm.k₀) (fun s => (body (p := p)).inputAlphabet.symm (bit s)) <|
          reset <| .goto fun _ => .inr .fill)
        (reset <| .goto fun _ => .inl (body (p := p)).tm.main)
  | .inr .collect => .pop (.inl (body (p := p)).tm.k₁)
      (fun s b => observe s (b.map (fun b => some ((body (p := p)).outputAlphabet b)))) <|
      .branch (fun s => s.2.isSome)
        (.push (.inr .accumulated) (fun s => some (bit s)) <|
          reset <| .goto fun _ => .inr .collect)
        (.push (.inr .accumulated) (fun _ => none) <| reset <| .goto fun _ => .inr .next)
  | .inr .finish => .pop (.inr .accumulated) observe <|
      .branch (fun s => s.2.isSome)
        (.push (.inr .output) (fun s => s.2.getD none) <| reset <| .goto fun _ => .inr .finish)
        ((pushPrefix (p := p)) (field Fraction.zero) (reset .halt))

def computer : FinTM2 where
  K := (Stack (p := p))
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := (Alphabet (p := p))
  Λ := (Label (p := p))
  main := .inr .next
  σ := (State (p := p))
  initialState := (initialState (p := p))
  Γk₀Fin := inferInstance
  m := (program (p := p))

def stackContents (input : List Wire) (saved : List Bool) (accumulated output : List Wire)
    (contents : (k : (body (p := p)).tm.K) → List ((body (p := p)).tm.Γ k)) : (k : (Stack (p := p))) → List ((Alphabet (p := p)) k)
  | .inl k => contents k
  | .inr .input => input
  | .inr .saved => saved
  | .inr .accumulated => accumulated
  | .inr .output => output
def cfg (label : Option (Label (p := p))) (state : (State (p := p))) (input : List Wire) (saved : List Bool)
    (accumulated output : List Wire)
    (contents : (k : (body (p := p)).tm.K) → List ((body (p := p)).tm.Γ k)) : (computer (p := p)).Cfg :=
  ⟨label, state, stackContents input saved accumulated output contents⟩
def empty : (k : (body (p := p)).tm.K) → List ((body (p := p)).tm.Γ k) := fun _ => []
def single (k : (body (p := p)).tm.K) (bits : List ((body (p := p)).tm.Γ k)) := Function.update (empty (p := p)) k bits
def ready (xs : List Fraction) (acc : List Wire) : (computer (p := p)).Cfg :=
  cfg (some (.inr .next)) (initialState (p := p)) (fields xs) [] acc [] (empty (p := p))
def done (bits : List Wire) : (computer (p := p)).Cfg := cfg none (initialState (p := p)) [] [] [] bits (empty (p := p))
abbrev Run (a b : (computer (p := p)).Cfg) (time : ℕ) := EvalsToInTime (computer (p := p)).step a (some b) time
private def one {a b : (computer (p := p)).Cfg} (h : (computer (p := p)).step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using! h, steps_le_m := le_rfl }
def seq {a b c : (computer (p := p)).Cfg} {m n : ℕ} (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using! EvalsToInTime.trans (computer (p := p)).step m n a b (some c) h h'

private def embed (tail acc : List Wire) (config : (body (p := p)).tm.Cfg) : (computer (p := p)).Cfg :=
  cfg (some (config.l.elim (.inr .collect) Sum.inl)) (config.var, none) tail [] acc [] config.stk

private theorem stackContents_update (input : List Wire) (saved : List Bool) (acc output : List Wire)
    (contents : (k : (body (p := p)).tm.K) → List ((body (p := p)).tm.Γ k)) (k : (body (p := p)).tm.K) (value : List ((body (p := p)).tm.Γ k)) :
    stackContents input saved acc output (Function.update contents k value) =
      Function.update (stackContents input saved acc output contents) (.inl k) value := by
  funext index
  cases index with
  | inr index => cases index <;> simp [stackContents]
  | inl index =>
      by_cases h : index = k
      · subst index; simp [stackContents]
      · simp [stackContents, Function.update, h]

private theorem lift_stepAux (tail acc : List Wire) (stmt : TM2.Stmt (body (p := p)).tm.Γ (body (p := p)).tm.Λ (body (p := p)).tm.σ)
    (state : (body (p := p)).tm.σ) (contents : (k : (body (p := p)).tm.K) → List ((body (p := p)).tm.Γ k)) :
    TM2.stepAux (lift stmt) (state, none) (stackContents tail [] acc [] contents) =
      embed tail acc (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [lift, TM2.stepAux]
      rw [← (stackContents_update (p := p))]
      exact ih _ _
  | peek k read next ih => simpa only [lift, TM2.stepAux, stackContents] using ih _ _
  | pop k read next ih =>
      simp only [lift, TM2.stepAux, stackContents]
      rw [← (stackContents_update (p := p))]
      exact ih _ _
  | load update next ih => simpa only [lift, TM2.stepAux] using ih _ _
  | branch test yes no iy ino =>
      cases h : test state <;> simp only [lift, TM2.stepAux, h, Bool.cond_false, Bool.cond_true]
      · exact ino _ _
      · exact iy _ _
  | goto next => rfl
  | halt => rfl

private theorem body_step (tail acc : List Wire) (config : (body (p := p)).tm.Cfg) (h : config.l ≠ none) :
    (computer (p := p)).step (embed tail acc config) = ((body (p := p)).tm.step config).map (embed tail acc) := by
  rcases config with ⟨label, state, contents⟩
  cases label with
  | none => simp at h
  | some label =>
      simp only [computer, FinTM2.step, embed, cfg, program, Option.elim_some,
        TM2.step, Option.map_some]
      congr 1
      exact lift_stepAux tail acc ((body (p := p)).tm.m label) state contents

private theorem body_iterate (tail acc : List Wire) (n : ℕ) (start finish : (body (p := p)).tm.Cfg)
    (h : (fun c => c.bind (body (p := p)).tm.step)^[n] (some start) = some finish) :
    (fun c => c.bind (computer (p := p)).step)^[n] (some (embed tail acc start)) = some (embed tail acc finish) := by
  induction n generalizing start with
  | zero => simpa using congrArg (Option.map (embed tail acc)) h
  | succ n ih =>
      have hn : (fun c => c.bind (body (p := p)).tm.step)^[n] none = none :=
        Function.iterate_fixed (by rfl) n
      rw [Function.iterate_succ_apply] at h ⊢
      change (fun c => c.bind (body (p := p)).tm.step)^[n] ((body (p := p)).tm.step start) = some finish at h
      change (fun c => c.bind (computer (p := p)).step)^[n] ((computer (p := p)).step (embed tail acc start)) = _
      have hl : start.l ≠ none := by
        intro hl
        have hs : (body (p := p)).tm.step start = none := by
          rcases start with ⟨label, state, contents⟩
          change label = none at hl
          subst label
          rfl
        rw [hs, hn] at h
        contradiction
      rw [body_step tail acc start hl]
      cases hs : (body (p := p)).tm.step start with
      | none => rw [hs, hn] at h; contradiction
      | some mid =>
          simp only [Option.map_some]
          exact ih mid (by rw [hs] at h; exact h)

private theorem single_eq (k : (body (p := p)).tm.K) (bits : List ((body (p := p)).tm.Γ k)) :
    single k bits = fun j => if h : j = k then (by rw [h]; exact bits) else [] := by
  funext j
  by_cases h : j = k
  · subst j; simp [single]
  · simp [single, empty, Function.update, h]


/-- The checked norm runs with the unprocessed list untouched. -/
def body_run (x : Fraction) (tail acc : List Wire) :
    Run (cfg (some (.inl (body (p := p)).tm.main)) (initialState (p := p)) tail [] acc []
        (single (body (p := p)).tm.k₀ (x.encode.map (body (p := p)).inputAlphabet.symm)))
      (cfg (some (.inr .collect)) (initialState (p := p)) tail [] acc []
        (single (body (p := p)).tm.k₁ ((x.norm p).encode.map (body (p := p)).outputAlphabet.symm)))
      ((body (p := p)).time.eval x.encode.length) where
  steps := ((body (p := p)).outputsFun x).steps
  evals_in_steps := by
    have h := body_iterate tail acc _ _ _ ((body (p := p)).outputsFun x).evals_in_steps
    simpa only [embed, initList, haltList, single_eq, initialState,
      Option.elim_some, Option.elim_none, RationalNorm.fractionEncoding] using! h
  steps_le_m := by simpa [RationalNorm.fractionEncoding] using
    ((body (p := p)).outputsFun x).steps_le_m

private theorem zero_encode : Fraction.zero.encode =
    [false, false, true, false, true] := rfl

local macro "loop_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, initialState,
    observe, bit, reset, empty, Function.update, zero_encode, field, pushPrefix]
   <;> first | rfl | (funext k; cases k with
     | inl k => simp [Function.update, stackContents, empty] <;> (intro h; cases h; rfl)
     | inr k => cases k <;> rfl)))

def scan_run (bits saved : List Bool) (tail acc : List Wire) :
    Run (cfg (some (.inr .scan)) (initialState (p := p))
        (bits.map some ++ none :: tail) saved acc [] (empty (p := p)))
      (cfg (some (.inr .fill)) (initialState (p := p))
        tail (bits.reverse ++ saved) acc [] (empty (p := p))) (bits.length + 1) := by
  induction bits generalizing saved with
  | nil => exact one (by loop_step)
  | cons b bits ih =>
      have h : Run (cfg (some (.inr .scan)) (initialState (p := p))
            ((some b :: bits.map some) ++ none :: tail) saved acc [] (empty (p := p)))
          (cfg (some (.inr .scan)) (initialState (p := p))
            (bits.map some ++ none :: tail) (b :: saved) acc [] (empty (p := p))) 1 := one (by loop_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (b :: saved))

private theorem single_nil (k : (body (p := p)).tm.K) : single k [] = (empty (p := p)) :=
  Function.update_eq_self k (empty (p := p))

def fill_run (saved : List Bool) (tail acc : List Wire) (bits : List ((body (p := p)).tm.Γ (body (p := p)).tm.k₀)) :
    Run (cfg (some (.inr .fill)) (initialState (p := p)) tail saved acc [] (single (body (p := p)).tm.k₀ bits))
      (cfg (some (.inl (body (p := p)).tm.main)) (initialState (p := p)) tail [] acc []
        (single (body (p := p)).tm.k₀ (saved.reverse.map (body (p := p)).inputAlphabet.symm ++ bits)))
      (saved.length + 1) := by
  induction saved generalizing bits with
  | nil => exact one (by loop_step)
  | cons b saved ih =>
      have h : Run (cfg (some (.inr .fill)) (initialState (p := p)) tail (b :: saved) acc []
            (single (body (p := p)).tm.k₀ bits))
          (cfg (some (.inr .fill)) (initialState (p := p)) tail saved acc []
            (single (body (p := p)).tm.k₀ ((body (p := p)).inputAlphabet.symm b :: bits))) 1 := by
        apply one
        simp only [computer, FinTM2.step, TM2.step, cfg, program, TM2.stepAux, stackContents,
          observe, bit, reset, initialState, List.head?_cons, List.tail_cons, Option.map_some,
          Option.isSome_some, Bool.cond_true, Option.getD_some]
        congr 2
        funext k
        cases k with
        | inl k =>
            by_cases hk : k = (body (p := p)).tm.k₀
            · subst k; simp [single, stackContents]
            · simp [single, stackContents, Function.update, hk]
        | inr k => cases k <;> simp [stackContents]
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih ((body (p := p)).inputAlphabet.symm b :: bits))

def collect_run (bits : List ((body (p := p)).tm.Γ (body (p := p)).tm.k₁)) (tail acc : List Wire) :
    Run (cfg (some (.inr .collect)) (initialState (p := p)) tail [] acc [] (single (body (p := p)).tm.k₁ bits))
      (cfg (some (.inr .next)) (initialState (p := p)) tail []
        (none :: List.append (α := Wire)
          (bits.reverse.map (fun b => some ((body (p := p)).outputAlphabet b))) acc) [] (empty (p := p)))
      (bits.length + 1) := by
  induction bits generalizing acc with
  | nil => rw [single_nil]; exact one (by loop_step)
  | cons b bits ih =>
      have h : Run (cfg (some (.inr .collect)) (initialState (p := p)) tail [] acc [] (single (body (p := p)).tm.k₁ (b :: bits)))
          (cfg (some (.inr .collect)) (initialState (p := p)) tail [] (some ((body (p := p)).outputAlphabet b) :: acc) []
            (single (body (p := p)).tm.k₁ bits)) 1 := by
        apply one
        simp only [computer, FinTM2.step, TM2.step, cfg, program, TM2.stepAux, stackContents,
          single, Function.update_self, List.head?_cons, List.tail_cons, Option.map_some,
          observe, bit, reset, initialState, Option.isSome_some, Bool.cond_true, Option.getD_some]
        congr 2
        funext k
        cases k with
        | inl k =>
            by_cases hk : k = (body (p := p)).tm.k₁
            · subst k; simp [stackContents]
            · simp [stackContents, Function.update, hk]
        | inr k => cases k <;> simp [stackContents]
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (some ((body (p := p)).outputAlphabet b) :: acc))

def finish_run (acc output : List Wire) :
    Run (cfg (some (.inr .finish)) (initialState (p := p)) [] [] acc output (empty (p := p)))
      ((done (p := p)) (field Fraction.zero ++ (acc.reverse ++ output))) (acc.length + 1) := by
  induction acc generalizing output with
  | nil => apply one; simp only [done]; loop_step
  | cons b acc ih =>
      have h : Run (cfg (some (.inr .finish)) (initialState (p := p)) [] [] (b :: acc) output (empty (p := p)))
          (cfg (some (.inr .finish)) (initialState (p := p)) [] [] acc (b :: output) (empty (p := p))) 1 :=
        one (by loop_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (b :: output))

def enter_run (x : Fraction) (xs : List Fraction) (acc : List Wire) :
    Run ((ready (p := p)) (x :: xs) acc)
      (cfg (some (.inl (body (p := p)).tm.main)) (initialState (p := p)) (fields xs) [] acc []
        (single (body (p := p)).tm.k₀ (x.encode.map (body (p := p)).inputAlphabet.symm)))
      (2 * x.encode.length + 3) := by
  have hn : Run ((ready (p := p)) (x :: xs) acc)
      (cfg (some (.inr .scan)) (initialState (p := p)) (field x ++ fields xs) [] acc [] (empty (p := p))) 1 := by
    apply one
    simp only [ready, fields, List.flatMap_cons]
    loop_step
  have hs := (scan_run (p := p)) x.encode [] (fields xs) acc
  have hf := (fill_run (p := p)) x.encode.reverse (fields xs) acc []
  simp only [single_nil, List.reverse_reverse, List.append_nil, List.length_reverse] at hs hf
  simp only [field, List.append_assoc, List.singleton_append] at hn
  convert seq hn (seq hs hf) using 1; omega

def iteration_cycle (x : Fraction) (xs : List Fraction) (acc : List Wire) :
    Run ((ready (p := p)) (x :: xs) acc) ((ready (p := p)) xs ((field (x.norm p)).reverse ++ acc))
      ((body (p := p)).time.eval x.encode.length + 2 * x.encode.length + (x.norm p).encode.length + 4) := by
  have hc := (collect_run (p := p)) ((x.norm p).encode.map (body (p := p)).outputAlphabet.symm) (fields xs) acc
  simp only [← List.map_reverse, List.map_map, Equiv.apply_symm_apply,
    Function.comp_def, List.length_map] at hc
  convert seq ((enter_run (p := p)) x xs acc) (seq ((body_run (p := p)) x (fields xs) acc) hc) using 1 <;>
    first | omega | simp [ready, field, List.reverse_append, List.map_reverse]

def exit_run (acc : List Wire) :
    Run ((ready (p := p)) [] acc) ((done (p := p)) (field Fraction.zero ++ acc.reverse)) (acc.length + 2) := by
  have hn : Run ((ready (p := p)) [] acc)
      (cfg (some (.inr .finish)) (initialState (p := p)) [] [] acc [] (empty (p := p))) 1 := by
    apply one
    simp only [ready, fields, List.flatMap_nil]
    loop_step
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq hn ((finish_run (p := p)) acc [])

theorem ready_eq_initList (xs : List Fraction) :
    (ready (p := p)) xs [] = initList (computer (p := p)) (fields xs) := by
  simp only [ready, initList, computer, cfg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

theorem done_eq_haltList (bits : List Wire) : (done (p := p)) bits = haltList (computer (p := p)) bits := by
  simp only [done, haltList, computer, cfg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k <;> rfl

end
end PhdThesisLean.RationalNormList.Machine
