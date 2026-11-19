import PhdThesisLean.RationalCountedFields

/-!
# Finite counted fraction traversal

The bounded count stage supplies unary marks followed by a delimiter and raw
payload bits. One pass consumes exactly that many valid fraction prefixes,
retaining their bits and the suffix. All failure paths clear every stack.
The core uses a decreasing potential; no arithmetic-cost premise is assumed.
-/
namespace PhdThesisLean.RationalCountedFields.Machine

open Computability Turing StateTransition
open RationalFractionPrefix (parse header body more prepend more_prepend)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

inductive Label
  | loadCount | next | sign | header (denominator : Bool) | body (denominator : Bool)
  | scanTail | reverse | rejectRemaining | rejectCount | rejectInput | rejectSaved
  deriving DecidableEq, Fintype

/-- Unbounded data here describe stacks; they are not machine registers. -/
structure Cursor where
  label : Label
  last : Bool
  remaining : ℕ
  count : ℕ
  input : List Bool
  saved : List (Option Bool)
  out : List (Option Bool)

def advance : Cursor → Sum (List (Option Bool)) Cursor
  | ⟨.loadCount, _, r, n, bs, s, o⟩ => .inr ⟨.rejectRemaining, false, r, n, bs, s, o⟩
  | ⟨.next, _, 0, n, bs, s, o⟩ => .inr ⟨.scanTail, false, 0, n, bs, none :: s, o⟩
  | ⟨.next, _, r + 1, n, bs, s, o⟩ => .inr ⟨.sign, false, r, n, bs, s, o⟩
  | ⟨.sign, _, r, n, [], s, o⟩ => .inr ⟨.rejectRemaining, false, r, n, [], s, o⟩
  | ⟨.sign, _, r, n, b :: bs, s, o⟩ => .inr ⟨.header false, !b, r, n, bs, some b :: s, o⟩
  | ⟨.header _, _, r, n, [], s, o⟩ => .inr ⟨.rejectRemaining, false, r, n, [], s, o⟩
  | ⟨.header d, a, r, n, true :: bs, s, o⟩ =>
      .inr ⟨.header d, a, r, n + 1, bs, some true :: s, o⟩
  | ⟨.header d, a, r, n, false :: bs, s, o⟩ =>
      .inr ⟨.body d, a, r, n, bs, some false :: s, o⟩
  | ⟨.body _, false, r, 0, bs, s, o⟩ => .inr ⟨.rejectRemaining, false, r, 0, bs, s, o⟩
  | ⟨.body false, true, r, 0, bs, s, o⟩ => .inr ⟨.header true, false, r, 0, bs, s, o⟩
  | ⟨.body true, true, r, 0, bs, s, o⟩ => .inr ⟨.next, false, r, 0, bs, none :: s, o⟩
  | ⟨.body _, _, r, n + 1, [], s, o⟩ => .inr ⟨.rejectRemaining, false, r, n, [], s, o⟩
  | ⟨.body d, _, r, n + 1, b :: bs, s, o⟩ => .inr ⟨.body d, b, r, n, bs, some b :: s, o⟩
  | ⟨.scanTail, _, r, n, [], s, o⟩ => .inr ⟨.reverse, false, r, n, [], s, o⟩
  | ⟨.scanTail, _, r, n, b :: bs, s, o⟩ => .inr ⟨.scanTail, false, r, n, bs, some b :: s, o⟩
  | ⟨.reverse, _, _, _, _, [], o⟩ => .inl o
  | ⟨.reverse, _, r, n, bs, b :: s, o⟩ => .inr ⟨.reverse, false, r, n, bs, s, b :: o⟩
  | ⟨.rejectRemaining, _, 0, n, bs, s, o⟩ => .inr ⟨.rejectCount, false, 0, n, bs, s, o⟩
  | ⟨.rejectRemaining, _, r + 1, n, bs, s, o⟩ => .inr ⟨.rejectRemaining, false, r, n, bs, s, o⟩
  | ⟨.rejectCount, _, r, 0, bs, s, o⟩ => .inr ⟨.rejectInput, false, r, 0, bs, s, o⟩
  | ⟨.rejectCount, _, r, n + 1, bs, s, o⟩ => .inr ⟨.rejectCount, false, r, n, bs, s, o⟩
  | ⟨.rejectInput, _, r, n, [], s, o⟩ => .inr ⟨.rejectSaved, false, r, n, [], s, o⟩
  | ⟨.rejectInput, _, r, n, _ :: bs, s, o⟩ => .inr ⟨.rejectInput, false, r, n, bs, s, o⟩
  | ⟨.rejectSaved, _, _, _, _, [], _⟩ => .inl []
  | ⟨.rejectSaved, _, r, n, bs, _ :: s, o⟩ => .inr ⟨.rejectSaved, false, r, n, bs, s, o⟩

def phaseWeight : Label → ℕ
  | .loadCount => 20 | .next => 5
  | .sign => 11 | .header false => 10 | .body false => 9
  | .header true => 8 | .body true => 7 | .scanTail => 3
  | .reverse => 2 | .rejectRemaining => 6 | .rejectCount => 5
  | .rejectInput => 4 | .rejectSaved => 1

def weight (c : Cursor) : ℕ :=
  12 * c.remaining + 4 * c.input.length + 2 * c.count +
    c.saved.length + phaseWeight c.label

theorem advance_decreases (c c' : Cursor) (h : advance c = .inr c') :
    weight c' < weight c := by
  rcases c with ⟨l, a, r, n, bs, s, o⟩
  cases l <;> cases r <;> cases n <;> cases bs <;> cases s <;> casesm* Bool <;>
    simp only [advance, reduceCtorEq] at h <;> cases h <;>
    simp [weight, phaseWeight] <;> omega

def meaning : Cursor → List (Option Bool)
  | ⟨.next, _, r, _, bs, s, _⟩ => render s (parseFields r bs)
  | ⟨.sign, _, _, _, [], _, _⟩ => []
  | ⟨.sign, _, r, n, b :: bs, s, _⟩ =>
      render s (finish r (prepend b (more false (header n (!b) bs))))
  | ⟨.header d, a, r, n, bs, s, _⟩ => render s (finish r (more d (header n a bs)))
  | ⟨.body d, a, r, n, bs, s, _⟩ => render s (finish r (more d (body n a bs)))
  | ⟨.scanTail, _, _, _, bs, s, _⟩ => s.reverse ++ bs.map some
  | ⟨.reverse, _, _, _, _, s, o⟩ => s.reverse ++ o
  | _ => []

def Ready (c : Cursor) : Prop :=
  c.label ≠ .loadCount ∧
  (c.label = .scanTail ∨ c.label = .reverse ∨ c.label = .rejectCount ∨
    c.label = .rejectInput ∨ c.label = .rejectSaved → c.remaining = 0) ∧
  (c.label = .next ∨ c.label = .sign ∨ c.label = .scanTail ∨ c.label = .reverse ∨ c.label = .rejectInput ∨
    c.label = .rejectSaved → c.count = 0) ∧
  (c.label = .reverse ∨ c.label = .rejectSaved → c.input = []) ∧
  (c.label ≠ .reverse → c.out = [])

theorem more_none (d : Bool) : more d none = none := by cases d <;> rfl

theorem more_true (r : RationalFractionPrefix.Result) : more true r = r := rfl

theorem more_empty (bits : List Bool) : more false (some ([], bits)) = header 0 false bits := by
  cases h : header 0 false bits <;> simp [more, h]

theorem meaning_advance (c : Cursor) (hc : Ready c) :
    meaning c = match advance c with | .inl bs => bs | .inr c' => meaning c' := by
  rcases c with ⟨l, a, r, n, bs, s, o⟩
  cases l <;> cases r <;> cases n <;> cases bs <;> cases s <;> casesm* Bool <;>
    simp_all [Ready, advance, meaning, header, body, more_prepend, render_finish_prepend,
      render_finish_empty, parseFields_zero, parseFields_succ, parse, more_none, more_true, more_empty,
      List.reverse_cons, List.append_assoc]
  all_goals simp [finish, render, wire, List.reverse_cons, List.append_assoc]

theorem ready_advance (c c' : Cursor) (hc : Ready c) (h : advance c = .inr c') :
    Ready c' := by
  rcases c with ⟨l, a, r, n, bs, s, o⟩
  cases l <;> cases r <;> cases n <;> cases bs <;> cases s <;> casesm* Bool <;>
    simp only [advance, reduceCtorEq] at h <;> cases h <;> simp_all [Ready]

inductive Stack | input | remaining | count | saved | output
  deriving DecidableEq, Fintype
abbrev State := Bool × Option (Option Bool)
def initial : State := (false, none)
def observe (s : State) (b : Option Bool) : State := (s.1, b.map some)
def observeCell (s : State) (b : Option (Option Bool)) : State := (s.1, b)
def held (s : State) : Bool := (s.2.getD none).getD false
def Alphabet : Stack → Type
  | .remaining | .count => Bool
  | .input | .saved | .output => Option Bool

def go (l : Label) (a : State → Bool) : TM2.Stmt Alphabet Label State :=
  .load (fun s => (a s, none)) (.goto fun _ => l)

def program : Label → TM2.Stmt Alphabet Label State
  | .loadCount => .pop .input observeCell <| .branch (fun s => s.2.isSome)
      (.branch (fun s => (s.2.getD none).isSome)
        (.push .remaining (fun _ => true) (go .loadCount (fun _ => false)))
        (go .next (fun _ => false)))
      (go .rejectRemaining (fun _ => false))
  | .next => .pop .remaining observe <| .branch (fun s => s.2.isSome)
      (go .sign (fun _ => false))
      (.push .saved (fun _ => none) (go .scanTail (fun _ => false)))
  | .sign => .pop .input observeCell <| .branch (fun s => s.2.isSome)
      (.push .saved (fun s => some (held s)) (go (.header false) (fun s => !held s)))
      (go .rejectRemaining (fun _ => false))
  | .header d => .pop .input observeCell <| .branch (fun s => s.2.isSome)
      (.push .saved (fun s => some (held s)) <| .branch held
        (.push .count (fun _ => true) (go (.header d) Prod.fst))
        (go (.body d) Prod.fst))
      (go .rejectRemaining (fun _ => false))
  | .body d => .pop .count observe <| .branch (fun s => s.2.isSome)
      (.pop .input observeCell <| .branch (fun s => s.2.isSome)
        (.push .saved (fun s => some (held s)) (go (.body d) held))
        (go .rejectRemaining (fun _ => false)))
      (.branch Prod.fst
        (if d then .push .saved (fun _ => none) (go .next (fun _ => false))
          else go (.header true) (fun _ => false))
        (go .rejectRemaining (fun _ => false)))
  | .scanTail => .pop .input observeCell <| .branch (fun s => s.2.isSome)
      (.push .saved (fun s => some (held s)) (go .scanTail (fun _ => false)))
      (go .reverse (fun _ => false))
  | .reverse => .pop .saved observeCell <| .branch (fun s => s.2.isSome)
      (.push .output (fun s => s.2.getD none) (go .reverse (fun _ => false)))
      (.load (fun _ => initial) .halt)
  | .rejectRemaining => .pop .remaining observe <| .branch (fun s => s.2.isSome)
      (go .rejectRemaining (fun _ => false)) (go .rejectCount (fun _ => false))
  | .rejectCount => .pop .count observe <| .branch (fun s => s.2.isSome)
      (go .rejectCount (fun _ => false)) (go .rejectInput (fun _ => false))
  | .rejectInput => .pop .input observeCell <| .branch (fun s => s.2.isSome)
      (go .rejectInput (fun _ => false)) (go .rejectSaved (fun _ => false))
  | .rejectSaved => .pop .saved observeCell <| .branch (fun s => s.2.isSome)
      (go .rejectSaved (fun _ => false)) (.load (fun _ => initial) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .loadCount
  σ := State
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := program

def contents (input : List (Option Bool)) (remaining count : List Bool) (saved out : List (Option Bool)) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .remaining => remaining | .count => count | .saved => saved | .output => out

def cfg (c : Cursor) : computer.Cfg :=
  ⟨some c.label, (c.last, none), contents (c.input.map some) (List.replicate c.remaining true) (List.replicate c.count true) c.saved c.out⟩

/-- Every abstract step is exactly one actual finite-machine transition. -/
theorem step_cfg (c : Cursor) (hc : Ready c) :
    computer.step (cfg c) = some (match advance c with
      | .inl bs => haltList computer bs | .inr c' => cfg c') := by
  rcases c with ⟨l, a, r, n, bs, s, o⟩
  cases l <;> cases r <;> cases n <;> cases bs <;> cases s <;> casesm* Bool <;>
    simp_all [Ready, advance, computer, FinTM2.step, cfg, program, go, contents,
      Alphabet, observe, observeCell, held, initial, List.replicate_succ,
      Function.update, haltList]
  all_goals funext k; cases k <;> rfl

/-- Total execution, including malformed inputs, full cleanup and state reset. -/
theorem run (c : Cursor) (hc : Ready c) :
    ∃ t, t ≤ weight c ∧
      (fun q => q.bind computer.step)^[t] (some (cfg c)) =
        some (haltList computer (meaning c)) := by
  generalize hw : weight c = w
  induction w using Nat.strong_induction_on generalizing c with
  | h w ih =>
      have hs := step_cfg c hc
      have hm := meaning_advance c hc
      cases he : advance c with
      | inl bs =>
          refine ⟨1, ?_, ?_⟩
          · rw [← hw]
            rcases c with ⟨l, a, r, n, bs, s, o⟩
            cases l <;> casesm* Bool <;> simp [weight, phaseWeight]
          · simpa [he, Function.iterate_one, hm] using hs
      | inr c' =>
          have hlt := advance_decreases c c' he
          obtain ⟨t, ht, hr⟩ := ih (weight c') (by omega) c'
            (ready_advance c c' hc he) rfl
          refine ⟨t + 1, by omega, ?_⟩
          rw [Function.iterate_succ_apply, Option.bind_some, hs]
          simpa [he, hm] using hr

def start (n : ℕ) (bits : List Bool) : Cursor := ⟨.next, false, n, 0, bits, [], []⟩

def input (n : ℕ) (bits : List Bool) : List (Option Bool) :=
  List.replicate n (some true) ++ none :: bits.map some

def loadCfg (n k : ℕ) (bits : List Bool) : computer.Cfg :=
  ⟨some .loadCount, initial,
    contents (input n bits) (List.replicate k true) [] [] []⟩

theorem step_load_succ (n k : ℕ) (bits : List Bool) :
    computer.step (loadCfg (n+1) k bits) = some (loadCfg n (k+1) bits) := by
  simp [computer, FinTM2.step, loadCfg, input, program, go, contents, Alphabet,
    observeCell, initial, List.replicate_succ, Function.update]
  funext j; cases j <;> rfl

theorem step_load_zero (k : ℕ) (bits : List Bool) :
    computer.step (loadCfg 0 k bits) = some (cfg (start k bits)) := by
  simp [computer, FinTM2.step, loadCfg, input, program, go, contents, Alphabet,
    observeCell, initial, cfg, start, Function.update]
  funext j; cases j <;> rfl

theorem load_run (n k : ℕ) (bits : List Bool) :
    (fun q => q.bind computer.step)^[n+1] (some (loadCfg n k bits)) =
      some (cfg (start (n+k) bits)) := by
  induction n generalizing k with
  | zero => simpa using step_load_zero k bits
  | succ n ih =>
      rw [Function.iterate_succ_apply, Option.bind_some, step_load_succ, ih]
      congr 3; omega

theorem init_eq (n : ℕ) (bits : List Bool) :
    initList computer (input n bits) = loadCfg n 0 bits := by
  unfold initList loadCfg
  congr
  funext k; cases k <;> rfl

/-- A complete counted traversal, including input loading and failure cleanup. -/
noncomputable def outputsInTime (n : ℕ) (bits : List Bool) :
    TM2OutputsInTime computer (input n bits) (some (output n bits))
      (13 * (input n bits).length + 6) := by
  have h := run (start n bits) (by simp [Ready, start])
  let t := Classical.choose h
  have ht := Classical.choose_spec h
  refine { steps := t+(n+1), evals_in_steps := ?_, steps_le_m := ?_ }
  · change (fun q => q.bind computer.step)^[t+(n+1)]
      (some (initList computer (input n bits))) = some (haltList computer (output n bits))
    rw [init_eq, Function.iterate_add_apply, load_run]
    simpa [start, meaning, output, t] using ht.2
  · have ht' : t ≤ 12*n + 4*bits.length + 5 := ht.1
    simp only [input, List.length_append, List.length_replicate,
      List.length_cons, List.length_map]
    omega

/-- Empty is the rejection marker produced by the bounded count stage. -/
noncomputable def emptyOutputsInTime :
    TM2OutputsInTime computer [] (some []) 6 := by
  refine { steps := 5, evals_in_steps := ?_, steps_le_m := by omega }
  simp [computer, FinTM2.step, initList, haltList, program, go, Alphabet,
    observeCell, observe, initial, Function.iterate_succ_apply, Function.update,
    flip, TM2.step, TM2.stepAux]
  funext k; cases k <;> rfl

#print axioms run
#print axioms outputsInTime
#print axioms emptyOutputsInTime

end PhdThesisLean.RationalCountedFields.Machine
