import PhdThesisLean.RationalFractionValidity

/-!
# Linear-time validity checking on arbitrary fraction bit strings

A concrete finite three-stack TM2 decides exactly the `Fraction.encode` image
in at most `3L+10` steps on every Boolean input of length `L`. Frame counts are
stack contents, never unbounded control state. Rejection, all empty-stack tests,
input/count cleanup and the final Boolean output are included in the bound.
-/

namespace PhdThesisLean.RationalFractionValidity.Machine

open Computability Turing StateTransition
open RationalVerifierBounds

set_option backward.isDefEq.respectTransparency false

inductive Label
  | sign | header (denominator : Bool) | body (denominator : Bool) | finish
  | drainCount (answer : Bool) | drainInput (answer : Bool)
  deriving DecidableEq, Fintype

/-- Mathematical description of stack contents, not the finite control type. -/
structure Cursor where
  label : Label
  last : Bool
  count : ℕ
  input : List Bool

def advance : Cursor → Sum Bool Cursor
  | ⟨.sign, _, n, []⟩ => .inr ⟨.drainCount false, false, n, []⟩
  | ⟨.sign, _, n, b :: bs⟩ => .inr ⟨.header false, !b, n, bs⟩
  | ⟨.header _, _, n, []⟩ => .inr ⟨.drainCount false, false, n, []⟩
  | ⟨.header d, a, n, true :: bs⟩ => .inr ⟨.header d, a, n + 1, bs⟩
  | ⟨.header d, a, n, false :: bs⟩ => .inr ⟨.body d, a, n, bs⟩
  | ⟨.body _, false, 0, bs⟩ => .inr ⟨.drainCount false, false, 0, bs⟩
  | ⟨.body false, true, 0, bs⟩ => .inr ⟨.header true, false, 0, bs⟩
  | ⟨.body true, true, 0, bs⟩ => .inr ⟨.finish, false, 0, bs⟩
  | ⟨.body _, _, n + 1, []⟩ => .inr ⟨.drainCount false, false, n, []⟩
  | ⟨.body d, _, n + 1, b :: bs⟩ => .inr ⟨.body d, b, n, bs⟩
  | ⟨.finish, _, n, []⟩ => .inr ⟨.drainCount true, false, n, []⟩
  | ⟨.finish, _, n, _ :: bs⟩ => .inr ⟨.drainCount false, false, n, bs⟩
  | ⟨.drainCount b, _, 0, bs⟩ => .inr ⟨.drainInput b, false, 0, bs⟩
  | ⟨.drainCount b, _, n + 1, bs⟩ => .inr ⟨.drainCount b, false, n, bs⟩
  | ⟨.drainInput b, _, _, []⟩ => .inl b
  | ⟨.drainInput b, _, n, _ :: bs⟩ => .inr ⟨.drainInput b, false, n, bs⟩

def phaseWeight : Label → ℕ
  | .sign => 10
  | .header false => 9
  | .body false => 8
  | .header true => 7
  | .body true => 6
  | .finish => 5
  | .drainCount _ => 2
  | .drainInput _ => 1

def weight (c : Cursor) : ℕ := 3 * c.input.length + 2 * c.count + phaseWeight c.label

theorem advance_decreases (c c' : Cursor) (h : advance c = .inr c') :
    weight c' < weight c := by
  rcases c with ⟨l, a, n, bs⟩
  cases l <;> cases n <;> cases bs <;> casesm* Bool <;>
    simp only [advance, reduceCtorEq] at h <;> cases h <;>
    simp [weight, phaseWeight] <;> omega

/-- Parser meaning of an arbitrary intermediate configuration. -/
def meaning : Cursor → Bool
  | ⟨.sign, _, _, []⟩ => false
  | ⟨.sign, _, n, b :: bs⟩ => continueField false (readHeader n (!b) bs)
  | ⟨.header d, a, n, bs⟩ => continueField d (readHeader n a bs)
  | ⟨.body d, a, n, bs⟩ => continueField d (readBody n a bs)
  | ⟨.finish, _, _, bs⟩ => bs.isEmpty
  | ⟨.drainCount b, _, _, _⟩ => b
  | ⟨.drainInput b, _, _, _⟩ => b

theorem meaning_advance (c : Cursor) :
    meaning c = match advance c with | .inl b => b | .inr c' => meaning c' := by
  rcases c with ⟨l, a, n, bs⟩
  cases l <;> cases n <;> cases bs <;> casesm* Bool <;>
    simp [advance, meaning, readHeader, readBody, continueField, Option.any]
  all_goals split <;> simp_all

inductive Stack
  | input | count | output
  deriving DecidableEq, Fintype

abbrev State := Bool × Option Bool
def initial : State := (false, none)
def observe (s : State) (b : Option Bool) : State := (s.1, b)
def held (s : State) : Bool := s.2.getD false
def Alphabet (_ : Stack) : Type := Bool

def go (label : Label) (a : State → Bool) : TM2.Stmt Alphabet Label State :=
  .load (fun s => (a s, none)) (.goto fun _ => label)

def program : Label → TM2.Stmt Alphabet Label State
  | .sign =>
      .pop .input observe <|
        .branch (fun s => s.2.isSome)
          (go (.header false) (fun s => !held s))
          (go (.drainCount false) (fun _ => false))
  | .header d =>
      .pop .input observe <|
        .branch (fun s => s.2.isSome)
          (.branch held
            (.push .count (fun _ => true) (go (.header d) Prod.fst))
            (go (.body d) Prod.fst))
          (go (.drainCount false) (fun _ => false))
  | .body d =>
      .pop .count observe <|
        .branch (fun s => s.2.isSome)
          (.pop .input observe <|
            .branch (fun s => s.2.isSome)
              (go (.body d) held)
              (go (.drainCount false) (fun _ => false)))
          (.branch Prod.fst
            (go (if d then .finish else .header true) (fun _ => false))
            (go (.drainCount false) (fun _ => false)))
  | .finish =>
      .pop .input observe <|
        .branch (fun s => s.2.isSome)
          (go (.drainCount false) (fun _ => false))
          (go (.drainCount true) (fun _ => false))
  | .drainCount b =>
      .pop .count observe <|
        .branch (fun s => s.2.isSome)
          (go (.drainCount b) (fun _ => false))
          (go (.drainInput b) (fun _ => false))
  | .drainInput b =>
      .pop .input observe <|
        .branch (fun s => s.2.isSome)
          (go (.drainInput b) (fun _ => false))
          (.push .output (fun _ => b) (.load (fun _ => initial) .halt))

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .sign
  σ := State
  initialState := initial
  Γk₀Fin := Bool.fintype
  m := program

def contents (input count output : List Bool) : (k : Stack) → List (Alphabet k)
  | .input => input
  | .count => count
  | .output => output

def cfg (c : Cursor) : computer.Cfg :=
  ⟨some c.label, (c.last, none), contents c.input (List.replicate c.count true) []⟩

/-- The only extra invariant: the count stack has been cleared before halting. -/
def Ready (c : Cursor) : Prop := ∀ b, c.label = .drainInput b → c.count = 0

theorem ready_advance (c c' : Cursor) (hc : Ready c) (h : advance c = .inr c') :
    Ready c' := by
  rcases c with ⟨l, a, n, bs⟩
  cases l <;> cases n <;> cases bs <;> casesm* Bool <;>
    simp only [advance, reduceCtorEq] at h <;> cases h <;> simp_all [Ready]

/-- One abstract transition is exactly one concrete TM2 transition. -/
theorem step_cfg (c : Cursor) (hc : Ready c) :
    computer.step (cfg c) = some (match advance c with
      | .inl b => haltList computer [b]
      | .inr c' => cfg c') := by
  rcases c with ⟨l, a, n, bs⟩
  cases l <;> cases n <;> cases bs <;> casesm* Bool <;>
    simp_all [Ready, advance, computer, FinTM2.step, cfg, program, go, contents,
      Alphabet, observe, held, initial, List.replicate_succ, Function.update, haltList]
  all_goals funext k; cases k <;> rfl

/-- Every input, including every rejection path, halts with all private stacks
empty and control reset within the decreasing bit-length potential. -/
theorem run (c : Cursor) (hc : Ready c) :
    ∃ t, t ≤ weight c ∧
      (fun q => q.bind computer.step)^[t] (some (cfg c)) =
        some (haltList computer [meaning c]) := by
  generalize hw : weight c = w
  induction w using Nat.strong_induction_on generalizing c with
  | h w ih =>
      have hs := step_cfg c hc
      have hm := meaning_advance c
      cases he : advance c with
      | inl b =>
          refine ⟨1, ?_, ?_⟩
          · rw [← hw]
            rcases c with ⟨l, a, n, bs⟩
            cases l <;> casesm* Bool <;> simp [weight, phaseWeight]
          · simpa [he, Function.iterate_one, hm] using hs
      | inr c' =>
          have hlt := advance_decreases c c' he
          obtain ⟨t, ht, hr⟩ := ih (weight c') (by omega) c'
            (ready_advance c c' hc he) rfl
          refine ⟨t + 1, by omega, ?_⟩
          rw [Function.iterate_succ_apply, Option.bind_some, hs]
          simpa [he, hm] using hr

def start (bits : List Bool) : Cursor := ⟨.sign, false, 0, bits⟩

private theorem init_eq (bits : List Bool) : initList computer bits = cfg (start bits) := by
  unfold initList cfg start
  congr
  funext k
  cases k <;> rfl

/-- Total, actual runtime bound on arbitrary raw Boolean strings. -/
noncomputable def outputsInTime (bits : List Bool) :
    TM2OutputsInTime computer bits (some [valid bits]) (3 * bits.length + 10) := by
  have h := run (start bits) (by simp [Ready, start])
  let t := Classical.choose h
  have ht := Classical.choose_spec h
  refine { steps := t, evals_in_steps := ?_, steps_le_m := ?_ }
  · change (fun q => q.bind computer.step)^[t] (some (initList computer bits)) =
      some (haltList computer [valid bits])
    rw [init_eq]
    have hm : meaning (start bits) = valid bits := by cases bits <;> rfl
    simpa [hm, t] using ht.2
  · exact ht.1

noncomputable def computableInPolyTime :
    LeanNPHardness.TM2ComputableInPolyTime
      LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding
      LeanNPHardness.finEncodingBoolBool valid where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 10
  outputsFun bits := by
    simpa [LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding,
      LeanNPHardness.finEncodingBoolBool, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using outputsInTime bits

/-- The machine accepts exactly the existing fraction encoding, with no
well-formed-input premise and no primitive-parser runtime assumption. -/
theorem accepts_iff (bits : List Bool) :
    valid bits = true ↔ ∃ x : Fraction, x.encode = bits := valid_iff bits

#print axioms computableInPolyTime
#print axioms outputsInTime
#print axioms accepts_iff

end PhdThesisLean.RationalFractionValidity.Machine
