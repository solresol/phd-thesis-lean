import PhdThesisLean.BinarySubtraction

/-!
# A linear-time binary subtraction machine

A three-stack finite TM2 scans aligned binary digits with a single borrow bit.
The reverse pass discards an underflow result, or removes high zero bits while
restoring the canonical difference. Both passes, exhaustion tests and cleanup
take exactly `2L+2` transitions in the complete aligned-pair input length `L`.
No arithmetic-cost or runtime hypothesis is supplied.
-/
namespace PhdThesisLean.BinarySubtraction.Machine

open Computability Turing StateTransition
open LeanNPHardness.MachinePrimitives

set_option backward.isDefEq.respectTransparency false

inductive Stack
  | input | work | output
  deriving DecidableEq, Fintype
inductive Label
  | scan | restore
  deriving DecidableEq, Fintype
structure State where
  borrow : Bool
  seen : Bool
  pair : Option Symbol
  bit : Option Bool
  deriving DecidableEq, Fintype

def state (borrow seen : Bool) : State := ⟨borrow, seen, none, none⟩
def initial : State := state false false
def Alphabet : Stack → Type
  | .input => Symbol
  | _ => Bool

def observed (s : State) : Bool × Bool :=
  let p := s.pair.getD (none, none)
  subStep s.borrow (p.1.getD false) (p.2.getD false)

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input (fun s p => {s with pair := p}) <|
      .branch (fun s => s.pair.isSome)
        (.push .work (fun s => (observed s).1) <|
          .load (fun s => state (observed s).2 false) (.goto fun _ => .scan))
        (.load (fun s => state s.borrow false) (.goto fun _ => .restore))
  | .restore => .pop .work (fun s b => {s with bit := b}) <|
      .branch (fun s => s.bit.isSome)
        (.branch (fun s => !s.borrow && (s.seen || s.bit.getD false))
          (.push .output (fun s => s.bit.getD false) <|
            .load (fun _ => state false true) (.goto fun _ => .restore))
          (.load (fun s => state s.borrow s.seen) (.goto fun _ => .restore)))
        (.load (fun _ => initial) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype Symbol)
  m := program

def contents (input : List Symbol) (work output : List Bool) :
    (k : Stack) → List (Alphabet k)
  | .input => input
  | .work => work
  | .output => output

def cfg (l : Option Label) (s : State) (input : List Symbol) (work output : List Bool) :
    computer.Cfg := ⟨l, s, contents input work output⟩

private theorem scan_cons (borrow : Bool) (p : Symbol) (ps : List Symbol) (work : List Bool) :
    computer.step (cfg (some .scan) (state borrow false) (p :: ps) work []) =
      some (cfg (some .scan) (state (subStep borrow (p.1.getD false) (p.2.getD false)).2 false)
        ps ((subStep borrow (p.1.getD false) (p.2.getD false)).1 :: work) []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, observed, Function.update]
  funext k; cases k <;> rfl

private theorem scan_nil (borrow : Bool) (work : List Bool) :
    computer.step (cfg (some .scan) (state borrow false) [] work []) =
      some (cfg (some .restore) (state borrow false) [] work []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state]

/-- One transition per source symbol plus the exhaustion test. -/
theorem scan_run (borrow : Bool) (ps : List Symbol) (work : List Bool) :
    (fun q => q.bind computer.step)^[ps.length + 1]
      (some (cfg (some .scan) (state borrow false) ps work [])) =
    some (cfg (some .restore) (state (subtract borrow ps).2 false) []
      ((subtract borrow ps).1.reverse ++ work) []) := by
  induction ps generalizing borrow work with
  | nil => simpa [subtract] using scan_nil borrow work
  | cons p ps ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, scan_cons, ih]
      simp [subtract, List.reverse_cons, List.append_assoc]

private theorem restore_nil (borrow seen : Bool) (output : List Bool) :
    computer.step (cfg (some .restore) (state borrow seen) [] [] output) =
      some (cfg none initial [] [] output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state]

private theorem drop_cons (b : Bool) (bs : List Bool) :
    computer.step (cfg (some .restore) (state true false) [] (b :: bs) []) =
      some (cfg (some .restore) (state true false) [] bs []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, Function.update]
  funext k; cases k <;> rfl

/-- Underflow is saturated to zero and the discarded bits are all charged. -/
theorem drop_run (bs : List Bool) :
    (fun q => q.bind computer.step)^[bs.length + 1]
      (some (cfg (some .restore) (state true false) [] bs [])) =
    some (cfg none initial [] [] []) := by
  induction bs with
  | nil => simpa using restore_nil true false []
  | cons b bs ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, drop_cons, ih]

private theorem restore_cons (b seen : Bool) (bs output : List Bool) :
    computer.step (cfg (some .restore) (state false seen) [] (b :: bs) output) =
      some (cfg (some .restore) (state false (b || seen)) [] bs
        (if b || seen then b :: output else output)) := by
  cases b <;> cases seen <;>
    simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, Function.update] <;>
    funext k <;> cases k <;> rfl

private theorem restore_encode_cons (b : Bool) (bs : List Bool) (n : ℕ) :
    computer.step (cfg (some .restore) (state false (decide (n ≠ 0))) [] (b :: bs)
      (encodeNat n)) =
      some (cfg (some .restore) (state false (decide (b.toNat + 2 * n ≠ 0))) [] bs
        (encodeNat (b.toNat + 2 * n))) := by
  rw [restore_cons, ← pushBit_encode]
  by_cases hn : n = 0
  · subst n; cases b <;> rfl
  · simp [pushBit, encode_isEmpty, hn]

/-- Reverse while dropping only high zeros; zero stays the empty word. -/
theorem restore_run (bs : List Bool) (n : ℕ) :
    (fun q => q.bind computer.step)^[bs.length + 1]
      (some (cfg (some .restore) (state false (decide (n ≠ 0))) [] bs (encodeNat n))) =
    some (cfg none initial [] [] (encodeNat (restoreValue bs n))) := by
  induction bs generalizing n with
  | nil => simpa [restoreValue] using restore_nil false (decide (n ≠ 0)) (encodeNat n)
  | cons b bs ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, restore_encode_cons, ih]
      rfl

/-- Exact execution, including both exhaustion transitions and state reset. -/
theorem run_raw (ps : List Symbol) :
    (fun q => q.bind computer.step)^[2 * ps.length + 2]
      (some (cfg (some .scan) initial ps [] [])) =
    some (cfg none initial [] []
      (encodeNat (if (subtract false ps).2 then 0 else value (subtract false ps).1))) := by
  rw [show 2 * ps.length + 2 = (ps.length + 1) + (ps.length + 1) by omega,
    Function.iterate_add_apply]
  change (fun q => q.bind computer.step)^[ps.length + 1]
    ((fun q => q.bind computer.step)^[ps.length + 1]
      (some (cfg (some .scan) (state false false) ps [] []))) = _
  rw [scan_run, List.append_nil]
  have hl : (subtract false ps).1.reverse.length = ps.length := by simp
  cases (subtract false ps).2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hr := restore_run (subtract false ps).1.reverse 0
    simpa only [hl, restoreValue_reverse, show encodeNat 0 = [] from rfl,
      show decide (0 ≠ 0) = false from rfl] using hr
  · simp only [↓reduceIte]
    simpa only [hl, show encodeNat 0 = [] from rfl] using drop_run (subtract false ps).1.reverse

theorem run (m n : ℕ) :
    (fun q => q.bind computer.step)^[2 * (encoding.encode (m, n)).length + 2]
      (some (cfg (some .scan) initial (encoding.encode (m, n)) [] [])) =
    some (cfg none initial [] [] (encodeNat (m - n))) := by
  simpa only [subtract_encode] using run_raw (encoding.encode (m, n))

private theorem init_eq (ps : List Symbol) :
    initList computer ps = cfg (some .scan) initial ps [] [] := by
  unfold initList cfg; congr; funext k; cases k <;> rfl

private theorem halt_eq (bs : List Bool) :
    haltList computer bs = cfg none initial [] [] bs := by
  unfold haltList cfg; congr; funext k; cases k <;> rfl

/-- Actual linear runtime in all aligned-pair input symbols. -/
def outputsInTime (x : ℕ × ℕ) :
    TM2OutputsInTime computer (encoding.encode x) (some (encodeNat (x.1 - x.2)))
      (2 * (encoding.encode x).length + 2) where
  steps := 2 * (encoding.encode x).length + 2
  evals_in_steps := by
    change (fun q => q.bind computer.step)^[_] (some (initList computer (encoding.encode x))) =
      some (haltList computer (encodeNat (x.1 - x.2)))
    rw [init_eq, halt_eq]
    exact run x.1 x.2
  steps_le_m := le_rfl

noncomputable def computableInPolyTime :
    LeanNPHardness.TM2ComputableInPolyTime encoding LeanNPHardness.finEncodingNatBool
      (fun x => x.1 - x.2) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun x := by
    simpa [LeanNPHardness.finEncodingNatBool, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using outputsInTime x

#print axioms scan_run
#print axioms drop_run
#print axioms restore_run
#print axioms run
#print axioms outputsInTime
#print axioms computableInPolyTime

end PhdThesisLean.BinarySubtraction.Machine
