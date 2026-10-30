import LeanNPHardness.BinaryConvertNat
import LeanNPHardness.MachineRun

/-!
# Binary long division by a fixed divisor

A finite three-stack TM2 reads mathlib's least-significant-bit-first encoding,
reverses it, and performs binary long division. The remainder is in `Fin p`:
for fixed `p` each digit transition is a finite lookup, not an uncharged
operation on an unbounded integer. Leading quotient zeros are suppressed.
This is a bit-machine primitive for the rational regression verifier; it does
not assert a runtime for the complete verifier or for repeated valuation.
-/

namespace PhdThesisLean.FixedDivisorBinary

open Computability Turing StateTransition
open LeanNPHardness.MachinePrimitives

set_option backward.isDefEq.respectTransparency false

/-- Value of the next most-significant-first bit after prefix `n`. -/
def next (n : ℕ) (b : Bool) : ℕ := 2 * n + b.toNat

/-- Read a big-endian suffix after the already read prefix. -/
def readBE : ℕ → List Bool → ℕ
  | n, [] => n
  | n, b :: bits => readBE (next n b) bits

theorem readBE_append (n : ℕ) (xs ys : List Bool) :
    readBE n (xs ++ ys) = readBE (readBE n xs) ys := by
  induction xs generalizing n with
  | nil => rfl
  | cons b xs ih => exact ih (next n b)

private theorem readBE_encodePosNum (n : PosNum) :
    readBE 0 (encodePosNum n).reverse = n := by
  induction n with
  | one => rfl
  | bit0 n ih => simp [encodePosNum, List.reverse_cons, readBE_append, readBE, next, ih, two_mul]
  | bit1 n ih => simp [encodePosNum, List.reverse_cons, readBE_append, readBE, next, ih, two_mul]

theorem readBE_encodeNat (n : ℕ) : readBE 0 (encodeNat n).reverse = n := by
  have h (m : Num) : readBE 0 (encodeNum m).reverse = (m : ℕ) := by
    cases m with
    | zero => rfl
    | pos m => exact readBE_encodePosNum m
  simpa [encodeNat] using h (n : Num)

variable (p : ℕ) (hp : 0 < p)

/-- The single quotient bit is a comparison against the fixed divisor. -/
def digit (r : Fin p) (b : Bool) : Bool := decide (p ≤ next r.val b)

/-- Remainder transition on a finite state space. -/
def remainder (r : Fin p) (b : Bool) : Fin p :=
  ⟨next r.val b % p, Nat.mod_lt _ hp⟩

theorem digit_div (r : Fin p) (b : Bool) :
    next r.val b / p = (digit p r b).toNat := by
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  have hlt : next r.val b < 2 * p := by dsimp [next]; omega
  by_cases h : p ≤ next r.val b
  · have hlo : 1 * p ≤ next r.val b := by omega
    have hhi : next r.val b < (1 + 1) * p := by omega
    rw [Nat.div_eq_of_lt_le hlo hhi]
    simp [digit, h]
  · rw [Nat.div_eq_of_lt (by omega)]
    simp [digit, h]

include hp in
theorem next_div (n : ℕ) (b : Bool) :
    next n b / p = 2 * (n / p) + next (n % p) b / p := by
  have he : next n b = next (n % p) b + p * (2 * (n / p)) := by
    have hn := Nat.mod_add_div n p
    dsimp [next]
    nlinarith
  rw [he, Nat.add_mul_div_left _ _ hp]
  omega

theorem next_mod (n : ℕ) (b : Bool) :
    next n b % p = next (n % p) b % p := by
  simp [next, Nat.add_mod, Nat.mul_mod]

/-- The quotient prefix remains in canonical little-endian encoding. -/
theorem encodeNat_next (q : ℕ) (b : Bool) :
    encodeNat (next q b) =
      if q ≠ 0 ∨ b = true then b :: encodeNat q else [] := by
  cases b with
  | false =>
      by_cases hq : q = 0
      · subst q; rfl
      · simpa [next, hq] using LeanNPHardness.BinaryConvert.encodeNat_even q (by omega)
  | true => simpa [next] using LeanNPHardness.BinaryConvert.encodeNat_odd q

inductive Stack
  | input | work | output
  deriving DecidableEq, Fintype

inductive Label
  | reverse | scan | finish
  deriving DecidableEq, Fintype

/-- No unbounded numeric register: the divisor is fixed in the program. -/
structure State (p : ℕ) where
  rem : Fin p
  bit : Option Bool
  started : Bool
  deriving DecidableEq, Fintype

def initialState : State p := ⟨⟨0, hp⟩, none, false⟩

def Alphabet (_ : Stack) : Type := Bool

def observe (s : State p) (b : Option Bool) : State p := { s with bit := b }

def held (s : State p) : Bool := s.bit.getD false

def outputBit (s : State p) : Bool := digit p s.rem (held p s)

def emit (s : State p) : Bool := s.started || outputBit p s

def advance (s : State p) : State p :=
  ⟨remainder p hp s.rem (held p s), s.bit, emit p s⟩

/-- Two linear scans and a final state reset. Every label contains a fixed
number of stack operations; arithmetic in the control has finite domain. -/
def program : Label → TM2.Stmt Alphabet Label (State p)
  | .reverse =>
      .pop .input (observe p) <|
        .branch (fun s => s.bit.isSome)
          (.push .work (held p) (.goto fun _ => .reverse))
          (.load (fun _ => initialState p hp) (.goto fun _ => .scan))
  | .scan =>
      .pop .work (observe p) <|
        .branch (fun s => s.bit.isSome)
          (.branch (emit p)
            (.push .output (outputBit p) <|
              .load (advance p hp) (.goto fun _ => .scan))
            (.load (advance p hp) (.goto fun _ => .scan)))
          (.goto fun _ => .finish)
  | .finish => .load (fun _ => initialState p hp) .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .reverse
  σ := State p
  initialState := initialState p hp
  Γk₀Fin := Bool.fintype
  m := program p hp

def stackContents (input work output : List Bool) : (k : Stack) → List (Alphabet k)
  | .input => input
  | .work => work
  | .output => output

def cfg (label : Option Label) (s : State p) (input work output : List Bool) :
    (computer p hp).Cfg where
  l := label
  var := s
  stk := stackContents input work output

/-- Semantic invariant: remainder, nonzero quotient flag, and a remembered bit. -/
def stateFor (n : ℕ) (last : Option Bool) : State p :=
  ⟨⟨n % p, Nat.mod_lt _ hp⟩, last, decide (n / p ≠ 0)⟩

theorem advance_stateFor (n : ℕ) (b : Bool) :
    advance p hp (stateFor p hp n (some b)) = stateFor p hp (next n b) (some b) := by
  have hd := digit_div p ⟨n % p, Nat.mod_lt _ hp⟩ b
  have hq := next_div p hp n b
  have hm := next_mod p n b
  have hflag :
      (decide (n / p ≠ 0) || digit p ⟨n % p, Nat.mod_lt _ hp⟩ b) =
        decide (next n b / p ≠ 0) := by
    cases hdigit : digit p ⟨n % p, Nat.mod_lt _ hp⟩ b <;>
      simp_all
  simp only [advance, stateFor, remainder, emit, outputBit, held, Option.getD_some]
  congr 1
  · exact Fin.ext hm.symm

theorem quotient_step (n : ℕ) (b : Bool) :
    (if emit p (stateFor p hp n (some b)) then
      outputBit p (stateFor p hp n (some b)) :: encodeNat (n / p)
    else encodeNat (n / p)) = encodeNat (next n b / p) := by
  have hd := digit_div p ⟨n % p, Nat.mod_lt _ hp⟩ b
  have hq := next_div p hp n b
  rw [hd] at hq
  rw [hq, ← next, encodeNat_next]
  simp only [emit, stateFor, outputBit, held, Option.getD_some]
  cases hq0 : n / p with
  | zero => cases hbit : digit p ⟨n % p, Nat.mod_lt _ hp⟩ b <;> simp [show encodeNat 0 = [] from rfl]
  | succ q => simp

private theorem step_reverse_nil (s : State p) (work output : List Bool) :
    (computer p hp).step (cfg p hp (some .reverse) s [] work output) =
      some (cfg p hp (some .scan) (initialState p hp) [] work output) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe, Function.update]

private theorem step_reverse_cons (s : State p) (b : Bool) (input work output : List Bool) :
    (computer p hp).step (cfg p hp (some .reverse) s (b :: input) work output) =
      some (cfg p hp (some .reverse) (observe p s (some b)) input (b :: work) output) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe, held, Function.update]
  funext k
  cases k <;> rfl

private theorem step_scan_nil (n : ℕ) (last : Option Bool) (output : List Bool) :
    (computer p hp).step (cfg p hp (some .scan) (stateFor p hp n last) [] [] output) =
      some (cfg p hp (some .finish) (stateFor p hp n none) [] [] output) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe, stateFor, Function.update]

private theorem step_scan_cons (n : ℕ) (last : Option Bool) (b : Bool)
    (bits suffix : List Bool) :
    (computer p hp).step
      (cfg p hp (some .scan) (stateFor p hp n last) [] (b :: bits)
        (encodeNat (n / p) ++ suffix)) =
      some (cfg p hp (some .scan) (stateFor p hp (next n b) (some b)) [] bits
        (encodeNat (next n b / p) ++ suffix)) := by
  have hs := advance_stateFor p hp n b
  have hq := quotient_step p hp n b
  have he : observe p (stateFor p hp n last) (some b) = stateFor p hp n (some b) := rfl
  have hbit : (stateFor p hp n (some b)).bit.isSome = true := rfl
  simp only [computer, FinTM2.step, TM2.step, cfg, program, TM2.stepAux,
    Alphabet, stackContents, List.head?_cons, List.tail_cons, he, hbit, Bool.cond_true]
  by_cases hh : emit p (stateFor p hp n (some b)) = true
  · simp only [hh, Bool.cond_true] at hq ⊢
    rw [hs]
    simp only [↓reduceIte] at hq
    congr 2
    funext k
    cases k <;> simp [Function.update, stackContents, ← hq]
  · have hf : emit p (stateFor p hp n (some b)) = false := by simpa using hh
    simp only [hf, Bool.cond_false] at hq ⊢
    rw [hs]
    simp only [Bool.false_eq_true, ↓reduceIte] at hq
    congr 2
    funext k
    cases k <;> simp [Function.update, stackContents, ← hq]

/-- Reverse an arbitrary input word, charging every pop and the empty check. -/
theorem reverse_run (input work output : List Bool) (s : State p) :
    (fun c => c.bind (computer p hp).step)^[input.length + 1]
      (some (cfg p hp (some .reverse) s input work output)) =
    some (cfg p hp (some .scan) (initialState p hp) []
      (input.reverse ++ work) output) := by
  induction input generalizing work s with
  | nil => simpa using step_reverse_nil p hp s work output
  | cons b input ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, Option.bind_some, step_reverse_cons]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (b :: work) (observe p s (some b))

/-- The complete long-division pass retains the actual remainder in finite
control, produces the canonical quotient, and preserves an output suffix. -/
theorem scan_run (bits suffix : List Bool) (n : ℕ) (last : Option Bool) :
    (fun c => c.bind (computer p hp).step)^[bits.length + 1]
      (some (cfg p hp (some .scan) (stateFor p hp n last) [] bits
        (encodeNat (n / p) ++ suffix))) =
    some (cfg p hp (some .finish) (stateFor p hp (readBE n bits) none) [] []
      (encodeNat (readBE n bits / p) ++ suffix)) := by
  induction bits generalizing n last with
  | nil => simpa [readBE] using step_scan_nil p hp n last (encodeNat (n / p) ++ suffix)
  | cons b bits ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, Option.bind_some, step_scan_cons]
      exact ih (next n b) (some b)

private theorem step_finish (s : State p) (output : List Bool) :
    (computer p hp).step (cfg p hp (some .finish) s [] [] output) =
      some (cfg p hp none (initialState p hp) [] [] output) := rfl

private theorem initial_eq : initialState p hp = stateFor p hp 0 none := by
  simp [initialState, stateFor]

/-- From the actual binary input alone to quotient and remainder, in exactly
`2s + 2` TM2 transitions. There is no unary expansion of the input integer. -/
theorem division_pass (n : ℕ) :
    (fun c => c.bind (computer p hp).step)^[2 * (encodeNat n).length + 2]
      (some (cfg p hp (some .reverse) (initialState p hp) (encodeNat n) [] [])) =
    some (cfg p hp (some .finish) (stateFor p hp n none) [] [] (encodeNat (n / p))) := by
  have hrev := reverse_run p hp (encodeNat n) [] [] (initialState p hp)
  have hscan := scan_run p hp (encodeNat n).reverse [] 0 none
  rw [show 2 * (encodeNat n).length + 2 =
    ((encodeNat n).reverse.length + 1) + ((encodeNat n).length + 1) by simp; omega,
    Function.iterate_add_apply, hrev]
  simpa [initial_eq, readBE_encodeNat, show encodeNat 0 = [] from rfl] using hscan

/-- The final reset costs one more transition and empties both work stacks. -/
theorem division_run (n : ℕ) :
    (fun c => c.bind (computer p hp).step)^[2 * (encodeNat n).length + 3]
      (some (cfg p hp (some .reverse) (initialState p hp) (encodeNat n) [] [])) =
    some (cfg p hp none (initialState p hp) [] [] (encodeNat (n / p))) := by
  rw [show 2 * (encodeNat n).length + 3 = 1 + (2 * (encodeNat n).length + 2) by omega,
    Function.iterate_add_apply, division_pass, Function.iterate_one, Option.bind_some,
    step_finish]

private theorem initList_eq (bits : List Bool) :
    initList (computer p hp) bits = cfg p hp (some .reverse) (initialState p hp) bits [] [] := by
  unfold initList cfg
  congr
  funext k
  cases k <;> rfl

private theorem haltList_eq (bits : List Bool) :
    haltList (computer p hp) bits = cfg p hp none (initialState p hp) [] [] bits := by
  unfold haltList cfg
  congr
  funext k
  cases k <;> rfl

/-- A linear bit-time witness on the library's standard natural encoding. -/
def outputsInTime (n : ℕ) :
    TM2OutputsInTime (computer p hp) (encodeNat n) (some (encodeNat (n / p)))
      (2 * (encodeNat n).length + 3) where
  steps := 2 * (encodeNat n).length + 3
  evals_in_steps := by
    rw [initList_eq, Option.map_some, haltList_eq]
    exact division_run p hp n
  steps_le_m := le_rfl

/-- An actual finite-machine polynomial-time division theorem, for each fixed
positive divisor. The theorem is not uniform in a binary-encoded divisor. -/
noncomputable def computableInPolyTime :
    LeanNPHardness.TM2ComputableInPolyTime LeanNPHardness.finEncodingNatBool
      LeanNPHardness.finEncodingNatBool (fun n => n / p) where
  tm := computer p hp
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun n := by
    simpa [LeanNPHardness.finEncodingNatBool, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_X] using outputsInTime p hp n

#print axioms readBE_encodeNat
#print axioms digit_div
#print axioms advance_stateFor
#print axioms quotient_step
#print axioms reverse_run
#print axioms scan_run
#print axioms division_pass
#print axioms division_run
#print axioms outputsInTime
#print axioms computableInPolyTime

end PhdThesisLean.FixedDivisorBinary
