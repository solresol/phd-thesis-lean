import PhdThesisLean.FixedDivisorBinary
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# A polynomial-time binary-input p-adic valuation machine

For every fixed prime, repeatedly perform finite-state binary long division.
The quotient remains binary throughout. A mark is emitted only for a positive
exact division; zero returns zero, matching `padicValNat`. The unary output is
at most the input bit length. This is a real TM2 runtime theorem for valuation,
not yet a rational-loss verifier or an NP-membership result.
-/

namespace PhdThesisLean.PadicValuationMachine

open Computability Turing StateTransition
open LeanNPHardness.MachinePrimitives
open FixedDivisorBinary (State initialState observe held advance stateFor readBE next)

set_option backward.isDefEq.respectTransparency false

inductive Stack
  | value | work | output
  deriving DecidableEq, Fintype

inductive Label
  | reverse | scan | check | cleanup
  deriving DecidableEq, Fintype

def Alphabet (_ : Stack) : Type := Bool

variable (p : ℕ) (hp : 0 < p)

/-- Exact division is repeated only when its quotient is positive. -/
def again (s : State p) : Bool := decide (s.rem.val = 0) && s.started

def program : Label → TM2.Stmt Alphabet Label (State p)
  | .reverse =>
      .pop .value (observe p) <|
        .branch (fun s => s.bit.isSome)
          (.push .work (held p) (.goto fun _ => .reverse))
          (.load (fun _ => initialState p hp) (.goto fun _ => .scan))
  | .scan =>
      .pop .work (observe p) <|
        .branch (fun s => s.bit.isSome)
          (.branch (FixedDivisorBinary.emit p)
            (.push .value (FixedDivisorBinary.outputBit p) <|
              .load (advance p hp) (.goto fun _ => .scan))
            (.load (advance p hp) (.goto fun _ => .scan)))
          (.goto fun _ => .check)
  | .check =>
      .branch (again p)
        (.push .output (fun _ => true) <|
          .load (fun _ => initialState p hp) (.goto fun _ => .reverse))
        (.goto fun _ => .cleanup)
  | .cleanup =>
      .pop .value (observe p) <|
        .branch (fun s => s.bit.isSome)
          (.goto fun _ => .cleanup)
          (.load (fun _ => initialState p hp) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .value
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .reverse
  σ := State p
  initialState := initialState p hp
  Γk₀Fin := Bool.fintype
  m := program p hp

def stackContents (value work output : List Bool) : (k : Stack) → List (Alphabet k)
  | .value => value
  | .work => work
  | .output => output

def cfg (label : Option Label) (s : State p) (value work output : List Bool) :
    (computer p hp).Cfg where
  l := label
  var := s
  stk := stackContents value work output

private theorem step_reverse_nil (s : State p) (work output : List Bool) :
    (computer p hp).step (cfg p hp (some .reverse) s [] work output) =
      some (cfg p hp (some .scan) (initialState p hp) [] work output) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe, Function.update]

private theorem step_reverse_cons (s : State p) (b : Bool) (value work output : List Bool) :
    (computer p hp).step (cfg p hp (some .reverse) s (b :: value) work output) =
      some (cfg p hp (some .reverse) (observe p s (some b)) value (b :: work) output) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe, held, Function.update]
  funext k
  cases k <;> rfl

private theorem step_scan_nil (n : ℕ) (last : Option Bool) (value output : List Bool) :
    (computer p hp).step (cfg p hp (some .scan) (stateFor p hp n last) value [] output) =
      some (cfg p hp (some .check) (stateFor p hp n none) value [] output) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe, stateFor, Function.update]

private theorem step_scan_cons (n : ℕ) (last : Option Bool) (b : Bool)
    (bits output : List Bool) :
    (computer p hp).step
      (cfg p hp (some .scan) (stateFor p hp n last) (encodeNat (n / p)) (b :: bits) output) =
      some (cfg p hp (some .scan) (stateFor p hp (next n b) (some b))
        (encodeNat (next n b / p)) bits output) := by
  have hs := FixedDivisorBinary.advance_stateFor p hp n b
  have hq := FixedDivisorBinary.quotient_step p hp n b
  have he : observe p (stateFor p hp n last) (some b) = stateFor p hp n (some b) := rfl
  have hbit : (stateFor p hp n (some b)).bit.isSome = true := rfl
  simp only [computer, FinTM2.step, TM2.step, cfg, program, TM2.stepAux,
    Alphabet, stackContents, List.head?_cons, List.tail_cons, he, hbit, Bool.cond_true]
  by_cases hh : FixedDivisorBinary.emit p (stateFor p hp n (some b)) = true
  · simp only [hh, Bool.cond_true] at hq ⊢
    rw [hs]
    simp only [↓reduceIte] at hq
    congr 2
    funext k
    cases k <;> simp [Function.update, stackContents, ← hq]
  · have hf : FixedDivisorBinary.emit p (stateFor p hp n (some b)) = false := by simpa using hh
    simp only [hf, Bool.cond_false] at hq ⊢
    rw [hs]
    simp only [Bool.false_eq_true, ↓reduceIte] at hq
    congr 2
    funext k
    cases k <;> simp [Function.update, stackContents, ← hq]

private theorem step_cleanup_nil (s : State p) (output : List Bool) :
    (computer p hp).step (cfg p hp (some .cleanup) s [] [] output) =
      some (cfg p hp none (initialState p hp) [] [] output) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe]

private theorem step_cleanup_cons (s : State p) (b : Bool) (value output : List Bool) :
    (computer p hp).step (cfg p hp (some .cleanup) s (b :: value) [] output) =
      some (cfg p hp (some .cleanup) (observe p s (some b)) value [] output) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe]
  funext k
  cases k <;> rfl

/-- The halt path drains the remaining binary quotient. -/
theorem cleanup_run (value output : List Bool) (s : State p) :
    (fun c => c.bind (computer p hp).step)^[value.length + 1]
      (some (cfg p hp (some .cleanup) s value [] output)) =
    some (cfg p hp none (initialState p hp) [] [] output) := by
  induction value generalizing s with
  | nil => simpa using step_cleanup_nil p hp s output
  | cons b value ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, Option.bind_some, step_cleanup_cons]
      exact ih (observe p s (some b))

theorem reverse_run (value work output : List Bool) (s : State p) :
    (fun c => c.bind (computer p hp).step)^[value.length + 1]
      (some (cfg p hp (some .reverse) s value work output)) =
    some (cfg p hp (some .scan) (initialState p hp) []
      (value.reverse ++ work) output) := by
  induction value generalizing work s with
  | nil => simpa using step_reverse_nil p hp s work output
  | cons b value ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, Option.bind_some, step_reverse_cons]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (b :: work) (observe p s (some b))

theorem scan_run (bits output : List Bool) (n : ℕ) (last : Option Bool) :
    (fun c => c.bind (computer p hp).step)^[bits.length + 1]
      (some (cfg p hp (some .scan) (stateFor p hp n last) (encodeNat (n / p)) bits output)) =
    some (cfg p hp (some .check) (stateFor p hp (readBE n bits) none)
      (encodeNat (readBE n bits / p)) [] output) := by
  induction bits generalizing n last with
  | nil => simpa [readBE] using step_scan_nil p hp n last (encodeNat (n / p)) output
  | cons b bits ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, Option.bind_some, step_scan_cons]
      exact ih (next n b) (some b)

private theorem initial_eq : initialState p hp = stateFor p hp 0 none := by
  simp [initialState, stateFor]

/-- A full division pass with a preserved valuation-output suffix. -/
theorem division_pass (n : ℕ) (output : List Bool) :
    (fun c => c.bind (computer p hp).step)^[2 * (encodeNat n).length + 2]
      (some (cfg p hp (some .reverse) (initialState p hp) (encodeNat n) [] output)) =
    some (cfg p hp (some .check) (stateFor p hp n none) (encodeNat (n / p)) [] output) := by
  have hrev := reverse_run p hp (encodeNat n) [] output (initialState p hp)
  have hscan := scan_run p hp (encodeNat n).reverse output 0 none
  rw [show 2 * (encodeNat n).length + 2 =
    ((encodeNat n).reverse.length + 1) + ((encodeNat n).length + 1) by simp; omega,
    Function.iterate_add_apply, hrev]
  simpa [initial_eq, FixedDivisorBinary.readBE_encodeNat, show encodeNat 0 = [] from rfl] using hscan

/-- The loop guard exactly characterizes a positive integer divisible by `p`. -/
theorem again_iff (n : ℕ) :
    again p (stateFor p hp n none) = true ↔ n ≠ 0 ∧ p ∣ n := by
  simp only [again, stateFor, Bool.and_eq_true, decide_eq_true_eq, Nat.dvd_iff_mod_eq_zero]
  have hn := Nat.mod_add_div n p
  constructor
  · rintro ⟨hm, hq⟩
    exact ⟨by intro hz; simp_all, hm⟩
  · rintro ⟨hn0, hm⟩
    exact ⟨hm, by intro hq; simp_all⟩

private theorem step_check_yes (n : ℕ) (output : List Bool) (h : n ≠ 0 ∧ p ∣ n) :
    (computer p hp).step
      (cfg p hp (some .check) (stateFor p hp n none) (encodeNat (n / p)) [] output) =
      some (cfg p hp (some .reverse) (initialState p hp) (encodeNat (n / p)) [] (true :: output)) := by
  have hg := (again_iff p hp n).2 h
  simp [computer, FinTM2.step, cfg, program, hg, stackContents, Alphabet]
  funext k
  cases k <;> rfl

private theorem step_check_no (n : ℕ) (output : List Bool) (h : ¬(n ≠ 0 ∧ p ∣ n)) :
    (computer p hp).step
      (cfg p hp (some .check) (stateFor p hp n none) (encodeNat (n / p)) [] output) =
      some (cfg p hp (some .cleanup) (stateFor p hp n none) (encodeNat (n / p)) [] output) := by
  have hg : again p (stateFor p hp n none) = false := by
    simpa using mt (again_iff p hp n).1 h
  simp [computer, FinTM2.step, cfg, program, hg]

/-- Positive division by at least two strictly reduces the binary length. -/
theorem size_div_lt (h2 : 2 ≤ p) {n : ℕ} (hn : 0 < n) : (n / p).size < n.size := by
  by_cases hq : n / p = 0
  · simp only [hq, Nat.size_zero]
    exact Nat.size_pos.mpr hn
  · have hdouble : 2 * (n / p) ≤ n := by
      have hd := Nat.div_mul_le_self n p
      nlinarith
    have hs := Nat.size_le_size hdouble
    have he : (2 * (n / p)).size = (n / p).size + 1 := by
      simpa [Nat.bit_val, two_mul] using
        (Nat.size_bit (b := false) (n := n / p) (by simp [Nat.bit_val, hq]))
    omega

/-- Exact recurrence of the machine execution, including empty-stack checks,
failed terminal division and cleanup. -/
def runtime (h2 : 2 ≤ p) (n : ℕ) : ℕ :=
  if h : n ≠ 0 ∧ p ∣ n then
    2 * n.size + 3 + runtime h2 (n / p)
  else 2 * n.size + (n / p).size + 4
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h.1) (by omega)

theorem runtime_le (h2 : 2 ≤ p) (n : ℕ) : runtime p h2 n ≤ 4 * (n.size + 1) ^ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [runtime]
      split_ifs with hn
      · have hlt : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn.1) (by omega)
        have hb := ih (n / p) hlt
        have hs := size_div_lt p h2 (Nat.pos_of_ne_zero hn.1)
        nlinarith
      · have hs := Nat.size_le_size (Nat.div_le_self n p)
        nlinarith

variable [Fact p.Prime]

/-- Positive exact division contributes one to the mathematical valuation. -/
theorem valuation_step {n : ℕ} (h : n ≠ 0 ∧ p ∣ n) :
    padicValNat p n = padicValNat p (n / p) + 1 := by
  have hv := one_le_padicValNat_of_dvd h.1 h.2
  have hd := padicValNat.div h.2
  omega

/-- Complete exact execution, with arbitrary preserved output suffix. The
computed value is mathlib's valuation, including its zero convention. -/
theorem valuation_run (n : ℕ) (output : List Bool) :
    (fun c => c.bind (computer p hp).step)^[runtime p (Fact.out : p.Prime).two_le n]
      (some (cfg p hp (some .reverse) (initialState p hp) (encodeNat n) [] output)) =
    some (cfg p hp none (initialState p hp) [] []
      (List.replicate (padicValNat p n) true ++ output)) := by
  induction n using Nat.strong_induction_on generalizing output with
  | h n ih =>
      rw [runtime]
      split_ifs with hn
      · have hlt : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn.1)
          (Fact.out : p.Prime).one_lt
        rw [show 2 * n.size + 3 + runtime p (Fact.out : p.Prime).two_le (n / p) =
          runtime p (Fact.out : p.Prime).two_le (n / p) + 1 + (2 * (encodeNat n).length + 2) by
            rw [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size]; omega,
          Function.iterate_add_apply, division_pass, Function.iterate_add_apply,
          Function.iterate_one, Option.bind_some, step_check_yes p hp n output hn,
          ih (n / p) hlt]
        rw [valuation_step p hn, List.replicate_succ']
        simp [List.append_assoc]
      · rw [show 2 * n.size + (n / p).size + 4 =
          ((encodeNat (n / p)).length + 1) + 1 + (2 * (encodeNat n).length + 2) by
            simp only [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size]; omega,
          Function.iterate_add_apply, division_pass, Function.iterate_add_apply,
          Function.iterate_one, Option.bind_some, step_check_no p hp n output hn,
          cleanup_run]
        have hv : padicValNat p n = 0 := by
          by_cases h0 : n = 0
          · simp [h0]
          · exact padicValNat.eq_zero_of_not_dvd (fun hd => hn ⟨h0, hd⟩)
        simp [hv]

omit [Fact p.Prime] in
private theorem initList_eq (bits : List Bool) :
    initList (computer p hp) bits = cfg p hp (some .reverse) (initialState p hp) bits [] [] := by
  unfold initList cfg
  congr
  funext k
  cases k <;> rfl

omit [Fact p.Prime] in
private theorem haltList_eq (bits : List Bool) :
    haltList (computer p hp) bits = cfg p hp none (initialState p hp) [] [] bits := by
  unfold haltList cfg
  congr
  funext k
  cases k <;> rfl

/-- Quadratic time in actual binary input length, with all work stacks empty
and the initial finite state restored on termination. -/
def outputsInTime (n : ℕ) :
    TM2OutputsInTime (computer p hp) (encodeNat n)
      (some (List.replicate (padicValNat p n) true)) (4 * ((encodeNat n).length + 1) ^ 2) where
  steps := runtime p (Fact.out : p.Prime).two_le n
  evals_in_steps := by
    rw [initList_eq, Option.map_some, haltList_eq]
    have h := valuation_run p hp n []
    rw [List.append_nil] at h
    exact h
  steps_le_m := by
    rw [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size]
    exact runtime_le p (Fact.out : p.Prime).two_le n

/-- The unary result is no longer than the original binary input. -/
theorem valuation_le_size (n : ℕ) : padicValNat p n ≤ n.size := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≠ 0 ∧ p ∣ n
      · have hlt : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn.1)
          (Fact.out : p.Prime).one_lt
        have hi := ih (n / p) hlt
        have hs := size_div_lt p (Fact.out : p.Prime).two_le (Nat.pos_of_ne_zero hn.1)
        rw [valuation_step p hn]
        omega
      · have hv : padicValNat p n = 0 := by
          by_cases h0 : n = 0
          · simp [h0]
          · exact padicValNat.eq_zero_of_not_dvd (fun hd => hn ⟨h0, hd⟩)
        simp [hv]

private theorem unary_eq (n : ℕ) : unaryEncodeNat n = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, List.replicate_succ, ih]

/-- Binary input and a unary valuation output; the latter is bounded by the
input bit length. This output convention is explicit in the theorem type. -/
noncomputable def computableInPolyTime :
    LeanNPHardness.TM2ComputableInPolyTime LeanNPHardness.finEncodingNatBool
      LeanNPHardness.unaryFinEncodingNat (padicValNat p) where
  tm := computer p hp
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 4 * (Polynomial.X + 1) ^ 2
  outputsFun n := by
    simpa [LeanNPHardness.finEncodingNatBool, LeanNPHardness.unaryFinEncodingNat,
      unary_eq, Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one] using outputsInTime p hp n

#print axioms again_iff
#print axioms size_div_lt
#print axioms runtime_le
#print axioms valuation_step
#print axioms valuation_le_size
#print axioms valuation_run
#print axioms outputsInTime
#print axioms computableInPolyTime

end PhdThesisLean.PadicValuationMachine
