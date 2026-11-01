import PhdThesisLean.PadicValuationMachine
import PhdThesisLean.RationalVerifierBounds

/-!
# Fixed-base powers on the valuation machine's unary output

A finite TM2 computes `p^e` in canonical binary from a unary exponent. Each
multiplication by the fixed positive base uses a binary scan with carry in
`Fin p`; no unbounded arithmetic occurs in the control. Composition with the
binary-input valuation machine computes `p^(padicValNat p n)` in polynomial
time. This is one verifier component, not the entire rational verifier.
-/

namespace PhdThesisLean.FixedBasePowerMachine

open Computability Turing StateTransition
open LeanNPHardness.MachinePrimitives

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (hp : 0 < p)

/-- Low product digit before division by two. -/
def digit (c : ℕ) (b : Bool) : ℕ := p * b.toNat + c

def mulBits : ℕ → List Bool → List Bool
  | c, [] => encodeNat c
  | c, b :: bits => decide (digit p c b % 2 = 1) :: mulBits (digit p c b / 2) bits

/-- Exact scan/flush time, including both empty-stack checks. -/
def scanTime : ℕ → List Bool → ℕ
  | c, [] => c.size + 2
  | c, b :: bits => scanTime (digit p c b / 2) bits + 1

theorem carry_lt (c : Fin p) (b : Bool) : digit p c.val b / 2 < p := by
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
  have := c.isLt
  cases b <;> simp [digit] <;> omega

theorem encodeNat_cons (n : ℕ) (hn : n ≠ 0) :
    encodeNat n = decide (n % 2 = 1) :: encodeNat (n / 2) := by
  simpa only [LeanNPHardness.BinaryConvert.bitsOf_eq] using
    LeanNPHardness.BinaryConvert.bitsOf_pos n hn

include hp in
/-- Multiplication preserves the canonical binary representation. -/
theorem mulBits_encodeNat (n c : ℕ) : mulBits p c (encodeNat n) = encodeNat (p * n + c) := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
      by_cases hn : n = 0
      · subst n; simp [mulBits, show encodeNat 0 = [] from rfl]
      · rw [encodeNat_cons n hn, mulBits, ih (n / 2) (by omega)]
        have hb : (decide (n % 2 = 1)).toNat = n % 2 := by
          have := Nat.mod_lt n (by decide : 0 < 2)
          by_cases h : n % 2 = 1 <;> simp [h]; omega
        have he : p * n + c = 2 * (p * (n / 2)) + digit p c (decide (n % 2 = 1)) := by
          have := Nat.mod_add_div n 2
          dsimp [digit]
          rw [hb]
          nlinarith
        rw [encodeNat_cons (p * n + c) (by have := Nat.mul_pos hp (Nat.pos_of_ne_zero hn); omega)]
        have hdiv : (p * n + c) / 2 = p * (n / 2) + digit p c (decide (n % 2 = 1)) / 2 := by
          rw [he]; omega
        have hmod : (p * n + c) % 2 = digit p c (decide (n % 2 = 1)) % 2 := by
          rw [he]; omega
        rw [hdiv, hmod]

theorem mulBits_length_le (bits : List Bool) (c : Fin p) :
    (mulBits p c.val bits).length ≤ bits.length + p.size := by
  induction bits generalizing c with
  | nil =>
      simp only [mulBits, List.length_nil, Nat.zero_add,
        LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size]
      exact Nat.size_le_size c.isLt.le
  | cons b bits ih =>
      have h := ih ⟨_, carry_lt p c b⟩
      simp only [mulBits, List.length_cons]
      dsimp only at h
      omega

theorem scanTime_le (bits : List Bool) (c : Fin p) :
    scanTime p c.val bits ≤ bits.length + p.size + 2 := by
  induction bits generalizing c with
  | nil =>
      simp only [scanTime, List.length_nil, Nat.zero_add]
      exact Nat.add_le_add_right (Nat.size_le_size c.isLt.le) 2
  | cons b bits ih =>
      have h := ih ⟨_, carry_lt p c b⟩
      simp only [scanTime, List.length_cons]
      dsimp only at h
      omega

inductive Stack
  | input | value | work
  deriving DecidableEq, Fintype

inductive Label
  | start | check | scan | flush | reverse
  deriving DecidableEq, Fintype

structure State (p : ℕ) where
  carry : Fin p
  bit : Option Bool
  deriving DecidableEq, Fintype

def initialState : State p := ⟨⟨0, hp⟩, none⟩
def observe (s : State p) (b : Option Bool) : State p := { s with bit := b }
def held (s : State p) : Bool := s.bit.getD false
def advance (s : State p) : State p :=
  ⟨⟨digit p s.carry.val (held p s) / 2, carry_lt p s.carry (held p s)⟩, none⟩
def half (s : State p) : State p :=
  ⟨⟨s.carry.val / 2, (Nat.div_le_self _ _).trans_lt s.carry.isLt⟩, none⟩
def Alphabet (_ : Stack) : Type := Bool

/-- Every arithmetic transition has a finite domain depending only on `p`. -/
def program : Label → TM2.Stmt Alphabet Label (State p)
  | .start => .push .value (fun _ => true) (.goto fun _ => .check)
  | .check =>
      .pop .input (observe p) <|
        .branch (fun s => s.bit.isSome)
          (.load (fun _ => initialState p hp) (.goto fun _ => .scan))
          (.load (fun _ => initialState p hp) .halt)
  | .scan =>
      .pop .value (observe p) <|
        .branch (fun s => s.bit.isSome)
          (.push .work (fun s => decide (digit p s.carry.val (held p s) % 2 = 1)) <|
            .load (advance p) (.goto fun _ => .scan))
          (.goto fun _ => .flush)
  | .flush =>
      .branch (fun s => decide (s.carry.val ≠ 0))
        (.push .work (fun s => decide (s.carry.val % 2 = 1)) <|
          .load (half p) (.goto fun _ => .flush))
        (.load (fun _ => initialState p hp) (.goto fun _ => .reverse))
  | .reverse =>
      .pop .work (observe p) <|
        .branch (fun s => s.bit.isSome)
          (.push .value (held p) (.goto fun _ => .reverse))
          (.load (fun _ => initialState p hp) (.goto fun _ => .check))

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .value
  Γ := Alphabet
  Λ := Label
  main := .start
  σ := State p
  initialState := initialState p hp
  Γk₀Fin := Bool.fintype
  m := program p hp

def stackContents (input value work : List Bool) : (k : Stack) → List (Alphabet k)
  | .input => input
  | .value => value
  | .work => work

def cfg (label : Option Label) (s : State p) (input value work : List Bool) :
    (computer p hp).Cfg where
  l := label
  var := s
  stk := stackContents input value work

private theorem step_scan_cons (c : Fin p) (last : Option Bool) (b : Bool)
    (input bits work : List Bool) :
    (computer p hp).step (cfg p hp (some .scan) ⟨c, last⟩ input (b :: bits) work) =
      some (cfg p hp (some .scan) ⟨⟨_, carry_lt p c b⟩, none⟩ input bits
        (decide (digit p c.val b % 2 = 1) :: work)) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observe, held, advance, Function.update]
  funext k
  cases k <;> rfl

private theorem step_scan_nil (c : Fin p) (last : Option Bool) (input work : List Bool) :
    (computer p hp).step (cfg p hp (some .scan) ⟨c, last⟩ input [] work) =
      some (cfg p hp (some .flush) ⟨c, none⟩ input [] work) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe, Function.update]

private theorem step_flush_zero (c : Fin p) (hc : c.val = 0) (input work : List Bool) :
    (computer p hp).step (cfg p hp (some .flush) ⟨c, none⟩ input [] work) =
      some (cfg p hp (some .reverse) (initialState p hp) input [] work) := by
  simp [computer, FinTM2.step, cfg, program, hc]

private theorem step_flush_pos (c : Fin p) (hc : c.val ≠ 0) (input work : List Bool) :
    (computer p hp).step (cfg p hp (some .flush) ⟨c, none⟩ input [] work) =
      some (cfg p hp (some .flush) (half p ⟨c, none⟩) input []
        (decide (c.val % 2 = 1) :: work)) := by
  simp [computer, FinTM2.step, cfg, program, hc, stackContents, Alphabet]
  funext k
  cases k <;> rfl

/-- Final carry emission costs exactly its binary length plus the zero test. -/
theorem flush_run (c : Fin p) (input work : List Bool) :
    (fun q => q.bind (computer p hp).step)^[c.val.size + 1]
      (some (cfg p hp (some .flush) ⟨c, none⟩ input [] work)) =
    some (cfg p hp (some .reverse) (initialState p hp) input []
      ((encodeNat c.val).reverse ++ work)) := by
  generalize hn : c.val = n
  induction n using Nat.strong_induction_on generalizing c work with
  | h n ih =>
      subst n
      by_cases hc : c.val = 0
      · simpa [hc, show encodeNat 0 = [] from rfl] using step_flush_zero p hp c hc input work
      · have he := encodeNat_cons c.val hc
        have hs := congrArg List.length he
        simp only [List.length_cons, LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size] at hs
        rw [hs, Function.iterate_succ_apply, Option.bind_some, step_flush_pos p hp c hc]
        have h := ih (c.val / 2) (by omega) (half p ⟨c, none⟩).carry
          (decide (c.val % 2 = 1) :: work) rfl
        simpa [half, he, List.reverse_cons, List.append_assoc] using h

/-- The scan preserves any exponent input and any reversed-output suffix. -/
theorem scan_run (bits input work : List Bool) (c : Fin p) (last : Option Bool) :
    (fun q => q.bind (computer p hp).step)^[scanTime p c.val bits]
      (some (cfg p hp (some .scan) ⟨c, last⟩ input bits work)) =
    some (cfg p hp (some .reverse) (initialState p hp) input []
      ((mulBits p c.val bits).reverse ++ work)) := by
  induction bits generalizing c last work with
  | nil =>
      rw [scanTime, Function.iterate_succ_apply, Option.bind_some, step_scan_nil]
      exact flush_run p hp c input work
  | cons b bits ih =>
      rw [scanTime, Function.iterate_succ_apply, Option.bind_some, step_scan_cons]
      simpa [mulBits, List.reverse_cons, List.append_assoc] using
        ih (decide (digit p c.val b % 2 = 1) :: work) ⟨_, carry_lt p c b⟩ none

private theorem step_reverse_nil (s : State p) (input value : List Bool) :
    (computer p hp).step (cfg p hp (some .reverse) s input value []) =
      some (cfg p hp (some .check) (initialState p hp) input value []) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe]

private theorem step_reverse_cons (s : State p) (b : Bool) (input value work : List Bool) :
    (computer p hp).step (cfg p hp (some .reverse) s input value (b :: work)) =
      some (cfg p hp (some .reverse) (observe p s (some b)) input (b :: value) work) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe, held, Function.update]
  funext k
  cases k <;> rfl

theorem reverse_run (work input value : List Bool) (s : State p) :
    (fun q => q.bind (computer p hp).step)^[work.length + 1]
      (some (cfg p hp (some .reverse) s input value work)) =
    some (cfg p hp (some .check) (initialState p hp) input (work.reverse ++ value) []) := by
  induction work generalizing s value with
  | nil => simpa using step_reverse_nil p hp s input value
  | cons b work ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, Option.bind_some, step_reverse_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (b :: value) (observe p s (some b))

def multiplyTime (n : ℕ) : ℕ := scanTime p 0 (encodeNat n) + (encodeNat (p * n)).length + 1

theorem multiply_run (n : ℕ) (input : List Bool) :
    (fun q => q.bind (computer p hp).step)^[multiplyTime p n]
      (some (cfg p hp (some .scan) (initialState p hp) input (encodeNat n) [])) =
    some (cfg p hp (some .check) (initialState p hp) input (encodeNat (p * n)) []) := by
  rw [multiplyTime, show scanTime p 0 (encodeNat n) + (encodeNat (p * n)).length + 1 =
      ((encodeNat (p * n)).reverse.length + 1) + scanTime p 0 (encodeNat n) by simp; omega,
    Function.iterate_add_apply]
  have h := scan_run p hp (encodeNat n) input [] ⟨0, hp⟩ none
  simp only [mulBits_encodeNat p hp, Nat.add_zero, List.append_nil] at h
  rw [show initialState p hp = (⟨⟨0, hp⟩, none⟩ : State p) from rfl, h]
  simpa only [List.length_reverse, List.reverse_reverse, List.append_nil, initialState] using
    reverse_run p hp (encodeNat (p * n)).reverse input [] (initialState p hp)

include hp in
theorem multiplyTime_le (n : ℕ) : multiplyTime p n ≤ 2 * n.size + 2 * p.size + 3 := by
  have ht := scanTime_le p (encodeNat n) ⟨0, hp⟩
  have hl := mulBits_length_le p (encodeNat n) ⟨0, hp⟩
  simp only [mulBits_encodeNat p hp, Nat.add_zero,
    LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size] at ht hl
  simp only [multiplyTime, LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size]
  omega


private theorem step_check_nil (s : State p) (value : List Bool) :
    (computer p hp).step (cfg p hp (some .check) s [] value []) =
      some (cfg p hp none (initialState p hp) [] value []) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe]

private theorem step_check_cons (s : State p) (input value : List Bool) :
    (computer p hp).step (cfg p hp (some .check) s (true :: input) value []) =
      some (cfg p hp (some .scan) (initialState p hp) input value []) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, observe]
  funext k
  cases k <;> rfl

/-- Exact time from the exponent loop, starting with binary accumulator `p^k`. -/
def powerTime (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | e + 1 => powerTime (k + 1) e + multiplyTime p (p ^ k) + 1

/-- Unary countdown, binary accumulator, and complete cleanup. -/
theorem power_run (e k : ℕ) :
    (fun q => q.bind (computer p hp).step)^[powerTime p k e]
      (some (cfg p hp (some .check) (initialState p hp)
        (List.replicate e true) (encodeNat (p ^ k)) [])) =
    some (cfg p hp none (initialState p hp) [] (encodeNat (p ^ (k + e))) []) := by
  induction e generalizing k with
  | zero => simpa [powerTime] using step_check_nil p hp (initialState p hp) (encodeNat (p ^ k))
  | succ e ih =>
      rw [powerTime, Function.iterate_succ_apply, Option.bind_some, List.replicate_succ,
        step_check_cons, Function.iterate_add_apply, multiply_run]
      rw [← pow_succ']
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

include hp in
theorem powerTime_le (e k : ℕ) :
    powerTime p k e ≤ e * (2 * p.size * (k + e) + 2 * p.size + 6) + 1 := by
  induction e generalizing k with
  | zero => simp [powerTime]
  | succ e ih =>
      have hi := ih (k + 1)
      have hm := multiplyTime_le p hp (p ^ k)
      have hs := RationalVerifierBounds.Fraction.size_pow_le p k
      simp only [powerTime]
      nlinarith

private theorem step_start (input : List Bool) :
    (computer p hp).step (cfg p hp (some .start) (initialState p hp) input [] []) =
      some (cfg p hp (some .check) (initialState p hp) input (encodeNat 1) []) := by
  simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    show encodeNat 1 = [true] from rfl]
  funext k
  cases k <;> rfl

private theorem initList_eq (bits : List Bool) :
    initList (computer p hp) bits = cfg p hp (some .start) (initialState p hp) bits [] [] := by
  unfold initList cfg
  congr
  funext k
  cases k <;> rfl

private theorem haltList_eq (bits : List Bool) :
    haltList (computer p hp) bits = cfg p hp none (initialState p hp) [] bits [] := by
  unfold haltList cfg
  congr
  funext k
  cases k <;> rfl

/-- Quadratic time in unary exponent length. The base is a program constant. -/
def outputsInTime (e : ℕ) :
    TM2OutputsInTime (computer p hp) (List.replicate e true)
      (some (encodeNat (p ^ e))) ((2 * p.size + 7) * (e + 1) ^ 2) where
  steps := powerTime p 0 e + 1
  evals_in_steps := by
    change (fun q : Option (computer p hp).Cfg => q.bind (computer p hp).step)^[powerTime p 0 e + 1]
      (some (initList (computer p hp) (List.replicate e true))) =
      some (haltList (computer p hp) (encodeNat (p ^ e)))
    rw [initList_eq, haltList_eq, Function.iterate_succ_apply, Option.bind_some, step_start]
    simpa only [pow_zero, Nat.zero_add] using power_run p hp e 0
  steps_le_m := by
    have h := powerTime_le p hp e 0
    nlinarith

private theorem unary_eq (e : ℕ) : unaryEncodeNat e = List.replicate e true := by
  induction e with
  | zero => rfl
  | succ e ih => simp [unaryEncodeNat, List.replicate_succ, ih]

/-- The exponent is unary, as supplied by `PadicValuationMachine`. There is
no polynomial-time claim for arbitrary binary exponents. -/
noncomputable def computableInPolyTime :
    LeanNPHardness.TM2ComputableInPolyTime LeanNPHardness.unaryFinEncodingNat
      LeanNPHardness.finEncodingNatBool (fun e => p ^ e) where
  tm := computer p hp
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C (2 * p.size + 7) * (Polynomial.X + 1) ^ 2
  outputsFun e := by
    simpa [LeanNPHardness.finEncodingNatBool, LeanNPHardness.unaryFinEncodingNat,
      unary_eq, Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one] using outputsInTime p hp e

variable [Fact p.Prime]

open LeanNPHardness.MachineComposition

/-- The two concrete machines, with the checked intermediate-list transfer. -/
noncomputable def valuationPowerAux : TM2ComputableAux Bool Bool :=
  compositionAux (PadicValuationMachine.computableInPolyTime p hp).toTM2ComputableAux
    (computableInPolyTime p hp).toTM2ComputableAux

/-- Use the proved unary output length to retain a quadratic bound in the
original binary magnitude length, including transfer and cleanup. -/
noncomputable def valuationPowerOutputsInTime (n : ℕ) :
    TM2OutputsInTime (valuationPowerAux p hp).tm (encodeNat n)
      (some (encodeNat (p ^ padicValNat p n)))
      ((2 * p.size + 15) * ((encodeNat n).length + 1) ^ 2) := by
  let first := (PadicValuationMachine.computableInPolyTime p hp).toTM2ComputableAux
  let second := (computableInPolyTime p hp).toTM2ComputableAux
  have run := compositionMachine_outputsInTime first second (encodeNat n)
    (List.replicate (padicValNat p n) true) (encodeNat (p ^ padicValNat p n))
    (4 * ((encodeNat n).length + 1) ^ 2)
    ((2 * p.size + 7) * (padicValNat p n + 1) ^ 2)
    (PadicValuationMachine.outputsInTime p hp n)
    (by
      change TM2OutputsInTime (computer p hp)
        ((List.replicate (padicValNat p n) true).map id)
        (some (encodeNat (p ^ padicValNat p n)))
        ((2 * p.size + 7) * (padicValNat p n + 1) ^ 2)
      simpa only [List.map_id] using outputsInTime p hp (padicValNat p n))
  apply evalsToInTimeMono run
  have hv := PadicValuationMachine.valuation_le_size p n
  simp only [List.length_replicate, LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size]
  have hsq : (padicValNat p n + 1) ^ 2 ≤ (n.size + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right hv 1) 2
  have hm := Nat.mul_le_mul_left (2 * p.size + 7) hsq
  nlinarith

/-- Binary input and binary output. No external arithmetic/runtime hypothesis
is supplied; the bound is `(2*size(p)+15)*(s+1)^2` actual TM2 steps. -/
noncomputable def valuationPowerComputableInPolyTime :
    LeanNPHardness.TM2ComputableInPolyTime LeanNPHardness.finEncodingNatBool
      LeanNPHardness.finEncodingNatBool (fun n => p ^ padicValNat p n) where
  toTM2ComputableAux := valuationPowerAux p hp
  time := Polynomial.C (2 * p.size + 15) * (Polynomial.X + 1) ^ 2
  outputsFun n := by
    simpa [valuationPowerAux, compositionAux, PadicValuationMachine.computableInPolyTime,
      computableInPolyTime, LeanNPHardness.finEncodingNatBool, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_pow, Polynomial.eval_one] using valuationPowerOutputsInTime p hp n

/-- Both powers used in `Fraction.norm` have polynomial binary output size.
The zero convention returns one here; `Fraction.norm` separately maps zero
fractions to zero. -/
theorem valuationPower_length_le (n : ℕ) :
    (encodeNat (p ^ padicValNat p n)).length ≤ p.size * n.size + 1 := by
  rw [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size]
  exact (RationalVerifierBounds.Fraction.size_pow_le p _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (PadicValuationMachine.valuation_le_size p n)) 1)

#print axioms mulBits_encodeNat
#print axioms scanTime_le
#print axioms multiply_run
#print axioms multiplyTime_le
#print axioms power_run
#print axioms powerTime_le
#print axioms outputsInTime
#print axioms computableInPolyTime
#print axioms valuationPowerOutputsInTime
#print axioms valuationPowerComputableInPolyTime
#print axioms valuationPower_length_le

end PhdThesisLean.FixedBasePowerMachine
