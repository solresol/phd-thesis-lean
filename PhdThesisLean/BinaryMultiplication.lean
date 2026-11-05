import PhdThesisLean.FixedBasePowerMachine
import LeanNPHardness.PairEncoding
import LeanNPHardness.BinaryArithmetic

/-!
# A finite binary multiplication machine

A Horner scan of the first magnitude uses only binary shifts and finite-carry
addition, preserving the second magnitude on work stacks. Both inputs and the
output use canonical binary, including the empty word for zero. The runtime
counts input routing, every loop and exhaustion transition, and full cleanup.
This is a magnitude-arithmetic component of the rational regression verifier.
-/
namespace PhdThesisLean.BinaryMultiplication

open Computability Turing StateTransition
open LeanNPHardness.MachinePrimitives

set_option backward.isDefEq.respectTransparency false

abbrev Symbol := Sum Bool Bool

def encoding := LeanNPHardness.PairEncoding.finEncoding
  LeanNPHardness.finEncodingNatBool LeanNPHardness.finEncodingNatBool

def wire (a b : List Bool) : List Symbol := a.map Sum.inl ++ b.map Sum.inr

@[simp] theorem encode_eq (x : ℕ × ℕ) :
    encoding.encode x = wire (encodeNat x.1) (encodeNat x.2) := rfl

@[simp] theorem wire_length (a b : List Bool) : (wire a b).length = a.length + b.length := by
  simp [wire]

def shift (bits : List Bool) : List Bool := if bits.isEmpty then [] else false :: bits

theorem shift_encode (a : ℕ) : shift (encodeNat a) = encodeNat (2 * a) := by
  by_cases ha : a = 0
  · subst a; rfl
  · have h : 2 * a ≠ 0 := by omega
    rw [FixedBasePowerMachine.encodeNat_cons (2 * a) h]
    have hn : (encodeNat a).isEmpty = false := by
      have hl := LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size a
      have hs : 0 < a.size := Nat.size_pos.mpr (by omega)
      cases he : encodeNat a <;> simp_all
    simp [shift, hn]

def next (bit : Bool) (n a : ℕ) : ℕ := 2 * a + bit.toNat * n

def horner (bits : List Bool) (n a : ℕ) : ℕ := bits.foldl (fun a bit => next bit n a) a

theorem horner_encode (m n : ℕ) : horner (encodeNat m).reverse n 0 = m * n := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm : m = 0
      · subst m; simp [horner, show encodeNat 0 = [] from rfl]
      · rw [FixedBasePowerMachine.encodeNat_cons m hm, List.reverse_cons]
        simp only [horner, List.foldl_append, List.foldl_cons, List.foldl_nil]
        change next (decide (m % 2 = 1)) n (horner (encodeNat (m / 2)).reverse n 0) = _
        rw [ih (m / 2) (by omega)]
        have hb : (decide (m % 2 = 1)).toNat = m % 2 := by
          have := Nat.mod_lt m (by decide : 0 < 2)
          by_cases h : m % 2 = 1 <;> simp [h]; omega
        dsimp [next]; rw [hb]
        have := Nat.mod_add_div m 2
        nlinarith

theorem next_size (bit : Bool) (n a : ℕ) :
    (next bit n a).size ≤ max a.size n.size + 2 := by
  have hs : (2 * a).size ≤ a.size + 1 := by
    have := congrArg List.length (shift_encode a)
    simp only [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size] at this
    simp only [shift] at this
    split at this <;> simp only [List.length_nil, List.length_cons,
      LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size] at this <;> omega
  cases bit
  · simpa [next] using hs.trans (by omega)
  · have := RationalVerifierBounds.Fraction.size_add (2 * a) n
    simpa [next] using this.trans (by omega)

inductive Stack
  | input | digits | factor | saved | value | work
  deriving DecidableEq, Fintype
inductive Label
  | route | check | shift | add | restore | factorRestore | drain
  deriving DecidableEq, Fintype
structure State where
  digit : Bool
  carry : Bool
  a : Option Bool
  b : Option Bool
  symbol : Option Symbol
  deriving DecidableEq, Fintype

def state (digit carry : Bool) : State := ⟨digit, carry, none, none, none⟩
def initial : State := state false false

def Alphabet : Stack → Type
  | .input => Symbol
  | _ => Bool

def observe (s : State) (a : Option Bool) : State := {s with a := a}
def observeB (s : State) (b : Option Bool) : State := {s with b := b}
def go (l : Label) (d c : Bool) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => state d c) (.goto fun _ => l)

def program : Label → TM2.Stmt Alphabet Label State
  | .route => .pop .input (fun s x => {s with symbol := x}) <|
      .branch (fun s => s.symbol.isSome)
        (.branch (fun s => match s.symbol with | some (.inl _) => true | _ => false)
          (.push .digits (fun s => match s.symbol with | some (.inl b) => b | _ => false)
            (go .route false false))
          (.push .saved (fun s => match s.symbol with | some (.inr b) => b | _ => false)
            (go .route false false)))
        (go .factorRestore false false)
  | .check => .pop .digits observe <|
      .branch (fun s => s.a.isSome)
        (.load (fun s => state (s.a.getD false) false) (.goto fun _ => .shift))
        (go .drain false false)
  | .shift => .pop .value observe <|
      .branch (fun s => s.a.isSome)
        (.push .value (fun s => s.a.getD false) <| .push .value (fun _ => false) <|
          .load (fun s => state s.digit false) (.goto fun s => if s.digit then .add else .check))
        (.load (fun s => state s.digit false) (.goto fun s => if s.digit then .add else .check))
  | .add => .pop .value observe <| .pop .factor observeB <|
      .branch (fun s => s.a.isSome || s.b.isSome)
        (.branch (fun s => s.b.isSome)
          (.push .saved (fun s => s.b.getD false) <|
            .push .work (fun s => (binaryAddStep s.carry s.a s.b).1) <|
              .load (fun s => state false (binaryAddStep s.carry s.a s.b).2)
                (.goto fun _ => .add))
          (.push .work (fun s => (binaryAddStep s.carry s.a s.b).1) <|
            .load (fun s => state false (binaryAddStep s.carry s.a s.b).2)
              (.goto fun _ => .add)))
        (.branch (fun s => s.carry)
          (.push .work (fun _ => true) (go .restore false false))
          (go .restore false false))
  | .restore => .pop .work observe <|
      .branch (fun s => s.a.isSome)
        (.push .value (fun s => s.a.getD false) (go .restore false false))
        (go .factorRestore false false)
  | .factorRestore => .pop .saved observe <|
      .branch (fun s => s.a.isSome)
        (.push .factor (fun s => s.a.getD false) (go .factorRestore false false))
        (go .check false false)
  | .drain => .pop .factor observe <|
      .branch (fun s => s.a.isSome)
        (go .drain false false)
        (.load (fun _ => initial) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .value
  Γ := Alphabet
  Λ := Label
  main := .route
  σ := State
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype Symbol)
  m := program

def contents (input : List Symbol) (digits factor saved value work : List Bool) :
    (k : Stack) → List (Alphabet k)
  | .input => input
  | .digits => digits
  | .factor => factor
  | .saved => saved
  | .value => value
  | .work => work

def cfg (l : Option Label) (s : State) (input : List Symbol)
    (digits factor saved value work : List Bool) : computer.Cfg :=
  ⟨l, s, contents input digits factor saved value work⟩

private theorem route_left (b : Bool) (input : List Symbol) (digits saved : List Bool) :
    computer.step (cfg (some .route) initial (Sum.inl b :: input) digits [] saved [] []) =
    some (cfg (some .route) initial input (b :: digits) [] saved [] []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, go, initial, state, Function.update]
  funext k; cases k <;> rfl

private theorem route_right (b : Bool) (input : List Symbol) (digits saved : List Bool) :
    computer.step (cfg (some .route) initial (Sum.inr b :: input) digits [] saved [] []) =
    some (cfg (some .route) initial input digits [] (b :: saved) [] []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, go, initial, state, Function.update]
  funext k; cases k <;> rfl

private theorem route_nil (digits saved : List Bool) :
    computer.step (cfg (some .route) initial [] digits [] saved [] []) =
    some (cfg (some .factorRestore) initial [] digits [] saved [] []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, go, initial, state]

theorem route_left_run (bits : List Bool) (input : List Symbol) (digits saved : List Bool) :
    (fun q => q.bind computer.step)^[bits.length]
      (some (cfg (some .route) initial (bits.map Sum.inl ++ input) digits [] saved [] [])) =
    some (cfg (some .route) initial input (bits.reverse ++ digits) [] saved [] []) := by
  induction bits generalizing digits with
  | nil => simp
  | cons b bits ih =>
      simp only [List.length_cons, List.map_cons, List.cons_append]
      rw [Function.iterate_succ_apply, Option.bind_some, route_left, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem route_right_run (bits : List Bool) (digits saved : List Bool) :
    (fun q => q.bind computer.step)^[bits.length + 1]
      (some (cfg (some .route) initial (bits.map Sum.inr) digits [] saved [] [])) =
    some (cfg (some .factorRestore) initial [] digits [] (bits.reverse ++ saved) [] []) := by
  induction bits generalizing saved with
  | nil => simpa using route_nil digits saved
  | cons b bits ih =>
      simp only [List.length_cons, List.map_cons]
      rw [Function.iterate_succ_apply, Option.bind_some, route_right, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem factor_restore_cons (b : Bool) (digits factor saved value : List Bool) :
    computer.step (cfg (some .factorRestore) initial [] digits factor (b :: saved) value []) =
    some (cfg (some .factorRestore) initial [] digits (b :: factor) saved value []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, go, initial, state, observe,
    Function.update]
  funext k; cases k <;> rfl

private theorem factor_restore_nil (digits factor value : List Bool) :
    computer.step (cfg (some .factorRestore) initial [] digits factor [] value []) =
    some (cfg (some .check) initial [] digits factor [] value []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, go, initial, state, observe]

theorem factor_restore_run (digits factor saved value : List Bool) :
    (fun q => q.bind computer.step)^[saved.length + 1]
      (some (cfg (some .factorRestore) initial [] digits factor saved value [])) =
    some (cfg (some .check) initial [] digits (saved.reverse ++ factor) [] value []) := by
  induction saved generalizing factor with
  | nil => simpa using factor_restore_nil digits factor value
  | cons b saved ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, factor_restore_cons, ih]
      simp [List.reverse_cons, List.append_assoc]


private theorem add_nil (d c : Bool) (digits saved work : List Bool) :
    computer.step (cfg (some .add) (state d c) [] digits [] saved [] work) =
    some (cfg (some .restore) initial [] digits [] saved []
      (if c then true :: work else work)) := by
  cases c <;> simp [computer, FinTM2.step, cfg, program, contents, Alphabet,
    go, initial, state, observe, observeB, Function.update]
  all_goals funext k; cases k <;> rfl

private theorem add_step (d c : Bool) (digits left right saved work : List Bool)
    (hne : left ≠ [] ∨ right ≠ []) :
    computer.step (cfg (some .add) (state d c) [] digits right saved left work) =
    some (cfg (some .add) (state false (binaryAddStep c left.head? right.head?).2)
      [] digits right.tail (right.take 1 ++ saved) left.tail
      ((binaryAddStep c left.head? right.head?).1 :: work)) := by
  cases left with
  | nil =>
      cases right with
      | nil => simp at hne
      | cons b right =>
          simp [computer, FinTM2.step, cfg, program, contents, Alphabet,
            go, initial, state, observe, observeB, Function.update]
          funext k; cases k <;> rfl
  | cons a left =>
      cases right <;>
        simp [computer, FinTM2.step, cfg, program, contents, Alphabet,
          go, initial, state, observe, observeB, Function.update]
      all_goals funext k; cases k <;> rfl

/-- One ripple-carry pass, with a copy of every factor digit retained. -/
theorem add_run (left right : List Bool) (d c : Bool) (digits saved work : List Bool) :
    (fun q => q.bind computer.step)^[max left.length right.length + 1]
      (some (cfg (some .add) (state d c) [] digits right saved left work)) =
    some (cfg (some .restore) initial [] digits [] (right.reverse ++ saved) []
      ((binaryAddBitsAux c left right).reverse ++ work)) := by
  induction left generalizing right d c saved work with
  | nil =>
      induction right generalizing d c saved work with
      | nil =>
          have h := add_nil d c digits saved work
          cases c <;> simpa [binaryAddBitsAux] using h
      | cons b right ih =>
          simp only [List.length_nil, Nat.zero_max] at ih
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply, Option.bind_some, add_step d c _ _ _ _ _ (by simp)]
          simp only [List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
            List.take_succ_cons, List.take_zero, List.singleton_append]
          rw [ih]
          simp [binaryAddBitsAux, List.reverse_cons, List.append_assoc]
  | cons a left ih =>
      cases right with
      | nil =>
          simp only [List.length_nil, List.length_cons, Nat.max_zero]
          rw [Function.iterate_succ_apply, Option.bind_some, add_step d c _ _ _ _ _ (by simp)]
          simp only [List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
            List.take_nil, List.nil_append]
          have h := ih [] false (binaryAddStep c (some a) none).2 saved
            ((binaryAddStep c (some a) none).1 :: work)
          simpa [binaryAddBitsAux, List.reverse_cons, List.append_assoc] using h
      | cons b right =>
          simp only [List.length_cons, Nat.succ_max_succ]
          rw [Function.iterate_succ_apply, Option.bind_some, add_step d c _ _ _ _ _ (by simp)]
          simp only [List.head?_cons, List.tail_cons,
            List.take_succ_cons, List.take_zero, List.singleton_append]
          rw [ih]
          simp [binaryAddBitsAux, List.reverse_cons, List.append_assoc]

private theorem restore_cons (b : Bool) (digits saved value work : List Bool) :
    computer.step (cfg (some .restore) initial [] digits [] saved value (b :: work)) =
    some (cfg (some .restore) initial [] digits [] saved (b :: value) work) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, go, initial, state, observe,
    Function.update]
  funext k; cases k <;> rfl

private theorem restore_nil (digits saved value : List Bool) :
    computer.step (cfg (some .restore) initial [] digits [] saved value []) =
    some (cfg (some .factorRestore) initial [] digits [] saved value []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, go, initial, state, observe]

theorem restore_run (digits saved value work : List Bool) :
    (fun q => q.bind computer.step)^[work.length + 1]
      (some (cfg (some .restore) initial [] digits [] saved value work)) =
    some (cfg (some .factorRestore) initial [] digits [] saved (work.reverse ++ value) []) := by
  induction work generalizing value with
  | nil => simpa using restore_nil digits saved value
  | cons b work ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, restore_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem check_cons (b d : Bool) (digits factor value : List Bool) :
    computer.step (cfg (some .check) (state d false) [] (b :: digits) factor [] value []) =
    some (cfg (some .shift) (state b false) [] digits factor [] value []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, observe]
  funext k; cases k <;> rfl

private theorem shift_step (b : Bool) (digits factor value : List Bool) :
    computer.step (cfg (some .shift) (state b false) [] digits factor [] value []) =
    some (cfg (some (if b then .add else .check)) (state b false)
      [] digits factor [] (shift value) []) := by
  cases value <;> simp [computer, FinTM2.step, cfg, program, contents, Alphabet,
    state, observe, shift, Function.update]
  funext k; cases k <;> rfl

private theorem check_nil (d : Bool) (factor value : List Bool) :
    computer.step (cfg (some .check) (state d false) [] [] factor [] value []) =
    some (cfg (some .drain) initial [] [] factor [] value []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, initial, go, observe]

private theorem drain_cons (b : Bool) (factor value : List Bool) :
    computer.step (cfg (some .drain) initial [] [] (b :: factor) [] value []) =
    some (cfg (some .drain) initial [] [] factor [] value []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, initial, go, observe]
  funext k; cases k <;> rfl

private theorem drain_nil (value : List Bool) :
    computer.step (cfg (some .drain) initial [] [] [] [] value []) =
    some (cfg none initial [] [] [] [] value []) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, state, initial, go, observe]

theorem drain_run (factor value : List Bool) :
    (fun q => q.bind computer.step)^[factor.length + 1]
      (some (cfg (some .drain) initial [] [] factor [] value [])) =
    some (cfg none initial [] [] [] [] value []) := by
  induction factor with
  | nil => simpa using drain_nil value
  | cons b factor ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, drain_cons, ih]


/-- Exact cost of one Horner digit, including both stack-restoration passes. -/
def roundTime (bit : Bool) (n a : ℕ) : ℕ :=
  if bit then max (2 * a).size n.size + (next bit n a).size + n.size + 5 else 2

theorem two_steps (bit d : Bool) (digits : List Bool) (n a : ℕ) :
    (fun q => q.bind computer.step)^[2]
      (some (cfg (some .check) (state d false) [] (bit :: digits) (encodeNat n) [] (encodeNat a) [])) =
    some (cfg (some (if bit then .add else .check)) (state bit false)
      [] digits (encodeNat n) [] (encodeNat (2 * a)) []) := by
  rw [show 2 = 1 + 1 from rfl, Function.iterate_succ_apply, Option.bind_some, check_cons]
  simpa only [Function.iterate_one, Option.bind_some, shift_encode] using
    shift_step bit digits (encodeNat n) (encodeNat a)

/-- A complete multiplication digit computes `2*a + bit*n` on binary stacks. -/
theorem round_run (bit d : Bool) (digits : List Bool) (n a : ℕ) :
    (fun q => q.bind computer.step)^[roundTime bit n a]
      (some (cfg (some .check) (state d false) [] (bit :: digits) (encodeNat n) [] (encodeNat a) [])) =
    some (cfg (some .check) initial [] digits (encodeNat n) [] (encodeNat (next bit n a)) []) := by
  cases bit
  · simpa [roundTime, next, initial] using two_steps false d digits n a
  · rw [show roundTime true n a =
        ((n.size + 1) + ((next true n a).size + 1) + (max (2 * a).size n.size + 1)) + 2 by
          simp [roundTime]; omega,
      Function.iterate_add_apply, two_steps]
    simp only [↓reduceIte]
    rw [Function.iterate_add_apply]
    have hadd := add_run (encodeNat (2 * a)) (encodeNat n) true false digits [] []
    simp only [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size,
      binaryAddBitsAux_encodeNat, List.append_nil] at hadd
    rw [hadd, Function.iterate_add_apply]
    have hr := restore_run digits (encodeNat n).reverse [] (encodeNat (2 * a + n)).reverse
    simp only [List.length_reverse, LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size,
      List.reverse_reverse, List.append_nil] at hr
    simp only [next, Bool.toNat_true, Nat.one_mul]
    rw [hr]
    have hf := factor_restore_run digits [] (encodeNat n).reverse (encodeNat (2 * a + n))
    simpa only [List.length_reverse, LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size,
      List.reverse_reverse, List.append_nil] using hf

/-- Exact recursive execution time; all loop-exit tests are counted. -/
def loopTime : List Bool → ℕ → ℕ → ℕ
  | [], n, _ => n.size + 2
  | bit :: bits, n, a => roundTime bit n a + loopTime bits n (next bit n a)

theorem loop_run (bits : List Bool) (n a : ℕ) :
    (fun q => q.bind computer.step)^[loopTime bits n a]
      (some (cfg (some .check) initial [] bits (encodeNat n) [] (encodeNat a) [])) =
    some (cfg none initial [] [] [] [] (encodeNat (horner bits n a)) []) := by
  simp only [initial]
  induction bits generalizing a with
  | nil =>
      rw [loopTime, show n.size + 2 = (n.size + 1) + 1 by omega,
        Function.iterate_succ_apply, Option.bind_some, check_nil false]
      simpa only [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size,
        horner, List.foldl_nil, initial] using drain_run (encodeNat n) (encodeNat a)
  | cons bit bits ih =>
      have h := round_run bit false bits n a
      simp only [initial] at h
      rw [loopTime, Nat.add_comm, Function.iterate_add_apply, h, ih]
      rfl

theorem roundTime_le (bit : Bool) (n a : ℕ) :
    roundTime bit n a ≤ 3 * max a.size n.size + 8 := by
  have hs := next_size bit n a
  have hd : (2 * a).size ≤ a.size + 1 := by
    have h := congrArg List.length (shift_encode a)
    simp only [shift] at h
    split at h <;> simp only [List.length_nil, List.length_cons,
      LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size] at h <;> omega
  cases bit <;> simp only [roundTime, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The accumulator grows by at most two bits per remaining Horner digit.
This deliberately coarse bound is polynomial in binary lengths. -/
theorem loopTime_le (bits : List Bool) (n a : ℕ) :
    loopTime bits n a ≤
      (bits.length + 1) * (3 * (max a.size n.size + 2 * bits.length) + 10) := by
  induction bits generalizing a with
  | nil => simp only [loopTime, List.length_nil]; omega
  | cons bit bits ih =>
      have hr := roundTime_le bit n a
      have hn := next_size bit n a
      have hmax : max (next bit n a).size n.size ≤ max a.size n.size + 2 := by omega
      have ht := ih (next bit n a)
      have hm := Nat.mul_le_mul_left (bits.length + 1)
        (show 3 * (max (next bit n a).size n.size + 2 * bits.length) + 10 ≤
          3 * (max a.size n.size + 2 + 2 * bits.length) + 10 by omega)
      simp only [loopTime, List.length_cons]
      nlinarith

/-- Full exact cost: route inputs, restore the factor, execute, then drain it. -/
def runtime (m n : ℕ) : ℕ := m.size + 2 * n.size + 2 + loopTime (encodeNat m).reverse n 0

theorem run (m n : ℕ) :
    (fun q => q.bind computer.step)^[runtime m n]
      (some (cfg (some .route) initial (wire (encodeNat m) (encodeNat n)) [] [] [] [] [])) =
    some (cfg none initial [] [] [] [] (encodeNat (m * n)) []) := by
  rw [show runtime m n = ((loopTime (encodeNat m).reverse n 0 + (n.size + 1)) +
      (n.size + 1)) + m.size by unfold runtime; omega,
    Function.iterate_add_apply]
  have hl := route_left_run (encodeNat m) ((encodeNat n).map Sum.inr) [] []
  simp only [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size, List.append_nil] at hl
  rw [show wire (encodeNat m) (encodeNat n) =
    (encodeNat m).map Sum.inl ++ (encodeNat n).map Sum.inr from rfl, hl, Function.iterate_add_apply]
  have hr := route_right_run (encodeNat n) (encodeNat m).reverse []
  simp only [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size, List.append_nil] at hr
  rw [hr, Function.iterate_add_apply]
  have hf := factor_restore_run (encodeNat m).reverse [] (encodeNat n).reverse []
  simp only [List.length_reverse, LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size,
    List.reverse_reverse, List.append_nil] at hf
  rw [hf]
  simpa only [horner_encode, show encodeNat 0 = [] from rfl] using loop_run (encodeNat m).reverse n 0

/-- A quadratic bound in the actual input symbol length. -/
theorem runtime_le (m n : ℕ) : runtime m n ≤ 6 * (m.size + n.size + 1)^2 +
    12 * (m.size + n.size + 1) := by
  have h := loopTime_le (encodeNat m).reverse n 0
  simp only [List.length_reverse, LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size,
    Nat.size_zero, Nat.zero_max] at h
  unfold runtime
  nlinarith

/-- The canonical product has at most the sum of the two input bit widths. -/
theorem output_length_le (x : ℕ × ℕ) :
    (encodeNat (x.1 * x.2)).length ≤ (encoding.encode x).length := by
  rw [encode_eq, wire_length]
  simp only [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size]
  exact RationalVerifierBounds.Fraction.size_mul x.1 x.2

private theorem init_eq (bits : List Symbol) :
    initList computer bits = cfg (some .route) initial bits [] [] [] [] [] := by
  unfold initList cfg; congr; funext k; cases k <;> rfl

private theorem halt_eq (bits : List Bool) :
    haltList computer bits = cfg none initial [] [] [] [] bits [] := by
  unfold haltList cfg; congr; funext k; cases k <;> rfl

/-- Actual finite-machine execution; no arithmetic or runtime premise. -/
def outputsInTime (x : ℕ × ℕ) :
    TM2OutputsInTime computer (encoding.encode x) (some (encodeNat (x.1 * x.2)))
      (6 * ((encoding.encode x).length + 1)^2 + 12 * ((encoding.encode x).length + 1)) where
  steps := runtime x.1 x.2
  evals_in_steps := by
    change (fun q => q.bind computer.step)^[_] (some (initList computer (encoding.encode x))) =
      some (haltList computer (encodeNat (x.1 * x.2)))
    rw [init_eq, halt_eq, encode_eq]
    exact run x.1 x.2
  steps_le_m := by
    change runtime x.1 x.2 ≤ 6 * ((wire (encodeNat x.1) (encodeNat x.2)).length + 1)^2 +
      12 * ((wire (encodeNat x.1) (encodeNat x.2)).length + 1)
    rw [wire_length]
    simpa only [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size] using runtime_le x.1 x.2

noncomputable def computableInPolyTime :
    LeanNPHardness.TM2ComputableInPolyTime encoding LeanNPHardness.finEncodingNatBool
      (fun x => x.1 * x.2) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 6 * (Polynomial.X + 1)^2 + 12 * (Polynomial.X + 1)
  outputsFun x := by
    simpa [LeanNPHardness.finEncodingNatBool, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
      using outputsInTime x

#print axioms horner_encode
#print axioms add_run
#print axioms round_run
#print axioms loop_run
#print axioms run
#print axioms runtime_le
#print axioms outputsInTime
#print axioms computableInPolyTime

end PhdThesisLean.BinaryMultiplication
