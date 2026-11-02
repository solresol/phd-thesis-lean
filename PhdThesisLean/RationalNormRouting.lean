import PhdThesisLean.FixedBasePowerMachine
import LeanNPHardness.PairExchange

/-!
# Binary routing for exact rational norms

The input is the existing signed, framed, unreduced fraction encoding. A finite
machine removes the sign and frames, retains the zero test, and exposes both
canonical magnitudes for the checked valuation-power machines. This module
also supplies a decoding left inverse; it does not claim rejection of every
malformed input by the routing machine.
-/

namespace PhdThesisLean.RationalNorm

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool TM2ComputableInPolyTime)
open RationalVerifierBounds

set_option backward.isDefEq.respectTransparency false

/-- The existing wire format, with a decoder retaining unreduced fields. -/
def decodeFraction (bits : List Bool) : Option Fraction := do
  let (z, tail) ← SmithEncoding.decodeIntPrefix bits
  let (d, rest) ← LeanNPHardness.BinaryNatLists.decodeNatPrefix tail
  if hd : 0 < d then
    if rest.isEmpty then some ⟨z, d, hd⟩ else none
  else none

@[simp] theorem decodeFraction_encode (x : Fraction) : decodeFraction x.encode = some x := by
  have hd := LeanNPHardness.BinaryNatLists.decodeNatPrefix_encodeNat_append x.den []
  simp only [List.append_nil] at hd
  cases x
  simp [decodeFraction, Fraction.encode, *]

def fractionEncoding : FinEncoding Fraction where
  Γ := Bool
  encode := Fraction.encode
  decode := decodeFraction
  decode_encode := decodeFraction_encode
  ΓFin := inferInstance

abbrev Fields := (ℕ × ℕ) × Bool
abbrev Symbol := Sum (Sum Bool Bool) Bool

def pairEncoding := LeanNPHardness.PairEncoding.finEncoding finEncodingNatBool finEncodingNatBool

def fieldsEncoding : FinEncoding Fields :=
  LeanNPHardness.PairEncoding.finEncoding pairEncoding finEncodingBoolBool

def prepare (x : Fraction) : Fields := ((x.num.natAbs, x.den), decide (x.num = 0))

def wire (a b : List Bool) (zero : Bool) : List Symbol :=
  a.map (fun bit => Sum.inl (Sum.inl bit)) ++
  b.map (fun bit => Sum.inl (Sum.inr bit)) ++ [Sum.inr zero]

@[simp] theorem fields_encode (x : Fields) :
    fieldsEncoding.encode x = wire (encodeNat x.1.1) (encodeNat x.1.2) x.2 := by
  simp [fieldsEncoding, pairEncoding, LeanNPHardness.PairEncoding.finEncoding,
    finEncodingNatBool, finEncodingBoolBool, wire, List.map_map, Function.comp_def]

namespace Prepare

inductive Stack
  | input | count | scratch | output
  deriving DecidableEq, Fintype

inductive Label
  | sign | prefix (denominator : Bool) | payload (denominator : Bool) | next (denominator : Bool)
  | reverse
  deriving DecidableEq, Fintype

structure State where
  bit : Option Bool
  symbol : Option Symbol
  nonzero : Bool
  deriving DecidableEq, Fintype

def initial : State := ⟨none, none, false⟩
def observe (s : State) (b : Option Bool) : State := {s with bit := b}
def tag (denominator bit : Bool) : Symbol :=
  Sum.inl (if denominator then Sum.inr bit else Sum.inl bit)
def mark (denominator : Bool) (s : State) : State :=
  {s with bit := none, nonzero := s.nonzero || !denominator}
def Alphabet : Stack → Type
  | .input | .count => Bool
  | .scratch | .output => Symbol

def program : Label → TM2.Stmt Alphabet Label State
  | .sign => .pop .input observe (.goto fun _ => .prefix false)
  | .prefix d =>
      .pop .input observe <|
        .branch (fun s => s.bit.isSome)
          (.branch (fun s => s.bit.getD false)
            (.push .count (fun _ => true) (.goto fun _ => .prefix d))
            (.goto fun _ => .payload d))
          (.load (fun _ => initial) .halt)
  | .payload d =>
      .pop .count observe <|
        .branch (fun s => s.bit.isSome)
          (.pop .input observe <|
            .branch (fun s => s.bit.isSome)
              (.push .scratch (fun s => tag d (s.bit.getD false)) <|
                .load (mark d) (.goto fun _ => .payload d))
              (.load (fun _ => initial) .halt))
          (.goto fun _ => .next d)
  | .next false => .goto fun _ => .prefix true
  | .next true =>
      .push .scratch (fun s => Sum.inr (!s.nonzero)) (.goto fun _ => .reverse)
  | .reverse =>
      .pop .scratch (fun s b => {s with symbol := b}) <|
        .branch (fun s => s.symbol.isSome)
          (.push .output (fun s => s.symbol.getD (Sum.inr false)) (.goto fun _ => .reverse))
          (.load (fun _ => initial) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .sign
  σ := State
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program

def contents (input count : List Bool) (scratch output : List Symbol) :
    (k : Stack) → List (Alphabet k)
  | .input => input
  | .count => count
  | .scratch => scratch
  | .output => output

def cfg (l : Option Label) (s : State) (input count : List Bool)
    (scratch output : List Symbol) : computer.Cfg := ⟨l, s, contents input count scratch output⟩

private theorem prefix_true (d : Bool) (s : State) (input count : List Bool)
    (scratch output : List Symbol) :
    computer.step (cfg (some (.prefix d)) s (true :: input) count scratch output) =
      some (cfg (some (.prefix d)) (observe s (some true)) input (true :: count) scratch output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, observe, Function.update]
  funext k; cases k <;> rfl

private theorem prefix_false (d : Bool) (s : State) (input count : List Bool)
    (scratch output : List Symbol) :
    computer.step (cfg (some (.prefix d)) s (false :: input) count scratch output) =
      some (cfg (some (.payload d)) (observe s (some false)) input count scratch output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, observe, Function.update]
  funext k; cases k <;> rfl

theorem prefix_run (d : Bool) (n : ℕ) (s : State) (input count : List Bool)
    (scratch output : List Symbol) :
    (fun q => q.bind computer.step)^[n + 1]
      (some (cfg (some (.prefix d)) s (List.replicate n true ++ false :: input) count scratch output)) =
    some (cfg (some (.payload d)) (observe s (some false)) input
      (List.replicate n true ++ count) scratch output) := by
  induction n generalizing s count with
  | zero => simpa using prefix_false d s input count scratch output
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [Function.iterate_succ_apply, Option.bind_some, prefix_true, ih]
      simp [observe, LeanNPHardness.MachinePrimitives.replicate_true_append_cons]

private theorem payload_cons (d b : Bool) (s : State) (input count : List Bool)
    (scratch output : List Symbol) :
    computer.step (cfg (some (.payload d)) s (b :: input) (true :: count) scratch output) =
      some (cfg (some (.payload d)) (mark d s) input count (tag d b :: scratch) output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, observe, mark, Function.update]
  funext k; cases k <;> rfl

private theorem payload_nil (d : Bool) (s : State) (input : List Bool)
    (scratch output : List Symbol) :
    computer.step (cfg (some (.payload d)) s input [] scratch output) =
      some (cfg (some (.next d)) (observe s none) input [] scratch output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, observe, Function.update]

/-- Each payload is read once; the length counter lives on a stack. -/
theorem payload_run (d : Bool) (bits input : List Bool) (scratch output : List Symbol)
    (s : State) :
    (fun q => q.bind computer.step)^[bits.length + 1]
      (some (cfg (some (.payload d)) s (bits ++ input)
        (List.replicate bits.length true) scratch output)) =
    some (cfg (some (.next d))
      ⟨none, s.symbol, s.nonzero || (!d && !bits.isEmpty)⟩ input []
      ((bits.map (tag d)).reverse ++ scratch) output) := by
  induction bits generalizing scratch s with
  | nil => simpa [observe] using payload_nil d s input scratch output
  | cons b bits ih =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append]
      rw [Function.iterate_succ_apply, Option.bind_some, payload_cons, ih]
      simp [mark, List.reverse_cons, List.append_assoc, Bool.or_assoc]
      cases d <;> cases s.nonzero <;> simp

private theorem reverse_cons (b : Symbol) (s : State) (scratch output : List Symbol) :
    computer.step (cfg (some .reverse) s [] [] (b :: scratch) output) =
      some (cfg (some .reverse) {s with symbol := some b} [] [] scratch (b :: output)) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet, Function.update]
  funext k; cases k <;> rfl

private theorem reverse_nil (s : State) (output : List Symbol) :
    computer.step (cfg (some .reverse) s [] [] [] output) =
      some (cfg none initial [] [] [] output) := by
  simp [computer, FinTM2.step, cfg, program, contents, Alphabet]

theorem reverse_run (scratch output : List Symbol) (s : State) :
    (fun q => q.bind computer.step)^[scratch.length + 1]
      (some (cfg (some .reverse) s [] [] scratch output)) =
    some (cfg none initial [] [] [] (scratch.reverse ++ output)) := by
  induction scratch generalizing output s with
  | nil => simpa using reverse_nil s output
  | cons b scratch ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, reverse_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem next_step (d : Bool) (z : Bool) (input : List Bool) (scratch : List Symbol) :
    computer.step (cfg (some (.next d)) ⟨none, none, z⟩ input [] scratch []) =
      some (if d then cfg (some .reverse) ⟨none, none, z⟩ input [] (Sum.inr (!z) :: scratch) []
        else cfg (some (.prefix true)) ⟨none, none, z⟩ input [] scratch []) := by
  cases d <;> simp [computer, FinTM2.step, cfg, program, contents, Alphabet]
  funext k; cases k <;> rfl

/-- Exact routing of signed, framed binary fields, including empty magnitudes. -/
theorem run (sign : Bool) (a b : List Bool) :
    (fun q => q.bind computer.step)^[3 * (a.length + b.length) + 9]
      (some (cfg (some .sign) initial
        (sign :: (LeanNPHardness.BinaryNatLists.frame a ++ LeanNPHardness.BinaryNatLists.frame b))
        [] [] [])) =
    some (cfg none initial [] [] [] (wire a b a.isEmpty)) := by
  have start : computer.step (cfg (some .sign) initial
      (sign :: (LeanNPHardness.BinaryNatLists.frame a ++ LeanNPHardness.BinaryNatLists.frame b)) [] [] []) =
      some (cfg (some (.prefix false)) (observe initial (some sign))
        (LeanNPHardness.BinaryNatLists.frame a ++ LeanNPHardness.BinaryNatLists.frame b) [] [] []) := by
    simp [computer, FinTM2.step, cfg, program, contents, Alphabet, observe]
    funext k; cases k <;> rfl
  rw [show 3 * (a.length + b.length) + 9 =
      (a.length + b.length + 2 + 1 + (b.length + 1) + (b.length + 1) + 1 +
        (a.length + 1) + (a.length + 1)) + 1 by omega,
    Function.iterate_succ_apply, Option.bind_some, start]
  simp only [LeanNPHardness.BinaryNatLists.frame, List.append_assoc, List.cons_append]
  rw [Function.iterate_add_apply, prefix_run]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply, payload_run]
  simp only [observe, initial, Bool.false_or, Bool.not_false, Bool.true_and]
  rw [Function.iterate_succ_apply, Option.bind_some, next_step]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Function.iterate_add_apply, prefix_run]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply]
  have hb := payload_run true b [] ((a.map (tag false)).reverse) []
    (observe ⟨none, none, !a.isEmpty⟩ (some false))
  simp only [List.append_nil] at hb
  rw [hb]
  simp only [observe, Bool.not_true, Bool.false_and, Bool.or_false]
  rw [Function.iterate_succ_apply, Option.bind_some, next_step]
  simp only [↓reduceIte, Bool.not_not]
  have h := reverse_run (Sum.inr a.isEmpty ::
    (b.map (tag true)).reverse ++ (a.map (tag false)).reverse) []
    ⟨none, none, !a.isEmpty⟩
  have ht0 : tag false = (fun bit => Sum.inl (Sum.inl bit)) := rfl
  have ht1 : tag true = (fun bit => Sum.inl (Sum.inr bit)) := rfl
  simpa [wire, ht0, ht1, initial, List.reverse_append, List.reverse_cons, List.map_map,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

private theorem init_eq (bits : List Bool) :
    initList computer bits = cfg (some .sign) initial bits [] [] [] := by
  unfold initList cfg; congr; funext k; cases k <;> rfl
private theorem halt_eq (bits : List Symbol) :
    haltList computer bits = cfg none initial [] [] [] bits := by
  unfold haltList cfg; congr; funext k; cases k <;> rfl

def outputsInTime (x : Fraction) :
    TM2OutputsInTime computer x.encode (some (fieldsEncoding.encode (prepare x)))
      (2 * x.encode.length + 3) where
  steps := 3 * ((encodeNat x.num.natAbs).length + (encodeNat x.den).length) + 9
  evals_in_steps := by
    change (fun q => q.bind computer.step)^[_] (some (initList computer x.encode)) =
      some (haltList computer (fieldsEncoding.encode (prepare x)))
    rw [init_eq, halt_eq, fields_encode]
    have hz : (encodeNat x.num.natAbs).isEmpty = decide (x.num = 0) := by
      apply Bool.eq_iff_iff.mpr
      rw [List.isEmpty_iff_length_eq_zero, decide_eq_true_eq,
        LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size, Nat.size_eq_zero, Int.natAbs_eq_zero]
    simpa [Fraction.encode, SmithEncoding.encodeInt, LeanNPHardness.BinaryNatLists.encodeNat,
      prepare, hz] using run (decide (x.num < 0)) (encodeNat x.num.natAbs) (encodeNat x.den)
  steps_le_m := by
    simp only [Fraction.encode_length, LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size]
    omega

/-- Actual finite-machine parsing and routing, linear in raw input bits. -/
noncomputable def computableInPolyTime : TM2ComputableInPolyTime fractionEncoding fieldsEncoding prepare where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 3
  outputsFun x := by
    simpa [fractionEncoding, Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] using outputsInTime x

end Prepare
end PhdThesisLean.RationalNorm
