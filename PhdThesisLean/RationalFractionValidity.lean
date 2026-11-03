import PhdThesisLean.RationalNormRouting

/-!
# Exact validity of signed binary fraction strings

The accepted language is exactly the existing `Fraction.encode` image. Stored
fractions may be unreduced, but each magnitude is canonical, zero has positive
sign, and the denominator is positive. This file proves the language contract;
`RationalFractionValidityMachine` supplies the actual all-input machine bound.
-/

namespace PhdThesisLean.RationalFractionValidity

open Computability
open RationalVerifierBounds
open LeanNPHardness

set_option backward.isDefEq.respectTransparency false

/-- Last payload bit, with the empty-payload policy supplied separately. -/
def lastBit : Bool → List Bool → Bool
  | a, [] => a
  | _, b :: bs => lastBit b bs

theorem lastBit_encodePosNum (a : Bool) (n : PosNum) :
    lastBit a (encodePosNum n) = true := by
  induction n generalizing a <;> simp_all [encodePosNum, lastBit]

theorem lastBit_encodeNat (a : Bool) (n : ℕ) :
    lastBit a (encodeNat n) = true ↔ n ≠ 0 ∨ a = true := by
  have h : ∀ m : Num, lastBit a (encodeNum m) = true ↔ (m : ℕ) ≠ 0 ∨ a = true := by
    intro m
    cases m with
    | zero => simp [encodeNum, lastBit]
    | pos p => simp [encodeNum, lastBit_encodePosNum, (PosNum.to_nat_pos p).ne']
  simpa [encodeNat] using h n

private theorem lastBit_pos (a : Bool) (b : Bool) (bs : List Bool)
    (h : lastBit a (b :: bs) = true) : ∃ p : PosNum, encodePosNum p = b :: bs := by
  induction bs generalizing a b with
  | nil =>
      cases b <;> simp_all [lastBit]
      exact ⟨.one, rfl⟩
  | cons c cs ih =>
      obtain ⟨p, hp⟩ := ih b c (by simpa [lastBit] using h)
      cases b
      · exact ⟨.bit0 p, by simp [encodePosNum, hp]⟩
      · exact ⟨.bit1 p, by simp [encodePosNum, hp]⟩

/-- The final high bit characterizes canonical binary words, including zero. -/
theorem lastBit_iff (a : Bool) (bs : List Bool) :
    lastBit a bs = true ↔ ∃ n : ℕ, encodeNat n = bs ∧ (n ≠ 0 ∨ a = true) := by
  constructor
  · intro h
    cases bs with
    | nil => exact ⟨0, rfl, Or.inr h⟩
    | cons b bs =>
        obtain ⟨p, hp⟩ := lastBit_pos a b bs h
        refine ⟨(p : ℕ), ?_, Or.inl (PosNum.to_nat_pos _).ne'⟩
        simpa [encodeNat, encodeNum] using hp
  · rintro ⟨n, rfl, h⟩
    exact (lastBit_encodeNat a n).2 h

/-- Read the counted payload and check its high bit (or empty policy). -/
def readBody : ℕ → Bool → List Bool → Option (List Bool)
  | 0, a, bits => if a then some bits else none
  | _ + 1, _, [] => none
  | n + 1, _, b :: bits => readBody n b bits

/-- The unary frame count lives on a stack in the machine implementation. -/
def readHeader : ℕ → Bool → List Bool → Option (List Bool)
  | _, _, [] => none
  | n, a, false :: bits => readBody n a bits
  | n, a, true :: bits => readHeader (n + 1) a bits

theorem readBody_iff (n : ℕ) (a : Bool) (input rest : List Bool) :
    readBody n a input = some rest ↔
      ∃ bs, bs.length = n ∧ lastBit a bs = true ∧ input = bs ++ rest := by
  induction n generalizing a input with
  | zero =>
      cases a <;> simp [readBody, lastBit]
  | succ n ih =>
      cases input with
      | nil =>
          simp only [readBody, reduceCtorEq, false_iff]
          rintro ⟨bs, hn, _, he⟩
          have := congrArg List.length he
          simp at this
          omega
      | cons b input =>
          rw [readBody, ih]
          constructor
          · rintro ⟨bs, hn, hl, rfl⟩
            exact ⟨b :: bs, by simp [hn], hl, rfl⟩
          · rintro ⟨bs, hn, hl, he⟩
            cases bs with
            | nil => simp at hn
            | cons c bs =>
                simp only [List.cons_append, List.cons.injEq] at he
                obtain ⟨rfl, he⟩ := he
                exact ⟨bs, by simpa using hn, hl, he⟩

theorem readHeader_iff (n : ℕ) (a : Bool) (input rest : List Bool) :
    readHeader n a input = some rest ↔
      ∃ k bs, bs.length = n + k ∧ lastBit a bs = true ∧
        input = List.replicate k true ++ false :: (bs ++ rest) := by
  induction input generalizing n with
  | nil =>
      simp only [readHeader, reduceCtorEq, false_iff]
      rintro ⟨k, bs, _, _, he⟩
      have := congrArg List.length he
      simp at this
  | cons b input ih =>
      cases b with
      | false =>
          rw [readHeader, readBody_iff]
          constructor
          · rintro ⟨bs, hn, hl, rfl⟩
            exact ⟨0, bs, by simpa using hn, hl, rfl⟩
          · rintro ⟨k, bs, hn, hl, he⟩
            cases k with
            | zero => exact ⟨bs, by simpa using hn, hl, by simpa using he⟩
            | succ k => simp [List.replicate_succ] at he
      | true =>
          rw [readHeader, ih]
          constructor
          · rintro ⟨k, bs, hn, hl, he⟩
            exact ⟨k + 1, bs, by omega, hl, by simp [List.replicate_succ, he]⟩
          · rintro ⟨k, bs, hn, hl, he⟩
            cases k with
            | zero => simp at he
            | succ k =>
                exact ⟨k, bs, by omega, hl, by simpa [List.replicate_succ] using he⟩

/-- Exact prefix-language characterization; the unused suffix is retained. -/
theorem field_iff (a : Bool) (input rest : List Bool) :
    readHeader 0 a input = some rest ↔
      ∃ n, (n ≠ 0 ∨ a = true) ∧ input = BinaryNatLists.encodeNat n ++ rest := by
  rw [readHeader_iff]
  constructor
  · rintro ⟨k, bs, hk, hl, he⟩
    obtain ⟨n, rfl, hn⟩ := (lastBit_iff a bs).1 hl
    refine ⟨n, hn, ?_⟩
    simpa [BinaryNatLists.encodeNat, BinaryNatLists.frame, hk, List.append_assoc] using he
  · rintro ⟨n, hn, rfl⟩
    exact ⟨(encodeNat n).length, encodeNat n, by simp,
      (lastBit_encodeNat a n).2 hn, by
        simp [BinaryNatLists.encodeNat, BinaryNatLists.frame, List.append_assoc]⟩

/-- After the numerator, require one positive denominator and complete exhaustion. -/
def continueField (denominator : Bool) (result : Option (List Bool)) : Bool :=
  match result with
  | none => false
  | some rest => if denominator then rest.isEmpty
      else (readHeader 0 false rest).any List.isEmpty

def valid : List Bool → Bool
  | [] => false
  | sign :: bits => continueField false (readHeader 0 (!sign) bits)

theorem continueField_true (d : Bool) (result : Option (List Bool)) :
    continueField d result = true ↔ ∃ rest, result = some rest ∧
      (if d then rest = [] else readHeader 0 false rest = some []) := by
  cases d <;> cases result <;> simp [continueField, Option.any]
  rename_i rest
  cases readHeader 0 false rest <;> simp

/-- Every accepted string, including adversarial inputs, is exactly a stored
fraction encoding. No gcd or coprimality condition is imposed. -/
theorem valid_iff (bits : List Bool) :
    valid bits = true ↔ ∃ x : Fraction, x.encode = bits := by
  cases bits with
  | nil =>
      simp only [valid, Bool.false_eq_true, false_iff]
      rintro ⟨x, hx⟩
      simp [Fraction.encode, SmithEncoding.encodeInt] at hx
  | cons sign bits =>
      rw [valid, continueField_true]
      simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨rest, hnum, hden⟩
        obtain ⟨n, hn, he⟩ := (field_iff (!sign) bits rest).1 hnum
        obtain ⟨d, hd, hdenc⟩ := (field_iff false rest []).1 hden
        simp only [Bool.false_eq_true, or_false, List.append_nil] at hd hdenc
        subst rest bits
        cases sign with
        | false =>
            refine ⟨⟨(n : ℤ), d, Nat.pos_of_ne_zero hd⟩, ?_⟩
            simp [Fraction.encode, SmithEncoding.encodeInt]
        | true =>
            have hn0 : n ≠ 0 := by simpa using hn
            refine ⟨⟨-(n : ℤ), d, Nat.pos_of_ne_zero hd⟩, ?_⟩
            simp [Fraction.encode, SmithEncoding.encodeInt, Nat.pos_of_ne_zero hn0]
      · rintro ⟨x, hx⟩
        have hsign : decide (x.num < 0) = sign := by
          simpa [Fraction.encode, SmithEncoding.encodeInt] using
            congrArg List.head? hx
        have hbits : bits = BinaryNatLists.encodeNat x.num.natAbs ++
            BinaryNatLists.encodeNat x.den := by
          simpa [Fraction.encode, SmithEncoding.encodeInt] using
            (congrArg List.tail hx).symm
        refine ⟨BinaryNatLists.encodeNat x.den, (field_iff _ _ _).2 ?_,
          (field_iff _ _ _).2 ⟨x.den, Or.inl x.positive.ne', by simp⟩⟩
        refine ⟨x.num.natAbs, ?_, hbits⟩
        by_cases hn : x.num = 0
        · subst sign
          simp [hn]
        · exact Or.inl (by simpa using hn)

@[simp] theorem valid_encode (x : Fraction) : valid x.encode = true :=
  (valid_iff x.encode).2 ⟨x, rfl⟩

theorem valid_rational (q : ℚ) : valid (RationalWitnessEncoding.encodeRat q) = true :=
  valid_encode (Fraction.ofRat q)

end PhdThesisLean.RationalFractionValidity
