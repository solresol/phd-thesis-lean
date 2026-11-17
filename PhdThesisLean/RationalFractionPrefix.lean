import PhdThesisLean.RationalFractionValidity

/-!
# Retaining exact fraction prefixes

The parser returns the original signed/framed fraction word and its untouched
suffix. It accepts exactly stored fractions, including unreduced ones. A later
module implements this function on every Boolean word with a finite TM2.
-/
namespace PhdThesisLean.RationalFractionPrefix

open Computability LeanNPHardness RationalVerifierBounds
open RationalFractionValidity (lastBit lastBit_iff lastBit_encodeNat)
set_option backward.isDefEq.respectTransparency false

abbrev Result := Option (List Bool × List Bool)

def prepend (b : Bool) (r : Result) : Result := r.map fun p => (b :: p.1, p.2)

def body : ℕ → Bool → List Bool → Result
  | 0, a, bits => if a then some ([], bits) else none
  | _ + 1, _, [] => none
  | n + 1, _, b :: bits => prepend b (body n b bits)

def header : ℕ → Bool → List Bool → Result
  | _, _, [] => none
  | n, a, false :: bits => prepend false (body n a bits)
  | n, a, true :: bits => prepend true (header (n + 1) a bits)

theorem prepend_eq (b : Bool) (r : Result) (part rest : List Bool) :
    prepend b r = some (part, rest) ↔
      ∃ tail, part = b :: tail ∧ r = some (tail, rest) := by
  cases r with
  | none => simp [prepend]
  | some p => rcases p with ⟨xs, ys⟩; simp [prepend, Prod.mk.injEq, eq_comm]

theorem body_iff (n : ℕ) (a : Bool) (input part rest : List Bool) :
    body n a input = some (part, rest) ↔
      part.length = n ∧ lastBit a part = true ∧ input = part ++ rest := by
  induction n generalizing a input part with
  | zero =>
      cases part with
      | nil => cases a <;> simp [body, lastBit, eq_comm]
      | cons b part => cases a <;> simp [body]
  | succ n ih =>
      cases input with
      | nil =>
          simp only [body, reduceCtorEq, false_iff]
          rintro ⟨hn, _, he⟩
          have := congrArg List.length he
          simp at this
          omega
      | cons b input =>
          rw [body, prepend_eq]
          cases part with
          | nil => simp
          | cons c part =>
              constructor
              · rintro ⟨tail, he, h⟩
                cases he
                obtain ⟨hn, hl, he⟩ := (ih _ _ _).1 h
                exact ⟨by simp [hn], hl, by simp [he]⟩
              · rintro ⟨hn, hl, he⟩
                have hbc : b = c := (List.cons.inj he).1
                subst c
                exact ⟨part, rfl, (ih _ _ _).2
                  ⟨by simpa using hn, hl, (List.cons.inj he).2⟩⟩

theorem header_iff (n : ℕ) (a : Bool) (input part rest : List Bool) :
    header n a input = some (part, rest) ↔
      ∃ k bs, bs.length = n + k ∧ lastBit a bs = true ∧
        part = List.replicate k true ++ false :: bs ∧ input = part ++ rest := by
  induction input generalizing n part with
  | nil =>
      simp only [header, reduceCtorEq, false_iff]
      rintro ⟨k, bs, _, _, rfl, he⟩
      have := congrArg List.length he
      simp at this
  | cons b input ih =>
      cases b with
      | false =>
          rw [header, prepend_eq]
          constructor
          · rintro ⟨bs, rfl, hb⟩
            obtain ⟨hn, hl, he⟩ := (body_iff _ _ _ _ _).1 hb
            exact ⟨0, bs, by simpa using hn, hl, rfl, by simp [he]⟩
          · rintro ⟨k, bs, hn, hl, rfl, he⟩
            cases k with
            | zero =>
                exact ⟨bs, rfl, (body_iff _ _ _ _ _).2
                  ⟨by simpa using hn, hl, by simpa using he⟩⟩
            | succ k => simp [List.replicate_succ] at he
      | true =>
          rw [header, prepend_eq]
          constructor
          · rintro ⟨part, rfl, hh⟩
            obtain ⟨k, bs, hn, hl, rfl, he⟩ := (ih _ _).1 hh
            exact ⟨k + 1, bs, by omega, hl, by simp [List.replicate_succ],
              by simp [he]⟩
          · rintro ⟨k, bs, hn, hl, rfl, he⟩
            cases k with
            | zero => simp at he
            | succ k =>
                refine ⟨List.replicate k true ++ false :: bs,
                  by simp [List.replicate_succ], (ih _ _).2 ?_⟩
                exact ⟨k, bs, by omega, hl, rfl, by simpa [List.replicate_succ] using he⟩

theorem field_iff (a : Bool) (input part rest : List Bool) :
    header 0 a input = some (part, rest) ↔
      ∃ n, (n ≠ 0 ∨ a = true) ∧ part = BinaryNatLists.encodeNat n ∧
        input = part ++ rest := by
  rw [header_iff]
  constructor
  · rintro ⟨k, bs, hk, hl, rfl, he⟩
    obtain ⟨n, rfl, hn⟩ := (lastBit_iff a bs).1 hl
    exact ⟨n, hn, by simp [BinaryNatLists.encodeNat, BinaryNatLists.frame, hk], he⟩
  · rintro ⟨n, hn, rfl, he⟩
    exact ⟨(encodeNat n).length, encodeNat n, by simp,
      (lastBit_encodeNat a n).2 hn, rfl, he⟩

/-- A completed numerator is followed by exactly one positive denominator. -/
def more (denominator : Bool) (r : Result) : Result :=
  if denominator then r else do
    let (part, tail) ← r
    let (den, rest) ← header 0 false tail
    pure (part ++ den, rest)

def parse : List Bool → Result
  | [] => none
  | b :: bits => prepend b (more false (header 0 (!b) bits))

theorem more_prepend (d b : Bool) (r : Result) :
    more d (prepend b r) = prepend b (more d r) := by
  cases d <;> cases r <;> simp [more, prepend]

theorem parse_iff (input part rest : List Bool) :
    parse input = some (part, rest) ↔
      ∃ x : Fraction, part = x.encode ∧ input = part ++ rest := by
  cases input with
  | nil =>
      simp only [parse, reduceCtorEq, false_iff]
      rintro ⟨x, rfl, he⟩
      simp [Fraction.encode, SmithEncoding.encodeInt] at he
  | cons sign input =>
      constructor
      · intro hp
        obtain ⟨joined, rfl, hj⟩ := (prepend_eq _ _ _ _).1 hp
        simp only [more, Bool.false_eq_true, ↓reduceIte] at hj
        cases hh : header 0 (!sign) input with
        | none => simp [hh] at hj
        | some pair =>
            rcases pair with ⟨num, tail⟩
            cases hd : header 0 false tail with
            | none => simp [hh, hd] at hj
            | some pair =>
                rcases pair with ⟨den, suffix⟩
                simp only [hh] at hj
                change (header 0 false tail).bind
                  (fun p => some (num ++ p.1, p.2)) = some (joined, rest) at hj
                rw [hd] at hj
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hj
                rcases hj with ⟨rfl, rfl⟩
                obtain ⟨n, hn, rfl, rfl⟩ := (field_iff _ _ _ _).1 hh
                obtain ⟨d, hpositive, rfl, rfl⟩ := (field_iff _ _ _ _).1 hd
                have hd0 : 0 < d := by simp only [Bool.false_eq_true, or_false] at hpositive; omega
                cases sign with
                | false =>
                    exact ⟨⟨n, d, hd0⟩, by simp [Fraction.encode, SmithEncoding.encodeInt],
                      by simp [List.append_assoc]⟩
                | true =>
                    have hn0 : 0 < n := by simp at hn; omega
                    exact ⟨⟨-(n : ℤ), d, hd0⟩,
                      by simp [Fraction.encode, SmithEncoding.encodeInt, hn0],
                      by simp [List.append_assoc]⟩
      · rintro ⟨x, rfl, he⟩
        have hs : decide (x.num < 0) = sign := by
          simpa [Fraction.encode, SmithEncoding.encodeInt] using (congrArg List.head? he).symm
        have hi : input = BinaryNatLists.encodeNat x.num.natAbs ++
            BinaryNatLists.encodeNat x.den ++ rest := by
          simpa [Fraction.encode, SmithEncoding.encodeInt] using congrArg List.tail he
        have hn := (field_iff (!sign) input (BinaryNatLists.encodeNat x.num.natAbs)
          (BinaryNatLists.encodeNat x.den ++ rest)).2
          ⟨x.num.natAbs, by
            by_cases hz : x.num = 0
            · simp [← hs, hz]
            · exact Or.inl (by simpa using hz), rfl, by simpa [List.append_assoc] using hi⟩
        have hd := (field_iff false (BinaryNatLists.encodeNat x.den ++ rest)
          (BinaryNatLists.encodeNat x.den) rest).2 ⟨x.den, Or.inl x.positive.ne', rfl, rfl⟩
        simp [parse, more, hn, hd, prepend, Fraction.encode, SmithEncoding.encodeInt, hs]

@[simp] theorem parse_encode_append (x : Fraction) (rest : List Bool) :
    parse (x.encode ++ rest) = some (x.encode, rest) :=
  (parse_iff _ _ _).2 ⟨x, rfl, rfl⟩

def render (saved : List (Option Bool)) (r : Result) : List (Option Bool) :=
  match r with
  | none => []
  | some (part, rest) => saved.reverse ++ part.map some ++ none :: rest.map some

def output (input : List Bool) : List (Option Bool) := render [] (parse input)

theorem render_prepend (saved : List (Option Bool)) (b : Bool) (r : Result) :
    render saved (prepend b r) = render (some b :: saved) r := by
  cases r <;> simp [render, prepend, List.reverse_cons, List.append_assoc]

@[simp] theorem output_encode_append (x : Fraction) (rest : List Bool) :
    output (x.encode ++ rest) = x.encode.map some ++ none :: rest.map some := by
  simp [output, render]

theorem output_length (input : List Bool) :
    (output input).length ≤ input.length + 1 := by
  unfold output
  cases hp : parse input with
  | none => simp [render]
  | some p =>
      rcases p with ⟨part, rest⟩
      obtain ⟨x, _, rfl⟩ := (parse_iff _ _ _).1 hp
      simp [render, Nat.add_assoc]

/-- Rejection means that no stored fraction is a prefix of the supplied word. -/
theorem parse_none_iff (input : List Bool) :
    parse input = none ↔ ¬ ∃ x : Fraction, ∃ rest, input = x.encode ++ rest := by
  constructor
  · intro h ⟨x, rest, he⟩
    subst input
    simp at h
  · intro h
    cases hp : parse input with
    | none => rfl
    | some p =>
        obtain ⟨x, he, hi⟩ := (parse_iff _ _ _).1 hp
        exact False.elim (h ⟨x, p.2, by simpa [he] using hi⟩)

theorem output_nil_iff (input : List Bool) :
    output input = [] ↔ parse input = none := by
  unfold output
  cases parse input <;> simp [render]

/-- The original rational serializer is accepted without normalizing its bits. -/
theorem output_rational_append (q : ℚ) (rest : List Bool) :
    output (RationalWitnessEncoding.encodeRat q ++ rest) =
      (RationalWitnessEncoding.encodeRat q).map some ++ none :: rest.map some :=
  output_encode_append (Fraction.ofRat q) rest

theorem successful_length (input : List Bool) (h : output input ≠ []) :
    (output input).length = input.length + 1 := by
  unfold output at h ⊢
  cases hp : parse input with
  | none => simp [hp, render] at h
  | some p =>
      obtain ⟨_, _, hi⟩ := (parse_iff _ _ _).1 hp
      simp [render, hi, Nat.add_assoc]

/-- Counts remain binary; this validates and retains their canonical frame,
without expanding the numeric value into unary. Zero counts are permitted. -/
def naturalOutput (input : List Bool) : List (Option Bool) :=
  render [] (header 0 true input)

theorem natural_iff (input part rest : List Bool) :
    header 0 true input = some (part, rest) ↔
      ∃ n, part = BinaryNatLists.encodeNat n ∧ input = part ++ rest := by
  simpa using field_iff true input part rest

@[simp] theorem naturalOutput_encode_append (n : ℕ) (rest : List Bool) :
    naturalOutput (BinaryNatLists.encodeNat n ++ rest) =
      (BinaryNatLists.encodeNat n).map some ++ none :: rest.map some := by
  have h := (natural_iff (BinaryNatLists.encodeNat n ++ rest)
    (BinaryNatLists.encodeNat n) rest).2 ⟨n, rfl, rfl⟩
  simp only [naturalOutput, h, render, List.reverse_nil, List.nil_append]

theorem naturalOutput_length (input : List Bool) :
    (naturalOutput input).length ≤ input.length + 1 := by
  unfold naturalOutput
  cases hp : header 0 true input with
  | none => simp [render]
  | some p =>
      obtain ⟨_, _, hi⟩ := (natural_iff _ _ _).1 hp
      simp [render, hi, Nat.add_assoc]

end PhdThesisLean.RationalFractionPrefix
