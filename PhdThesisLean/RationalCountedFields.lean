import PhdThesisLean.BoundedBinaryCount

/-!
# Exact counted fraction-prefix traversal

Read exactly the declared number of stored fractions. Retain each fraction's
original bits and the untouched suffix, including unreduced fractions and
multiplicities. This module proves the language; the companion machine proves
actual time, and a later wrapper joins the bounded binary count parser.
-/
namespace PhdThesisLean.RationalCountedFields

open RationalVerifierBounds
open RationalFractionPrefix (parse header body more prepend)
set_option backward.isDefEq.respectTransparency false

abbrev Result := Option (List (List Bool) × List Bool)

def parseFields : ℕ → List Bool → Result
  | 0, bits => some ([], bits)
  | n+1, bits => do
      let (part, rest) ← parse bits
      let (parts, tail) ← parseFields n rest
      pure (part :: parts, tail)

def wire (parts : List (List Bool)) : List (Option Bool) :=
  parts.flatMap fun part => part.map some ++ [none]

def render (saved : List (Option Bool)) : Result → List (Option Bool)
  | none => []
  | some (parts, tail) => saved.reverse ++ wire parts ++ none :: tail.map some

def finish (n : ℕ) (r : RationalFractionPrefix.Result) : Result := do
  let (part, rest) ← r
  let (parts, tail) ← parseFields n rest
  pure (part :: parts, tail)

theorem parseFields_zero (bits : List Bool) : parseFields 0 bits = some ([], bits) := rfl

theorem parseFields_succ (n : ℕ) (bits : List Bool) :
    parseFields (n+1) bits = finish n (parse bits) := rfl

def output (n : ℕ) (bits : List Bool) : List (Option Bool) :=
  render [] (parseFields n bits)

theorem render_finish_prepend (n : ℕ) (saved : List (Option Bool))
    (b : Bool) (r : RationalFractionPrefix.Result) :
    render saved (finish n (prepend b r)) = render (some b :: saved) (finish n r) := by
  cases r with
  | none => rfl
  | some p =>
      rcases p with ⟨part, rest⟩
      cases hp : parseFields n rest <;>
        simp [prepend, finish, hp, render, wire, List.reverse_cons, List.append_assoc]

theorem render_finish_empty (n : ℕ) (saved : List (Option Bool)) (bits : List Bool) :
    render saved (finish n (some ([], bits))) =
      render (none :: saved) (parseFields n bits) := by
  cases hp : parseFields n bits <;>
    simp [finish, hp, render, wire, List.reverse_cons, List.append_assoc]

/-- Exact language on arbitrary words, not just a serializer round trip. -/
theorem parseFields_iff (n : ℕ) (bits : List Bool) (parts : List (List Bool))
    (tail : List Bool) :
    parseFields n bits = some (parts, tail) ↔
      ∃ xs : List Fraction, xs.length = n ∧ parts = xs.map Fraction.encode ∧
        bits = xs.flatMap Fraction.encode ++ tail := by
  induction n generalizing bits parts tail with
  | zero =>
      simp only [parseFields, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨[], rfl, rfl, rfl⟩
      · rintro ⟨xs, hx, rfl, rfl⟩
        have : xs = [] := by simpa using hx
        simp [this]
  | succ n ih =>
      constructor
      · intro h
        cases hp : parse bits with
        | none => simp [parseFields, hp] at h
        | some pair =>
            rcases pair with ⟨part, rest⟩
            cases hps : parseFields n rest with
            | none => simp [parseFields, hp, hps] at h
            | some pair =>
                rcases pair with ⟨ps, ts⟩
                obtain ⟨x, rfl, rfl⟩ := (RationalFractionPrefix.parse_iff _ _ _).1 hp
                obtain ⟨xs, hn, rfl, rfl⟩ := (ih _ _ _).1 hps
                simp [parseFields, hp, hps] at h
                rcases h with ⟨rfl, rfl⟩
                exact ⟨x :: xs, by simp [hn], rfl, by simp [List.append_assoc]⟩
      · rintro ⟨xs, hn, rfl, rfl⟩
        cases xs with
        | nil => simp at hn
        | cons x xs =>
            have hxs : xs.length = n := by simpa using hn
            simp [List.append_assoc, parseFields, (ih _ _ _).2 ⟨xs, hxs, rfl, rfl⟩]

@[simp] theorem parseFields_encode_append (xs : List Fraction) (tail : List Bool) :
    parseFields xs.length (xs.flatMap Fraction.encode ++ tail) =
      some (xs.map Fraction.encode, tail) :=
  (parseFields_iff _ _ _ _).2 ⟨xs, rfl, rfl, rfl⟩

theorem output_nil_iff (n : ℕ) (bits : List Bool) :
    output n bits = [] ↔ parseFields n bits = none := by
  unfold output
  cases parseFields n bits <;> simp [render]

theorem output_success_iff (n : ℕ) (bits : List Bool) :
    output n bits ≠ [] ↔ ∃ xs : List Fraction, ∃ tail,
      xs.length = n ∧ bits = xs.flatMap Fraction.encode ++ tail := by
  rw [ne_eq, output_nil_iff]
  constructor
  · intro h
    cases hp : parseFields n bits with
    | none => exact False.elim (h hp)
    | some pair =>
        obtain ⟨xs, hn, _, he⟩ := (parseFields_iff _ _ _ _).1 hp
        exact ⟨xs, pair.2, hn, he⟩
  · rintro ⟨xs, tail, rfl, rfl⟩
    simp

theorem wire_length (parts : List (List Bool)) :
    (wire parts).length = parts.flatten.length + parts.length := by
  induction parts with
  | nil => rfl
  | cons p ps ih => simp [wire, List.flatten_cons, List.length_flatMap] at *; omega

theorem output_length_le (n : ℕ) (bits : List Bool) :
    (output n bits).length ≤ bits.length + n + 1 := by
  cases hp : parseFields n bits with
  | none => simp [output, hp, render]
  | some pair =>
      rcases pair with ⟨parts, tail⟩
      obtain ⟨xs, hn, rfl, rfl⟩ := (parseFields_iff _ _ _ _).1 hp
      rw [output, ← hn, parseFields_encode_append]
      simp [render, wire_length, ← List.flatMap_def, Nat.add_assoc]
      omega


end PhdThesisLean.RationalCountedFields
