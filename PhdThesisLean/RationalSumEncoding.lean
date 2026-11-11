import PhdThesisLean.RationalAdditionMachine

/-!
# Serialized fraction lists and accumulation widths

This internal list representation retains every original fraction bit and adds
one delimiter per fraction. It is not the binary-counted regression input.
The accumulator budget is additive in the source bit lengths, even though the
fractions are never reduced by a gcd.
-/
namespace PhdThesisLean.RationalSum

open RationalVerifierBounds
open LeanNPHardness (FinEncoding)

def field (x : Fraction) : List (Option Bool) := x.encode.map some ++ [none]
def fields (xs : List Fraction) : List (Option Bool) := xs.flatMap field
def encode (x : Fraction × List Fraction) : List (Option Bool) := field x.1 ++ fields x.2

def readFields : List (Option Bool) → List Bool → Option (List Fraction)
  | [], [] => some []
  | [], _ :: _ => none
  | some b :: bs, acc => readFields bs (b :: acc)
  | none :: bs, acc => do
      let x ← RationalNorm.decodeFraction acc.reverse
      let xs ← readFields bs []
      pure (x :: xs)

theorem readFields_bits (bits : List Bool) (tail : List (Option Bool)) (acc : List Bool) :
    readFields (bits.map some ++ tail) acc = readFields tail (bits.reverse ++ acc) := by
  induction bits generalizing acc with
  | nil => rfl
  | cons b bits ih => simpa [readFields, List.reverse_cons, List.append_assoc] using ih (b :: acc)

@[simp] theorem readFields_fields (xs : List Fraction) : readFields (fields xs) [] = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [fields] at ih ⊢
      simp [field, List.append_assoc, readFields_bits, readFields, ih]

def decode (bits : List (Option Bool)) : Option (Fraction × List Fraction) := do
  let xs ← readFields bits []
  match xs with
  | [] => none
  | x :: xs => some (x, xs)

@[simp] theorem decode_encode (x : Fraction × List Fraction) : decode (encode x) = some x := by
  have h : encode x = fields (x.1 :: x.2) := rfl
  simp [decode, h]

def encoding : FinEncoding (Fraction × List Fraction) where
  Γ := Option Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

def width (x : Fraction) : ℕ := max x.num.natAbs.size x.den.size
def budget (z : Fraction) (xs : List Fraction) : ℕ :=
  width z + (xs.map (fun x => width x + 1)).sum

theorem bounded_width (x : Fraction) : x.Bounded (width x) :=
  ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩

theorem width_add (z x : Fraction) : width (z.add x) ≤ width z + width x + 1 := by
  have h := Fraction.bounded_add (bounded_width z) (bounded_width x)
  exact max_le h.1 h.2

theorem budget_step (z x : Fraction) (xs : List Fraction) :
    budget (z.add x) xs ≤ budget z (x :: xs) := by
  have := width_add z x
  simp only [budget, List.map_cons, List.sum_cons]
  omega

theorem budget_le_length (z : Fraction) (xs : List Fraction) :
    budget z xs ≤ (encode (z, xs)).length := by
  have hw (x : Fraction) : width x + 1 ≤ (field x).length := by
    simp only [width, field, List.length_append, List.length_map, List.length_singleton,
      Fraction.encode_length]
    omega
  have hs : (xs.map (fun x => width x + 1)).sum ≤ (fields xs).length := by
    induction xs with
    | nil => simp [fields]
    | cons x xs ih =>
        have := hw x
        simp only [fields, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at *
        omega
  have := hw z
  simp only [budget, encode, List.length_append]
  omega

theorem count_le_length (z : Fraction) (xs : List Fraction) :
    xs.length ≤ (encode (z, xs)).length := by
  have h : xs.length ≤ (fields xs).length := by
    induction xs with
    | nil => simp [fields]
    | cons x xs ih => simp only [fields, List.flatMap_cons, List.length_append,
        field, List.length_map, List.length_cons] at *; omega
  simp only [encode, List.length_append]
  omega

theorem accumulator_bounded {z : Fraction} {xs : List Fraction} {s : ℕ}
    (h : budget z xs ≤ s) : z.Bounded s :=
  (bounded_width z).mono (by unfold budget at h; omega)

theorem head_bounded {z x : Fraction} {xs : List Fraction} {s : ℕ}
    (h : budget z (x :: xs) ≤ s) : x.Bounded s :=
  (bounded_width x).mono (by simp only [budget, List.map_cons, List.sum_cons] at h; omega)

theorem fold_bounded (xs : List Fraction) (z : Fraction) :
    (xs.foldl Fraction.add z).Bounded (budget z xs) := by
  induction xs generalizing z with
  | nil => exact bounded_width z
  | cons x xs ih => exact (ih (z.add x)).mono (budget_step z x xs)

theorem prefix_bounded (xs : List Fraction) (z : Fraction) (k : ℕ) :
    ((xs.take k).foldl Fraction.add z).Bounded (budget z xs) := by
  induction xs generalizing z k with
  | nil => simpa [budget] using bounded_width z
  | cons x xs ih =>
      cases k with
      | zero => exact accumulator_bounded le_rfl
      | succ k => exact (ih (z.add x) k).mono (budget_step z x xs)

theorem output_length_le (x : Fraction × List Fraction) :
    (x.2.foldl Fraction.add x.1).encode.length ≤ 4 * (encode x).length + 3 := by
  exact (Fraction.encode_length_le (fold_bounded x.2 x.1)).trans
    (by have h := budget_le_length x.1 x.2;
        change budget x.1 x.2 ≤ (encode x).length at h; omega)

end PhdThesisLean.RationalSum
