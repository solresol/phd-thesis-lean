import PhdThesisLean.RationalSum

/-!
# Internal paired-column encoding for rational dot products

Each pair retains the two original Boolean fraction words and adds one list
delimiter. This runtime-length representation is the input to the product
traversal; producing it from a regression record is a separate machine phase.
-/
namespace PhdThesisLean.RationalDotProduct

open RationalVerifierBounds
open LeanNPHardness (FinEncoding)

def pairField (x : Fraction × Fraction) : List (Option Bool) :=
  (RationalArithmetic.encode x).map some ++ [none]

def pairFields (xs : List (Fraction × Fraction)) : List (Option Bool) :=
  xs.flatMap pairField

def readPairs : List (Option Bool) → List Bool → Option (List (Fraction × Fraction))
  | [], [] => some []
  | [], _ :: _ => none
  | some b :: bs, acc => readPairs bs (b :: acc)
  | none :: bs, acc => do
      let x ← RationalArithmetic.decode acc.reverse
      let xs ← readPairs bs []
      pure (x :: xs)

theorem readPairs_bits (bits : List Bool) (tail : List (Option Bool)) (acc : List Bool) :
    readPairs (bits.map some ++ tail) acc = readPairs tail (bits.reverse ++ acc) := by
  induction bits generalizing acc with
  | nil => rfl
  | cons b bits ih => simpa [readPairs, List.reverse_cons, List.append_assoc] using ih (b :: acc)

@[simp] theorem readPairs_pairFields (xs : List (Fraction × Fraction)) :
    readPairs (pairFields xs) [] = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [pairFields] at ih ⊢
      simp [pairField, List.append_assoc, readPairs_bits, readPairs, ih]

def encoding : FinEncoding (List (Fraction × Fraction)) where
  Γ := Option Bool
  encode := pairFields
  decode bits := readPairs bits []
  decode_encode := readPairs_pairFields
  ΓFin := inferInstance

def multiply (x : Fraction × Fraction) : Fraction := x.1.mul x.2

theorem pairFields_length (xs : List (Fraction × Fraction)) :
    (pairFields xs).length = (xs.map (fun x => (RationalArithmetic.encode x).length + 1)).sum := by
  simp [pairFields, pairField, List.length_flatMap]

theorem count_le_length (xs : List (Fraction × Fraction)) :
    xs.length ≤ (pairFields xs).length := by
  induction xs with
  | nil => simp [pairFields]
  | cons x xs ih =>
      simp only [pairFields, List.flatMap_cons, pairField, List.length_append, List.length_map,
        List.length_cons] at *
      omega

end PhdThesisLean.RationalDotProduct
