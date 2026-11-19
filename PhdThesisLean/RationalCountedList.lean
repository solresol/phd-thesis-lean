import PhdThesisLean.RationalCountedFieldsMachine

/-!
# Total polynomial-time parsing of counted binary rational lists

Compose bounded binary count parsing with the proved finite field traversal.
Every raw binary word either rejects or yields exactly the declared number of
valid fraction words followed by its unmodified suffix. This validates data
and certificate lists; rectangular record compatibility is a separate step.
-/
namespace PhdThesisLean.RationalCountedList

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open LeanNPHardness
open RationalVerifierBounds
open RationalCountedFields (parseFields wire)
set_option backward.isDefEq.respectTransparency false

abbrev Source := Option (ℕ × List Bool)

def sourceWord : Source → List (Option Bool)
  | none => []
  | some (n, bits) => RationalCountedFields.Machine.input n bits

def unaryDecode : List (Option Bool) → Option (ℕ × List Bool)
  | [] => none
  | none :: bits => some (0, bits.filterMap id)
  | some _ :: bits => (unaryDecode bits).map fun p => (p.1+1, p.2)

theorem unaryDecode_input (n : ℕ) (bits : List Bool) :
    unaryDecode (RationalCountedFields.Machine.input n bits) = some (n, bits) := by
  induction n with
  | zero => simp [RationalCountedFields.Machine.input, unaryDecode, List.filterMap_map]
  | succ n ih =>
      simpa [RationalCountedFields.Machine.input, List.replicate_succ, unaryDecode]
        using congrArg (Option.map fun p : ℕ × List Bool => (p.1+1, p.2)) ih

def sourceDecode (xs : List (Option Bool)) : Option Source :=
  if xs = [] then some none else (unaryDecode xs).map some

theorem source_decode_encode (x : Source) : sourceDecode (sourceWord x) = some x := by
  cases x with
  | none => rfl
  | some pair =>
      rcases pair with ⟨n, bits⟩
      have hn : RationalCountedFields.Machine.input n bits ≠ [] := by
        simp [RationalCountedFields.Machine.input]
      simp [sourceDecode, sourceWord, hn, unaryDecode_input]

def sourceEncoding : FinEncoding Source where
  Γ := Option Bool
  encode := sourceWord
  decode := sourceDecode
  decode_encode := source_decode_encode
  ΓFin := inferInstance

def boundedSource (xs : List Bool) : Source := do
  let (n, bits) ← BoundedBinaryCount.parsed xs
  if n ≤ bits.length then some (n, bits) else none

theorem boundedSource_of_parsed (bits rest : List Bool) (n : ℕ)
    (hp : BoundedBinaryCount.parsed bits = some (n, rest)) :
    boundedSource bits = if n ≤ rest.length then some (n, rest) else none := by
  unfold boundedSource
  rw [hp]
  rfl

@[simp] theorem boundedSource_encode_append (n : ℕ) (rest : List Bool) :
    boundedSource (BinaryNatLists.encodeNat n ++ rest) =
      if n ≤ rest.length then some (n, rest) else none :=
  boundedSource_of_parsed _ _ _ (BoundedBinaryCount.parsed_encode_append n rest)

theorem sourceWord_boundedSource (xs : List Bool) :
    sourceWord (boundedSource xs) = BoundedBinaryCount.output xs := by
  cases hp : BoundedBinaryCount.parsed xs with
  | none => simp [boundedSource, hp, sourceWord, BoundedBinaryCount.output, BoundedBinaryCount.bounded]
  | some pair =>
      rcases pair with ⟨n, bits⟩
      simp [boundedSource, hp, BoundedBinaryCount.output, BoundedBinaryCount.bounded,
        BoundedBinaryCount.Machine.output]
      split <;> simp [sourceWord, RationalCountedFields.Machine.input]

/-- The exact physical output of the existing total bounded count machine. -/
noncomputable def countComputableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding sourceEncoding boundedSource where
  toTM2ComputableAux := BoundedBinaryCount.computableInPolyTime.toTM2ComputableAux
  time := BoundedBinaryCount.computableInPolyTime.time
  outputsFun xs := by
    simpa only [sourceEncoding, sourceWord_boundedSource,
      RationalFractionPrefix.Machine.outputEncoding] using!
        BoundedBinaryCount.computableInPolyTime.outputsFun xs

def traverse : Source → List (Option Bool)
  | none => []
  | some (n, bits) => RationalCountedFields.output n bits

noncomputable def traversalComputableInPolyTime :
    TM2ComputableInPolyTime sourceEncoding RationalFractionPrefix.Machine.outputEncoding traverse where
  tm := RationalCountedFields.Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 13 * Polynomial.X + 6
  outputsFun x := by
    cases x with
    | none => simpa [sourceEncoding, sourceWord, traverse,
        RationalFractionPrefix.Machine.outputEncoding, Equiv.refl] using
          RationalCountedFields.Machine.emptyOutputsInTime
    | some pair =>
        rcases pair with ⟨n, bits⟩
        simpa [sourceEncoding, sourceWord, traverse,
          RationalFractionPrefix.Machine.outputEncoding, Equiv.refl] using
            RationalCountedFields.Machine.outputsInTime n bits

def output (xs : List Bool) : List (Option Bool) := traverse (boundedSource xs)

/-- Polynomial time on every raw binary word, including malformed and oversized
counts and malformed fields encountered at any point in a list. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding
      RationalFractionPrefix.Machine.outputEncoding output :=
  MachineComposition.compositionComputableInPolyTime _ _ _ _ _
    countComputableInPolyTime traversalComputableInPolyTime

theorem fields_count_le (xs : List Fraction) :
    xs.length ≤ (xs.flatMap Fraction.encode).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : 0 < x.encode.length := by
        simp [Fraction.encode, SmithEncoding.encodeInt]
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      omega

/-- No count-capacity side condition remains in the accepted language:
every valid fraction contributes at least one payload bit. -/
theorem output_success_iff (bits : List Bool) :
    output bits ≠ [] ↔ ∃ xs : List Fraction, ∃ tail,
      bits = BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail := by
  constructor
  · intro h
    cases hp : BoundedBinaryCount.parsed bits with
    | none => simp [output, boundedSource, hp, traverse] at h
    | some pair =>
        rcases pair with ⟨n, rest⟩
        have he := (BoundedBinaryCount.parsed_iff _ _ _).1 hp
        by_cases hb : n ≤ rest.length
        · have hs : RationalCountedFields.output n rest ≠ [] := by
            simpa [output, boundedSource, hp, hb, traverse] using h
          obtain ⟨xs, tail, rfl, rfl⟩ := (RationalCountedFields.output_success_iff _ _).1 hs
          exact ⟨xs, tail, by simpa [List.append_assoc] using he⟩
        · simp [output, boundedSource, hp, hb, traverse] at h
  · rintro ⟨xs, tail, rfl⟩
    have hb : xs.length ≤ (xs.flatMap Fraction.encode ++ tail).length := by
      have := fields_count_le xs
      simp only [List.length_append]; omega
    simp only [output, List.append_assoc, boundedSource_encode_append]
    rw [ite_eq_left hb]
    simp [traverse, RationalCountedFields.output, RationalCountedFields.render]

theorem output_nil_iff (bits : List Bool) :
    output bits = [] ↔ ¬ ∃ xs : List Fraction, ∃ tail,
      bits = BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail := by
  simpa using not_congr (output_success_iff bits)

/-- Exact preservation of every field bit, multiplicity, order and suffix. -/
theorem output_encode_append (xs : List Fraction) (tail : List Bool) :
    output (BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode ++ tail) =
      wire (xs.map Fraction.encode) ++ none :: tail.map some := by
  have hb : xs.length ≤ (xs.flatMap Fraction.encode ++ tail).length := by
    have := fields_count_le xs
    simp only [List.length_append]; omega
  simp only [output, List.append_assoc, boundedSource_encode_append]
  rw [ite_eq_left hb]
  simp [traverse, RationalCountedFields.output, RationalCountedFields.render]

theorem output_length_le (bits : List Bool) : (output bits).length ≤ 2*bits.length+1 := by
  cases hp : BoundedBinaryCount.parsed bits with
  | none => simp [output, boundedSource, hp, traverse]
  | some pair =>
      rcases pair with ⟨n, rest⟩
      have he := (BoundedBinaryCount.parsed_iff _ _ _).1 hp
      by_cases hb : n ≤ rest.length
      · have ht := RationalCountedFields.output_length_le n rest
        rw [output, boundedSource_of_parsed bits rest n hp]
        rw [ite_eq_left hb]
        change (RationalCountedFields.output n rest).length ≤ _
        simp only [he, List.length_append]
        omega
      · simp [output, boundedSource, hp, hb, traverse]

/-- Instantiates the actual composed time polynomial in original input bits. -/
noncomputable def outputsInTime (bits : List Bool) :
    Turing.TM2OutputsInTime computableInPolyTime.tm
      (bits.map computableInPolyTime.inputAlphabet.symm)
      (some ((output bits).map computableInPolyTime.outputAlphabet.symm))
      (computableInPolyTime.time.eval bits.length) :=
  computableInPolyTime.outputsFun bits

/-- Original rational data/certificate format, with an arbitrary next section. -/
theorem output_encodeRats_append (qs : List ℚ) (tail : List Bool) :
    output (RationalWitnessEncoding.encodeRats qs ++ tail) =
      wire (qs.map RationalWitnessEncoding.encodeRat) ++ none :: tail.map some := by
  simpa [RationalWitnessEncoding.encodeRats, List.flatMap_map, List.map_map,
    show (fun q => (Fraction.ofRat q).encode) = RationalWitnessEncoding.encodeRat from rfl,
    Function.comp_def] using
      output_encode_append (qs.map Fraction.ofRat) tail

#print axioms computableInPolyTime
#print axioms output_success_iff
#print axioms output_nil_iff
#print axioms output_length_le
#print axioms output_encodeRats_append
#print axioms outputsInTime

end PhdThesisLean.RationalCountedList
