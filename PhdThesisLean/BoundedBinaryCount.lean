import PhdThesisLean.BoundedBinaryCountMachine

/-!
# Total polynomial-time bounded binary count parsing

On every raw Boolean word, validate a canonical framed natural prefix and
accept precisely when its value is at most the remaining payload length.
Success returns that many unary marks, a delimiter, and the unchanged payload.
Failure returns the empty word. Both phases are actual finite TM2 machines.
This is a bounded counter for record parsing, not a record-shape validator.
-/
namespace PhdThesisLean.BoundedBinaryCount

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)
open LeanNPHardness
open RationalFractionPrefix (naturalOutput header natural_iff)
set_option backward.isDefEq.respectTransparency false

abbrev Source := Option (ℕ × List Bool)

def sourceWord : Source → List (Option Bool)
  | none => []
  | some (n, rest) => Machine.input n rest

def sourceDecode (xs : List (Option Bool)) : Option Source :=
  if xs = [] then some none else (BinaryNatLists.decodeNatPrefix (xs.filterMap id)).map some

theorem source_decode_encode (x : Source) : sourceDecode (sourceWord x) = some x := by
  cases x with
  | none => rfl
  | some p =>
      rcases p with ⟨n, rest⟩
      simp [sourceDecode, sourceWord, Machine.input, List.filterMap_append,
        List.filterMap_map]

def sourceEncoding : FinEncoding Source where
  Γ := Option Bool
  encode := sourceWord
  decode := sourceDecode
  decode_encode := source_decode_encode
  ΓFin := inferInstance

/-- The decoder here only specifies the intermediate meaning. Its actual
implementation is the already proved retaining natural-prefix machine. -/
def parsed (xs : List Bool) : Source :=
  if naturalOutput xs = [] then none else BinaryNatLists.decodeNatPrefix xs

theorem sourceWord_parsed (xs : List Bool) : sourceWord (parsed xs) = naturalOutput xs := by
  cases hp : header 0 true xs with
  | none => simp [parsed, naturalOutput, hp, RationalFractionPrefix.render, sourceWord]
  | some pair =>
      rcases pair with ⟨part, rest⟩
      obtain ⟨n, rfl, rfl⟩ := (natural_iff _ _ _).1 hp
      simp [parsed, Machine.input, sourceWord]

@[simp] theorem parsed_encode_append (n : ℕ) (rest : List Bool) :
    parsed (BinaryNatLists.encodeNat n ++ rest) = some (n, rest) := by
  simp [parsed]

theorem parsed_iff (xs : List Bool) (n : ℕ) (rest : List Bool) :
    parsed xs = some (n, rest) ↔ xs = BinaryNatLists.encodeNat n ++ rest := by
  constructor
  · intro h
    cases hp : header 0 true xs with
    | none => simp [parsed, naturalOutput, hp, RationalFractionPrefix.render] at h
    | some pair =>
        obtain ⟨k, he, hi⟩ := (natural_iff _ _ _).1 hp
        rw [he] at hi
        subst xs
        simp only [parsed_encode_append, Option.some.injEq, Prod.mk.injEq] at h
        simp [h.1, h.2]
  · rintro rfl; exact parsed_encode_append n rest

noncomputable def prefixComputableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding sourceEncoding parsed where
  tm := RationalFractionPrefix.Machine.naturalComputer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X + 11
  outputsFun xs := by
    simpa [MachinePrimitives.RawBoolList.finEncoding, sourceEncoding, sourceWord_parsed,
      Equiv.refl] using RationalFractionPrefix.Machine.naturalOutputsInTime xs

def bounded : Source → List (Option Bool)
  | none => []
  | some (n, rest) => Machine.output n rest

noncomputable def boundedComputableInPolyTime :
    TM2ComputableInPolyTime sourceEncoding RationalFractionPrefix.Machine.outputEncoding bounded where
  tm := Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 10 * (Polynomial.X + 1)^2
  outputsFun x := by
    cases x with
    | none => simpa [sourceEncoding, sourceWord, bounded,
        RationalFractionPrefix.Machine.outputEncoding, Equiv.refl] using Machine.emptyOutputsInTime
    | some p => rcases p with ⟨n, rest⟩
                simpa [sourceEncoding, sourceWord, bounded,
                  RationalFractionPrefix.Machine.outputEncoding, Equiv.refl] using Machine.outputsInTime n rest

def output (xs : List Bool) : List (Option Bool) := bounded (parsed xs)

/-- Total on every raw binary word. Malformed or oversized counts reject. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding
      RationalFractionPrefix.Machine.outputEncoding output :=
  MachineComposition.compositionComputableInPolyTime _ _ _ _ _
    prefixComputableInPolyTime boundedComputableInPolyTime

@[simp] theorem output_encode_append (n : ℕ) (rest : List Bool) :
    output (BinaryNatLists.encodeNat n ++ rest) =
      if n ≤ rest.length then List.replicate n (some true) ++ none :: rest.map some else [] := by
  simp [output, bounded, Machine.output]

/-- Exact success language; the payload is retained, with its original order. -/
theorem output_success_iff (xs : List Bool) :
    output xs ≠ [] ↔ ∃ n rest, xs = BinaryNatLists.encodeNat n ++ rest ∧ n ≤ rest.length := by
  constructor
  · intro h
    cases hp : parsed xs with
    | none => simp [output, hp, bounded] at h
    | some pair =>
        rcases pair with ⟨n, rest⟩
        refine ⟨n, rest, (parsed_iff _ _ _).1 hp, ?_⟩
        by_contra hn
        simp [output, hp, bounded, Machine.output, hn] at h
  · rintro ⟨n, rest, rfl, hn⟩
    simp [hn]

theorem output_nil_iff (xs : List Bool) :
    output xs = [] ↔ ¬ ∃ n rest, xs = BinaryNatLists.encodeNat n ++ rest ∧ n ≤ rest.length := by
  simpa using not_congr (output_success_iff xs)

/-- The safely expanded counter and payload together have only linear size. -/
theorem output_length_le (xs : List Bool) : (output xs).length ≤ 2*xs.length+1 := by
  cases hp : parsed xs with
  | none => simp [output, hp, bounded]
  | some pair =>
      rcases pair with ⟨n, rest⟩
      have he := (parsed_iff _ _ _).1 hp
      simp only [output, hp, bounded, Machine.output]
      split <;> simp_all; omega

/-- Every count accepted by this parser is bounded in the original input bits. -/
theorem accepted_count_le (xs : List Bool) (n : ℕ) (rest : List Bool)
    (hp : parsed xs = some (n, rest)) (ha : output xs ≠ []) : n ≤ xs.length := by
  have he := (parsed_iff _ _ _).1 hp
  have hn : n ≤ rest.length := by
    by_contra hn
    simp [output, hp, bounded, Machine.output, hn] at ha
  simp only [he, List.length_append]
  omega

/-- Instantiates the composed machine on every raw word, with its proved
polynomial evaluated at the actual binary input length. -/
noncomputable def outputsInTime (xs : List Bool) :
    Turing.TM2OutputsInTime computableInPolyTime.tm
      (xs.map computableInPolyTime.inputAlphabet.symm)
      (some ((output xs).map computableInPolyTime.outputAlphabet.symm))
      (computableInPolyTime.time.eval xs.length) :=
  computableInPolyTime.outputsFun xs

open RationalWitnessEncoding

theorem count_le_payload (qs : List ℚ) : qs.length ≤ (qs.flatMap encodeRat).length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append, encodeRat_length]
      omega

/-- The bounded parser does not reject valid data or certificate list headers. -/
theorem output_encodeRats_append (qs : List ℚ) (tail : List Bool) :
    output (encodeRats qs ++ tail) =
      List.replicate qs.length (some true) ++ none :: (qs.flatMap encodeRat ++ tail).map some := by
  have h := count_le_payload qs
  rw [encodeRats, List.append_assoc, output_encode_append, ite_eq_left]
  simpa only [List.length_append] using Nat.le_add_right_of_le h

/-- Original row dimensions are bounded by their remaining encoded payload,
including zero rows. This does not yet check record shape. -/
theorem rowCount_accepted {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (tail : List Bool) :
    output (encodeInput A y B ++ tail) ≠ [] := by
  apply output_success_iff _ |>.2
  refine ⟨r, BinaryNatLists.encodeNat d ++ encodeRats (inputEntries A y) ++ encodeRat B ++ tail,
    by simp [encodeInput, List.append_assoc], ?_⟩
  have h := count_le_encodeRats (inputEntries A y)
  rw [inputEntries_length] at h
  simp only [List.length_append]
  nlinarith

/-- Positive row count ensures that a valid column dimension is payload-bounded,
as in the thesis. Zero-row inputs need a separate dimension convention. -/
theorem columnCount_accepted {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (tail : List Bool) (hr : 0 < r) :
    output (BinaryNatLists.encodeNat d ++ encodeRats (inputEntries A y) ++ encodeRat B ++ tail) ≠ [] := by
  apply output_success_iff _ |>.2
  refine ⟨d, encodeRats (inputEntries A y) ++ encodeRat B ++ tail,
    by simp [List.append_assoc], ?_⟩
  have h := count_le_encodeRats (inputEntries A y)
  rw [inputEntries_length] at h
  simp only [List.length_append]
  nlinarith

/-- The data count presented to the bounded parser is exactly `r*(d+1)`. -/
theorem dataCount_output {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (tail : List Bool) :
    output (encodeRats (inputEntries A y) ++ tail) =
      List.replicate (r*(d+1)) (some true) ++
        none :: ((inputEntries A y).flatMap encodeRat ++ tail).map some := by
  simpa only [inputEntries_length] using output_encodeRats_append (inputEntries A y) tail

/-- A genuine certificate's count becomes exactly `d` bounded unary marks. -/
theorem certificateCount_output {d : ℕ} (β : Fin d → ℚ) (tail : List Bool) :
    output (encodeRats (List.ofFn β) ++ tail) =
      List.replicate d (some true) ++ none :: ((List.ofFn β).flatMap encodeRat ++ tail).map some := by
  simpa only [List.length_ofFn] using output_encodeRats_append (List.ofFn β) tail

#print axioms outputsInTime
#print axioms rowCount_accepted
#print axioms columnCount_accepted
#print axioms dataCount_output
#print axioms certificateCount_output

#print axioms sourceWord_parsed
#print axioms parsed_iff
#print axioms computableInPolyTime
#print axioms output_success_iff
#print axioms output_nil_iff
#print axioms output_length_le

end PhdThesisLean.BoundedBinaryCount
