import PhdThesisLean.RationalBinaryVerifier

/-!
# Soundness for arbitrary certificates of a fixed rational instance

A certificate is an arbitrary Boolean word. It cannot alter the dimensions,
observations or threshold in the preceding instance. Successful certificates
contain exactly the required number of fractions, possibly unreduced, and no
trailing data. Their rational values witness the original threshold problem.
-/
namespace PhdThesisLean.RationalCertificateSoundness

open LeanNPHardness RationalVerifierBounds
open RationalWitnessEncoding (encodeInput)
open RationalCertificateBroadcast (observations)
set_option backward.isDefEq.respectTransparency false

def encodeCertificate (xs : List Fraction) : List Bool :=
  BinaryNatLists.encodeNat xs.length ++ xs.flatMap Fraction.encode

theorem validation_original_append {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (w : List Bool) (hr : 0 < r) :
    RationalRecordValidation.output (encodeInput A y B ++ w) =
      (((RationalCertificateBroadcast.listEncoding RationalCertificateBroadcast.rowEncoding).encode
        (observations A y)).map RationalRectangularFields.rowCell ++ [.dataEnd],
        RationalCertificateTail.output d ((Fraction.ofRat B).encode ++ w)) := by
  simp only [RationalRecordValidation.output,RationalRecordValidation.prepared,
    RationalRecordRouting.prepare,RationalRecordData.output_original_append A y B w hr,
    RationalRecordRouting.split_internalRows,RationalNorm.ofRat_encode]

theorem prefix_unique (a b : Fraction) (u v : List Bool)
    (h : a.encode ++ u = b.encode ++ v) : a.encode = b.encode ∧ u = v := by
  have ha := (RationalFractionPrefix.parse_iff (a.encode ++ u) a.encode u).2 ⟨a,rfl,rfl⟩
  have hb := (RationalFractionPrefix.parse_iff (b.encode ++ v) b.encode v).2 ⟨b,rfl,rfl⟩
  rw [h,hb] at ha
  exact ⟨(congrArg Prod.fst (Option.some.inj ha)).symm,
    (congrArg Prod.snd (Option.some.inj ha)).symm⟩

/-- The boundary between the fixed instance and an arbitrary certificate is
preserved; acceptance cannot reinterpret any part of the instance. -/
theorem validated_iff {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (w : List Bool) (hr : 0 < r) :
    RationalRecordValidation.Validated (encodeInput A y B ++ w) ↔
      ∃ xs : List Fraction, xs.length = d ∧ w = encodeCertificate xs := by
  rw [RationalRecordValidation.Validated,validation_original_append A y B w hr]
  simp only [ne_eq,List.append_eq_nil_iff,List.cons_ne_nil,and_false,not_false_eq_true,true_and]
  have ht := RationalCertificateTail.output_success_iff d ((Fraction.ofRat B).encode ++ w)
  constructor
  · intro h
    obtain ⟨b,xs,hlen,he⟩ := ht.1 h
    have hu := prefix_unique (Fraction.ofRat B) b w (encodeCertificate xs)
      (by simpa [encodeCertificate,List.append_assoc] using he)
    exact ⟨xs,hlen,hu.2⟩
  · rintro ⟨xs,hlen,rfl⟩
    exact ht.2 ⟨Fraction.ofRat B,xs,hlen,by simp [encodeCertificate,List.append_assoc]⟩

noncomputable def storedSource {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (xs : List Fraction) (hx : xs.length = d) :
    RationalRegressionInternal.Source :=
  ⟨(xs,observations A y),by
    intro row hrow
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
    simp [hx]⟩

theorem parser_stored {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (xs : List Fraction) (hx : xs.length = d) (hr : 0 < r) :
    RationalRecordParser.output (encodeInput A y B ++ encodeCertificate xs) =
      RationalRecordSource.wire (storedSource A y xs hx,Fraction.ofRat B) := by
  rw [RationalRecordParser.output_eq,ite_eq_left
    ((validated_iff A y B _ hr).2 ⟨xs,hx,rfl⟩),
    validation_original_append A y B _ hr]
  have ht : RationalCertificateTail.output d ((Fraction.ofRat B).encode ++ encodeCertificate xs) =
      RationalCertificateTail.result xs (Fraction.ofRat B) := by
    simpa [encodeCertificate,hx,List.append_assoc] using
      RationalCertificateTail.output_encode (Fraction.ofRat B) xs
  rw [ht,RationalCertificateTail.result_encode]
  rfl

/-- Coefficients are the values of the stored fractions, without requiring
canonical or relatively prime numerator/denominator pairs. -/
def coefficients {d : ℕ} (xs : List Fraction) (hx : xs.length = d) : Fin d → ℚ :=
  fun i => (xs.get ⟨i.val,by omega⟩).value

theorem values_coefficients {d : ℕ} (xs : List Fraction) (hx : xs.length = d) :
    xs.map Fraction.value = List.ofFn (coefficients xs hx) := by
  apply List.ext_get
  · simp [hx]
  · intro n h₁ h₂
    simp [coefficients]

variable (p : ℕ) [Fact p.Prime]

theorem map_zip_values (as xs : List Fraction) :
    (as.zip xs).map (fun pair => pair.1.value * pair.2.value) =
      ((as.map Fraction.value).zip (xs.map Fraction.value)).map (fun pair => pair.1 * pair.2) := by
  induction as generalizing xs with
  | nil => simp
  | cons a as ih => cases xs <;> simp [ih]

theorem stored_correct {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (xs : List Fraction) (hx : xs.length = d) :
    RationalRegressionInternal.check p (storedSource A y xs hx,Fraction.ofRat B) = true ↔
      RationalWitnesses.loss p A y (coefficients xs hx) ≤ B := by
  rw [RationalBinaryVerifier.check_stored_values,RationalWitnesses.loss_eq_thesis]
  simp only [storedSource,observations,List.map_ofFn,Fraction.value_ofRat]
  have hv := values_coefficients xs hx
  have hz (i : Fin r) :
      ((List.ofFn fun j => Fraction.ofRat (A i j)).zip xs).map
        (fun pair => pair.1.value * pair.2.value) =
      List.ofFn (fun j => A i j * coefficients xs hx j) := by
    rw [map_zip_values]
    simp only [List.map_ofFn,Function.comp_def,Fraction.value_ofRat,hv]
    have he := List.zip_map' (l := List.ofFn (fun j : Fin d => j))
      (f := fun j => A i j) (g := coefficients xs hx)
    simp only [List.map_ofFn,Function.comp_def] at he
    rw [he,List.map_ofFn]
    rfl
  simp [Function.comp_def,hz,List.sum_ofFn,Matrix.mulVec,dotProduct]

theorem check_certificate {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (xs : List Fraction) (hx : xs.length = d) (hr : 0 < r) :
    RationalBinaryVerifier.check p (encodeInput A y B ++ encodeCertificate xs) = true ↔
      RationalWitnesses.loss p A y (coefficients xs hx) ≤ B := by
  rw [RationalBinaryVerifier.check,RationalBinaryVerifier.source_of_wire _ _
    (parser_stored A y B xs hx hr)]
  exact stored_correct p A y B xs hx

/-- Soundness has no length, syntax or reducedness assumption on the word. -/
theorem sound {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (w : List Bool) (hr : 0 < r)
    (h : RationalBinaryVerifier.check p (encodeInput A y B ++ w) = true) :
    ∃ β : Fin d → ℚ, RationalWitnesses.loss p A y β ≤ B := by
  have hv : RationalRecordValidation.Validated (encodeInput A y B ++ w) := by
    by_contra hn
    rw [RationalBinaryVerifier.check_invalid p _ hn] at h
    contradiction
  obtain ⟨xs,hx,rfl⟩ := (validated_iff A y B w hr).1 hv
  exact ⟨coefficients xs hx,(check_certificate p A y B xs hx hr).1 h⟩

#print axioms validated_iff
#print axioms parser_stored
#print axioms stored_correct
#print axioms check_certificate
#print axioms sound

end PhdThesisLean.RationalCertificateSoundness
