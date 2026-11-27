import PhdThesisLean.RationalAffineData

/-!
# Affine summed rational regression is in NP

Instances retain their original binary encoding, before inserting a column of
ones. The machine parses those original bits, physically inserts the column,
and executes the existing certificate validation and arithmetic pipeline.
The classical choice of a matrix presentation below identifies the semantic
function only; it supplies neither an executed decoder nor a cost hypothesis.
-/
namespace PhdThesisLean.RationalAffineNP

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open LeanNPHardness RationalVerifierBounds
open LeanNPHardness.MachineComposition LeanNPHardness.MachineAdapters
open RationalRegressionNP (Instance encoding original)
open RationalWitnessEncoding (encodeInput encodeRats)
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
noncomputable section

structure Data where
  r : ℕ
  d : ℕ
  A : Matrix (Fin r) (Fin d) ℚ
  y : Fin r → ℚ
  B : ℚ
  positive : 0 < r

def Data.bits (x : Data) : List Bool := encodeInput x.A x.y x.B
theorem exists_data (x : Instance) : ∃ a : Data, a.bits = x.val := by
  obtain ⟨r,d,A,y,B,hr,he⟩ := x.property
  exact ⟨⟨r,d,A,y,B,hr⟩,he.symm⟩
def data (x : Instance) : Data := Classical.choose (exists_data x)
theorem data_bits (x : Instance) : (data x).bits = x.val := Classical.choose_spec (exists_data x)

def expanded (x : Instance × List Bool) : List Bool :=
  encodeInput (RegularisedCandidates.affineDesign (data x.1).A) (data x.1).y (data x.1).B ++ x.2

def validate (x : RationalRecordData.Result) : RationalRecordValidation.Result :=
  let z := RationalRecordRouting.prepare x
  (z.1,RationalCertificateTail.output z.2.1 z.2.2)

def validateComputableInPolyTime :
    TM2ComputableInPolyTime RationalRecordData.outputEncoding
      RationalRecordValidation.outputEncoding validate :=
  compositionComputableInPolyTime _ _ _ _ _ RationalRecordRouting.computableInPolyTime
    (pairRightComputableInPolyTime _ _ _ _ RationalCertificateTail.computableInPolyTime)

def finish (x : RationalRecordData.Result) : List RationalRecordAssembly.Out :=
  RationalRecordAssembly.assemble
    (RationalRecordParser.guard (RationalRecordValidation.outputEncoding.encode (validate x)))

def finishComputableInPolyTime :
    TM2ComputableInPolyTime RationalRecordData.outputEncoding RationalRecordAssembly.outputEncoding finish :=
  compositionComputableInPolyTime _ _ _ _ _
    (compositionComputableInPolyTime _ _ _ _ _ validateComputableInPolyTime
      RationalRecordParser.guardComputableInPolyTime)
    RationalRecordAssembly.computableInPolyTime

def parsed (x : Instance × List Bool) : RationalRecordData.Result :=
  RationalAffineData.augment (RationalRecordData.output (RationalRegressionNP.pack x))

theorem parsed_eq (x : Instance × List Bool) : parsed x = RationalRecordData.output (expanded x) := by
  have h := RationalAffineData.original_append (data x.1).A (data x.1).y (data x.1).B
    x.2 (data x.1).positive
  change RationalAffineData.augment (RationalRecordData.output ((data x.1).bits ++ x.2)) = _ at h
  simpa only [data_bits,parsed,RationalRegressionNP.pack,expanded] using h

def parsedComputableInPolyTime :
    TM2ComputableInPolyTime (PairEncoding.finEncoding encoding EncodedLanguage.certificateEncoding)
      RationalRecordData.outputEncoding parsed :=
  compositionComputableInPolyTime _ _ _ RationalRegressionNP.pack
    (fun bits => RationalAffineData.augment (RationalRecordData.output bits))
    RationalRegressionNP.packComputableInPolyTime RationalAffineData.parsedComputableInPolyTime

def source (x : Instance × List Bool) : RationalRecordSource.Input :=
  RationalBinaryVerifier.source (expanded x)

theorem source_encode (x : Instance × List Bool) :
    RationalRegressionInternal.encoding.encode (source x) = finish (parsed x) := by
  rw [source,RationalBinaryVerifier.source_encode,parsed_eq]
  rfl

/-- The actual finite machine starts from the original encoded instance and
arbitrary certificate. Every parser, insertion, validation and transfer is charged. -/
@[irreducible] def sourceComputableInPolyTime :
    TM2ComputableInPolyTime (PairEncoding.finEncoding encoding EncodedLanguage.certificateEncoding)
      RationalRegressionInternal.encoding source := by
  let raw := compositionComputableInPolyTime _ _ _ _ _ parsedComputableInPolyTime finishComputableInPolyTime
  exact { raw with
    outputsFun := fun x => by
      simpa only [source_encode,RationalRecordAssembly.outputEncoding,Function.comp_apply,id_eq]
        using! raw.outputsFun x }

variable (p : ℕ) [Fact p.Prime]

def verify : Instance × List Bool → Bool := RationalRegressionInternal.check p ∘ source

set_option maxHeartbeats 800000 in
def computableInPolyTime :=
  compositionComputableInPolyTime
    (PairEncoding.finEncoding encoding EncodedLanguage.certificateEncoding)
    RationalRegressionInternal.encoding finEncodingBoolBool source
    (RationalRegressionInternal.check p) sourceComputableInPolyTime
    (RationalRegressionInternal.computableInPolyTime p)

/-- The machine's result is independent of the chosen matrix presentation. -/
theorem verify_original {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (hr : 0 < r) (w : List Bool) :
    verify p (original A y B hr,w) = RationalBinaryVerifier.check p
      (encodeInput (RegularisedCandidates.affineDesign A) y B ++ w) := by
  have hp := RationalAffineData.original_append A y B w hr
  have he : source (original A y B hr,w) = RationalBinaryVerifier.source
      (encodeInput (RegularisedCandidates.affineDesign A) y B ++ w) := by
    apply RationalRegressionInternal.encoding.encode_injective
    rw [source_encode,RationalBinaryVerifier.source_encode]
    change finish (RationalAffineData.augment (RationalRecordData.output (encodeInput A y B ++ w))) = _
    rw [hp]
    rfl
  simp only [verify,Function.comp_apply,he,RationalBinaryVerifier.check]

def problem : EncodedLanguage Instance where
  encoding := encoding
  accepts x := ∃ (r d : ℕ) (A : Matrix (Fin r) (Fin d) ℚ)
      (y : Fin r → ℚ) (B : ℚ), 0 < r ∧ x.val = encodeInput A y B ∧
      ∃ (c : ℚ) (β : Fin d → ℚ), ∑ i, padicNorm p (y i - ((A *ᵥ β) i + c)) ≤ B

def certificateBound : Polynomial ℕ := 28*(Polynomial.X+1)^3+9*(Polynomial.X+1)+1
theorem certificateBound_eval (n : ℕ) : certificateBound.eval n = 28*(n+1)^3+9*(n+1)+1 := by
  simp [certificateBound]

theorem sound_original {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (hr : 0 < r) (w : List Bool)
    (h : verify p (original A y B hr,w) = true) :
    ∃ (c : ℚ) (β : Fin d → ℚ), ∑ i, padicNorm p (y i - ((A *ᵥ β) i + c)) ≤ B := by
  rw [verify_original] at h
  obtain ⟨θ,hθ⟩ := RationalCertificateSoundness.sound p
    (RegularisedCandidates.affineDesign A) y B w hr h
  refine ⟨θ 0,fun i => θ i.succ,?_⟩
  have he : Fin.cons (θ 0) (fun i => θ i.succ) = θ := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  rw [← RationalWitnesses.loss_affineDesign,he]
  exact hθ

theorem sound (x : Instance) (w : List Bool) (h : verify p (x,w) = true) : (problem p).accepts x := by
  obtain ⟨r,d,A,y,B,hr,he⟩ := x.property
  have hx : x = original A y B hr := Subtype.ext he
  exact ⟨r,d,A,y,B,hr,he,sound_original p A y B hr w (by simpa [hx] using h)⟩

theorem complete (x : Instance) (h : (problem p).accepts x) :
    ∃ w : List Bool, w.length ≤ certificateBound.eval (encoding.encode x).length ∧
      verify p (x,w) = true := by
  obtain ⟨r,d,A,y,B,hr,he,c,β,hβ⟩ := h
  obtain ⟨c',β',hmin,hlen⟩ := RationalWitnessEncoding.exists_affine_minimizer_encoding p A y B hr
  have hx : x = original A y B hr := Subtype.ext he
  refine ⟨encodeRats (List.ofFn (Fin.cons c' β')),?_,?_⟩
  · simpa [encoding,he,certificateBound_eval] using hlen
  · rw [hx,verify_original,RationalBinaryVerifier.check_correct p _ _ _ _ hr,
      RationalWitnesses.loss_affineDesign]
    exact (hmin c β).trans hβ

theorem accepts_original_iff {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (hr : 0 < r) :
    (problem p).accepts (original A y B hr) ↔
      ∃ (c : ℚ) (β : Fin d → ℚ), ∑ i, padicNorm p (y i - ((A *ᵥ β) i + c)) ≤ B := by
  constructor
  · intro h
    obtain ⟨w,_,hw⟩ := complete p _ h
    exact sound_original p A y B hr w hw
  · intro h
    exact ⟨r,d,A,y,B,hr,rfl,h⟩

def polytimeVerifier : EncodedLanguage.PolytimeVerifier (problem p) where
  verify := verify p
  certificateBound := certificateBound
  sound := sound p
  complete := complete p
  polytime := ⟨computableInPolyTime p⟩

/-- Thesis `prop:regression-np-complete`, affine NP membership, in the original
binary rational input length. NP-hardness under this encoding is separate. -/
theorem inNP : (problem p).InNP := (polytimeVerifier p).toInNP

/-- Complete machine time in original instance plus certificate bits. -/
def outputsInTime (x : Instance) (w : List Bool) :
    Turing.TM2OutputsInTime (computableInPolyTime p).tm
      (((PairEncoding.finEncoding encoding EncodedLanguage.certificateEncoding).encode (x,w)).map
        (computableInPolyTime p).inputAlphabet.symm)
      (some ([verify p (x,w)].map (computableInPolyTime p).outputAlphabet.symm))
      ((computableInPolyTime p).time.eval (x.val.length+w.length)) := by
  simpa only [RationalRegressionNP.pair_length,finEncodingBoolBool] using!
    (computableInPolyTime p).outputsFun (x,w)

/-- Substitution of the affine certificate bound into the whole machine clock. -/
def shortTime : Polynomial ℕ := (computableInPolyTime p).time.comp (Polynomial.X+certificateBound)

def shortOutputsInTime (x : Instance) (w : List Bool)
    (hw : w.length ≤ certificateBound.eval x.val.length) :
    Turing.TM2OutputsInTime (computableInPolyTime p).tm
      (((PairEncoding.finEncoding encoding EncodedLanguage.certificateEncoding).encode (x,w)).map
        (computableInPolyTime p).inputAlphabet.symm)
      (some ([verify p (x,w)].map (computableInPolyTime p).outputAlphabet.symm))
      ((shortTime p).eval x.val.length) := by
  apply MachinePrimitives.evalsToInTimeMono (outputsInTime p x w)
  simp only [shortTime,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X]
  exact MachineRuntime.polynomial_eval_mono _ (Nat.add_le_add_left hw _)

#print axioms sourceComputableInPolyTime
#print axioms computableInPolyTime
#print axioms verify_original
#print axioms sound
#print axioms complete
#print axioms accepts_original_iff
#print axioms inNP
#print axioms outputsInTime
#print axioms shortOutputsInTime

end
end PhdThesisLean.RationalAffineNP
