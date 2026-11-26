import PhdThesisLean.RationalCertificateSoundness
import LeanNPHardness.ComplexityClasses

/-!
# NP membership for binary rational summed regression at each fixed prime

Instances are canonical binary words for rational matrices, targets and a
threshold, with positive row count. This subtype fixes the instance boundary;
certificates are arbitrary Boolean words as required by the library NP class.
The semantic decoder of the subtype is not used to justify any machine cost:
the actual verifier removes the pair tags in two linear passes and runs the
already proved total original-bit parser and arithmetic machine.

Zero columns are also allowed. This includes the thesis's positive-dimensional
ordinary problem. Affine membership and the binary-rational hardness reduction
remain separate obligations.
-/
namespace PhdThesisLean.RationalRegressionNP

open Computability hiding FinEncoding finEncodingBoolBool
open LeanNPHardness
open RationalWitnessEncoding (encodeInput encodeRats)
set_option backward.isDefEq.respectTransparency false
noncomputable section

def ValidInput (bits : List Bool) : Prop :=
  ∃ (r d : ℕ) (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ),
    0 < r ∧ bits = encodeInput A y B

abbrev Instance := {bits : List Bool // ValidInput bits}

def encoding : FinEncoding Instance := by
  classical
  exact {
    Γ := Bool
    encode := Subtype.val
    decode := fun bits => if h : ValidInput bits then some ⟨bits,h⟩ else none
    decode_encode := fun x => by simp [x.property]
    ΓFin := inferInstance }

def original {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (hr : 0 < r) : Instance :=
  ⟨encodeInput A y B,⟨r,d,A,y,B,hr,rfl⟩⟩

variable (p : ℕ) [Fact p.Prime]

/-- Semantic rational threshold decision, over the explicit binary instance
encoding. Existence here is unrestricted by the certificate-size bound. -/
def problem : EncodedLanguage Instance where
  encoding := encoding
  accepts x := ∃ (r d : ℕ) (A : Matrix (Fin r) (Fin d) ℚ)
      (y : Fin r → ℚ) (B : ℚ),
    0 < r ∧ x.val = encodeInput A y B ∧
      ∃ β : Fin d → ℚ, RationalWitnesses.loss p A y β ≤ B

def verify (x : Instance × List Bool) : Bool :=
  RationalBinaryVerifier.check p (x.1.val ++ x.2)

/-- Pair encoding adds one finite tag per symbol and no extra symbols. -/
theorem pair_length (x : Instance × List Bool) :
    ((PairEncoding.finEncoding encoding EncodedLanguage.certificateEncoding).encode x).length =
      x.1.val.length + x.2.length := by
  simp [PairEncoding.finEncoding,encoding,EncodedLanguage.certificateEncoding,
    MachinePrimitives.RawBoolList.finEncoding]

def pack (x : Instance × List Bool) : List Bool := x.1.val ++ x.2

/-- Physical tag removal, including order restoration and final cleanup. -/
def packComputableInPolyTime :
    TM2ComputableInPolyTime (PairEncoding.finEncoding encoding EncodedLanguage.certificateEncoding)
      MachinePrimitives.RawBoolList.finEncoding pack where
  tm := AllDifferentCSPMachine.UnaryBridgeMachine.computer (Sum.inl false) RationalRowResidual.untag
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2*Polynomial.X+2
  outputsFun x := by
    have h := AllDifferentCSPMachine.UnaryBridgeMachine.outputsInTime (Sum.inl false)
      RationalRowResidual.untag
      ((PairEncoding.finEncoding encoding EncodedLanguage.certificateEncoding).encode x)
    simpa [Equiv.refl,PairEncoding.finEncoding,encoding,EncodedLanguage.certificateEncoding,
      MachinePrimitives.RawBoolList.finEncoding,pack,RationalRowResidual.untag,List.map_map,
      Function.comp_def] using h

set_option maxHeartbeats 800000 in
/-- Every packing pass and the composition transfer is charged, followed by
the complete verifier, at a polynomial in instance plus certificate length. -/
def computableInPolyTime :
    TM2ComputableInPolyTime (PairEncoding.finEncoding encoding EncodedLanguage.certificateEncoding)
      finEncodingBoolBool (verify p) :=
  MachineComposition.compositionComputableInPolyTime
    (PairEncoding.finEncoding encoding EncodedLanguage.certificateEncoding)
    MachinePrimitives.RawBoolList.finEncoding finEncodingBoolBool pack
    (RationalBinaryVerifier.check p)
    packComputableInPolyTime (RationalBinaryVerifier.computableInPolyTime p)

def certificateBound : Polynomial ℕ := 12*Polynomial.X^3+9*Polynomial.X+1

theorem certificateBound_eval (n : ℕ) : certificateBound.eval n = 12*n^3+9*n+1 := by
  simp [certificateBound]

theorem sound (x : Instance) (w : List Bool) (h : verify p (x,w) = true) :
    (problem p).accepts x := by
  obtain ⟨r,d,A,y,B,hr,he⟩ := x.property
  refine ⟨r,d,A,y,B,hr,he,?_⟩
  exact RationalCertificateSoundness.sound p A y B w hr (by simpa [verify,he] using h)

theorem complete (x : Instance) (h : (problem p).accepts x) :
    ∃ w : List Bool, w.length ≤ certificateBound.eval (encoding.encode x).length ∧
      verify p (x,w) = true := by
  obtain ⟨r,d,A,y,B,hr,he,hs⟩ := h
  obtain ⟨β,hβ,hlen⟩ := (RationalBinaryVerifier.threshold_iff_short_verifier p A y B hr).1 hs
  refine ⟨encodeRats (List.ofFn β),?_,?_⟩
  · simpa [encoding,he,certificateBound_eval] using hlen
  · simpa [verify,he] using hβ

/-- Exact correspondence for every original rational instance, independent of
which representation witnesses the instance subtype. -/
theorem accepts_original_iff {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (hr : 0 < r) :
    (problem p).accepts (original A y B hr) ↔
      ∃ β : Fin d → ℚ, RationalWitnesses.loss p A y β ≤ B := by
  constructor
  · intro h
    obtain ⟨w,_,hw⟩ := complete p _ h
    exact RationalCertificateSoundness.sound p A y B w hr hw
  · intro h
    exact ⟨r,d,A,y,B,hr,rfl,h⟩

def polytimeVerifier : EncodedLanguage.PolytimeVerifier (problem p) where
  verify := verify p
  certificateBound := certificateBound
  sound := sound p
  complete := complete p
  polytime := ⟨computableInPolyTime p⟩

/-- Ordinary summed rational p-adic regression is in the library NP class,
with binary rational inputs and arbitrary binary certificates. -/
theorem inNP : (problem p).InNP := (polytimeVerifier p).toInNP

#print axioms encoding
#print axioms packComputableInPolyTime
#print axioms computableInPolyTime
#print axioms sound
#print axioms complete
#print axioms accepts_original_iff
#print axioms polytimeVerifier
#print axioms inNP

end
end PhdThesisLean.RationalRegressionNP
