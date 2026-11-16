import PhdThesisLean.RationalResidualList

/-!
# A finite polynomial-time regression checker on the internal source format

The input contains the response/coefficient rows, one reusable certificate and
the threshold. Row counts are runtime data. Equal column counts are a typed
input contract; the decoder checks that contract semantically, but no machine
parser or malformed-binary-input rejection is claimed here.
-/
namespace PhdThesisLean.RationalRegressionInternal

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open RationalVerifierBounds
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)
open LeanNPHardness.MachineComposition LeanNPHardness.MachineAdapters
open RationalCertificateBroadcast (Row certificate observations)

set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A single certificate and runtime-many rectangular observation rows. -/
def Compatible (x : List Fraction × List Row) : Prop :=
  ∀ row ∈ x.2, row.2.length = x.1.length
instance (x : List Fraction × List Row) : Decidable (Compatible x) :=
  inferInstanceAs (Decidable (∀ row ∈ x.2, row.2.length = x.1.length))
abbrev Source := {x : List Fraction × List Row // Compatible x}

def sourceEncoding : FinEncoding Source where
  Γ := RationalCertificateBroadcast.sourceEncoding.Γ
  encode x := RationalCertificateBroadcast.sourceEncoding.encode x.val
  decode bits := do
    let x ← RationalCertificateBroadcast.sourceEncoding.decode bits
    if h : Compatible x then some ⟨x, h⟩ else none
  decode_encode x := by
    simp only [RationalCertificateBroadcast.sourceEncoding.decode_encode]
    simp [x.property]
  ΓFin := RationalCertificateBroadcast.sourceEncoding.ΓFin

/-- Zipping is semantic identification of the already proved pairing machine. -/
def rows (x : Source) : List RationalResidualList.Machine.Row :=
  x.val.2.map fun row => (row.1, row.2.zip x.val.1)

theorem zip_projections (xs ys : List Fraction) (h : xs.length = ys.length) :
    (xs.zip ys).map Prod.fst = xs ∧ (xs.zip ys).map Prod.snd = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          have hi := ih ys (by simpa using h)
          simpa using hi

theorem rows_encode (x : Source) :
    RationalResidualList.encoding.encode (rows x) =
      RationalCertificateBroadcast.outputEncoding.encode
        (RationalCertificateBroadcast.broadcast x.val) := by
  simp only [RationalResidualList.encoding, RationalCertificateBroadcast.outputEncoding,
    RationalCertificateBroadcast.listEncoding, rows, RationalCertificateBroadcast.broadcast,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro row hrow
  have hp := zip_projections row.2 x.val.1 (x.property row hrow)
  simp only [Function.comp_apply, RationalColumnPairing.rowEncoding,
    RationalCertificateBroadcast.separatedRowEncoding, LeanNPHardness.PairEncoding.finEncoding,
    RationalColumnPairing.encoding, hp.1, hp.2]

/-- The same broadcast machine, with its physical output identified as row inputs. -/
def broadcastComputableInPolyTime :
    TM2ComputableInPolyTime sourceEncoding RationalResidualList.encoding rows where
  toTM2ComputableAux := RationalCertificateBroadcast.computableInPolyTime.toTM2ComputableAux
  time := RationalCertificateBroadcast.computableInPolyTime.time
  outputsFun x := by
    simpa only [sourceEncoding, rows_encode] using!
      RationalCertificateBroadcast.computableInPolyTime.outputsFun x.val

def residuals (x : Source) : List Fraction := (rows x).map RationalRowResidual.evaluate

def residualsComputableInPolyTime :
    TM2ComputableInPolyTime sourceEncoding RationalNormList.encoding residuals :=
  compositionComputableInPolyTime _ _ _ _ _
    broadcastComputableInPolyTime RationalResidualList.computableInPolyTime

variable (p : ℕ) [Fact p.Prime]

def loss (x : Source) : Fraction := sum ((residuals x).map (Fraction.norm p))

/-- Certificate reuse, per-row pairing and arithmetic, norm traversal and summation. -/
def lossComputableInPolyTime :
    TM2ComputableInPolyTime sourceEncoding RationalNorm.fractionEncoding (loss p) :=
  compositionComputableInPolyTime sourceEncoding RationalNormList.encoding
    RationalNorm.fractionEncoding residuals
    (fun xs => sum (xs.map (Fraction.norm p)))
    residualsComputableInPolyTime (RationalNormList.sumComputableInPolyTime p)

def regressionSource {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (β : Fin d → ℚ) : Source :=
  ⟨(certificate β, observations A y), by
    intro row hrow
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    simp [certificate]⟩

theorem rows_regression {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (β : Fin d → ℚ) :
    rows (regressionSource A y β) = List.ofFn fun i =>
      (Fraction.ofRat (y i), RationalDotProduct.pairs (A i) β) := by
  simp only [rows, regressionSource, observations, certificate, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply congrArg (fun columns => (Fraction.ofRat (y i), columns))
  simpa only [List.map_ofFn, Function.comp_def, RationalDotProduct.pairs] using
    (List.zip_map' (l := List.ofFn (fun j : Fin d => j))
      (f := fun j => Fraction.ofRat (A i j)) (g := fun j => Fraction.ofRat (β j)))

theorem residuals_regression {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (β : Fin d → ℚ) :
    residuals (regressionSource A y β) = RationalNormList.residuals A y β := by
  simp [residuals, rows_regression, List.map_ofFn, RationalRowResidual.evaluate_row,
    RationalNormList.residuals, Function.comp_def]

theorem loss_regression {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (β : Fin d → ℚ) :
    loss p (regressionSource A y β) = sum (losses p A y β) := by
  rw [loss, residuals_regression, RationalNormList.map_residuals]

theorem loss_value_correct {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (β : Fin d → ℚ) :
    (loss p (regressionSource A y β)).value = RationalWitnesses.loss p A y β := by
  rw [loss_regression, value_loss]

/-- Threshold is retained on stacks while the entire loss machine runs. -/
def encoding : FinEncoding (Source × Fraction) :=
  LeanNPHardness.PairEncoding.finEncoding sourceEncoding RationalNorm.fractionEncoding

def check (x : Source × Fraction) : Bool := (loss p x.1).le x.2

def computableInPolyTime :
    TM2ComputableInPolyTime encoding LeanNPHardness.finEncodingBoolBool (check p) := by
  let paired := pairReductionComputableInPolyTime sourceEncoding RationalNorm.fractionEncoding
    RationalNorm.fractionEncoding (loss p) (lossComputableInPolyTime p)
  let untagged := compositionComputableInPolyTime _ _ _ _ _ paired
    RationalRowResidual.untagComputableInPolyTime
  exact compositionComputableInPolyTime _ _ _ _ _ untagged
    RationalArithmetic.comparisonComputableInPolyTime

theorem check_regression {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) :
    check p (regressionSource A y β, Fraction.ofRat B) =
      RationalVerifierBounds.check p A y B β := by
  simp only [check, loss_regression, RationalVerifierBounds.check]

theorem check_correct {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) :
    check p (regressionSource A y β, Fraction.ofRat B) = true ↔
      RationalWitnesses.loss p A y β ≤ B := by
  rw [check_regression, RationalVerifierBounds.check_correct]

/-- All internal symbols are charged to the actual original input/certificate bits. -/
theorem input_length_le {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) :
    (encoding.encode (regressionSource A y β, Fraction.ofRat B)).length ≤
      3 * totalBits A y B β := by
  have hs := RationalCertificateBroadcast.source_length_le A y B β
  have hb : (Fraction.ofRat B).encode.length ≤ totalBits A y B β := by
    rw [RationalNorm.ofRat_encode]
    simp only [totalBits, RationalWitnessEncoding.encodeInput, List.length_append]
    omega
  simpa only [encoding, LeanNPHardness.PairEncoding.finEncoding_encode_length,
    sourceEncoding, regressionSource, RationalNorm.fractionEncoding] using
      (show (RationalCertificateBroadcast.sourceEncoding.encode
        (certificate β, observations A y)).length + (Fraction.ofRat B).encode.length ≤
          3 * totalBits A y B β by omega)

def time : Polynomial ℕ := (computableInPolyTime p).time.comp (3 * Polynomial.X)

theorem time_eval (s : ℕ) : (time p).eval s = (computableInPolyTime p).time.eval (3 * s) := by
  simp [time, Polynomial.eval_comp]

/-- Complete internal checker: one certificate and the threshold enter, one bit
exits. This does not include translating/validating the original binary record. -/
def outputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) :
    TM2OutputsInTime (computableInPolyTime p).tm
      ((encoding.encode (regressionSource A y β, Fraction.ofRat B)).map
        (computableInPolyTime p).inputAlphabet.symm)
      (some ([RationalVerifierBounds.check p A y B β].map
        (computableInPolyTime p).outputAlphabet.symm))
      ((time p).eval (totalBits A y B β)) := by
  have h := (computableInPolyTime p).outputsFun (regressionSource A y β, Fraction.ofRat B)
  rw [check_regression] at h
  apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono h
  rw [time_eval]
  exact LeanNPHardness.MachineRuntime.polynomial_eval_mono _ (input_length_le A y B β)

#print axioms broadcastComputableInPolyTime
#print axioms residualsComputableInPolyTime
#print axioms lossComputableInPolyTime
#print axioms loss_value_correct
#print axioms computableInPolyTime
#print axioms check_correct
#print axioms input_length_le
#print axioms outputsInTime

end
end PhdThesisLean.RationalRegressionInternal
