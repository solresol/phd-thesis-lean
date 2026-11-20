import PhdThesisLean.RationalRectangularFieldsMachine

/-!
# Polynomial-time rectangular data validation

This is the dimension/count and row-partitioning stage. It consumes bounded
unary dimensions and the counted-list parser's output; producing this combined
stage input from the original binary record remains a composition obligation.
-/
namespace PhdThesisLean.RationalRectangularFields

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open LeanNPHardness
set_option backward.isDefEq.respectTransparency false

abbrev Source := ℕ × ℕ × Bits

def readUnary : Bits → Option (ℕ × Bits)
  | [] => none
  | none :: bs => some (0,bs)
  | some _ :: bs => (readUnary bs).map fun p => (p.1+1,p.2)

theorem readUnary_append (n : ℕ) (bs : Bits) :
    readUnary (List.replicate n (some true) ++ none :: bs) = some (n,bs) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, readUnary, ih]

def decodeSource (bs : Bits) : Option Source := do
  let (r,rest) ← readUnary bs
  let (d,rest) ← readUnary rest
  pure (r,d,rest)

def inputEncoding : FinEncoding Source where
  Γ := Option Bool
  encode x := Machine.input x.1 x.2.1 x.2.2
  decode := decodeSource
  decode_encode x := by
    rcases x with ⟨r,d,bs⟩
    simp [decodeSource, Machine.input, List.append_assoc, readUnary_append]
  ΓFin := inferInstance

def outputEncoding : FinEncoding (List Cell) where
  Γ := Cell
  encode := id
  decode := some
  decode_encode _ := rfl
  ΓFin := inferInstance

/-- No arithmetic-cost premise; the witness is the concrete six-stack machine. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputEncoding outputEncoding (fun x => output x.1 x.2.1 x.2.2) where
  tm := Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 32*(Polynomial.X+1)^2
  outputsFun x := by
    rcases x with ⟨r,d,bs⟩
    have h := MachinePrimitives.evalsToInTimeMono (Machine.outputsInTime r d bs) (Machine.time_le r d bs)
    simpa [inputEncoding, outputEncoding, Equiv.refl] using! h

open RationalVerifierBounds

def dataSuffix {d : ℕ} (B : ℚ) (β : Fin d → ℚ) : List Bool :=
  RationalWitnessEncoding.encodeRat B ++ RationalWitnessEncoding.encodeRats (List.ofFn β)

def parsedData {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ)
    (B : ℚ) (β : Fin d → ℚ) : Bits :=
  RationalCountedList.output
    (RationalWitnessEncoding.encodeRats (RationalWitnessEncoding.inputEntries A y) ++ dataSuffix B β)

theorem parsedData_length_le {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) :
    (parsedData A y B β).length ≤ 2*totalBits A y B β+1 := by
  have h := RationalCountedList.output_length_le
    (RationalWitnessEncoding.encodeRats (RationalWitnessEncoding.inputEntries A y) ++ dataSuffix B β)
  simp only [dataSuffix, totalBits, RationalWitnessEncoding.encodeInput, List.length_append] at h ⊢
  exact h.trans (by omega)

theorem originalDataTime_le {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    4*r*d + 21*r + 3*d + 4*(parsedData A y B β).length + 10 ≤
      4*(totalBits A y B β)^2 + 32*totalBits A y B β + 14 := by
  let S := totalBits A y B β
  have hb := parsedData_length_le A y B β
  have hrows : r ≤ S := (RationalWitnessEncoding.rows_le_input_length A y B).trans (by
    simp only [S, totalBits]; omega)
  have hcols : d ≤ S := (RationalWitnessEncoding.input_size_bounds A y B hr).1.trans (by
    simp only [S, totalBits]; omega)
  have hm := Nat.mul_le_mul hrows hcols
  change 4*r*d+21*r+3*d+4*(parsedData A y B β).length+10 ≤ 4*S^2+32*S+14
  change (parsedData A y B β).length ≤ 2*S+1 at hb
  nlinarith

/-- Actual stage execution charged in original combined input/certificate bits.
The preceding binary-parser executions/transfers are not included in this bound. -/
noncomputable def originalDataOutputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    Turing.TM2OutputsInTime Machine.computer (Machine.input r d (parsedData A y B β))
      (some (((RationalCertificateBroadcast.listEncoding RationalCertificateBroadcast.rowEncoding).encode
        (RationalCertificateBroadcast.observations A y)).map rowCell ++
          .dataEnd :: (dataSuffix B β).map Cell.tail))
      (4*(totalBits A y B β)^2 + 32*totalBits A y B β + 14) := by
  have h := MachinePrimitives.evalsToInTimeMono (Machine.outputsInTime r d (parsedData A y B β))
    (originalDataTime_le A y B β hr)
  simpa only [parsedData, output_original_data] using! h

#print axioms computableInPolyTime
#print axioms originalDataTime_le
#print axioms originalDataOutputsInTime

end PhdThesisLean.RationalRectangularFields
