import PhdThesisLean.RationalResidualListMachine

/-!
# Polynomial-time evaluation of every observation from one certificate

The loop is an actual finite TM2, and sequential composition includes all
intermediate transfers. The source still uses internal delimited fraction
words; parsing/validating the original binary record is a separate obligation.
-/
namespace PhdThesisLean.RationalResidualList

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open RationalVerifierBounds
open RationalSum (field fields)
open RationalCertificateBroadcast (frame frames listEncoding)
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)
open LeanNPHardness.MachineComposition

set_option backward.isDefEq.respectTransparency false
noncomputable section

def encoding : FinEncoding (List Machine.Row) := listEncoding RationalColumnPairing.rowEncoding

theorem encode_eq (xs : List Machine.Row) : encoding.encode xs = Machine.rowFields xs := by
  simp only [encoding, listEncoding, frames, Machine.rowFields, List.flatMap_map]
  rfl

theorem count_le_length (xs : List Machine.Row) : xs.length ≤ (Machine.rowFields xs).length := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
      simp only [Machine.rowFields, List.flatMap_cons, Machine.rowField, frame,
        List.length_append, List.length_map, List.length_cons] at *
      omega

/-- Output size follows from actual machine pushes per charged transition. -/
def outputSize : Polynomial ℕ := outputSizePolynomial RationalColumnPairing.rowEncoding
  RationalNorm.fractionEncoding RationalRowResidual.evaluate Machine.body

set_option maxRecDepth 2048 in
theorem output_length_le (x : Machine.Row) :
    (RationalRowResidual.evaluate x).encode.length ≤ outputSize.eval (Machine.rowWord x).length :=
by
  simpa only [outputSize, outputSizePolynomial_eval, Machine.rowWord,
    RationalNorm.fractionEncoding] using
    LeanNPHardness.MachineRuntime.computableInPolyTime_output_length_le
      RationalColumnPairing.rowEncoding RationalNorm.fractionEncoding
      RationalRowResidual.evaluate Machine.body x

def passTime : Polynomial ℕ := Machine.body.time + 2 * outputSize + 2 * Polynomial.X + 6

theorem passTime_eval (s : ℕ) : passTime.eval s =
    Machine.body.time.eval s + 2 * outputSize.eval s + 2 * s + 6 := by simp [passTime]

/-- The prefix is stored in reverse order and is never recopied during a call.
The bound charges its final reversal as well as all future output symbols. -/
def run_bounded (xs : List Machine.Row) (acc : List (Option Bool)) (s : ℕ)
    (h : (Machine.rowFields xs).length ≤ s) :
    Machine.Run (Machine.ready xs acc)
      (Machine.done
        (acc.reverse ++ fields (xs.map RationalRowResidual.evaluate)))
      ((xs.length + 1) * passTime.eval s + acc.length) := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.map_nil, fields, List.flatMap_nil, List.append_nil]
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono
        (Machine.exit_run acc)
      simp only [List.length_nil, zero_add, one_mul, passTime_eval]
      omega
  | cons x xs ih =>
      have hin : (Machine.rowWord x).length ≤ s := by
        simp only [Machine.rowFields, List.flatMap_cons, List.length_append,
          Machine.rowField, RationalCertificateBroadcast.frame, List.length_map,
          List.length_singleton] at h
        omega
      have htail : (Machine.rowFields xs).length ≤ s := by
        simp only [Machine.rowFields, List.flatMap_cons, List.length_append] at h ⊢
        omega
      have hout' := (output_length_le x).trans
        (LeanNPHardness.MachineRuntime.polynomial_eval_mono outputSize hin)
      have hcost := LeanNPHardness.MachineRuntime.polynomial_eval_mono
        Machine.body.time hin
      have hrun := Machine.seq (Machine.iteration_cycle x xs acc)
        (ih ((field (RationalRowResidual.evaluate x)).reverse ++ acc) htail)
      simp only [List.reverse_append, List.reverse_reverse, List.map_cons, fields,
        List.flatMap_cons, List.append_assoc] at hrun ⊢
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono hrun
      simp only [List.length_cons, List.length_append, List.length_reverse,
        field, List.length_map, List.length_nil, passTime_eval]
      nlinarith

def time : Polynomial ℕ := (Polynomial.X + 1) * passTime

theorem time_eval (s : ℕ) : time.eval s =
    (s + 1) * (Machine.body.time.eval s + 2 * outputSize.eval s + 2 * s + 6) := by
  simp [time, passTime_eval]

/-- Traverse all rows, producing the ordered exact unreduced residual list. -/
def outputsInTime (xs : List Machine.Row) :
    TM2OutputsInTime Machine.computer (Machine.rowFields xs)
      (some (RationalNormList.encoding.encode (xs.map RationalRowResidual.evaluate)))
      (time.eval (Machine.rowFields xs).length) := by
  have h := run_bounded xs [] (Machine.rowFields xs).length le_rfl
  have h' := LeanNPHardness.MachinePrimitives.evalsToInTimeMono h
    (show (xs.length + 1) * passTime.eval (Machine.rowFields xs).length + [].length ≤
        time.eval (Machine.rowFields xs).length by
      simpa [time] using Nat.mul_le_mul_right (passTime.eval (Machine.rowFields xs).length)
        (Nat.add_le_add_right (count_le_length xs) 1))
  simpa only [Machine.ready_eq_initList, Machine.done_eq_haltList, List.reverse_nil,
    List.append_nil, List.nil_append, RationalNormList.encoding] using! h'

def computableInPolyTime : TM2ComputableInPolyTime encoding RationalNormList.encoding
    (List.map RationalRowResidual.evaluate) where
  tm := Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := time
  outputsFun xs := by simpa only [Equiv.refl, List.map_id, encode_eq] using outputsInTime xs

#print axioms Machine.body_run
#print axioms Machine.iteration_cycle
#print axioms run_bounded
#print axioms computableInPolyTime
#print axioms output_length_le

end
end PhdThesisLean.RationalResidualList
