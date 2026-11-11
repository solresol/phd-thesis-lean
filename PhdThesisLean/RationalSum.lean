import PhdThesisLean.RationalSumMachine

/-!
# Polynomial-time exact accumulation of binary fractions

The source is an initial fraction and a runtime-length delimited fraction list.
The bound includes every addition and all control and stack transfers. No
arithmetic-operation cost or iteration-width hypothesis is supplied by callers.
-/
namespace PhdThesisLean.RationalSum

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open RationalVerifierBounds
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)

set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A bound for a complete cycle, including the final empty-list branch. -/
def passTime : Polynomial ℕ :=
  Machine.body.time.comp (8 * Polynomial.X + 6) + 24 * Polynomial.X + 24

theorem passTime_eval (s : ℕ) :
    passTime.eval s = Machine.body.time.eval (8 * s + 6) + 24 * s + 24 := by
  simp [passTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp]

/-- Induction counts actual controller cycles, with a preserved additive width
budget. The input tail is not recopied or discarded during an addition. -/
def run_bounded (xs : List Fraction) (z : Fraction) (s : ℕ) (h : budget z xs ≤ s) :
    Machine.Run (Machine.ready z xs) (Machine.done (xs.foldl Fraction.add z))
      ((xs.length + 1) * passTime.eval s) := by
  induction xs generalizing z with
  | nil =>
      have hz := Fraction.encode_length_le (accumulator_bounded h)
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (Machine.exit_run z)
      simp only [List.length_nil, zero_add, one_mul, passTime_eval]
      omega
  | cons x xs ih =>
      have hnext := (budget_step z x xs).trans h
      have hz := Fraction.encode_length_le (accumulator_bounded h)
      have hx := Fraction.encode_length_le (head_bounded h)
      have hout := Fraction.encode_length_le (accumulator_bounded hnext)
      have hcost := LeanNPHardness.MachineRuntime.polynomial_eval_mono Machine.body.time
        (show z.encode.length + x.encode.length ≤ 8 * s + 6 by omega)
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono
        (Machine.seq (Machine.iteration_cycle z x xs) (ih (z.add x) hnext))
      simp only [List.length_cons, passTime_eval]
      nlinarith

def time : Polynomial ℕ := (Polynomial.X + 1) * passTime

theorem time_eval (s : ℕ) :
    time.eval s = (s + 1) * (Machine.body.time.eval (8 * s + 6) + 24 * s + 24) := by
  simp [time, passTime_eval, Polynomial.eval_mul, Polynomial.eval_add]

def outputsInTime (x : Fraction × List Fraction) :
    TM2OutputsInTime Machine.computer (encode x)
      (some (x.2.foldl Fraction.add x.1).encode) (time.eval (encode x).length) := by
  have h := run_bounded x.2 x.1 (encode x).length (budget_le_length x.1 x.2)
  have h' := LeanNPHardness.MachinePrimitives.evalsToInTimeMono h
    (Nat.mul_le_mul_right (passTime.eval (encode x).length)
      (Nat.add_le_add_right (count_le_length x.1 x.2) 1))
  simpa only [Machine.ready_eq_initList, Machine.done_eq_haltList, time,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using! h'

/-- One uniform finite TM2 for every list length and every encoded fraction. -/
def computableInPolyTime : TM2ComputableInPolyTime encoding RationalNorm.fractionEncoding
    (fun x => x.2.foldl Fraction.add x.1) where
  tm := Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := time
  outputsFun x := by simpa [Equiv.refl, encoding, RationalNorm.fractionEncoding] using outputsInTime x

/-- Specialization to summation: a fixed encoded zero precedes the list. The
constant prefix, fraction bits and all delimiters are included in input size. -/
def listEncoding : FinEncoding (List Fraction) where
  Γ := Option Bool
  encode xs := encode (Fraction.zero, xs)
  decode bits := (decode bits).map Prod.snd
  decode_encode xs := by simp
  ΓFin := inferInstance

def sumComputableInPolyTime : TM2ComputableInPolyTime listEncoding RationalNorm.fractionEncoding sum where
  tm := Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := time
  outputsFun xs := by
    simpa [Equiv.refl, listEncoding, RationalNorm.fractionEncoding, sum] using
      outputsInTime (Fraction.zero, xs)

theorem value_correct (x : Fraction × List Fraction) :
    (x.2.foldl Fraction.add x.1).value = x.1.value + (x.2.map Fraction.value).sum :=
  value_fold_add x.2 x.1

/-- This is the evaluator's exact stored loss fraction, not just an equal
rational number. Its production is charged once the norm list is serialized. -/
def lossOutputsInTime (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (β : Fin d → ℚ) :
    TM2OutputsInTime Machine.computer (listEncoding.encode (losses p A y β))
      (some (sum (losses p A y β)).encode)
      (time.eval (listEncoding.encode (losses p A y β)).length) :=
  outputsInTime (Fraction.zero, losses p A y β)

theorem list_length (xs : List Fraction) :
    (listEncoding.encode xs).length = 6 + (xs.map (fun x => x.encode.length + 1)).sum := by
  simp [listEncoding, encode, fields, field, List.length_flatMap, Fraction.encode_length,
    Fraction.zero]
  omega

/-- Bound the actual summation source in the original input/certificate bits.
The list contains one norm per observation, including repeated observations. -/
theorem loss_input_length_le (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    (listEncoding.encode (losses p A y β)).length ≤
      6 + totalBits A y B β * (4 * normWidth p (totalBits A y B β) + 4) := by
  rw [list_length]
  have hs := (source_bounds A y B β hr).1
  have hsum : ((losses p A y β).map (fun x => x.encode.length + 1)).sum ≤
      r * (4 * normWidth p (totalBits A y B β) + 4) := by
    calc
      _ ≤ ((losses p A y β).map (fun _ => 4 * normWidth p (totalBits A y B β) + 4)).sum := by
        apply List.sum_le_sum
        intro x hx
        have := Fraction.encode_length_le (norm_bounds p A y B β hr x hx)
        omega
      _ = _ := by simp [losses, Function.comp_def]
  nlinarith

def lossTime (p : ℕ) : Polynomial ℕ := time.comp
  (6 + Polynomial.X * (4 * (Polynomial.C p.size * ((Polynomial.X + 1) *
    (2 * Polynomial.X + 1)) + 1) + 4))

theorem lossTime_eval (p s : ℕ) : (lossTime p).eval s =
    time.eval (6 + s * (4 * normWidth p s + 4)) := by
  simp [lossTime, Polynomial.eval_comp, normWidth, residualWidth]

/-- Actual summation-machine time measured against the original binary size.
Constructing the serialized norm list is explicitly outside this endpoint. -/
def boundedLossOutputsInTime (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    TM2OutputsInTime Machine.computer (listEncoding.encode (losses p A y β))
      (some (sum (losses p A y β)).encode) ((lossTime p).eval (totalBits A y B β)) := by
  apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (lossOutputsInTime p A y β)
  rw [lossTime_eval]
  exact LeanNPHardness.MachineRuntime.polynomial_eval_mono _ (loss_input_length_le p A y B β hr)

#print axioms computableInPolyTime
#print axioms sumComputableInPolyTime
#print axioms run_bounded
#print axioms lossOutputsInTime
#print axioms boundedLossOutputsInTime
#print axioms output_length_le
#print axioms value_correct

end
end PhdThesisLean.RationalSum
