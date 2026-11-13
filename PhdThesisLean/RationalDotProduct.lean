import PhdThesisLean.RationalDotProductMachine

/-!
# Polynomial-time runtime-length rational dot products

The input contains paired fraction words, one pair per column. Every variable
product, traversal, transfer and exact summation is charged. Original-record
parsing and pairing a row with the certificate remain separate obligations.
-/
namespace PhdThesisLean.RationalDotProduct

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open RationalVerifierBounds
open RationalSum (field fields)
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)
open LeanNPHardness.MachineComposition

set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Includes collecting each result and the later reversal of that result. -/
def passTime : Polynomial ℕ := Machine.body.time +
  Polynomial.C 4 * Polynomial.X + 6

theorem passTime_eval (s : ℕ) : passTime.eval s =
    Machine.body.time.eval s + 4 * s + 6 := by
  simp [passTime]

/-- The prefix is stored in reverse order and is never recopied during a call.
The bound charges its final reversal as well as all future output symbols. -/
def run_bounded (xs : List (Fraction × Fraction)) (acc : List (Option Bool)) (s : ℕ)
    (h : (pairFields xs).length ≤ s) :
    Machine.Run (Machine.ready xs acc)
      (Machine.done
        (field Fraction.zero ++ acc.reverse ++ fields (xs.map multiply)))
      ((xs.length + 1) * passTime.eval s + acc.length) := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.map_nil, fields, List.flatMap_nil, List.append_nil]
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono
        (Machine.exit_run acc)
      simp only [List.length_nil, zero_add, one_mul, passTime_eval]
      omega
  | cons x xs ih =>
      have hin : (RationalArithmetic.encode x).length ≤ s := by
        simp only [pairFields, List.flatMap_cons, List.length_append, pairField, List.length_map,
          List.length_singleton] at h
        omega
      have htail : (pairFields xs).length ≤ s := by
        simp only [pairFields, List.flatMap_cons, List.length_append] at h ⊢
        omega
      have hout : (multiply x).encode.length ≤ s :=
        (RationalArithmetic.multiplication_length_le x).trans hin
      have hcost := LeanNPHardness.MachineRuntime.polynomial_eval_mono
        Machine.body.time hin
      have hrun := Machine.seq (Machine.iteration_cycle x xs acc)
        (ih ((field (multiply x)).reverse ++ acc) htail)
      simp only [List.reverse_append, List.reverse_reverse, List.map_cons, fields,
        List.flatMap_cons, List.append_assoc] at hrun ⊢
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono hrun
      simp only [List.length_cons, List.length_append, List.length_reverse,
        field, List.length_map, List.length_nil, passTime_eval]
      nlinarith

def time : Polynomial ℕ := (Polynomial.X + 1) * passTime

theorem time_eval (s : ℕ) : time.eval s =
    (s + 1) * (Machine.body.time.eval s + 4 * s + 6) := by
  simp [time, passTime_eval]

/-- Produces the exact original format consumed by the existing summation
machine, including its fixed six-symbol initial-zero field. -/
def outputsInTime (xs : List (Fraction × Fraction)) :
    TM2OutputsInTime Machine.computer (pairFields xs)
      (some (RationalSum.listEncoding.encode (xs.map multiply)))
      (time.eval (pairFields xs).length) := by
  have h := run_bounded xs [] (pairFields xs).length le_rfl
  have h' := LeanNPHardness.MachinePrimitives.evalsToInTimeMono h
    (show (xs.length + 1) * passTime.eval (pairFields xs).length + [].length ≤
        time.eval (pairFields xs).length by
      simpa [time] using Nat.mul_le_mul_right (passTime.eval (pairFields xs).length)
        (Nat.add_le_add_right (count_le_length xs) 1))
  simpa only [Machine.ready_eq_initList, Machine.done_eq_haltList, List.reverse_nil,
    List.append_nil, RationalSum.listEncoding, RationalSum.encode] using! h'

def computableInPolyTime : TM2ComputableInPolyTime encoding RationalSum.listEncoding
    (List.map multiply) where
  tm := Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := time
  outputsFun xs := by simpa [Equiv.refl, encoding] using outputsInTime xs

/-- A linear bound on the complete produced product list. -/
theorem output_length_le (xs : List (Fraction × Fraction)) :
    (RationalSum.listEncoding.encode (xs.map multiply)).length ≤
      (pairFields xs).length + 6 := by
  rw [RationalSum.list_length, pairFields_length]
  have hs : ((xs.map multiply).map (fun x => x.encode.length + 1)).sum ≤
      (xs.map (fun x => (RationalArithmetic.encode x).length + 1)).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        have hx : (multiply x).encode.length ≤ (RationalArithmetic.encode x).length :=
          RationalArithmetic.multiplication_length_le x
        simp only [List.map_cons, List.sum_cons]
        nlinarith
  omega

/-- A composed finite machine: paired fractions to their exact dot product. All
map/sum adapter transfers are part of the polynomial-time witness. -/
def sumComputableInPolyTime : TM2ComputableInPolyTime encoding RationalNorm.fractionEncoding
    (fun xs => sum (xs.map multiply)) :=
  compositionComputableInPolyTime _ _ _ _ _
    computableInPolyTime RationalSum.sumComputableInPolyTime

theorem value_correct (xs : List (Fraction × Fraction)) :
    (sum (xs.map multiply)).value = (xs.map (fun x => x.1.value * x.2.value)).sum := by
  simp [sum, value_fold_add, List.map_map, Function.comp_def, multiply]


/-- Columns retain their order and multiplicity, including a zero-column row. -/
def pairs {d : ℕ} (row β : Fin d → ℚ) : List (Fraction × Fraction) :=
  List.ofFn fun j => (Fraction.ofRat (row j), Fraction.ofRat (β j))

theorem map_pairs {d : ℕ} (row β : Fin d → ℚ) :
    (pairs row β).map multiply = products row β := by
  simp [pairs, products, multiply, List.map_ofFn, Function.comp_def]

theorem dot_value_correct {d : ℕ} (row β : Fin d → ℚ) :
    (sum ((pairs row β).map multiply)).value = ∑ j, row j * β j := by
  rw [PhdThesisLean.RationalDotProduct.value_correct]
  simp [pairs, List.map_ofFn, List.sum_ofFn]

/-- Exact unreduced product accumulation, from an already paired row. -/
def dotOutputsInTime {d : ℕ} (row β : Fin d → ℚ) :
    TM2OutputsInTime sumComputableInPolyTime.tm
      ((pairFields (pairs row β)).map sumComputableInPolyTime.inputAlphabet.symm)
      (some ((sum (products row β)).encode.map sumComputableInPolyTime.outputAlphabet.symm))
      (sumComputableInPolyTime.time.eval (pairFields (pairs row β)).length) := by
  simpa only [map_pairs, encoding, RationalNorm.fractionEncoding] using!
    sumComputableInPolyTime.outputsFun (pairs row β)

/-- Original data and certificate bits charge the paired row source too. -/
theorem row_input_length_le {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) (i : Fin r) :
    (pairFields (pairs (A i) β)).length ≤
      totalBits A y B β * (8 * totalBits A y B β + 7) := by
  rw [pairFields_length]
  have hs := source_bounds A y B β hr
  have hsum : ((pairs (A i) β).map (fun x => (RationalArithmetic.encode x).length + 1)).sum ≤
      d * (8 * totalBits A y B β + 7) := by
    calc
      _ ≤ ((pairs (A i) β).map (fun _ => 8 * totalBits A y B β + 7)).sum := by
        apply List.sum_le_sum
        intro x hx
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
        have ha := Fraction.encode_length_le (hs.2.2.2.2.1 i j)
        have hb := Fraction.encode_length_le (hs.2.2.2.2.2 j)
        simp only [RationalArithmetic.encode, List.length_append]
        omega
      _ = _ := by simp [pairs, Function.comp_def]
  have hd := hs.2.1
  nlinarith

def rowTime : Polynomial ℕ := sumComputableInPolyTime.time.comp
  (Polynomial.X * (8 * Polynomial.X + 7))

theorem rowTime_eval (s : ℕ) : rowTime.eval s =
    sumComputableInPolyTime.time.eval (s * (8 * s + 7)) := by
  simp [rowTime, Polynomial.eval_comp]

/-- Actual product traversal and summation time in original combined bits.
This size substitution does not charge production of the paired source. -/
def boundedDotOutputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) (i : Fin r) :
    TM2OutputsInTime sumComputableInPolyTime.tm
      ((pairFields (pairs (A i) β)).map sumComputableInPolyTime.inputAlphabet.symm)
      (some ((sum (products (A i) β)).encode.map sumComputableInPolyTime.outputAlphabet.symm))
      (rowTime.eval (totalBits A y B β)) := by
  apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (dotOutputsInTime (A i) β)
  rw [rowTime_eval]
  exact LeanNPHardness.MachineRuntime.polynomial_eval_mono _ (row_input_length_le A y B β hr i)

#print axioms Machine.iteration_cycle
#print axioms run_bounded
#print axioms computableInPolyTime
#print axioms sumComputableInPolyTime
#print axioms output_length_le
#print axioms boundedDotOutputsInTime
#print axioms dot_value_correct

end
end PhdThesisLean.RationalDotProduct
