import PhdThesisLean.RationalNormListMachine

/-!
# Polynomial-time norm traversal and summed loss from serialized residuals

The input is a runtime-length internal delimited list, retaining the original
Boolean fraction words. Norm production, the zero prefix, transfers and exact
summation are charged. Computing residuals and parsing the original regression
record are separate obligations.
-/
namespace PhdThesisLean.RationalNormList

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open RationalVerifierBounds
open RationalSum (field fields)
open LeanNPHardness (FinEncoding TM2ComputableInPolyTime)
open LeanNPHardness.MachineComposition

set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- No hidden initial accumulator in the source encoding. -/
def encoding : FinEncoding (List Fraction) where
  Γ := Option Bool
  encode := fields
  decode bits := RationalSum.readFields bits []
  decode_encode := RationalSum.readFields_fields
  ΓFin := inferInstance

theorem fields_length (xs : List Fraction) :
    (fields xs).length = (xs.map (fun x => x.encode.length + 1)).sum := by
  simp [fields, field, List.length_flatMap]

theorem count_le_length (xs : List Fraction) : xs.length ≤ (fields xs).length := by
  induction xs with
  | nil => simp [fields]
  | cons x xs ih =>
      simp only [fields, List.flatMap_cons, field, List.length_append, List.length_map,
        List.length_cons] at *
      omega

variable (p : ℕ) [Fact p.Prime]

/-- Includes collecting each result and the later reversal of that result. -/
def passTime : Polynomial ℕ := (Machine.body (p := p)).time +
  Polynomial.C (8 * p.size + 2) * Polynomial.X + 20

theorem passTime_eval (s : ℕ) : (passTime p).eval s =
    (Machine.body (p := p)).time.eval s + (8 * p.size + 2) * s + 20 := by
  simp [passTime]

/-- The prefix is stored in reverse order and is never recopied during a call.
The bound charges its final reversal as well as all future output symbols. -/
def run_bounded (xs : List Fraction) (acc : List (Option Bool)) (s : ℕ)
    (h : (fields xs).length ≤ s) :
    Machine.Run (Machine.ready (p := p) xs acc)
      (Machine.done (p := p)
        (field Fraction.zero ++ acc.reverse ++ fields (xs.map (Fraction.norm p))))
      ((xs.length + 1) * (passTime p).eval s + acc.length) := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.map_nil, fields, List.flatMap_nil, List.append_nil]
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono
        (Machine.exit_run (p := p) acc)
      simp only [List.length_nil, zero_add, one_mul, passTime_eval]
      omega
  | cons x xs ih =>
      have hin : x.encode.length ≤ s := by
        simp only [fields, List.flatMap_cons, List.length_append, field, List.length_map,
          List.length_singleton] at h
        omega
      have htail : (fields xs).length ≤ s := by
        simp only [fields, List.flatMap_cons, List.length_append] at h ⊢
        omega
      have hout := RationalNorm.output_length_le p x
      have hout' : (x.norm p).encode.length ≤ 4 * p.size * s + 7 :=
        hout.trans (by nlinarith)
      have hcost := LeanNPHardness.MachineRuntime.polynomial_eval_mono
        (Machine.body (p := p)).time hin
      have hrun := Machine.seq (Machine.iteration_cycle (p := p) x xs acc)
        (ih ((field (x.norm p)).reverse ++ acc) htail)
      simp only [List.reverse_append, List.reverse_reverse, List.map_cons, fields,
        List.flatMap_cons, List.append_assoc] at hrun ⊢
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono hrun
      simp only [List.length_cons, List.length_append, List.length_reverse,
        field, List.length_map, List.length_nil, passTime_eval]
      nlinarith

def time : Polynomial ℕ := (Polynomial.X + 1) * passTime p

theorem time_eval (s : ℕ) : (time p).eval s =
    (s + 1) * ((Machine.body (p := p)).time.eval s + (8 * p.size + 2) * s + 20) := by
  simp [time, passTime_eval]

/-- Produces the exact original format consumed by the existing summation
machine, including its fixed six-symbol initial-zero field. -/
def outputsInTime (xs : List Fraction) :
    TM2OutputsInTime (Machine.computer (p := p)) (fields xs)
      (some (RationalSum.listEncoding.encode (xs.map (Fraction.norm p))))
      ((time p).eval (fields xs).length) := by
  have h := run_bounded p xs [] (fields xs).length le_rfl
  have h' := LeanNPHardness.MachinePrimitives.evalsToInTimeMono h
    (show (xs.length + 1) * (passTime p).eval (fields xs).length + [].length ≤
        (time p).eval (fields xs).length by
      simpa [time] using Nat.mul_le_mul_right ((passTime p).eval (fields xs).length)
        (Nat.add_le_add_right (count_le_length xs) 1))
  simpa only [Machine.ready_eq_initList, Machine.done_eq_haltList, List.reverse_nil,
    List.append_nil, RationalSum.listEncoding, RationalSum.encode] using! h'

def computableInPolyTime : TM2ComputableInPolyTime encoding RationalSum.listEncoding
    (List.map (Fraction.norm p)) where
  tm := Machine.computer (p := p)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := time p
  outputsFun xs := by simpa [Equiv.refl, encoding] using outputsInTime p xs

/-- A fixed-prime linear bound on the complete produced norm list. -/
theorem output_length_le (xs : List Fraction) :
    (RationalSum.listEncoding.encode (xs.map (Fraction.norm p))).length ≤
      (4 * p.size + 8) * (fields xs).length + 6 := by
  rw [RationalSum.list_length, fields_length]
  have hs : ((xs.map (Fraction.norm p)).map (fun x => x.encode.length + 1)).sum ≤
      (4 * p.size + 8) * (xs.map (fun x => x.encode.length + 1)).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        have hx := RationalNorm.output_length_le p x
        simp only [List.map_cons, List.sum_cons]
        nlinarith
  omega

/-- A composed finite machine: residual fractions to exact summed norm. All
map/sum adapter transfers are part of the polynomial-time witness. -/
def sumComputableInPolyTime : TM2ComputableInPolyTime encoding RationalNorm.fractionEncoding
    (fun xs => sum (xs.map (Fraction.norm p))) :=
  compositionComputableInPolyTime _ _ _ _ _
    (computableInPolyTime p) RationalSum.sumComputableInPolyTime

theorem value_correct (xs : List Fraction) :
    (sum (xs.map (Fraction.norm p))).value = (xs.map (fun x => padicNorm p x.value)).sum := by
  simp [sum, value_fold_add, List.map_map, Function.comp_def, Fraction.value_norm]

/-- Ordered observation list: repeated observations remain repeated entries. -/
def residuals {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ)
    (β : Fin d → ℚ) : List Fraction := List.ofFn fun i => residual (A i) β (y i)

theorem map_residuals {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (β : Fin d → ℚ) :
    (residuals A y β).map (Fraction.norm p) = losses p A y β := by
  simp [residuals, losses, List.map_ofFn, Function.comp_def]

/-- This endpoint starts with serialized residuals, not an already produced
norm list; its result is exactly the evaluator's stored loss fraction. -/
def lossOutputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (β : Fin d → ℚ) :
    TM2OutputsInTime (sumComputableInPolyTime p).tm
      ((encoding.encode (residuals A y β)).map (sumComputableInPolyTime p).inputAlphabet.symm)
      (some ((sum (losses p A y β)).encode.map (sumComputableInPolyTime p).outputAlphabet.symm))
      ((sumComputableInPolyTime p).time.eval (encoding.encode (residuals A y β)).length) := by
  simpa only [map_residuals, RationalNorm.fractionEncoding] using!
    (sumComputableInPolyTime p).outputsFun (residuals A y β)

theorem loss_value_correct {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (β : Fin d → ℚ) :
    (sum ((residuals A y β).map (Fraction.norm p))).value = RationalWitnesses.loss p A y β := by
  rw [map_residuals, value_loss]

/-- Charge the internal residual source in the original data/certificate bits. -/
theorem residual_input_length_le {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    (encoding.encode (residuals A y β)).length ≤
      totalBits A y B β * (4 * residualWidth (totalBits A y B β) + 4) := by
  rw [encoding, fields_length]
  have hs := (source_bounds A y B β hr).1
  have hsum : ((residuals A y β).map (fun x => x.encode.length + 1)).sum ≤
      r * (4 * residualWidth (totalBits A y B β) + 4) := by
    calc
      _ ≤ ((residuals A y β).map (fun _ => 4 * residualWidth (totalBits A y B β) + 4)).sum := by
        apply List.sum_le_sum
        intro x hx
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        have hb := Fraction.encode_length_le (residual_bounds A y B β hr i)
        omega
      _ = _ := by simp [residuals, Function.comp_def]
  nlinarith

def lossTime : Polynomial ℕ := (sumComputableInPolyTime p).time.comp
  (Polynomial.X * (4 * ((Polynomial.X + 1) * (2 * Polynomial.X + 1)) + 4))

theorem lossTime_eval (s : ℕ) : (lossTime p).eval s =
    (sumComputableInPolyTime p).time.eval (s * (4 * residualWidth s + 4)) := by
  simp [lossTime, Polynomial.eval_comp, residualWidth]

/-- Norm traversal plus summation in polynomial original combined bit size.
No cost for generating the residual source is inferred from its size bound. -/
def boundedLossOutputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    TM2OutputsInTime (sumComputableInPolyTime p).tm
      ((encoding.encode (residuals A y β)).map (sumComputableInPolyTime p).inputAlphabet.symm)
      (some ((sum (losses p A y β)).encode.map (sumComputableInPolyTime p).outputAlphabet.symm))
      ((lossTime p).eval (totalBits A y B β)) := by
  apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (lossOutputsInTime p A y β)
  rw [lossTime_eval]
  exact LeanNPHardness.MachineRuntime.polynomial_eval_mono _ (residual_input_length_le A y B β hr)

#print axioms Machine.iteration_cycle
#print axioms run_bounded
#print axioms computableInPolyTime
#print axioms sumComputableInPolyTime
#print axioms output_length_le
#print axioms boundedLossOutputsInTime
#print axioms loss_value_correct

end
end PhdThesisLean.RationalNormList
