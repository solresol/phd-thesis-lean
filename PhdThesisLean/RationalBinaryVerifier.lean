import PhdThesisLean.RationalRecordAssembly

/-!
# A total polynomial-time verifier on the original binary regression record

Original binary dimensions, rational data, threshold and counted certificate
enter one finite machine. Parsing, source assembly, certificate broadcast,
residual arithmetic, fixed-prime norms, summation and comparison are all charged.
Malformed records return false. NP membership and the hardness encoding bridge
are separate class-level obligations.
-/
namespace PhdThesisLean.RationalBinaryVerifier

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness RationalVerifierBounds
open RationalRecordAssembly (Cell Out Part part route assemble)
open RationalRecordSource (Input wire)
set_option backward.isDefEq.respectTransparency false

/-- A fixed negative threshold for the empty loss, used only after rejection. -/
def rejected : Input := (⟨([],[]),by simp [RationalRegressionInternal.Compatible]⟩,⟨-1,1,by decide⟩)

theorem rejected_encode : RationalRegressionInternal.encoding.encode rejected =
    RationalRecordAssembly.rejectWord := by rfl

theorem check_rejected (p : ℕ) [Fact p.Prime] :
    RationalRegressionInternal.check p rejected = false := by rfl

theorem part_map_keep {α : Type} (p q : Part) (xs : List α) (f : α → Cell) (g : α → Out)
    (h : ∀ x, route (f x) = some (p,g x)) :
    part q (xs.map f) = if q=p then xs.map g else [] := by
  by_cases hp : q=p
  · subst q
    induction xs with
    | nil => simp [part]
    | cons x xs ih => simp [part,h,ih]
  · induction xs with
    | nil => simp [part,hp]
    | cons x xs ih => simp [part,h,hp,ih]

theorem part_row_map (p : Part) (rs : List (Option RationalCertificateBroadcast.Machine.RowCell)) :
    part p (rs.map (fun c => Sum.inl (RationalRectangularFields.rowCell c))) =
      if p=.rows then rs.map (fun c => Sum.inl (Sum.inr c)) else [] := by
  apply part_map_keep
  intro c
  cases c
  all_goals try casesm* RationalCertificateBroadcast.Machine.RowCell
  all_goals try casesm* RationalCertificateBroadcast.Machine.Wire
  all_goals rfl

theorem part_cert_map (p : Part) (cs : List (Option Bool)) :
    part p (cs.map (fun c => Sum.inr (Sum.inl c))) =
      if p=.cert then cs.map (fun c => Sum.inl (Sum.inl c)) else [] :=
  part_map_keep .cert p cs _ _ (by intro c; rfl)

theorem part_bound_map (p : Part) (bs : List Bool) :
    part p (bs.map (fun c => Sum.inr (Sum.inr c))) =
      if p=.bound then bs.map Sum.inr else [] :=
  part_map_keep .bound p bs _ _ (by intro c; rfl)

/-- Exact physical agreement, including all row and fraction delimiters. -/
theorem assemble_wire (x : Input) : assemble (wire x) = RationalRegressionInternal.encoding.encode x := by
  rw [assemble,ite_eq_right (RationalRecordSource.wire_ne_nil x)]
  have hw : wire x =
      ((RationalCertificateBroadcast.listEncoding RationalCertificateBroadcast.rowEncoding).encode x.1.val.2).map
        (fun c => Sum.inl (RationalRectangularFields.rowCell c)) ++ [.inl .dataEnd] ++
      (RationalNormList.encoding.encode x.1.val.1).map (fun c => Sum.inr (Sum.inl c)) ++
      x.2.encode.map (fun c => Sum.inr (Sum.inr c)) := by
    simp [wire,RationalRecordValidation.outputEncoding,PairEncoding.finEncoding,
      RationalRectangularFields.outputEncoding,RationalTailAssembly.outputEncoding,
      RationalCertificateTail.resultEncoding,RationalNorm.fractionEncoding,
      List.map_map,Function.comp_def,List.append_assoc]
  dsimp only [RationalNormList.encoding] at hw
  rw [hw]
  simp only [RationalRecordAssembly.part_append,part_row_map,part_cert_map,part_bound_map]
  simp [part,route,RationalRegressionInternal.encoding,RationalRegressionInternal.sourceEncoding,
    RationalCertificateBroadcast.sourceEncoding,PairEncoding.finEncoding,
    RationalNorm.fractionEncoding,RationalNormList.encoding,List.map_map,Function.comp_def,List.append_assoc]

/-- Semantic extraction only; execution is supplied by the proved assembly
machine, not by this decoder. -/
noncomputable def source (bits : List Bool) : Input :=
  (RationalRegressionInternal.encoding.decode (assemble (RationalRecordParser.output bits))).getD rejected

theorem source_of_wire (bits : List Bool) (x : Input)
    (h : RationalRecordParser.output bits = wire x) : source bits = x := by
  simp [source,h,assemble_wire]

theorem source_of_invalid (bits : List Bool) (h : ¬ RationalRecordValidation.Validated bits) :
    source bits = rejected := by
  rw [source,(RationalRecordParser.output_nil_iff bits).2 h]
  simp only [assemble,ite_true,← rejected_encode,FinEncoding.decode_encode,Option.getD_some]

theorem source_encode (bits : List Bool) :
    RationalRegressionInternal.encoding.encode (source bits) = assemble (RationalRecordParser.output bits) := by
  by_cases h : RationalRecordValidation.Validated bits
  · obtain ⟨x,hx⟩ := RationalRecordSource.exists_source bits h
    rw [source_of_wire bits x hx,hx,assemble_wire]
  · rw [source_of_invalid bits h,rejected_encode,(RationalRecordParser.output_nil_iff bits).2 h]
    rfl

/-- Original bits through total validation and actual linear-time reordering. -/
noncomputable def sourceComputableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding
      RationalRegressionInternal.encoding source := by
  let machine := MachineComposition.compositionComputableInPolyTime _ _ _ _ _
    RationalRecordParser.computableInPolyTime RationalRecordAssembly.computableInPolyTime
  exact { machine with
    outputsFun := fun bits => by
      simpa only [source_encode,RationalRecordAssembly.outputEncoding,Function.comp_apply]
        using! machine.outputsFun bits }

theorem source_original {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    source (RationalWitnessEncoding.encodeInput A y B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β)) =
        (RationalRegressionInternal.regressionSource A y β,Fraction.ofRat B) :=
  source_of_wire _ _ (RationalRecordSource.output_original A y B β hr)

theorem source_length_le (bits : List Bool) :
    (RationalRegressionInternal.encoding.encode (source bits)).length ≤ 16*bits.length+21 := by
  rw [source_encode]
  have hp := RationalRecordParser.output_length_le bits
  have ha := RationalRecordAssembly.assemble_length_le (RationalRecordParser.output bits)
  omega

variable (p : ℕ) [Fact p.Prime]

noncomputable def check (bits : List Bool) : Bool := RationalRegressionInternal.check p (source bits)

/-- The whole verifier, including every arithmetic and structural transfer, is
polynomial in the original binary record length. The prime is fixed. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding finEncodingBoolBool (check p) :=
  MachineComposition.compositionComputableInPolyTime _ _ _ _ _
    sourceComputableInPolyTime (RationalRegressionInternal.computableInPolyTime p)

theorem check_invalid (bits : List Bool) (h : ¬ RationalRecordValidation.Validated bits) :
    check p bits = false := by rw [check,source_of_invalid bits h,check_rejected]

/-- The stored fractions need not be reduced. This formula identifies the
actual loss on every compatible parsed source, including zero rows/columns. -/
theorem check_stored_values (x : Input) : RationalRegressionInternal.check p x = true ↔
    (x.1.val.2.map (fun row => padicNorm p (row.1.value -
      ((row.2.zip x.1.val.1).map (fun pair => pair.1.value * pair.2.value)).sum))).sum ≤ x.2.value := by
  rw [RationalRegressionInternal.check,Fraction.le_correct]
  simp [RationalRegressionInternal.loss,RationalRegressionInternal.residuals,
    RationalRegressionInternal.rows,sum,value_fold_add,List.map_map,
    Fraction.value_norm,RationalRowResidual.evaluate,RationalDotProduct.multiply,
    Function.comp_def]

/-- No raw word can bypass the typed arithmetic contract or parse rejection. -/
theorem check_true_iff (bits : List Bool) : check p bits = true ↔
    ∃ x : Input, RationalRecordParser.output bits = wire x ∧
      RationalRegressionInternal.check p x = true := by
  constructor
  · intro hc
    have hv : RationalRecordValidation.Validated bits := by
      by_contra h
      rw [check_invalid p bits h] at hc
      contradiction
    obtain ⟨x,hx⟩ := RationalRecordSource.exists_source bits hv
    exact ⟨x,hx,by simpa only [check,source_of_wire bits x hx] using hc⟩
  · rintro ⟨x,hx,hc⟩
    simpa only [check,source_of_wire bits x hx] using hc

theorem check_original {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    check p (RationalWitnessEncoding.encodeInput A y B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β)) = RationalVerifierBounds.check p A y B β := by
  rw [check,source_original A y B β hr,RationalRegressionInternal.check_regression]

/-- Statement-faithful summed p-adic regression on the original binary words. -/
theorem check_correct {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    check p (RationalWitnessEncoding.encodeInput A y B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β)) = true ↔
        RationalWitnesses.loss p A y β ≤ B := by
  rw [check_original p A y B β hr,RationalVerifierBounds.check_correct]

noncomputable def outputsInTime (bits : List Bool) :
    TM2OutputsInTime (computableInPolyTime p).tm
      (bits.map (computableInPolyTime p).inputAlphabet.symm)
      (some ([check p bits].map (computableInPolyTime p).outputAlphabet.symm))
      ((computableInPolyTime p).time.eval bits.length) := (computableInPolyTime p).outputsFun bits

/-- No preparsed data, precomputed loss or arithmetic-cost premise is supplied. -/
noncomputable def originalOutputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    TM2OutputsInTime (computableInPolyTime p).tm
      ((RationalWitnessEncoding.encodeInput A y B ++
        RationalWitnessEncoding.encodeRats (List.ofFn β)).map (computableInPolyTime p).inputAlphabet.symm)
      (some ([RationalVerifierBounds.check p A y B β].map (computableInPolyTime p).outputAlphabet.symm))
      ((computableInPolyTime p).time.eval (totalBits A y B β)) := by
  simpa only [check_original p A y B β hr,List.length_append,totalBits] using!
    outputsInTime p (RationalWitnessEncoding.encodeInput A y B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β))

/-- The complete verifier's clock after substituting the proved witness bound. -/
noncomputable def shortTime : Polynomial ℕ :=
  (computableInPolyTime p).time.comp (12*Polynomial.X^3+10*Polynomial.X+1)

noncomputable def shortOriginalOutputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r)
    (hβ : (RationalWitnessEncoding.encodeRats (List.ofFn β)).length ≤
      12*(RationalWitnessEncoding.encodeInput A y B).length^3 +
        9*(RationalWitnessEncoding.encodeInput A y B).length+1) :
    TM2OutputsInTime (computableInPolyTime p).tm
      ((RationalWitnessEncoding.encodeInput A y B ++
        RationalWitnessEncoding.encodeRats (List.ofFn β)).map (computableInPolyTime p).inputAlphabet.symm)
      (some ([RationalVerifierBounds.check p A y B β].map (computableInPolyTime p).outputAlphabet.symm))
      ((shortTime p).eval (RationalWitnessEncoding.encodeInput A y B).length) := by
  apply MachinePrimitives.evalsToInTimeMono (originalOutputsInTime p A y B β hr)
  simp only [shortTime,Polynomial.eval_comp]
  apply MachineRuntime.polynomial_eval_mono
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,totalBits]
  omega

/-- This joins size and binary-machine correctness, while the class-level NP
language/encoding declaration remains a separate obligation. -/
theorem threshold_iff_short_verifier {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (hr : 0 < r) :
    (∃ β, RationalWitnesses.loss p A y β ≤ B) ↔
      ∃ β : Fin d → ℚ, check p (RationalWitnessEncoding.encodeInput A y B ++
        RationalWitnessEncoding.encodeRats (List.ofFn β)) = true ∧
          (RationalWitnessEncoding.encodeRats (List.ofFn β)).length ≤
            12*(RationalWitnessEncoding.encodeInput A y B).length^3 +
              9*(RationalWitnessEncoding.encodeInput A y B).length+1 := by
  simp only [check_correct p A y B _ hr]
  exact RationalWitnessEncoding.threshold_iff_short_certificate p A y B hr

#print axioms assemble_wire
#print axioms source_encode
#print axioms sourceComputableInPolyTime
#print axioms computableInPolyTime
#print axioms check_stored_values
#print axioms check_true_iff
#print axioms check_correct
#print axioms check_invalid
#print axioms originalOutputsInTime
#print axioms shortOriginalOutputsInTime
#print axioms threshold_iff_short_verifier

end PhdThesisLean.RationalBinaryVerifier
