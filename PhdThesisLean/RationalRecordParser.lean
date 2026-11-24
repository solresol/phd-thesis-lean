import PhdThesisLean.RationalRecordValidation

/-!
# A total polynomial-time parser for the original regression record

The final finite-machine pass combines both validation outcomes. It returns
the retained rows and the validated certificate/threshold pair, or the empty
word on any malformed record. This is parsing, not the regression loss test.
-/
namespace PhdThesisLean.RationalRecordParser

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness RationalVerifierBounds
set_option backward.isDefEq.respectTransparency false

abbrev Cell := Sum RationalRectangularFields.Cell RationalTailAssembly.Out
def good (bs : List Cell) : Bool := bs.any Sum.isLeft && bs.any Sum.isRight
def guard (bs : List Cell) : List Cell := if good bs then bs else []

namespace Machine
inductive Label | scan (left right : Bool) | finish (keep : Bool) deriving DecidableEq, Fintype
inductive Stack | input | saved | output deriving DecidableEq, Fintype
abbrev State := Option Cell
def Alphabet (_ : Stack) := Cell
def go (l : Label) : TM2.Stmt Alphabet Label State := .load (fun _ => none) (.goto fun _ => l)
def program : Label → TM2.Stmt Alphabet Label State
  | .scan l r => .pop .input (fun _ b => b) <| .branch Option.isSome
      (.push .saved (fun s => s.getD (.inl .dataEnd)) <|
        .branch (fun s => (s.getD (.inl .dataEnd)).isLeft)
          (go (.scan true r)) (go (.scan l true)))
      (go (.finish (l && r)))
  | .finish keep => .pop .saved (fun _ b => b) <| .branch Option.isSome
      (if keep then .push .output (fun s => s.getD (.inl .dataEnd)) (go (.finish keep))
        else go (.finish keep)) (.load (fun _ => none) .halt)
def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan false false
  σ := State
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Cell)
  m := program
def contents (bs saved out : List Cell) : (k : Stack) → List (Alphabet k)
  | .input => bs | .saved => saved | .output => out
def cfg (l : Label) (bs saved out : List Cell) : computer.Cfg := ⟨some l,none,contents bs saved out⟩

theorem step_scan (l r : Bool) (b : Cell) (bs saved out : List Cell) :
    computer.step (cfg (.scan l r) (b::bs) saved out) =
      some (cfg (.scan (l || b.isLeft) (r || b.isRight)) bs (b::saved) out) := by
  cases b <;> simp [cfg,computer,FinTM2.step,program,go,contents,Function.update]
  all_goals funext k; cases k <;> rfl

theorem scan_run (l r : Bool) (bs saved out : List Cell) :
    (fun q => q.bind computer.step)^[bs.length+1] (some (cfg (.scan l r) bs saved out)) =
      some (cfg (.finish ((l || bs.any Sum.isLeft) && (r || bs.any Sum.isRight)))
        [] (bs.reverse++saved) out) := by
  induction bs generalizing l r saved with
  | nil => simp [cfg,computer,FinTM2.step,program,go,contents,Function.update]
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply,Option.bind_some,step_scan,ih]
      simp [List.reverse_cons,List.append_assoc,Bool.or_assoc]

theorem finish_run (keep : Bool) (saved out : List Cell) :
    (fun q => q.bind computer.step)^[saved.length+1] (some (cfg (.finish keep) [] saved out)) =
      some (haltList computer ((if keep then saved.reverse else []) ++ out)) := by
  induction saved generalizing out with
  | nil =>
      simp [cfg,computer,FinTM2.step,program,go,contents,haltList]
      funext k; cases k <;> rfl
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      have hs : computer.step (cfg (.finish keep) [] (b::bs) out) =
          some (cfg (.finish keep) [] bs (if keep then b::out else out)) := by
        cases keep <;> simp [cfg,computer,FinTM2.step,program,go,contents,Function.update]
        all_goals funext k; cases k <;> rfl
      rw [Option.bind_some,hs,ih]
      cases keep <;> simp [List.reverse_cons,List.append_assoc]

noncomputable def outputsInTime (bs : List Cell) :
    TM2OutputsInTime computer bs (some (guard bs)) (2*bs.length+2) := by
  have hi : initList computer bs = cfg (.scan false false) bs [] [] := by
    unfold initList cfg computer; congr; funext k; cases k <;> rfl
  refine { steps := (bs.length+1)+(bs.length+1), steps_le_m := by omega,
           evals_in_steps := ?_ }
  change (fun q => q.bind computer.step)^[_] (some (initList computer bs)) = _
  rw [hi,Function.iterate_add_apply,scan_run]
  simp only [Bool.false_or,List.append_nil]
  simpa [guard,good] using finish_run (good bs) bs.reverse []
end Machine

def outputEncoding : FinEncoding (List Cell) where
  Γ := Cell
  encode := id
  decode := some
  decode_encode _ := rfl
  ΓFin := inferInstance

theorem guard_encode (x : RationalRecordValidation.Result) :
    guard (RationalRecordValidation.outputEncoding.encode x) =
      if x.1 = [] ∨ x.2 = [] then [] else RationalRecordValidation.outputEncoding.encode x := by
  rcases x with ⟨rows,tail⟩
  cases rows <;> cases tail <;>
    simp [guard,good,RationalRecordValidation.outputEncoding,PairEncoding.finEncoding,
      RationalRectangularFields.outputEncoding,RationalTailAssembly.outputEncoding,
      List.any_map,Function.comp_def]

noncomputable def guardComputableInPolyTime :
    TM2ComputableInPolyTime RationalRecordValidation.outputEncoding outputEncoding
      (fun x => guard (RationalRecordValidation.outputEncoding.encode x)) where
  tm := Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2*Polynomial.X+2
  outputsFun x := by
    simpa [outputEncoding,Equiv.refl] using! Machine.outputsInTime
      (RationalRecordValidation.outputEncoding.encode x)

def output (bits : List Bool) : List Cell :=
  guard (RationalRecordValidation.outputEncoding.encode (RationalRecordValidation.output bits))

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding outputEncoding output :=
  MachineComposition.compositionComputableInPolyTime _ _ _ RationalRecordValidation.output
    (fun x => guard (RationalRecordValidation.outputEncoding.encode x))
    RationalRecordValidation.computableInPolyTime guardComputableInPolyTime

theorem output_eq (bits : List Bool) : output bits =
    if RationalRecordValidation.Validated bits then
      RationalRecordValidation.outputEncoding.encode (RationalRecordValidation.output bits) else [] := by
  rw [output,guard_encode]
  simp only [RationalRecordValidation.Validated]
  by_cases hl : (RationalRecordValidation.output bits).1 = []
  all_goals by_cases hr : (RationalRecordValidation.output bits).2 = []
  all_goals simp [hl,hr]

theorem output_success_iff (bits : List Bool) :
    output bits ≠ [] ↔ RationalRecordValidation.Validated bits := by
  rw [output_eq]
  by_cases h : RationalRecordValidation.Validated bits
  · simp only [h,↓reduceIte,iff_true]
    simpa [RationalRecordValidation.outputEncoding,PairEncoding.finEncoding,
      RationalRectangularFields.outputEncoding,RationalTailAssembly.outputEncoding]
      using (not_and_or.mpr (Or.inl h.1))
  · simp [h]

theorem output_nil_iff (bits : List Bool) :
    output bits = [] ↔ ¬ RationalRecordValidation.Validated bits := by
  simpa using not_congr (output_success_iff bits)

theorem output_length_le (bits : List Bool) : (output bits).length ≤ 16*bits.length+14 := by
  rw [output_eq]
  split
  · exact RationalRecordValidation.output_length_le bits
  · simp

theorem output_original {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    output (RationalWitnessEncoding.encodeInput A y B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β)) =
      RationalRecordValidation.outputEncoding.encode
        (((RationalCertificateBroadcast.listEncoding RationalCertificateBroadcast.rowEncoding).encode
          (RationalCertificateBroadcast.observations A y)).map RationalRectangularFields.rowCell ++ [.dataEnd],
          RationalCertificateTail.resultEncoding.encode
            (RationalCertificateBroadcast.certificate β,Fraction.ofRat B)) := by
  rw [output_eq,ite_eq_left (RationalRecordValidation.validated_original A y B β hr),
    RationalRecordValidation.output_original A y B β hr]

noncomputable def outputsInTime (bits : List Bool) :
    TM2OutputsInTime computableInPolyTime.tm
      (bits.map computableInPolyTime.inputAlphabet.symm)
      (some ((output bits).map computableInPolyTime.outputAlphabet.symm))
      (computableInPolyTime.time.eval bits.length) := computableInPolyTime.outputsFun bits

/-- Total original-word parsing with all rejection cleanup, retaining exact
internal rows, certificate and threshold on a valid rational record. -/
noncomputable def originalOutputsInTime {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    TM2OutputsInTime computableInPolyTime.tm
      ((RationalWitnessEncoding.encodeInput A y B ++
        RationalWitnessEncoding.encodeRats (List.ofFn β)).map computableInPolyTime.inputAlphabet.symm)
      (some ((RationalRecordValidation.outputEncoding.encode
        (((RationalCertificateBroadcast.listEncoding RationalCertificateBroadcast.rowEncoding).encode
          (RationalCertificateBroadcast.observations A y)).map RationalRectangularFields.rowCell ++ [.dataEnd],
          RationalCertificateTail.resultEncoding.encode
            (RationalCertificateBroadcast.certificate β,Fraction.ofRat B))).map
              computableInPolyTime.outputAlphabet.symm))
      (computableInPolyTime.time.eval (totalBits A y B β)) := by
  simpa only [output_original A y B β hr,List.length_append,totalBits] using!
    outputsInTime (RationalWitnessEncoding.encodeInput A y B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β))

#print axioms Machine.outputsInTime
#print axioms computableInPolyTime
#print axioms output_success_iff
#print axioms output_nil_iff
#print axioms output_original
#print axioms originalOutputsInTime

end PhdThesisLean.RationalRecordParser
