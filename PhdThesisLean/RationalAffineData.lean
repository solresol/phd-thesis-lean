import PhdThesisLean.RationalRegressionNP

/-!
# Executed column-of-ones insertion for the affine verifier

The original binary data parser runs first. A finite transducer then increments
the retained unary column count and inserts the literal fraction one between
each response and its coefficients. The original threshold/certificate suffix
is preserved. All copying, reversal and transfers have machine time bounds.
-/
namespace PhdThesisLean.RationalAffineData

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness RationalVerifierBounds
open RationalRectangularFields (Cell)
set_option backward.isDefEq.respectTransparency false

abbrev Symbol := Sum Unit Cell
def isResponse : Symbol → Bool
  | .inr (.response _) => true
  | _ => false
def one : List Symbol :=
  (Fraction.ofRat 1).encode.map (fun b => .inr (.coefficient b)) ++ [.inr .fieldEnd]
def scan : Bool → List Symbol → List Symbol
  | _, [] => []
  | previous, b::bs =>
      (if previous && !isResponse b then one else []) ++ b :: scan (isResponse b) bs
def output (bs : List Symbol) : List Symbol := .inl () :: scan false bs

theorem one_eq : one =
    [.inr (.coefficient false),.inr (.coefficient true),.inr (.coefficient false),
     .inr (.coefficient true),.inr (.coefficient true),.inr (.coefficient false),
     .inr (.coefficient true),.inr .fieldEnd] := by rfl

theorem one_length : one.length = 8 := by decide
theorem scan_length_le (previous : Bool) (bs : List Symbol) :
    (scan previous bs).length ≤ 9*bs.length := by
  induction bs generalizing previous with
  | nil => simp [scan]
  | cons b bs ih =>
      simp only [scan,List.length_append,List.length_cons]
      have := ih (isResponse b)
      split <;> simp only [one_length,List.length_nil] <;> omega

namespace Machine
inductive Label | start | scan (previous : Bool) | finish deriving DecidableEq, Fintype
inductive Stack | input | saved | output deriving DecidableEq, Fintype
abbrev State := Option Symbol
def Alphabet (_ : Stack) := Symbol
def go (l : Label) : TM2.Stmt Alphabet Label State := .load (fun _ => none) (.goto fun _ => l)
def emit : List Symbol → TM2.Stmt Alphabet Label State → TM2.Stmt Alphabet Label State
  | [], next => next
  | b::bs, next => .push .saved (fun _ => b) (emit bs next)
def next : TM2.Stmt Alphabet Label State :=
  .push .saved (fun s => s.getD (.inl ())) <|
    .load (fun s => s) (.goto fun s => .scan (isResponse (s.getD (.inl ()))))
def program : Label → TM2.Stmt Alphabet Label State
  | .start => .push .saved (fun _ => .inl ()) (go (.scan false))
  | .scan previous => .pop .input (fun _ b => b) <| .branch Option.isSome
      (.branch (fun s => previous && !isResponse (s.getD (.inl ())))
        (emit one next) next)
      (go .finish)
  | .finish => .pop .saved (fun _ b => b) <| .branch Option.isSome
      (.push .output (fun s => s.getD (.inl ())) (go .finish))
      (.load (fun _ => none) .halt)
def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .start
  σ := State
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Symbol)
  m := program
def contents (bs saved out : List Symbol) : (k : Stack) → List (Alphabet k)
  | .input => bs | .saved => saved | .output => out
def cfg (l : Label) (state : State) (bs saved out : List Symbol) : computer.Cfg :=
  ⟨some l,state,contents bs saved out⟩

theorem step_scan (previous : Bool) (state : State) (b : Symbol)
    (bs saved out : List Symbol) :
    computer.step (cfg (.scan previous) state (b::bs) saved out) =
      some (cfg (.scan (isResponse b)) (some b) bs
        (b :: ((if previous && !isResponse b then one else []).reverse ++ saved)) out) := by
  cases previous <;> cases b
  all_goals try casesm* Unit
  all_goals try casesm* Cell
  all_goals simp [cfg,computer,FinTM2.step,program,emit,next,one_eq,isResponse,contents,Function.update]
  all_goals funext k; cases k <;> rfl

theorem scan_run (previous : Bool) (state : State) (bs saved out : List Symbol) :
    (fun q => q.bind computer.step)^[bs.length+1]
      (some (cfg (.scan previous) state bs saved out)) =
      some (cfg .finish none [] ((scan previous bs).reverse++saved) out) := by
  induction bs generalizing previous state saved with
  | nil => simp [scan,cfg,computer,FinTM2.step,program,go,contents]
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply,Option.bind_some,step_scan,ih]
      simp [scan,List.reverse_append,List.reverse_cons,List.append_assoc]

theorem finish_run (saved out : List Symbol) :
    (fun q => q.bind computer.step)^[saved.length+1] (some (cfg .finish none [] saved out)) =
      some (haltList computer (saved.reverse ++ out)) := by
  induction saved generalizing out with
  | nil =>
      simp [cfg,computer,FinTM2.step,program,go,contents,haltList]
      funext k; cases k <;> rfl
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      have hs : computer.step (cfg .finish none [] (b::bs) out) =
          some (cfg .finish none [] bs (b::out)) := by
        simp [cfg,computer,FinTM2.step,program,go,contents,Function.update]
        funext k; cases k <;> rfl
      rw [Option.bind_some,hs,ih]
      simp [List.reverse_cons,List.append_assoc]

noncomputable def outputsInTime (bs : List Symbol) :
    TM2OutputsInTime computer bs (some (output bs)) (10*bs.length+4) := by
  have hi : initList computer bs = cfg .start none bs [] [] := by
    unfold initList cfg computer; congr; funext k; cases k <;> rfl
  have hs : computer.step (cfg .start none bs [] []) =
      some (cfg (.scan false) none bs [.inl ()] []) := by
    simp [cfg,computer,FinTM2.step,program,go,contents]
    funext k; cases k <;> rfl
  refine {
    steps := ((scan false bs).length+2)+(bs.length+1)+1
    steps_le_m := by have := scan_length_le false bs; omega
    evals_in_steps := ?_ }
  change (fun q => q.bind computer.step)^[_] (some (initList computer bs)) = _
  rw [hi,Function.iterate_succ_apply,Option.bind_some,hs,Function.iterate_add_apply,scan_run]
  have hf := finish_run ((scan false bs).reverse ++ [.inl ()]) []
  simpa [output,List.reverse_append] using hf
end Machine

def wireEncoding : FinEncoding (List Symbol) where
  Γ := Symbol
  encode := id
  decode := some
  decode_encode _ := rfl
  ΓFin := inferInstance

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime RationalRecordData.outputEncoding wireEncoding
      (fun x => output (RationalRecordData.outputEncoding.encode x)) where
  tm := Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 10*Polynomial.X+4
  outputsFun x := by
    simpa [wireEncoding,Equiv.refl] using! Machine.outputsInTime
      (RationalRecordData.outputEncoding.encode x)


def oneCells : List Cell := (Fraction.ofRat 1).encode.map Cell.coefficient ++ [.fieldEnd]
def extend : Bool → List Cell → List Cell
  | _, [] => []
  | previous, c::cs =>
      (if previous && !isResponse (.inr c) then oneCells else []) ++
        c :: extend (isResponse (.inr c)) cs

theorem scan_map (previous : Bool) (cs : List Cell) :
    scan previous (cs.map Sum.inr) = (extend previous cs).map Sum.inr := by
  induction cs generalizing previous with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.map_cons,scan,extend,List.map_append,ih]
      split <;> simp [one,oneCells,List.map_map,Function.comp_def]

theorem scan_marks (n : ℕ) (bs : List Symbol) :
    scan false (List.replicate n (.inl ()) ++ bs) =
      List.replicate n (.inl ()) ++ scan false bs := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ,scan,isResponse,ih]

def augment (x : RationalRecordData.Result) : RationalRecordData.Result :=
  (x.1+1,extend false x.2)

theorem output_encode (x : RationalRecordData.Result) :
    output (RationalRecordData.outputEncoding.encode x) =
      RationalRecordData.outputEncoding.encode (augment x) := by
  simp [output,RationalRecordData.outputEncoding,PairEncoding.finEncoding,
    RationalTailAssembly.unaryEncoding,RationalRectangularFields.outputEncoding,
    List.map_replicate,scan_marks,scan_map,augment,List.replicate_succ]

noncomputable def augmentComputableInPolyTime :
    TM2ComputableInPolyTime RationalRecordData.outputEncoding RationalRecordData.outputEncoding augment :=
  { computableInPolyTime with
    outputsFun := fun x => by simpa only [output_encode,wireEncoding,id_eq]
      using! computableInPolyTime.outputsFun x }

theorem extend_plain (cs : List Cell) (tail : List Cell)
    (h : ∀ c ∈ cs, isResponse (.inr c) = false) :
    extend false (cs++tail) = cs ++ extend false tail := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [extend,h c (by simp),ih (by aesop)]

theorem extend_response (previous : Bool) (bs : List Bool) (tail : List Cell) (h : bs ≠ []) :
    extend previous (bs.map Cell.response ++ tail) =
      bs.map Cell.response ++ extend true tail := by
  cases bs with
  | nil => contradiction
  | cons b bs =>
      simp only [List.map_cons,List.cons_append,extend,isResponse,Bool.not_true,Bool.and_false,
        Bool.false_eq_true,↓reduceIte,List.nil_append]
      congr 1
      induction bs with
      | nil => rfl
      | cons b bs ih => simp [extend,isResponse,ih]

theorem extend_after_response (cs : List Cell) (tail : List Cell)
    (h : ∀ c ∈ cs, isResponse (.inr c) = false) :
    extend true (cs ++ .rowEnd :: tail) =
      oneCells ++ cs ++ .rowEnd :: extend false tail := by
  cases cs with
  | nil => simp [extend,isResponse]
  | cons c cs =>
      simp only [List.cons_append,extend,h c (by simp),Bool.not_false,Bool.true_and,
        ↓reduceIte]
      rw [extend_plain cs (.rowEnd::tail) (by intro c hc; exact h c (by simp [hc]))]
      simp [extend,isResponse,List.append_assoc]

def augmentRow (row : RationalCertificateBroadcast.Row) : RationalCertificateBroadcast.Row :=
  (row.1,Fraction.ofRat 1 :: row.2)

theorem extend_row (row : RationalCertificateBroadcast.Row) (tail : List Cell) :
    extend false (RationalRectangularFields.rowWire (row.1.encode,row.2.map Fraction.encode) ++ tail) =
      RationalRectangularFields.rowWire
        ((augmentRow row).1.encode,(augmentRow row).2.map Fraction.encode) ++ extend false tail := by
  simp only [RationalRectangularFields.rowWire,List.append_assoc]
  rw [extend_response false row.1.encode _ (RationalCertificateTail.fraction_nonempty row.1)]
  simp only [List.singleton_append]
  rw [extend_after_response]
  · simp [augmentRow,oneCells,List.append_assoc]
  · intro c hc
    simp only [List.mem_flatMap,List.mem_append,List.mem_map,List.mem_singleton] at hc
    obtain ⟨f,_,hc⟩ := hc
    rcases hc with ⟨b,_,rfl⟩ | rfl <;> rfl

theorem extend_rows (rs : List RationalCertificateBroadcast.Row) (tail : List Bool) :
    extend false (RationalRectangularFields.rowsWire (RationalRectangularFields.fractionRows rs) ++
      .dataEnd :: tail.map Cell.tail) =
      RationalRectangularFields.rowsWire (RationalRectangularFields.fractionRows (rs.map augmentRow)) ++
        .dataEnd :: tail.map Cell.tail := by
  induction rs with
  | nil =>
      simp only [RationalRectangularFields.fractionRows,List.map_nil,RationalRectangularFields.rowsWire,
        List.flatMap_nil,List.nil_append,extend,isResponse,Bool.false_and]
      simpa [extend] using extend_plain (tail.map Cell.tail) [] (by intro c hc; obtain ⟨b,_,rfl⟩ := List.mem_map.mp hc; rfl)
  | cons row rs ih =>
      simp only [RationalRectangularFields.fractionRows,List.map_cons,RationalRectangularFields.rowsWire,
        List.flatMap_cons,List.append_assoc] at ih ⊢
      rw [extend_row,ih]

theorem observations_affine {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) :
    (RationalCertificateBroadcast.observations A y).map augmentRow =
      RationalCertificateBroadcast.observations (RegularisedCandidates.affineDesign A) y := by
  simp [RationalCertificateBroadcast.observations,augmentRow,List.map_ofFn,
    RegularisedCandidates.affineDesign,ContactTheorem.augment,List.ofFn_succ,Function.comp_def]

noncomputable def parsedComputableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding RationalRecordData.outputEncoding
      (fun bits => augment (RationalRecordData.output bits)) :=
  MachineComposition.compositionComputableInPolyTime _ _ _ _ _
    RationalRecordData.computableInPolyTime augmentComputableInPolyTime

/-- Exact correspondence in original bits, with an entirely arbitrary suffix. -/
theorem original_append {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (w : List Bool) (hr : 0 < r) :
    augment (RationalRecordData.output (RationalWitnessEncoding.encodeInput A y B ++ w)) =
      RationalRecordData.output
        (RationalWitnessEncoding.encodeInput (RegularisedCandidates.affineDesign A) y B ++ w) := by
  rw [RationalRecordData.output_original_append A y B w hr,
    RationalRecordData.output_original_append (RegularisedCandidates.affineDesign A) y B w hr]
  simp only [augment,← RationalRectangularFields.rowsWire_fractionRows,
    extend_rows,observations_affine]

#print axioms Machine.outputsInTime
#print axioms augmentComputableInPolyTime
#print axioms parsedComputableInPolyTime
#print axioms original_append

end PhdThesisLean.RationalAffineData
