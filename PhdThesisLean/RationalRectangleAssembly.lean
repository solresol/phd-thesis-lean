import PhdThesisLean.RationalRecordPrefix
import PhdThesisLean.RationalCertificateTail

/-!
# Assemble the rectangular validator's input and retain the column count

Both unary header delimiters are checked before accepting the tagged prefix.
Column marks are copied onto a separate finite-machine stack. Failure produces
an invalid rectangular payload with zero dimensions, so a missing delimiter
cannot be mistaken for a successful zero dimension.
-/
namespace PhdThesisLean.RationalRectangleAssembly

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness RationalDimensionRouting
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev Cell := Sum (Option Bool) (Sum (Option Bool) (Option Bool))
abbrev Out := Sum Unit (Option Bool)
inductive Phase | rows | columns | data deriving DecidableEq, Fintype

def route : Phase → Cell → Option (Phase × Option Bool × Bool)
  | .rows, .inl (some true) => some (.rows, some true, false)
  | .rows, .inl none => some (.columns, none, false)
  | .columns, .inr (.inl (some true)) => some (.columns, some true, true)
  | .columns, .inr (.inl none) => some (.data, none, false)
  | .data, .inr (.inr b) => some (.data, b, false)
  | _, _ => none

def scan : Phase → List Cell → Option (Bits × ℕ)
  | .data, [] => some ([],0)
  | _, [] => none
  | q, b::bs => do
      let (q',v,copy) ← route q b
      let (rest,n) ← scan q' bs
      pure (v::rest,n + if copy then 1 else 0)

def failure : List Out := [.inr none,.inr none]
def render (n : ℕ) (saved : Bits) : Option (Bits × ℕ) → List Out
  | none => failure
  | some (bs,k) => List.replicate (n+k) (.inl ()) ++ (saved.reverse ++ bs).map .inr

def output (bs : List Cell) : List Out := render 0 [] (scan .rows bs)


theorem render_step (n : ℕ) (s : Bits) (v : Option Bool) (copy : Bool) (r : Option (Bits × ℕ)) :
    render n s (r.bind (fun p => some (v::p.1,p.2 + if copy then 1 else 0))) =
      render (n + if copy then 1 else 0) (v::s) r := by
  cases r with
  | none => rfl
  | some p =>
      rcases p with ⟨bs,k⟩
      cases copy <;> simp [render,List.reverse_cons,List.map_append,List.append_assoc,
        Nat.add_left_comm,Nat.add_comm]

@[simp] theorem render_none (n : ℕ) (s : Bits) : render n s none = failure := rfl
@[simp] theorem render_some (n : ℕ) (s bs : Bits) (k : ℕ) :
    render n s (some (bs,k)) = List.replicate (n+k) (.inl ()) ++ (s.reverse ++ bs).map .inr := rfl

theorem render_cons (n : ℕ) (s : Bits) (v : Option Bool) (r : Option (Bits × ℕ)) :
    render n s (r.bind (fun p => some (v::p.1,p.2))) = render n (v::s) r := by
  simpa using render_step n s v false r

theorem render_copy (n : ℕ) (s : Bits) (v : Option Bool) (r : Option (Bits × ℕ)) :
    render n s (r.bind (fun p => some (v::p.1,p.2+1))) = render (n+1) (v::s) r := by
  simpa using render_step n s v true r

namespace Machine
inductive Label | scan (q : Phase) | reverse | emitCount | rejectInput | rejectSaved | rejectCount
  deriving DecidableEq, Fintype
structure Cursor where
  label : Label
  input : List Cell
  saved : Bits
  count : ℕ
  out : List Out

def advance : Cursor → Sum (List Out) Cursor
  | ⟨.scan q,b::bs,s,n,o⟩ => match route q b with
      | none => .inr ⟨.rejectInput,bs,s,n,o⟩
      | some (q',v,copy) => .inr ⟨.scan q',bs,v::s,n + if copy then 1 else 0,o⟩
  | ⟨.scan .data,[],s,n,o⟩ => .inr ⟨.reverse,[],s,n,o⟩
  | ⟨.scan _,[],s,n,o⟩ => .inr ⟨.rejectInput,[],s,n,o⟩
  | ⟨.reverse,bs,b::s,n,o⟩ => .inr ⟨.reverse,bs,s,n,.inr b::o⟩
  | ⟨.reverse,bs,[],n,o⟩ => .inr ⟨.emitCount,bs,[],n,o⟩
  | ⟨.emitCount,_,_,0,o⟩ => .inl o
  | ⟨.emitCount,bs,s,n+1,o⟩ => .inr ⟨.emitCount,bs,s,n,.inl ()::o⟩
  | ⟨.rejectInput,_::bs,s,n,o⟩ => .inr ⟨.rejectInput,bs,s,n,o⟩
  | ⟨.rejectInput,[],s,n,o⟩ => .inr ⟨.rejectSaved,[],s,n,o⟩
  | ⟨.rejectSaved,bs,_::s,n,o⟩ => .inr ⟨.rejectSaved,bs,s,n,o⟩
  | ⟨.rejectSaved,bs,[],n,o⟩ => .inr ⟨.rejectCount,bs,[],n,o⟩
  | ⟨.rejectCount,_,_,0,_⟩ => .inl failure
  | ⟨.rejectCount,bs,s,n+1,o⟩ => .inr ⟨.rejectCount,bs,s,n,o⟩

def phaseWeight : Label → ℕ
  | .scan _ => 10 | .reverse => 3 | .emitCount => 1
  | .rejectInput => 6 | .rejectSaved => 5 | .rejectCount => 4

def weight (c : Cursor) : ℕ := 4*c.input.length + c.saved.length + c.count + phaseWeight c.label

def Ready (c : Cursor) : Prop :=
  (c.label = .reverse ∨ c.label = .emitCount ∨ c.label = .rejectSaved ∨ c.label = .rejectCount → c.input = []) ∧
  (c.label = .emitCount ∨ c.label = .rejectCount → c.saved = []) ∧
  (c.label ≠ .reverse ∧ c.label ≠ .emitCount → c.out = [])

def meaning (c : Cursor) : List Out := match c.label with
  | .scan q => render c.count c.saved (scan q c.input)
  | .reverse => List.replicate c.count (.inl ()) ++ c.saved.reverse.map .inr ++ c.out
  | .emitCount => List.replicate c.count (.inl ()) ++ c.out
  | _ => failure

theorem advance_decreases (c c' : Cursor) (h : advance c = .inr c') : weight c' < weight c := by
  rcases c with ⟨l,bs,s,n,o⟩
  cases l <;> cases bs <;> cases s <;> cases n
  all_goals try casesm* Phase
  all_goals try casesm* Cell
  all_goals try casesm* Sum (Option Bool) (Option Bool)
  all_goals try casesm* Option Bool
  all_goals try casesm* Bool
  all_goals simp only [advance,route,reduceCtorEq] at h
  all_goals cases h
  all_goals simp [weight,phaseWeight]
  all_goals omega

theorem ready_advance (c c' : Cursor) (hc : Ready c) (h : advance c = .inr c') : Ready c' := by
  rcases c with ⟨l,bs,s,n,o⟩
  cases l <;> cases bs <;> cases s <;> cases n
  all_goals try casesm* Phase
  all_goals try casesm* Cell
  all_goals try casesm* Sum (Option Bool) (Option Bool)
  all_goals try casesm* Option Bool
  all_goals try casesm* Bool
  all_goals simp only [advance,route,reduceCtorEq] at h
  all_goals cases h
  all_goals simp_all [Ready]

theorem meaning_advance (c : Cursor) (hc : Ready c) :
    meaning c = match advance c with | .inl bs => bs | .inr c' => meaning c' := by
  rcases c with ⟨l,bs,s,n,o⟩
  cases l <;> cases bs <;> cases s <;> cases n
  all_goals try casesm* Phase
  all_goals try casesm* Cell
  all_goals try casesm* Sum (Option Bool) (Option Bool)
  all_goals try casesm* Option Bool
  all_goals try casesm* Bool
  all_goals simp_all [Ready,meaning,advance,scan,route,render_cons,render_copy,List.reverse_cons,
    List.map_append,List.append_assoc,List.replicate_succ]
  all_goals rw [← List.cons_append, ← List.replicate_succ, List.replicate_succ', List.append_assoc]
  all_goals rfl

inductive Stack | input | saved | count | output deriving DecidableEq, Fintype
abbrev State := Option Cell × Option (Option Bool)
def initial : State := (none,none)
def Alphabet : Stack → Type
  | .input => Cell | .saved => Option Bool | .count => Unit | .output => Out

def go (l : Label) : TM2.Stmt Alphabet Label State := .load (fun _ => initial) (.goto fun _ => l)
def held (q : Phase) (s : State) : Option (Phase × Option Bool × Bool) :=
  s.1.bind (route q)
def program : Label → TM2.Stmt Alphabet Label State
  | .scan q => .pop .input (fun s b => (b,s.2)) <| .branch (fun s => s.1.isSome)
      (.branch (fun s => (held q s).isSome)
        (.push .saved (fun s => ((held q s).getD (.data,none,false)).2.1) <|
          .branch (fun s => ((held q s).getD (.data,none,false)).2.2)
            (.push .count (fun _ => ()) <| .load (fun _ => initial) (.goto fun _ => .scan .columns))
            (.branch (fun s => decide (((held q s).getD (.data,none,false)).1 = .rows))
              (go (.scan .rows)) (.branch (fun s => decide (((held q s).getD (.data,none,false)).1 = .columns))
                (go (.scan .columns)) (go (.scan .data)))))
        (go .rejectInput))
      (go (if q = .data then .reverse else .rejectInput))
  | .reverse => .pop .saved (fun s b => (s.1,b)) <| .branch (fun s => s.2.isSome)
      (.push .output (fun s => .inr (s.2.getD none)) (go .reverse)) (go .emitCount)
  | .emitCount => .pop .count (fun s b => (b.map (fun _ => .inl none),s.2)) <|
      .branch (fun s => s.1.isSome) (.push .output (fun _ => .inl ()) (go .emitCount))
        (.load (fun _ => initial) .halt)
  | .rejectInput => .pop .input (fun s b => (b,s.2)) <| .branch (fun s => s.1.isSome)
      (go .rejectInput) (go .rejectSaved)
  | .rejectSaved => .pop .saved (fun s b => (s.1,b)) <| .branch (fun s => s.2.isSome)
      (go .rejectSaved) (go .rejectCount)
  | .rejectCount => .pop .count (fun s b => (b.map (fun _ => .inl none),s.2)) <|
      .branch (fun s => s.1.isSome) (go .rejectCount)
        (.push .output (fun _ => .inr none) <| .push .output (fun _ => .inr none) <|
          .load (fun _ => initial) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan .rows
  σ := State
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype Cell)
  m := program

def contents (bs : List Cell) (s : Bits) (n : ℕ) (o : List Out) : (k : Stack) → List (Alphabet k)
  | .input => bs | .saved => s | .count => List.replicate n () | .output => o

def cfg (c : Cursor) : computer.Cfg := ⟨some c.label,initial,contents c.input c.saved c.count c.out⟩

theorem step_cfg (c : Cursor) (hc : Ready c) :
    computer.step (cfg c) = some (match advance c with
      | .inl bs => haltList computer bs | .inr c' => cfg c') := by
  rcases c with ⟨l,bs,s,n,o⟩
  cases l <;> cases bs <;> cases s <;> cases n
  all_goals try casesm* Phase
  all_goals try casesm* Cell
  all_goals try casesm* Sum (Option Bool) (Option Bool)
  all_goals try casesm* Option Bool
  all_goals try casesm* Bool
  all_goals simp_all [Ready,advance,route,computer,FinTM2.step,cfg,program,held,go,contents,
    initial,Function.update,haltList,List.replicate_succ]
  all_goals funext k; cases k <;> rfl

theorem run (c : Cursor) (hc : Ready c) :
    ∃ t, t ≤ weight c ∧ (fun q => q.bind computer.step)^[t] (some (cfg c)) =
      some (haltList computer (meaning c)) := by
  generalize hw : weight c = w
  induction w using Nat.strong_induction_on generalizing c with
  | h w ih =>
      have hs := step_cfg c hc
      have hm := meaning_advance c hc
      cases he : advance c with
      | inl bs =>
          refine ⟨1, ?_, ?_⟩
          · rw [← hw]; rcases c with ⟨l,bs,s,n,o⟩; cases l <;> simp [weight,phaseWeight]
          · simpa [he,Function.iterate_one,hm] using hs
      | inr c' =>
          have hlt := advance_decreases c c' he
          obtain ⟨t,ht,hr⟩ := ih (weight c') (by omega) c' (ready_advance c c' hc he) rfl
          refine ⟨t+1,by omega,?_⟩
          rw [Function.iterate_succ_apply,Option.bind_some,hs]
          simpa [he,hm] using hr

noncomputable def outputsInTime (bs : List Cell) :
    TM2OutputsInTime computer bs (some (output bs)) (4*bs.length+10) := by
  let c : Cursor := ⟨.scan .rows,bs,[],0,[]⟩
  let h := run c (by simp [c,Ready])
  let t := Classical.choose h
  have ht := (Classical.choose_spec h).1
  have hr := (Classical.choose_spec h).2
  have hi : initList computer bs = cfg c := by
    unfold initList cfg computer; congr; funext k; cases k <;> rfl
  exact { steps := t, steps_le_m := ht, evals_in_steps := by simpa [hi,c,meaning,output,t] using! hr }
end Machine


def outputEncoding : FinEncoding (List Out) where
  Γ := Out
  encode := id
  decode := some
  decode_encode _ := rfl
  ΓFin := inferInstance

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime RationalRecordPrefix.outputEncoding outputEncoding
      (fun x => output (RationalRecordPrefix.outputEncoding.encode x)) where
  tm := Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4*Polynomial.X+10
  outputsFun x := by
    simpa [outputEncoding,Equiv.refl] using! Machine.outputsInTime
      (RationalRecordPrefix.outputEncoding.encode x)

def preparedEncoding : FinEncoding (ℕ × RationalRectangularFields.Source) :=
  PairEncoding.finEncoding RationalTailAssembly.unaryEncoding RationalRectangularFields.inputEncoding

def prepare (x : RationalRecordPrefix.Result) : ℕ × RationalRectangularFields.Source :=
  if x.1 = [] ∨ x.2.1 = [] then (0,0,0,[]) else
    (x.2.1.length-1,x.1.length-1,x.2.1.length-1,x.2.2)

theorem scan_data (bs : Bits) : scan .data (bs.map (fun b => .inr (.inr b))) = some (bs,0) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [scan,route,ih]

theorem scan_columns (d : ℕ) (bs : Bits) :
    scan .columns ((countWord d).map (fun b => .inr (.inl b)) ++
      bs.map (fun b => .inr (.inr b))) = some (countWord d ++ bs,d) := by
  induction d with
  | zero => simp [countWord,scan,route,scan_data]
  | succ d ih =>
      change (scan .columns ((countWord d).map (fun b => .inr (.inl b)) ++
        bs.map (fun b => .inr (.inr b)))).bind
          (fun p => some (some true::p.1,p.2+1)) = _
      rw [ih]
      simp [countWord,List.replicate_succ]

theorem scan_rows (r d : ℕ) (bs : Bits) :
    scan .rows (RationalRecordPrefix.outputEncoding.encode (countWord r,countWord d,bs)) =
      some (countWord r ++ countWord d ++ bs,d) := by
  induction r with
  | zero =>
      convert congrArg (fun v : Option (Bits × ℕ) =>
        v.bind (fun p => some (none::p.1,p.2))) (scan_columns d bs) using 1 <;>
          simp [RationalRecordPrefix.outputEncoding,PairEncoding.finEncoding,
            RationalFractionPrefix.Machine.outputEncoding,countWord,scan,route,
            List.map_map,Function.comp_def]
  | succ r ih =>
      change (scan .rows (RationalRecordPrefix.outputEncoding.encode (countWord r,countWord d,bs))).bind
        (fun p => some (some true::p.1,p.2+0)) = _
      rw [ih]
      simp [countWord,List.replicate_succ]

theorem output_headers (r d : ℕ) (bs : Bits) :
    output (RationalRecordPrefix.outputEncoding.encode (countWord r,countWord d,bs)) =
      preparedEncoding.encode (d,r,d,bs) := by
  rw [output,scan_rows]
  simp [render,preparedEncoding,PairEncoding.finEncoding,RationalTailAssembly.unaryEncoding,
    RationalRectangularFields.inputEncoding,RationalRectangularFields.Machine.input,
    countWord,List.append_assoc]

theorem scan_missing_columns (r : ℕ) :
    scan .rows (RationalRecordPrefix.outputEncoding.encode (countWord r,[],[])) = none := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change (scan .rows (RationalRecordPrefix.outputEncoding.encode (countWord r,[],[]))).bind
        (fun p => some (some true::p.1,p.2+0)) = _
      rw [ih]
      rfl

/-- On every original raw word, physical assembly yields a well-encoded stage
input. Failed headers yield the deliberately invalid empty rectangle payload. -/
theorem output_prefix (bits : List Bool) :
    output (RationalRecordPrefix.outputEncoding.encode (RationalRecordPrefix.output bits)) =
      preparedEncoding.encode (prepare (RationalRecordPrefix.output bits)) := by
  rcases splitCount_cases bits with hf | ⟨r,rest,hr,he,hb⟩
  · have hx : RationalRecordPrefix.output bits = ([],[],[]) := by
      simp only [RationalRecordPrefix.output,hf,RationalRecordPrefix.columns]
      rfl
    rw [hx]
    rfl
  · rcases splitCount_cases rest with hf | ⟨d,data,hd,he',hb'⟩
    · simp only [RationalRecordPrefix.output,hr,RationalRecordPrefix.columns,hf]
      have hc : RationalCountedList.output [] = [] := by rfl
      rw [hc]
      rw [output,scan_missing_columns]
      simp [prepare,render,failure,preparedEncoding,PairEncoding.finEncoding,
        RationalTailAssembly.unaryEncoding,RationalRectangularFields.inputEncoding,
        RationalRectangularFields.Machine.input]
    · simp only [RationalRecordPrefix.output,hr,RationalRecordPrefix.columns,hd]
      rw [output_headers]
      simp [prepare,countWord]

#print axioms Machine.outputsInTime
#print axioms output_prefix
#print axioms computableInPolyTime

end PhdThesisLean.RationalRectangleAssembly
