import PhdThesisLean.RationalRecordData

/-!
# Preserve validated rows while routing the original certificate suffix

The four-stack machine stably partitions the rectangular stage's output.
It retains the data-end marker with the rows, so an empty row list is not
confused with failed data validation. Dimension marks accompany the raw suffix.
Every scan, reversal, transfer and final state reset is counted.
-/
namespace PhdThesisLean.RationalRecordRouting

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness
open RationalRectangularFields (Cell)
set_option backward.isDefEq.respectTransparency false

abbrev Input := Sum Unit Cell
abbrev Right := Sum Unit Bool
abbrev Out := Sum Cell Right

def route : Input → Out
  | .inl u => .inr (.inl u)
  | .inr (.tail b) => .inr (.inr b)
  | .inr c => .inl c

def left : List Input → List Cell
  | [] => []
  | b::bs => match route b with | .inl c => c::left bs | .inr _ => left bs
def right : List Input → List Right
  | [] => []
  | b::bs => match route b with | .inl _ => right bs | .inr c => c::right bs
def output (bs : List Input) : List Out := (left bs).map .inl ++ (right bs).map .inr

theorem length_parts (bs : List Input) : (left bs).length + (right bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases h : route b <;> simp [left,right,h] <;> omega

theorem parts_append (xs ys : List Input) :
    left (xs++ys) = left xs ++ left ys ∧ right (xs++ys) = right xs ++ right ys := by
  induction xs with
  | nil => simp [left,right]
  | cons b bs ih => cases h : route b <;> simp [left,right,h,ih]

namespace Machine

inductive Label | scan | reverseRight | reverseLeft deriving DecidableEq, Fintype
inductive Stack | input | savedLeft | savedRight | output deriving DecidableEq, Fintype
abbrev State := Option Input × Option Cell × Option Right
def initial : State := (none,none,none)
def Alphabet : Stack → Type
  | .input => Input | .savedLeft => Cell | .savedRight => Right | .output => Out
def go (l : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => initial) (.goto fun _ => l)
def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input (fun s b => (b,s.2)) <| .branch (fun s => s.1.isSome)
      (.branch (fun s => (route (s.1.getD (.inl ()))).isLeft)
        (.push .savedLeft (fun s => match route (s.1.getD (.inl ())) with | .inl c => c | .inr _ => .dataEnd) (go .scan))
        (.push .savedRight (fun s => match route (s.1.getD (.inl ())) with | .inr c => c | .inl _ => .inl ()) (go .scan)))
      (go .reverseRight)
  | .reverseRight => .pop .savedRight (fun s b => (s.1,s.2.1,b)) <|
      .branch (fun s => s.2.2.isSome)
        (.push .output (fun s => .inr (s.2.2.getD (.inl ()))) (go .reverseRight))
        (go .reverseLeft)
  | .reverseLeft => .pop .savedLeft (fun s b => (s.1,b,s.2.2)) <|
      .branch (fun s => s.2.1.isSome)
        (.push .output (fun s => .inl (s.2.1.getD .dataEnd)) (go .reverseLeft))
        (.load (fun _ => initial) .halt)
def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype Input)
  m := program
def contents (bs : List Input) (ls : List Cell) (rs : List Right) (out : List Out) :
    (k : Stack) → List (Alphabet k)
  | .input => bs | .savedLeft => ls | .savedRight => rs | .output => out
def cfg (l : Label) (bs : List Input) (ls : List Cell) (rs : List Right) (out : List Out) :
    computer.Cfg := ⟨some l,initial,contents bs ls rs out⟩

theorem step_scan (b : Input) (bs : List Input) (ls : List Cell) (rs : List Right) (out : List Out) :
    computer.step (cfg .scan (b::bs) ls rs out) = some (match route b with
      | .inl c => cfg .scan bs (c::ls) rs out
      | .inr c => cfg .scan bs ls (c::rs) out) := by
  cases b
  all_goals try casesm* Unit
  all_goals try casesm* Cell
  all_goals simp [route,cfg,computer,FinTM2.step,program,go,contents,initial,Function.update]
  all_goals funext k; cases k <;> rfl

theorem scan_run (bs : List Input) (ls : List Cell) (rs : List Right) (out : List Out) :
    (fun q => q.bind computer.step)^[bs.length+1] (some (cfg .scan bs ls rs out)) =
      some (cfg .reverseRight [] ((left bs).reverse++ls) ((right bs).reverse++rs) out) := by
  induction bs generalizing ls rs with
  | nil => simp [left,right,cfg,computer,FinTM2.step,program,go,contents,initial,Function.update]
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply,Option.bind_some,step_scan]
      cases h : route b <;> simpa [left,right,h,List.reverse_cons,List.append_assoc] using ih _ _

theorem reverseRight_run (ls : List Cell) (rs : List Right) (out : List Out) :
    (fun q => q.bind computer.step)^[rs.length+1] (some (cfg .reverseRight [] ls rs out)) =
      some (cfg .reverseLeft [] ls [] (rs.reverse.map .inr ++ out)) := by
  induction rs generalizing out with
  | nil => simp [cfg,computer,FinTM2.step,program,go,contents,initial,Function.update]
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      have hs : computer.step (cfg .reverseRight [] ls (b::bs) out) =
          some (cfg .reverseRight [] ls bs (.inr b::out)) := by
        simp [cfg,computer,FinTM2.step,program,go,contents,initial,Function.update]
        funext k; cases k <;> rfl
      rw [Option.bind_some,hs,ih]
      simp [List.reverse_cons,List.map_append,List.append_assoc]

theorem reverseLeft_run (ls : List Cell) (out : List Out) :
    (fun q => q.bind computer.step)^[ls.length+1] (some (cfg .reverseLeft [] ls [] out)) =
      some (haltList computer (ls.reverse.map .inl ++ out)) := by
  induction ls generalizing out with
  | nil =>
      simp [cfg,computer,FinTM2.step,program,go,contents,initial,Function.update,haltList]
      funext k; cases k <;> rfl
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      have hs : computer.step (cfg .reverseLeft [] (b::bs) [] out) =
          some (cfg .reverseLeft [] bs [] (.inl b::out)) := by
        simp [cfg,computer,FinTM2.step,program,go,contents,initial,Function.update]
        funext k; cases k <;> rfl
      rw [Option.bind_some,hs,ih]
      simp [List.reverse_cons,List.map_append,List.append_assoc]

noncomputable def outputsInTime (bs : List Input) :
    TM2OutputsInTime computer bs (some (output bs)) (2*bs.length+3) := by
  have hi : initList computer bs = cfg .scan bs [] [] [] := by
    unfold initList cfg computer; congr; funext k; cases k <;> rfl
  refine { steps := (left bs).length+1+((right bs).length+1)+(bs.length+1)
           steps_le_m := ?_
           evals_in_steps := ?_ }
  · change (fun q => q.bind computer.step)^[_] (some (initList computer bs)) = _
    rw [hi,Function.iterate_add_apply,scan_run,List.append_nil,List.append_nil]
    rw [Function.iterate_add_apply]
    have hr := reverseRight_run (left bs).reverse (right bs).reverse []
    simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hr
    rw [hr]
    simpa [output] using reverseLeft_run (left bs).reverse ((right bs).map .inr)
  · have := length_parts bs; omega
end Machine

def split : List Cell → List Cell × List Bool
  | [] => ([],[])
  | .tail b::bs => let p := split bs; (p.1,b::p.2)
  | c::bs => let p := split bs; (c::p.1,p.2)
def prepare (x : RationalRecordData.Result) : List Cell × (ℕ × List Bool) :=
  ((split x.2).1,x.1,(split x.2).2)
def preparedEncoding := PairEncoding.finEncoding RationalRectangularFields.outputEncoding
  RationalCertificateTail.inputEncoding

theorem split_length (cs : List Cell) : (split cs).1.length+(split cs).2.length = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [split] <;> omega

theorem split_append (xs ys : List Cell) :
    split (xs++ys) = ((split xs).1++(split ys).1,(split xs).2++(split ys).2) := by
  induction xs with
  | nil => simp [split]
  | cons c cs ih => cases c <;> simp [split,ih]

theorem split_retained (xs : List Cell) (h : ∀ b, Cell.tail b ∉ xs) : split xs = (xs,[]) := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
      have ht : ∀ b, Cell.tail b ∉ cs := by intro b hb; exact h b (by simp [hb])
      cases c <;> simp_all [split]

theorem split_tail (bits : List Bool) : split (bits.map Cell.tail) = ([],bits) := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [split,ih]

theorem split_rowsWire (rs : List RationalRectangularFields.Row) (bits : List Bool) :
    split (RationalRectangularFields.rowsWire rs ++ .dataEnd :: bits.map Cell.tail) =
      (RationalRectangularFields.rowsWire rs ++ [.dataEnd],bits) := by
  have h : ∀ b, Cell.tail b ∉ RationalRectangularFields.rowsWire rs := by
    intro b
    simp [RationalRectangularFields.rowsWire,RationalRectangularFields.rowWire]
  simp [split_append,split_retained _ h,split,split_tail]

theorem split_internalRows (cs : List (Option RationalCertificateBroadcast.Machine.RowCell))
    (bits : List Bool) :
    split (cs.map RationalRectangularFields.rowCell ++ .dataEnd :: bits.map Cell.tail) =
      (cs.map RationalRectangularFields.rowCell ++ [.dataEnd],bits) := by
  have h : ∀ b, Cell.tail b ∉ cs.map RationalRectangularFields.rowCell := by
    intro b hb
    obtain ⟨c,_,hc⟩ := List.mem_map.mp hb
    cases c
    all_goals try casesm* RationalCertificateBroadcast.Machine.RowCell
    all_goals try casesm* RationalCertificateBroadcast.Machine.Wire
    all_goals simp [RationalRectangularFields.rowCell] at hc
  simp [split_append,split_retained _ h,split,split_tail]

theorem parts_cells (cs : List Cell) :
    left (cs.map .inr) = (split cs).1 ∧
    right (cs.map .inr) = (split cs).2.map Sum.inr := by
  induction cs with
  | nil => simp [left,right,split]
  | cons c cs ih => cases c <;> simp [left,right,route,split,ih]

theorem output_encode (x : RationalRecordData.Result) :
    output (RationalRecordData.outputEncoding.encode x) = preparedEncoding.encode (prepare x) := by
  rcases x with ⟨d,cs⟩
  have hc : left (List.replicate d (.inl ())) = [] ∧
      right (List.replicate d (.inl ())) = List.replicate d (.inl ()) := by
    induction d with
    | zero => simp [left,right]
    | succ d ih => simp [List.replicate_succ,left,right,route,ih]
  simp [output,RationalRecordData.outputEncoding,PairEncoding.finEncoding,
    RationalTailAssembly.unaryEncoding,RationalRectangularFields.outputEncoding,
    parts_append,hc,parts_cells,preparedEncoding,prepare,RationalCertificateTail.inputEncoding,
    MachinePrimitives.RawBoolList.finEncoding,List.map_map,Function.comp_def]

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime RationalRecordData.outputEncoding preparedEncoding prepare where
  tm := Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2*Polynomial.X+3
  outputsFun x := by
    simpa [Equiv.refl,output_encode] using! Machine.outputsInTime
      (RationalRecordData.outputEncoding.encode x)

#print axioms Machine.outputsInTime
#print axioms output_encode
#print axioms computableInPolyTime

end PhdThesisLean.RationalRecordRouting
