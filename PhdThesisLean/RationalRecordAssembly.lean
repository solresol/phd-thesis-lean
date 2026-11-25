import PhdThesisLean.RationalRecordSource

/-!
# Reorder parsed records into the arithmetic checker's physical input

A finite five-stack machine stably collects certificate, rows and threshold.
The data-end marker is discarded. Empty parser output becomes an empty source
with threshold -1, which the arithmetic checker rejects. No unbounded decoder
or arithmetic operation occurs in this transducer.
-/
namespace PhdThesisLean.RationalRecordAssembly

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness RationalVerifierBounds
set_option backward.isDefEq.respectTransparency false

abbrev Cell := RationalRecordParser.Cell
abbrev Out := Sum (Sum (Option Bool) (Option (Sum Bool (Option Bool)))) Bool
inductive Part | cert | rows | bound deriving DecidableEq, Fintype

def route : Cell → Option (Part × Out)
  | .inl (.response b) => some (.rows,.inl (.inr (some (.inl b))))
  | .inl (.coefficient b) => some (.rows,.inl (.inr (some (.inr (some b)))))
  | .inl .fieldEnd => some (.rows,.inl (.inr (some (.inr none))))
  | .inl .rowEnd => some (.rows,.inl (.inr none))
  | .inl _ => none
  | .inr (.inl b) => some (.cert,.inl (.inl b))
  | .inr (.inr b) => some (.bound,.inr b)
def part (p : Part) : List Cell → List Out
  | [] => []
  | b::bs => match route b with
    | none => part p bs
    | some (q,c) => if p=q then c::part p bs else part p bs

def rejectWord : List Out := [true,true,false,true,true,false,true].map Sum.inr
def assemble (bs : List Cell) : List Out :=
  if bs = [] then rejectWord else part .cert bs ++ part .rows bs ++ part .bound bs

theorem part_append (p : Part) (xs ys : List Cell) :
    part p (xs++ys) = part p xs ++ part p ys := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      cases h : route b with
      | none => simp [part,h,ih]
      | some x =>
          rcases x with ⟨q,c⟩
          by_cases hp : p=q
          · subst q; simp [part,h,ih]
          · simp [part,h,hp,ih]

theorem parts_length_le (bs : List Cell) :
    (part .cert bs).length + (part .rows bs).length + (part .bound bs).length ≤ bs.length := by
  induction bs with
  | nil => simp [part]
  | cons b bs ih =>
      cases h : route b with
      | none => simp [part,h]; omega
      | some x => rcases x with ⟨p,c⟩; cases p <;> simp [part,h] <;> omega

theorem assemble_length_le (bs : List Cell) : (assemble bs).length ≤ bs.length+7 := by
  by_cases h : bs=[]
  · simp [assemble,h,rejectWord]
  · have hl := parts_length_le bs
    simp only [assemble,h,ite_false,List.length_append]
    omega

namespace Machine
inductive Label | start | scan | reverseBound | reverseRows | reverseCert deriving DecidableEq, Fintype
inductive Stack | input | cert | rows | bound | output deriving DecidableEq, Fintype
abbrev State := Option Cell × Option Out
def initial : State := (none,none)
def Alphabet : Stack → Type
  | .input => Cell | _ => Out
def go (l : Label) : TM2.Stmt Alphabet Label State := .load (fun _ => initial) (.goto fun _ => l)
def emit (bs : List Out) : TM2.Stmt Alphabet Label State :=
  bs.foldl (fun next b => .push .output (fun _ => b) next) (.load (fun _ => initial) .halt)
def pushRouted (s : Stack) : TM2.Stmt Alphabet Label State :=
  match s with
  | .input => go .scan
  | .cert => .push .cert (fun st => ((route (st.1.getD (.inl .dataEnd))).getD (.cert,.inr false)).2) (go .scan)
  | .rows => .push .rows (fun st => ((route (st.1.getD (.inl .dataEnd))).getD (.rows,.inr false)).2) (go .scan)
  | .bound => .push .bound (fun st => ((route (st.1.getD (.inl .dataEnd))).getD (.bound,.inr false)).2) (go .scan)
  | .output => go .scan

def program : Label → TM2.Stmt Alphabet Label State
  | .start => .pop .input (fun s b => (b,s.2)) <| .branch (fun s => s.1.isSome)
      (.push .input (fun s => s.1.getD (.inl .dataEnd)) (go .scan)) (emit rejectWord)
  | .scan => .pop .input (fun s b => (b,s.2)) <| .branch (fun s => s.1.isSome)
      (.branch (fun s => (route (s.1.getD (.inl .dataEnd))).isSome)
        (.branch (fun s => ((route (s.1.getD (.inl .dataEnd))).getD (.cert,.inr false)).1 == .cert)
          (pushRouted .cert)
          (.branch (fun s => ((route (s.1.getD (.inl .dataEnd))).getD (.cert,.inr false)).1 == .rows)
            (pushRouted .rows) (pushRouted .bound)))
        (go .scan))
      (go .reverseBound)
  | .reverseBound => .pop .bound (fun s b => (s.1,b)) <| .branch (fun s => s.2.isSome)
      (.push .output (fun s => s.2.getD (.inr false)) (go .reverseBound)) (go .reverseRows)
  | .reverseRows => .pop .rows (fun s b => (s.1,b)) <| .branch (fun s => s.2.isSome)
      (.push .output (fun s => s.2.getD (.inr false)) (go .reverseRows)) (go .reverseCert)
  | .reverseCert => .pop .cert (fun s b => (s.1,b)) <| .branch (fun s => s.2.isSome)
      (.push .output (fun s => s.2.getD (.inr false)) (go .reverseCert)) (.load (fun _ => initial) .halt)
def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .start
  σ := State
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype Cell)
  m := program
def contents (bs : List Cell) (cs rs ts out : List Out) : (k : Stack) → List (Alphabet k)
  | .input => bs | .cert => cs | .rows => rs | .bound => ts | .output => out
def cfg (l : Label) (bs : List Cell) (cs rs ts out : List Out) : computer.Cfg :=
  ⟨some l,initial,contents bs cs rs ts out⟩

theorem step_scan (b : Cell) (bs : List Cell) (cs rs ts out : List Out) :
    computer.step (cfg .scan (b::bs) cs rs ts out) = some (match route b with
      | none => cfg .scan bs cs rs ts out
      | some (.cert,c) => cfg .scan bs (c::cs) rs ts out
      | some (.rows,c) => cfg .scan bs cs (c::rs) ts out
      | some (.bound,c) => cfg .scan bs cs rs (c::ts) out) := by
  cases b
  all_goals try casesm* RationalRectangularFields.Cell
  all_goals try casesm* RationalTailAssembly.Out
  all_goals simp [route,cfg,computer,FinTM2.step,program,pushRouted,go,contents,initial,Function.update]
  all_goals funext k; cases k <;> rfl

theorem scan_run (bs : List Cell) (cs rs ts out : List Out) :
    (fun q => q.bind computer.step)^[bs.length+1] (some (cfg .scan bs cs rs ts out)) =
      some (cfg .reverseBound [] ((part .cert bs).reverse++cs)
        ((part .rows bs).reverse++rs) ((part .bound bs).reverse++ts) out) := by
  induction bs generalizing cs rs ts with
  | nil => simp [part,cfg,computer,FinTM2.step,program,go,contents,initial]
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply,Option.bind_some,step_scan]
      cases h : route b with
      | none => rw [ih]; simp [part,h]
      | some x =>
          rcases x with ⟨p,c⟩
          cases p <;> dsimp only <;> rw [ih] <;>
            simp [part,h,List.reverse_cons,List.append_assoc]

theorem bound_run (ts cs rs out : List Out) :
    (fun q => q.bind computer.step)^[ts.length+1] (some (cfg .reverseBound [] cs rs ts out)) =
      some (cfg .reverseRows [] cs rs [] (ts.reverse++out)) := by
  induction ts generalizing out with
  | nil => simp [cfg,computer,FinTM2.step,program,go,contents,initial,Function.update]
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      have hs : computer.step (cfg .reverseBound [] cs rs (b::bs) out) =
          some (cfg .reverseBound [] cs rs bs (b::out)) := by
        simp [cfg,computer,FinTM2.step,program,go,contents,initial,Function.update]
        funext k; cases k <;> rfl
      rw [Option.bind_some,hs,ih]
      simp [List.reverse_cons,List.append_assoc]

theorem rows_run (rs cs out : List Out) :
    (fun q => q.bind computer.step)^[rs.length+1] (some (cfg .reverseRows [] cs rs [] out)) =
      some (cfg .reverseCert [] cs [] [] (rs.reverse++out)) := by
  induction rs generalizing out with
  | nil => simp [cfg,computer,FinTM2.step,program,go,contents,initial,Function.update]
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      have hs : computer.step (cfg .reverseRows [] cs (b::bs) [] out) =
          some (cfg .reverseRows [] cs bs [] (b::out)) := by
        simp [cfg,computer,FinTM2.step,program,go,contents,initial,Function.update]
        funext k; cases k <;> rfl
      rw [Option.bind_some,hs,ih]
      simp [List.reverse_cons,List.append_assoc]

theorem cert_run (cs out : List Out) :
    (fun q => q.bind computer.step)^[cs.length+1] (some (cfg .reverseCert [] cs [] [] out)) =
      some (haltList computer (cs.reverse++out)) := by
  induction cs generalizing out with
  | nil =>
      simp [cfg,computer,FinTM2.step,program,contents,initial,haltList]
      funext k; cases k <;> rfl
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      have hs : computer.step (cfg .reverseCert [] (b::bs) [] [] out) =
          some (cfg .reverseCert [] bs [] [] (b::out)) := by
        simp [cfg,computer,FinTM2.step,program,go,contents,initial,Function.update]
        funext k; cases k <;> rfl
      rw [Option.bind_some,hs,ih]
      simp [List.reverse_cons,List.append_assoc]

noncomputable def outputsInTime (bs : List Cell) :
    TM2OutputsInTime computer bs (some (assemble bs)) (2*bs.length+5) := by
  have hi : initList computer bs = cfg .start bs [] [] [] [] := by
    unfold initList cfg computer; congr; funext k; cases k <;> rfl
  cases bs with
  | nil =>
      refine { steps := 1, steps_le_m := by simp, evals_in_steps := ?_ }
      change computer.step (initList computer []) = _
      rw [hi]
      simp [assemble,cfg,computer,FinTM2.step,program,emit,rejectWord,initial,contents,haltList]
      funext k; cases k <;> rfl
  | cons b bs =>
      have hl := parts_length_le (b::bs)
      simp only [List.length_cons] at hl
      let n := (part .cert (b::bs)).length + 1 +
        ((part .rows (b::bs)).length + 1 + ((part .bound (b::bs)).length + 1 + ((b::bs).length + 1))) + 1
      refine { steps := n
               steps_le_m := by dsimp [n]; omega
               evals_in_steps := ?_ }
      dsimp only [n]
      change (fun q => q.bind computer.step)^[_] (some (initList computer (b::bs))) = _
      rw [hi,Function.iterate_succ_apply]
      have hs : computer.step (cfg .start (b::bs) [] [] [] []) = some (cfg .scan (b::bs) [] [] [] []) := by
        simp [cfg,computer,FinTM2.step,program,go,contents,initial,Function.update]
      rw [Option.bind_some,hs,
        Function.iterate_add_apply (m := (part .cert (b::bs)).length+1),
        Function.iterate_add_apply (m := (part .rows (b::bs)).length+1),
        Function.iterate_add_apply (m := (part .bound (b::bs)).length+1),scan_run]
      simp only [List.append_nil]
      rw [show (part .bound (b::bs)).length+1 = (part .bound (b::bs)).reverse.length+1 by simp,bound_run]
      rw [show (part .rows (b::bs)).length+1 = (part .rows (b::bs)).reverse.length+1 by simp,rows_run]
      rw [show (part .cert (b::bs)).length+1 = (part .cert (b::bs)).reverse.length+1 by simp,cert_run]
      simp [assemble,List.append_assoc]
end Machine

def outputEncoding : FinEncoding (List Out) where
  Γ := Out
  encode := id
  decode := some
  decode_encode _ := rfl
  ΓFin := inferInstance

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime RationalRecordParser.outputEncoding outputEncoding assemble where
  tm := Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2*Polynomial.X+5
  outputsFun bs := by
    simpa [RationalRecordParser.outputEncoding,outputEncoding,Equiv.refl] using! Machine.outputsInTime bs

#print axioms Machine.outputsInTime
#print axioms computableInPolyTime

end PhdThesisLean.RationalRecordAssembly
