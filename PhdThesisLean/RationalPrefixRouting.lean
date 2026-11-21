import PhdThesisLean.RationalCountedList
import PhdThesisLean.RationalRegressionInternal

/-!
# Routing a retained fraction prefix into a machine pair

The prefix parser's delimiter is converted to disjoint pair tags by an actual
finite machine. A failed prefix becomes the pair of empty words; its empty
first component remains distinguishable from every valid fraction.
-/
namespace PhdThesisLean.RationalPrefixRouting

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness
set_option backward.isDefEq.respectTransparency false

abbrev Bits := List (Option Bool)
abbrev Pair := List Bool × List Bool

def parts : Bool → Bits → Pair
  | _, [] => ([],[])
  | _, none :: bs => parts false bs
  | true, some b :: bs => let p := parts true bs; (b :: p.1,p.2)
  | false, some b :: bs => let p := parts false bs; (p.1,b :: p.2)

def tagged : Bool → Bits → List (Sum Bool Bool)
  | _, [] => []
  | _, none :: bs => tagged false bs
  | true, some b :: bs => .inl b :: tagged true bs
  | false, some b :: bs => .inr b :: tagged false bs

def pairEncoding : FinEncoding Pair :=
  PairEncoding.finEncoding MachinePrimitives.RawBoolList.finEncoding
    MachinePrimitives.RawBoolList.finEncoding

theorem parts_false (bs : Bits) : (parts false bs).1 = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [parts, ih]

theorem tagged_encode (a : Bool) (bs : Bits) :
    tagged a bs = pairEncoding.encode (parts a bs) := by
  induction bs generalizing a with
  | nil => cases a <;> rfl
  | cons b bs ih =>
      cases b <;> cases a <;>
        simp [tagged, parts, ih, pairEncoding, PairEncoding.finEncoding,
          MachinePrimitives.RawBoolList.finEncoding, parts_false]

theorem parts_append (xs ys : List Bool) :
    parts true (xs.map some ++ none :: ys.map some) = (xs,ys) := by
  have h (ys : List Bool) : parts false (ys.map some) = ([],ys) := by
    induction ys with
    | nil => rfl
    | cons b bs ih => simp [parts, ih]
  induction xs with
  | nil => simpa [parts] using h ys
  | cons b bs ih => simp [parts, ih]

theorem tagged_length_le (a : Bool) (bs : Bits) : (tagged a bs).length ≤ bs.length := by
  induction bs generalizing a with
  | nil => simp [tagged]
  | cons b bs ih => cases b <;> cases a <;> simp [tagged] <;> have := ih false <;> have := ih true <;> omega

namespace Machine

inductive Label | scan (first : Bool) | reverse deriving DecidableEq, Fintype
inductive Stack | input | saved | output deriving DecidableEq, Fintype
abbrev State := Option (Option Bool) × Option (Sum Bool Bool)
def initial : State := (none,none)
def Alphabet : Stack → Type
  | .input => Option Bool
  | .saved | .output => Sum Bool Bool
def go (l : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => initial) (.goto fun _ => l)
def program : Label → TM2.Stmt Alphabet Label State
  | .scan a => .pop .input (fun s b => (b,s.2)) <| .branch (fun s => s.1.isSome)
      (.branch (fun s => (s.1.getD none).isSome)
        (.push .saved (fun s => if a then .inl ((s.1.getD none).getD false)
          else .inr ((s.1.getD none).getD false)) (go (.scan a))) (go (.scan false)))
      (go .reverse)
  | .reverse => .pop .saved (fun s b => (s.1,b)) <| .branch (fun s => s.2.isSome)
      (.push .output (fun s => s.2.getD (.inl false)) (go .reverse))
      (.load (fun _ => initial) .halt)
def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan true
  σ := State
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := program
def contents (bs : Bits) (saved out : List (Sum Bool Bool)) : (k : Stack) → List (Alphabet k)
  | .input => bs | .saved => saved | .output => out
def cfg (l : Label) (bs : Bits) (saved out : List (Sum Bool Bool)) : computer.Cfg :=
  ⟨some l,initial,contents bs saved out⟩

theorem step_scan (a : Bool) (b : Option Bool) (bs : Bits)
    (saved out : List (Sum Bool Bool)) :
    computer.step (cfg (.scan a) (b::bs) saved out) =
      some (match b with
        | none => cfg (.scan false) bs saved out
        | some v => cfg (.scan a) bs ((if a then .inl v else .inr v)::saved) out) := by
  cases b <;> cases a <;>
    simp [cfg, computer, FinTM2.step, program, go, contents, initial, Function.update]
  all_goals funext k; cases k <;> rfl

theorem scan_run (a : Bool) (bs : Bits) (saved out : List (Sum Bool Bool)) :
    (fun q => q.bind computer.step)^[bs.length+1] (some (cfg (.scan a) bs saved out)) =
      some (cfg .reverse [] ((tagged a bs).reverse ++ saved) out) := by
  induction bs generalizing a saved with
  | nil =>
      simp [cfg, tagged, computer, FinTM2.step, program, go, contents, initial, Function.update]
  | cons b bs ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, step_scan]
      cases b <;> cases a <;>
        simpa [tagged, List.reverse_cons, List.append_assoc] using ih _ _

theorem reverse_run (saved out : List (Sum Bool Bool)) :
    (fun q => q.bind computer.step)^[saved.length+1] (some (cfg .reverse [] saved out)) =
      some (haltList computer (saved.reverse ++ out)) := by
  induction saved generalizing out with
  | nil =>
      simp [cfg, computer, FinTM2.step, program, go, contents, initial, Function.update, haltList]
      funext k; cases k <;> rfl
  | cons b bs ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      have hs : computer.step (cfg .reverse [] (b::bs) out) =
          some (cfg .reverse [] bs (b::out)) := by
        simp [cfg, computer, FinTM2.step, program, go, contents, initial, Function.update]
        funext k; cases k <;> rfl
      rw [Option.bind_some, hs, ih]
      simp [List.reverse_cons, List.append_assoc]

noncomputable def outputsInTime (bs : Bits) :
    TM2OutputsInTime computer bs (some (tagged true bs)) (2*bs.length+2) := by
  have hi : initList computer bs = cfg (.scan true) bs [] [] := by
    unfold initList cfg computer; congr; funext k; cases k <;> rfl
  refine { steps := (tagged true bs).length+1+(bs.length+1)
           steps_le_m := ?_
           evals_in_steps := ?_ }
  · change (fun q => q.bind computer.step)^[_] (some (initList computer bs)) = _
    rw [hi, Function.iterate_add_apply, scan_run, List.append_nil]
    simpa using reverse_run (tagged true bs).reverse []
  · have := tagged_length_le true bs; omega

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime RationalFractionPrefix.Machine.outputEncoding pairEncoding (parts true) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2*Polynomial.X+2
  outputsFun bs := by
    simpa [RationalFractionPrefix.Machine.outputEncoding, Equiv.refl, tagged_encode] using outputsInTime bs

end Machine

def splitPrefix (bs : List Bool) : Pair := parts true (RationalFractionPrefix.output bs)

theorem prefix_of_parse (bs xs ys : List Bool)
    (h : RationalFractionPrefix.parse bs = some (xs,ys)) : splitPrefix bs = (xs,ys) := by
  simp [splitPrefix, RationalFractionPrefix.output, RationalFractionPrefix.render, h, parts_append]

theorem prefix_of_none (bs : List Bool) (h : RationalFractionPrefix.parse bs = none) :
    splitPrefix bs = ([],[]) := by
  simp [splitPrefix, RationalFractionPrefix.output, RationalFractionPrefix.render, h, parts]

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding pairEncoding splitPrefix :=
  MachineComposition.compositionComputableInPolyTime _ _ _ _ _
    RationalFractionPrefix.Machine.computableInPolyTime Machine.computableInPolyTime

#print axioms computableInPolyTime
#print axioms Machine.outputsInTime

end PhdThesisLean.RationalPrefixRouting
