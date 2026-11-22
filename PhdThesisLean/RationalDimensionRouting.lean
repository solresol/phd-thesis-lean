import PhdThesisLean.RationalCountedList
import PhdThesisLean.RationalRegressionInternal

/-!
# Routing bounded binary dimensions without losing failure markers

The count delimiter is retained in the first component: a valid zero count
has one delimiter, whereas failure has an empty first component. The finite
machine preserves this distinction while routing the unmodified binary suffix.
-/
namespace PhdThesisLean.RationalDimensionRouting

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness
set_option backward.isDefEq.respectTransparency false

abbrev Bits := List (Option Bool)
abbrev Pair := Bits × List Bool

def parts : Bool → Bits → Pair
  | _, [] => ([],[])
  | a, none :: bs => let p := parts false bs; (if a then none :: p.1 else p.1, p.2)
  | true, some b :: bs => let p := parts true bs; (some b :: p.1,p.2)
  | false, some b :: bs => let p := parts false bs; (p.1,b :: p.2)

def tagged : Bool → Bits → List (Sum (Option Bool) Bool)
  | _, [] => []
  | a, none :: bs => if a then .inl none :: tagged false bs else tagged false bs
  | true, some b :: bs => .inl (some b) :: tagged true bs
  | false, some b :: bs => .inr b :: tagged false bs

def pairEncoding : FinEncoding Pair :=
  PairEncoding.finEncoding RationalFractionPrefix.Machine.outputEncoding
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
          MachinePrimitives.RawBoolList.finEncoding, RationalFractionPrefix.Machine.outputEncoding, parts_false]

theorem parts_append (xs ys : List Bool) :
    parts true (xs.map some ++ none :: ys.map some) = (xs.map some ++ [none],ys) := by
  have h (ys : List Bool) : parts false (ys.map some) = ([],ys) := by
    induction ys with
    | nil => rfl
    | cons b bs ih => simp [parts, ih]
  induction xs with
  | nil => simp [parts, h ys]
  | cons b bs ih => simp [parts, ih]

theorem tagged_length_le (a : Bool) (bs : Bits) : (tagged a bs).length ≤ bs.length := by
  induction bs generalizing a with
  | nil => simp [tagged]
  | cons b bs ih => cases b <;> cases a <;> simp [tagged] <;> have := ih false <;> have := ih true <;> omega

namespace Machine

inductive Label | scan (first : Bool) | reverse deriving DecidableEq, Fintype
inductive Stack | input | saved | output deriving DecidableEq, Fintype
abbrev State := Option (Option Bool) × Option (Sum (Option Bool) Bool)
def initial : State := (none,none)
def Alphabet : Stack → Type
  | .input => Option Bool
  | .saved | .output => Sum (Option Bool) Bool
def go (l : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => initial) (.goto fun _ => l)
def program : Label → TM2.Stmt Alphabet Label State
  | .scan a => .pop .input (fun s b => (b,s.2)) <| .branch (fun s => s.1.isSome)
      (.branch (fun s => (s.1.getD none).isSome)
        (.push .saved (fun s => if a then .inl (some ((s.1.getD none).getD false))
          else .inr ((s.1.getD none).getD false)) (go (.scan a)))
        (if a then .push .saved (fun _ => .inl none) (go (.scan false)) else go (.scan false)))
      (go .reverse)
  | .reverse => .pop .saved (fun s b => (s.1,b)) <| .branch (fun s => s.2.isSome)
      (.push .output (fun s => s.2.getD (.inl none)) (go .reverse))
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
def contents (bs : Bits) (saved out : List (Sum (Option Bool) Bool)) : (k : Stack) → List (Alphabet k)
  | .input => bs | .saved => saved | .output => out
def cfg (l : Label) (bs : Bits) (saved out : List (Sum (Option Bool) Bool)) : computer.Cfg :=
  ⟨some l,initial,contents bs saved out⟩

theorem step_scan (a : Bool) (b : Option Bool) (bs : Bits)
    (saved out : List (Sum (Option Bool) Bool)) :
    computer.step (cfg (.scan a) (b::bs) saved out) =
      some (match b with
        | none => cfg (.scan false) bs (if a then .inl none :: saved else saved) out
        | some v => cfg (.scan a) bs ((if a then .inl (some v) else .inr v)::saved) out) := by
  cases b <;> cases a <;>
    simp [cfg, computer, FinTM2.step, program, go, contents, initial, Function.update]
  all_goals funext k; cases k <;> rfl

theorem scan_run (a : Bool) (bs : Bits) (saved out : List (Sum (Option Bool) Bool)) :
    (fun q => q.bind computer.step)^[bs.length+1] (some (cfg (.scan a) bs saved out)) =
      some (cfg .reverse [] ((tagged a bs).reverse ++ saved) out) := by
  induction bs generalizing a saved with
  | nil =>
      simp [cfg, tagged, computer, FinTM2.step, program, go, contents, initial, Function.update]
  | cons b bs ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, step_scan]
      cases b <;> cases a <;>
        simpa [tagged, List.reverse_cons, List.append_assoc] using ih _ _

theorem reverse_run (saved out : List (Sum (Option Bool) Bool)) :
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

def countWord (n : ℕ) : Bits := List.replicate n (some true) ++ [none]

def splitCount (bits : List Bool) : Pair := parts true (BoundedBinaryCount.output bits)

theorem splitCount_encode_append (n : ℕ) (rest : List Bool) :
    splitCount (BinaryNatLists.encodeNat n ++ rest) =
      if n ≤ rest.length then (countWord n,rest) else ([],[]) := by
  simp only [splitCount, BoundedBinaryCount.output_encode_append]
  split
  · rw [show List.replicate n (some true) = (List.replicate n true).map some by simp,
      parts_append]
    simp [countWord]
  · rfl

theorem splitCount_of_failure (bits : List Bool) (h : BoundedBinaryCount.output bits = []) :
    splitCount bits = ([],[]) := by simp [splitCount, h, parts]

theorem splitCount_eq_iff (bits : List Bool) (n : ℕ) (rest : List Bool) :
    splitCount bits = (countWord n,rest) ↔
      bits = BinaryNatLists.encodeNat n ++ rest ∧ n ≤ rest.length := by
  constructor
  · intro h
    have ha : BoundedBinaryCount.output bits ≠ [] := by
      intro hf
      rw [splitCount_of_failure bits hf] at h
      have := congrArg Prod.fst h
      simp [countWord] at this
    obtain ⟨m,tail,rfl,hm⟩ := (BoundedBinaryCount.output_success_iff bits).1 ha
    rw [splitCount_encode_append, ite_eq_left hm] at h
    have hc := congrArg (fun p : Pair => p.1.length) h
    have ht := congrArg Prod.snd h
    simp [countWord] at hc
    change tail = rest at ht
    subst m; subst tail
    exact ⟨rfl,hm⟩
  · rintro ⟨rfl,h⟩
    exact (splitCount_encode_append n rest).trans (ite_eq_left h)

theorem splitCount_cases (bits : List Bool) :
    splitCount bits = ([],[]) ∨ ∃ n rest,
      splitCount bits = (countWord n,rest) ∧
        bits = BinaryNatLists.encodeNat n ++ rest ∧ n ≤ rest.length := by
  by_cases h : BoundedBinaryCount.output bits = []
  · exact Or.inl (splitCount_of_failure bits h)
  · obtain ⟨n,rest,he,hn⟩ := (BoundedBinaryCount.output_success_iff bits).1 h
    exact Or.inr ⟨n,rest,(splitCount_eq_iff bits n rest).2 ⟨he,hn⟩,he,hn⟩

/-- The original binary count parser, bounded expansion, retained marker routing,
and transfers are all executed by finite machines. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime MachinePrimitives.RawBoolList.finEncoding pairEncoding splitCount :=
  MachineComposition.compositionComputableInPolyTime _ _ _ _ _
    BoundedBinaryCount.computableInPolyTime Machine.computableInPolyTime

#print axioms Machine.outputsInTime
#print axioms splitCount_eq_iff
#print axioms computableInPolyTime

end PhdThesisLean.RationalDimensionRouting
