import PhdThesisLean.RationalPrefixRouting

/-!
# Certificate count, exhaustion, and threshold assembly

This stage takes a unary expected dimension, a retained threshold word, and
the counted-list parser's output. It checks exactly that many nonempty fields
and a final list marker with no suffix, then moves the threshold after the
certificate. Fraction validity is established by the preceding parser stages.
-/
namespace PhdThesisLean.RationalTailAssembly

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open LeanNPHardness
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

abbrev Cell := Sum Unit (Sum Bool (Option Bool))
abbrev Result := Option (List (Option Bool))
abbrev Out := Sum (Option Bool) Bool
def certCell (b : Option Bool) : Cell := .inr (.inr b)
def thresholdCell (b : Bool) : Cell := .inr (.inl b)
def add (b : Option Bool) (r : Result) : Result := r.map (b :: ·)
def exhausted : List Cell → Result
  | [] => some []
  | _ => none
def finish : List Cell → Result
  | .inr (.inr none) :: bs => exhausted bs
  | _ => none
def scan (next : List Cell → Result) : List Cell → Result
  | .inr (.inr (some b)) :: bs => add (some b) (scan next bs)
  | .inr (.inr none) :: bs => add none (next bs)
  | _ => none
def field (next : List Cell → Result) : List Cell → Result
  | .inr (.inr (some b)) :: bs => add (some b) (scan next bs)
  | _ => none
def fields : ℕ → List Cell → Result
  | 0, bs => finish bs
  | n+1, bs => field (fields n) bs
def threshold (n : ℕ) : List Cell → Option (List (Option Bool) × List Bool)
  | .inr (.inl b) :: bs => (threshold n bs).map fun p => (p.1,b::p.2)
  | bs => (fields n bs).map fun fs => (fs,[])
def render (t : List Bool) (s : List (Option Bool)) (r : Result) : List Out :=
  match r with
  | none => []
  | some fs => (s.reverse ++ fs).map .inl ++ t.reverse.map .inr
def renderThreshold (t : List Bool) (r : Option (List (Option Bool) × List Bool)) : List Out :=
  match r with
  | none => []
  | some (fs,bs) => fs.map .inl ++ (t.reverse ++ bs).map .inr
def output (n : ℕ) (t : List Bool) (fs : List (Option Bool)) : List Out :=
  if t = [] then [] else render t.reverse [] (fields n (fs.map certCell))
def input (n : ℕ) (t : List Bool) (fs : List (Option Bool)) : List Cell :=
  List.replicate n (.inl ()) ++ t.map thresholdCell ++ fs.map certCell

theorem render_add (t : List Bool) (s : List (Option Bool)) (b : Option Bool) (r : Result) :
    render t s (add b r) = render t (b::s) r := by
  cases r <;> simp [render, add, List.reverse_cons, List.append_assoc]

def wire := RationalCountedFields.wire

theorem scan_wire (next : List Cell → Result) (f : List Bool) (rest : List (Option Bool)) :
    scan next ((f.map some ++ none :: rest).map certCell) =
      (next (rest.map certCell)).map (fun fs => f.map some ++ none :: fs) := by
  induction f with
  | nil => rfl
  | cons b f ih =>
      change add (some b) (scan next ((f.map some ++ none :: rest).map certCell)) = _
      rw [ih]
      simp [add, Option.map_map, Function.comp_def]

theorem field_wire (next : List Cell → Result) (f : List Bool) (rest : List (Option Bool))
    (hf : f ≠ []) :
    field next ((f.map some ++ none :: rest).map certCell) =
      (next (rest.map certCell)).map (fun fs => f.map some ++ none :: fs) := by
  cases f with
  | nil => contradiction
  | cons b f =>
      change add (some b) (scan next ((f.map some ++ none :: rest).map certCell)) = _
      rw [scan_wire]
      simp [add, Option.map_map, Function.comp_def]

theorem fields_wire (n : ℕ) (fs : List (List Bool)) (tail : List (Option Bool))
    (hf : ∀ f ∈ fs, f ≠ []) :
    fields n ((wire fs ++ none :: tail).map certCell) =
      if fs.length = n ∧ tail = [] then some (wire fs) else none := by
  induction fs generalizing n with
  | nil => cases n <;> cases tail <;> simp [wire, RationalCountedFields.wire, fields, field, finish, exhausted, certCell]
  | cons f fs ih =>
      have hne := hf f (by simp)
      have ht : ∀ f ∈ fs, f ≠ [] := by intro f h; exact hf f (by simp [h])
      cases n with
      | zero =>
          cases f with
          | nil => contradiction
          | cons b f => simp [wire, RationalCountedFields.wire, fields, finish, certCell]
      | succ n =>
          have hw : wire (f::fs) ++ none :: tail = f.map some ++ none :: (wire fs ++ none :: tail) := by
            simp [wire, RationalCountedFields.wire, List.append_assoc]
          rw [fields, hw, field_wire _ _ _ hne, ih n ht]
          by_cases h : fs.length = n ∧ tail = [] <;>
            simp [h, wire, RationalCountedFields.wire]

theorem threshold_blocks (n : ℕ) (t : List Bool) (fs : List (Option Bool)) :
    threshold n (t.map thresholdCell ++ fs.map certCell) =
      (fields n (fs.map certCell)).map (fun xs => (xs,t)) := by
  induction t with
  | nil => cases fs <;> simp [threshold, certCell]
  | cons b t ih => simp [thresholdCell, threshold, ih, Option.map_map, Function.comp_def]

/-- Exact count agreement and exhaustion, after both fraction parsers have run. -/
theorem output_wire (n : ℕ) (t : List Bool) (fs : List (List Bool))
    (tail : List (Option Bool)) (hf : ∀ f ∈ fs, f ≠ []) :
    output n t (wire fs ++ none :: tail) =
      if t ≠ [] ∧ fs.length = n ∧ tail = [] then
        (wire fs).map Sum.inl ++ t.map Sum.inr else [] := by
  rw [output, fields_wire n fs tail hf]
  by_cases h : t = []
  · simp [h]
  · rw [ite_eq_right h]
    by_cases he : fs.length = n ∧ tail = []
    · simp [he, h, render]
    · rw [ite_eq_right he]
      simp only [render, ne_eq, h, not_false_eq_true, true_and, ite_eq_right he]


namespace Machine

inductive Label
  | load | thresholdStart | threshold | column | fieldStart | field | endList | exhausted
  | reverseThreshold | reverseCert | rejectCount | rejectInput | rejectThreshold | rejectSaved
  deriving DecidableEq, Fintype
structure Cursor where
  label : Label
  count : ℕ
  input : List Cell
  threshold : List Bool
  saved : List (Option Bool)
  out : List Out

def advance : Cursor → Sum (List Out) Cursor
  | ⟨.load,n,bs,t,s,o⟩ => .inr ⟨.rejectCount,n,bs,t,s,o⟩
  | ⟨.thresholdStart,n,.inr (.inl b)::bs,t,s,o⟩ => .inr ⟨.threshold,n,bs,b::t,s,o⟩
  | ⟨.thresholdStart,n,bs,t,s,o⟩ => .inr ⟨.rejectCount,n,bs,t,s,o⟩
  | ⟨.threshold,n,.inr (.inl b)::bs,t,s,o⟩ => .inr ⟨.threshold,n,bs,b::t,s,o⟩
  | ⟨.threshold,n,bs,t,s,o⟩ => .inr ⟨.column,n,bs,t,s,o⟩
  | ⟨.column,0,bs,t,s,o⟩ => .inr ⟨.endList,0,bs,t,s,o⟩
  | ⟨.column,n+1,bs,t,s,o⟩ => .inr ⟨.fieldStart,n,bs,t,s,o⟩
  | ⟨.fieldStart,n,.inr (.inr (some b))::bs,t,s,o⟩ => .inr ⟨.field,n,bs,t,some b::s,o⟩
  | ⟨.fieldStart,n,bs,t,s,o⟩ => .inr ⟨.rejectCount,n,bs,t,s,o⟩
  | ⟨.field,n,.inr (.inr (some b))::bs,t,s,o⟩ => .inr ⟨.field,n,bs,t,some b::s,o⟩
  | ⟨.field,n,.inr (.inr none)::bs,t,s,o⟩ => .inr ⟨.column,n,bs,t,none::s,o⟩
  | ⟨.field,n,bs,t,s,o⟩ => .inr ⟨.rejectCount,n,bs,t,s,o⟩
  | ⟨.endList,n,.inr (.inr none)::bs,t,s,o⟩ => .inr ⟨.exhausted,n,bs,t,s,o⟩
  | ⟨.endList,n,bs,t,s,o⟩ => .inr ⟨.rejectCount,n,bs,t,s,o⟩
  | ⟨.exhausted,n,[],t,s,o⟩ => .inr ⟨.reverseThreshold,n,[],t,s,o⟩
  | ⟨.exhausted,n,bs,t,s,o⟩ => .inr ⟨.rejectCount,n,bs,t,s,o⟩
  | ⟨.reverseThreshold,n,bs,[],s,o⟩ => .inr ⟨.reverseCert,n,bs,[],s,o⟩
  | ⟨.reverseThreshold,n,bs,b::t,s,o⟩ => .inr ⟨.reverseThreshold,n,bs,t,s,.inr b::o⟩
  | ⟨.reverseCert,_,_,_,[],o⟩ => .inl o
  | ⟨.reverseCert,n,bs,t,b::s,o⟩ => .inr ⟨.reverseCert,n,bs,t,s,.inl b::o⟩
  | ⟨.rejectCount,0,bs,t,s,o⟩ => .inr ⟨.rejectInput,0,bs,t,s,o⟩
  | ⟨.rejectCount,n+1,bs,t,s,o⟩ => .inr ⟨.rejectCount,n,bs,t,s,o⟩
  | ⟨.rejectInput,n,[],t,s,o⟩ => .inr ⟨.rejectThreshold,n,[],t,s,o⟩
  | ⟨.rejectInput,n,_::bs,t,s,o⟩ => .inr ⟨.rejectInput,n,bs,t,s,o⟩
  | ⟨.rejectThreshold,n,bs,[],s,o⟩ => .inr ⟨.rejectSaved,n,bs,[],s,o⟩
  | ⟨.rejectThreshold,n,bs,_::t,s,o⟩ => .inr ⟨.rejectThreshold,n,bs,t,s,o⟩
  | ⟨.rejectSaved,_,_,_,[],_⟩ => .inl []
  | ⟨.rejectSaved,n,bs,t,_::s,o⟩ => .inr ⟨.rejectSaved,n,bs,t,s,o⟩

def phaseWeight : Label → ℕ
  | .load => 20 | .thresholdStart => 12 | .threshold => 11 | .column => 10
  | .fieldStart => 12 | .field => 11 | .endList => 9 | .exhausted => 8
  | .reverseThreshold => 2 | .reverseCert => 1
  | .rejectCount => 5 | .rejectInput => 4 | .rejectThreshold => 3 | .rejectSaved => 1
def weight (c : Cursor) : ℕ :=
  4*c.count + 4*c.input.length + c.threshold.length + c.saved.length + phaseWeight c.label

def meaning : Cursor → List Out
  | ⟨.thresholdStart,n,.inr (.inl b)::bs,t,_,_⟩ => renderThreshold (b::t) (threshold n bs)
  | ⟨.threshold,n,bs,t,_,_⟩ => renderThreshold t (threshold n bs)
  | ⟨.column,n,bs,t,s,_⟩ => render t s (fields n bs)
  | ⟨.fieldStart,n,bs,t,s,_⟩ => render t s (field (fields n) bs)
  | ⟨.field,n,bs,t,s,_⟩ => render t s (scan (fields n) bs)
  | ⟨.endList,_,bs,t,s,_⟩ => render t s (finish bs)
  | ⟨.exhausted,_,bs,t,s,_⟩ => render t s (exhausted bs)
  | ⟨.reverseThreshold,_,_,t,s,o⟩ => s.reverse.map .inl ++ t.reverse.map .inr ++ o
  | ⟨.reverseCert,_,_,_,s,o⟩ => s.reverse.map .inl ++ o
  | _ => []
def Ready (c : Cursor) : Prop :=
  c.label ≠ .load ∧
  (c.label = .endList ∨ c.label = .exhausted ∨ c.label = .reverseThreshold ∨
    c.label = .reverseCert ∨ c.label = .rejectInput ∨ c.label = .rejectThreshold ∨
    c.label = .rejectSaved → c.count = 0) ∧
  (c.label = .reverseThreshold ∨ c.label = .reverseCert ∨
    c.label = .rejectThreshold ∨ c.label = .rejectSaved → c.input = []) ∧
  (c.label = .reverseCert ∨ c.label = .rejectSaved → c.threshold = []) ∧
  (c.label = .thresholdStart ∨ c.label = .threshold → c.saved = []) ∧
  (c.label ≠ .reverseThreshold ∧ c.label ≠ .reverseCert → c.out = [])

theorem advance_decreases (c c' : Cursor) (h : advance c = .inr c') : weight c' < weight c := by
  rcases c with ⟨l,n,bs,t,s,o⟩
  cases l <;> cases n <;> cases bs <;> cases t <;> cases s <;>
    (repeat' first | casesm* Cell | casesm* Sum Bool (Option Bool) | casesm* Option Bool) <;>
    simp only [advance, reduceCtorEq] at h <;> cases h <;> simp [weight, phaseWeight] <;> omega

theorem ready_advance (c c' : Cursor) (hc : Ready c) (h : advance c = .inr c') : Ready c' := by
  rcases c with ⟨l,n,bs,t,s,o⟩
  cases l <;> cases n <;> cases bs <;> cases t <;> cases s <;>
    (repeat' first | casesm* Cell | casesm* Sum Bool (Option Bool) | casesm* Option Bool) <;>
    simp only [advance, reduceCtorEq] at h <;> cases h <;> simp_all [Ready]

theorem meaning_advance (c : Cursor) (hc : Ready c) :
    meaning c = match advance c with | .inl bs => bs | .inr c' => meaning c' := by
  rcases c with ⟨l,n,bs,t,s,o⟩
  cases l <;> cases n <;> cases bs <;> cases t <;> cases s <;>
    (repeat' first | casesm* Cell | casesm* Sum Bool (Option Bool) | casesm* Option Bool) <;>
    simp_all [Ready, advance, meaning, threshold, fields, field, scan, finish, exhausted,
      add, render, renderThreshold, List.reverse_cons, List.append_assoc]
  all_goals repeat' split <;> simp_all
  all_goals (repeat' first | casesm* ∃ _, _ | casesm* _ ∧ _); subst_vars; simp_all

inductive Stack | input | count | threshold | saved | output deriving DecidableEq, Fintype
structure State where
  cell : Option Cell := none
  mark : Option Unit := none
  bit : Option Bool := none
  saved : Option (Option Bool) := none
  deriving DecidableEq, Fintype
def initial : State := ⟨none,none,none,none⟩
def Alphabet : Stack → Type
  | .input => Cell | .count => Unit | .threshold => Bool | .saved => Option Bool | .output => Out
def go (l : Label) : TM2.Stmt Alphabet Label State := .load (fun _ => initial) (.goto fun _ => l)
def peek (s : State) (b : Option Cell) : State := {s with cell := b}
def isThreshold (s : State) : Bool := match s.cell with | some (.inr (.inl _)) => true | _ => false
def isField (s : State) : Bool := match s.cell with | some (.inr (.inr (some _))) => true | _ => false
def isEnd (s : State) : Bool := decide (s.cell = some (certCell none))
def thresholdBit (s : State) : Bool := match s.cell with | some (.inr (.inl b)) => b | _ => false
def fieldBit (s : State) : Bool := match s.cell with | some (.inr (.inr (some b))) => b | _ => false
def popInput (l : Label) : TM2.Stmt Alphabet Label State := .pop .input peek (go l)
def fieldStep (start : Bool) : TM2.Stmt Alphabet Label State :=
  .peek .input peek <| .branch isField
    (.pop .input peek <| .push .saved (fun s => some (fieldBit s)) (go .field))
    (if start then go .rejectCount else .branch isEnd
      (.pop .input peek <| .push .saved (fun _ => none) (go .column)) (go .rejectCount))
def program : Label → TM2.Stmt Alphabet Label State
  | .load => .peek .input peek <| .branch (fun s => decide (s.cell = some (.inl ())))
      (.pop .input peek <| .push .count (fun _ => ()) (go .load)) (go .thresholdStart)
  | .thresholdStart => .peek .input peek <| .branch isThreshold
      (.pop .input peek <| .push .threshold thresholdBit (go .threshold)) (go .rejectCount)
  | .threshold => .peek .input peek <| .branch isThreshold
      (.pop .input peek <| .push .threshold thresholdBit (go .threshold)) (go .column)
  | .column => .pop .count (fun s b => {s with mark := b}) <|
      .branch (fun s => s.mark.isSome) (go .fieldStart) (go .endList)
  | .fieldStart => fieldStep true
  | .field => fieldStep false
  | .endList => .peek .input peek <| .branch isEnd (popInput .exhausted) (go .rejectCount)
  | .exhausted => .peek .input peek <| .branch (fun s => s.cell.isSome)
      (go .rejectCount) (go .reverseThreshold)
  | .reverseThreshold => .pop .threshold (fun s b => {s with bit := b}) <|
      .branch (fun s => s.bit.isSome)
        (.push .output (fun s => .inr (s.bit.getD false)) (go .reverseThreshold)) (go .reverseCert)
  | .reverseCert => .pop .saved (fun s b => {s with saved := b}) <|
      .branch (fun s => s.saved.isSome)
        (.push .output (fun s => .inl (s.saved.getD none)) (go .reverseCert))
        (.load (fun _ => initial) .halt)
  | .rejectCount => .pop .count (fun s b => {s with mark := b}) <|
      .branch (fun s => s.mark.isSome) (go .rejectCount) (go .rejectInput)
  | .rejectInput => .pop .input peek <|
      .branch (fun s => s.cell.isSome) (go .rejectInput) (go .rejectThreshold)
  | .rejectThreshold => .pop .threshold (fun s b => {s with bit := b}) <|
      .branch (fun s => s.bit.isSome) (go .rejectThreshold) (go .rejectSaved)
  | .rejectSaved => .pop .saved (fun s b => {s with saved := b}) <|
      .branch (fun s => s.saved.isSome) (go .rejectSaved) (.load (fun _ => initial) .halt)
def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .load
  σ := State
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype Cell)
  m := program
def contents (bs : List Cell) (marks : List Unit) (t : List Bool)
    (s : List (Option Bool)) (o : List Out) : (k : Stack) → List (Alphabet k)
  | .input => bs | .count => marks | .threshold => t | .saved => s | .output => o
def cfg (c : Cursor) : computer.Cfg :=
  ⟨some c.label,initial,contents c.input (List.replicate c.count ()) c.threshold c.saved c.out⟩

theorem step_cfg (c : Cursor) (hc : Ready c) :
    computer.step (cfg c) = some (match advance c with
      | .inl bs => haltList computer bs | .inr c' => cfg c') := by
  rcases c with ⟨l,n,bs,t,s,o⟩
  cases l <;> cases n <;> cases bs <;> cases t <;> cases s <;>
    (repeat' first | casesm* Cell | casesm* Sum Bool (Option Bool) | casesm* Option Bool) <;>
    simp_all [Ready, advance, cfg, computer, FinTM2.step, program, fieldStep, popInput, peek,
      go, contents, initial, isThreshold, isField, isEnd, thresholdBit, fieldBit,
      certCell, List.replicate_succ, Function.update, haltList]
  all_goals first | (intro h; cases h) | (funext k; cases k <;> rfl)

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
          · rw [← hw]; rcases c with ⟨l,n,bs,t,s,o⟩; cases l <;> simp [weight, phaseWeight]
          · simpa [he, Function.iterate_one, hm] using hs
      | inr c' =>
          have hlt := advance_decreases c c' he
          obtain ⟨t,ht,hr⟩ := ih (weight c') (by omega) c' (ready_advance c c' hc he) rfl
          refine ⟨t+1, by omega, ?_⟩
          rw [Function.iterate_succ_apply, Option.bind_some, hs]
          simpa [he, hm] using hr

def start (n : ℕ) (t : List Bool) (fs : List (Option Bool)) : Cursor :=
  ⟨.thresholdStart,n,t.map thresholdCell ++ fs.map certCell,[],[],[]⟩
def loadCfg (n k : ℕ) (t : List Bool) (fs : List (Option Bool)) : computer.Cfg :=
  ⟨some .load,initial,contents (input n t fs) (List.replicate k ()) [] [] []⟩

theorem step_load_succ (n k : ℕ) (t : List Bool) (fs : List (Option Bool)) :
    computer.step (loadCfg (n+1) k t fs) = some (loadCfg n (k+1) t fs) := by
  simp [loadCfg, input, computer, FinTM2.step, program, peek, go, initial,
    contents, List.replicate_succ, Function.update]
  funext j; cases j <;> rfl

theorem step_load_zero (k : ℕ) (t : List Bool) (fs : List (Option Bool)) :
    computer.step (loadCfg 0 k t fs) = some (cfg (start k t fs)) := by
  cases t <;> cases fs <;>
    simp [loadCfg, input, computer, FinTM2.step, program, peek, go, initial,
      contents, thresholdCell, certCell, cfg, start, Function.update]

theorem load_run (n k : ℕ) (t : List Bool) (fs : List (Option Bool)) :
    (fun q => q.bind computer.step)^[n+1] (some (loadCfg n k t fs)) =
      some (cfg (start (n+k) t fs)) := by
  induction n generalizing k with
  | zero => simpa using step_load_zero k t fs
  | succ n ih =>
      rw [Function.iterate_succ_apply, Option.bind_some, step_load_succ, ih]
      congr 3; omega

theorem meaning_start (n : ℕ) (t : List Bool) (fs : List (Option Bool)) :
    meaning (start n t fs) = output n t fs := by
  cases t with
  | nil => cases fs <;> simp [start, meaning, output, certCell]
  | cons b t =>
      simp [start, meaning, thresholdCell, threshold_blocks, output, renderThreshold,
        render, List.reverse_cons]
      split <;> simp_all

/-- Linear actual transition bound, including loading the expected count,
checking the final marker/exhaustion, reordering, and every failure cleanup. -/
noncomputable def outputsInTime (n : ℕ) (t : List Bool) (fs : List (Option Bool)) :
    TM2OutputsInTime computer (input n t fs) (some (output n t fs))
      (5*(input n t fs).length+13) := by
  have h := run (start n t fs) (by simp [Ready, start])
  let k := Classical.choose h
  have hk := Classical.choose_spec h
  have hi : initList computer (input n t fs) = loadCfg n 0 t fs := by
    unfold initList loadCfg computer; congr; funext j; cases j <;> rfl
  refine { steps := k+(n+1), evals_in_steps := ?_, steps_le_m := ?_ }
  · change (fun q => q.bind computer.step)^[_] (some (initList computer (input n t fs))) = _
    rw [hi, Function.iterate_add_apply, load_run, Nat.add_zero]
    simpa [k, meaning_start] using hk.2
  · have ht : k ≤ 4*n+4*(t.length+fs.length)+12 := by
      simpa [k, start, weight, phaseWeight] using hk.1
    simp only [input, List.length_append, List.length_replicate, List.length_map]
    omega


end Machine
def unaryEncoding : FinEncoding ℕ where
  Γ := Unit
  encode n := List.replicate n ()
  decode bs := some bs.length
  decode_encode n := by simp
  ΓFin := inferInstance

def inputEncoding : FinEncoding (ℕ × List Bool × List (Option Bool)) :=
  PairEncoding.finEncoding unaryEncoding
    (PairEncoding.finEncoding MachinePrimitives.RawBoolList.finEncoding
      RationalFractionPrefix.Machine.outputEncoding)

def outputEncoding : FinEncoding (List Out) where
  Γ := Out
  encode := id
  decode := some
  decode_encode _ := rfl
  ΓFin := inferInstance

theorem input_encode (n : ℕ) (t : List Bool) (fs : List (Option Bool)) :
    inputEncoding.encode (n,t,fs) = input n t fs := by
  simp [inputEncoding, PairEncoding.finEncoding, unaryEncoding,
    MachinePrimitives.RawBoolList.finEncoding, RationalFractionPrefix.Machine.outputEncoding,
    input, List.map_append, List.map_map, Function.comp_def, List.append_assoc]
  rfl

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputEncoding outputEncoding (fun x => output x.1 x.2.1 x.2.2) where
  tm := Machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 5*Polynomial.X+13
  outputsFun x := by
    rcases x with ⟨n,t,fs⟩
    simpa [input_encode, outputEncoding, Equiv.refl] using! Machine.outputsInTime n t fs

#print axioms Machine.run
#print axioms Machine.outputsInTime
#print axioms computableInPolyTime
#print axioms output_wire

end PhdThesisLean.RationalTailAssembly
