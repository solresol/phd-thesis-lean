import PhdThesisLean.RationalRectangularFields

/-!
# Finite runtime-dimension row partitioning

Unary dimensions are supplied by the already bounded count stage. The columns
counter moves to a restoration stack once per coefficient and is restored for
the next row. Both counters are stacks, not unbounded control registers.
-/
namespace PhdThesisLean.RationalRectangularFields.Machine

open Computability Turing StateTransition
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

inductive Label
  | loadRows | loadColumns | row | responseStart | response | column
  | coefficientStart | coefficient | restore | endData | tail | clearColumns | reverse
  | rejectRows | rejectColumns | rejectUsed | rejectInput | rejectSaved
  deriving DecidableEq, Fintype

/-- These natural numbers describe unary stack lengths only. -/
structure Cursor where
  label : Label
  remaining : ℕ
  columns : ℕ
  used : ℕ
  input : Bits
  saved : List Cell
  out : List Cell

def advance : Cursor → Sum (List Cell) Cursor
  | ⟨.loadRows, r, n, k, bs, s, o⟩
  | ⟨.loadColumns, r, n, k, bs, s, o⟩ => .inr ⟨.rejectRows, r, n, k, bs, s, o⟩
  | ⟨.row, 0, n, k, bs, s, o⟩ => .inr ⟨.endData, 0, n, k, bs, s, o⟩
  | ⟨.row, r+1, n, k, bs, s, o⟩ => .inr ⟨.responseStart, r, n, k, bs, s, o⟩
  | ⟨.responseStart, r, n, k, some b :: bs, s, o⟩ =>
      .inr ⟨.response, r, n, k, bs, .response b :: s, o⟩
  | ⟨.responseStart, r, n, k, [], s, o⟩ => .inr ⟨.rejectRows, r, n, k, [], s, o⟩
  | ⟨.responseStart, r, n, k, none :: bs, s, o⟩ => .inr ⟨.rejectRows, r, n, k, bs, s, o⟩
  | ⟨.response, r, n, k, some b :: bs, s, o⟩ =>
      .inr ⟨.response, r, n, k, bs, .response b :: s, o⟩
  | ⟨.response, r, n, k, none :: bs, s, o⟩ => .inr ⟨.column, r, n, k, bs, s, o⟩
  | ⟨.response, r, n, k, [], s, o⟩ => .inr ⟨.rejectRows, r, n, k, [], s, o⟩
  | ⟨.column, r, 0, k, bs, s, o⟩ => .inr ⟨.restore, r, 0, k, bs, .rowEnd :: s, o⟩
  | ⟨.column, r, n+1, k, bs, s, o⟩ => .inr ⟨.coefficientStart, r, n, k+1, bs, s, o⟩
  | ⟨.coefficientStart, r, n, k, some b :: bs, s, o⟩ =>
      .inr ⟨.coefficient, r, n, k, bs, .coefficient b :: s, o⟩
  | ⟨.coefficientStart, r, n, k, [], s, o⟩ => .inr ⟨.rejectRows, r, n, k, [], s, o⟩
  | ⟨.coefficientStart, r, n, k, none :: bs, s, o⟩ => .inr ⟨.rejectRows, r, n, k, bs, s, o⟩
  | ⟨.coefficient, r, n, k, some b :: bs, s, o⟩ =>
      .inr ⟨.coefficient, r, n, k, bs, .coefficient b :: s, o⟩
  | ⟨.coefficient, r, n, k, none :: bs, s, o⟩ =>
      .inr ⟨.column, r, n, k, bs, .fieldEnd :: s, o⟩
  | ⟨.coefficient, r, n, k, [], s, o⟩ => .inr ⟨.rejectRows, r, n, k, [], s, o⟩
  | ⟨.restore, r, n, 0, bs, s, o⟩ => .inr ⟨.row, r, n, 0, bs, s, o⟩
  | ⟨.restore, r, n, k+1, bs, s, o⟩ => .inr ⟨.restore, r, n+1, k, bs, s, o⟩
  | ⟨.endData, r, n, k, none :: bs, s, o⟩ => .inr ⟨.tail, r, n, k, bs, .dataEnd :: s, o⟩
  | ⟨.endData, r, n, k, [], s, o⟩ => .inr ⟨.rejectRows, r, n, k, [], s, o⟩
  | ⟨.endData, r, n, k, some _ :: bs, s, o⟩ => .inr ⟨.rejectRows, r, n, k, bs, s, o⟩
  | ⟨.tail, r, n, k, some b :: bs, s, o⟩ => .inr ⟨.tail, r, n, k, bs, .tail b :: s, o⟩
  | ⟨.tail, r, n, k, none :: bs, s, o⟩ => .inr ⟨.rejectRows, r, n, k, bs, s, o⟩
  | ⟨.tail, r, n, k, [], s, o⟩ => .inr ⟨.clearColumns, r, n, k, [], s, o⟩
  | ⟨.clearColumns, r, 0, k, bs, s, o⟩ => .inr ⟨.reverse, r, 0, k, bs, s, o⟩
  | ⟨.clearColumns, r, n+1, k, bs, s, o⟩ => .inr ⟨.clearColumns, r, n, k, bs, s, o⟩
  | ⟨.reverse, _, _, _, _, [], o⟩ => .inl o
  | ⟨.reverse, r, n, k, bs, b :: s, o⟩ => .inr ⟨.reverse, r, n, k, bs, s, b :: o⟩
  | ⟨.rejectRows, 0, n, k, bs, s, o⟩ => .inr ⟨.rejectColumns, 0, n, k, bs, s, o⟩
  | ⟨.rejectRows, r+1, n, k, bs, s, o⟩ => .inr ⟨.rejectRows, r, n, k, bs, s, o⟩
  | ⟨.rejectColumns, r, 0, k, bs, s, o⟩ => .inr ⟨.rejectUsed, r, 0, k, bs, s, o⟩
  | ⟨.rejectColumns, r, n+1, k, bs, s, o⟩ => .inr ⟨.rejectColumns, r, n, k, bs, s, o⟩
  | ⟨.rejectUsed, r, n, 0, bs, s, o⟩ => .inr ⟨.rejectInput, r, n, 0, bs, s, o⟩
  | ⟨.rejectUsed, r, n, k+1, bs, s, o⟩ => .inr ⟨.rejectUsed, r, n, k, bs, s, o⟩
  | ⟨.rejectInput, r, n, k, [], s, o⟩ => .inr ⟨.rejectSaved, r, n, k, [], s, o⟩
  | ⟨.rejectInput, r, n, k, _ :: bs, s, o⟩ => .inr ⟨.rejectInput, r, n, k, bs, s, o⟩
  | ⟨.rejectSaved, _, _, _, _, [], _⟩ => .inl []
  | ⟨.rejectSaved, r, n, k, bs, _ :: s, o⟩ => .inr ⟨.rejectSaved, r, n, k, bs, s, o⟩

def phaseWeight : Label → ℕ
  | .loadRows | .loadColumns => 30 | .row => 8
  | .responseStart => 13 | .response => 12 | .column => 11
  | .coefficientStart => 12 | .coefficient => 11 | .restore => 9
  | .endData => 7 | .tail => 6 | .clearColumns => 5 | .reverse => 2
  | .rejectRows => 6 | .rejectColumns => 5 | .rejectUsed => 4
  | .rejectInput => 3 | .rejectSaved => 1

def loopWeight : Label → ℕ → ℕ → ℕ
  | .responseStart, n, k | .response, n, k | .column, n, k
  | .coefficientStart, n, k | .coefficient, n, k => 3*n+k
  | .restore, _, k => k
  | _, _, _ => 0

def weight (c : Cursor) : ℕ :=
  c.remaining * (4*(c.columns+c.used)+20) + 2*(c.columns+c.used) +
    loopWeight c.label c.columns c.used + 4*c.input.length + c.saved.length + phaseWeight c.label

theorem advance_decreases (c c' : Cursor) (h : advance c = .inr c') : weight c' < weight c := by
  rcases c with ⟨l,r,n,k,bs,s,o⟩
  cases l <;> cases r <;> cases n <;> cases k <;> cases bs <;> cases s <;> (try casesm* Option Bool) <;>
    simp only [advance, reduceCtorEq] at h <;> cases h <;>
    simp [weight, loopWeight, phaseWeight, Nat.mul_add, Nat.add_mul] <;> omega

def endRow (r d : ℕ) (bs : Bits) : Result := add [.rowEnd] (rows r d bs)

def meaning : Cursor → List Cell
  | ⟨.row, r, n, k, bs, s, _⟩ => render s (rows r (n+k) bs)
  | ⟨.responseStart, r, n, k, bs, s, _⟩ => render s (field true (fields n (endRow r (n+k))) bs)
  | ⟨.response, r, n, k, bs, s, _⟩ => render s (scan true (fields n (endRow r (n+k))) bs)
  | ⟨.column, r, n, k, bs, s, _⟩ => render s (fields n (endRow r (n+k)) bs)
  | ⟨.coefficientStart, r, n, k, bs, s, _⟩ => render s (field false (fields n (endRow r (n+k))) bs)
  | ⟨.coefficient, r, n, k, bs, s, _⟩ => render s (scan false (fields n (endRow r (n+k))) bs)
  | ⟨.restore, r, n, k, bs, s, _⟩ => render s (rows r (n+k) bs)
  | ⟨.endData, _, _, _, bs, s, _⟩ => render s (ending bs)
  | ⟨.tail, _, _, _, bs, s, _⟩ => render s (tail bs)
  | ⟨.clearColumns, _, _, _, _, s, _⟩ => s.reverse
  | ⟨.reverse, _, _, _, _, s, o⟩ => s.reverse ++ o
  | _ => []

def Ready (c : Cursor) : Prop :=
  c.label ≠ .loadRows ∧ c.label ≠ .loadColumns ∧
  (c.label = .endData ∨ c.label = .tail ∨ c.label = .clearColumns ∨ c.label = .reverse ∨
    c.label = .rejectColumns ∨ c.label = .rejectUsed ∨ c.label = .rejectInput ∨ c.label = .rejectSaved → c.remaining = 0) ∧
  (c.label = .reverse ∨ c.label = .rejectUsed ∨ c.label = .rejectInput ∨ c.label = .rejectSaved → c.columns = 0) ∧
  (c.label = .row ∨ c.label = .endData ∨ c.label = .tail ∨ c.label = .clearColumns ∨ c.label = .reverse ∨
    c.label = .rejectInput ∨ c.label = .rejectSaved → c.used = 0) ∧
  (c.label = .clearColumns ∨ c.label = .reverse ∨ c.label = .rejectSaved → c.input = []) ∧
  (c.label ≠ .reverse → c.out = [])

theorem ready_advance (c c' : Cursor) (hc : Ready c) (h : advance c = .inr c') : Ready c' := by
  rcases c with ⟨l,r,n,k,bs,s,o⟩
  cases l <;> cases r <;> cases n <;> cases k <;> cases bs <;> cases s <;> (try casesm* Option Bool) <;>
    simp only [advance, reduceCtorEq] at h <;> cases h <;> simp_all [Ready]

theorem meaning_advance (c : Cursor) (hc : Ready c) :
    meaning c = match advance c with | .inl bs => bs | .inr c' => meaning c' := by
  rcases c with ⟨l,r,n,k,bs,s,o⟩
  cases l <;> cases r <;> cases n <;> cases k <;> cases bs <;> cases s <;> (try casesm* Option Bool) <;>
    simp_all [Ready, advance, meaning, rows, fields, field, scan, ending, tail, endRow,
      render_add, tag, close, List.reverse_cons, List.append_assoc, Nat.add_assoc]
  all_goals first | rfl | simp [Nat.add_left_comm, Nat.add_comm, fields, field, tag]

inductive Stack | input | remaining | columns | used | saved | output deriving DecidableEq, Fintype
structure State where
  bit : Option (Option Bool) := none
  cell : Option Cell := none
  deriving DecidableEq, Fintype
def initial : State := ⟨none,none⟩
def observe (s : State) (b : Option Bool) : State := {s with bit := b.map some}
def observeBit (s : State) (b : Option (Option Bool)) : State := {s with bit := b}
def held (s : State) : Bool := (s.bit.getD none).getD false
def Alphabet : Stack → Type
  | .input => Option Bool
  | .remaining | .columns | .used => Bool
  | .saved | .output => Cell

def go (l : Label) : TM2.Stmt Alphabet Label State := .load (fun _ => initial) (.goto fun _ => l)
def reject : TM2.Stmt Alphabet Label State := go .rejectRows
def hasBit (yes no : TM2.Stmt Alphabet Label State) : TM2.Stmt Alphabet Label State :=
  .branch (fun s => s.bit.isSome && (s.bit.getD none).isSome) yes no
def fieldStep (response start : Bool) : TM2.Stmt Alphabet Label State :=
  .pop .input observeBit <| .branch (fun s => s.bit.isSome)
    (hasBit
      (.push .saved (fun s => tag response (held s)) (go (if response then .response else .coefficient)))
      (if start then reject else if response then go .column else
        .push .saved (fun _ => .fieldEnd) (go .column))) reject

def program : Label → TM2.Stmt Alphabet Label State
  | .loadRows => .pop .input observeBit <| .branch (fun s => s.bit.isSome)
      (hasBit (.push .remaining (fun _ => true) (go .loadRows)) (go .loadColumns)) reject
  | .loadColumns => .pop .input observeBit <| .branch (fun s => s.bit.isSome)
      (hasBit (.push .columns (fun _ => true) (go .loadColumns)) (go .row)) reject
  | .row => .pop .remaining observe <| .branch (fun s => s.bit.isSome) (go .responseStart) (go .endData)
  | .responseStart => fieldStep true true
  | .response => fieldStep true false
  | .coefficientStart => fieldStep false true
  | .coefficient => fieldStep false false
  | .column => .pop .columns observe <| .branch (fun s => s.bit.isSome)
      (.push .used (fun _ => true) (go .coefficientStart))
      (.push .saved (fun _ => .rowEnd) (go .restore))
  | .restore => .pop .used observe <| .branch (fun s => s.bit.isSome)
      (.push .columns (fun _ => true) (go .restore)) (go .row)
  | .endData => .pop .input observeBit <| .branch (fun s => s.bit.isSome)
      (hasBit reject (.push .saved (fun _ => .dataEnd) (go .tail))) reject
  | .tail => .pop .input observeBit <| .branch (fun s => s.bit.isSome)
      (hasBit (.push .saved (fun s => .tail (held s)) (go .tail)) reject) (go .clearColumns)
  | .clearColumns => .pop .columns observe <| .branch (fun s => s.bit.isSome) (go .clearColumns) (go .reverse)
  | .reverse => .pop .saved (fun s b => {s with cell := b}) <| .branch (fun s => s.cell.isSome)
      (.push .output (fun s => s.cell.getD .dataEnd) (go .reverse)) (.load (fun _ => initial) .halt)
  | .rejectRows => .pop .remaining observe <| .branch (fun s => s.bit.isSome) (go .rejectRows) (go .rejectColumns)
  | .rejectColumns => .pop .columns observe <| .branch (fun s => s.bit.isSome) (go .rejectColumns) (go .rejectUsed)
  | .rejectUsed => .pop .used observe <| .branch (fun s => s.bit.isSome) (go .rejectUsed) (go .rejectInput)
  | .rejectInput => .pop .input observeBit <| .branch (fun s => s.bit.isSome) (go .rejectInput) (go .rejectSaved)
  | .rejectSaved => .pop .saved (fun s b => {s with cell := b}) <| .branch (fun s => s.cell.isSome)
      (go .rejectSaved) (.load (fun _ => initial) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .loadRows
  σ := State
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := program

def contents (input : Bits) (r n k : List Bool) (saved out : List Cell) :
    (j : Stack) → List (Alphabet j)
  | .input => input | .remaining => r | .columns => n | .used => k | .saved => saved | .output => out
def cfg (c : Cursor) : computer.Cfg :=
  ⟨some c.label, initial, contents c.input (List.replicate c.remaining true)
    (List.replicate c.columns true) (List.replicate c.used true) c.saved c.out⟩

theorem step_cfg (c : Cursor) (hc : Ready c) :
    computer.step (cfg c) = some (match advance c with
      | .inl bs => haltList computer bs | .inr c' => cfg c') := by
  rcases c with ⟨l,r,n,k,bs,s,o⟩
  cases l <;> cases r <;> cases n <;> cases k <;> cases bs <;> cases s <;> (try casesm* Option Bool) <;>
    simp_all [Ready, advance, computer, FinTM2.step, cfg, program, fieldStep, hasBit, reject,
      go, contents, Alphabet, observe, observeBit, held, initial, tag, List.replicate_succ,
      Function.update, haltList]
  all_goals funext j; cases j <;> rfl

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
          · rw [← hw]
            rcases c with ⟨l,r,n,k,bs,s,o⟩
            cases l <;> simp [weight, phaseWeight]
          · simpa [he, Function.iterate_one, hm] using hs
      | inr c' =>
          have hlt := advance_decreases c c' he
          obtain ⟨t, ht, hr⟩ := ih (weight c') (by omega) c' (ready_advance c c' hc he) rfl
          refine ⟨t+1, by omega, ?_⟩
          rw [Function.iterate_succ_apply, Option.bind_some, hs]
          simpa [he, hm] using hr

def start (r d : ℕ) (bits : Bits) : Cursor := ⟨.row,r,d,0,bits,[],[]⟩
def input (r d : ℕ) (bits : Bits) : Bits :=
  List.replicate r (some true) ++ none :: List.replicate d (some true) ++ none :: bits
def loadColumnsCfg (r d n : ℕ) (bits : Bits) : computer.Cfg :=
  ⟨some .loadColumns, initial, contents (List.replicate d (some true) ++ none :: bits)
    (List.replicate r true) (List.replicate n true) [] [] []⟩
def loadRowsCfg (r d n : ℕ) (bits : Bits) : computer.Cfg :=
  ⟨some .loadRows, initial, contents (input r d bits) (List.replicate n true) [] [] [] []⟩

theorem step_loadColumns_succ (r d n : ℕ) (bits : Bits) :
    computer.step (loadColumnsCfg r (d+1) n bits) = some (loadColumnsCfg r d (n+1) bits) := by
  simp [computer, FinTM2.step, loadColumnsCfg, program, hasBit, go, contents,
    Alphabet, observeBit, initial, List.replicate_succ, Function.update]
  funext j; cases j <;> rfl
theorem step_loadColumns_zero (r n : ℕ) (bits : Bits) :
    computer.step (loadColumnsCfg r 0 n bits) = some (cfg (start r n bits)) := by
  simp [computer, FinTM2.step, loadColumnsCfg, program, hasBit, go, contents,
    Alphabet, observeBit, initial, cfg, start, Function.update]
  funext j; cases j <;> rfl
theorem loadColumns_run (r d n : ℕ) (bits : Bits) :
    (fun q => q.bind computer.step)^[d+1] (some (loadColumnsCfg r d n bits)) =
      some (cfg (start r (d+n) bits)) := by
  induction d generalizing n with
  | zero => simpa using step_loadColumns_zero r n bits
  | succ d ih =>
      rw [Function.iterate_succ_apply, Option.bind_some, step_loadColumns_succ, ih]
      congr 3; omega
theorem step_loadRows_succ (r d n : ℕ) (bits : Bits) :
    computer.step (loadRowsCfg (r+1) d n bits) = some (loadRowsCfg r d (n+1) bits) := by
  simp [computer, FinTM2.step, loadRowsCfg, input, program, hasBit, go, contents,
    Alphabet, observeBit, initial, List.replicate_succ, Function.update]
  funext j; cases j <;> rfl
theorem step_loadRows_zero (d n : ℕ) (bits : Bits) :
    computer.step (loadRowsCfg 0 d n bits) = some (loadColumnsCfg n d 0 bits) := by
  simp [computer, FinTM2.step, loadRowsCfg, loadColumnsCfg, input, program, hasBit, go, contents,
    Alphabet, observeBit, initial, Function.update]
  funext j; cases j <;> rfl
theorem loadRows_run (r d n : ℕ) (bits : Bits) :
    (fun q => q.bind computer.step)^[r+1] (some (loadRowsCfg r d n bits)) =
      some (loadColumnsCfg (r+n) d 0 bits) := by
  induction r generalizing n with
  | zero => simpa using step_loadRows_zero d n bits
  | succ r ih =>
      rw [Function.iterate_succ_apply, Option.bind_some, step_loadRows_succ, ih]
      congr 2; omega
theorem init_eq (r d : ℕ) (bits : Bits) : initList computer (input r d bits) = loadRowsCfg r d 0 bits := by
  unfold initList loadRowsCfg
  congr
  funext j; cases j <;> rfl

/-- Includes both unary-header loads, every row/column step, restoring columns,
retaining the suffix, final reversal, and every rejection/cleanup path. -/
noncomputable def outputsInTime (r d : ℕ) (bits : Bits) :
    TM2OutputsInTime computer (input r d bits) (some (output r d bits))
      (4*r*d + 21*r + 3*d + 4*bits.length + 10) := by
  have h := run (start r d bits) (by simp [Ready, start])
  let t := Classical.choose h
  have ht := Classical.choose_spec h
  refine { steps := t+(d+1)+(r+1), evals_in_steps := ?_, steps_le_m := ?_ }
  · change (fun q => q.bind computer.step)^[t+(d+1)+(r+1)]
      (some (initList computer (input r d bits))) = some (haltList computer (output r d bits))
    rw [init_eq, Function.iterate_add_apply, loadRows_run, Nat.add_zero,
      Function.iterate_add_apply, loadColumns_run, Nat.add_zero]
    simpa [start, meaning, output, t] using ht.2
  · have ht' : t ≤ r*(4*d+20)+2*d+4*bits.length+8 := ht.1
    nlinarith

theorem time_le (r d : ℕ) (bits : Bits) :
    4*r*d + 21*r + 3*d + 4*bits.length + 10 ≤ 32*((input r d bits).length+1)^2 := by
  simp only [input, List.length_append, List.length_cons, List.length_replicate]
  nlinarith

#print axioms run
#print axioms outputsInTime
#print axioms time_le

end PhdThesisLean.RationalRectangularFields.Machine
