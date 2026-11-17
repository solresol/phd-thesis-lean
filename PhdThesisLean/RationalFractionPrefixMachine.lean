import PhdThesisLean.RationalFractionPrefix

/-!
# Total linear-time fraction-prefix parsing with retention

A four-stack finite TM2 splits the first signed/framed fraction from an
arbitrary Boolean input. Success preserves every bit and inserts one delimiter;
rejection emits the empty word. The count is a stack of frame-width marks.
Every path, including rejection and cleanup, takes at most `4L+10` actual
transitions. A second entry validates and retains a canonical natural field
in `4L+11` transitions; its numeric value remains binary.
-/
namespace PhdThesisLean.RationalFractionPrefix.Machine

open Computability Turing StateTransition
set_option backward.isDefEq.respectTransparency false

inductive Label
  | natural | sign | header (denominator : Bool) | body (denominator : Bool)
  | scanTail | reverse | rejectCount | rejectInput | rejectSaved
  deriving DecidableEq, Fintype

/-- Unbounded data here describe stacks; they are not machine registers. -/
structure Cursor where
  label : Label
  last : Bool
  count : ℕ
  input : List Bool
  saved : List (Option Bool)
  out : List (Option Bool)

def advance : Cursor → Sum (List (Option Bool)) Cursor
  | ⟨.natural, _, n, bs, s, o⟩ => .inr ⟨.header true, true, n, bs, s, o⟩
  | ⟨.sign, _, n, [], s, o⟩ => .inr ⟨.rejectCount, false, n, [], s, o⟩
  | ⟨.sign, _, n, b :: bs, s, o⟩ => .inr ⟨.header false, !b, n, bs, some b :: s, o⟩
  | ⟨.header _, _, n, [], s, o⟩ => .inr ⟨.rejectCount, false, n, [], s, o⟩
  | ⟨.header d, a, n, true :: bs, s, o⟩ =>
      .inr ⟨.header d, a, n + 1, bs, some true :: s, o⟩
  | ⟨.header d, a, n, false :: bs, s, o⟩ =>
      .inr ⟨.body d, a, n, bs, some false :: s, o⟩
  | ⟨.body _, false, 0, bs, s, o⟩ => .inr ⟨.rejectCount, false, 0, bs, s, o⟩
  | ⟨.body false, true, 0, bs, s, o⟩ => .inr ⟨.header true, false, 0, bs, s, o⟩
  | ⟨.body true, true, 0, bs, s, o⟩ => .inr ⟨.scanTail, false, 0, bs, none :: s, o⟩
  | ⟨.body _, _, n + 1, [], s, o⟩ => .inr ⟨.rejectCount, false, n, [], s, o⟩
  | ⟨.body d, _, n + 1, b :: bs, s, o⟩ => .inr ⟨.body d, b, n, bs, some b :: s, o⟩
  | ⟨.scanTail, _, n, [], s, o⟩ => .inr ⟨.reverse, false, n, [], s, o⟩
  | ⟨.scanTail, _, n, b :: bs, s, o⟩ => .inr ⟨.scanTail, false, n, bs, some b :: s, o⟩
  | ⟨.reverse, _, _, _, [], o⟩ => .inl o
  | ⟨.reverse, _, n, bs, b :: s, o⟩ => .inr ⟨.reverse, false, n, bs, s, b :: o⟩
  | ⟨.rejectCount, _, 0, bs, s, o⟩ => .inr ⟨.rejectInput, false, 0, bs, s, o⟩
  | ⟨.rejectCount, _, n + 1, bs, s, o⟩ => .inr ⟨.rejectCount, false, n, bs, s, o⟩
  | ⟨.rejectInput, _, n, [], s, o⟩ => .inr ⟨.rejectSaved, false, n, [], s, o⟩
  | ⟨.rejectInput, _, n, _ :: bs, s, o⟩ => .inr ⟨.rejectInput, false, n, bs, s, o⟩
  | ⟨.rejectSaved, _, _, _, [], _⟩ => .inl []
  | ⟨.rejectSaved, _, n, bs, _ :: s, o⟩ => .inr ⟨.rejectSaved, false, n, bs, s, o⟩

def phaseWeight : Label → ℕ
  | .natural => 11
  | .sign => 10 | .header false => 9 | .body false => 8
  | .header true => 7 | .body true => 6 | .scanTail => 4
  | .reverse | .rejectCount => 3 | .rejectInput => 2 | .rejectSaved => 1

def weight (c : Cursor) : ℕ :=
  4 * c.input.length + 2 * c.count + c.saved.length + phaseWeight c.label

theorem advance_decreases (c c' : Cursor) (h : advance c = .inr c') :
    weight c' < weight c := by
  rcases c with ⟨l, a, n, bs, s, o⟩
  cases l <;> cases n <;> cases bs <;> cases s <;> casesm* Bool <;>
    simp only [advance, reduceCtorEq] at h <;> cases h <;>
    simp [weight, phaseWeight] <;> omega

def meaning : Cursor → List (Option Bool)
  | ⟨.natural, _, n, bs, s, _⟩ => render s (header n true bs)
  | ⟨.sign, _, _, [], _, _⟩ => []
  | ⟨.sign, _, n, b :: bs, s, _⟩ =>
      render s (prepend b (more false (header n (!b) bs)))
  | ⟨.header d, a, n, bs, s, _⟩ => render s (more d (header n a bs))
  | ⟨.body d, a, n, bs, s, _⟩ => render s (more d (body n a bs))
  | ⟨.scanTail, _, _, bs, s, _⟩ => s.reverse ++ bs.map some
  | ⟨.reverse, _, _, _, s, o⟩ => s.reverse ++ o
  | _ => []

def Ready (c : Cursor) : Prop :=
  (c.label = .scanTail ∨ c.label = .reverse ∨ c.label = .rejectInput ∨
    c.label = .rejectSaved → c.count = 0) ∧
  (c.label = .reverse ∨ c.label = .rejectSaved → c.input = []) ∧
  (c.label ≠ .reverse → c.out = [])

theorem meaning_advance (c : Cursor) (hc : Ready c) :
    meaning c = match advance c with | .inl bs => bs | .inr c' => meaning c' := by
  rcases c with ⟨l, a, n, bs, s, o⟩
  cases l <;> cases n <;> cases bs <;> cases s <;> casesm* Bool <;>
    simp_all [Ready, advance, meaning, header, body, more_prepend, render_prepend,
      List.reverse_cons, List.append_assoc]
  all_goals simp [more, render, header, body, prepend]
  all_goals split <;> split <;> simp_all
  all_goals obtain ⟨he, _⟩ := ‹_ ∧ _›; simp [← he]

theorem ready_advance (c c' : Cursor) (hc : Ready c) (h : advance c = .inr c') :
    Ready c' := by
  rcases c with ⟨l, a, n, bs, s, o⟩
  cases l <;> cases n <;> cases bs <;> cases s <;> casesm* Bool <;>
    simp only [advance, reduceCtorEq] at h <;> cases h <;> simp_all [Ready]

inductive Stack | input | count | saved | output
  deriving DecidableEq, Fintype
abbrev State := Bool × Option (Option Bool)
def initial : State := (false, none)
def observe (s : State) (b : Option Bool) : State := (s.1, b.map some)
def observeCell (s : State) (b : Option (Option Bool)) : State := (s.1, b)
def held (s : State) : Bool := (s.2.getD none).getD false
def Alphabet : Stack → Type
  | .input | .count => Bool
  | .saved | .output => Option Bool

def go (l : Label) (a : State → Bool) : TM2.Stmt Alphabet Label State :=
  .load (fun s => (a s, none)) (.goto fun _ => l)

def program : Label → TM2.Stmt Alphabet Label State
  | .natural => go (.header true) (fun _ => true)
  | .sign => .pop .input observe <| .branch (fun s => s.2.isSome)
      (.push .saved (fun s => some (held s)) (go (.header false) (fun s => !held s)))
      (go .rejectCount (fun _ => false))
  | .header d => .pop .input observe <| .branch (fun s => s.2.isSome)
      (.push .saved (fun s => some (held s)) <| .branch held
        (.push .count (fun _ => true) (go (.header d) Prod.fst))
        (go (.body d) Prod.fst))
      (go .rejectCount (fun _ => false))
  | .body d => .pop .count observe <| .branch (fun s => s.2.isSome)
      (.pop .input observe <| .branch (fun s => s.2.isSome)
        (.push .saved (fun s => some (held s)) (go (.body d) held))
        (go .rejectCount (fun _ => false)))
      (.branch Prod.fst
        (if d then .push .saved (fun _ => none) (go .scanTail (fun _ => false))
          else go (.header true) (fun _ => false))
        (go .rejectCount (fun _ => false)))
  | .scanTail => .pop .input observe <| .branch (fun s => s.2.isSome)
      (.push .saved (fun s => some (held s)) (go .scanTail (fun _ => false)))
      (go .reverse (fun _ => false))
  | .reverse => .pop .saved observeCell <| .branch (fun s => s.2.isSome)
      (.push .output (fun s => s.2.getD none) (go .reverse (fun _ => false)))
      (.load (fun _ => initial) .halt)
  | .rejectCount => .pop .count observe <| .branch (fun s => s.2.isSome)
      (go .rejectCount (fun _ => false)) (go .rejectInput (fun _ => false))
  | .rejectInput => .pop .input observe <| .branch (fun s => s.2.isSome)
      (go .rejectInput (fun _ => false)) (go .rejectSaved (fun _ => false))
  | .rejectSaved => .pop .saved observeCell <| .branch (fun s => s.2.isSome)
      (go .rejectSaved (fun _ => false)) (.load (fun _ => initial) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .sign
  σ := State
  initialState := initial
  Γk₀Fin := Bool.fintype
  m := program

def contents (input count : List Bool) (saved out : List (Option Bool)) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .count => count | .saved => saved | .output => out

def cfg (c : Cursor) : computer.Cfg :=
  ⟨some c.label, (c.last, none), contents c.input (List.replicate c.count true) c.saved c.out⟩

/-- Every abstract step is exactly one actual finite-machine transition. -/
theorem step_cfg (c : Cursor) (hc : Ready c) :
    computer.step (cfg c) = some (match advance c with
      | .inl bs => haltList computer bs | .inr c' => cfg c') := by
  rcases c with ⟨l, a, n, bs, s, o⟩
  cases l <;> cases n <;> cases bs <;> cases s <;> casesm* Bool <;>
    simp_all [Ready, advance, computer, FinTM2.step, cfg, program, go, contents,
      Alphabet, observe, observeCell, held, initial, List.replicate_succ,
      Function.update, haltList]
  all_goals funext k; cases k <;> rfl

/-- Total execution, including malformed inputs, full cleanup and state reset. -/
theorem run (c : Cursor) (hc : Ready c) :
    ∃ t, t ≤ weight c ∧
      (fun q => q.bind computer.step)^[t] (some (cfg c)) =
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
            rcases c with ⟨l, a, n, bs, s, o⟩
            cases l <;> casesm* Bool <;> simp [weight, phaseWeight]
          · simpa [he, Function.iterate_one, hm] using hs
      | inr c' =>
          have hlt := advance_decreases c c' he
          obtain ⟨t, ht, hr⟩ := ih (weight c') (by omega) c'
            (ready_advance c c' hc he) rfl
          refine ⟨t + 1, by omega, ?_⟩
          rw [Function.iterate_succ_apply, Option.bind_some, hs]
          simpa [he, hm] using hr

def start (bits : List Bool) : Cursor := ⟨.sign, false, 0, bits, [], []⟩

theorem init_eq (bits : List Bool) : initList computer bits = cfg (start bits) := by
  unfold initList cfg start
  congr
  funext k
  cases k <;> rfl

noncomputable def outputsInTime (bits : List Bool) :
    TM2OutputsInTime computer bits (some (output bits)) (4 * bits.length + 10) := by
  have h := run (start bits) (by simp [Ready, start])
  let t := Classical.choose h
  have ht := Classical.choose_spec h
  refine { steps := t, evals_in_steps := ?_, steps_le_m := ht.1 }
  change (fun q => q.bind computer.step)^[t] (some (initList computer bits)) =
    some (haltList computer (output bits))
  rw [init_eq]
  have hm : meaning (start bits) = output bits := by
    cases bits <;> rfl
  simpa [hm, t] using ht.2

/-- Raw output words: empty means rejection, a delimiter marks success. -/
def outputEncoding : LeanNPHardness.FinEncoding (List (Option Bool)) where
  Γ := Option Bool
  encode := id
  decode := some
  decode_encode _ := rfl
  ΓFin := inferInstance

noncomputable def computableInPolyTime :
    LeanNPHardness.TM2ComputableInPolyTime
      LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding outputEncoding output where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X + 10
  outputsFun bits := by
    simpa [LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding, outputEncoding,
      Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using outputsInTime bits

/-- Original rational input, with an arbitrary trailing binary record retained. -/
noncomputable def rationalOutputsInTime (q : ℚ) (rest : List Bool) :
    TM2OutputsInTime computer
      (RationalWitnessEncoding.encodeRat q ++ rest)
      (some ((RationalWitnessEncoding.encodeRat q).map some ++ none :: rest.map some))
      (4 * (RationalWitnessEncoding.encodeRat q ++ rest).length + 10) := by
  simpa only [output_rational_append] using
    outputsInTime (RationalWitnessEncoding.encodeRat q ++ rest)

/-- The same transition system entered at the canonical natural-field parser. -/
def naturalComputer : FinTM2 := { computer with main := .natural }

noncomputable def naturalOutputsInTime (bits : List Bool) :
    TM2OutputsInTime naturalComputer bits (some (naturalOutput bits))
      (4 * bits.length + 11) := by
  let c : Cursor := ⟨.natural, false, 0, bits, [], []⟩
  have h := run c (by simp [c, Ready])
  let t := Classical.choose h
  have ht := Classical.choose_spec h
  refine { steps := t, evals_in_steps := ?_, steps_le_m := ht.1 }
  have hi : initList naturalComputer bits = cfg c := by
    unfold initList cfg c naturalComputer computer
    congr
    funext k
    cases k <;> rfl
  change (fun q => q.bind computer.step)^[t] (some (initList naturalComputer bits)) =
    some (haltList computer (naturalOutput bits))
  rw [hi]
  exact ht.2

noncomputable def naturalComputableInPolyTime :
    LeanNPHardness.TM2ComputableInPolyTime
      LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding outputEncoding naturalOutput where
  tm := naturalComputer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X + 11
  outputsFun bits := by
    simpa [LeanNPHardness.MachinePrimitives.RawBoolList.finEncoding, outputEncoding,
      Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using naturalOutputsInTime bits

#print axioms naturalOutputsInTime
#print axioms naturalComputableInPolyTime
#print axioms outputsInTime
#print axioms computableInPolyTime
#print axioms parse_iff
#print axioms output_length

end PhdThesisLean.RationalFractionPrefix.Machine
