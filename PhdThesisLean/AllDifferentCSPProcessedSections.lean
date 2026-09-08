import PhdThesisLean.AllDifferentCSPSourceSections

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-!
# Process both structural sections from the actual compiler input

The pinned generic adapter transforms the left component of a checked pair.
A small finite machine exchanges the two raw section streams, including their
alphabet tags, so that the same adapter can process scopes and preserve the
already expanded domains. A second exchange restores the domain/scope order.
Header retention and complete structural assembly are still separate tasks.
-/

namespace SectionPairExchange

abbrev Symbol := Sum (Option Bool) (Option Bool)
abbrev State := Option Symbol

inductive Stack
  | input | left | right | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | left | right
  deriving DecidableEq, Fintype

private abbrev Alphabet (_ : Stack) := Symbol
private def present : State → Bool | some _ => true | none => false
private def isLeft : State → Bool | some (.inl _) => true | _ => false
private def held : State → Symbol | some symbol => symbol | none => .inl none
private def exchanged : State → Symbol
  | some (.inl symbol) => .inr symbol
  | some (.inr symbol) => .inl symbol
  | none => .inl none

/-- Classify and retag, then restore the left stream before the right stream.
The last restored stream appears first on the output stack. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input (fun _ symbol => symbol) <| .branch present
      (.branch isLeft
        (.push .left exchanged <| .goto (fun _ => .scan))
        (.push .right exchanged <| .goto (fun _ => .scan)))
      (.goto (fun _ => .left))
  | .left => .pop .left (fun _ symbol => symbol) <| .branch present
      (.push .output held <| .goto (fun _ => .left))
      (.goto (fun _ => .right))
  | .right => .pop .right (fun _ symbol => symbol) <| .branch present
      (.push .output held <| .goto (fun _ => .right)) .halt

/-- Four finite-alphabet stacks suffice for both directions of section exchange. -/
def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := none
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input left right output : List Symbol) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .left => left | .right => right | .output => output

private def cfg (label : Option Label) (state : State)
    (input left right output : List Symbol) : computer.Cfg :=
  ⟨label, state, stackContents input left right output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) :=
  EvalsToInTime computer.step a (some b) time

private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }

private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "exchange_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, present,
    isLeft, held, exchanged, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def scan_run (source left right output : List Symbol) (state : State) :
    Run (cfg (some .scan) state source left right output)
      (cfg (some .left) none []
        ((LeanNPHardness.PairEncoding.leftSymbols source).reverse.map Sum.inr ++ left)
        ((LeanNPHardness.PairEncoding.rightSymbols source).reverse.map Sum.inl ++ right)
        output) (source.length + 1) := by
  induction source generalizing left right state with
  | nil => exact one (by exchange_step)
  | cons symbol source ih =>
      cases symbol with
      | inl symbol =>
          have h : Run (cfg (some .scan) state (.inl symbol :: source) left right output)
              (cfg (some .scan) (some (.inl symbol)) source (.inr symbol :: left) right output)
              1 := one (by exchange_step)
          simpa [LeanNPHardness.PairEncoding.leftSymbols,
            LeanNPHardness.PairEncoding.rightSymbols, List.reverse_cons,
            List.map_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using seq h (ih (.inr symbol :: left) right _)
      | inr symbol =>
          have h : Run (cfg (some .scan) state (.inr symbol :: source) left right output)
              (cfg (some .scan) (some (.inr symbol)) source left (.inl symbol :: right) output)
              1 := one (by exchange_step)
          simpa [LeanNPHardness.PairEncoding.leftSymbols,
            LeanNPHardness.PairEncoding.rightSymbols, List.reverse_cons,
            List.map_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using seq h (ih left (.inl symbol :: right) _)

private def left_run (left right output : List Symbol) (state : State) :
    Run (cfg (some .left) state [] left right output)
      (cfg (some .right) none [] [] right (left.reverse ++ output))
      (left.length + 1) := by
  induction left generalizing output state with
  | nil => exact one (by exchange_step)
  | cons symbol left ih =>
      have h : Run (cfg (some .left) state [] (symbol :: left) right output)
          (cfg (some .left) (some symbol) [] left right (symbol :: output)) 1 :=
        one (by exchange_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (symbol :: output) _)

private def right_run (right output : List Symbol) (state : State) :
    Run (cfg (some .right) state [] [] right output)
      (cfg none none [] [] [] (right.reverse ++ output)) (right.length + 1) := by
  induction right generalizing output state with
  | nil => exact one (by exchange_step)
  | cons symbol right ih =>
      have h : Run (cfg (some .right) state [] [] (symbol :: right) output)
          (cfg (some .right) (some symbol) [] [] right (symbol :: output)) 1 :=
        one (by exchange_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (symbol :: output) _)

private theorem init_eq (input : List Symbol) :
    initList computer input = cfg (some .scan) none input [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Symbol) :
    haltList computer output = cfg none none [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

/-- Exact canonical pair exchange in at most `2s+3` steps, with no restrictions
on the raw words; empty sections and all delimiters are preserved. -/
def outputsInTime (left right : List (Option Bool)) :
    TM2OutputsInTime computer (left.map Sum.inl ++ right.map Sum.inr)
      (some (right.map Sum.inl ++ left.map Sum.inr))
      (2 * (left.length + right.length) + 3) := by
  have hscan := scan_run (left.map Sum.inl ++ right.map Sum.inr) [] [] [] none
  simp only [LeanNPHardness.PairEncoding.leftSymbols_append,
    LeanNPHardness.PairEncoding.rightSymbols_append,
    LeanNPHardness.PairEncoding.leftSymbols_map_inl,
    LeanNPHardness.PairEncoding.leftSymbols_map_inr,
    LeanNPHardness.PairEncoding.rightSymbols_map_inl,
    LeanNPHardness.PairEncoding.rightSymbols_map_inr,
    List.nil_append, List.append_nil, List.length_append, List.length_map] at hscan
  have hleft := left_run (left.reverse.map Sum.inr) (right.reverse.map Sum.inl) [] none
  have hright := right_run (right.reverse.map Sum.inl) (left.map Sum.inr) none
  simp only [List.map_reverse, List.reverse_reverse, List.append_nil] at hscan hleft hright
  have h := seq (seq hscan hleft) hright
  rw [TM2OutputsInTime, init_eq]
  simp only [Option.map_some]
  rw [halt_eq]
  convert h using 1
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, two_mul]

end SectionPairExchange

/-- Put scopes first so the existing checked pair-left adapter can process them. -/
noncomputable def exchangeDomainScopePayloadComputableInPolyTime :
    @TM2ComputableInPolyTime (List (ℕ × ℕ) × List (List ℕ))
      (List (List ℕ) × List (ℕ × ℕ))
      (LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
        ScopeFieldSection.rowPayloadFinEncoding)
      (LeanNPHardness.PairEncoding.finEncoding ScopeFieldSection.rowPayloadFinEncoding
        DomainFieldRow.outputFinEncoding) Prod.swap where
  tm := SectionPairExchange.computer
  inputAlphabet := Equiv.refl SectionPairExchange.Symbol
  outputAlphabet := Equiv.refl SectionPairExchange.Symbol
  time := 2 * Polynomial.X + 3
  outputsFun pair := by
    simpa [LeanNPHardness.PairEncoding.finEncoding, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_X] using SectionPairExchange.outputsInTime
        (DomainFieldRow.outputFinEncoding.encode pair.1)
        (ScopeFieldSection.rowPayloadFinEncoding.encode pair.2)

/-- Restore the original section order after the scope machine has emitted its tags. -/
noncomputable def exchangeScopeDomainOutputComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ) × List (ℕ × ℕ))
      (List (ℕ × ℕ) × List (List ℕ))
      (LeanNPHardness.PairEncoding.finEncoding ScopeFieldSection.outputFinEncoding
        DomainFieldRow.outputFinEncoding)
      (LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
        ScopeFieldSection.outputFinEncoding) Prod.swap where
  tm := SectionPairExchange.computer
  inputAlphabet := Equiv.refl SectionPairExchange.Symbol
  outputAlphabet := Equiv.refl SectionPairExchange.Symbol
  time := 2 * Polynomial.X + 3
  outputsFun pair := by
    simpa [LeanNPHardness.PairEncoding.finEncoding, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_X] using SectionPairExchange.outputsInTime
        (ScopeFieldSection.outputFinEncoding.encode pair.1)
        (DomainFieldRow.outputFinEncoding.encode pair.2)

/-- The complete paired scope pass increases wire length by at most a factor
of four, counting the preserved domain stream as part of both encodings. -/
theorem pairedScopeSection_output_length_le (pair : List (ℕ × ℕ) × List (List ℕ)) :
    ((LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
      ScopeFieldSection.outputFinEncoding).encode pair).length ≤
    4 * ((LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
      ScopeFieldSection.rowPayloadFinEncoding).encode pair).length := by
  have h := ScopeFieldSection.outputEncode_length_le_linear pair.2
  simp only [LeanNPHardness.PairEncoding.finEncoding_encode_length]
  change (DomainFieldRow.outputFinEncoding.encode pair.1).length +
      (ScopeFieldSection.outputEncode pair.2).length ≤ _
  omega

/-- Process all scopes while preserving the exact domain occurrence output.
Only the scope encoding changes; no scope, entry, or repetition is discarded. -/
noncomputable def pairedScopeSectionComputableInPolyTime :
    @TM2ComputableInPolyTime (List (ℕ × ℕ) × List (List ℕ))
      (List (ℕ × ℕ) × List (List ℕ))
      (LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
        ScopeFieldSection.rowPayloadFinEncoding)
      (LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
        ScopeFieldSection.outputFinEncoding) id := by
  let scopeFirst := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    ScopeFieldSection.rowPayloadFinEncoding ScopeFieldSection.outputFinEncoding
    DomainFieldRow.outputFinEncoding id scopeSectionComputableInPolyTime
  let first := compositionComputableInPolyTime _ _ _ _ _
    exchangeDomainScopePayloadComputableInPolyTime scopeFirst
  let composed := compositionComputableInPolyTime _ _ _ _ _ first
    exchangeScopeDomainOutputComputableInPolyTime
  exact { composed with
    outputsFun := fun pair => by
      simpa [Function.comp_def] using composed.outputsFun pair }

/-- The actual Boolean compiler input constructs both exact tagged structural
sections internally. The variable and record-count headers are not yet emitted. -/
noncomputable def runtimeCompilerProcessedSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem (List (ℕ × ℕ) × List (List ℕ))
      RuntimeCompilerInput.finEncoding
      (LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
        ScopeFieldSection.outputFinEncoding)
      (fun C => (RuntimeStructuralView.indexedDomainOccurrences C.domains, C.scopes)) := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerDomainAndScopesComputableInPolyTime pairedScopeSectionComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa [Function.comp_def] using composed.outputsFun C }

#print axioms SectionPairExchange.computer
#print axioms SectionPairExchange.outputsInTime
#print axioms exchangeDomainScopePayloadComputableInPolyTime
#print axioms exchangeScopeDomainOutputComputableInPolyTime
#print axioms pairedScopeSection_output_length_le
#print axioms pairedScopeSectionComputableInPolyTime
#print axioms runtimeCompilerProcessedSectionsComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
