import PhdThesisLean.AllDifferentCSPStructuralAssembly

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-!
# Linear assembly of the complete structural payload

Strip the transport tags from the two section streams, retain every local
record tag and field, and move the saved binary variable count into its
singleton header row. The concrete finite machine outputs the exact checked
structural view in the exhaustion-delimited payload encoding.
-/

namespace StructuralAssemblyMachine

inductive Stack
  | input | body | header | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | flushBody | flushHeader
  deriving DecidableEq, Fintype

abbrev Tagged := Sum (Sum (Option Bool) (Option Bool)) Bool
abbrev State := Option Tagged
abbrev Alphabet : Stack → Type
  | .input => Tagged
  | .header => Bool
  | _ => Option Bool

private def popped (_ : State) (symbol : Option Tagged) : State := symbol
private def poppedBody (_ : State) (symbol : Option (Option Bool)) : State :=
  symbol.map (fun field => .inl (.inl field))
private def poppedHeader (_ : State) (symbol : Option Bool) : State := symbol.map .inr
private def present : State → Bool | some _ => true | none => false
private def isHeader : State → Bool | some (.inr _) => true | _ => false
private def heldField : State → Option Bool
  | some (.inl (.inl field)) | some (.inl (.inr field)) => field
  | _ => none
private def heldBit : State → Bool | some (.inr bit) => bit | _ => false

/-- Four finite stacks; the fixed singleton-row header costs three pushes.
No unbounded numeric value or arithmetic operation occurs in the control. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input popped <| .branch present
      (.branch isHeader
        (.push .header heldBit <| .goto (fun _ => .scan))
        (.push .body heldField <| .goto (fun _ => .scan)))
      (.goto (fun _ => .flushBody))
  | .flushBody => .pop .body poppedBody <| .branch present
      (.push .output heldField <| .goto (fun _ => .flushBody))
      (.goto (fun _ => .flushHeader))
  | .flushHeader => .pop .header poppedHeader <| .branch present
      (.push .output (fun s => some (heldBit s)) <| .goto (fun _ => .flushHeader))
      (.push .output (fun _ => none) <| .push .output (fun _ => some true) <|
        .push .output (fun _ => none) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := none
  Γk₀Fin := show Fintype Tagged from inferInstance
  m := program

private def stackContents (input : List Tagged) (body : List (Option Bool))
    (header : List Bool) (output : List (Option Bool)) : (k : Stack) → List (Alphabet k)
  | .input => input | .body => body | .header => header | .output => output

private def cfg (label : Option Label) (state : State) (input : List Tagged)
    (body : List (Option Bool)) (header : List Bool) (output : List (Option Bool)) :
    computer.Cfg :=
  ⟨label, state, stackContents input body header output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) :=
  EvalsToInTime computer.step a (some b) time

private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }

private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "assembly_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, popped,
    poppedBody, poppedHeader, present, isHeader, heldField, heldBit, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def bodySymbol : Tagged → Option (Option Bool)
  | .inl (.inl field) | .inl (.inr field) => some field
  | .inr _ => none

private def headerSymbol : Tagged → Option Bool
  | .inr bit => some bit
  | .inl _ => none

private def scan_run (input : List Tagged) (body : List (Option Bool))
    (header : List Bool) (output : List (Option Bool)) (state : State) :
    Run (cfg (some .scan) state input body header output)
      (cfg (some .flushBody) none []
        ((input.filterMap bodySymbol).reverse ++ body)
        ((input.filterMap headerSymbol).reverse ++ header) output)
      (input.length + 1) := by
  induction input generalizing body header state with
  | nil => exact one (by assembly_step)
  | cons symbol input ih =>
      cases symbol with
      | inl part =>
          cases part with
          | inl field =>
              have h : Run (cfg (some .scan) state (.inl (.inl field) :: input) body header output)
                  (cfg (some .scan) (some (.inl (.inl field))) input (field :: body) header output)
                  1 := one (by assembly_step)
              simpa [bodySymbol, headerSymbol, List.reverse_cons, List.append_assoc,
                Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                seq h (ih (field :: body) header (some (.inl (.inl field))))
          | inr field =>
              have h : Run (cfg (some .scan) state (.inl (.inr field) :: input) body header output)
                  (cfg (some .scan) (some (.inl (.inr field))) input (field :: body) header output)
                  1 := one (by assembly_step)
              simpa [bodySymbol, headerSymbol, List.reverse_cons, List.append_assoc,
                Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                seq h (ih (field :: body) header (some (.inl (.inr field))))
      | inr bit =>
          have h : Run (cfg (some .scan) state (.inr bit :: input) body header output)
              (cfg (some .scan) (some (.inr bit)) input body (bit :: header) output)
              1 := one (by assembly_step)
          simpa [bodySymbol, headerSymbol, List.reverse_cons, List.append_assoc,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            seq h (ih body (bit :: header) (some (.inr bit)))

private def flushBody_run (body : List (Option Bool)) (header : List Bool)
    (output : List (Option Bool)) (state : State) :
    Run (cfg (some .flushBody) state [] body header output)
      (cfg (some .flushHeader) none [] [] header (body.reverse ++ output))
      (body.length + 1) := by
  induction body generalizing output state with
  | nil => exact one (by assembly_step)
  | cons field body ih =>
      have h : Run (cfg (some .flushBody) state [] (field :: body) header output)
          (cfg (some .flushBody) (some (.inl (.inl field))) [] body header (field :: output))
          1 := one (by assembly_step)
      simpa [List.reverse_cons, List.append_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (ih (field :: output) (some (.inl (.inl field))))

private def flushHeader_run (header : List Bool) (output : List (Option Bool)) (state : State) :
    Run (cfg (some .flushHeader) state [] [] header output)
      (cfg none none [] [] [] ([none, some true, none] ++ header.reverse.map some ++ output))
      (header.length + 1) := by
  induction header generalizing output state with
  | nil => exact one (by assembly_step)
  | cons bit header ih =>
      have h : Run (cfg (some .flushHeader) state [] [] (bit :: header) output)
          (cfg (some .flushHeader) (some (.inr bit)) [] [] header (some bit :: output))
          1 := one (by assembly_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (ih (some bit :: output) (some (.inr bit)))

private def wire (domains scopes : List (Option Bool)) (countBits : List Bool) : List Tagged :=
  domains.map (fun field => .inl (.inl field)) ++
    scopes.map (fun field => .inl (.inr field)) ++ countBits.map .inr

private def run_layout (domains scopes : List (Option Bool)) (countBits : List Bool) :
    Run (cfg (some .scan) none (wire domains scopes countBits) [] [] [])
      (cfg none none [] [] [] ([none, some true, none] ++ countBits.map some ++ domains ++ scopes))
      (2 * (wire domains scopes countBits).length + 3) := by
  have hs := scan_run (wire domains scopes countBits) [] [] [] none
  have hb := flushBody_run (domains ++ scopes).reverse countBits.reverse [] none
  have hh := flushHeader_run countBits.reverse (domains ++ scopes) none
  have hnone {α β : Type} (xs : List α) :
      xs.filterMap (fun _ => (none : Option β)) = [] := by
    simp only [List.filterMap_eq_nil_iff, implies_true]
  simp [wire, List.filterMap_append, List.filterMap_map, Function.comp_def,
    bodySymbol, headerSymbol, hnone] at hs
  simp only [List.reverse_reverse, List.append_nil] at hb hh
  simp only [List.reverse_append] at hb
  have hall := seq (seq hs hb) hh
  simpa [wire, List.length_append, List.length_map, List.length_reverse,
    List.append_assoc, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
    two_mul] using hall

private theorem init_eq (input : List Tagged) :
    initList computer input = cfg (some .scan) none input [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List (Option Bool)) :
    haltList computer output = cfg none none [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

end StructuralAssemblyMachine

/-- Complete singleton-header/section assembly in at most `2s+3` steps for
the actual counted-section wire length `s`, clearing every non-output stack. -/
def structuralAssembly_outputsInTime (sections : CountedSections.Value) :
    TM2OutputsInTime StructuralAssemblyMachine.computer
      (CountedSections.finEncoding.encode sections)
      (some (RuntimeStructuralView.payloadFinEncoding.encode
        (CountedSections.toStructuralView sections)))
      (2 * (CountedSections.finEncoding.encode sections).length + 3) := by
  rw [TM2OutputsInTime, StructuralAssemblyMachine.init_eq]
  simp only [Option.map_some]
  rw [StructuralAssemblyMachine.halt_eq]
  have h := StructuralAssemblyMachine.run_layout
    (DomainFieldRow.outputEncode sections.1.1) (ScopeFieldSection.outputEncode sections.1.2)
    (encodeNat sections.2)
  simpa [RuntimeStructuralView.payloadFinEncoding,
    RuntimeStructuralView.payloadEncode_toStructuralView, CountedSections.finEncoding,
    CountedSections.sectionsFinEncoding, LeanNPHardness.PairEncoding.finEncoding,
    DomainFieldRow.outputFinEncoding, ScopeFieldSection.outputFinEncoding,
    finEncodingNatBool, encodingNatBool, StructuralAssemblyMachine.wire,
    List.map_append, List.map_map, Function.comp_def] using h

noncomputable def structuralAssemblyComputableInPolyTime :
    @TM2ComputableInPolyTime CountedSections.Value AllDifferentCSPEncoding.RuntimeStructuralView
      CountedSections.finEncoding RuntimeStructuralView.payloadFinEncoding
      CountedSections.toStructuralView where
  tm := StructuralAssemblyMachine.computer
  inputAlphabet := Equiv.refl StructuralAssemblyMachine.Tagged
  outputAlphabet := Equiv.refl (Option Bool)
  time := 2 * Polynomial.X + 3
  outputsFun sections := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_X] using structuralAssembly_outputsInTime sections

/-- Construct the exact full structural view from the actual Boolean compiler
input in polynomial bit-level time, using the checked row-payload encoding. -/
noncomputable def runtimeCompilerStructuralPayloadComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem AllDifferentCSPEncoding.RuntimeStructuralView
      RuntimeCompilerInput.finEncoding RuntimeStructuralView.payloadFinEncoding
      AllDifferentCSPEncoding.RuntimeStructuralView.ofRuntimeSystem := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerCountedSectionsComputableInPolyTime structuralAssemblyComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa [Function.comp_def, CountedSections.toStructuralView_ofRuntimeSystem]
        using composed.outputsFun C }

#print axioms StructuralAssemblyMachine.computer
#print axioms structuralAssembly_outputsInTime
#print axioms structuralAssemblyComputableInPolyTime
#print axioms runtimeCompilerStructuralPayloadComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
