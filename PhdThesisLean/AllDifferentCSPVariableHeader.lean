import PhdThesisLean.AllDifferentCSPProcessedSections

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-!
# Retain the variable count before expanding the domain section

The third source field is the checked variable count. Copy its canonical
binary payload while retaining the entire source word, then use the upstream
pair-left machine to preserve this count through both structural section
passes. In particular, trailing empty domains must still count as variables.
Record-count construction and final header/section assembly remain separate.
-/

namespace VariableHeader

/-- The unchanged checked source paired with its standard binary variable count. -/
def outputFinEncoding : FinEncoding (RuntimeSystem × ℕ) :=
  LeanNPHardness.PairEncoding.finEncoding RuntimeSourceSections.inputFinEncoding
    finEncodingNatBool

/-- Extract from the source header, before domain expansion can lose empty rows. -/
def retain (C : RuntimeSystem) : RuntimeSystem × ℕ := (C, C.domains.length)

theorem inputEncode_eq_prefix (C : RuntimeSystem) :
    RuntimeSourceSections.inputFinEncoding.encode C =
      SourceOrderRawFields.encode
        [1 + C.domains.length + C.scopes.length, 1, C.domains.length] ++
      DomainFieldSection.rowPayloadEncode C.domains ++
      DomainFieldSection.rowPayloadEncode C.scopes := by
  rw [RuntimeSourceSections.inputEncode_eq_sections]
  simp [DomainFieldSection.inputEncode, DomainFieldSection.inputFields,
    DomainFieldSection.rowPayloadEncode, SourceOrderRawFields.encode, List.append_assoc]

/-- Only the copied binary header increases size; input values are unchanged. -/
theorem output_length_le (C : RuntimeSystem) :
    (outputFinEncoding.encode (retain C)).length ≤
      2 * (RuntimeSourceSections.inputFinEncoding.encode C).length := by
  simp only [outputFinEncoding, retain, LeanNPHardness.PairEncoding.finEncoding_encode_length]
  rw [inputEncode_eq_prefix]
  simp [SourceOrderRawFields.encode, finEncodingNatBool, encodingNatBool]
  omega

end VariableHeader

namespace VariableHeaderMachine

inductive Field
  | outer | singleton | variables
  deriving DecidableEq, Fintype

inductive Stack
  | input | source | header | output
  deriving DecidableEq, Fintype

inductive Label
  | start (field : Field) | bits (field : Field) | suffix | flushHeader | flushSource
  deriving DecidableEq, Fintype

abbrev Tagged := Sum (Option Bool) Bool
abbrev State := Option (Option Bool)
abbrev Alphabet : Stack → Type
  | .output => Tagged
  | _ => Option Bool

private def popped (_ : State) (symbol : State) : State := symbol
private def present : State → Bool | some _ => true | none => false
private def isBit : State → Bool | some (some _) => true | _ => false
private def held : State → Option Bool | some symbol => symbol | none => none
private def heldBit : State → Bool | some (some bit) => bit | _ => false
private def next : Field → Label
  | .outer => .start .singleton | .singleton => .start .variables | .variables => .suffix

/-- Four finite-alphabet stacks copy the third field without decoding a natural
into the control state. Each bit is read and copied explicitly. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .start field => .pop .input popped <| .push .source held <|
      .goto (fun _ => .bits field)
  | .bits field => .pop .input popped <| .branch isBit
      (.push .source held <|
        match field with
        | .variables => .push .header held <| .goto (fun _ => .bits field)
        | _ => .goto (fun _ => .bits field))
      (.branch present
        (.push .input held <| .goto (fun _ => next field))
        (.goto (fun _ => next field)))
  | .suffix => .pop .input popped <| .branch present
      (.push .source held <| .goto (fun _ => .suffix))
      (.goto (fun _ => .flushHeader))
  | .flushHeader => .pop .header popped <| .branch present
      (.push .output (fun s => .inr (heldBit s)) <| .goto (fun _ => .flushHeader))
      (.goto (fun _ => .flushSource))
  | .flushSource => .pop .source popped <| .branch present
      (.push .output (fun s => .inl (held s)) <| .goto (fun _ => .flushSource)) .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .start .outer
  σ := State
  initialState := none
  Γk₀Fin := show Fintype (Option Bool) from inferInstance
  m := program

private def stackContents (input source header : List (Option Bool)) (output : List Tagged) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .source => source | .header => header | .output => output

private def cfg (label : Option Label) (state : State)
    (input source header : List (Option Bool)) (output : List Tagged) : computer.Cfg :=
  ⟨label, state, stackContents input source header output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) :=
  EvalsToInTime computer.step a (some b) time

private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }

private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "header_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, popped,
    present, isBit, held, heldBit, next, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def Boundary : List (Option Bool) → Prop
  | [] => True | none :: _ => True | some _ :: _ => False

private theorem boundary_payload (rows : List (List ℕ)) :
    Boundary (DomainFieldSection.rowPayloadEncode rows) := by
  cases rows <;> simp [DomainFieldSection.rowPayloadEncode,
    DomainFieldSection.rowFields, SourceOrderRawFields.encode, Boundary]

private theorem boundary_append (xs ys : List (Option Bool))
    (hx : Boundary xs) (hy : Boundary ys) : Boundary (xs ++ ys) := by
  cases xs with
  | nil => exact hy
  | cons symbol xs => cases symbol <;> simp_all [Boundary]

private def saved (field : Field) (bits : List Bool) : List (Option Bool) :=
  match field with | .variables => bits.reverse.map some | _ => []

private def bits_run (field : Field) (bits : List Bool)
    (tail source header : List (Option Bool)) (output : List Tagged)
    (state : State) (htail : Boundary tail) :
    Run (cfg (some (.bits field)) state (bits.map some ++ tail) source header output)
      (cfg (some (next field)) tail.head? tail
        (bits.reverse.map some ++ source) (saved field bits ++ header) output)
      (bits.length + 1) := by
  induction bits generalizing source header state with
  | nil =>
      apply one
      cases tail with
      | nil => cases field <;> simp only [saved] <;> header_step
      | cons symbol tail =>
          cases symbol with
          | none => cases field <;> simp only [saved] <;> header_step
          | some bit => exact False.elim htail
  | cons bit bits ih =>
      have h : Run
          (cfg (some (.bits field)) state ((bit :: bits).map some ++ tail) source header output)
          (cfg (some (.bits field)) (some (some bit)) (bits.map some ++ tail)
            (some bit :: source) (saved field [bit] ++ header) output) 1 := by
        apply one
        cases field <;> simp only [saved] <;> header_step
      have rest := ih (some bit :: source) (saved field [bit] ++ header) (some (some bit))
      cases field <;> simpa [saved, List.reverse_cons, List.append_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using seq h rest

private def field_run (field : Field) (bits : List Bool)
    (tail source header : List (Option Bool)) (output : List Tagged)
    (state : State) (htail : Boundary tail) :
    Run (cfg (some (.start field)) state (none :: (bits.map some ++ tail)) source header output)
      (cfg (some (next field)) tail.head? tail
        ((none :: bits.map some).reverse ++ source) (saved field bits ++ header) output)
      (bits.length + 2) := by
  have h : Run
      (cfg (some (.start field)) state (none :: (bits.map some ++ tail)) source header output)
      (cfg (some (.bits field)) (some none) (bits.map some ++ tail)
        (none :: source) header output) 1 := one (by header_step)
  simpa [List.reverse_cons, List.map_reverse, List.append_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    seq h (bits_run field bits tail (none :: source) header output (some none) htail)

private def suffix_run (input source header : List (Option Bool))
    (output : List Tagged) (state : State) :
    Run (cfg (some .suffix) state input source header output)
      (cfg (some .flushHeader) none [] (input.reverse ++ source) header output)
      (input.length + 1) := by
  induction input generalizing source state with
  | nil => exact one (by header_step)
  | cons symbol input ih =>
      have h : Run (cfg (some .suffix) state (symbol :: input) source header output)
          (cfg (some .suffix) (some symbol) input (symbol :: source) header output) 1 :=
        one (by header_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (symbol :: source) (some symbol))

private def flushHeader_run (bits : List Bool) (source : List (Option Bool))
    (output : List Tagged) (state : State) :
    Run (cfg (some .flushHeader) state [] source (bits.map some) output)
      (cfg (some .flushSource) none [] source [] (bits.reverse.map Sum.inr ++ output))
      (bits.length + 1) := by
  induction bits generalizing output state with
  | nil => exact one (by header_step)
  | cons bit bits ih =>
      have h : Run (cfg (some .flushHeader) state [] source ((bit :: bits).map some) output)
          (cfg (some .flushHeader) (some (some bit)) [] source (bits.map some)
            (Sum.inr bit :: output)) 1 := one (by header_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (Sum.inr bit :: output) (some (some bit)))

private def flushSource_run (source : List (Option Bool)) (output : List Tagged) (state : State) :
    Run (cfg (some .flushSource) state [] source [] output)
      (cfg none none [] [] [] (source.reverse.map Sum.inl ++ output))
      (source.length + 1) := by
  induction source generalizing output state with
  | nil => exact one (by header_step)
  | cons symbol source ih =>
      have h : Run (cfg (some .flushSource) state [] (symbol :: source) [] output)
          (cfg (some .flushSource) (some symbol) [] source [] (Sum.inl symbol :: output)) 1 :=
        one (by header_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (Sum.inl symbol :: output) (some symbol))

private def wire (outer singleton countBits : List Bool) (tail : List (Option Bool)) :
    List (Option Bool) :=
  (none :: outer.map some) ++ (none :: singleton.map some) ++
    (none :: countBits.map some) ++ tail

private def run_layout (outer singleton countBits : List Bool) (tail : List (Option Bool))
    (htail : Boundary tail) :
    Run (cfg (some (.start .outer)) none (wire outer singleton countBits tail) [] [] [])
      (cfg none none [] [] []
        ((wire outer singleton countBits tail).map Sum.inl ++ countBits.map Sum.inr))
      (3 * (wire outer singleton countBits tail).length + 6) := by
  let a := none :: outer.map some
  let b := none :: singleton.map some
  let c := none :: countBits.map some
  have houter := field_run .outer outer
    (b ++ c ++ tail) [] [] [] none (by simp [b, Boundary])
  have hsingleton := field_run .singleton singleton
    (c ++ tail) a.reverse [] [] (some none) (by simp [c, Boundary])
  have hvariables := field_run .variables countBits tail
    (b.reverse ++ a.reverse) [] [] (some none) htail
  have hsuffix := suffix_run tail (c.reverse ++ b.reverse ++ a.reverse)
    (countBits.reverse.map some) [] tail.head?
  have hheader := flushHeader_run countBits.reverse
    (tail.reverse ++ c.reverse ++ b.reverse ++ a.reverse) [] none
  have hsource := flushSource_run
    (tail.reverse ++ c.reverse ++ b.reverse ++ a.reverse) (countBits.map Sum.inr) none
  simp only [next, saved, List.append_nil, List.reverse_reverse,
    List.append_assoc] at houter hsingleton hvariables hsuffix hheader hsource
  have hall := seq (seq (seq (seq (seq houter hsingleton) hvariables) hsuffix) hheader) hsource
  have hbound : outer.length + 2 + (singleton.length + 2) + (countBits.length + 2) +
      (tail.length + 1) + (countBits.reverse.length + 1) +
      (tail.reverse ++ c.reverse ++ b.reverse ++ a.reverse).length + 1 ≤
      3 * (wire outer singleton countBits tail).length + 6 := by
    simp [wire, a, b, c]
    omega
  have hmono := LeanNPHardness.MachinePrimitives.evalsToInTimeMono hall (by
    simpa [Nat.add_assoc] using hbound)
  simpa [wire, a, b, c, List.reverse_append, List.map_append, List.map_reverse,
    List.reverse_reverse, List.cons_append, List.append_assoc] using hmono

private theorem init_eq (input : List (Option Bool)) :
    initList computer input = cfg (some (.start .outer)) none input [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Tagged) :
    haltList computer output = cfg none none [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

end VariableHeaderMachine

/-- Exact source preservation and variable-count copying in at most `3s+6`
steps for the complete raw input length `s`, including zero variables. -/
def variableHeader_outputsInTime (C : RuntimeSystem) :
    TM2OutputsInTime VariableHeaderMachine.computer
      (RuntimeSourceSections.inputFinEncoding.encode C)
      (some (VariableHeader.outputFinEncoding.encode (VariableHeader.retain C)))
      (3 * (RuntimeSourceSections.inputFinEncoding.encode C).length + 6) := by
  rw [TM2OutputsInTime, VariableHeaderMachine.init_eq]
  simp only [Option.map_some]
  rw [VariableHeaderMachine.halt_eq]
  have h := VariableHeaderMachine.run_layout
    (encodeNat (1 + C.domains.length + C.scopes.length)) (encodeNat 1)
    (encodeNat C.domains.length)
    (DomainFieldSection.rowPayloadEncode C.domains ++ DomainFieldSection.rowPayloadEncode C.scopes)
    (VariableHeaderMachine.boundary_append _ _
      (VariableHeaderMachine.boundary_payload C.domains)
      (VariableHeaderMachine.boundary_payload C.scopes))
  simpa [VariableHeader.outputFinEncoding, VariableHeader.retain,
    LeanNPHardness.PairEncoding.finEncoding, VariableHeader.inputEncode_eq_prefix,
    SourceOrderRawFields.encode, VariableHeaderMachine.wire, finEncodingNatBool, encodingNatBool,
    List.cons_append, List.append_assoc] using h

/-- The retained count is computed from the checked source, not supplied by the caller. -/
noncomputable def variableHeaderComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem (RuntimeSystem × ℕ)
      RuntimeSourceSections.inputFinEncoding VariableHeader.outputFinEncoding
      VariableHeader.retain where
  tm := VariableHeaderMachine.computer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl VariableHeaderMachine.Tagged
  time := 3 * Polynomial.X + 6
  outputsFun C := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_X] using variableHeader_outputsInTime C

/-- The actual Boolean compiler input constructs the retained source/count pair. -/
noncomputable def runtimeCompilerVariableHeaderComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem (RuntimeSystem × ℕ)
      RuntimeCompilerInput.finEncoding VariableHeader.outputFinEncoding
      VariableHeader.retain := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerSourceSystemComputableInPolyTime variableHeaderComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa [Function.comp_def] using composed.outputsFun C }

#print axioms VariableHeader.output_length_le
#print axioms VariableHeaderMachine.computer
#print axioms variableHeader_outputsInTime
#print axioms variableHeaderComputableInPolyTime
#print axioms runtimeCompilerVariableHeaderComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
