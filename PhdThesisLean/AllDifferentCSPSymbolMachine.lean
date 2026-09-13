import PhdThesisLean.AllDifferentCSPSymbols
import PhdThesisLean.AllDifferentCSPCountedSections

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-!
# Extract domain symbols while retaining the exact occurrence stream

Each checked occurrence consists of four source-order fields: row length,
tag, variable index, and symbol. A finite four-phase scan copies every input
cell and separately retains only the symbol fields. The output uses the
existing checked pair and raw-field encodings. Deduplication and ranking
remain subsequent machine obligations.
-/

namespace DomainSymbolExtraction

abbrev Value := List (ℕ × ℕ) × List ℕ

def finEncoding : FinEncoding Value :=
  LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
    SourceOrderRawFields.finEncoding

def retain (occurrences : List (ℕ × ℕ)) : Value :=
  (occurrences, DomainSymbols.extract occurrences)

end DomainSymbolExtraction

namespace DomainSymbolMachine

inductive Field
  | row | tag | index | value
  deriving DecidableEq, Fintype

def next : Field → Field
  | .row => .tag | .tag => .index | .index => .value | .value => .row

def advance (field : Field) : Option Bool → Field
  | none => next field | some _ => field

inductive Stack
  | input | source | symbols | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | flushSymbols | flushSource
  deriving DecidableEq, Fintype

abbrev Tagged := Sum (Option Bool) (Option Bool)
abbrev State := Field × Option (Option Bool)
abbrev Alphabet : Stack → Type
  | .output => Tagged | _ => Option Bool

def initialState : State := (.value, none)

private def observe (state : State) (symbol : Option (Option Bool)) : State :=
  (symbol.elim state.1 (advance state.1), symbol)
private def remember (state : State) (symbol : Option (Option Bool)) : State :=
  (state.1, symbol)
private def present (state : State) : Bool := state.2.isSome
private def held (state : State) : Option Bool := state.2.getD none

/-- Four finite stacks and four field phases. All numbers stay in binary on
stacks; the control only distinguishes delimiters, bits, and field positions. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch present
      (.push .source held <| .branch (fun state => decide (state.1 = .value))
        (.push .symbols held <| .goto (fun _ => .scan))
        (.goto (fun _ => .scan)))
      (.goto (fun _ => .flushSymbols))
  | .flushSymbols => .pop .symbols remember <| .branch present
      (.push .output (fun state => .inr (held state)) <| .goto (fun _ => .flushSymbols))
      (.goto (fun _ => .flushSource))
  | .flushSource => .pop .source remember <| .branch present
      (.push .output (fun state => .inl (held state)) <| .goto (fun _ => .flushSource))
      (.load (fun _ => initialState) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := initialState
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input source symbols : List (Option Bool))
    (output : List Tagged) : (k : Stack) → List (Alphabet k)
  | .input => input | .source => source | .symbols => symbols | .output => output

private def cfg (label : Option Label) (field : Field) (symbol : Option (Option Bool))
    (input source symbols : List (Option Bool)) (output : List Tagged) : computer.Cfg :=
  ⟨label, (field, symbol), stackContents input source symbols output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) :=
  EvalsToInTime computer.step a (some b) time

private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }

private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

private def widen {a b : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (hmn : m ≤ n) : Run a b n :=
  { h with steps_le_m := h.steps_le_m.trans hmn }

local macro "symbol_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observe, remember, present, held, initialState, advance, next, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

/-- A pure trace used only to describe the finite scanner's exact execution. -/
private def collect (field : Field) : List (Option Bool) → Field × List (Option Bool)
  | [] => (field, [])
  | cell :: cells =>
      let following := advance field cell
      let rest := collect following cells
      (rest.1, if following = .value then cell :: rest.2 else rest.2)

private theorem collect_length_le (field : Field) (input : List (Option Bool)) :
    (collect field input).2.length ≤ input.length := by
  induction input generalizing field with
  | nil => simp [collect]
  | cons cell cells ih =>
      dsimp only [collect]
      split <;> simp only [List.length_cons] <;> have := ih (advance field cell) <;> omega

private def scan_run (field : Field) (input source symbols : List (Option Bool))
    (output : List Tagged) (symbol : Option (Option Bool)) :
    Run (cfg (some .scan) field symbol input source symbols output)
      (cfg (some .flushSymbols) (collect field input).1 none []
        (input.reverse ++ source) ((collect field input).2.reverse ++ symbols) output)
      (input.length + 1) := by
  induction input generalizing field source symbols symbol with
  | nil =>
      simp only [collect, List.reverse_nil, List.nil_append]
      exact one (by symbol_step)
  | cons cell cells ih =>
      have h : Run (cfg (some .scan) field symbol (cell :: cells) source symbols output)
          (cfg (some .scan) (advance field cell) (some cell) cells (cell :: source)
            (if advance field cell = .value then cell :: symbols else symbols) output) 1 := by
        apply one
        cases field <;> cases cell <;> symbol_step
      have rest := ih (advance field cell) (cell :: source)
        (if advance field cell = .value then cell :: symbols else symbols) (some cell)
      have both := seq h rest
      by_cases hc : advance field cell = .value <;>
        simpa [collect, hc, List.reverse_cons, List.append_assoc,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using both

private def flushSymbols_run (field : Field) (source symbols : List (Option Bool))
    (output : List Tagged) (symbol : Option (Option Bool)) :
    Run (cfg (some .flushSymbols) field symbol [] source symbols output)
      (cfg (some .flushSource) field none [] source []
        (symbols.reverse.map Sum.inr ++ output)) (symbols.length + 1) := by
  induction symbols generalizing output symbol with
  | nil => exact one (by symbol_step)
  | cons cell cells ih =>
      have h : Run (cfg (some .flushSymbols) field symbol [] source (cell :: cells) output)
          (cfg (some .flushSymbols) field (some cell) [] source cells (.inr cell :: output)) 1 :=
        one (by symbol_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (.inr cell :: output) (some cell))

private def flushSource_run (field : Field) (source : List (Option Bool))
    (output : List Tagged) (symbol : Option (Option Bool)) :
    Run (cfg (some .flushSource) field symbol [] source [] output)
      (cfg none .value none [] [] [] (source.reverse.map Sum.inl ++ output))
      (source.length + 1) := by
  induction source generalizing output symbol with
  | nil => exact one (by symbol_step)
  | cons cell cells ih =>
      have h : Run (cfg (some .flushSource) field symbol [] (cell :: cells) [] output)
          (cfg (some .flushSource) field (some cell) [] cells [] (.inl cell :: output)) 1 :=
        one (by symbol_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (.inl cell :: output) (some cell))

private theorem collect_bits (field : Field) (bits : List Bool) (rest : List (Option Bool)) :
    collect field (bits.map some ++ rest) =
      ((collect field rest).1,
        (if field = .value then bits.map some else []) ++ (collect field rest).2) := by
  induction bits with
  | nil => simp
  | cons bit bits ih =>
      by_cases hf : field = .value
      · subst field
        simp [collect, advance, ih]
      · simp [collect, advance, ih, hf]

private theorem collect_field (field : Field) (value : ℕ) (rest : List (Option Bool)) :
    collect field (none :: (encodeNat value).map some ++ rest) =
      ((collect (next field) rest).1,
        (if next field = .value then none :: (encodeNat value).map some else []) ++
          (collect (next field) rest).2) := by
  by_cases hf : next field = .value <;> simp [collect, advance, collect_bits, hf]

private theorem collect_occurrences (occurrences : List (ℕ × ℕ)) :
    collect .value (DomainFieldRow.outputEncode occurrences) =
      (.value, SourceOrderRawFields.encode (DomainSymbols.extract occurrences)) := by
  induction occurrences with
  | nil => rfl
  | cons occurrence occurrences ih =>
      change collect .value
        (DomainOccurrenceFieldBlock.outputEncode occurrence ++ DomainFieldRow.outputEncode occurrences) = _
      have hblock : DomainOccurrenceFieldBlock.outputEncode occurrence =
          (none :: (encodeNat 3).map some) ++ (none :: (encodeNat 0).map some) ++
          (none :: (encodeNat occurrence.1).map some) ++
          (none :: (encodeNat occurrence.2).map some) := by
        simp [DomainOccurrenceFieldBlock.outputEncode, SourceOrderRawFields.encode]
      rw [hblock]
      simp only [List.append_assoc, collect_field, next]
      simp [ih, DomainSymbols.extract, SourceOrderRawFields.encode, List.flatMap_cons]

private def run_occurrences (occurrences : List (ℕ × ℕ)) :
    Run (cfg (some .scan) .value none (DomainFieldRow.outputEncode occurrences) [] [] [])
      (cfg none .value none [] [] []
        ((DomainFieldRow.outputEncode occurrences).map Sum.inl ++
          (SourceOrderRawFields.encode (DomainSymbols.extract occurrences)).map Sum.inr))
      (3 * (DomainFieldRow.outputEncode occurrences).length + 3) := by
  let input := DomainFieldRow.outputEncode occurrences
  let values := SourceOrderRawFields.encode (DomainSymbols.extract occurrences)
  have hs := scan_run .value input [] [] [] none
  have ht : collect .value input = (.value, values) := collect_occurrences occurrences
  simp only [ht, List.append_nil] at hs
  have hv := flushSymbols_run .value input.reverse values.reverse [] none
  have hi := flushSource_run .value input.reverse (values.map Sum.inr) none
  simp only [List.reverse_reverse, List.append_nil] at hv hi
  have hall := seq (seq hs hv) hi
  have hlen := collect_length_le .value input
  rw [ht] at hlen
  apply widen hall
  simp only [List.length_reverse]
  dsimp only at hlen
  dsimp only [input] at *
  omega

private theorem init_eq (input : List (Option Bool)) :
    initList computer input = cfg (some .scan) .value none input [] [] [] := by
  simp only [initList, computer, cfg, initialState]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Tagged) :
    haltList computer output = cfg none .value none [] [] [] output := by
  simp only [haltList, computer, cfg, initialState]
  congr 1
  funext k
  cases k <;> rfl

end DomainSymbolMachine

namespace DomainSymbolExtraction

/-- Extracted symbols are a selection of complete fields of the input wire. -/
theorem symbolsEncode_length_le (occurrences : List (ℕ × ℕ)) :
    (SourceOrderRawFields.encode (DomainSymbols.extract occurrences)).length ≤
      (DomainFieldRow.outputEncode occurrences).length := by
  have h := DomainSymbolMachine.collect_length_le .value (DomainFieldRow.outputEncode occurrences)
  simpa only [DomainSymbolMachine.collect_occurrences] using h

/-- The complete retained-source/symbol pair is at most twice its input length. -/
theorem retain_encode_length_le (occurrences : List (ℕ × ℕ)) :
    (finEncoding.encode (retain occurrences)).length ≤
      2 * (DomainFieldRow.outputEncode occurrences).length := by
  have h := symbolsEncode_length_le occurrences
  simp only [finEncoding, retain, LeanNPHardness.PairEncoding.finEncoding_encode_length]
  change (DomainFieldRow.outputEncode occurrences).length +
    (SourceOrderRawFields.encode (DomainSymbols.extract occurrences)).length ≤ _
  omega

end DomainSymbolExtraction

/-- Extract symbol fields and retain the entire occurrence wire in `3s+3`
finite-machine steps, measured in its actual bit/delimiter length. -/
def domainSymbolExtraction_outputsInTime (occurrences : List (ℕ × ℕ)) :
    TM2OutputsInTime DomainSymbolMachine.computer (DomainFieldRow.outputEncode occurrences)
      (some (DomainSymbolExtraction.finEncoding.encode (DomainSymbolExtraction.retain occurrences)))
      (3 * (DomainFieldRow.outputEncode occurrences).length + 3) := by
  rw [TM2OutputsInTime, DomainSymbolMachine.init_eq]
  simp only [Option.map_some]
  rw [DomainSymbolMachine.halt_eq]
  simpa [DomainSymbolExtraction.finEncoding, DomainSymbolExtraction.retain,
    LeanNPHardness.PairEncoding.finEncoding, DomainFieldRow.outputFinEncoding,
    SourceOrderRawFields.finEncoding] using DomainSymbolMachine.run_occurrences occurrences

noncomputable def domainSymbolExtractionComputableInPolyTime :
    @TM2ComputableInPolyTime (List (ℕ × ℕ)) DomainSymbolExtraction.Value
      DomainFieldRow.outputFinEncoding DomainSymbolExtraction.finEncoding
      DomainSymbolExtraction.retain where
  tm := DomainSymbolMachine.computer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl DomainSymbolMachine.Tagged
  time := 3 * Polynomial.X + 3
  outputsFun occurrences := by
    simpa [Equiv.refl, DomainFieldRow.outputFinEncoding,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_natCast, Polynomial.eval_X]
      using domainSymbolExtraction_outputsInTime occurrences

namespace CountedSymbolSections

abbrev Sections := DomainSymbolExtraction.Value × List (List ℕ)
abbrev Value := Sections × ℕ

def sectionsFinEncoding : FinEncoding Sections :=
  LeanNPHardness.PairEncoding.finEncoding DomainSymbolExtraction.finEncoding
    ScopeFieldSection.outputFinEncoding

def finEncoding : FinEncoding Value :=
  LeanNPHardness.PairEncoding.finEncoding sectionsFinEncoding finEncodingNatBool

/-- Keep both processed sections and the variable count; attach the symbol list. -/
def retain (sections : CountedSections.Value) : Value :=
  ((DomainSymbolExtraction.retain sections.1.1, sections.1.2), sections.2)

def ofRuntimeSystem (C : RuntimeSystem) : Value := retain (CountedSections.ofRuntimeSystem C)

/-- Removing the newly attached symbols recovers all original counted sections. -/
def original (sections : Value) : CountedSections.Value :=
  ((sections.1.1.1, sections.1.2), sections.2)

theorem original_retain (sections : CountedSections.Value) :
    original (retain sections) = sections := rfl

theorem toStructuralView_ofRuntimeSystem (C : RuntimeSystem) :
    CountedSections.toStructuralView (original (ofRuntimeSystem C)) =
      RuntimeStructuralView.ofRuntimeSystem C := rfl

theorem symbols_ofRuntimeSystem (C : RuntimeSystem) :
    (ofRuntimeSystem C).1.1.2 = C.domains.flatten :=
  DomainSymbols.extract_indexedDomainOccurrences C.domains

/-- The machine-produced symbols are an exact input to the checked rank contract. -/
theorem rank_symbols_eq_relabelValue (C : RuntimeSystem) (value : ℕ) :
    DomainSymbols.rank (ofRuntimeSystem C).1.1.2 value =
      C.toExplicitSystem.relabelValue value := by
  rw [symbols_ofRuntimeSystem, DomainSymbols.rank_flatten_eq_relabelValue]

/-- Including all scopes and the variable count, extraction at most doubles
the full counted-section wire length. -/
theorem retain_encode_length_le (sections : CountedSections.Value) :
    (finEncoding.encode (retain sections)).length ≤
      2 * (CountedSections.finEncoding.encode sections).length := by
  have h := DomainSymbolExtraction.retain_encode_length_le sections.1.1
  simp only [finEncoding, sectionsFinEncoding, retain, CountedSections.finEncoding,
    CountedSections.sectionsFinEncoding, LeanNPHardness.PairEncoding.finEncoding_encode_length]
  change (DomainSymbolExtraction.finEncoding.encode
      (DomainSymbolExtraction.retain sections.1.1)).length +
      (ScopeFieldSection.outputFinEncoding.encode sections.1.2).length +
      (finEncodingNatBool.encode sections.2).length ≤
    2 * ((DomainFieldRow.outputEncode sections.1.1).length +
      (ScopeFieldSection.outputFinEncoding.encode sections.1.2).length +
      (finEncodingNatBool.encode sections.2).length)
  omega

end CountedSymbolSections

/-- Extract the symbols while carrying the complete processed scope section. -/
noncomputable def symbolSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime CountedSections.Sections CountedSymbolSections.Sections
      CountedSections.sectionsFinEncoding CountedSymbolSections.sectionsFinEncoding
      (fun sections => (DomainSymbolExtraction.retain sections.1, sections.2)) :=
  LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    DomainFieldRow.outputFinEncoding DomainSymbolExtraction.finEncoding
    ScopeFieldSection.outputFinEncoding _ domainSymbolExtractionComputableInPolyTime

/-- Carry the saved variable count through the same checked extraction. -/
noncomputable def countedSymbolSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime CountedSections.Value CountedSymbolSections.Value
      CountedSections.finEncoding CountedSymbolSections.finEncoding CountedSymbolSections.retain :=
  LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    CountedSections.sectionsFinEncoding CountedSymbolSections.sectionsFinEncoding
    finEncodingNatBool _ symbolSectionsComputableInPolyTime

/-- From actual Boolean compiler input, construct the exact domain-symbol
list while preserving occurrences, scopes, and the original variable count.
The composition theorem includes all preprocessing and transfer costs. -/
noncomputable def runtimeCompilerSymbolSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem CountedSymbolSections.Value
      RuntimeCompilerInput.finEncoding CountedSymbolSections.finEncoding
      CountedSymbolSections.ofRuntimeSystem := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerCountedSectionsComputableInPolyTime countedSymbolSectionsComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa [Function.comp_def, CountedSymbolSections.ofRuntimeSystem] using composed.outputsFun C }

#print axioms DomainSymbolMachine.computer
#print axioms domainSymbolExtraction_outputsInTime
#print axioms domainSymbolExtractionComputableInPolyTime
#print axioms DomainSymbolExtraction.retain_encode_length_le
#print axioms CountedSymbolSections.toStructuralView_ofRuntimeSystem
#print axioms CountedSymbolSections.rank_symbols_eq_relabelValue
#print axioms CountedSymbolSections.retain_encode_length_le
#print axioms runtimeCompilerSymbolSectionsComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
