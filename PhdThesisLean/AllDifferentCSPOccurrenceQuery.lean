import PhdThesisLean.AllDifferentCSPRankLoop

/-!
# Stage a canonical-rank query from the next indexed occurrence

The checked input is the existing occurrence/symbol wire restricted to a
nonempty occurrence list. The machine removes its first record, constructs
that value's rank query, and retains the variable index, remaining records,
and complete symbol list. Every copy and order-restoration pass is charged.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace OccurrenceQuery

abbrev Input := (ℕ × ℕ) × DomainSymbolExtraction.Value
abbrev Retained := ℕ × DomainSymbolExtraction.Value
abbrev Output := DomainSymbolMembership.Input × Retained

def source (input : Input) : DomainSymbolExtraction.Value :=
  (input.1 :: input.2.1, input.2.2)

def inputEncode (input : Input) := DomainSymbolExtraction.finEncoding.encode (source input)

def inputDecode (wire : List (Sum (Option Bool) (Option Bool))) : Option Input := do
  let (occurrences, symbols) ← DomainSymbolExtraction.finEncoding.decode wire
  match occurrences with
  | [] => none
  | occurrence :: rest => some (occurrence, rest, symbols)

@[simp] theorem inputDecode_encode (input : Input) :
    inputDecode (inputEncode input) = some input := by
  rcases input with ⟨⟨index, value⟩, rest, symbols⟩
  simp [inputDecode, inputEncode, source, Encoding.decode_encode]

def inputFinEncoding : FinEncoding Input where
  Γ := Sum (Option Bool) (Option Bool)
  encode := inputEncode
  decode := inputDecode
  decode_encode := inputDecode_encode
  ΓFin := inferInstance

def retainedFinEncoding : FinEncoding Retained :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingNatBool DomainSymbolExtraction.finEncoding

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding DomainSymbolMembership.finEncoding retainedFinEncoding

def prepare (input : Input) : Output :=
  ((input.1.2, input.2.2), (input.1.1, input.2))

theorem input_length (input : Input) :
    (inputEncode input).length = (encodeNat input.1.1).length +
      (encodeNat input.1.2).length + (DomainFieldRow.outputEncode input.2.1).length +
      (SourceOrderRawFields.encode input.2.2).length + 6 := by
  simp [inputEncode, source, DomainSymbolExtraction.finEncoding,
    DomainFieldRow.outputFinEncoding, DomainFieldRow.outputEncode,
    DomainOccurrenceFieldBlock.outputEncode_eq_prefix, DomainOccurrenceFieldBlock.inputEncode,
    DomainOccurrenceFieldBlock.headerPrefix, SourceOrderRawFields.finEncoding,
    SourceOrderRawFields.encode, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]
  omega

theorem output_length (input : Input) :
    (outputFinEncoding.encode (prepare input)).length + 6 =
      (inputEncode input).length + (SourceOrderRawFields.encode input.2.2).length := by
  rw [input_length]
  simp [outputFinEncoding, retainedFinEncoding, prepare,
    DomainSymbolMembership.finEncoding, DomainSymbolExtraction.finEncoding,
    DomainFieldRow.outputFinEncoding, SourceOrderRawFields.finEncoding,
    finEncodingNatBool, encodingNatBool]
  omega

theorem output_length_le (input : Input) :
    (outputFinEncoding.encode (prepare input)).length ≤ 2 * (inputEncode input).length := by
  have h := output_length input
  have hi := input_length input
  omega

end OccurrenceQuery

namespace OccurrenceQueryMachine

abbrev Raw := Option Bool
abbrev Wire := Sum Raw Raw
abbrev Output := Sum (Sum Bool Raw) (Sum Bool (Sum Raw Raw))

inductive Phase
  | start | row | tag | index | value | rest
  deriving DecidableEq, Fintype

def advance : Phase → Phase
  | .start => .row | .row => .tag | .tag => .index
  | .index => .value | .value => .rest | .rest => .rest

inductive Block
  | target | querySymbols | index | rest | symbols
  deriving DecidableEq, Fintype

inductive Stack
  | input | saved (block : Block) | output
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Wire | .saved _ => Raw | .output => Output

inductive Label
  | scan | emit (block : Block)
  deriving DecidableEq, Fintype

abbrev State := Phase × Option Wire

def initialState : State := (.start, none)
private def observe (state : State) (cell : Option Wire) : State :=
  (if cell = some (.inl none) then advance state.1 else state.1, cell)
private def remember (state : State) (cell : Option Raw) : State :=
  (state.1, cell.map Sum.inl)
private def raw (state : State) : Raw := (state.2.bind Sum.getLeft?).getD none
private def symbol (state : State) : Raw := (state.2.bind Sum.getRight?).getD none
private def clear (state : State) : State := (state.1, none)

def tag : Block → Raw → Output
  | .target, bit => .inl (.inl (bit.getD false))
  | .querySymbols, cell => .inl (.inr cell)
  | .index, bit => .inr (.inl (bit.getD false))
  | .rest, cell => .inr (.inr (.inl cell))
  | .symbols, cell => .inr (.inr (.inr cell))

def next : Block → Option Label
  | .symbols => some (.emit .rest) | .rest => some (.emit .index)
  | .index => some (.emit .querySymbols) | .querySymbols => some (.emit .target)
  | .target => none

def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input observe <| .branch (fun s => s.2.isSome)
      (.branch (fun s => (s.2.bind Sum.getRight?).isSome)
        (.push (.saved .querySymbols) symbol <| .push (.saved .symbols) symbol <|
          .load clear <| .goto fun _ => .scan)
        (.branch (fun s => decide (s.1 = .rest))
          (.push (.saved .rest) raw <| .load clear <| .goto fun _ => .scan)
          (.branch (fun s => decide (s.1 = .index) && (raw s).isSome)
            (.push (.saved .index) raw <| .load clear <| .goto fun _ => .scan)
            (.branch (fun s => decide (s.1 = .value) && (raw s).isSome)
              (.push (.saved .target) raw <| .load clear <| .goto fun _ => .scan)
              (.load clear <| .goto fun _ => .scan)))))
      (.load (fun _ => initialState) <| .goto fun _ => .emit .symbols)
  | .emit block => .pop (.saved block) remember <| .branch (fun s => s.2.isSome)
      (.push .output (fun s => tag block (raw s)) <| .goto fun _ => .emit block)
      (.load (fun _ => initialState) <|
        match next block with
        | some label => .goto fun _ => label
        | none => .halt)

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

private def stackContents (input : List Wire) (target querySymbols index rest symbols : List Raw)
    (output : List Output) : (k : Stack) → List (Alphabet k)
  | .input => input | .saved .target => target | .saved .querySymbols => querySymbols
  | .saved .index => index | .saved .rest => rest | .saved .symbols => symbols
  | .output => output

private def cfg (label : Option Label) (state : State) (input : List Wire)
    (target querySymbols index rest symbols : List Raw) (output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input target querySymbols index rest symbols output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "occurrence_query_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, next,
    initialState, observe, remember, raw, symbol, clear, advance, Function.update]
   <;> first | rfl | (funext k; cases k with
     | input => rfl | saved block => cases block <;> rfl | output => rfl)))

private def index_bits_run (bits : List Bool) (suffix : List Wire)
    (target querySymbols index rest symbols : List Raw) :
    Run (cfg (some .scan) (.index, none) (bits.map (fun b => .inl (some b)) ++ suffix)
        target querySymbols index rest symbols [])
      (cfg (some .scan) (.index, none) suffix target querySymbols ((bits.map some).reverse ++ index) rest symbols []) bits.length := by
  induction bits generalizing index with
  | nil => exact EvalsToInTime.refl _ _
  | cons cell bits ih =>
      have h : Run (cfg (some .scan) (.index, none)
          ((cell :: bits).map (fun b => .inl (some b)) ++ suffix) target querySymbols index rest symbols [])
          (cfg (some .scan) (.index, none) (bits.map (fun b => .inl (some b)) ++ suffix)
            target querySymbols (some cell :: index) rest symbols []) 1 := one (by occurrence_query_step)
      simpa [List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (some cell :: index))

private def value_bits_run (bits : List Bool) (suffix : List Wire)
    (target querySymbols index rest symbols : List Raw) :
    Run (cfg (some .scan) (.value, none) (bits.map (fun b => .inl (some b)) ++ suffix)
        target querySymbols index rest symbols [])
      (cfg (some .scan) (.value, none) suffix ((bits.map some).reverse ++ target) querySymbols index rest symbols []) bits.length := by
  induction bits generalizing target with
  | nil => exact EvalsToInTime.refl _ _
  | cons cell bits ih =>
      have h : Run (cfg (some .scan) (.value, none)
          ((cell :: bits).map (fun b => .inl (some b)) ++ suffix) target querySymbols index rest symbols [])
          (cfg (some .scan) (.value, none) (bits.map (fun b => .inl (some b)) ++ suffix)
            (some cell :: target) querySymbols index rest symbols []) 1 := one (by occurrence_query_step)
      simpa [List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (some cell :: target))

private def rest_cells_run (cells : List Raw) (suffix : List Wire)
    (target querySymbols index rest symbols : List Raw) :
    Run (cfg (some .scan) (.rest, none) (cells.map (Sum.inl) ++ suffix)
        target querySymbols index rest symbols [])
      (cfg (some .scan) (.rest, none) suffix target querySymbols index (cells.reverse ++ rest) symbols []) cells.length := by
  induction cells generalizing rest with
  | nil => exact EvalsToInTime.refl _ _
  | cons cell cells ih =>
      have h : Run (cfg (some .scan) (.rest, none)
          ((cell :: cells).map (Sum.inl) ++ suffix) target querySymbols index rest symbols [])
          (cfg (some .scan) (.rest, none) (cells.map (Sum.inl) ++ suffix)
            target querySymbols index (cell :: rest) symbols []) 1 := one (by cases cell <;> occurrence_query_step)
      simpa [List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (cell :: rest))

private def symbol_cells_run (cells : List Raw) (suffix : List Wire) (phase : Phase)
    (target querySymbols index rest symbols : List Raw) :
    Run (cfg (some .scan) (phase, none) (cells.map (Sum.inr) ++ suffix)
        target querySymbols index rest symbols [])
      (cfg (some .scan) (phase, none) suffix target (cells.reverse ++ querySymbols) index rest (cells.reverse ++ symbols) []) cells.length := by
  induction cells generalizing querySymbols symbols with
  | nil => exact EvalsToInTime.refl _ _
  | cons cell cells ih =>
      have h : Run (cfg (some .scan) (phase, none)
          ((cell :: cells).map (Sum.inr) ++ suffix) target querySymbols index rest symbols [])
          (cfg (some .scan) (phase, none) (cells.map (Sum.inr) ++ suffix)
            target (cell :: querySymbols) index rest (cell :: symbols) []) 1 := one (by cases phase <;> occurrence_query_step)
      simpa [List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (cell :: querySymbols) (cell :: symbols))

private def emit_target (target querySymbols index rest symbols : List Raw)
    (output : List Output) (state : State) :
    Run (cfg (some (.emit .target)) state [] target querySymbols index rest symbols output)
      (cfg (next .target) initialState [] [] querySymbols index rest symbols
        (target.reverse.map (tag .target) ++ output)) (target.length + 1) := by
  induction target generalizing output state with
  | nil => exact one (by occurrence_query_step)
  | cons cell targetTail ih =>
      have h : Run (cfg (some (.emit .target)) state [] (cell :: targetTail) querySymbols index rest symbols output)
          (cfg (some (.emit .target)) (state.1, some (.inl cell)) [] (targetTail) querySymbols index rest symbols
            (tag .target cell :: output)) 1 := one (by occurrence_query_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (tag .target cell :: output) (state.1, some (.inl cell)))

private def emit_querySymbols (target querySymbols index rest symbols : List Raw)
    (output : List Output) (state : State) :
    Run (cfg (some (.emit .querySymbols)) state [] target querySymbols index rest symbols output)
      (cfg (next .querySymbols) initialState [] target [] index rest symbols
        (querySymbols.reverse.map (tag .querySymbols) ++ output)) (querySymbols.length + 1) := by
  induction querySymbols generalizing output state with
  | nil => exact one (by occurrence_query_step)
  | cons cell querySymbolsTail ih =>
      have h : Run (cfg (some (.emit .querySymbols)) state [] target (cell :: querySymbolsTail) index rest symbols output)
          (cfg (some (.emit .querySymbols)) (state.1, some (.inl cell)) [] target (querySymbolsTail) index rest symbols
            (tag .querySymbols cell :: output)) 1 := one (by occurrence_query_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (tag .querySymbols cell :: output) (state.1, some (.inl cell)))

private def emit_index (target querySymbols index rest symbols : List Raw)
    (output : List Output) (state : State) :
    Run (cfg (some (.emit .index)) state [] target querySymbols index rest symbols output)
      (cfg (next .index) initialState [] target querySymbols [] rest symbols
        (index.reverse.map (tag .index) ++ output)) (index.length + 1) := by
  induction index generalizing output state with
  | nil => exact one (by occurrence_query_step)
  | cons cell indexTail ih =>
      have h : Run (cfg (some (.emit .index)) state [] target querySymbols (cell :: indexTail) rest symbols output)
          (cfg (some (.emit .index)) (state.1, some (.inl cell)) [] target querySymbols (indexTail) rest symbols
            (tag .index cell :: output)) 1 := one (by occurrence_query_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (tag .index cell :: output) (state.1, some (.inl cell)))

private def emit_rest (target querySymbols index rest symbols : List Raw)
    (output : List Output) (state : State) :
    Run (cfg (some (.emit .rest)) state [] target querySymbols index rest symbols output)
      (cfg (next .rest) initialState [] target querySymbols index [] symbols
        (rest.reverse.map (tag .rest) ++ output)) (rest.length + 1) := by
  induction rest generalizing output state with
  | nil => exact one (by occurrence_query_step)
  | cons cell restTail ih =>
      have h : Run (cfg (some (.emit .rest)) state [] target querySymbols index (cell :: restTail) symbols output)
          (cfg (some (.emit .rest)) (state.1, some (.inl cell)) [] target querySymbols index (restTail) symbols
            (tag .rest cell :: output)) 1 := one (by occurrence_query_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (tag .rest cell :: output) (state.1, some (.inl cell)))

private def emit_symbols (target querySymbols index rest symbols : List Raw)
    (output : List Output) (state : State) :
    Run (cfg (some (.emit .symbols)) state [] target querySymbols index rest symbols output)
      (cfg (next .symbols) initialState [] target querySymbols index rest []
        (symbols.reverse.map (tag .symbols) ++ output)) (symbols.length + 1) := by
  induction symbols generalizing output state with
  | nil => exact one (by occurrence_query_step)
  | cons cell symbolsTail ih =>
      have h : Run (cfg (some (.emit .symbols)) state [] target querySymbols index rest (cell :: symbolsTail) output)
          (cfg (some (.emit .symbols)) (state.1, some (.inl cell)) [] target querySymbols index rest (symbolsTail)
            (tag .symbols cell :: output)) 1 := one (by occurrence_query_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (tag .symbols cell :: output) (state.1, some (.inl cell)))

private def header_run (suffix : List Wire) :
    Run (cfg (some .scan) initialState
        ([.inl none, .inl (some true), .inl (some true), .inl none, .inl none] ++ suffix)
        [] [] [] [] [] [])
      (cfg (some .scan) (.index, none) suffix [] [] [] [] [] []) 5 := by
  have h0 : Run (cfg (some .scan) (.start, none) ([.inl none, .inl (some true), .inl (some true), .inl none, .inl none] ++ suffix) [] [] [] [] [] [])
      (cfg (some .scan) (.row, none) ([.inl (some true), .inl (some true), .inl none, .inl none] ++ suffix) [] [] [] [] [] []) 1 :=
    one (by occurrence_query_step)
  have h1 : Run (cfg (some .scan) (.row, none) ([.inl (some true), .inl (some true), .inl none, .inl none] ++ suffix) [] [] [] [] [] [])
      (cfg (some .scan) (.row, none) ([.inl (some true), .inl none, .inl none] ++ suffix) [] [] [] [] [] []) 1 :=
    one (by occurrence_query_step)
  have h2 : Run (cfg (some .scan) (.row, none) ([.inl (some true), .inl none, .inl none] ++ suffix) [] [] [] [] [] [])
      (cfg (some .scan) (.row, none) ([.inl none, .inl none] ++ suffix) [] [] [] [] [] []) 1 :=
    one (by occurrence_query_step)
  have h3 : Run (cfg (some .scan) (.row, none) ([.inl none, .inl none] ++ suffix) [] [] [] [] [] [])
      (cfg (some .scan) (.tag, none) ([.inl none] ++ suffix) [] [] [] [] [] []) 1 :=
    one (by occurrence_query_step)
  have h4 : Run (cfg (some .scan) (.tag, none) ([.inl none] ++ suffix) [] [] [] [] [] [])
      (cfg (some .scan) (.index, none) (suffix) [] [] [] [] [] []) 1 :=
    one (by occurrence_query_step)
  exact seq (seq (seq (seq h0 h1) h2) h3) h4

private def remaining_run (occurrences : List (ℕ × ℕ)) (suffix : List Wire)
    (target index : List Raw) :
    Run (cfg (some .scan) (.value, none)
        ((DomainFieldRow.outputEncode occurrences).map Sum.inl ++ suffix)
        target [] index [] [] [])
      (cfg (some .scan) (if occurrences.isEmpty then .value else .rest, none)
        suffix target [] index (DomainFieldRow.outputEncode occurrences).reverse [] [])
      (DomainFieldRow.outputEncode occurrences).length := by
  cases occurrences with
  | nil => exact EvalsToInTime.refl _ _
  | cons occurrence occurrences =>
      let tail := [some true, some true, none, none] ++ (encodeNat occurrence.1).map some ++
        none :: (encodeNat occurrence.2).map some ++
        DomainFieldRow.outputEncode occurrences
      have wire : DomainFieldRow.outputEncode (occurrence :: occurrences) = none :: tail := by
        simp [DomainFieldRow.outputEncode, DomainOccurrenceFieldBlock.outputEncode_eq_prefix,
          DomainOccurrenceFieldBlock.headerPrefix, DomainOccurrenceFieldBlock.inputEncode,
          SourceOrderRawFields.encode, tail, List.append_assoc]
      have h : Run (cfg (some .scan) (.value, none)
          (.inl none :: tail.map Sum.inl ++ suffix) target [] index [] [] [])
          (cfg (some .scan) (.rest, none) (tail.map Sum.inl ++ suffix)
            target [] index [none] [] []) 1 := one (by occurrence_query_step)
      have ht := rest_cells_run tail suffix target [] index [none] []
      simpa [wire, List.reverse_cons, List.append_assoc, Nat.add_comm] using seq h ht

private def scan_all (index value : ℕ) (occurrences : List (ℕ × ℕ)) (symbols : List ℕ) :
    Run (cfg (some .scan) initialState
        (OccurrenceQuery.inputEncode ((index, value), occurrences, symbols)) [] [] [] [] [] [])
      (cfg (some (.emit .symbols)) initialState []
        ((encodeNat value).map some).reverse (SourceOrderRawFields.encode symbols).reverse
        ((encodeNat index).map some).reverse (DomainFieldRow.outputEncode occurrences).reverse
        (SourceOrderRawFields.encode symbols).reverse [])
      ((OccurrenceQuery.inputEncode ((index, value), occurrences, symbols)).length + 1) := by
  let i := encodeNat index
  let v := encodeNat value
  let r := DomainFieldRow.outputEncode occurrences
  let s := SourceOrderRawFields.encode symbols
  let suffix := r.map Sum.inl ++ s.map Sum.inr
  have hh := header_run (i.map (fun b => .inl (some b)) ++
    (.inl none :: v.map (fun b => .inl (some b)) ++ suffix))
  have hi := index_bits_run i (.inl none :: v.map (fun b => .inl (some b)) ++ suffix)
    [] [] [] [] []
  simp only [List.append_nil] at hi
  have hd : Run (cfg (some .scan) (.index, none)
      (.inl none :: v.map (fun b => .inl (some b)) ++ suffix) [] [] (i.map some).reverse [] [] [])
      (cfg (some .scan) (.value, none) (v.map (fun b => .inl (some b)) ++ suffix)
        [] [] (i.map some).reverse [] [] []) 1 := one (by occurrence_query_step)
  have hv := value_bits_run v suffix [] [] (i.map some).reverse [] []
  simp only [List.append_nil] at hv
  have hr := remaining_run occurrences (s.map Sum.inr) (v.map some).reverse (i.map some).reverse
  let phase : Phase := if occurrences.isEmpty then .value else .rest
  have hs := symbol_cells_run s [] phase (v.map some).reverse [] (i.map some).reverse r.reverse []
  simp only [List.append_nil] at hs
  have he : Run (cfg (some .scan) (phase, none) []
      (v.map some).reverse s.reverse (i.map some).reverse r.reverse s.reverse [])
      (cfg (some (.emit .symbols)) initialState []
        (v.map some).reverse s.reverse (i.map some).reverse r.reverse s.reverse []) 1 :=
    one (by occurrence_query_step)
  have result := seq (seq (seq (seq (seq (seq hh hi) hd) hv) hr) hs) he
  convert result using 1
  · simp [OccurrenceQuery.inputEncode, OccurrenceQuery.source, DomainSymbolExtraction.finEncoding,
      LeanNPHardness.PairEncoding.finEncoding, DomainFieldRow.outputFinEncoding,
      DomainFieldRow.outputEncode, DomainOccurrenceFieldBlock.outputEncode_eq_prefix,
      DomainOccurrenceFieldBlock.inputEncode, DomainOccurrenceFieldBlock.headerPrefix,
      SourceOrderRawFields.finEncoding, SourceOrderRawFields.encode,
      i, v, r, s, suffix, List.map_append, List.map_map, Function.comp_def, List.append_assoc]
  · rw [OccurrenceQuery.input_length]
    dsimp [i, v, r, s]
    omega

private def emit_all (target index : List Bool) (rest symbols : List Raw) :
    Run (cfg (some (.emit .symbols)) initialState []
        (target.map some).reverse symbols.reverse (index.map some).reverse rest.reverse symbols.reverse [])
      (cfg none initialState [] [] [] [] [] []
        ((target.map some).map (tag .target) ++ symbols.map (tag .querySymbols) ++
          (index.map some).map (tag .index) ++ rest.map (tag .rest) ++ symbols.map (tag .symbols)))
      (target.length + index.length + rest.length + 2 * symbols.length + 5) := by
  have hs := emit_symbols (target.map some).reverse symbols.reverse
    (index.map some).reverse rest.reverse symbols.reverse [] initialState
  have hr := emit_rest (target.map some).reverse symbols.reverse
    (index.map some).reverse rest.reverse [] (symbols.map (tag .symbols)) initialState
  have hi := emit_index (target.map some).reverse symbols.reverse
    (index.map some).reverse [] []
    (rest.map (tag .rest) ++ symbols.map (tag .symbols)) initialState
  have hq := emit_querySymbols (target.map some).reverse symbols.reverse [] [] []
    ((index.map some).map (tag .index) ++ rest.map (tag .rest) ++ symbols.map (tag .symbols)) initialState
  have ht := emit_target (target.map some).reverse [] [] [] []
    (symbols.map (tag .querySymbols) ++ (index.map some).map (tag .index) ++
      rest.map (tag .rest) ++ symbols.map (tag .symbols)) initialState
  simp only [List.reverse_reverse, List.length_reverse, List.length_map, List.append_nil,
    next, List.append_assoc] at hs hr hi hq ht ⊢
  convert seq (seq (seq (seq hs hr) hi) hq) ht using 1
  omega

private def run (input : OccurrenceQuery.Input) :
    Run (cfg (some .scan) initialState (OccurrenceQuery.inputEncode input) [] [] [] [] [] [])
      (cfg none initialState [] [] [] [] [] [] (OccurrenceQuery.outputFinEncoding.encode
        (OccurrenceQuery.prepare input)))
      (3 * (OccurrenceQuery.inputEncode input).length + 6) := by
  rcases input with ⟨⟨index, value⟩, occurrences, symbols⟩
  have hs := scan_all index value occurrences symbols
  have he := emit_all (encodeNat value) (encodeNat index)
    (DomainFieldRow.outputEncode occurrences) (SourceOrderRawFields.encode symbols)
  apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (by
    convert seq hs he using 1
    simp [OccurrenceQuery.outputFinEncoding, OccurrenceQuery.retainedFinEncoding,
      OccurrenceQuery.prepare, DomainSymbolMembership.finEncoding, DomainSymbolExtraction.finEncoding,
      LeanNPHardness.PairEncoding.finEncoding, DomainFieldRow.outputFinEncoding,
      finEncodingNatBool, encodingNatBool, SourceOrderRawFields.finEncoding,
      tag, List.map_map, Function.comp_def, List.append_assoc]
    rfl)
  rw [OccurrenceQuery.input_length]
  dsimp only
  omega

private theorem init_eq (input : List Wire) :
    initList computer input = cfg (some .scan) initialState input [] [] [] [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k with
  | input => rfl | saved block => cases block <;> rfl | output => rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none initialState [] [] [] [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k with
  | input => rfl | saved block => cases block <;> rfl | output => rfl

end OccurrenceQueryMachine

/-- Construct the rank query and exact retained source in `3s+6` finite-machine
steps for the full occurrence/symbol input length, clearing all work stacks. -/
def occurrenceQuery_outputsInTime (input : OccurrenceQuery.Input) :
    TM2OutputsInTime OccurrenceQueryMachine.computer (OccurrenceQuery.inputFinEncoding.encode input)
      (some (OccurrenceQuery.outputFinEncoding.encode (OccurrenceQuery.prepare input)))
      (3 * (OccurrenceQuery.inputFinEncoding.encode input).length + 6) := by
  rw [TM2OutputsInTime, OccurrenceQueryMachine.init_eq]
  simp only [Option.map_some]
  rw [OccurrenceQueryMachine.halt_eq]
  exact OccurrenceQueryMachine.run input

noncomputable def occurrenceQueryComputableInPolyTime :
    @TM2ComputableInPolyTime OccurrenceQuery.Input OccurrenceQuery.Output
      OccurrenceQuery.inputFinEncoding OccurrenceQuery.outputFinEncoding OccurrenceQuery.prepare where
  tm := OccurrenceQueryMachine.computer
  inputAlphabet := Equiv.refl OccurrenceQueryMachine.Wire
  outputAlphabet := Equiv.refl OccurrenceQueryMachine.Output
  time := 3 * Polynomial.X + 6
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X] using occurrenceQuery_outputsInTime input

#print axioms OccurrenceQuery.inputDecode_encode
#print axioms OccurrenceQuery.output_length
#print axioms occurrenceQuery_outputsInTime
#print axioms occurrenceQueryComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
