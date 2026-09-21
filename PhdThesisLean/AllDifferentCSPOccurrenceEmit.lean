import PhdThesisLean.AllDifferentCSPOccurrenceRank

/-!
# Emit a binary relabelled occurrence while retaining the next source

The finite machine consumes the computed unary rank, counts it with the
checked canonical binary-successor operation, and emits the exact tagged
occurrence record. The saved index and complete remaining source survive.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace OccurrenceEmit

abbrev Output := (ℕ × ℕ) × DomainSymbolExtraction.Value

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding DomainOccurrenceFieldBlock.outputFinEncoding
    DomainSymbolExtraction.finEncoding

def emit (input : OccurrenceQuery.Ranked) : Output :=
  ((input.2.1, input.1), input.2.2)

theorem input_length (input : OccurrenceQuery.Ranked) :
    (OccurrenceQuery.rankedFinEncoding.encode input).length =
      input.1 + (encodeNat input.2.1).length +
        (DomainSymbolExtraction.finEncoding.encode input.2.2).length := by
  simp [OccurrenceQuery.rankedFinEncoding, OccurrenceQuery.retainedFinEncoding,
    unaryFinEncodingNat, unaryEncodeNat_eq_replicate_true,
    finEncodingNatBool, encodingNatBool, Nat.add_assoc]

theorem output_length (input : OccurrenceQuery.Ranked) :
    (outputFinEncoding.encode (emit input)).length =
      (encodeNat input.2.1).length + (encodeNat input.1).length +
        (DomainSymbolExtraction.finEncoding.encode input.2.2).length + 6 := by
  simp [outputFinEncoding, emit, DomainOccurrenceFieldBlock.outputFinEncoding,
    DomainOccurrenceFieldBlock.outputEncode_eq_prefix, DomainOccurrenceFieldBlock.headerPrefix,
    DomainOccurrenceFieldBlock.inputEncode, SourceOrderRawFields.encode]
  omega

/-- Binary conversion can only shorten the tally; the six new cells are the
record's exact length, tag, and field delimiters. -/
theorem output_length_le (input : OccurrenceQuery.Ranked) :
    (outputFinEncoding.encode (emit input)).length ≤
      (OccurrenceQuery.rankedFinEncoding.encode input).length + 6 := by
  rw [output_length, input_length]
  have h := BinaryNatLists.encodeNat_length_le input.1
  omega

end OccurrenceEmit

namespace OccurrenceEmitMachine

abbrev Raw := Option Bool
abbrev Source := Sum Raw Raw
abbrev Input := Sum Bool (Sum Bool Source)
abbrev Output := Sum Raw Source
abbrev State := Option Input

inductive Stack
  | input | count | work | index | source | output
  deriving DecidableEq, Fintype

inductive Label
  | tally | carry | restore | index | source | emitSource | reverseRank | emitRank | emitIndex
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Input
  | .count | .work | .index => Bool
  | .source => Source
  | .output => Output

private def popped (_ : State) (cell : Option Input) : State := cell
private def poppedBit (_ : State) (cell : Option Bool) : State := cell.map Sum.inl
private def poppedSource (_ : State) (cell : Option Source) : State :=
  cell.map (fun c => .inr (.inr c))
private def present (state : State) : Bool := state.isSome
private def isRank : State → Bool | some (.inl _) => true | _ => false
private def isIndex : State → Bool | some (.inr (.inl _)) => true | _ => false
private def held : State → Input | some cell => cell | none => .inl false
private def bit : State → Bool
  | some (.inl b) | some (.inr (.inl b)) => b | _ => false
private def sourceCell : State → Source
  | some (.inr (.inr cell)) => cell | _ => .inl none

def program : Label → TM2.Stmt Alphabet Label State
  | .tally => .pop .input popped <| .branch isRank
      (.goto fun _ => .carry)
      (.branch present (.push .input held <| .goto fun _ => .index)
        (.goto fun _ => .index))
  | .carry => .pop .count poppedBit <| .branch present
      (.branch bit
        (.push .work (fun _ => false) <| .goto fun _ => .carry)
        (.push .count (fun _ => true) <| .goto fun _ => .restore))
      (.push .count (fun _ => true) <| .goto fun _ => .restore)
  | .restore => .pop .work poppedBit <| .branch present
      (.push .count bit <| .goto fun _ => .restore)
      (.goto fun _ => .tally)
  | .index => .pop .input popped <| .branch isIndex
      (.push .index bit <| .goto fun _ => .index)
      (.branch present (.push .input held <| .goto fun _ => .source)
        (.goto fun _ => .source))
  | .source => .pop .input popped <| .branch present
      (.push .source sourceCell <| .goto fun _ => .source)
      (.goto fun _ => .emitSource)
  | .emitSource => .pop .source poppedSource <| .branch present
      (.push .output (fun s => .inr (sourceCell s)) <| .goto fun _ => .emitSource)
      (.goto fun _ => .reverseRank)
  | .reverseRank => .pop .count poppedBit <| .branch present
      (.push .work bit <| .goto fun _ => .reverseRank)
      (.goto fun _ => .emitRank)
  | .emitRank => .pop .work poppedBit <| .branch present
      (.push .output (fun s => .inl (some (bit s))) <| .goto fun _ => .emitRank)
      (.push .output (fun _ => .inl none) <| .goto fun _ => .emitIndex)
  | .emitIndex => .pop .index poppedBit <| .branch present
      (.push .output (fun s => .inl (some (bit s))) <| .goto fun _ => .emitIndex)
      (.push .output (fun _ => .inl none) <|
        .push .output (fun _ => .inl none) <|
        .push .output (fun _ => .inl (some true)) <|
        .push .output (fun _ => .inl (some true)) <|
        .push .output (fun _ => .inl none) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .tally
  σ := State
  initialState := none
  Γk₀Fin := show Fintype Input from inferInstance
  m := program

private def stackContents (input : List Input) (count work index : List Bool)
    (source : List Source) (output : List Output) : (k : Stack) → List (Alphabet k)
  | .input => input | .count => count | .work => work | .index => index
  | .source => source | .output => output

private def cfg (label : Option Label) (state : State) (input : List Input)
    (count work index : List Bool) (source : List Source) (output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input count work index source output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) :=
  EvalsToInTime computer.step a (some b) time

private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1
    evals_in_steps := by simpa [Function.iterate_one] using h
    steps_le_m := le_rfl }

private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

private def mono {a b : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (hle : m ≤ n) : Run a b n :=
  { steps := h.steps
    evals_in_steps := h.evals_in_steps
    steps_le_m := h.steps_le_m.trans hle }

local macro "occurrence_emit_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, popped,
    poppedBit, poppedSource, present, isRank, isIndex, held, bit, sourceCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def restore_run (work count : List Bool) (input : List Input) (state : State) :
    Run (cfg (some .restore) state input count work [] [] [])
      (cfg (some .tally) none input (work.reverse ++ count) [] [] [] [])
      (work.length + 1) := by
  induction work generalizing count state with
  | nil => exact one (by occurrence_emit_step)
  | cons b work ih =>
      have h : Run (cfg (some .restore) state input count (b :: work) [] [] [])
          (cfg (some .restore) (some (.inl b)) input (b :: count) work [] [] []) 1 :=
        one (by cases b <;> occurrence_emit_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (b :: count) (some (.inl b)))

private def carry_run (bits acc : List Bool) (input : List Input) (state : State) :
    Run (cfg (some .carry) state input bits acc [] [] [])
      (cfg (some .tally) none input (acc.reverse ++ binarySuccBits bits) [] [] [] [])
      (2 * bits.length + acc.length + 2) := by
  induction bits generalizing acc state with
  | nil =>
      have h : Run (cfg (some .carry) state input [] acc [] [] [])
          (cfg (some .restore) none input [true] acc [] [] []) 1 :=
        one (by occurrence_emit_step)
      simpa [binarySuccBits, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (restore_run acc [true] input none)
  | cons b bits ih =>
      cases b with
      | false =>
          have h : Run (cfg (some .carry) state input (false :: bits) acc [] [] [])
              (cfg (some .restore) (some (.inl false)) input (true :: bits) acc [] [] []) 1 :=
            one (by occurrence_emit_step)
          apply mono (by
            simpa [binarySuccBits] using
              seq h (restore_run acc (true :: bits) input (some (.inl false))))
          simp only [List.length_cons]
          omega
      | true =>
          have h : Run (cfg (some .carry) state input (true :: bits) acc [] [] [])
              (cfg (some .carry) (some (.inl true)) input bits (false :: acc) [] [] []) 1 :=
            one (by occurrence_emit_step)
          apply mono (by
            simpa only [binarySuccBits, List.reverse_cons, List.singleton_append,
              List.append_assoc] using seq h (ih (false :: acc) (some (.inl true))))
          simp only [List.length_cons]
          omega

private def tallyTime : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, current => 1 + (2 * (encodeNat current).length + 2) + tallyTime n (current + 1)

private def tally_run (n current : ℕ) (rest : List (Sum Bool Source)) (state : State) :
    Run (cfg (some .tally) state
        (List.replicate n (.inl true) ++ rest.map Sum.inr) (encodeNat current) [] [] [] [])
      (cfg (some .index) ((rest.map Sum.inr).head?) (rest.map Sum.inr)
        (encodeNat (current + n)) [] [] [] []) (tallyTime n current) := by
  induction n generalizing current state with
  | zero => cases rest <;> exact one (by occurrence_emit_step)
  | succ n ih =>
      have h : Run
          (cfg (some .tally) state (List.replicate (n + 1) (.inl true) ++ rest.map Sum.inr)
            (encodeNat current) [] [] [] [])
          (cfg (some .carry) (some (.inl true))
            (List.replicate n (.inl true) ++ rest.map Sum.inr) (encodeNat current) [] [] [] []) 1 :=
        one (by simp only [List.replicate_succ]; occurrence_emit_step)
      have hc := carry_run (encodeNat current) []
        (List.replicate n (.inl true) ++ rest.map Sum.inr) (some (.inl true))
      simp only [List.reverse_nil, List.nil_append, binarySuccBits_encodeNat, List.length_nil,
        Nat.add_zero] at hc
      simpa [tallyTime, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq (seq h hc) (ih (current + 1) none)

private theorem tallyTime_le (n current : ℕ) :
    tallyTime n current ≤ 4 * n * (current + n + 1) + 1 := by
  induction n generalizing current with
  | zero => simp [tallyTime]
  | succ n ih =>
      have h := ih (current + 1)
      have hb := BinaryNatLists.encodeNat_length_le current
      simp only [tallyTime]
      nlinarith

private def index_run (bits saved count : List Bool) (source : List Source) (state : State) :
    Run (cfg (some .index) state
        (bits.map (fun b => .inr (.inl b)) ++ source.map (fun c => .inr (.inr c)))
        count [] saved [] [])
      (cfg (some .source) ((source.map (fun c => .inr (.inr c))).head?)
        (source.map (fun c => .inr (.inr c))) count [] (bits.reverse ++ saved) [] [])
      (bits.length + 1) := by
  induction bits generalizing saved state with
  | nil => cases source <;> exact one (by occurrence_emit_step)
  | cons b bits ih =>
      have h : Run (cfg (some .index) state
          ((b :: bits).map (fun b => .inr (.inl b)) ++ source.map (fun c => .inr (.inr c)))
          count [] saved [] [])
          (cfg (some .index) (some (.inr (.inl b)))
            (bits.map (fun b => .inr (.inl b)) ++ source.map (fun c => .inr (.inr c)))
            count [] (b :: saved) [] []) 1 := one (by occurrence_emit_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (b :: saved) (some (.inr (.inl b))))

private def source_run (source saved : List Source) (count index : List Bool) (state : State) :
    Run (cfg (some .source) state (source.map (fun c => .inr (.inr c))) count [] index saved [])
      (cfg (some .emitSource) none [] count [] index (source.reverse ++ saved) [])
      (source.length + 1) := by
  induction source generalizing saved state with
  | nil => exact one (by occurrence_emit_step)
  | cons cell source ih =>
      have h : Run (cfg (some .source) state
          ((cell :: source).map (fun c => .inr (.inr c))) count [] index saved [])
          (cfg (some .source) (some (.inr (.inr cell)))
            (source.map (fun c => .inr (.inr c))) count [] index (cell :: saved) []) 1 :=
        one (by occurrence_emit_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (cell :: saved) (some (.inr (.inr cell))))

private def emitSource_run (source : List Source) (count index : List Bool)
    (output : List Output) (state : State) :
    Run (cfg (some .emitSource) state [] count [] index source output)
      (cfg (some .reverseRank) none [] count [] index [] (source.reverse.map Sum.inr ++ output))
      (source.length + 1) := by
  induction source generalizing output state with
  | nil => exact one (by occurrence_emit_step)
  | cons cell source ih =>
      have h : Run (cfg (some .emitSource) state [] count [] index (cell :: source) output)
          (cfg (some .emitSource) (some (.inr (.inr cell))) [] count [] index source
            (.inr cell :: output)) 1 := one (by occurrence_emit_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (.inr cell :: output) (some (.inr (.inr cell))))

private def reverseRank_run (count work index : List Bool) (output : List Output) (state : State) :
    Run (cfg (some .reverseRank) state [] count work index [] output)
      (cfg (some .emitRank) none [] [] (count.reverse ++ work) index [] output)
      (count.length + 1) := by
  induction count generalizing work state with
  | nil => exact one (by occurrence_emit_step)
  | cons b count ih =>
      have h : Run (cfg (some .reverseRank) state [] (b :: count) work index [] output)
          (cfg (some .reverseRank) (some (.inl b)) [] count (b :: work) index [] output) 1 :=
        one (by occurrence_emit_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (b :: work) (some (.inl b)))

private def emitRank_run (work index : List Bool) (output : List Output) (state : State) :
    Run (cfg (some .emitRank) state [] [] work index [] output)
      (cfg (some .emitIndex) none [] [] [] index []
        (.inl none :: work.reverse.map (fun b => .inl (some b)) ++ output))
      (work.length + 1) := by
  induction work generalizing output state with
  | nil => exact one (by occurrence_emit_step)
  | cons b work ih =>
      have h : Run (cfg (some .emitRank) state [] [] (b :: work) index [] output)
          (cfg (some .emitRank) (some (.inl b)) [] [] work index []
            (.inl (some b) :: output)) 1 := one (by occurrence_emit_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (.inl (some b) :: output) (some (.inl b)))

private def emitIndex_run (index : List Bool) (output : List Output) (state : State) :
    Run (cfg (some .emitIndex) state [] [] [] index [] output)
      (cfg none none [] [] [] [] []
        ((DomainOccurrenceFieldBlock.headerPrefix ++ [none]).map Sum.inl ++
          index.reverse.map (fun b => .inl (some b)) ++ output))
      (index.length + 1) := by
  induction index generalizing output state with
  | nil => exact one (by simp only [DomainOccurrenceFieldBlock.headerPrefix]; occurrence_emit_step)
  | cons b index ih =>
      have h : Run (cfg (some .emitIndex) state [] [] [] (b :: index) [] output)
          (cfg (some .emitIndex) (some (.inl b)) [] [] [] index []
            (.inl (some b) :: output)) 1 := one (by occurrence_emit_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seq h (ih (.inl (some b) :: output) (some (.inl b)))

private def run (input : OccurrenceQuery.Ranked) :
    Run (cfg (some .tally) none (OccurrenceQuery.rankedFinEncoding.encode input) [] [] [] [] [])
      (cfg none none [] [] [] [] [] (OccurrenceEmit.outputFinEncoding.encode (OccurrenceEmit.emit input)))
      (tallyTime input.1 0 + 2 * (encodeNat input.2.1).length +
        2 * (DomainSymbolExtraction.finEncoding.encode input.2.2).length +
        2 * (encodeNat input.1).length + 6) := by
  let index := encodeNat input.2.1
  let source := DomainSymbolExtraction.finEncoding.encode input.2.2
  let rest : List (Sum Bool Source) := index.map Sum.inl ++ source.map Sum.inr
  have ht := tally_run input.1 0 rest none
  simp only [Nat.zero_add, show encodeNat 0 = [] by simp [encodeNat, encodeNum]] at ht
  have hi := index_run index [] (encodeNat input.1) source ((rest.map Sum.inr).head?)
  have hs := source_run source [] (encodeNat input.1) index.reverse
    ((source.map (fun c => .inr (.inr c))).head?)
  have he := emitSource_run source.reverse (encodeNat input.1) index.reverse [] none
  have hr := reverseRank_run (encodeNat input.1) [] index.reverse (source.map Sum.inr) none
  have hb := emitRank_run (encodeNat input.1).reverse index.reverse (source.map Sum.inr) none
  have hf := emitIndex_run index.reverse
    (.inl none :: (encodeNat input.1).map (fun b => .inl (some b)) ++ source.map Sum.inr) none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hi hs he hr hb hf
  have ht' : Run (cfg (some .tally) none (OccurrenceQuery.rankedFinEncoding.encode input) [] [] [] [] [])
      (cfg (some .index) ((rest.map Sum.inr).head?)
        (index.map (fun b => .inr (.inl b)) ++ source.map (fun c => .inr (.inr c)))
        (encodeNat input.1) [] [] [] []) (tallyTime input.1 0) := by
    simpa [OccurrenceQuery.rankedFinEncoding, OccurrenceQuery.retainedFinEncoding,
      unaryFinEncodingNat, unaryEncodeNat_eq_replicate_true, finEncodingNatBool, encodingNatBool,
      rest, index, source, List.map_append, List.map_map, Function.comp_def] using ht
  convert seq (seq (seq (seq (seq (seq ht' hi) hs) he) hr) hb) hf using 1
  · simp [OccurrenceEmit.outputFinEncoding, OccurrenceEmit.emit,
      DomainOccurrenceFieldBlock.outputFinEncoding, DomainOccurrenceFieldBlock.outputEncode_eq_prefix,
      DomainOccurrenceFieldBlock.inputEncode, SourceOrderRawFields.encode, index, source,
      List.map_append, List.map_map, Function.comp_def, List.append_assoc]
  · dsimp [index, source]
    omega

private theorem init_eq (input : List Input) :
    initList computer input = cfg (some .tally) none input [] [] [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none none [] [] [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

end OccurrenceEmitMachine

/-- Convert the tally and emit one binary record in quadratic time in the
complete input wire, including retained-source copies and empty cases. -/
def occurrenceEmit_outputsInTime (input : OccurrenceQuery.Ranked) :
    TM2OutputsInTime OccurrenceEmitMachine.computer (OccurrenceQuery.rankedFinEncoding.encode input)
      (some (OccurrenceEmit.outputFinEncoding.encode (OccurrenceEmit.emit input)))
      (12 * ((OccurrenceQuery.rankedFinEncoding.encode input).length + 1) ^ 2) := by
  rw [TM2OutputsInTime, OccurrenceEmitMachine.init_eq]
  simp only [Option.map_some]
  rw [OccurrenceEmitMachine.halt_eq]
  have h := OccurrenceEmitMachine.run input
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  have ht := OccurrenceEmitMachine.tallyTime_le input.1 0
  have hb := BinaryNatLists.encodeNat_length_le input.1
  rw [OccurrenceEmit.input_length]
  nlinarith

noncomputable def occurrenceEmitComputableInPolyTime :
    @TM2ComputableInPolyTime OccurrenceQuery.Ranked OccurrenceEmit.Output
      OccurrenceQuery.rankedFinEncoding OccurrenceEmit.outputFinEncoding OccurrenceEmit.emit where
  tm := OccurrenceEmitMachine.computer
  inputAlphabet := Equiv.refl OccurrenceEmitMachine.Input
  outputAlphabet := Equiv.refl OccurrenceEmitMachine.Output
  time := 12 * (Polynomial.X + 1) ^ 2
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using occurrenceEmit_outputsInTime input

#print axioms OccurrenceEmit.output_length_le
#print axioms occurrenceEmit_outputsInTime
#print axioms occurrenceEmitComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
