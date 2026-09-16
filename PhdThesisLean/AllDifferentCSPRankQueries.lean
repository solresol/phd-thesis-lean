import PhdThesisLean.AllDifferentCSPSymbolComparison

/-!
# Prepare one canonical-rank iteration from its serialized input

The input is the existing target/symbol-list wire, restricted by its decoder to
nonempty lists. A finite pass constructs the membership query, comparison pair,
and remaining rank query together. Every copied bit is charged, and the target
and tail survive both later predicate calls. This does not yet iterate or count
ranks; `cor:all-different-csp` remains partial.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace RankQueries

/-- Target, current symbol, and remaining source symbols. -/
abbrev Input := ℕ × ℕ × List ℕ

abbrev Output := DomainSymbolMembership.Input ×
  (DomainSymbolComparison.Input × DomainSymbolMembership.Input)

def inputEncode (input : Input) :=
  DomainSymbolMembership.finEncoding.encode (input.1, input.2.1 :: input.2.2)

def inputDecode (wire : List (Sum Bool (Option Bool))) : Option Input := do
  let (target, symbols) ← DomainSymbolMembership.finEncoding.decode wire
  match symbols with
  | [] => none
  | symbol :: rest => some (target, symbol, rest)

@[simp] theorem inputDecode_encode (input : Input) :
    inputDecode (inputEncode input) = some input := by
  rcases input with ⟨target, symbol, rest⟩
  simp [inputDecode, inputEncode, Encoding.decode_encode]

def inputFinEncoding : FinEncoding Input where
  Γ := Sum Bool (Option Bool)
  encode := inputEncode
  decode := inputDecode
  decode_encode := inputDecode_encode
  ΓFin := inferInstance

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding DomainSymbolMembership.finEncoding
    (LeanNPHardness.PairEncoding.finEncoding DomainSymbolComparison.finEncoding
      DomainSymbolMembership.finEncoding)

/-- Queries to test repetition and order, followed by the next rank input. -/
def prepare (input : Input) : Output :=
  ((input.2.1, input.2.2), ((input.2.1, input.1), (input.1, input.2.2)))

theorem input_length (input : Input) :
    (inputEncode input).length =
      (encodeNat input.1).length + (encodeNat input.2.1).length + 1 +
        (SourceOrderRawFields.encode input.2.2).length := by
  simp [inputEncode, DomainSymbolMembership.finEncoding, finEncodingNatBool,
    encodingNatBool, SourceOrderRawFields.finEncoding, SourceOrderRawFields.encode,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Each payload bit/delimiter is copied twice; only the consumed head's field
separator disappears. Arbitrarily large symbols are measured by their bits. -/
theorem output_length (input : Input) :
    (outputFinEncoding.encode (prepare input)).length + 2 =
      2 * (inputEncode input).length := by
  rw [input_length]
  simp [outputFinEncoding, prepare, DomainSymbolMembership.finEncoding,
    DomainSymbolComparison.finEncoding, finEncodingNatBool, encodingNatBool,
    SourceOrderRawFields.finEncoding]
  omega

end RankQueries

namespace RankQueryMachine

abbrev Wire := Sum Bool (Option Bool)
abbrev Raw := Option Bool
abbrev Output := Sum Wire (Sum (Sum Bool Bool) Wire)

inductive Block
  | mh | mt | ch | ct | rt | rr
  deriving DecidableEq, Fintype

inductive Stack
  | input | saved (block : Block) | output
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Wire | .saved _ => Raw | .output => Output

inductive Label
  | target | head | tail | emit (block : Block)
  deriving DecidableEq, Fintype

abbrev State := Option Wire × Option Raw

def initialState : State := (none, none)

private def observe (_ : State) (cell : Option Wire) : State := (cell, none)
private def remember (_ : State) (cell : Option Raw) : State := (none, cell)
private def targetBit (state : State) : Option Bool := state.1.bind Sum.getLeft?
private def sourceCell (state : State) : Option Raw := state.1.bind Sum.getRight?
private def headBit (state : State) : Option Bool := (sourceCell state).join

def tag : Block → Raw → Output
  | .mh, bit => .inl (.inl (bit.getD false))
  | .mt, cell => .inl (.inr cell)
  | .ch, bit => .inr (.inl (.inl (bit.getD false)))
  | .ct, bit => .inr (.inl (.inr (bit.getD false)))
  | .rt, bit => .inr (.inr (.inl (bit.getD false)))
  | .rr, cell => .inr (.inr (.inr cell))

def next : Block → Option Label
  | .rr => some (.emit .rt) | .rt => some (.emit .ct)
  | .ct => some (.emit .ch) | .ch => some (.emit .mt)
  | .mt => some (.emit .mh) | .mh => none

def program : Label → TM2.Stmt Alphabet Label State
  | .target => .pop .input observe <|
      .branch (fun s => (targetBit s).isSome)
        (.push (.saved .ct) targetBit <| .push (.saved .rt) targetBit <|
          .goto fun _ => .target)
        (.load (fun _ => initialState) <| .goto fun _ => .head)
  | .head => .pop .input observe <|
      .branch (fun s => (headBit s).isSome)
        (.push (.saved .mh) headBit <| .push (.saved .ch) headBit <|
          .goto fun _ => .head)
        (.branch (fun s => s.1.isSome)
          (.push (.saved .mt) (fun _ => none) <| .push (.saved .rr) (fun _ => none) <|
            .load (fun _ => initialState) <| .goto fun _ => .tail)
          (.load (fun _ => initialState) <| .goto fun _ => .emit .rr))
  | .tail => .pop .input observe <|
      .branch (fun s => (sourceCell s).isSome)
        (.push (.saved .mt) (fun s => (sourceCell s).getD none) <|
          .push (.saved .rr) (fun s => (sourceCell s).getD none) <|
            .goto fun _ => .tail)
        (.load (fun _ => initialState) <| .goto fun _ => .emit .rr)
  | .emit block => .pop (.saved block) remember <|
      .branch (fun s => s.2.isSome)
        (.push .output (fun s => tag block (s.2.getD none)) <| .goto fun _ => .emit block)
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
  main := .target
  σ := State
  initialState := initialState
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input : List Wire) (mh mt ch ct rt rr : List Raw)
    (output : List Output) : (k : Stack) → List (Alphabet k)
  | .input => input | .saved .mh => mh | .saved .mt => mt | .saved .ch => ch
  | .saved .ct => ct | .saved .rt => rt | .saved .rr => rr | .output => output

private def cfg (label : Option Label) (state : State) (input : List Wire)
    (mh mt ch ct rt rr : List Raw) (output : List Output) : computer.Cfg :=
  ⟨label, state, stackContents input mh mt ch ct rt rr output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "query_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, next,
    observe, remember, targetBit, sourceCell, headBit, Function.update]
   <;> first | rfl | (funext k; cases k with
     | input => rfl | saved block => cases block <;> rfl | output => rfl)))

private def target_run (bits : List Bool) (rest : List Wire)
    (ct rt : List Raw) (state : State) :
    Run (cfg (some .target) state (bits.map Sum.inl ++ .inr none :: rest) [] [] [] ct rt [] [])
      (cfg (some .head) initialState rest [] [] []
        ((bits.map some).reverse ++ ct) ((bits.map some).reverse ++ rt) [] [])
      (bits.length + 1) := by
  induction bits generalizing ct rt state with
  | nil => exact one (by query_step)
  | cons bit bits ih =>
      have h : Run (cfg (some .target) state
          ((bit :: bits).map Sum.inl ++ .inr none :: rest) [] [] [] ct rt [] [])
          (cfg (some .target) (some (.inl bit), none)
            (bits.map Sum.inl ++ .inr none :: rest) [] [] [] (some bit :: ct) (some bit :: rt) [] []) 1 :=
        one (by query_step)
      simpa [List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (some bit :: ct) (some bit :: rt) (some (.inl bit), none))

private def head_bits_run (bits : List Bool) (rest : List Wire)
    (mh ch ct rt : List Raw) (state : State) :
    Run (cfg (some .head) state (bits.map (fun b => .inr (some b)) ++ rest) mh [] ch ct rt [] [])
      (cfg (some .head) (if bits.isEmpty then state else (some (.inr (some bits.getLast!)), none))
        rest ((bits.map some).reverse ++ mh) [] ((bits.map some).reverse ++ ch) ct rt [] [])
      bits.length := by
  induction bits generalizing mh ch state with
  | nil => exact EvalsToInTime.refl _ _
  | cons bit bits ih =>
      have h : Run (cfg (some .head) state
          ((bit :: bits).map (fun b => .inr (some b)) ++ rest) mh [] ch ct rt [] [])
          (cfg (some .head) (some (.inr (some bit)), none)
            (bits.map (fun b => .inr (some b)) ++ rest) (some bit :: mh) [] (some bit :: ch) ct rt [] []) 1 :=
        one (by query_step)
      have hi := seq h (ih (some bit :: mh) (some bit :: ch) (some (.inr (some bit)), none))
      cases bits <;> simpa [List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

private def tail_run (cells : List Raw) (mh mt ch ct rt rr : List Raw) (state : State) :
    Run (cfg (some .tail) state (cells.map Sum.inr) mh mt ch ct rt rr [])
      (cfg (some (.emit .rr)) initialState [] mh (cells.reverse ++ mt) ch ct rt
        (cells.reverse ++ rr) []) (cells.length + 1) := by
  induction cells generalizing mt rr state with
  | nil => exact one (by query_step)
  | cons cell cells ih =>
      have h : Run (cfg (some .tail) state ((cell :: cells).map Sum.inr) mh mt ch ct rt rr [])
          (cfg (some .tail) (some (.inr cell), none) (cells.map Sum.inr)
            mh (cell :: mt) ch ct rt (cell :: rr) []) 1 := one (by query_step)
      simpa [List.map_cons, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (cell :: mt) (cell :: rr) (some (.inr cell), none))

private def emit_mh (mh mt ch ct rt rr : List Raw) (output : List Output) (state : State) :
    Run (cfg (some (.emit .mh)) state [] mh mt ch ct rt rr output)
      (cfg (next .mh) initialState [] [] mt ch ct rt rr ((mh.reverse.map (tag .mh)) ++ output))
      (mh.length + 1) := by
  induction mh generalizing output state with
  | nil => exact one (by query_step)
  | cons cell mh ih =>
      have h : Run (cfg (some (.emit .mh)) state [] (cell :: mh) mt ch ct rt rr output)
          (cfg (some (.emit .mh)) (none, some cell) [] mh mt ch ct rt rr (tag .mh cell :: output)) 1 :=
        one (by query_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (tag .mh cell :: output) (none, some cell))

private def emit_mt (mh mt ch ct rt rr : List Raw) (output : List Output) (state : State) :
    Run (cfg (some (.emit .mt)) state [] mh mt ch ct rt rr output)
      (cfg (next .mt) initialState [] mh [] ch ct rt rr ((mt.reverse.map (tag .mt)) ++ output))
      (mt.length + 1) := by
  induction mt generalizing output state with
  | nil => exact one (by query_step)
  | cons cell mt ih =>
      have h : Run (cfg (some (.emit .mt)) state [] mh (cell :: mt) ch ct rt rr output)
          (cfg (some (.emit .mt)) (none, some cell) [] mh mt ch ct rt rr (tag .mt cell :: output)) 1 :=
        one (by query_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (tag .mt cell :: output) (none, some cell))

private def emit_ch (mh mt ch ct rt rr : List Raw) (output : List Output) (state : State) :
    Run (cfg (some (.emit .ch)) state [] mh mt ch ct rt rr output)
      (cfg (next .ch) initialState [] mh mt [] ct rt rr ((ch.reverse.map (tag .ch)) ++ output))
      (ch.length + 1) := by
  induction ch generalizing output state with
  | nil => exact one (by query_step)
  | cons cell ch ih =>
      have h : Run (cfg (some (.emit .ch)) state [] mh mt (cell :: ch) ct rt rr output)
          (cfg (some (.emit .ch)) (none, some cell) [] mh mt ch ct rt rr (tag .ch cell :: output)) 1 :=
        one (by query_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (tag .ch cell :: output) (none, some cell))

private def emit_ct (mh mt ch ct rt rr : List Raw) (output : List Output) (state : State) :
    Run (cfg (some (.emit .ct)) state [] mh mt ch ct rt rr output)
      (cfg (next .ct) initialState [] mh mt ch [] rt rr ((ct.reverse.map (tag .ct)) ++ output))
      (ct.length + 1) := by
  induction ct generalizing output state with
  | nil => exact one (by query_step)
  | cons cell ct ih =>
      have h : Run (cfg (some (.emit .ct)) state [] mh mt ch (cell :: ct) rt rr output)
          (cfg (some (.emit .ct)) (none, some cell) [] mh mt ch ct rt rr (tag .ct cell :: output)) 1 :=
        one (by query_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (tag .ct cell :: output) (none, some cell))

private def emit_rt (mh mt ch ct rt rr : List Raw) (output : List Output) (state : State) :
    Run (cfg (some (.emit .rt)) state [] mh mt ch ct rt rr output)
      (cfg (next .rt) initialState [] mh mt ch ct [] rr ((rt.reverse.map (tag .rt)) ++ output))
      (rt.length + 1) := by
  induction rt generalizing output state with
  | nil => exact one (by query_step)
  | cons cell rt ih =>
      have h : Run (cfg (some (.emit .rt)) state [] mh mt ch ct (cell :: rt) rr output)
          (cfg (some (.emit .rt)) (none, some cell) [] mh mt ch ct rt rr (tag .rt cell :: output)) 1 :=
        one (by query_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (tag .rt cell :: output) (none, some cell))

private def emit_rr (mh mt ch ct rt rr : List Raw) (output : List Output) (state : State) :
    Run (cfg (some (.emit .rr)) state [] mh mt ch ct rt rr output)
      (cfg (next .rr) initialState [] mh mt ch ct rt [] ((rr.reverse.map (tag .rr)) ++ output))
      (rr.length + 1) := by
  induction rr generalizing output state with
  | nil => exact one (by query_step)
  | cons cell rr ih =>
      have h : Run (cfg (some (.emit .rr)) state [] mh mt ch ct rt (cell :: rr) output)
          (cfg (some (.emit .rr)) (none, some cell) [] mh mt ch ct rt rr (tag .rr cell :: output)) 1 :=
        one (by query_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (tag .rr cell :: output) (none, some cell))

private def head_run (bits : List Bool) (symbols : List ℕ) (target : List Raw) :
    Run (cfg (some .head) initialState
        (bits.map (fun b => .inr (some b)) ++ (SourceOrderRawFields.encode symbols).map Sum.inr)
        [] [] [] target target [] [])
      (cfg (some (.emit .rr)) initialState []
        (bits.map some).reverse (SourceOrderRawFields.encode symbols).reverse
        (bits.map some).reverse target target (SourceOrderRawFields.encode symbols).reverse [])
      (bits.length + (SourceOrderRawFields.encode symbols).length + 1) := by
  let state : State := if bits.isEmpty then initialState else (some (.inr (some bits.getLast!)), none)
  have hb := head_bits_run bits ((SourceOrderRawFields.encode symbols).map Sum.inr)
    [] [] target target initialState
  simp only [List.append_nil] at hb
  cases symbols with
  | nil =>
      have he : Run (cfg (some .head) state [] (bits.map some).reverse []
          (bits.map some).reverse target target [] [])
          (cfg (some (.emit .rr)) initialState [] (bits.map some).reverse []
            (bits.map some).reverse target target [] []) 1 := one (by query_step)
      simpa [SourceOrderRawFields.encode] using seq hb he
  | cons symbol symbols =>
      let rest := (encodeNat symbol).map some ++ SourceOrderRawFields.encode symbols
      have he : Run (cfg (some .head) state (.inr none :: rest.map Sum.inr)
          (bits.map some).reverse [] (bits.map some).reverse target target [] [])
          (cfg (some .tail) initialState (rest.map Sum.inr)
            (bits.map some).reverse [none] (bits.map some).reverse target target [none] []) 1 :=
        one (by query_step)
      have ht := tail_run rest (bits.map some).reverse [none] (bits.map some).reverse
        target target [none] initialState
      simpa [SourceOrderRawFields.encode, rest, List.map_append, List.map_cons,
        List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using seq (seq hb he) ht

private def emit_all (head target tail : List Raw) :
    Run (cfg (some (.emit .rr)) initialState [] head.reverse tail.reverse
        head.reverse target.reverse target.reverse tail.reverse [])
      (cfg none initialState [] [] [] [] [] [] []
        (head.map (tag .mh) ++ tail.map (tag .mt) ++ head.map (tag .ch) ++
          target.map (tag .ct) ++ target.map (tag .rt) ++ tail.map (tag .rr)))
      (2 * (head.length + target.length + tail.length) + 6) := by
  have hrr := emit_rr head.reverse tail.reverse head.reverse target.reverse target.reverse tail.reverse [] initialState
  have hrt := emit_rt head.reverse tail.reverse head.reverse target.reverse target.reverse []
    (tail.map (tag .rr)) initialState
  have hct := emit_ct head.reverse tail.reverse head.reverse target.reverse [] []
    (target.map (tag .rt) ++ tail.map (tag .rr)) initialState
  have hch := emit_ch head.reverse tail.reverse head.reverse [] [] []
    (target.map (tag .ct) ++ target.map (tag .rt) ++ tail.map (tag .rr)) initialState
  have hmt := emit_mt head.reverse tail.reverse [] [] [] []
    (head.map (tag .ch) ++ target.map (tag .ct) ++ target.map (tag .rt) ++ tail.map (tag .rr)) initialState
  have hmh := emit_mh head.reverse [] [] [] [] []
    (tail.map (tag .mt) ++ head.map (tag .ch) ++ target.map (tag .ct) ++
      target.map (tag .rt) ++ tail.map (tag .rr)) initialState
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil, next, List.append_assoc]
    at hrr hrt hct hch hmt hmh ⊢
  convert seq (seq (seq (seq (seq hrr hrt) hct) hch) hmt) hmh using 1
  omega

private def run (input : RankQueries.Input) :
    Run (cfg (some .target) initialState (RankQueries.inputEncode input) [] [] [] [] [] [] [])
      (cfg none initialState [] [] [] [] [] [] [] (RankQueries.outputFinEncoding.encode (RankQueries.prepare input)))
      (3 * (RankQueries.inputEncode input).length + 5) := by
  rcases input with ⟨target, symbol, symbols⟩
  let t := encodeNat target
  let h := encodeNat symbol
  let r := SourceOrderRawFields.encode symbols
  have ht := target_run t (h.map (fun b => .inr (some b)) ++ r.map Sum.inr) [] [] initialState
  have hh := head_run h symbols (t.map some).reverse
  have he := emit_all (h.map some) (t.map some) r
  simp only [List.append_nil] at ht
  have result := seq (seq ht hh) he
  convert result using 1
  · simp [RankQueries.inputEncode, DomainSymbolMembership.finEncoding,
      LeanNPHardness.PairEncoding.finEncoding, finEncodingNatBool, encodingNatBool,
      SourceOrderRawFields.finEncoding, SourceOrderRawFields.encode,
      t, h, r, List.map_append, List.map_map, Function.comp_def]
  · simp [RankQueries.outputFinEncoding, RankQueries.prepare,
      DomainSymbolMembership.finEncoding, DomainSymbolComparison.finEncoding,
      LeanNPHardness.PairEncoding.finEncoding, finEncodingNatBool, encodingNatBool,
      SourceOrderRawFields.finEncoding, t, h, r, tag, List.map_append, List.map_map,
      Function.comp_def, List.append_assoc]
    rfl
  · rw [RankQueries.input_length]
    simp only [List.length_map]
    dsimp [t, h, r]
    omega

private theorem init_eq (input : List Wire) :
    initList computer input = cfg (some .target) initialState input [] [] [] [] [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k with
  | input => rfl | saved block => cases block <;> rfl | output => rfl

private theorem halt_eq (output : List Output) :
    haltList computer output = cfg none initialState [] [] [] [] [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k with
  | input => rfl | saved block => cases block <;> rfl | output => rfl

end RankQueryMachine

/-- Prepare all three exact queries in `3s+5` finite-machine steps, including
all copies, ordering passes, and cleanup, for complete rank-input wire length `s`. -/
def rankQueries_outputsInTime (input : RankQueries.Input) :
    TM2OutputsInTime RankQueryMachine.computer (RankQueries.inputFinEncoding.encode input)
      (some (RankQueries.outputFinEncoding.encode (RankQueries.prepare input)))
      (3 * (RankQueries.inputFinEncoding.encode input).length + 5) := by
  rw [TM2OutputsInTime, RankQueryMachine.init_eq]
  simp only [Option.map_some]
  rw [RankQueryMachine.halt_eq]
  exact RankQueryMachine.run input

noncomputable def rankQueriesComputableInPolyTime :
    @TM2ComputableInPolyTime RankQueries.Input RankQueries.Output
      RankQueries.inputFinEncoding RankQueries.outputFinEncoding RankQueries.prepare where
  tm := RankQueryMachine.computer
  inputAlphabet := Equiv.refl RankQueryMachine.Wire
  outputAlphabet := Equiv.refl RankQueryMachine.Output
  time := 3 * Polynomial.X + 5
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X] using rankQueries_outputsInTime input

#print axioms RankQueries.inputDecode_encode
#print axioms RankQueries.output_length
#print axioms rankQueries_outputsInTime
#print axioms rankQueriesComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
