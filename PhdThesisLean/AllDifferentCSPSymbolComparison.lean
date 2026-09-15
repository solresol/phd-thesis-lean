import PhdThesisLean.AllDifferentCSPSymbolRankStep
import Mathlib.Logic.Equiv.Bool

/-!
# Serialized comparison for the canonical symbol-rank loop

The rank recurrence needs a comparison of a symbol with the target value.
The existing upstream comparator takes aligned canonical binary words. This
loader constructs that alignment from a checked tagged pair, charging every
load, reversal, and alignment step. The comparison kernel is reused unchanged.
The repeated rank driver and the full all-different corollary remain pending.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition LeanNPHardness.MachinePrimitives

namespace DomainSymbolComparison

abbrev Input := ℕ × ℕ

/-- A source symbol followed by the rank target, each in canonical binary. -/
def finEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingNatBool finEncodingNatBool

def less (input : Input) : Bool := decide (input.1 < input.2)

theorem input_length (symbol value : ℕ) :
    (finEncoding.encode (symbol, value)).length =
      (encodeNat symbol).length + (encodeNat value).length := by
  simp [finEncoding, finEncodingNatBool, encodingNatBool]

end DomainSymbolComparison

namespace SymbolComparisonLoader

abbrev Wire := Sum Bool Bool
abbrev Aligned := Option Bool × Option Bool

inductive Stack
  | input | saved (side : Bool) | ready (side : Bool) | buffer | output
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Wire | .saved _ | .ready _ => Bool | .buffer | .output => Aligned

inductive Label
  | read | restore (side : Bool) | align | finish
  deriving DecidableEq, Fintype

structure State where
  cell : Option Wire
  left : Option Bool
  right : Option Bool
  pair : Option Aligned
  deriving DecidableEq, Fintype

def initialState : State := ⟨none, none, none, none⟩

private def observe (s : State) (cell : Option Wire) : State := { s with cell := cell }
private def leftBit (s : State) : Option Bool := s.cell.bind Sum.getLeft?
private def rightBit (s : State) : Option Bool := s.cell.bind Sum.getRight?
private def observeLeft (s : State) (bit : Option Bool) : State := { s with left := bit }
private def observeRight (s : State) (bit : Option Bool) : State := { s with right := bit }
private def observePair (s : State) (pair : Option Aligned) : State := { s with pair := pair }

def program : Label → TM2.Stmt Alphabet Label State
  | .read => .pop .input observe <|
      .branch (fun s => (leftBit s).isSome)
        (.push (.saved false) (fun s => (leftBit s).getD false) <| .goto fun _ => .read)
        (.branch (fun s => (rightBit s).isSome)
          (.push (.saved true) (fun s => (rightBit s).getD false) <| .goto fun _ => .read)
          (.load (fun _ => initialState) <| .goto fun _ => .restore false))
  | .restore side => .pop (.saved side) observeLeft <|
      .branch (fun s => s.left.isSome)
        (.push (.ready side) (fun s => s.left.getD false) <| .goto fun _ => .restore side)
        (.load (fun _ => initialState) <|
          .goto fun _ => if side then .align else .restore true)
  | .align => .pop (.ready false) observeLeft <| .pop (.ready true) observeRight <|
      .branch (fun s => s.left.isSome || s.right.isSome)
        (.push .buffer (fun s => (s.left, s.right)) <| .goto fun _ => .align)
        (.load (fun _ => initialState) <| .goto fun _ => .finish)
  | .finish => .pop .buffer observePair <|
      .branch (fun s => s.pair.isSome)
        (.push .output (fun s => s.pair.getD (none, none)) <| .goto fun _ => .finish)
        (.load (fun _ => initialState) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .read
  σ := State
  initialState := initialState
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input : List Wire) (sl sr left right : List Bool)
    (buffer output : List Aligned) : (k : Stack) → List (Alphabet k)
  | .input => input | .saved false => sl | .saved true => sr
  | .ready false => left | .ready true => right | .buffer => buffer | .output => output

private def cfg (label : Option Label) (state : State) (input : List Wire)
    (sl sr left right : List Bool) (buffer output : List Aligned) : computer.Cfg :=
  ⟨label, state, stackContents input sl sr left right buffer output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "loader_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    observe, leftBit, rightBit, observeLeft, observeRight, observePair, Function.update]
   <;> first | rfl | (funext k; cases k with
     | input => rfl | saved side => cases side <;> rfl
     | ready side => cases side <;> rfl | buffer => rfl | output => rfl)))

private def read_run (input : List Wire) (sl sr : List Bool) (state : State) :
    Run (cfg (some .read) state input sl sr [] [] [] [])
      (cfg (some (.restore false)) initialState []
        ((LeanNPHardness.PairEncoding.leftSymbols input).reverse ++ sl)
        ((LeanNPHardness.PairEncoding.rightSymbols input).reverse ++ sr) [] [] [] [])
      (input.length + 1) := by
  induction input generalizing sl sr state with
  | nil => exact one (by loader_step)
  | cons cell input ih =>
      cases cell with
      | inl bit =>
          have h : Run (cfg (some .read) state (.inl bit :: input) sl sr [] [] [] [])
              (cfg (some .read) { state with cell := some (.inl bit) }
                input (bit :: sl) sr [] [] [] []) 1 := one (by loader_step)
          simpa [LeanNPHardness.PairEncoding.leftSymbols, LeanNPHardness.PairEncoding.rightSymbols,
            List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using seq h (ih (bit :: sl) sr { state with cell := some (.inl bit) })
      | inr bit =>
          have h : Run (cfg (some .read) state (.inr bit :: input) sl sr [] [] [] [])
              (cfg (some .read) { state with cell := some (.inr bit) }
                input sl (bit :: sr) [] [] [] []) 1 := one (by loader_step)
          simpa [LeanNPHardness.PairEncoding.leftSymbols, LeanNPHardness.PairEncoding.rightSymbols,
            List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using seq h (ih sl (bit :: sr) { state with cell := some (.inr bit) })

private def restore_left (sl sr left : List Bool) (state : State) :
    Run (cfg (some (.restore false)) state [] sl sr left [] [] [])
      (cfg (some (.restore true)) initialState [] [] sr (sl.reverse ++ left) [] [] [])
      (sl.length + 1) := by
  induction sl generalizing left state with
  | nil => exact one (by loader_step)
  | cons bit sl ih =>
      have h : Run (cfg (some (.restore false)) state [] (bit :: sl) sr left [] [] [])
          (cfg (some (.restore false)) { state with left := some bit }
            [] sl sr (bit :: left) [] [] []) 1 := one (by loader_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using seq h (ih (bit :: left) { state with left := some bit })

private def restore_right (sr left right : List Bool) (state : State) :
    Run (cfg (some (.restore true)) state [] [] sr left right [] [])
      (cfg (some .align) initialState [] [] [] left (sr.reverse ++ right) [] [])
      (sr.length + 1) := by
  induction sr generalizing right state with
  | nil => exact one (by loader_step)
  | cons bit sr ih =>
      have h : Run (cfg (some (.restore true)) state [] [] (bit :: sr) left right [] [])
          (cfg (some (.restore true)) { state with left := some bit }
            [] [] sr left (bit :: right) [] []) 1 := one (by loader_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using seq h (ih (bit :: right) { state with left := some bit })

theorem zipBits_length (left right : List Bool) :
    (BinaryNatPair.zipBits left right).length = max left.length right.length := by
  induction left generalizing right with
  | nil =>
      induction right with
      | nil => simp [BinaryNatPair.zipBits]
      | cons bit right ih => simp [BinaryNatPair.zipBits, ih]
  | cons bit left ih =>
      cases right with
      | nil => simp [BinaryNatPair.zipBits, ih]
      | cons other right => simp only [BinaryNatPair.zipBits, List.length_cons, ih]; omega

private def align_run (left right : List Bool) (buffer : List Aligned) (state : State) :
    Run (cfg (some .align) state [] [] [] left right buffer [])
      (cfg (some .finish) initialState [] [] [] [] []
        ((BinaryNatPair.zipBits left right).reverse ++ buffer) [])
      (max left.length right.length + 1) := by
  induction left generalizing right buffer state with
  | nil =>
      induction right generalizing buffer state with
      | nil =>
          simp only [BinaryNatPair.zipBits, List.reverse_nil, List.nil_append]
          exact one (by loader_step)
      | cons bit right ih =>
          have h : Run (cfg (some .align) state [] [] [] [] (bit :: right) buffer [])
              (cfg (some .align) { state with left := none, right := some bit }
                [] [] [] [] right ((none, some bit) :: buffer) []) 1 := one (by loader_step)
          simpa [BinaryNatPair.zipBits, List.reverse_cons, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            seq h (ih ((none, some bit) :: buffer) { state with left := none, right := some bit })
  | cons bit left ih =>
      cases right with
      | nil =>
          have h : Run (cfg (some .align) state [] [] [] (bit :: left) [] buffer [])
              (cfg (some .align) { state with left := some bit, right := none }
                [] [] [] left [] ((some bit, none) :: buffer) []) 1 := one (by loader_step)
          simpa [BinaryNatPair.zipBits, List.reverse_cons, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            seq h (ih [] ((some bit, none) :: buffer) { state with left := some bit, right := none })
      | cons other right =>
          have h : Run (cfg (some .align) state [] [] [] (bit :: left) (other :: right) buffer [])
              (cfg (some .align) { state with left := some bit, right := some other }
                [] [] [] left right ((some bit, some other) :: buffer) []) 1 := one (by loader_step)
          convert seq h (ih right ((some bit, some other) :: buffer)
            { state with left := some bit, right := some other }) using 1
          · simp [BinaryNatPair.zipBits, List.reverse_cons, List.append_assoc]
          · simp only [List.length_cons]; omega

private def finish_run (buffer output : List Aligned) (state : State) :
    Run (cfg (some .finish) state [] [] [] [] [] buffer output)
      (cfg none initialState [] [] [] [] [] [] (buffer.reverse ++ output))
      (buffer.length + 1) := by
  induction buffer generalizing output state with
  | nil => exact one (by loader_step)
  | cons pair buffer ih =>
      have h : Run (cfg (some .finish) state [] [] [] [] [] (pair :: buffer) output)
          (cfg (some .finish) { state with pair := some pair }
            [] [] [] [] [] buffer (pair :: output)) 1 := one (by loader_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using seq h (ih (pair :: output) { state with pair := some pair })

private def run (symbol value : ℕ) :
    Run (cfg (some .read) initialState (DomainSymbolComparison.finEncoding.encode (symbol, value))
        [] [] [] [] [] [])
      (cfg none initialState [] [] [] [] [] [] (BinaryNatPair.encode (symbol, value)))
      (4 * (DomainSymbolComparison.finEncoding.encode (symbol, value)).length + 5) := by
  let left := encodeNat symbol
  let right := encodeNat value
  have hr := read_run (left.map Sum.inl ++ right.map Sum.inr) [] [] initialState
  simp only [LeanNPHardness.PairEncoding.leftSymbols_append,
    LeanNPHardness.PairEncoding.rightSymbols_append,
    LeanNPHardness.PairEncoding.leftSymbols_map_inl,
    LeanNPHardness.PairEncoding.leftSymbols_map_inr,
    LeanNPHardness.PairEncoding.rightSymbols_map_inl,
    LeanNPHardness.PairEncoding.rightSymbols_map_inr,
    List.append_nil, List.nil_append, List.length_append, List.length_map] at hr
  have hl := restore_left left.reverse right.reverse [] initialState
  have ht := restore_right right.reverse left [] initialState
  have ha := align_run left right [] initialState
  have hf := finish_run (BinaryNatPair.zipBits left right).reverse [] initialState
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse, zipBits_length] at hl ht ha hf
  have h := seq (seq (seq (seq hr hl) ht) ha) hf
  apply evalsToInTimeMono h
  rw [DomainSymbolComparison.input_length]
  change _ ≤ 4 * (left.length + right.length) + 5
  omega

private theorem init_eq (input : List Wire) :
    initList computer input = cfg (some .read) initialState input [] [] [] [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k with
  | input => rfl | saved side => cases side <;> rfl | ready side => cases side <;> rfl
  | buffer => rfl | output => rfl

private theorem halt_eq (output : List Aligned) :
    haltList computer output = cfg none initialState [] [] [] [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k with
  | input => rfl | saved side => cases side <;> rfl | ready side => cases side <;> rfl
  | buffer => rfl | output => rfl

end SymbolComparisonLoader

/-- Construct the complete aligned input to the upstream comparison kernel in
at most `4s+5` steps for the serialized symbol/target wire length `s`. -/
def domainSymbolAlignment_outputsInTime (input : DomainSymbolComparison.Input) :
    TM2OutputsInTime SymbolComparisonLoader.computer
      (DomainSymbolComparison.finEncoding.encode input)
      (some (BinaryNatPair.encode input))
      (4 * (DomainSymbolComparison.finEncoding.encode input).length + 5) := by
  rcases input with ⟨symbol, value⟩
  rw [TM2OutputsInTime, SymbolComparisonLoader.init_eq]
  simp only [Option.map_some]
  rw [SymbolComparisonLoader.halt_eq]
  exact SymbolComparisonLoader.run symbol value

noncomputable def domainSymbolAlignmentComputableInPolyTime :
    @TM2ComputableInPolyTime DomainSymbolComparison.Input (ℕ × ℕ)
      DomainSymbolComparison.finEncoding BinaryNatPair.finEncoding id where
  tm := SymbolComparisonLoader.computer
  inputAlphabet := Equiv.refl SymbolComparisonLoader.Wire
  outputAlphabet := Equiv.refl SymbolComparisonLoader.Aligned
  time := 4 * Polynomial.X + 5
  outputsFun input := by
    simpa [Equiv.refl, BinaryNatPair.finEncoding, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_X] using
      domainSymbolAlignment_outputsInTime input

theorem domainSymbolAlignment_output_length_le (input : DomainSymbolComparison.Input) :
    (BinaryNatPair.encode input).length ≤
      (DomainSymbolComparison.finEncoding.encode input).length := by
  rw [BinaryNatPair.encode, SymbolComparisonLoader.zipBits_length,
    DomainSymbolComparison.input_length]
  omega

private theorem swap_zipBits (left right : List Bool) :
    (BinaryNatPair.zipBits left right).map Prod.swap = BinaryNatPair.zipBits right left := by
  induction left generalizing right with
  | nil =>
      induction right with
      | nil => simp [BinaryNatPair.zipBits]
      | cons bit right ih => simp [BinaryNatPair.zipBits, ih]
  | cons bit left ih =>
      cases right with
      | nil => simp [BinaryNatPair.zipBits, ih]
      | cons other right => simp [BinaryNatPair.zipBits, ih]

/-- Reuse the upstream less-or-equal kernel. Swapping each aligned cell and
complementing its Boolean alphabet implements strict comparison without a new
arithmetic kernel. Both recodings are explicit finite-alphabet equivalences. -/
noncomputable def alignedSymbolLessComputableInPolyTime :
    @TM2ComputableInPolyTime (ℕ × ℕ) Bool BinaryNatPair.finEncoding
      finEncodingBoolBool DomainSymbolComparison.less where
  tm := binaryLEComputer
  inputAlphabet := Equiv.prodComm (Option Bool) (Option Bool)
  outputAlphabet := Equiv.boolNot
  time := Polynomial.X + 1
  outputsFun input := by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    change TM2OutputsInTime binaryLEComputer
      ((BinaryNatPair.encode input).map Prod.swap)
      (some [!(decide (input.1 < input.2))]) ((BinaryNatPair.encode input).length + 1)
    rw [BinaryNatPair.encode, swap_zipBits]
    have hn : (!(decide (input.1 < input.2))) = decide (input.2 ≤ input.1) := by
      by_cases h : input.1 < input.2
      · have h' : ¬input.2 ≤ input.1 := by omega
        simp [h, h']
      · have h' : input.2 ≤ input.1 := by omega
        simp [h, h']
    rw [hn]
    simpa [BinaryNatPair.encode, SymbolComparisonLoader.zipBits_length,
      Nat.max_comm] using binaryLE_outputsInTime (input.2, input.1)

/-- Compare a serialized symbol with its target in `9s+10` steps. The bound
includes loading, canonical alignment, the complete intermediate transfer,
and the upstream comparison. The output alphabet decodes the kernel bit to
exactly `symbol < target`. -/
noncomputable def domainSymbolLessComputableInPolyTime :
    @TM2ComputableInPolyTime DomainSymbolComparison.Input Bool
      DomainSymbolComparison.finEncoding finEncodingBoolBool DomainSymbolComparison.less where
  toTM2ComputableAux := compositionAux
    domainSymbolAlignmentComputableInPolyTime.toTM2ComputableAux
    alignedSymbolLessComputableInPolyTime.toTM2ComputableAux
  time := 9 * Polynomial.X + 10
  outputsFun input := by
    let first := domainSymbolAlignmentComputableInPolyTime.toTM2ComputableAux
    let second := alignedSymbolLessComputableInPolyTime.toTM2ComputableAux
    have hsecond := alignedSymbolLessComputableInPolyTime.outputsFun input
    simp only [alignedSymbolLessComputableInPolyTime, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one] at hsecond
    have h := compositionMachine_outputsInTime first second
      (DomainSymbolComparison.finEncoding.encode input) (BinaryNatPair.encode input)
      [!DomainSymbolComparison.less input]
      (4 * (DomainSymbolComparison.finEncoding.encode input).length + 5)
      ((BinaryNatPair.encode input).length + 1)
      (domainSymbolAlignment_outputsInTime input) (by exact hsecond)
    change TM2OutputsInTime (compositionMachine first second)
      (List.map id (DomainSymbolComparison.finEncoding.encode input))
      (some [!DomainSymbolComparison.less input]) _
    rw [List.map_id]
    apply evalsToInTimeMono h
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    have hs := domainSymbolAlignment_output_length_le input
    omega

/-- The complete comparison, including transfer, has this explicit linear bound. -/
theorem domainSymbolLess_time (s : ℕ) :
    domainSymbolLessComputableInPolyTime.time.eval s = 9 * s + 10 := by
  simp [domainSymbolLessComputableInPolyTime]

namespace DomainSymbolComparison

/-- Both Boolean branches now have checked finite-machine implementations;
this recurrence specifies how the future repeated rank driver combines them. -/
theorem rank_cons (symbol value : ℕ) (symbols : List ℕ) :
    DomainSymbols.rank (symbol :: symbols) value = DomainSymbols.rank symbols value +
      if less (symbol, value) && !DomainSymbolMembership.contains (symbol, symbols) then 1 else 0 :=
  DomainSymbolMembership.rank_cons symbol symbols value

/-- Exact size of the rank query before taking its first symbol. The target
bits and the candidate bits are both charged to the same complete wire. -/
theorem input_head_length (symbol value : ℕ) (symbols : List ℕ) :
    (DomainSymbolMembership.finEncoding.encode (value, symbol :: symbols)).length =
      (finEncoding.encode (symbol, value)).length + 1 +
        (SourceOrderRawFields.encode symbols).length := by
  simp [finEncoding, DomainSymbolMembership.finEncoding, finEncodingNatBool, encodingNatBool,
    SourceOrderRawFields.finEncoding, SourceOrderRawFields.encode,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Extracting a comparison pair fits inside the original target/symbol wire.
This size identity does not supply the retaining extraction machine. -/
theorem input_length_le_rank_query (symbol value : ℕ) (symbols : List ℕ) :
    (finEncoding.encode (symbol, value)).length + 1 ≤
      (DomainSymbolMembership.finEncoding.encode (value, symbol :: symbols)).length := by
  rw [input_head_length]
  omega

end DomainSymbolComparison

#print axioms domainSymbolAlignment_outputsInTime
#print axioms domainSymbolAlignmentComputableInPolyTime
#print axioms domainSymbolAlignment_output_length_le

#print axioms alignedSymbolLessComputableInPolyTime
#print axioms domainSymbolLessComputableInPolyTime
#print axioms domainSymbolLess_time
#print axioms DomainSymbolComparison.rank_cons
#print axioms DomainSymbolComparison.input_head_length
#print axioms DomainSymbolComparison.input_length_le_rank_query

end PhdThesisLean.AllDifferentCSPMachine
