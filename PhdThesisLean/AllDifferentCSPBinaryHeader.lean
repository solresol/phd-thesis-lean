import PhdThesisLean.AllDifferentCSPRowCount

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-!
# Stage the computed structural row count as a binary outer header

The input is the exact structural payload and its internally computed unary
row tally. A finite machine increments a binary counter once per tally mark,
then prepends that counter and reverses the complete wire into the existing
raw structural encoding. Every payload bit and delimiter is retained.
-/

namespace StructuralCountedPayload

/-- The tally is checked redundancy in this encoding of the structural view. -/
def checkedDecode (input : List (Sum (Option Bool) Bool)) :
    Option AllDifferentCSPEncoding.RuntimeStructuralView :=
  (finEncoding.decode input).bind fun pair =>
    if pair.2 = pair.1.records.length + 1 then some pair.1 else none

@[simp]
theorem checkedDecode_encode (view : AllDifferentCSPEncoding.RuntimeStructuralView) :
    checkedDecode (finEncoding.encode (retain view)) = some view := by
  simp [checkedDecode, finEncoding.decode_encode, retain]

def checkedFinEncoding : FinEncoding AllDifferentCSPEncoding.RuntimeStructuralView where
  Γ := Sum (Option Bool) Bool
  encode view := finEncoding.encode (retain view)
  decode := checkedDecode
  decode_encode := checkedDecode_encode
  ΓFin := inferInstance

end StructuralCountedPayload

namespace StructuralBinaryHeaderMachine

inductive Stack
  | input | payload | count | work | output
  deriving DecidableEq, Fintype

inductive Label
  | scan | tally | carry | restore | emitCount | restorePayload | finish
  deriving DecidableEq, Fintype

abbrev Tagged := Sum (Option Bool) Bool
abbrev State := Option Tagged
abbrev Alphabet : Stack → Type
  | .input => Tagged
  | .count | .work => Bool
  | .payload | .output => Option Bool
private def popped (_ : State) (symbol : Option Tagged) : State := symbol
private def poppedBit (_ : State) (symbol : Option Bool) : State := symbol.map Sum.inr
private def poppedCell (_ : State) (symbol : Option (Option Bool)) : State := symbol.map Sum.inl
private def present : State → Bool | some _ => true | none => false
private def isPayload : State → Bool | some (.inl _) => true | _ => false
private def held : State → Tagged | some symbol => symbol | none => .inr false
private def heldBit : State → Bool | some (.inr bit) => bit | _ => false
private def heldCell : State → Option Bool | some (.inl cell) => cell | _ => none

/-- All arithmetic is implemented by finite carry and restore transitions. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .scan => .pop .input popped <| .branch isPayload
      (.push .payload heldCell <| .goto (fun _ => .scan))
      (.branch present
        (.push .input held <| .goto (fun _ => .tally))
        (.goto (fun _ => .tally)))
  | .tally => .pop .input popped <| .branch present
      (.goto (fun _ => .carry))
      (.push .output (fun _ => none) <| .goto (fun _ => .emitCount))
  | .carry => .pop .count poppedBit <| .branch present
      (.branch heldBit
        (.push .work (fun _ => false) <| .goto (fun _ => .carry))
        (.push .count (fun _ => true) <| .goto (fun _ => .restore)))
      (.push .count (fun _ => true) <| .goto (fun _ => .restore))
  | .restore => .pop .work poppedBit <| .branch present
      (.push .count heldBit <| .goto (fun _ => .restore))
      (.goto (fun _ => .tally))
  | .emitCount => .pop .count poppedBit <| .branch present
      (.push .output (fun s => some (heldBit s)) <| .goto (fun _ => .emitCount))
      (.goto (fun _ => .restorePayload))
  | .restorePayload => .pop .payload poppedCell <| .branch present
      (.push .input (fun s => .inl (heldCell s)) <| .goto (fun _ => .restorePayload))
      (.goto (fun _ => .finish))
  | .finish => .pop .input popped <| .branch present
      (.push .output heldCell <| .goto (fun _ => .finish)) .halt

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

private def stackContents (input : List Tagged) (payload : List (Option Bool))
    (count work : List Bool) (output : List (Option Bool)) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .payload => payload | .count => count
  | .work => work | .output => output

private def cfg (label : Option Label) (state : State)
    (input : List Tagged) (payload : List (Option Bool))
    (count work : List Bool) (output : List (Option Bool)) : computer.Cfg :=
  ⟨label, state, stackContents input payload count work output⟩

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

local macro "binary_header_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, popped,
    poppedBit, poppedCell, present, isPayload, held, heldBit, heldCell, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

private def restore_run (work count : List Bool) (input : List Tagged)
    (payload output : List (Option Bool)) (state : State) :
    Run (cfg (some .restore) state input payload count work output)
      (cfg (some .tally) none input payload (work.reverse ++ count) [] output)
      (work.length + 1) := by
  induction work generalizing count state with
  | nil => exact one (by binary_header_step)
  | cons bit work ih =>
      have h : Run (cfg (some .restore) state input payload count (bit :: work) output)
          (cfg (some .restore) (some (.inr bit)) input payload (bit :: count) work output) 1 :=
        one (by cases bit <;> binary_header_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (bit :: count) (some (.inr bit)))

private def carry_run (bits acc : List Bool) (input : List Tagged)
    (payload output : List (Option Bool)) (state : State) :
    Run (cfg (some .carry) state input payload bits acc output)
      (cfg (some .tally) none input payload (acc.reverse ++ binarySuccBits bits) [] output)
      (2 * bits.length + acc.length + 2) := by
  induction bits generalizing acc state with
  | nil =>
      have h : Run (cfg (some .carry) state input payload [] acc output)
          (cfg (some .restore) none input payload [true] acc output) 1 :=
        one (by binary_header_step)
      simpa [binarySuccBits, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (restore_run acc [true] input payload output none)
  | cons bit bits ih =>
      cases bit with
      | false =>
          have h : Run (cfg (some .carry) state input payload (false :: bits) acc output)
              (cfg (some .restore) (some (.inr false)) input payload (true :: bits) acc output) 1 :=
            one (by binary_header_step)
          apply mono (by
            simpa [binarySuccBits] using
              seq h (restore_run acc (true :: bits) input payload output (some (.inr false))))
          simp only [List.length_cons]
          omega
      | true =>
          have h : Run (cfg (some .carry) state input payload (true :: bits) acc output)
              (cfg (some .carry) (some (.inr true)) input payload bits (false :: acc) output) 1 :=
            one (by binary_header_step)
          apply mono (by
            simpa only [binarySuccBits, List.reverse_cons, List.singleton_append,
              List.append_assoc] using seq h (ih (false :: acc) (some (.inr true))))
          simp only [List.length_cons]
          omega

private def tallyTime : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, current => 1 + (2 * (encodeNat current).length + 2) + tallyTime n (current + 1)

private def tally_run (n current : ℕ) (payload output : List (Option Bool)) (state : State) :
    Run (cfg (some .tally) state (List.replicate n (.inr true)) payload (encodeNat current) [] output)
      (cfg (some .emitCount) none [] payload (encodeNat (current + n)) [] (none :: output))
      (tallyTime n current) := by
  induction n generalizing current state with
  | zero => exact one (by binary_header_step)
  | succ n ih =>
      have h : Run
          (cfg (some .tally) state (List.replicate (n + 1) (.inr true)) payload (encodeNat current) [] output)
          (cfg (some .carry) (some (.inr true)) (List.replicate n (.inr true)) payload (encodeNat current) [] output) 1 :=
        one (by simp only [List.replicate_succ]; binary_header_step)
      have hc := carry_run (encodeNat current) [] (List.replicate n (.inr true)) payload output (some (.inr true))
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

private def scan_run (cells saved : List (Option Bool)) (n : ℕ) (state : State) :
    Run (cfg (some .scan) state (cells.map Sum.inl ++ List.replicate n (.inr true)) saved [] [] [])
      (cfg (some .tally) (List.replicate n (.inr true)).head?
        (List.replicate n (.inr true)) (cells.reverse ++ saved) [] [] [])
      (cells.length + 1) := by
  induction cells generalizing saved state with
  | nil =>
      apply one
      cases n <;> simp only [List.replicate_zero, List.replicate_succ] <;> binary_header_step
  | cons cell cells ih =>
      have h : Run
          (cfg (some .scan) state ((cell :: cells).map Sum.inl ++ List.replicate n (.inr true)) saved [] [] [])
          (cfg (some .scan) (some (.inl cell)) (cells.map Sum.inl ++ List.replicate n (.inr true))
            (cell :: saved) [] [] []) 1 := one (by binary_header_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (cell :: saved) (some (.inl cell)))

private def emitCount_run (bits : List Bool) (payload output : List (Option Bool)) (state : State) :
    Run (cfg (some .emitCount) state [] payload bits [] output)
      (cfg (some .restorePayload) none [] payload [] [] (bits.reverse.map some ++ output))
      (bits.length + 1) := by
  induction bits generalizing output state with
  | nil => exact one (by binary_header_step)
  | cons bit bits ih =>
      have h : Run (cfg (some .emitCount) state [] payload (bit :: bits) [] output)
          (cfg (some .emitCount) (some (.inr bit)) [] payload bits [] (some bit :: output)) 1 :=
        one (by cases bit <;> binary_header_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (ih (some bit :: output) (some (.inr bit)))

private def restorePayload_run (payload : List (Option Bool)) (input : List Tagged)
    (output : List (Option Bool)) (state : State) :
    Run (cfg (some .restorePayload) state input payload [] [] output)
      (cfg (some .finish) none (payload.reverse.map Sum.inl ++ input) [] [] [] output)
      (payload.length + 1) := by
  induction payload generalizing input state with
  | nil => exact one (by binary_header_step)
  | cons cell payload ih =>
      have h : Run (cfg (some .restorePayload) state input (cell :: payload) [] [] output)
          (cfg (some .restorePayload) (some (.inl cell)) (.inl cell :: input) payload [] [] output) 1 :=
        one (by binary_header_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (ih (.inl cell :: input) (some (.inl cell)))

private def finish_run (cells output : List (Option Bool)) (state : State) :
    Run (cfg (some .finish) state (cells.map Sum.inl) [] [] [] output)
      (cfg none none [] [] [] [] (cells.reverse ++ output)) (cells.length + 1) := by
  induction cells generalizing output state with
  | nil => exact one (by binary_header_step)
  | cons cell cells ih =>
      have h : Run (cfg (some .finish) state ((cell :: cells).map Sum.inl) [] [] [] output)
          (cfg (some .finish) (some (.inl cell)) (cells.map Sum.inl) [] [] [] (cell :: output)) 1 :=
        one (by binary_header_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (cell :: output) (some (.inl cell)))

private def run (cells : List (Option Bool)) (n : ℕ) :
    Run (cfg (some .scan) none (cells.map Sum.inl ++ List.replicate n (.inr true)) [] [] [] [])
      (cfg none none [] [] [] [] ((none :: (encodeNat n).map some ++ cells).reverse))
      (3 * cells.length + tallyTime n 0 + (encodeNat n).length + 4) := by
  have hs := scan_run cells [] n none
  have ht := tally_run n 0 cells.reverse [] (List.replicate n (.inr true)).head?
  simp only [List.append_nil] at hs
  simp only [Nat.zero_add, show encodeNat 0 = [] by simp [encodeNat, encodeNum]] at ht
  have he := emitCount_run (encodeNat n) cells.reverse [none] none
  have hp := restorePayload_run cells.reverse [] ((encodeNat n).reverse.map some ++ [none]) none
  simp only [List.reverse_reverse, List.append_nil] at hp
  have hf := finish_run cells ((encodeNat n).reverse.map some ++ [none]) none
  apply mono (by
    simpa only [List.reverse_cons, List.reverse_append, List.map_reverse,
      List.reverse_nil, List.append_assoc, List.nil_append] using
      seq (seq (seq (seq hs ht) he) hp) hf)
  simp only [List.length_reverse]
  omega

private theorem runTime_le (cells : List (Option Bool)) (n : ℕ) :
    3 * cells.length + tallyTime n 0 + (encodeNat n).length + 4 ≤
      8 * (cells.length + n + 1) ^ 2 := by
  have ht := tallyTime_le n 0
  have hb := BinaryNatLists.encodeNat_length_le n
  nlinarith

private theorem init_eq (input : List Tagged) :
    initList computer input = cfg (some .scan) none input [] [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List (Option Bool)) :
    haltList computer output = cfg none none [] [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

end StructuralBinaryHeaderMachine

/-- Convert the internally computed tally, insert the exact binary count, and
reverse into the existing raw structural format in at most `8(s+1)^2` steps. -/
def structuralBinaryHeader_outputsInTime (view : AllDifferentCSPEncoding.RuntimeStructuralView) :
    TM2OutputsInTime StructuralBinaryHeaderMachine.computer
      (StructuralCountedPayload.checkedFinEncoding.encode view)
      (some (RuntimeStructuralView.rawFinEncoding.encode view))
      (8 * ((StructuralCountedPayload.checkedFinEncoding.encode view).length + 1) ^ 2) := by
  rw [TM2OutputsInTime, StructuralBinaryHeaderMachine.init_eq]
  simp only [Option.map_some]
  rw [StructuralBinaryHeaderMachine.halt_eq]
  have h := StructuralBinaryHeaderMachine.mono
    (StructuralBinaryHeaderMachine.run (RuntimeStructuralView.payloadEncode view) (view.records.length + 1))
    (StructuralBinaryHeaderMachine.runTime_le (RuntimeStructuralView.payloadEncode view) (view.records.length + 1))
  simpa [StructuralCountedPayload.checkedFinEncoding, StructuralCountedPayload.encode_retain,
    RuntimeStructuralView.raw_encode_eq_count_payload, SourceOrderRawFields.encode] using h

noncomputable def structuralBinaryHeaderComputableInPolyTime :
    @TM2ComputableInPolyTime AllDifferentCSPEncoding.RuntimeStructuralView
      AllDifferentCSPEncoding.RuntimeStructuralView StructuralCountedPayload.checkedFinEncoding
      RuntimeStructuralView.rawFinEncoding id where
  tm := StructuralBinaryHeaderMachine.computer
  inputAlphabet := Equiv.refl StructuralBinaryHeaderMachine.Tagged
  outputAlphabet := Equiv.refl (Option Bool)
  time := 8 * (Polynomial.X + 1) ^ 2
  outputsFun view := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X]
      using structuralBinaryHeader_outputsInTime view

/-- Repackage the checked row-count machine under the redundant-count codec;
the tally is produced by the machine, not supplied as an assumption. -/
noncomputable def structuralRowCountCheckedComputableInPolyTime :
    @TM2ComputableInPolyTime AllDifferentCSPEncoding.RuntimeStructuralView
      AllDifferentCSPEncoding.RuntimeStructuralView RuntimeStructuralView.payloadFinEncoding
      StructuralCountedPayload.checkedFinEncoding id where
  tm := structuralRowCountComputableInPolyTime.tm
  inputAlphabet := structuralRowCountComputableInPolyTime.inputAlphabet
  outputAlphabet := structuralRowCountComputableInPolyTime.outputAlphabet
  time := structuralRowCountComputableInPolyTime.time
  outputsFun := structuralRowCountComputableInPolyTime.outputsFun

#print axioms StructuralCountedPayload.checkedDecode_encode
#print axioms StructuralBinaryHeaderMachine.computer
#print axioms structuralBinaryHeader_outputsInTime
#print axioms structuralBinaryHeaderComputableInPolyTime
#print axioms structuralRowCountCheckedComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
