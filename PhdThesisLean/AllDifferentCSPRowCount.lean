import PhdThesisLean.AllDifferentCSPAssemblyMachine

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-!
# Count and retain the complete structural payload

Traverse the checked row lengths with explicit binary countdowns. Save every
payload cell unchanged and emit one unary tally mark per row, including the
singleton variable header. The result uses the standard tagged pair encoding.
Binary header conversion and the original framing bridge are separate passes.
-/

namespace StructuralCountedPayload

/-- Pair the exact structural payload with its computed unary outer row count. -/
def finEncoding : FinEncoding (AllDifferentCSPEncoding.RuntimeStructuralView × ℕ) :=
  LeanNPHardness.PairEncoding.finEncoding
    RuntimeStructuralView.payloadFinEncoding unaryFinEncodingNat

def retain (view : AllDifferentCSPEncoding.RuntimeStructuralView) :
    AllDifferentCSPEncoding.RuntimeStructuralView × ℕ :=
  (view, view.records.length + 1)

@[simp]
theorem encode_retain (view : AllDifferentCSPEncoding.RuntimeStructuralView) :
    finEncoding.encode (retain view) =
      (RuntimeStructuralView.payloadEncode view).map Sum.inl ++
        List.replicate (view.records.length + 1) (.inr true) := by
  simp [finEncoding, LeanNPHardness.PairEncoding.finEncoding, retain,
    RuntimeStructuralView.payloadFinEncoding, unaryFinEncodingNat,
    unaryEncodeNat_eq_replicate_true]

end StructuralCountedPayload

namespace StructuralRowCountMachine

inductive Stack
  | input | count | work | scratch | output
  deriving DecidableEq, Fintype

inductive Label
  | start | readLength | restoreCount | checkCount
  | startValue | copyValue | pred | predCheck | predRestore | finish
  deriving DecidableEq, Fintype

abbrev State := Option (Option Bool)
abbrev OutputSymbol := Sum (Option Bool) Bool
abbrev Alphabet : Stack → Type
  | .output => OutputSymbol
  | _ => Option Bool
private def popped (_ : State) (symbol : State) : State := symbol
private def present : State → Bool | some _ => true | none => false
private def isBit : State → Bool | some (some _) => true | _ => false
private def bitTrue : State → Bool | some (some true) => true | _ => false
private def held : State → Option Bool | some symbol => symbol | none => none

/-- Preserve a looked-ahead delimiter and continue in the specified phase. -/
private def boundary (next : Label) : TM2.Stmt Alphabet Label State :=
  .branch present
    (.push .input held <| .goto (fun _ => next))
    (.goto (fun _ => next))

/-- Concrete finite control; no natural-number arithmetic is hidden in a step. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .start => .pop .input popped <| .branch present
      (.push .output (fun _ => .inr true) <|
        .push .scratch (fun _ => none) <| .goto (fun _ => .readLength))
      (.goto (fun _ => .finish))
  | .readLength => .pop .input popped <| .branch isBit
      (.push .work held <| .push .scratch held <| .goto (fun _ => .readLength))
      (boundary .restoreCount)
  | .restoreCount => .pop .work popped <| .branch present
      (.push .count held <| .goto (fun _ => .restoreCount))
      (.goto (fun _ => .checkCount))
  | .checkCount => .pop .count popped <| .branch present
      (.push .count held <| .goto (fun _ => .startValue))
      (.goto (fun _ => .start))
  | .startValue => .pop .input popped <|
      .push .scratch (fun _ => none) <| .goto (fun _ => .copyValue)
  | .copyValue => .pop .input popped <| .branch isBit
      (.push .scratch held <| .goto (fun _ => .copyValue))
      (boundary .pred)
  | .pred => .pop .count popped <| .branch present
      (.branch bitTrue (.goto (fun _ => .predCheck))
        (.push .work (fun _ => some true) <| .goto (fun _ => .pred)))
      (.goto (fun _ => .predRestore))
  | .predCheck => .pop .count popped <| .branch present
      (.push .count held <| .push .count (fun _ => some false) <|
        .goto (fun _ => .predRestore))
      (.goto (fun _ => .predRestore))
  | .predRestore => .pop .work popped <| .branch present
      (.push .count held <| .goto (fun _ => .predRestore))
      (.goto (fun _ => .checkCount))
  | .finish => .pop .scratch popped <| .branch present
      (.push .output (fun s => .inl (held s)) <| .goto (fun _ => .finish)) .halt

/-- Five finite-alphabet stacks; tally marks are emitted by a fixed push. -/
def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .start
  σ := State
  initialState := none
  Γk₀Fin := show Fintype (Option Bool) from inferInstance
  m := program

private def stackContents (input count work scratch : List (Option Bool))
    (output : List OutputSymbol) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .count => count | .work => work
  | .scratch => scratch | .output => output

private def cfg (label : Option Label) (state : State)
    (input count work scratch : List (Option Bool))
    (output : List OutputSymbol) : computer.Cfg :=
  ⟨label, state, stackContents input count work scratch output⟩

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

-- Reduce a single finite transition, including all stack updates.
local macro "row_count_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, popped,
    present, isBit, bitTrue, held, boundary, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

/-- A raw field ends either at a delimiter or at payload exhaustion. -/
private def Boundary : List (Option Bool) → Prop
  | [] => True | none :: _ => True | some _ :: _ => False

private theorem boundary_fields (fields : List ℕ) (tail : List (Option Bool))
    (htail : Boundary tail) : Boundary (SourceOrderRawFields.encode fields ++ tail) := by
  cases fields <;> simp [SourceOrderRawFields.encode, Boundary] at *
  exact htail

private def readLength_run (bits : List Bool) (tail count work scratch : List (Option Bool))
    (output : List OutputSymbol)
    (state : State) (htail : Boundary tail) :
    Run (cfg (some .readLength) state (bits.map some ++ tail) count work scratch output)
      (cfg (some .restoreCount) tail.head? tail count
        (bits.reverse.map some ++ work)
        (bits.reverse.map some ++ scratch) output)
      (bits.length + 1) := by
  induction bits generalizing work scratch state with
  | nil =>
      apply one
      cases tail with
      | nil => row_count_step
      | cons symbol tail =>
          cases symbol with
          | none => row_count_step
          | some bit => exact False.elim htail
  | cons bit bits ih =>
      have h : Run
          (cfg (some .readLength) state ((bit :: bits).map some ++ tail) count work scratch output)
          (cfg (some .readLength) (some (some bit)) (bits.map some ++ tail) count
            (some bit :: work) (some bit :: scratch) output) 1 := one (by cases bit <;> row_count_step)
      simpa [List.reverse_cons, List.reverse_append, List.map_append,
        List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (ih (some bit :: work) (some bit :: scratch) (some (some bit)))

private def restore_run (label : Label) (hlabel : label = .restoreCount ∨ label = .predRestore)
    (work input count scratch : List (Option Bool))
    (output : List OutputSymbol) (state : State) :
    Run (cfg (some label) state input count work scratch output)
      (cfg (some .checkCount) none input (work.reverse ++ count) [] scratch output)
      (work.length + 1) := by
  induction work generalizing count state with
  | nil =>
      apply one
      rcases hlabel with rfl | rfl <;> row_count_step
  | cons symbol work ih =>
      have h : Run (cfg (some label) state input count (symbol :: work) scratch output)
          (cfg (some label) (some symbol) input (symbol :: count) work scratch output) 1 := by
        apply one
        rcases hlabel with rfl | rfl <;> cases symbol <;> row_count_step
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (symbol :: count) (some symbol))

private def copyValue_run (bits : List Bool) (tail count work scratch : List (Option Bool))
    (output : List OutputSymbol)
    (state : State) (htail : Boundary tail) :
    Run (cfg (some .copyValue) state (bits.map some ++ tail) count work scratch output)
      (cfg (some .pred) tail.head? tail count work
        (bits.reverse.map some ++ scratch) output) (bits.length + 1) := by
  induction bits generalizing scratch state with
  | nil =>
      apply one
      cases tail with
      | nil => row_count_step
      | cons symbol tail =>
          cases symbol with
          | none => row_count_step
          | some bit => exact False.elim htail
  | cons bit bits ih =>
      have h : Run
          (cfg (some .copyValue) state ((bit :: bits).map some ++ tail) count work scratch output)
          (cfg (some .copyValue) (some (some bit)) (bits.map some ++ tail) count work
            (some bit :: scratch) output) 1 := one (by cases bit <;> row_count_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (some bit :: scratch) (some (some bit)))

private def pred_run (bits acc : List Bool) (input scratch : List (Option Bool))
    (output : List OutputSymbol)
    (state : State) :
    Run (cfg (some .pred) state input (bits.map some) (acc.map some) scratch output)
      (cfg (some .checkCount) none input ((acc.reverse ++ binaryPredBits bits).map some)
        [] scratch output) (2 * bits.length + acc.length + 2) := by
  induction bits generalizing acc state with
  | nil =>
      have h : Run (cfg (some .pred) state input [] (acc.map some) scratch output)
          (cfg (some .predRestore) none input [] (acc.map some) scratch output) 1 := one (by row_count_step)
      simpa [binaryPredBits, List.map_reverse, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (restore_run .predRestore (Or.inr rfl) (acc.map some) input [] scratch output none)
  | cons bit bits ih =>
      cases bit with
      | false =>
          have h : Run (cfg (some .pred) state input ((false :: bits).map some) (acc.map some) scratch output)
              (cfg (some .pred) (some (some false)) input (bits.map some) ((true :: acc).map some)
                scratch output) 1 := one (by row_count_step)
          apply mono (by
            simpa [binaryPredBits, List.reverse_cons, List.map_append, List.append_assoc] using
              seq h (ih (true :: acc) (some (some false))))
          simp
          omega
      | true =>
          have h : Run (cfg (some .pred) state input ((true :: bits).map some) (acc.map some) scratch output)
              (cfg (some .predCheck) (some (some true)) input (bits.map some) (acc.map some) scratch output)
              1 := one (by row_count_step)
          cases bits with
          | nil =>
              have hcheck : Run
                  (cfg (some .predCheck) (some (some true)) input [] (acc.map some) scratch output)
                  (cfg (some .predRestore) none input [] (acc.map some) scratch output) 1 := one (by row_count_step)
              apply mono (by
                simpa [binaryPredBits, List.map_reverse] using seq (seq h hcheck)
                  (restore_run .predRestore (Or.inr rfl) (acc.map some) input [] scratch output none))
              simp
              omega
          | cons next rest =>
              have hcheck : Run
                  (cfg (some .predCheck) (some (some true)) input ((next :: rest).map some)
                    (acc.map some) scratch output)
                  (cfg (some .predRestore) (some (some next)) input ((false :: next :: rest).map some)
                    (acc.map some) scratch output) 1 := one (by cases next <;> row_count_step)
              apply mono (by
                simpa [binaryPredBits, List.map_append, List.map_reverse] using seq (seq h hcheck)
                  (restore_run .predRestore (Or.inr rfl) (acc.map some) input
                    ((false :: next :: rest).map some) scratch output (some (some next))))
              simp
              omega

private theorem encode_zero : encodeNat 0 = [] := by
  unfold encodeNat
  change encodeNum (Num.ofNat' 0) = []
  rw [Num.ofNat'_zero]
  rfl

private theorem encode_succ_ne_nil (n : ℕ) : encodeNat (n + 1) ≠ [] := by
  intro h
  have hd := congrArg decodeNat h
  have hzero : decodeNat [] = 0 := rfl
  have : n + 1 = 0 := by simpa only [decode_encodeNat, hzero] using hd
  omega

private def valuesTime : List ℕ → ℕ
  | [] => 1
  | value :: values => (encodeNat value).length +
      2 * (encodeNat (values.length + 1)).length + 5 + valuesTime values

private def values_run (values : List ℕ) (tail scratch : List (Option Bool))
    (output : List OutputSymbol)
    (state : State) (htail : Boundary tail) :
    Run (cfg (some .checkCount) state (SourceOrderRawFields.encode values ++ tail)
        ((encodeNat values.length).map some) [] scratch output)
      (cfg (some .start) none tail [] []
        ((SourceOrderRawFields.encode values).reverse ++ scratch) output)
      (valuesTime values) := by
  induction values generalizing scratch state with
  | nil =>
      simp only [valuesTime, List.length_nil, encode_zero, List.map_nil,
        SourceOrderRawFields.encode, List.flatMap_nil, List.nil_append, List.reverse_nil]
      exact one (by row_count_step)
  | cons value values ih =>
      let count := (encodeNat (values.length + 1)).map some
      let after := SourceOrderRawFields.encode values ++ tail
      have hcount : count ≠ [] := by
        simpa [count] using encode_succ_ne_nil values.length
      have hcheck : Run
          (cfg (some .checkCount) state
            (none :: (encodeNat value).map some ++ after) count [] scratch output)
          (cfg (some .startValue) count.head?
            (none :: (encodeNat value).map some ++ after) count [] scratch output) 1 := by
        apply one
        cases hcountEq : count with
        | nil => exact False.elim (hcount hcountEq)
        | cons symbol count => cases symbol <;> row_count_step
      have hstart : Run
          (cfg (some .startValue) count.head?
            (none :: (encodeNat value).map some ++ after) count [] scratch output)
          (cfg (some .copyValue) (some none)
            ((encodeNat value).map some ++ after) count [] (none :: scratch) output) 1 :=
        one (by row_count_step)
      have hcopy := copyValue_run (encodeNat value) after count [] (none :: scratch)
        output (some none) (boundary_fields values tail htail)
      have hpred := pred_run (encodeNat (values.length + 1)) [] after
        ((encodeNat value).reverse.map some ++ none :: scratch) output after.head?
      have hprefix := seq (seq (seq hcheck hstart) hcopy) (by simpa [count] using hpred)
      have hrest := ih ((encodeNat value).reverse.map some ++ none :: scratch) none
      convert seq hprefix (by simpa [after, List.map_reverse] using hrest) using 1 <;>
        simp [valuesTime, SourceOrderRawFields.encode, count, after,
          List.reverse_append, List.append_assoc]
      omega

private def rowTime (values : List ℕ) : ℕ :=
  2 * (encodeNat values.length).length + 3 + valuesTime values

private def row_run (values : List ℕ) (tail scratch : List (Option Bool))
    (output : List OutputSymbol) (state : State) (htail : Boundary tail) :
    Run (cfg (some .start) state (ScopeFieldBlock.inputEncode values ++ tail) [] [] scratch output)
      (cfg (some .start) none tail [] []
        ((ScopeFieldBlock.inputEncode values).reverse ++ scratch) (.inr true :: output))
      (rowTime values) := by
  let bits := encodeNat values.length
  let after := SourceOrderRawFields.encode values ++ tail
  let staged := bits.reverse.map some ++ none :: scratch
  have hstart : Run
      (cfg (some .start) state (none :: bits.map some ++ after) [] [] scratch output)
      (cfg (some .readLength) (some none) (bits.map some ++ after) [] []
        (none :: scratch) (.inr true :: output)) 1 := one (by row_count_step)
  have hread := readLength_run bits after [] [] (none :: scratch) (.inr true :: output)
    (some none) (boundary_fields values tail htail)
  have hrestore := restore_run .restoreCount (Or.inl rfl)
    (bits.reverse.map some) after [] staged (.inr true :: output) after.head?
  have hprefix := seq (seq hstart hread) (by simpa [staged] using hrestore)
  have hvalues := values_run values tail staged (.inr true :: output) none htail
  convert seq hprefix
    (by simpa [bits, after, staged, List.reverse_append, List.append_assoc] using hvalues) using 1 <;>
    simp [rowTime, ScopeFieldBlock.inputEncode_eq, ScopeFieldBlock.fieldSegment,
      bits, after, List.reverse_append, List.append_assoc]
  omega

private def rowsTime (rows : List (List ℕ)) : ℕ := (rows.map rowTime).sum

private theorem boundary_rows (rows : List (List ℕ)) :
    Boundary (DomainFieldSection.rowPayloadEncode rows) := by
  cases rows <;> simp [DomainFieldSection.rowPayloadEncode,
    DomainFieldSection.rowFields, SourceOrderRawFields.encode, Boundary]

private def rows_run (rows : List (List ℕ)) (scratch : List (Option Bool)) (output : List OutputSymbol)
    (state : State) :
    Run (cfg (some .start) state (DomainFieldSection.rowPayloadEncode rows) [] [] scratch output)
      (cfg (some .start) (if rows = [] then state else none) [] [] []
        ((DomainFieldSection.rowPayloadEncode rows).reverse ++ scratch)
        (List.replicate rows.length (.inr true) ++ output))
      (rowsTime rows) := by
  induction rows generalizing scratch output state with
  | nil =>
      refine { steps := 0, evals_in_steps := ?_, steps_le_m := le_rfl }
      rfl
  | cons values rows ih =>
      have hrow := row_run values (DomainFieldSection.rowPayloadEncode rows) scratch output
        state (boundary_rows rows)
      have hrest := ih ((ScopeFieldBlock.inputEncode values).reverse ++ scratch)
        (.inr true :: output) none
      have hinput : DomainFieldSection.rowPayloadEncode (values :: rows) =
          ScopeFieldBlock.inputEncode values ++ DomainFieldSection.rowPayloadEncode rows := by
        simp [ScopeFieldSection.rowPayloadEncode_eq_block_inputs]
      have hstate : (if rows = [] then (none : State) else none) = none := by split <;> rfl
      rw [hstate] at hrest
      simpa [hinput, rowsTime, List.reverse_append, List.append_assoc,
        List.replicate_succ'] using seq hrow hrest

private def finish_run (scratch : List (Option Bool)) (output : List OutputSymbol) (state : State) :
    Run (cfg (some .finish) state [] [] [] scratch output)
      (cfg none none [] [] [] [] (scratch.reverse.map Sum.inl ++ output)) (scratch.length + 1) := by
  induction scratch generalizing output state with
  | nil => exact one (by row_count_step)
  | cons symbol scratch ih =>
      have h : Run (cfg (some .finish) state [] [] [] (symbol :: scratch) output)
          (cfg (some .finish) (some symbol) [] [] [] scratch (.inl symbol :: output)) 1 :=
        one (by cases symbol <;> row_count_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (.inl symbol :: output) (some symbol))

private def run (rows : List (List ℕ)) :
    Run (cfg (some .start) none (DomainFieldSection.rowPayloadEncode rows) [] [] [] [])
      (cfg none none [] [] [] []
        ((DomainFieldSection.rowPayloadEncode rows).map Sum.inl ++
          List.replicate rows.length (.inr true)))
      (rowsTime rows + (DomainFieldSection.rowPayloadEncode rows).length + 2) := by
  have hrows := rows_run rows [] [] none
  have hstate : (if rows = [] then (none : State) else none) = none := by split <;> rfl
  rw [hstate] at hrows
  have hstart : Run
      (cfg (some .start) none [] [] [] (DomainFieldSection.rowPayloadEncode rows).reverse
        (List.replicate rows.length (.inr true)))
      (cfg (some .finish) none [] [] [] (DomainFieldSection.rowPayloadEncode rows).reverse
        (List.replicate rows.length (.inr true))) 1 := one (by row_count_step)
  have hfinish := finish_run (DomainFieldSection.rowPayloadEncode rows).reverse
    (List.replicate rows.length (.inr true)) none
  convert seq (seq (by simpa using hrows) hstart) hfinish using 1 <;> simp
  omega

/-! The countdown cost is charged to explicitly present entry fields. -/

private def valueBits (values : List ℕ) : ℕ :=
  (values.map fun value => (encodeNat value).length).sum

private theorem valuesTime_le (values : List ℕ) :
    valuesTime values ≤ valueBits values + 2 * values.length ^ 2 + 7 * values.length + 1 := by
  induction values with
  | nil => simp [valuesTime, valueBits]
  | cons value values ih =>
      have hc := BinaryNatLists.encodeNat_length_le (values.length + 1)
      simp only [valuesTime, valueBits, List.map_cons, List.sum_cons,
        List.length_cons] at ih ⊢
      nlinarith

private def rowSize (values : List ℕ) : ℕ := (ScopeFieldBlock.inputEncode values).length

private theorem rowSize_eq (values : List ℕ) :
    rowSize values = (encodeNat values.length).length + values.length + valueBits values + 1 := by
  simp [rowSize, ScopeFieldBlock.inputEncode, SourceOrderRawFields.encode, valueBits]
  omega

private theorem rowTime_le (values : List ℕ) : rowTime values ≤ 12 * rowSize values ^ 2 := by
  have ht := valuesTime_le values
  have heq := rowSize_eq values
  have hc := BinaryNatLists.encodeNat_length_le values.length
  have hn : values.length ≤ rowSize values := by omega
  have hb : valueBits values ≤ rowSize values := by omega
  have hp : 1 ≤ rowSize values := by omega
  have hsq := Nat.pow_le_pow_left hn 2
  dsimp only [rowTime]
  nlinarith

private theorem rowsTime_le (rows : List (List ℕ)) :
    rowsTime rows ≤ 12 * (DomainFieldSection.rowPayloadEncode rows).length ^ 2 := by
  induction rows with
  | nil => simp [rowsTime, DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
      SourceOrderRawFields.encode]
  | cons values rows ih =>
      have ht := rowTime_le values
      have hinput : (DomainFieldSection.rowPayloadEncode (values :: rows)).length =
          rowSize values + (DomainFieldSection.rowPayloadEncode rows).length := by
        simp [ScopeFieldSection.rowPayloadEncode_eq_block_inputs, rowSize]
      simp only [rowsTime, List.map_cons, List.sum_cons] at ih ⊢
      rw [hinput]
      nlinarith

private theorem runTime_le (rows : List (List ℕ)) :
    rowsTime rows + (DomainFieldSection.rowPayloadEncode rows).length + 2 ≤
      20 * ((DomainFieldSection.rowPayloadEncode rows).length + 1) ^ 2 := by
  have hr := rowsTime_le rows
  nlinarith

private theorem init_eq (input : List (Option Bool)) :
    initList computer input = cfg (some .start) none input [] [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List OutputSymbol) :
    haltList computer output = cfg none none [] [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k <;> rfl

end StructuralRowCountMachine


/-- Preserve every payload cell and construct its complete outer row count in
at most `20(s+1)^2` steps, for actual payload bit/delimiter length `s`. -/
def structuralRowCount_outputsInTime (view : AllDifferentCSPEncoding.RuntimeStructuralView) :
    TM2OutputsInTime StructuralRowCountMachine.computer
      (RuntimeStructuralView.payloadEncode view)
      (some (StructuralCountedPayload.finEncoding.encode (StructuralCountedPayload.retain view)))
      (20 * ((RuntimeStructuralView.payloadEncode view).length + 1) ^ 2) := by
  rw [TM2OutputsInTime, StructuralRowCountMachine.init_eq]
  simp only [Option.map_some]
  rw [StructuralRowCountMachine.halt_eq]
  have h := StructuralRowCountMachine.mono (StructuralRowCountMachine.run view.toNatLists)
    (StructuralRowCountMachine.runTime_le view.toNatLists)
  simpa [StructuralCountedPayload.encode_retain, RuntimeStructuralView.payloadEncode,
    AllDifferentCSPEncoding.RuntimeStructuralView.toNatLists] using h

/-- A finite-machine witness for retaining the view and deriving the count;
no precomputed count is supplied to this pass. -/
noncomputable def structuralRowCountComputableInPolyTime :
    @TM2ComputableInPolyTime AllDifferentCSPEncoding.RuntimeStructuralView
      (AllDifferentCSPEncoding.RuntimeStructuralView × ℕ)
      RuntimeStructuralView.payloadFinEncoding StructuralCountedPayload.finEncoding
      StructuralCountedPayload.retain where
  tm := StructuralRowCountMachine.computer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl StructuralRowCountMachine.OutputSymbol
  time := 20 * (Polynomial.X + 1) ^ 2
  outputsFun view := by
    simpa [RuntimeStructuralView.payloadFinEncoding, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X]
      using structuralRowCount_outputsInTime view

#print axioms StructuralCountedPayload.encode_retain
#print axioms StructuralRowCountMachine.computer
#print axioms structuralRowCount_outputsInTime
#print axioms structuralRowCountComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
