import PhdThesisLean.AllDifferentCSPScopeSection

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-!
# Complete scope-section structural machine

The finite driver increments each binary row length, inserts the scope tag,
and copies exactly the counted number of fields before starting the next row.
It restores a delimiter after looking ahead, so empty rows and the final row
use the same control path. The count is decremented by explicit binary borrow;
all work stacks are empty at halt. Time is measured in raw bit/delimiter cells.
-/

namespace ScopeSectionMachine

inductive Stack
  | input | count | work | scratch | output
  deriving DecidableEq, Fintype

inductive Label
  | start | readCarry | readLength | restoreCount | checkCount
  | startValue | copyValue | pred | predCheck | predRestore | finish
  deriving DecidableEq, Fintype

abbrev State := Option (Option Bool)
abbrev Alphabet (_ : Stack) := Option Bool
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

/-- Tag insertion after the entire original count has been saved. -/
private def tag (carry : Bool) : TM2.Stmt Alphabet Label State :=
  let next := .push .scratch (fun _ => none) <|
    .push .scratch (fun _ => some true) <| boundary .restoreCount
  if carry then .push .scratch (fun _ => some true) next else next

/-- Concrete finite control; no natural-number arithmetic is hidden in a step. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .start => .pop .input popped <| .branch present
      (.push .scratch (fun _ => none) <| .goto (fun _ => .readCarry))
      (.goto (fun _ => .finish))
  | .readCarry => .pop .input popped <| .branch isBit
      (.push .work held <| .branch bitTrue
        (.push .scratch (fun _ => some false) <| .goto (fun _ => .readCarry))
        (.push .scratch (fun _ => some true) <| .goto (fun _ => .readLength)))
      (tag true)
  | .readLength => .pop .input popped <| .branch isBit
      (.push .work held <| .push .scratch held <| .goto (fun _ => .readLength))
      (tag false)
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
      (.push .output held <| .goto (fun _ => .finish)) .halt

/-- Five stacks over a three-symbol alphabet and finite control. -/
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

private def stackContents (input count work scratch output : List (Option Bool)) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .count => count | .work => work
  | .scratch => scratch | .output => output

private def cfg (label : Option Label) (state : State)
    (input count work scratch output : List (Option Bool)) : computer.Cfg :=
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
local macro "scope_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, popped,
    present, isBit, bitTrue, held, tag, boundary, Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

/-- A raw field ends either at a delimiter or at payload exhaustion. -/
private def Boundary : List (Option Bool) → Prop
  | [] => True | none :: _ => True | some _ :: _ => False

private theorem boundary_fields (fields : List ℕ) (tail : List (Option Bool))
    (htail : Boundary tail) : Boundary (SourceOrderRawFields.encode fields ++ tail) := by
  cases fields <;> simp [SourceOrderRawFields.encode, Boundary] at *
  exact htail

private def readLength_run (bits : List Bool) (tail count work scratch output : List (Option Bool))
    (state : State) (htail : Boundary tail) :
    Run (cfg (some .readLength) state (bits.map some ++ tail) count work scratch output)
      (cfg (some .restoreCount) tail.head? tail count
        (bits.reverse.map some ++ work)
        ((bits.map some ++ ScopeFieldBlock.tagSegment).reverse ++ scratch) output)
      (bits.length + 1) := by
  induction bits generalizing work scratch state with
  | nil =>
      apply one
      cases tail with
      | nil => scope_step
      | cons symbol tail =>
          cases symbol with
          | none => scope_step
          | some bit => exact False.elim htail
  | cons bit bits ih =>
      have h : Run
          (cfg (some .readLength) state ((bit :: bits).map some ++ tail) count work scratch output)
          (cfg (some .readLength) (some (some bit)) (bits.map some ++ tail) count
            (some bit :: work) (some bit :: scratch) output) 1 := one (by cases bit <;> scope_step)
      simpa [List.reverse_cons, List.reverse_append, List.map_append,
        List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (ih (some bit :: work) (some bit :: scratch) (some (some bit)))

private def readCarry_run (bits : List Bool) (tail count work scratch output : List (Option Bool))
    (state : State) (htail : Boundary tail) :
    Run (cfg (some .readCarry) state (bits.map some ++ tail) count work scratch output)
      (cfg (some .restoreCount) tail.head? tail count
        (bits.reverse.map some ++ work)
        (((binarySuccBits bits).map some ++ ScopeFieldBlock.tagSegment).reverse ++ scratch) output)
      (bits.length + 1) := by
  induction bits generalizing work scratch state with
  | nil =>
      apply one
      cases tail with
      | nil => scope_step
      | cons symbol tail =>
          cases symbol with
          | none => scope_step
          | some bit => exact False.elim htail
  | cons bit bits ih =>
      cases bit with
      | false =>
          have h : Run
              (cfg (some .readCarry) state ((false :: bits).map some ++ tail) count work scratch output)
              (cfg (some .readLength) (some (some false)) (bits.map some ++ tail) count
                (some false :: work) (some true :: scratch) output) 1 := one (by scope_step)
          simpa [binarySuccBits, List.reverse_cons, List.reverse_append, List.map_append,
            List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            seq h (readLength_run bits tail count (some false :: work)
              (some true :: scratch) output (some (some false)) htail)
      | true =>
          have h : Run
              (cfg (some .readCarry) state ((true :: bits).map some ++ tail) count work scratch output)
              (cfg (some .readCarry) (some (some true)) (bits.map some ++ tail) count
                (some true :: work) (some false :: scratch) output) 1 := one (by scope_step)
          simpa [binarySuccBits, List.reverse_cons, List.reverse_append, List.map_append,
            List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            seq h (ih (some true :: work) (some false :: scratch) (some (some true)))

private def restore_run (label : Label) (hlabel : label = .restoreCount ∨ label = .predRestore)
    (work input count scratch output : List (Option Bool)) (state : State) :
    Run (cfg (some label) state input count work scratch output)
      (cfg (some .checkCount) none input (work.reverse ++ count) [] scratch output)
      (work.length + 1) := by
  induction work generalizing count state with
  | nil =>
      apply one
      rcases hlabel with rfl | rfl <;> scope_step
  | cons symbol work ih =>
      have h : Run (cfg (some label) state input count (symbol :: work) scratch output)
          (cfg (some label) (some symbol) input (symbol :: count) work scratch output) 1 := by
        apply one
        rcases hlabel with rfl | rfl <;> cases symbol <;> scope_step
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (symbol :: count) (some symbol))

private def copyValue_run (bits : List Bool) (tail count work scratch output : List (Option Bool))
    (state : State) (htail : Boundary tail) :
    Run (cfg (some .copyValue) state (bits.map some ++ tail) count work scratch output)
      (cfg (some .pred) tail.head? tail count work
        (bits.reverse.map some ++ scratch) output) (bits.length + 1) := by
  induction bits generalizing scratch state with
  | nil =>
      apply one
      cases tail with
      | nil => scope_step
      | cons symbol tail =>
          cases symbol with
          | none => scope_step
          | some bit => exact False.elim htail
  | cons bit bits ih =>
      have h : Run
          (cfg (some .copyValue) state ((bit :: bits).map some ++ tail) count work scratch output)
          (cfg (some .copyValue) (some (some bit)) (bits.map some ++ tail) count work
            (some bit :: scratch) output) 1 := one (by cases bit <;> scope_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (some bit :: scratch) (some (some bit)))

private def pred_run (bits acc : List Bool) (input scratch output : List (Option Bool))
    (state : State) :
    Run (cfg (some .pred) state input (bits.map some) (acc.map some) scratch output)
      (cfg (some .checkCount) none input ((acc.reverse ++ binaryPredBits bits).map some)
        [] scratch output) (2 * bits.length + acc.length + 2) := by
  induction bits generalizing acc state with
  | nil =>
      have h : Run (cfg (some .pred) state input [] (acc.map some) scratch output)
          (cfg (some .predRestore) none input [] (acc.map some) scratch output) 1 := one (by scope_step)
      simpa [binaryPredBits, List.map_reverse, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (restore_run .predRestore (Or.inr rfl) (acc.map some) input [] scratch output none)
  | cons bit bits ih =>
      cases bit with
      | false =>
          have h : Run (cfg (some .pred) state input ((false :: bits).map some) (acc.map some) scratch output)
              (cfg (some .pred) (some (some false)) input (bits.map some) ((true :: acc).map some)
                scratch output) 1 := one (by scope_step)
          apply mono (by
            simpa [binaryPredBits, List.reverse_cons, List.map_append, List.append_assoc] using
              seq h (ih (true :: acc) (some (some false))))
          simp
          omega
      | true =>
          have h : Run (cfg (some .pred) state input ((true :: bits).map some) (acc.map some) scratch output)
              (cfg (some .predCheck) (some (some true)) input (bits.map some) (acc.map some) scratch output)
              1 := one (by scope_step)
          cases bits with
          | nil =>
              have hcheck : Run
                  (cfg (some .predCheck) (some (some true)) input [] (acc.map some) scratch output)
                  (cfg (some .predRestore) none input [] (acc.map some) scratch output) 1 := one (by scope_step)
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
                    (acc.map some) scratch output) 1 := one (by cases next <;> scope_step)
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

private def values_run (values : List ℕ) (tail scratch output : List (Option Bool))
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
      exact one (by scope_step)
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
        | cons symbol count => cases symbol <;> scope_step
      have hstart : Run
          (cfg (some .startValue) count.head?
            (none :: (encodeNat value).map some ++ after) count [] scratch output)
          (cfg (some .copyValue) (some none)
            ((encodeNat value).map some ++ after) count [] (none :: scratch) output) 1 :=
        one (by scope_step)
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

private def row_run (values : List ℕ) (tail scratch output : List (Option Bool))
    (state : State) (htail : Boundary tail) :
    Run (cfg (some .start) state (ScopeFieldBlock.inputEncode values ++ tail) [] [] scratch output)
      (cfg (some .start) none tail [] []
        ((ScopeFieldBlock.outputEncode values).reverse ++ scratch) output)
      (rowTime values) := by
  let bits := encodeNat values.length
  let after := SourceOrderRawFields.encode values ++ tail
  let staged := ((binarySuccBits bits).map some ++ ScopeFieldBlock.tagSegment).reverse ++ none :: scratch
  have hstart : Run
      (cfg (some .start) state (none :: bits.map some ++ after) [] [] scratch output)
      (cfg (some .readCarry) (some none) (bits.map some ++ after) [] [] (none :: scratch) output) 1 :=
    one (by scope_step)
  have hread := readCarry_run bits after [] [] (none :: scratch) output (some none)
    (boundary_fields values tail htail)
  have hrestore := restore_run .restoreCount (Or.inl rfl)
    (bits.reverse.map some) after [] staged output after.head?
  have hprefix := seq (seq hstart hread) (by simpa [staged] using hrestore)
  have hvalues := values_run values tail staged output none htail
  convert seq hprefix
    (by simpa [bits, after, staged, List.reverse_append, List.append_assoc] using hvalues) using 1 <;>
    simp [rowTime, ScopeFieldBlock.inputEncode_eq, ScopeFieldBlock.outputEncode_eq,
      ScopeFieldBlock.fieldSegment, bits, after, List.reverse_append, List.append_assoc]
  omega

private def rowsTime (scopes : List (List ℕ)) : ℕ := (scopes.map rowTime).sum

private theorem boundary_rows (scopes : List (List ℕ)) :
    Boundary (DomainFieldSection.rowPayloadEncode scopes) := by
  cases scopes <;> simp [DomainFieldSection.rowPayloadEncode,
    DomainFieldSection.rowFields, SourceOrderRawFields.encode, Boundary]

private def rows_run (scopes : List (List ℕ)) (scratch output : List (Option Bool))
    (state : State) :
    Run (cfg (some .start) state (DomainFieldSection.rowPayloadEncode scopes) [] [] scratch output)
      (cfg (some .start) (if scopes = [] then state else none) [] [] []
        ((ScopeFieldSection.outputEncode scopes).reverse ++ scratch) output)
      (rowsTime scopes) := by
  induction scopes generalizing scratch state with
  | nil =>
      refine { steps := 0, evals_in_steps := ?_, steps_le_m := le_rfl }
      rfl
  | cons values scopes ih =>
      have hrow := row_run values (DomainFieldSection.rowPayloadEncode scopes) scratch output
        state (boundary_rows scopes)
      have hrest := ih ((ScopeFieldBlock.outputEncode values).reverse ++ scratch) none
      have hinput : DomainFieldSection.rowPayloadEncode (values :: scopes) =
          ScopeFieldBlock.inputEncode values ++ DomainFieldSection.rowPayloadEncode scopes := by
        simp [ScopeFieldSection.rowPayloadEncode_eq_block_inputs]
      have hstate : (if scopes = [] then (none : State) else none) = none := by split <;> rfl
      rw [hstate] at hrest
      simpa [hinput, rowsTime, ScopeFieldSection.outputEncode, List.reverse_append,
        List.append_assoc] using seq hrow hrest

private def finish_run (scratch output : List (Option Bool)) (state : State) :
    Run (cfg (some .finish) state [] [] [] scratch output)
      (cfg none none [] [] [] [] (scratch.reverse ++ output)) (scratch.length + 1) := by
  induction scratch generalizing output state with
  | nil => exact one (by scope_step)
  | cons symbol scratch ih =>
      have h : Run (cfg (some .finish) state [] [] [] (symbol :: scratch) output)
          (cfg (some .finish) (some symbol) [] [] [] scratch (symbol :: output)) 1 :=
        one (by cases symbol <;> scope_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (symbol :: output) (some symbol))

private def run (scopes : List (List ℕ)) :
    Run (cfg (some .start) none (DomainFieldSection.rowPayloadEncode scopes) [] [] [] [])
      (cfg none none [] [] [] [] (ScopeFieldSection.outputEncode scopes))
      (rowsTime scopes + (ScopeFieldSection.outputEncode scopes).length + 2) := by
  have hrows := rows_run scopes [] [] none
  have hstate : (if scopes = [] then (none : State) else none) = none := by split <;> rfl
  rw [hstate] at hrows
  have hstart : Run
      (cfg (some .start) none [] [] [] (ScopeFieldSection.outputEncode scopes).reverse [])
      (cfg (some .finish) none [] [] [] (ScopeFieldSection.outputEncode scopes).reverse []) 1 :=
    one (by scope_step)
  have hfinish := finish_run (ScopeFieldSection.outputEncode scopes).reverse [] none
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

private theorem rowsTime_le (scopes : List (List ℕ)) :
    rowsTime scopes ≤ 12 * (DomainFieldSection.rowPayloadEncode scopes).length ^ 2 := by
  induction scopes with
  | nil => simp [rowsTime, DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
      SourceOrderRawFields.encode]
  | cons values scopes ih =>
      have ht := rowTime_le values
      have hinput : (DomainFieldSection.rowPayloadEncode (values :: scopes)).length =
          rowSize values + (DomainFieldSection.rowPayloadEncode scopes).length := by
        simp [ScopeFieldSection.rowPayloadEncode_eq_block_inputs, rowSize]
      simp only [rowsTime, List.map_cons, List.sum_cons] at ih ⊢
      rw [hinput]
      nlinarith

private theorem runTime_le (scopes : List (List ℕ)) :
    rowsTime scopes + (ScopeFieldSection.outputEncode scopes).length + 2 ≤
      20 * ((DomainFieldSection.rowPayloadEncode scopes).length + 1) ^ 2 := by
  have hr := rowsTime_le scopes
  have ho := ScopeFieldSection.outputEncode_length_le_linear scopes
  change (ScopeFieldSection.outputEncode scopes).length ≤
    4 * (DomainFieldSection.rowPayloadEncode scopes).length at ho
  nlinarith

private theorem init_eq (input : List (Option Bool)) :
    initList computer input = cfg (some .start) none input [] [] [] [] := by
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

end ScopeSectionMachine

/-- The exact complete scope stream is emitted in quadratic bit-level time,
including empty scopes, repeated scopes, repeated entries, and exhaustion. -/
def scopeSection_outputsInTime (scopes : List (List ℕ)) :
    TM2OutputsInTime ScopeSectionMachine.computer
      (DomainFieldSection.rowPayloadEncode scopes)
      (some (ScopeFieldSection.outputEncode scopes))
      (20 * ((DomainFieldSection.rowPayloadEncode scopes).length + 1) ^ 2) := by
  rw [TM2OutputsInTime, ScopeSectionMachine.init_eq]
  simp only [Option.map_some]
  rw [ScopeSectionMachine.halt_eq]
  exact ScopeSectionMachine.mono (ScopeSectionMachine.run scopes)
    (ScopeSectionMachine.runTime_le scopes)

/-- A genuine finite-machine witness for the identity on whole scope lists
between the checked source payload and exact tagged-output encodings. -/
noncomputable def scopeSectionComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ)) (List (List ℕ))
      ScopeFieldSection.rowPayloadFinEncoding ScopeFieldSection.outputFinEncoding id where
  tm := ScopeSectionMachine.computer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl (Option Bool)
  time := 20 * (Polynomial.X + 1) ^ 2
  outputsFun scopes := by
    simpa [ScopeFieldSection.rowPayloadFinEncoding, DomainFieldSection.rowPayloadFinEncoding,
      ScopeFieldSection.outputFinEncoding, Equiv.refl, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_natCast,
      Polynomial.eval_one, Polynomial.eval_X] using scopeSection_outputsInTime scopes

/-- Start from the complete counted section and construct the checked payload
inside the verified generic sequential composition. -/
noncomputable def completeScopeSectionComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ)) (List (List ℕ))
      ScopeFieldSection.inputFinEncoding ScopeFieldSection.outputFinEncoding id := by
  let composed := compositionComputableInPolyTime
    ScopeFieldSection.inputFinEncoding ScopeFieldSection.rowPayloadFinEncoding
    ScopeFieldSection.outputFinEncoding id id
    scopeRowPayloadStructuredComputableInPolyTime scopeSectionComputableInPolyTime
  exact { composed with
    outputsFun := fun scopes => by
      simpa [Function.comp_def] using composed.outputsFun scopes }

#print axioms ScopeSectionMachine.computer
#print axioms scopeSection_outputsInTime
#print axioms scopeSectionComputableInPolyTime
#print axioms completeScopeSectionComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
