import PhdThesisLean.AllDifferentCSPScopeMachine
import PhdThesisLean.AllDifferentCSPStructuralMachine
import LeanNPHardness.PairReductionComputable

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-!
# Split the complete source into checked domain and scope sections

The source is the existing source-order view of the actual compiler input.
The finite machine skips the outer list count and the singleton header length,
retains the domain count, and uses separate binary row and entry countdowns to
locate the domain/scope boundary. It emits the existing tagged pair encoding,
so a checked component machine can run while preserving the other section.
-/

namespace RuntimeSourceSections

/-- Reuse the checked full source-order representation at its runtime-system type. -/
def inputFinEncoding : FinEncoding RuntimeSystem where
  Γ := Option Bool
  encode C := SourceOrderRawNatLists.encode C.toNatLists
  decode bits := (SourceOrderRawNatLists.decode bits).bind RuntimeSystem.ofNatLists
  decode_encode C := by simp
  ΓFin := inferInstance

/-- Counted domains and exhaustion-delimited scopes, in the reusable tagged pair encoding. -/
def outputFinEncoding : FinEncoding (List (List ℕ) × List (List ℕ)) :=
  LeanNPHardness.PairEncoding.finEncoding DomainFieldSection.inputFinEncoding
    ScopeFieldSection.rowPayloadFinEncoding

/-- Splitting retains every row and entry in its original section. -/
def split (C : RuntimeSystem) : List (List ℕ) × List (List ℕ) :=
  (C.domains, C.scopes)

/-- The precise full source layout, including both fields removed by the splitter. -/
theorem inputEncode_eq_sections (C : RuntimeSystem) :
    inputFinEncoding.encode C =
      SourceOrderRawFields.encode [1 + C.domains.length + C.scopes.length, 1] ++
        DomainFieldSection.inputEncode C.domains ++
        DomainFieldSection.rowPayloadEncode C.scopes := by
  change SourceOrderRawNatLists.encode C.toNatLists = _
  rw [← DomainFieldSection.inputEncode_eq_sourceOrderRawNatLists]
  simp [RuntimeSystem.toNatLists, DomainFieldSection.inputEncode,
    DomainFieldSection.inputFields, DomainFieldSection.rowFields,
    DomainFieldSection.rowPayloadEncode, SourceOrderRawFields.encode,
    List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Splitting adds only finite alphabet tags and removes two source fields. -/
theorem output_length_le_input (C : RuntimeSystem) :
    (outputFinEncoding.encode (split C)).length ≤ (inputFinEncoding.encode C).length := by
  rw [inputEncode_eq_sections]
  simp [outputFinEncoding, split, LeanNPHardness.PairEncoding.finEncoding,
    DomainFieldSection.inputFinEncoding, DomainFieldSection.rowPayloadFinEncoding]

end RuntimeSourceSections

namespace SourceSectionMachine

inductive Counter
  | rows | values
  deriving DecidableEq, Fintype

inductive Stack
  | input | count (counter : Counter) | work | scratch | output
  deriving DecidableEq, Fintype

inductive Label
  | start | skipOuter | skipSingleton | startRow | startValue | copyValue
  | read (counter : Counter) | restore (counter : Counter) | check (counter : Counter)
  | pred (counter : Counter) | predCheck (counter : Counter) | predRestore (counter : Counter)
  | suffix | finish
  deriving DecidableEq, Fintype

abbrev Tagged := Sum (Option Bool) (Option Bool)
abbrev State := Option Tagged
abbrev Alphabet : Stack → Type
  | .scratch | .output => Tagged
  | _ => Option Bool
private def popped (_ : State) (symbol : Option (Option Bool)) : State := symbol.map Sum.inl
private def present : State → Bool | some _ => true | none => false
private def isBit : State → Bool | some (.inl (some _)) => true | _ => false
private def bitTrue : State → Bool | some (.inl (some true)) => true | _ => false
private def held : State → Option Bool | some (.inl symbol) => symbol | _ => none
private def tagged : State → Tagged | some symbol => symbol | none => .inl none

private def boundary (next : Label) : TM2.Stmt Alphabet Label State :=
  .branch present (.push .input held <| .goto (fun _ => next)) (.goto (fun _ => next))

/-- Every countdown and boundary decision is implemented in finite control. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .start => .pop .input popped <| .goto (fun _ => .skipOuter)
  | .skipOuter => .pop .input popped <| .branch isBit
      (.goto (fun _ => .skipOuter)) (.goto (fun _ => .skipSingleton))
  | .skipSingleton => .pop .input popped <| .branch isBit
      (.goto (fun _ => .skipSingleton))
      (.push .scratch (fun _ => .inl none) <| .goto (fun _ => .read .rows))
  | .read counter => .pop .input popped <| .branch isBit
      (.push .work held <| .push .scratch (fun s => .inl (held s)) <|
        .goto (fun _ => .read counter)) (boundary (.restore counter))
  | .restore counter => .pop (.work) popped <| .branch present
      (.push (.count counter) held <| .goto (fun _ => .restore counter))
      (.goto (fun _ => .check counter))
  | .check counter => .pop (.count counter) popped <| .branch present
      (.push (.count counter) held <| .goto (fun _ =>
        match counter with | .rows => .startRow | .values => .startValue))
      (.goto (fun _ => match counter with | .rows => .suffix | .values => .pred .rows))
  | .startRow => .pop .input popped <| .push .scratch (fun _ => .inl none) <|
      .goto (fun _ => .read .values)
  | .startValue => .pop .input popped <| .push .scratch (fun _ => .inl none) <|
      .goto (fun _ => .copyValue)
  | .copyValue => .pop .input popped <| .branch isBit
      (.push .scratch (fun s => .inl (held s)) <| .goto (fun _ => .copyValue))
      (boundary (.pred .values))
  | .pred counter => .pop (.count counter) popped <| .branch present
      (.branch bitTrue (.goto (fun _ => .predCheck counter))
        (.push .work (fun _ => some true) <| .goto (fun _ => .pred counter)))
      (.goto (fun _ => .predRestore counter))
  | .predCheck counter => .pop (.count counter) popped <| .branch present
      (.push (.count counter) held <| .push (.count counter) (fun _ => some false) <|
        .goto (fun _ => .predRestore counter))
      (.goto (fun _ => .predRestore counter))
  | .predRestore counter => .pop .work popped <| .branch present
      (.push (.count counter) held <| .goto (fun _ => .predRestore counter))
      (.goto (fun _ => .check counter))
  | .suffix => .pop .input popped <| .branch present
      (.push .scratch (fun s => .inr (held s)) <| .goto (fun _ => .suffix))
      (.goto (fun _ => .finish))
  | .finish => .pop .scratch (fun _ symbol => symbol) <| .branch present
      (.push .output tagged <| .goto (fun _ => .finish)) .halt

/-- Six finite-alphabet stacks, with separate binary row and entry counters. -/
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

private def stackContents (input rows values work : List (Option Bool))
    (scratch output : List Tagged) : (k : Stack) → List (Alphabet k)
  | .input => input | .count .rows => rows | .count .values => values
  | .work => work | .scratch => scratch | .output => output

private def cfg (label : Option Label) (state : State)
    (input rows values work : List (Option Bool)) (scratch output : List Tagged) : computer.Cfg :=
  ⟨label, state, stackContents input rows values work scratch output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) :=
  EvalsToInTime computer.step a (some b) time

private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }

private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

private def mono {a b : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (hle : m ≤ n) : Run a b n :=
  { steps := h.steps, evals_in_steps := h.evals_in_steps, steps_le_m := h.steps_le_m.trans hle }

local macro "split_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet, popped,
    present, isBit, bitTrue, held, tagged, boundary, Function.update]
   <;> first | rfl | (funext k; cases k with
     | count counter => cases counter <;> rfl
     | _ => rfl)))

private def Boundary : List (Option Bool) → Prop
  | [] => True | none :: _ => True | some _ :: _ => False

private theorem boundary_fields (fields : List ℕ) (tail : List (Option Bool))
    (htail : Boundary tail) : Boundary (SourceOrderRawFields.encode fields ++ tail) := by
  cases fields <;> simp [SourceOrderRawFields.encode, Boundary] at *
  exact htail

private theorem boundary_rows (rows : List (List ℕ)) :
    Boundary (DomainFieldSection.rowPayloadEncode rows) := by
  cases rows <;> simp [DomainFieldSection.rowPayloadEncode,
    DomainFieldSection.rowFields, SourceOrderRawFields.encode, Boundary]

private def read_run (counter : Counter) (bits : List Bool)
    (tail rows values work : List (Option Bool)) (scratch output : List Tagged)
    (state : State) (htail : Boundary tail) :
    Run (cfg (some (.read counter)) state (bits.map some ++ tail) rows values work scratch output)
      (cfg (some (.restore counter)) (tail.head?.map Sum.inl) tail rows values
        (bits.reverse.map some ++ work)
        ((bits.map (fun b => Sum.inl (some b))).reverse ++ scratch) output)
      (bits.length + 1) := by
  induction bits generalizing work scratch state with
  | nil =>
      apply one
      cases tail with
      | nil => split_step
      | cons symbol tail =>
          cases symbol with
          | none => split_step
          | some bit => exact False.elim htail
  | cons bit bits ih =>
      have h : Run
          (cfg (some (.read counter)) state ((bit :: bits).map some ++ tail) rows values work scratch output)
          (cfg (some (.read counter)) (some (.inl (some bit))) (bits.map some ++ tail) rows values
            (some bit :: work) (.inl (some bit) :: scratch) output) 1 :=
        one (by cases bit <;> split_step)
      simpa [List.reverse_cons, List.reverse_append, List.map_append,
        List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (ih (some bit :: work) (.inl (some bit) :: scratch) (some (.inl (some bit))))

/-- Put the selected counter in one argument so its binary loop is proved once. -/
private def ccfg (counter : Counter) (label : Option Label) (state : State)
    (input count other work : List (Option Bool)) (scratch output : List Tagged) : computer.Cfg :=
  match counter with
  | .rows => cfg label state input count other work scratch output
  | .values => cfg label state input other count work scratch output

private def restore_run (counter : Counter) (label : Label)
    (hlabel : label = .restore counter ∨ label = .predRestore counter)
    (work input count other : List (Option Bool)) (scratch output : List Tagged) (state : State) :
    Run (ccfg counter (some label) state input count other work scratch output)
      (ccfg counter (some (.check counter)) none input (work.reverse ++ count) other [] scratch output)
      (work.length + 1) := by
  induction work generalizing count state with
  | nil =>
      apply one
      rcases hlabel with rfl | rfl <;> cases counter <;> simp only [ccfg] <;> split_step
  | cons symbol work ih =>
      have h : Run (ccfg counter (some label) state input count other (symbol :: work) scratch output)
          (ccfg counter (some label) (some (.inl symbol)) input (symbol :: count) other work scratch output) 1 := by
        apply one
        rcases hlabel with rfl | rfl <;> cases counter <;> cases symbol <;>
          simp only [ccfg] <;> split_step
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (symbol :: count) (some (.inl symbol)))

private def copyValue_run (bits : List Bool) (tail rows values work : List (Option Bool))
    (scratch output : List Tagged) (state : State) (htail : Boundary tail) :
    Run (cfg (some .copyValue) state (bits.map some ++ tail) rows values work scratch output)
      (cfg (some (.pred .values)) (tail.head?.map Sum.inl) tail rows values work
        ((bits.map (fun b => Sum.inl (some b))).reverse ++ scratch) output) (bits.length + 1) := by
  induction bits generalizing scratch state with
  | nil =>
      apply one
      cases tail with
      | nil => split_step
      | cons symbol tail =>
          cases symbol with
          | none => split_step
          | some bit => exact False.elim htail
  | cons bit bits ih =>
      have h : Run
          (cfg (some .copyValue) state ((bit :: bits).map some ++ tail) rows values work scratch output)
          (cfg (some .copyValue) (some (.inl (some bit))) (bits.map some ++ tail) rows values work
            (.inl (some bit) :: scratch) output) 1 := one (by cases bit <;> split_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (.inl (some bit) :: scratch) (some (.inl (some bit))))

private def pred_run (counter : Counter) (bits acc : List Bool)
    (input other : List (Option Bool)) (scratch output : List Tagged)
    (state : State) :
    Run (ccfg counter (some (.pred counter)) state input (bits.map some) other (acc.map some) scratch output)
      (ccfg counter (some (.check counter)) none input ((acc.reverse ++ binaryPredBits bits).map some) other
        [] scratch output) (2 * bits.length + acc.length + 2) := by
  induction bits generalizing acc state with
  | nil =>
      have h : Run (ccfg counter (some (.pred counter)) state input [] other (acc.map some) scratch output)
          (ccfg counter (some (.predRestore counter)) none input [] other (acc.map some) scratch output) 1 := one (by cases counter <;> simp only [ccfg] <;> split_step)
      simpa [binaryPredBits, List.map_reverse, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (restore_run counter (.predRestore counter) (Or.inr rfl) (acc.map some) input [] other scratch output none)
  | cons bit bits ih =>
      cases bit with
      | false =>
          have h : Run (ccfg counter (some (.pred counter)) state input ((false :: bits).map some) other (acc.map some) scratch output)
              (ccfg counter (some (.pred counter)) (some (.inl (some false))) input (bits.map some) other ((true :: acc).map some)
                scratch output) 1 := one (by cases counter <;> simp only [ccfg] <;> split_step)
          apply mono (by
            simpa [binaryPredBits, List.reverse_cons, List.map_append, List.append_assoc] using
              seq h (ih (true :: acc) (some (.inl (some false)))))
          simp
          omega
      | true =>
          have h : Run (ccfg counter (some (.pred counter)) state input ((true :: bits).map some) other (acc.map some) scratch output)
              (ccfg counter (some (.predCheck counter)) (some (.inl (some true))) input (bits.map some) other (acc.map some) scratch output)
              1 := one (by cases counter <;> simp only [ccfg] <;> split_step)
          cases bits with
          | nil =>
              have hcheck : Run
                  (ccfg counter (some (.predCheck counter)) (some (.inl (some true))) input [] other (acc.map some) scratch output)
                  (ccfg counter (some (.predRestore counter)) none input [] other (acc.map some) scratch output) 1 := one (by cases counter <;> simp only [ccfg] <;> split_step)
              apply mono (by
                simpa [binaryPredBits, List.map_reverse] using seq (seq h hcheck)
                  (restore_run counter (.predRestore counter) (Or.inr rfl) (acc.map some) input [] other scratch output none))
              simp
              omega
          | cons next rest =>
              have hcheck : Run
                  (ccfg counter (some (.predCheck counter)) (some (.inl (some true))) input ((next :: rest).map some) other
                    (acc.map some) scratch output)
                  (ccfg counter (some (.predRestore counter)) (some (.inl (some next))) input ((false :: next :: rest).map some) other
                    (acc.map some) scratch output) 1 := one (by cases next <;> cases counter <;> simp only [ccfg] <;> split_step)
              apply mono (by
                simpa [binaryPredBits, List.map_append, List.map_reverse] using seq (seq h hcheck)
                  (restore_run counter (.predRestore counter) (Or.inr rfl) (acc.map some) input
                    ((false :: next :: rest).map some) other scratch output (some (.inl (some next)))))
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

private def values_run (values : List ℕ) (tail rows : List (Option Bool)) (scratch output : List Tagged)
    (state : State) (htail : Boundary tail) :
    Run (cfg (some (.check .values)) state (SourceOrderRawFields.encode values ++ tail)
        rows ((encodeNat values.length).map some) [] scratch output)
      (cfg (some (.pred .rows)) none tail rows [] []
        (((SourceOrderRawFields.encode values).map Sum.inl).reverse ++ scratch) output)
      (valuesTime values) := by
  induction values generalizing scratch state with
  | nil =>
      simp only [valuesTime, List.length_nil, encode_zero, List.map_nil,
        SourceOrderRawFields.encode, List.flatMap_nil, List.nil_append, List.reverse_nil]
      exact one (by split_step)
  | cons value values ih =>
      let count := (encodeNat (values.length + 1)).map some
      let after := SourceOrderRawFields.encode values ++ tail
      have hcount : count ≠ [] := by
        simpa [count] using encode_succ_ne_nil values.length
      have hcheck : Run
          (cfg (some (.check .values)) state
            (none :: (encodeNat value).map some ++ after) rows count [] scratch output)
          (cfg (some .startValue) (count.head?.map Sum.inl)
            (none :: (encodeNat value).map some ++ after) rows count [] scratch output) 1 := by
        apply one
        cases hcountEq : count with
        | nil => exact False.elim (hcount hcountEq)
        | cons symbol count => cases symbol <;> split_step
      have hstart : Run
          (cfg (some .startValue) (count.head?.map Sum.inl)
            (none :: (encodeNat value).map some ++ after) rows count [] scratch output)
          (cfg (some .copyValue) (some (.inl none))
            ((encodeNat value).map some ++ after) rows count [] (.inl none :: scratch) output) 1 :=
        one (by split_step)
      have hcopy := copyValue_run (encodeNat value) after rows count [] (.inl none :: scratch)
        output (some (.inl none)) (boundary_fields values tail htail)
      have hpred := pred_run .values (encodeNat (values.length + 1)) [] after rows
        (((encodeNat value).map (fun b => Sum.inl (some b))).reverse ++ .inl none :: scratch) output (after.head?.map Sum.inl)
      have hprefix := seq (seq (seq hcheck hstart) hcopy) (by simpa [ccfg, count] using hpred)
      have hrest := ih (((encodeNat value).map (fun b => Sum.inl (some b))).reverse ++ .inl none :: scratch) none
      convert seq hprefix (by simpa [after, List.map_reverse] using hrest) using 1 <;>
        simp [valuesTime, SourceOrderRawFields.encode, count, after,
          List.reverse_append, List.append_assoc, List.map_append, List.map_map, Function.comp_def]
      omega

private def rowTime (values : List ℕ) : ℕ :=
  2 * (encodeNat values.length).length + 3 + valuesTime values

private def row_run (values : List ℕ) (tail rows : List (Option Bool))
    (scratch output : List Tagged) (state : State) (htail : Boundary tail) :
    Run (cfg (some .startRow) state (ScopeFieldBlock.inputEncode values ++ tail) rows [] [] scratch output)
      (cfg (some (.pred .rows)) none tail rows [] []
        (((ScopeFieldBlock.inputEncode values).map Sum.inl).reverse ++ scratch) output)
      (rowTime values) := by
  let bits := encodeNat values.length
  let after := SourceOrderRawFields.encode values ++ tail
  let staged := ((bits.map (fun b => Sum.inl (some b))).reverse ++ .inl none :: scratch)
  have hstart : Run
      (cfg (some .startRow) state (none :: bits.map some ++ after) rows [] [] scratch output)
      (cfg (some (.read .values)) (some (.inl none)) (bits.map some ++ after) rows [] []
        (.inl none :: scratch) output) 1 := one (by split_step)
  have hread := read_run .values bits after rows [] [] (.inl none :: scratch) output
    (some (.inl none)) (boundary_fields values tail htail)
  have hrestore := restore_run .values (.restore .values) (Or.inl rfl)
    (bits.reverse.map some) after [] rows staged output (after.head?.map Sum.inl)
  have hprefix := seq (seq hstart hread) (by simpa [ccfg, staged] using hrestore)
  have hvalues := values_run values tail rows staged output none htail
  convert seq hprefix
    (by simpa [bits, after, staged, List.reverse_append, List.append_assoc] using hvalues) using 1 <;>
    simp [rowTime, ScopeFieldBlock.inputEncode_eq, ScopeFieldBlock.fieldSegment,
      bits, after, List.reverse_append, List.append_assoc, List.map_append,
      List.map_map, Function.comp_def]
  omega

private def rowsTime : List (List ℕ) → ℕ
  | [] => 1
  | row :: rows => rowTime row + 2 * (encodeNat (rows.length + 1)).length + 3 + rowsTime rows

private def rows_run (domains : List (List ℕ)) (tail : List (Option Bool))
    (scratch output : List Tagged) (state : State) (htail : Boundary tail) :
    Run (cfg (some (.check .rows)) state
        (DomainFieldSection.rowPayloadEncode domains ++ tail)
        ((encodeNat domains.length).map some) [] [] scratch output)
      (cfg (some .suffix) none tail [] [] []
        (((DomainFieldSection.rowPayloadEncode domains).map Sum.inl).reverse ++ scratch) output)
      (rowsTime domains) := by
  induction domains generalizing scratch state with
  | nil =>
      simp only [rowsTime, List.length_nil, encode_zero, List.map_nil,
        DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
        SourceOrderRawFields.encode, List.flatMap_nil, List.nil_append, List.reverse_nil]
      exact one (by split_step)
  | cons row domains ih =>
      let count := (encodeNat (domains.length + 1)).map some
      let after := DomainFieldSection.rowPayloadEncode domains ++ tail
      let staged := ((ScopeFieldBlock.inputEncode row).map Sum.inl).reverse ++ scratch
      have hcount : count ≠ [] := by simpa [count] using encode_succ_ne_nil domains.length
      have hcheck : Run
          (cfg (some (.check .rows)) state (ScopeFieldBlock.inputEncode row ++ after) count [] [] scratch output)
          (cfg (some .startRow) (count.head?.map Sum.inl)
            (ScopeFieldBlock.inputEncode row ++ after) count [] [] scratch output) 1 := by
        apply one
        cases hcountEq : count with
        | nil => exact False.elim (hcount hcountEq)
        | cons symbol count => cases symbol <;> split_step
      have hrow := row_run row after count scratch output (count.head?.map Sum.inl)
        (boundary_fields (DomainFieldSection.rowFields domains) tail htail)
      have hpred := pred_run .rows (encodeNat (domains.length + 1)) [] after [] staged output none
      have hprefix := seq (seq hcheck hrow) (by simpa [ccfg, count, staged] using hpred)
      have hrest := ih staged none
      have hinput : DomainFieldSection.rowPayloadEncode (row :: domains) =
          ScopeFieldBlock.inputEncode row ++ DomainFieldSection.rowPayloadEncode domains := by
        simp [ScopeFieldSection.rowPayloadEncode_eq_block_inputs]
      convert seq hprefix (by simpa [after] using hrest) using 1 <;>
        simp [hinput, rowsTime, staged, after, count, List.reverse_append, List.append_assoc, List.map_append]
      omega

private def skipSingleton_run (bits : List Bool) (tail : List (Option Bool))
    (state : State) :
    Run (cfg (some .skipSingleton) state (bits.map some ++ none :: tail) [] [] [] [] [])
      (cfg (some (.read .rows)) (some (.inl none)) tail [] [] [] [.inl none] [])
      (bits.length + 1) := by
  induction bits generalizing state with
  | nil => exact one (by split_step)
  | cons bit bits ih =>
      have h : Run
          (cfg (some .skipSingleton) state ((bit :: bits).map some ++ none :: tail) [] [] [] [] [])
          (cfg (some .skipSingleton) (some (.inl (some bit)))
            (bits.map some ++ none :: tail) [] [] [] [] []) 1 := one (by cases bit <;> split_step)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (ih (some (.inl (some bit))))

private def skipOuter_run (bits : List Bool) (tail : List (Option Bool)) (state : State) :
    Run (cfg (some .skipOuter) state (bits.map some ++ none :: tail) [] [] [] [] [])
      (cfg (some .skipSingleton) (some (.inl none)) tail [] [] [] [] [])
      (bits.length + 1) := by
  induction bits generalizing state with
  | nil => exact one (by split_step)
  | cons bit bits ih =>
      have h : Run
          (cfg (some .skipOuter) state ((bit :: bits).map some ++ none :: tail) [] [] [] [] [])
          (cfg (some .skipOuter) (some (.inl (some bit)))
            (bits.map some ++ none :: tail) [] [] [] [] []) 1 := one (by cases bit <;> split_step)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (ih (some (.inl (some bit))))

private def suffix_run (input : List (Option Bool)) (scratch output : List Tagged) (state : State) :
    Run (cfg (some .suffix) state input [] [] [] scratch output)
      (cfg (some .finish) none [] [] [] [] ((input.map Sum.inr).reverse ++ scratch) output)
      (input.length + 1) := by
  induction input generalizing scratch state with
  | nil => exact one (by split_step)
  | cons symbol input ih =>
      have h : Run (cfg (some .suffix) state (symbol :: input) [] [] [] scratch output)
          (cfg (some .suffix) (some (.inl symbol)) input [] [] [] (.inr symbol :: scratch) output) 1 :=
        one (by cases symbol <;> split_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (.inr symbol :: scratch) (some (.inl symbol)))

private def finish_run (scratch output : List Tagged) (state : State) :
    Run (cfg (some .finish) state [] [] [] [] scratch output)
      (cfg none none [] [] [] [] [] (scratch.reverse ++ output)) (scratch.length + 1) := by
  induction scratch generalizing output state with
  | nil => exact one (by split_step)
  | cons symbol scratch ih =>
      have h : Run (cfg (some .finish) state [] [] [] [] (symbol :: scratch) output)
          (cfg (some .finish) (some symbol) [] [] [] [] scratch (symbol :: output)) 1 :=
        one (by split_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (symbol :: output) (some symbol))
private def runTime (C : RuntimeSystem) : ℕ :=
  (encodeNat (1 + C.domains.length + C.scopes.length)).length +
    (encodeNat 1).length + 2 * (encodeNat C.domains.length).length + 5 +
    rowsTime C.domains + (DomainFieldSection.rowPayloadEncode C.scopes).length +
    (RuntimeSourceSections.outputFinEncoding.encode (RuntimeSourceSections.split C)).length + 2

private def run (C : RuntimeSystem) :
    Run (cfg (some .start) none (RuntimeSourceSections.inputFinEncoding.encode C) [] [] [] [] [])
      (cfg none none [] [] [] [] []
        (RuntimeSourceSections.outputFinEncoding.encode (RuntimeSourceSections.split C)))
      (runTime C) := by
  let outer := encodeNat (1 + C.domains.length + C.scopes.length)
  let singleton := encodeNat 1
  let count := encodeNat C.domains.length
  let payload := DomainFieldSection.rowPayloadEncode C.domains ++
    DomainFieldSection.rowPayloadEncode C.scopes
  let source := none :: outer.map some ++ none :: singleton.map some ++ none :: count.map some ++ payload
  let header : List Tagged := (.inl none :: count.map (fun b => .inl (some b))).reverse
  let domainOutput := ((DomainFieldSection.rowPayloadEncode C.domains).map Sum.inl).reverse ++ header
  let output := RuntimeSourceSections.outputFinEncoding.encode (RuntimeSourceSections.split C)
  have hinput : RuntimeSourceSections.inputFinEncoding.encode C = source := by
    rw [RuntimeSourceSections.inputEncode_eq_sections]
    simp [source, outer, singleton, count, payload, SourceOrderRawFields.encode,
      DomainFieldSection.inputEncode, DomainFieldSection.inputFields,
      DomainFieldSection.rowPayloadEncode, List.append_assoc]
  have houtput : output.reverse =
      ((DomainFieldSection.rowPayloadEncode C.scopes).map Sum.inr).reverse ++ domainOutput := by
    simp [output, RuntimeSourceSections.outputFinEncoding, RuntimeSourceSections.split,
      LeanNPHardness.PairEncoding.finEncoding, DomainFieldSection.inputFinEncoding,
      DomainFieldSection.rowPayloadFinEncoding, DomainFieldSection.inputEncode,
      DomainFieldSection.inputFields, DomainFieldSection.rowPayloadEncode,
      SourceOrderRawFields.encode, domainOutput, header, count, List.reverse_append,
      List.append_assoc, List.map_append, List.map_map, Function.comp_def]
  have houtputForward : RuntimeSourceSections.outputFinEncoding.encode
      (RuntimeSourceSections.split C) = domainOutput.reverse ++
        (DomainFieldSection.rowPayloadEncode C.scopes).map Sum.inr := by
    have h := congrArg List.reverse houtput
    simpa [output] using h
  have hstart : Run (cfg (some .start) none source [] [] [] [] [])
      (cfg (some .skipOuter) (some (.inl none))
        (outer.map some ++ none :: singleton.map some ++ none :: count.map some ++ payload)
        [] [] [] [] []) 1 := one (by simp only [source]; split_step)
  have houter := skipOuter_run outer
    (singleton.map some ++ none :: count.map some ++ payload) (some (.inl none))
  have hsingleton := skipSingleton_run singleton (count.map some ++ payload) (some (.inl none))
  have hread := read_run .rows count payload [] [] [] [.inl none] [] (some (.inl none))
    (boundary_fields (DomainFieldSection.rowFields C.domains)
      (DomainFieldSection.rowPayloadEncode C.scopes) (boundary_rows C.scopes))
  have hrestore := restore_run .rows (.restore .rows) (Or.inl rfl)
    (count.reverse.map some) payload [] [] header [] (payload.head?.map Sum.inl)
  simp only [List.append_assoc, List.cons_append] at hstart houter hsingleton
  have hprefix := seq (seq (seq (seq hstart houter) hsingleton) hread)
    (by simpa [ccfg, header, List.reverse_cons] using hrestore)
  have hrows := rows_run C.domains (DomainFieldSection.rowPayloadEncode C.scopes)
    header [] none (boundary_rows C.scopes)
  have hdomains := seq hprefix (by simpa [payload, count, header, List.reverse_cons] using hrows)
  have hsuffix := suffix_run (DomainFieldSection.rowPayloadEncode C.scopes) domainOutput [] none
  have hfinish := finish_run output.reverse [] none
  have hlast := seq hsuffix (by simpa [houtput] using hfinish)
  convert seq hdomains (by simpa [domainOutput, header, List.reverse_cons] using hlast) using 1 <;>
    simp [hinput, runTime, houtputForward, domainOutput, header, outer, singleton, count,
      List.reverse_append, List.append_assoc]
  omega

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

private theorem rowsTime_le (domains : List (List ℕ)) :
    rowsTime domains ≤ 12 * (DomainFieldSection.rowPayloadEncode domains).length ^ 2 +
      2 * domains.length ^ 2 + 5 * domains.length + 1 := by
  induction domains with
  | nil => simp [rowsTime, DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
      SourceOrderRawFields.encode]
  | cons row domains ih =>
      have ht := rowTime_le row
      have hc := BinaryNatLists.encodeNat_length_le (domains.length + 1)
      have hinput : (DomainFieldSection.rowPayloadEncode (row :: domains)).length =
          rowSize row + (DomainFieldSection.rowPayloadEncode domains).length := by
        simp [ScopeFieldSection.rowPayloadEncode_eq_block_inputs, rowSize]
      simp only [rowsTime, List.length_cons] at ih ⊢
      rw [hinput]
      nlinarith

private theorem runTime_le (C : RuntimeSystem) :
    runTime C ≤ 40 * ((RuntimeSourceSections.inputFinEncoding.encode C).length + 1) ^ 2 := by
  let s := (RuntimeSourceSections.inputFinEncoding.encode C).length
  have hsize : s = (encodeNat (1 + C.domains.length + C.scopes.length)).length +
      (encodeNat 1).length + (encodeNat C.domains.length).length +
      (DomainFieldSection.rowPayloadEncode C.domains).length +
      (DomainFieldSection.rowPayloadEncode C.scopes).length + 3 := by
    dsimp [s]
    rw [RuntimeSourceSections.inputEncode_eq_sections]
    simp [SourceOrderRawFields.encode, DomainFieldSection.inputEncode,
      DomainFieldSection.inputFields, DomainFieldSection.rowPayloadEncode]
    omega
  have hr := rowsTime_le C.domains
  have hn := ScopeFieldSection.length_le_rowPayloadEncode_length C.domains
  have ho := RuntimeSourceSections.output_length_le_input C
  have hd : (DomainFieldSection.rowPayloadEncode C.domains).length ≤ s := by omega
  have hcount : C.domains.length ≤ s := by omega
  have hd2 := Nat.pow_le_pow_left hd 2
  have hn2 := Nat.pow_le_pow_left hcount 2
  change _ ≤ 40 * (s + 1) ^ 2
  dsimp only [runTime]
  change _ ≤ s at ho
  nlinarith

private theorem init_eq (input : List (Option Bool)) :
    initList computer input = cfg (some .start) none input [] [] [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k with
  | count counter => cases counter <;> rfl
  | _ => rfl

private theorem halt_eq (output : List Tagged) :
    haltList computer output = cfg none none [] [] [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k with
  | count counter => cases counter <;> rfl
  | _ => rfl

end SourceSectionMachine

/-- Exact splitting from the full raw source, including empty sections and rows,
in quadratic time in the actual bit/delimiter input length. -/
def sourceSections_outputsInTime (C : RuntimeSystem) :
    TM2OutputsInTime SourceSectionMachine.computer
      (RuntimeSourceSections.inputFinEncoding.encode C)
      (some (RuntimeSourceSections.outputFinEncoding.encode (RuntimeSourceSections.split C)))
      (40 * ((RuntimeSourceSections.inputFinEncoding.encode C).length + 1) ^ 2) := by
  rw [TM2OutputsInTime, SourceSectionMachine.init_eq]
  simp only [Option.map_some]
  rw [SourceSectionMachine.halt_eq]
  exact SourceSectionMachine.mono (SourceSectionMachine.run C) (SourceSectionMachine.runTime_le C)

/-- A finite-machine split into the existing checked pair of section encodings. -/
noncomputable def sourceSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem (List (List ℕ) × List (List ℕ))
      RuntimeSourceSections.inputFinEncoding RuntimeSourceSections.outputFinEncoding
      RuntimeSourceSections.split where
  tm := SourceSectionMachine.computer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl SourceSectionMachine.Tagged
  time := 40 * (Polynomial.X + 1) ^ 2
  outputsFun C := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_natCast, Polynomial.eval_one,
      Polynomial.eval_X] using sourceSections_outputsInTime C

/-- Reuse the complete checked compiler-to-source machine at the runtime-system type. -/
noncomputable def runtimeCompilerSourceSystemComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem RuntimeSystem
      RuntimeCompilerInput.finEncoding RuntimeSourceSections.inputFinEncoding id where
  toTM2ComputableAux := runtimeCompilerSourceOrderFieldsComputableInPolyTime.toTM2ComputableAux
  time := runtimeCompilerSourceOrderFieldsComputableInPolyTime.time
  outputsFun C := runtimeCompilerSourceOrderFieldsComputableInPolyTime.outputsFun C

/-- The actual compiler input produces both checked sections internally. -/
noncomputable def runtimeCompilerSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem (List (List ℕ) × List (List ℕ))
      RuntimeCompilerInput.finEncoding RuntimeSourceSections.outputFinEncoding
      RuntimeSourceSections.split := by
  let composed := compositionComputableInPolyTime
    RuntimeCompilerInput.finEncoding RuntimeSourceSections.inputFinEncoding
    RuntimeSourceSections.outputFinEncoding id RuntimeSourceSections.split
    runtimeCompilerSourceSystemComputableInPolyTime sourceSectionsComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa [Function.comp_def] using composed.outputsFun C }

/-- Expand all domains while preserving every scope through the checked generic pair-left API. -/
noncomputable def pairedDomainSectionComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ) × List (List ℕ))
      (List (ℕ × ℕ) × List (List ℕ)) RuntimeSourceSections.outputFinEncoding
      (LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
        ScopeFieldSection.rowPayloadFinEncoding)
      (fun sections => (RuntimeStructuralView.indexedDomainOccurrences sections.1, sections.2)) :=
  LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    DomainFieldSection.inputFinEncoding DomainFieldRow.outputFinEncoding
    ScopeFieldSection.rowPayloadFinEncoding RuntimeStructuralView.indexedDomainOccurrences
    completeDomainSectionComputableInPolyTime

/-- Full compiler input to exact indexed domain output paired with untouched scopes. -/
noncomputable def runtimeCompilerDomainAndScopesComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem (List (ℕ × ℕ) × List (List ℕ))
      RuntimeCompilerInput.finEncoding
      (LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
        ScopeFieldSection.rowPayloadFinEncoding)
      (fun C => (RuntimeStructuralView.indexedDomainOccurrences C.domains, C.scopes)) := by
  let composed := compositionComputableInPolyTime RuntimeCompilerInput.finEncoding
    RuntimeSourceSections.outputFinEncoding
    (LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding
      ScopeFieldSection.rowPayloadFinEncoding) RuntimeSourceSections.split
    (fun sections => (RuntimeStructuralView.indexedDomainOccurrences sections.1, sections.2))
    runtimeCompilerSectionsComputableInPolyTime pairedDomainSectionComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa [Function.comp_def, RuntimeSourceSections.split] using composed.outputsFun C }

#print axioms RuntimeSourceSections.inputEncode_eq_sections
#print axioms RuntimeSourceSections.output_length_le_input
#print axioms SourceSectionMachine.computer
#print axioms sourceSections_outputsInTime
#print axioms sourceSectionsComputableInPolyTime
#print axioms runtimeCompilerSectionsComputableInPolyTime
#print axioms pairedDomainSectionComputableInPolyTime
#print axioms runtimeCompilerDomainAndScopesComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
