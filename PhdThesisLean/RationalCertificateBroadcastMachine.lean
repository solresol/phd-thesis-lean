import PhdThesisLean.RationalColumnPairing

/-!
# A finite machine reusing one certificate across all observations

The source contains one delimited certificate and runtime-many delimited row
words. Each row contains its response and separate coefficient fields. The
machine copies the certificate for each row and restores it before advancing.
It produces the exact separated row-input words for `RationalColumnPairing`.
This phase assumes the internal source format; it does not parse the original
binary dimension/count headers or validate fraction words.
-/
namespace PhdThesisLean.RationalCertificateBroadcast.Machine

open Computability Turing StateTransition
set_option backward.isDefEq.respectTransparency false

abbrev Wire := Option Bool
abbrev RowCell := Sum Bool Wire
abbrev Cell := Sum Bool (Sum Wire Wire)
abbrev Source := Sum Wire (Option RowCell)

def rowCell : RowCell → Cell | .inl b => .inl b | .inr b => .inr (.inl b)
def certCell (b : Wire) : Cell := .inr (.inr b)
def field (row : List RowCell) : List (Option RowCell) := row.map some ++ [none]
def fields (rows : List (List RowCell)) : List (Option RowCell) := rows.flatMap field
def input (cert : List Wire) (rows : List (List RowCell)) : List Source :=
  cert.map Sum.inl ++ (fields rows).map Sum.inr

def outputField (cert : List Wire) (row : List RowCell) : List (Option Cell) :=
  (row.map rowCell ++ cert.map certCell).map some ++ [none]
def output (cert : List Wire) (rows : List (List RowCell)) : List (Option Cell) :=
  rows.flatMap (outputField cert)

inductive Stack | input | certificate | saved | accumulated | output deriving DecidableEq, Fintype
inductive Label | load | restore (emit : Bool) | next | scan | copy | clear | finish
  deriving DecidableEq, Fintype
structure State where
  source : Option Source := none
  wire : Option Wire := none
  cell : Option (Option Cell) := none
  deriving DecidableEq, Fintype

def initial : State := ⟨none, none, none⟩
def Alphabet : Stack → Type
  | .input => Source
  | .certificate | .saved => Wire
  | .accumulated | .output => Option Cell

def reset (next : TM2.Stmt Alphabet Label State) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => initial) next

def program : Label → TM2.Stmt Alphabet Label State
  | .load => .peek .input (fun s b => {s with source := b}) <|
      .branch (fun s => s.source.any Sum.isLeft)
        (.pop .input (fun s _ => s) <|
          .push .saved (fun s => (s.source.getD (.inl none)).elim id (fun _ => none)) <|
          reset <| .goto fun _ => .load)
        (reset <| .goto fun _ => .restore false)
  | .restore emit => .pop .saved (fun s b => {s with wire := b}) <|
      .branch (fun s => s.wire.isSome)
        (.push .certificate (fun s => s.wire.getD none) <|
          reset <| .goto fun _ => .restore emit)
        (if emit then .push .accumulated (fun _ => none) <| reset <| .goto fun _ => .next
          else reset <| .goto fun _ => .next)
  | .next => .peek .input (fun s b => {s with source := b}) <|
      .branch (fun s => s.source.isSome)
        (reset <| .goto fun _ => .scan)
        (reset <| .goto fun _ => .clear)
  | .scan => .pop .input (fun s b => {s with source := b}) <|
      .branch (fun s => (s.source.getD (.inr none)).elim (fun _ => false) Option.isSome)
        (.push .accumulated (fun s => some (rowCell
          (((s.source.getD (.inr none)).elim (fun _ => none) id).getD (.inl false)))) <|
          reset <| .goto fun _ => .scan)
        (reset <| .goto fun _ => .copy)
  | .copy => .pop .certificate (fun s b => {s with wire := b}) <|
      .branch (fun s => s.wire.isSome)
        (.push .saved (fun s => s.wire.getD none) <|
          .push .accumulated (fun s => some (certCell (s.wire.getD none))) <|
          reset <| .goto fun _ => .copy)
        (reset <| .goto fun _ => .restore true)
  | .clear => .pop .certificate (fun s b => {s with wire := b}) <|
      .branch (fun s => s.wire.isSome)
        (reset <| .goto fun _ => .clear)
        (reset <| .goto fun _ => .finish)
  | .finish => .pop .accumulated (fun s b => {s with cell := b}) <|
      .branch (fun s => s.cell.isSome)
        (.push .output (fun s => s.cell.getD none) <|
          reset <| .goto fun _ => .finish)
        (reset .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .load
  σ := State
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype Source)
  m := program

def contents (input : List Source) (cert saved : List Wire) (acc out : List (Option Cell)) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .certificate => cert | .saved => saved
  | .accumulated => acc | .output => out

def cfg (label : Option Label) (input : List Source) (cert saved : List Wire)
    (acc out : List (Option Cell)) : computer.Cfg :=
  ⟨label, initial, contents input cert saved acc out⟩

abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time

def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using! h, steps_le_m := le_rfl }
def seq {a b c : computer.Cfg} {m n : ℕ} (h : Run a b m) (h' : Run b c n) :
    Run a c (m + n) := by
  simpa [Nat.add_comm] using! EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "machine_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, contents, Alphabet, initial, reset,
    Function.update, rowCell, certCell]
   <;> first | rfl | (funext k; cases k <;> rfl)))

/-- Read the certificate once. The first row cell stays on the source stack. -/
def load_run (cert saved : List Wire) (rows : List (List RowCell)) :
    Run (cfg (some .load) (input cert rows) [] saved [] [])
      (cfg (some (.restore false)) ((fields rows).map Sum.inr) []
        (cert.reverse ++ saved) [] []) (cert.length + 1) := by
  induction cert generalizing saved with
  | nil =>
      apply one
      cases h : fields rows with
      | nil => simp only [input, h]; machine_step
      | cons x xs => simp only [input, h]; machine_step
  | cons b cert ih =>
      have h : Run (cfg (some .load) (input (b :: cert) rows) [] saved [] [])
          (cfg (some .load) (input cert rows) [] (b :: saved) [] []) 1 := by
        apply one
        simp only [input, List.map_cons, List.cons_append]
        machine_step
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (b :: saved))

/-- Restoring reverses the temporary copy and optionally terminates a row. -/
def restore_run (emit : Bool) (saved cert : List Wire) (tail : List Source)
    (acc : List (Option Cell)) :
    Run (cfg (some (.restore emit)) tail cert saved acc [])
      (cfg (some .next) tail (saved.reverse ++ cert) []
        (if emit then none :: acc else acc) []) (saved.length + 1) := by
  induction saved generalizing cert with
  | nil => apply one; cases emit <;> machine_step
  | cons b saved ih =>
      have h : Run (cfg (some (.restore emit)) tail cert (b :: saved) acc [])
          (cfg (some (.restore emit)) tail (b :: cert) saved acc []) 1 := one (by machine_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (b :: cert))

def scan_run (row : List RowCell) (tail : List Source) (cert : List Wire)
    (acc : List (Option Cell)) :
    Run (cfg (some .scan) ((field row).map Sum.inr ++ tail) cert [] acc [])
      (cfg (some .copy) tail cert []
        ((row.map (fun b => some (rowCell b))).reverse ++ acc) []) (row.length + 1) := by
  induction row generalizing acc with
  | nil => apply one; simp only [field]; machine_step
  | cons b row ih =>
      have h : Run (cfg (some .scan) ((field (b :: row)).map Sum.inr ++ tail) cert [] acc [])
          (cfg (some .scan) ((field row).map Sum.inr ++ tail) cert []
            (some (rowCell b) :: acc) []) 1 := by
        apply one
        simp only [field, List.map_cons, List.cons_append]
        cases b <;> machine_step
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (some (rowCell b) :: acc))

/-- Each certificate symbol is copied to the row and to the restoration stack. -/
def copy_run (cert saved : List Wire) (tail : List Source) (acc : List (Option Cell)) :
    Run (cfg (some .copy) tail cert saved acc [])
      (cfg (some (.restore true)) tail [] (cert.reverse ++ saved)
        ((cert.map (fun b => some (certCell b))).reverse ++ acc) []) (cert.length + 1) := by
  induction cert generalizing saved acc with
  | nil => exact one (by machine_step)
  | cons b cert ih =>
      have h : Run (cfg (some .copy) tail (b :: cert) saved acc [])
          (cfg (some .copy) tail cert (b :: saved) (some (certCell b) :: acc) []) 1 :=
        one (by machine_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (b :: saved) (some (certCell b) :: acc))

def cycle (row : List RowCell) (rows : List (List RowCell)) (cert : List Wire)
    (acc : List (Option Cell)) :
    Run (cfg (some .next) ((fields (row :: rows)).map Sum.inr) cert [] acc [])
      (cfg (some .next) ((fields rows).map Sum.inr) cert []
        ((outputField cert row).reverse ++ acc) []) (row.length + 2 * cert.length + 4) := by
  have hn : Run (cfg (some .next) ((fields (row :: rows)).map Sum.inr) cert [] acc [])
      (cfg (some .scan) ((field row).map Sum.inr ++ (fields rows).map Sum.inr) cert [] acc []) 1 := by
    apply one
    cases row <;> simp only [fields, List.flatMap_cons, field, List.map_append,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    all_goals machine_step
  have hs := scan_run row ((fields rows).map Sum.inr) cert acc
  have hc := copy_run cert [] ((fields rows).map Sum.inr)
    ((row.map (fun b => some (rowCell b))).reverse ++ acc)
  have hr := restore_run true cert.reverse [] ((fields rows).map Sum.inr)
    ((cert.map (fun b => some (certCell b))).reverse ++
      (row.map (fun b => some (rowCell b))).reverse ++ acc)
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse, List.append_assoc, ↓reduceIte] at hc hr
  convert seq hn (seq hs (seq hc hr)) using 1 <;>
    first | omega | simp [outputField, List.reverse_append, List.map_append, List.map_map,
      Function.comp_def, List.append_assoc]

def clear_run (cert : List Wire) (acc : List (Option Cell)) :
    Run (cfg (some .clear) [] cert [] acc [])
      (cfg (some .finish) [] [] [] acc []) (cert.length + 1) := by
  induction cert with
  | nil => exact one (by machine_step)
  | cons b cert ih =>
      have h : Run (cfg (some .clear) [] (b :: cert) [] acc [])
          (cfg (some .clear) [] cert [] acc []) 1 := one (by machine_step)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using seq h ih

def finish_run (acc out : List (Option Cell)) :
    Run (cfg (some .finish) [] [] [] acc out)
      (cfg none [] [] [] [] (acc.reverse ++ out)) (acc.length + 1) := by
  induction acc generalizing out with
  | nil => exact one (by machine_step)
  | cons b acc ih =>
      have h : Run (cfg (some .finish) [] [] [] (b :: acc) out)
          (cfg (some .finish) [] [] [] acc (b :: out)) 1 := one (by machine_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (b :: out))

/-- The final certificate is cleared, along with every temporary stack. -/
def exit_run (cert : List Wire) (acc : List (Option Cell)) :
    Run (cfg (some .next) [] cert [] acc [])
      (cfg none [] [] [] [] acc.reverse) (cert.length + acc.length + 3) := by
  have hn : Run (cfg (some .next) [] cert [] acc [])
      (cfg (some .clear) [] cert [] acc []) 1 := one (by machine_step)
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    seq hn (seq (clear_run cert acc) (finish_run acc []))

theorem output_length (cert : List Wire) (rows : List (List RowCell)) :
    (output cert rows).length = (fields rows).length + rows.length * cert.length := by
  induction rows with
  | nil => simp [output, fields]
  | cons row rows ih =>
      simp only [output, fields, List.flatMap_cons, List.length_append, outputField, field,
        List.length_map, List.length_cons, List.length_nil] at *
      nlinarith

theorem count_le_length (rows : List (List RowCell)) : rows.length ≤ (fields rows).length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [fields, List.flatMap_cons, field, List.length_append, List.length_map,
        List.length_cons, List.length_nil] at *
      nlinarith

/-- Whole runtime-length traversal, with copying, restoration and final reversal. -/
def rows_run (rows : List (List RowCell)) (cert : List Wire) (acc : List (Option Cell)) :
    Run (cfg (some .next) ((fields rows).map Sum.inr) cert [] acc [])
      (cfg none [] [] [] [] (acc.reverse ++ output cert rows))
      ((fields rows).length + rows.length * (2 * cert.length + 3) + cert.length +
        (output cert rows).length + acc.length + 3) := by
  induction rows generalizing acc with
  | nil => simpa [fields, output] using exit_run cert acc
  | cons row rows ih =>
      have h := seq (cycle row rows cert acc) (ih ((outputField cert row).reverse ++ acc))
      convert h using 1
      · simp [output, List.reverse_append, List.append_assoc]
      · simp only [fields, output, List.flatMap_cons, List.length_append, List.length_reverse,
          field, outputField, List.length_map, List.length_cons, List.length_nil]
        ring

theorem init_eq (cert : List Wire) (rows : List (List RowCell)) :
    initList computer (input cert rows) = cfg (some .load) (input cert rows) [] [] [] [] := by
  unfold initList cfg; congr; funext k; cases k <;> rfl

theorem halt_eq (bits : List (Option Cell)) : haltList computer bits = cfg none [] [] [] [] bits := by
  unfold haltList cfg; congr; funext k; cases k <;> rfl

/-- Actual finite-machine steps, polynomial in the complete single-copy source. -/
def outputsInTime (cert : List Wire) (rows : List (List RowCell)) :
    TM2OutputsInTime computer (input cert rows) (some (output cert rows))
      (3 * (input cert rows).length ^ 2 + 8 * (input cert rows).length + 5) := by
  have hl := load_run cert [] rows
  have hr := restore_run false cert.reverse [] ((fields rows).map Sum.inr) []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse, Bool.false_eq_true,
    ↓reduceIte] at hl hr
  have h := seq hl (seq hr (rows_run rows cert []))
  have hc := count_le_length rows
  have hb := Nat.mul_le_mul hc (show cert.length ≤ cert.length + (fields rows).length by omega)
  have h' := LeanNPHardness.MachinePrimitives.evalsToInTimeMono h
    (show cert.length + 1 + (cert.length + 1 +
        ((fields rows).length + rows.length * (2 * cert.length + 3) + cert.length +
          (output cert rows).length + [].length + 3)) ≤
        3 * (input cert rows).length ^ 2 + 8 * (input cert rows).length + 5 by
      rw [output_length]
      simp only [input, List.length_append, List.length_map, List.length_nil]
      nlinarith)
  simpa only [TM2OutputsInTime, init_eq, halt_eq, Option.map_some, List.reverse_nil,
    List.nil_append] using! h'

end PhdThesisLean.RationalCertificateBroadcast.Machine
