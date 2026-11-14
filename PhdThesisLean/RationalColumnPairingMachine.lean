import PhdThesisLean.RationalRowResidual
import PhdThesisLean.RationalNormList

/-!
# Finite-machine pairing of separate row and certificate fields

The tagged input contains two delimited lists of original Boolean fraction
words. Routing reverses each list onto its own stack. Reading the lists from
the last field to the first then writes the paired-column output directly in
forward order. Unequal field counts clear every stack and return `[none]`.
This internal-format machine does not validate fraction words or decode the
original binary dimension/count headers.
-/
namespace PhdThesisLean.RationalColumnPairing.Machine

open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool
open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime
open StateTransition

set_option backward.isDefEq.respectTransparency false

abbrev Wire := Option Bool
inductive Stack | input | left | right | output deriving DecidableEq, Fintype
inductive Label | route | next | left | right | cleanLeft | cleanRight | cleanOutput
  deriving DecidableEq, Fintype
structure State where
  tagged : Option (Sum Wire Wire) := none
  first : Option Wire := none
  second : Option Wire := none
  deriving DecidableEq, Fintype

def initial : State := ⟨none, none, none⟩
def Alphabet : Stack → Type | .input => Sum Wire Wire | _ => Wire

def reset (next : TM2.Stmt Alphabet Label State) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => initial) next

def program : Label → TM2.Stmt Alphabet Label State
  | .route => .pop .input (fun s b => {s with tagged := b}) <|
      .branch (fun s => s.tagged.isSome)
        (.branch (fun s => (s.tagged.getD (.inl none)).isLeft)
          (.push .left (fun s => (s.tagged.getD (.inl none)).elim id id) <|
            reset <| .goto fun _ => .route)
          (.push .right (fun s => (s.tagged.getD (.inl none)).elim id id) <|
            reset <| .goto fun _ => .route))
        (reset <| .goto fun _ => .next)
  | .next => .pop .left (fun s b => {s with first := b}) <|
      .pop .right (fun s b => {s with second := b}) <|
      .branch (fun s => s.first.isSome)
        (.branch (fun s => s.second.isSome)
          (.push .output (fun _ => none) <| reset <| .goto fun _ => .right)
          (reset <| .goto fun _ => .cleanLeft))
        (.branch (fun s => s.second.isSome)
          (reset <| .goto fun _ => .cleanLeft)
          (reset .halt))
  | .left => .peek .left (fun s b => {s with first := b}) <|
      .branch (fun s => (s.first.getD none).isSome)
        (.pop .left (fun s _ => s) <| .push .output (fun s => s.first.getD none) <|
          reset <| .goto fun _ => .left)
        (reset <| .goto fun _ => .next)
  | .right => .peek .right (fun s b => {s with first := b}) <|
      .branch (fun s => (s.first.getD none).isSome)
        (.pop .right (fun s _ => s) <| .push .output (fun s => s.first.getD none) <|
          reset <| .goto fun _ => .right)
        (reset <| .goto fun _ => .left)
  | .cleanLeft => .pop .left (fun s b => {s with first := b}) <|
      .branch (fun s => s.first.isSome)
        (reset <| .goto fun _ => .cleanLeft)
        (reset <| .goto fun _ => .cleanRight)
  | .cleanRight => .pop .right (fun s b => {s with first := b}) <|
      .branch (fun s => s.first.isSome)
        (reset <| .goto fun _ => .cleanRight)
        (reset <| .goto fun _ => .cleanOutput)
  | .cleanOutput => .pop .output (fun s b => {s with first := b}) <|
      .branch (fun s => s.first.isSome)
        (reset <| .goto fun _ => .cleanOutput)
        (.push .output (fun _ => none) <| reset .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .route
  σ := State
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype (Sum Wire Wire))
  m := program

def contents (input : List (Sum Wire Wire)) (left right output : List Wire) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .left => left | .right => right | .output => output

def cfg (label : Option Label) (input : List (Sum Wire Wire))
    (left right output : List Wire) : computer.Cfg :=
  ⟨label, initial, contents input left right output⟩

abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time

def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using! h, steps_le_m := le_rfl }
def seq {a b c : computer.Cfg} {m n : ℕ} (h : Run a b m) (h' : Run b c n) :
    Run a c (m + n) := by
  simpa [Nat.add_comm] using! EvalsToInTime.trans computer.step m n a b (some c) h h'

local macro "machine_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, contents, Alphabet, initial, reset,
    Function.update]
   <;> first | rfl | (funext k; cases k <;> rfl)))

def route_left (bits : List Wire) (tail : List (Sum Wire Wire)) (left right output : List Wire) :
    Run (cfg (some .route) (bits.map Sum.inl ++ tail) left right output)
      (cfg (some .route) tail (bits.reverse ++ left) right output) bits.length := by
  induction bits generalizing left with
  | nil => exact { steps := 0, evals_in_steps := rfl, steps_le_m := le_rfl }
  | cons b bits ih =>
      have h : Run (cfg (some .route) ((Sum.inl b :: bits.map Sum.inl) ++ tail) left right output)
          (cfg (some .route) (bits.map Sum.inl ++ tail) (b :: left) right output) 1 :=
        one (by machine_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using seq h (ih (b :: left))

def route_right (bits : List Wire) (left right output : List Wire) :
    Run (cfg (some .route) (bits.map Sum.inr) left right output)
      (cfg (some .next) [] left (bits.reverse ++ right) output) (bits.length + 1) := by
  induction bits generalizing right with
  | nil => exact one (by machine_step)
  | cons b bits ih =>
      have h : Run (cfg (some .route) (Sum.inr b :: bits.map Sum.inr) left right output)
          (cfg (some .route) (bits.map Sum.inr) left (b :: right) output) 1 :=
        one (by machine_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (b :: right))

/-- A raw word field; no arithmetic or normalization is performed. -/
def field (bits : List Bool) : List Wire := bits.map some ++ [none]
def fields (words : List (List Bool)) : List Wire := words.flatMap field
/-- Reversed fields, with the last source field presented first. -/
def back (words : List (List Bool)) : List Wire := words.flatMap (fun w => (field w).reverse)

theorem back_cons (w : List Bool) (ws : List (List Bool)) :
    back (w :: ws) = none :: (w.reverse.map some ++ back ws) := by
  simp [back, field, List.reverse_append, List.map_reverse]

theorem back_reverse (ws : List (List Bool)) : back ws.reverse = (fields ws).reverse := by
  simp [back, fields, List.reverse_flatMap, Function.comp_def]

theorem back_length (ws : List (List Bool)) : (back ws).length = (fields ws).length := by
  simp [back, fields, List.length_flatMap]

theorem back_boundary (ws : List (List Bool)) : ((back ws).head?.getD none).isSome = false := by
  cases ws with
  | nil => rfl
  | cons w ws => simp [back_cons]

def right_run (bits : List Bool) (tail : List (List Bool)) (left output : List Wire) :
    Run (cfg (some .right) [] left (bits.map some ++ back tail) output)
      (cfg (some .left) [] left (back tail) (bits.reverse.map some ++ output))
      (bits.length + 1) := by
  induction bits generalizing output with
  | nil =>
      apply one
      cases tail <;> simp only [back, List.flatMap_nil, List.flatMap_cons, field,
        List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append]
      all_goals machine_step
  | cons b bits ih =>
      have h : Run (cfg (some .right) [] left (some b :: (bits.map some ++ back tail)) output)
          (cfg (some .right) [] left (bits.map some ++ back tail) (some b :: output)) 1 :=
        one (by machine_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using seq h (ih (some b :: output))

def left_run (bits : List Bool) (tail : List (List Bool)) (right output : List Wire) :
    Run (cfg (some .left) [] (bits.map some ++ back tail) right output)
      (cfg (some .next) [] (back tail) right (bits.reverse.map some ++ output))
      (bits.length + 1) := by
  induction bits generalizing output with
  | nil =>
      apply one
      cases tail <;> simp only [back, List.flatMap_nil, List.flatMap_cons, field,
        List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append]
      all_goals machine_step
  | cons b bits ih =>
      have h : Run (cfg (some .left) [] (some b :: (bits.map some ++ back tail)) right output)
          (cfg (some .left) [] (bits.map some ++ back tail) right (some b :: output)) 1 :=
        one (by machine_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using seq h (ih (some b :: output))

def cycle (a b : List Bool) (xs ys : List (List Bool)) (output : List Wire) :
    Run (cfg (some .next) [] (back (a :: xs)) (back (b :: ys)) output)
      (cfg (some .next) [] (back xs) (back ys) (field (a ++ b) ++ output))
      (a.length + b.length + 3) := by
  have hn : Run (cfg (some .next) [] (back (a :: xs)) (back (b :: ys)) output)
      (cfg (some .right) [] (a.reverse.map some ++ back xs)
        (b.reverse.map some ++ back ys) (none :: output)) 1 := by
    apply one
    simp only [back_cons]
    machine_step
  have hr := right_run b.reverse ys (a.reverse.map some ++ back xs) (none :: output)
  have hl := left_run a.reverse xs (back ys) (b.map some ++ none :: output)
  simp only [List.reverse_reverse, List.length_reverse] at hr hl
  convert seq hn (seq hr hl) using 1 <;>
    first | omega | simp [field, List.map_append, List.append_assoc]

/-- Pair equal-length lists, including all output construction and exhaustion. -/
def zip_run (xs ys : List (List Bool)) (h : xs.length = ys.length) (output : List Wire) :
    Run (cfg (some .next) [] (back xs) (back ys) output)
      (cfg none [] [] [] (fields ((xs.zipWith List.append ys).reverse) ++ output))
      ((fields xs).length + (fields ys).length + xs.length + 1) := by
  induction xs generalizing ys output with
  | nil =>
      have hy : ys = [] := by simpa using h.symm
      subst ys
      apply one
      simp only [back, fields, List.flatMap_nil, List.zipWith_nil_left, List.reverse_nil, List.nil_append]
      machine_step
  | cons a xs ih =>
      cases ys with
      | nil => simp at h
      | cons b ys =>
          have he : xs.length = ys.length := by simpa using h
          have hr := seq (cycle a b xs ys output) (ih ys he (field (a ++ b) ++ output))
          convert hr using 1
          · simp [fields, List.reverse_cons, List.append_assoc]
          · simp only [fields, List.flatMap_cons, List.length_append, field,
              List.length_map, List.length_cons, List.length_nil]
            omega

def clean_output (output : List Wire) :
    Run (cfg (some .cleanOutput) [] [] [] output) (cfg none [] [] [] [none])
      (output.length + 1) := by
  induction output with
  | nil => exact one (by machine_step)
  | cons b output ih =>
      have h : Run (cfg (some .cleanOutput) [] [] [] (b :: output))
          (cfg (some .cleanOutput) [] [] [] output) 1 := one (by machine_step)
      simpa [Nat.add_comm] using seq h ih

def clean_right (right output : List Wire) :
    Run (cfg (some .cleanRight) [] [] right output) (cfg none [] [] [] [none])
      (right.length + output.length + 2) := by
  induction right with
  | nil =>
      have h : Run (cfg (some .cleanRight) [] [] [] output)
          (cfg (some .cleanOutput) [] [] [] output) 1 := one (by machine_step)
      simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using seq h (clean_output output)
  | cons b right ih =>
      have h : Run (cfg (some .cleanRight) [] [] (b :: right) output)
          (cfg (some .cleanRight) [] [] right output) 1 := one (by machine_step)
      simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using seq h ih

def clean_left (left right output : List Wire) :
    Run (cfg (some .cleanLeft) [] left right output) (cfg none [] [] [] [none])
      (left.length + right.length + output.length + 3) := by
  induction left with
  | nil =>
      have h : Run (cfg (some .cleanLeft) [] [] right output)
          (cfg (some .cleanRight) [] [] right output) 1 := one (by machine_step)
      simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using seq h (clean_right right output)
  | cons b left ih =>
      have h : Run (cfg (some .cleanLeft) [] (b :: left) right output)
          (cfg (some .cleanLeft) [] left right output) 1 := one (by machine_step)
      simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using seq h ih

/-- Count mismatch is rejected with no binary count expansion or leftover output. -/
def mismatch_run (xs ys : List (List Bool)) (h : xs.length ≠ ys.length) (output : List Wire) :
    Run (cfg (some .next) [] (back xs) (back ys) output) (cfg none [] [] [] [none])
      (2 * ((fields xs).length + (fields ys).length) + output.length + 4) := by
  induction xs generalizing ys output with
  | nil =>
      cases ys with
      | nil => exact False.elim (h rfl)
      | cons b ys =>
          have hn : Run (cfg (some .next) [] [] (back (b :: ys)) output)
              (cfg (some .cleanLeft) [] [] (b.reverse.map some ++ back ys) output) 1 := by
            apply one
            simp only [back_cons]
            machine_step
          apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono
            (seq hn (clean_left [] (b.reverse.map some ++ back ys) output))
          simp only [fields, List.flatMap_cons, List.flatMap_nil, field, List.length_append,
            List.length_map, List.length_reverse, List.length_singleton, List.length_nil,
            back_length]
          omega
  | cons a xs ih =>
      cases ys with
      | nil =>
          have hn : Run (cfg (some .next) [] (back (a :: xs)) [] output)
              (cfg (some .cleanLeft) [] (a.reverse.map some ++ back xs) [] output) 1 := by
            apply one
            simp only [back_cons]
            machine_step
          apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono
            (seq hn (clean_left (a.reverse.map some ++ back xs) [] output))
          simp only [fields, List.flatMap_cons, List.flatMap_nil, field, List.length_append,
            List.length_map, List.length_reverse, List.length_singleton, List.length_nil,
            back_length]
          omega
      | cons b ys =>
          have he : xs.length ≠ ys.length := by simpa using h
          apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono
            (seq (cycle a b xs ys output) (ih ys he (field (a ++ b) ++ output)))
          simp only [fields, List.flatMap_cons, field, List.length_append,
            List.length_map, List.length_singleton]
          omega

def input (xs ys : List (List Bool)) : List (Sum Wire Wire) :=
  (fields xs).map Sum.inl ++ (fields ys).map Sum.inr

theorem input_length (xs ys : List (List Bool)) :
    (input xs ys).length = (fields xs).length + (fields ys).length := by simp [input]

def route_run (xs ys : List (List Bool)) :
    Run (cfg (some .route) (input xs ys) [] [] [])
      (cfg (some .next) [] (back xs.reverse) (back ys.reverse) [])
      ((input xs ys).length + 1) := by
  have hl := route_left (fields xs) ((fields ys).map Sum.inr) [] [] []
  simp only [List.append_nil] at hl
  have h := seq hl (route_right (fields ys) (fields xs).reverse [] [])
  simpa [input, back_reverse, Nat.add_assoc] using h

theorem fields_reverse_length (xs : List (List Bool)) :
    (fields xs.reverse).length = (fields xs).length := by
  rw [← back_length, back_reverse, List.length_reverse]

theorem count_le_length (xs : List (List Bool)) : xs.length ≤ (fields xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [fields, List.flatMap_cons, field, List.length_append, List.length_map,
        List.length_cons, List.length_nil] at *
      omega

theorem zip_reverse (xs ys : List (List Bool)) (h : xs.length = ys.length) :
    xs.reverse.zipWith List.append ys.reverse = (xs.zipWith List.append ys).reverse := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := by simpa using h.symm
      subst ys
      rfl
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          have he : xs.length = ys.length := by simpa using h
          simp only [List.reverse_cons, List.zipWith_cons_cons]
          rw [List.zipWith_append (by simpa using he), ih ys he]
          rfl

theorem init_eq (xs ys : List (List Bool)) :
    initList computer (input xs ys) = cfg (some .route) (input xs ys) [] [] [] := by
  unfold initList cfg; congr; funext k; cases k <;> rfl

theorem halt_eq (bits : List Wire) : haltList computer bits = cfg none [] [] [] bits := by
  unfold haltList cfg; congr; funext k; cases k <;> rfl

/-- Uniform linear time for successful pairing, in complete serialized input length. -/
def outputsInTime (xs ys : List (List Bool)) (h : xs.length = ys.length) :
    TM2OutputsInTime computer (input xs ys) (some (fields (xs.zipWith List.append ys)))
      (3 * (input xs ys).length + 2) := by
  have he : xs.reverse.length = ys.reverse.length := by simpa using h
  have hr := seq (route_run xs ys) (zip_run xs.reverse ys.reverse he [])
  have hz : (xs.reverse.zipWith List.append ys.reverse).reverse = xs.zipWith List.append ys := by
    rw [zip_reverse xs ys h, List.reverse_reverse]
  rw [hz] at hr
  simp only [List.append_nil, fields_reverse_length, List.length_reverse] at hr
  have hb := count_le_length xs
  have hr' := LeanNPHardness.MachinePrimitives.evalsToInTimeMono hr
    (show (input xs ys).length + 1 +
        ((fields xs).length + (fields ys).length + xs.length + 1) ≤
        3 * (input xs ys).length + 2 by rw [input_length]; omega)
  simpa only [TM2OutputsInTime, init_eq, halt_eq, Option.map_some] using! hr'

/-- Rejection includes clearing the partial paired output and both source tails. -/
def rejectsInTime (xs ys : List (List Bool)) (h : xs.length ≠ ys.length) :
    TM2OutputsInTime computer (input xs ys) (some [none])
      (3 * (input xs ys).length + 5) := by
  have he : xs.reverse.length ≠ ys.reverse.length := by simpa using h
  have hr := seq (route_run xs ys) (mismatch_run xs.reverse ys.reverse he [])
  have hr' := LeanNPHardness.MachinePrimitives.evalsToInTimeMono hr
    (show (input xs ys).length + 1 +
        (2 * ((fields xs.reverse).length + (fields ys.reverse).length) + [].length + 4) ≤
        3 * (input xs ys).length + 5 by
      simp only [fields_reverse_length, List.length_nil, input_length]; omega)
  simpa only [TM2OutputsInTime, init_eq, halt_eq, Option.map_some] using! hr'

end PhdThesisLean.RationalColumnPairing.Machine
