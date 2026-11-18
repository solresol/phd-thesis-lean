import PhdThesisLean.RationalFractionPrefixMachine

/-!
# Payload-bounded expansion of a binary count

After the checked natural-prefix parser, this finite machine converts a count
into unary only when it is at most the length of the retained payload. Binary
Horner evaluation consumes a payload-sized budget before allocating each mark.
Oversized counts reject and clear all stacks, without expanding their value.
-/
namespace PhdThesisLean.BoundedBinaryCount.Machine

open Computability Turing StateTransition
open LeanNPHardness
set_option backward.isDefEq.respectTransparency false

inductive Stack | input | bits | budget | count | temp | saved | output
  deriving DecidableEq, Fintype
inductive Label
  | header | digits | payload | next | double (bit : Bool) | restore (bit : Bool)
  | add (bit : Bool) | clearBudget | finishPayload | finishCount
  | rejectBits | rejectBudget | rejectCount | rejectTemp | rejectSaved
  deriving DecidableEq, Fintype
abbrev State := Option (Option Bool)
def Alphabet : Stack → Type
  | .input | .output => Option Bool
  | _ => Bool

def go (l : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => none) (.goto fun _ => l)
def stop : TM2.Stmt Alphabet Label State := .load (fun _ => none) .halt
def readBit (_ : State) (b : Option Bool) : State := b.map some
def bit (s : State) : Bool := (s.getD none).getD false

def program : Label → TM2.Stmt Alphabet Label State
  | .header => .pop .input (fun _ b => b) <| .branch Option.isSome
      (.branch bit (go .header) (go .digits)) stop
  | .digits => .pop .input (fun _ b => b) <| .branch (fun s => (s.getD none).isSome)
      (.push .bits bit (go .digits)) (go .payload)
  | .payload => .pop .input (fun _ b => b) <| .branch Option.isSome
      (.push .saved bit <| .push .budget (fun _ => true) (go .payload)) (go .next)
  | .next => .pop .bits readBit <| .branch Option.isSome
      (.branch bit (go (.double true)) (go (.double false))) (go .clearBudget)
  | .double b => .pop .count readBit <| .branch Option.isSome
      (.pop .budget readBit <| .branch Option.isSome
        (.push .temp (fun _ => true) <| .push .temp (fun _ => true) (go (.double b)))
        (go .rejectBits))
      (go (.restore b))
  | .restore b => .pop .temp readBit <| .branch Option.isSome
      (.push .count (fun _ => true) (go (.restore b))) (go (.add b))
  | .add false => go .next
  | .add true => .pop .budget readBit <| .branch Option.isSome
      (.push .count (fun _ => true) (go .next)) (go .rejectBits)
  | .clearBudget => .pop .budget readBit <| .branch Option.isSome
      (go .clearBudget) (go .finishPayload)
  | .finishPayload => .pop .saved readBit <| .branch Option.isSome
      (.push .output (fun s => some (bit s)) (go .finishPayload))
      (.push .output (fun _ => none) (go .finishCount))
  | .finishCount => .pop .count readBit <| .branch Option.isSome
      (.push .output (fun _ => some true) (go .finishCount)) stop
  | .rejectBits => .pop .bits readBit <| .branch Option.isSome
      (go .rejectBits) (go .rejectBudget)
  | .rejectBudget => .pop .budget readBit <| .branch Option.isSome
      (go .rejectBudget) (go .rejectCount)
  | .rejectCount => .pop .count readBit <| .branch Option.isSome
      (go .rejectCount) (go .rejectTemp)
  | .rejectTemp => .pop .temp readBit <| .branch Option.isSome
      (go .rejectTemp) (go .rejectSaved)
  | .rejectSaved => .pop .saved readBit <| .branch Option.isSome
      (go .rejectSaved) stop

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .header
  σ := State
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := program

def contents (input : List (Option Bool)) (bits : List Bool)
    (budget count temp : ℕ) (saved : List Bool) (out : List (Option Bool)) :
    (k : Stack) → List (Alphabet k)
  | .input => input | .bits => bits | .budget => List.replicate budget true
  | .count => List.replicate count true | .temp => List.replicate temp true
  | .saved => saved | .output => out

def cfg (label : Option Label) (input : List (Option Bool)) (bits : List Bool)
    (budget count temp : ℕ) (saved : List Bool) (out : List (Option Bool)) : computer.Cfg :=
  ⟨label, none, contents input bits budget count temp saved out⟩
abbrev Run (a b : computer.Cfg) (t : ℕ) := EvalsToInTime computer.step a (some b) t

def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using! h, steps_le_m := le_rfl }
def seq {a b c : computer.Cfg} {m n : ℕ} (h : Run a b m) (h' : Run b c n) :
    Run a c (m+n) := by
  simpa [Nat.add_comm] using! EvalsToInTime.trans computer.step m n a b (some c) h h'
def mono {a b : computer.Cfg} {m n : ℕ} (h : Run a b m) (hm : m ≤ n) : Run a b n :=
  MachinePrimitives.evalsToInTimeMono h hm

local macro "machine_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, contents, Alphabet, go, stop,
    readBit, bit, Function.update, List.replicate_succ]
   <;> first | rfl | (funext k; cases k <;> rfl)))

def halt (out : List (Option Bool)) : computer.Cfg := cfg none [] [] 0 0 0 [] out

def rejectSaved_run (saved : List Bool) :
    Run (cfg (some .rejectSaved) [] [] 0 0 0 saved []) (halt []) (saved.length+1) := by
  induction saved with
  | nil => apply one; unfold halt; machine_step
  | cons b bs ih =>
      have h : Run (cfg (some .rejectSaved) [] [] 0 0 0 (b::bs) [])
          (cfg (some .rejectSaved) [] [] 0 0 0 bs []) 1 := one (by machine_step)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h ih

def rejectTemp_run (t : ℕ) (saved : List Bool) :
    Run (cfg (some .rejectTemp) [] [] 0 0 t saved []) (halt [])
      (t+saved.length+2) := by
  induction t with
  | zero =>
      have h : Run (cfg (some .rejectTemp) [] [] 0 0 0 saved [])
          (cfg (some .rejectSaved) [] [] 0 0 0 saved []) 1 := one (by machine_step)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (rejectSaved_run saved)
  | succ t ih =>
      have h : Run (cfg (some .rejectTemp) [] [] 0 0 (t+1) saved [])
          (cfg (some .rejectTemp) [] [] 0 0 t saved []) 1 := one (by machine_step)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h ih

def rejectCount_run (v t : ℕ) (saved : List Bool) :
    Run (cfg (some .rejectCount) [] [] 0 v t saved []) (halt [])
      (v+t+saved.length+3) := by
  induction v with
  | zero =>
      have h : Run (cfg (some .rejectCount) [] [] 0 0 t saved [])
          (cfg (some .rejectTemp) [] [] 0 0 t saved []) 1 := one (by machine_step)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (rejectTemp_run t saved)
  | succ v ih =>
      have h : Run (cfg (some .rejectCount) [] [] 0 (v+1) t saved [])
          (cfg (some .rejectCount) [] [] 0 v t saved []) 1 := one (by machine_step)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h ih

def rejectBudget_run (u v t : ℕ) (saved : List Bool) :
    Run (cfg (some .rejectBudget) [] [] u v t saved []) (halt [])
      (u+v+t+saved.length+4) := by
  induction u with
  | zero =>
      have h : Run (cfg (some .rejectBudget) [] [] 0 v t saved [])
          (cfg (some .rejectCount) [] [] 0 v t saved []) 1 := one (by machine_step)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (rejectCount_run v t saved)
  | succ u ih =>
      have h : Run (cfg (some .rejectBudget) [] [] (u+1) v t saved [])
          (cfg (some .rejectBudget) [] [] u v t saved []) 1 := one (by machine_step)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h ih

def reject_run (bits : List Bool) (u v t : ℕ) (saved : List Bool) :
    Run (cfg (some .rejectBits) [] bits u v t saved []) (halt [])
      (bits.length+u+v+t+saved.length+5) := by
  induction bits with
  | nil =>
      have h : Run (cfg (some .rejectBits) [] [] u v t saved [])
          (cfg (some .rejectBudget) [] [] u v t saved []) 1 := one (by machine_step)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (rejectBudget_run u v t saved)
  | cons b bs ih =>
      have h : Run (cfg (some .rejectBits) [] (b::bs) u v t saved [])
          (cfg (some .rejectBits) [] bs u v t saved []) 1 := one (by machine_step)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h ih

def double_run (b : Bool) (bits : List Bool) (u v t : ℕ) (saved : List Bool)
    (h : v ≤ u) :
    Run (cfg (some (.double b)) [] bits u v t saved [])
      (cfg (some (.restore b)) [] bits (u-v) 0 (t+2*v) saved []) (v+1) := by
  induction v generalizing u t with
  | zero => apply one; simpa using (show computer.step (cfg (some (.double b)) [] bits u 0 t saved []) =
        some (cfg (some (.restore b)) [] bits u 0 t saved []) by machine_step)
  | succ v ih =>
      cases u with
      | zero => omega
      | succ u =>
          have hs : Run (cfg (some (.double b)) [] bits (u+1) (v+1) t saved [])
              (cfg (some (.double b)) [] bits u v (t+2) saved []) 1 := one (by machine_step)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add]
            using seq hs (ih u (t+2) (by omega))

def double_overflow (b : Bool) (bits : List Bool) (u v t : ℕ) (saved : List Bool)
    (h : u < v) :
    Run (cfg (some (.double b)) [] bits u v t saved []) (halt [])
      (bits.length+2*u+v+t+saved.length+6) := by
  induction u generalizing v t with
  | zero =>
      cases v with
      | zero => omega
      | succ v =>
          have hs : Run (cfg (some (.double b)) [] bits 0 (v+1) t saved [])
              (cfg (some .rejectBits) [] bits 0 v t saved []) 1 := one (by machine_step)
          apply mono (seq hs (reject_run bits 0 v t saved))
          omega
  | succ u ih =>
      cases v with
      | zero => omega
      | succ v =>
          have hs : Run (cfg (some (.double b)) [] bits (u+1) (v+1) t saved [])
              (cfg (some (.double b)) [] bits u v (t+2) saved []) 1 := one (by machine_step)
          apply mono (seq hs (ih v (t+2) (by omega)))
          omega

def restore_run (b : Bool) (bits : List Bool) (u v t : ℕ) (saved : List Bool) :
    Run (cfg (some (.restore b)) [] bits u v t saved [])
      (cfg (some (.add b)) [] bits u (v+t) 0 saved []) (t+1) := by
  induction t generalizing v with
  | zero => apply one; simpa using (show computer.step (cfg (some (.restore b)) [] bits u v 0 saved []) =
        some (cfg (some (.add b)) [] bits u v 0 saved []) by machine_step)
  | succ t ih =>
      have hs : Run (cfg (some (.restore b)) [] bits u v (t+1) saved [])
          (cfg (some (.restore b)) [] bits u (v+1) t saved []) 1 := one (by machine_step)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq hs (ih (v+1))

def clearBudget_run (u v : ℕ) (saved : List Bool) :
    Run (cfg (some .clearBudget) [] [] u v 0 saved [])
      (cfg (some .finishPayload) [] [] 0 v 0 saved []) (u+1) := by
  induction u with
  | zero => exact one (by machine_step)
  | succ u ih =>
      have h : Run (cfg (some .clearBudget) [] [] (u+1) v 0 saved [])
          (cfg (some .clearBudget) [] [] u v 0 saved []) 1 := one (by machine_step)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h ih

def finishPayload_run (v : ℕ) (saved : List Bool) (out : List (Option Bool)) :
    Run (cfg (some .finishPayload) [] [] 0 v 0 saved out)
      (cfg (some .finishCount) [] [] 0 v 0 [] (none :: saved.reverse.map some ++ out))
      (saved.length+1) := by
  induction saved generalizing out with
  | nil => exact one (by machine_step)
  | cons b bs ih =>
      have h : Run (cfg (some .finishPayload) [] [] 0 v 0 (b::bs) out)
          (cfg (some .finishPayload) [] [] 0 v 0 bs (some b::out)) 1 := one (by machine_step)
      simpa [List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih (some b::out))

def finishCount_run (v : ℕ) (out : List (Option Bool)) :
    Run (cfg (some .finishCount) [] [] 0 v 0 [] out)
      (halt (List.replicate v (some true) ++ out)) (v+1) := by
  induction v generalizing out with
  | zero => apply one; unfold halt; machine_step
  | succ v ih =>
      have h : Run (cfg (some .finishCount) [] [] 0 (v+1) 0 [] out)
          (cfg (some .finishCount) [] [] 0 v 0 [] (some true::out)) 1 := one (by machine_step)
      simpa only [List.replicate_succ', List.append_assoc, List.singleton_append,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h (ih (some true::out))

def success (v : ℕ) (saved : List Bool) : List (Option Bool) :=
  List.replicate v (some true) ++ none :: saved.reverse.map some

def exit_run (u v : ℕ) (saved : List Bool) :
    Run (cfg (some .next) [] [] u v 0 saved []) (halt (success v saved))
      (u+v+saved.length+4) := by
  have h : Run (cfg (some .next) [] [] u v 0 saved [])
      (cfg (some .clearBudget) [] [] u v 0 saved []) 1 := one (by machine_step)
  have hp := finishPayload_run v saved []
  simp only [List.append_nil] at hp
  simpa [success, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    seq h (seq (clearBudget_run u v saved)
      (seq hp (finishCount_run v (none :: saved.reverse.map some))))

/-- Horner evaluation of most-significant-bit-first digits. -/
def value : ℕ → List Bool → ℕ
  | v, [] => v
  | v, b::bs => value (2*v+b.toNat) bs

theorem le_value (v : ℕ) (bs : List Bool) : v ≤ value v bs := by
  induction bs generalizing v with
  | nil => rfl
  | cons b bs ih => simp only [value]; have := ih (2*v+b.toNat); omega

def result (B v : ℕ) (bs saved : List Bool) : List (Option Bool) :=
  if value v bs ≤ B then success (value v bs) saved else []

def loopTime (B k s : ℕ) : ℕ := (k+1)*(6*B+2*k+s+10)

/-- A successful bit consumes budget before allocating its new count marks. -/
def round_run (b : Bool) (bits : List Bool) (B v : ℕ) (saved : List Bool)
    (hv : v ≤ B) (h : 2*v+b.toNat ≤ B) :
    Run (cfg (some .next) [] (b::bits) (B-v) v 0 saved [])
      (cfg (some .next) [] bits (B-(2*v+b.toNat)) (2*v+b.toNat) 0 saved []) (3*v+4) := by
  have hn : Run (cfg (some .next) [] (b::bits) (B-v) v 0 saved [])
      (cfg (some (.double b)) [] bits (B-v) v 0 saved []) 1 := by
    apply one; cases b <;> machine_step
  have hd := double_run b bits (B-v) v 0 saved (by omega)
  have hr := restore_run b bits (B-v-v) 0 (2*v) saved
  simp only [Nat.zero_add] at hd hr
  have ha : Run (cfg (some (.add b)) [] bits (B-v-v) (2*v) 0 saved [])
      (cfg (some .next) [] bits (B-(2*v+b.toNat)) (2*v+b.toNat) 0 saved []) 1 := by
    apply one
    cases b with
    | false => simp only [Bool.toNat_false, Nat.add_zero]; have he : B-v-v = B-2*v := by omega
               rw [he]; machine_step
    | true =>
        simp only [Bool.toNat_true] at h ⊢
        have he : B-v-v = (B-(2*v+1))+1 := by omega
        rw [he]; machine_step
  convert seq hn (seq hd (seq hr ha)) using 1; omega

/-- Overflow clears even the unread digits; its cost depends on source length. -/
def round_overflow (b : Bool) (bits : List Bool) (B v : ℕ) (saved : List Bool)
    (hv : v ≤ B) (h : B < 2*v+b.toNat) :
    Run (cfg (some .next) [] (b::bits) (B-v) v 0 saved []) (halt [])
      (bits.length+6*B+saved.length+10) := by
  have hn : Run (cfg (some .next) [] (b::bits) (B-v) v 0 saved [])
      (cfg (some (.double b)) [] bits (B-v) v 0 saved []) 1 := by
    apply one; cases b <;> machine_step
  by_cases hd : v ≤ B-v
  · have hdouble := double_run b bits (B-v) v 0 saved hd
    have hr := restore_run b bits (B-v-v) 0 (2*v) saved
    simp only [Nat.zero_add] at hdouble hr
    have hb : b = true := by cases b <;> simp_all; omega
    subst b
    have hz : B-v-v = 0 := by simp at h; omega
    rw [hz] at hdouble hr
    have ha : Run (cfg (some (.add true)) [] bits 0 (2*v) 0 saved [])
        (cfg (some .rejectBits) [] bits 0 (2*v) 0 saved []) 1 := one (by machine_step)
    apply mono (seq hn (seq hdouble (seq hr (seq ha (reject_run bits 0 (2*v) 0 saved)))))
    omega
  · apply mono (seq hn (double_overflow b bits (B-v) v 0 saved (by omega)))
    omega

/-- Both acceptance and rejection have a polynomial bound in the budget and bits. -/
def loop_run (bs : List Bool) (B v : ℕ) (saved : List Bool) (hv : v ≤ B) :
    Run (cfg (some .next) [] bs (B-v) v 0 saved []) (halt (result B v bs saved))
      (loopTime B bs.length saved.length) := by
  induction bs generalizing v with
  | nil =>
      simp only [result, value, ite_eq_left hv]
      apply mono (exit_run (B-v) v saved)
      simp [loopTime]; omega
  | cons b bs ih =>
      by_cases h : 2*v+b.toNat ≤ B
      · have hr := seq (round_run b bs B v saved hv h) (ih (2*v+b.toNat) h)
        change Run _ (halt (result B (2*v+b.toNat) bs saved)) _
        apply mono hr
        simp only [loopTime, List.length_cons]
        nlinarith
      · have hbad : ¬ value v (b::bs) ≤ B := by
          have := le_value (2*v+b.toNat) bs
          simp only [value]; omega
        simp only [result, ite_eq_right hbad]
        apply mono (round_overflow b bs B v saved hv (by omega))
        simp only [loopTime, List.length_cons]
        nlinarith

def input (n : ℕ) (rest : List Bool) : List (Option Bool) :=
  (BinaryNatLists.encodeNat n).map some ++ none :: rest.map some

def header_run (k : ℕ) (tail : List (Option Bool)) :
    Run (cfg (some .header) ((List.replicate k true).map some ++ some false :: tail) [] 0 0 0 [] [])
      (cfg (some .digits) tail [] 0 0 0 [] []) (k+1) := by
  induction k with
  | zero => exact one (by machine_step)
  | succ k ih =>
      have h : Run (cfg (some .header) ((List.replicate (k+1) true).map some ++ some false :: tail) [] 0 0 0 [] [])
          (cfg (some .header) ((List.replicate k true).map some ++ some false :: tail) [] 0 0 0 [] []) 1 := by
        apply one; simp only [List.replicate_succ, List.map_cons, List.cons_append]; machine_step
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seq h ih

def digits_run (digits bits : List Bool) (rest : List Bool) :
    Run (cfg (some .digits) (digits.map some ++ none :: rest.map some) bits 0 0 0 [] [])
      (cfg (some .payload) (rest.map some) (digits.reverse ++ bits) 0 0 0 [] [])
      (digits.length+1) := by
  induction digits generalizing bits with
  | nil => exact one (by machine_step)
  | cons b bs ih =>
      have h : Run (cfg (some .digits) ((b::bs).map some ++ none :: rest.map some) bits 0 0 0 [] [])
          (cfg (some .digits) (bs.map some ++ none :: rest.map some) (b::bits) 0 0 0 [] []) 1 := by
        apply one; simp only [List.map_cons, List.cons_append]; machine_step
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using seq h (ih (b::bits))

def payload_run (rest bits saved : List Bool) (u : ℕ) :
    Run (cfg (some .payload) (rest.map some) bits u 0 0 saved [])
      (cfg (some .next) [] bits (u+rest.length) 0 0 (rest.reverse ++ saved) [])
      (rest.length+1) := by
  induction rest generalizing saved u with
  | nil => exact one (by machine_step)
  | cons b bs ih =>
      have h : Run (cfg (some .payload) ((b::bs).map some) bits u 0 0 saved [])
          (cfg (some .payload) (bs.map some) bits (u+1) 0 0 (b::saved) []) 1 := by
        apply one; simp only [List.map_cons]; machine_step
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using seq h (ih (b::saved) (u+1))

theorem value_append (v : ℕ) (xs ys : List Bool) :
    value v (xs++ys) = value (value v xs) ys := by
  induction xs generalizing v with
  | nil => rfl
  | cons b bs ih => exact ih (2*v+b.toNat)

private theorem value_encodePosNum (n : PosNum) :
    value 0 (encodePosNum n).reverse = n := by
  induction n with
  | one => rfl
  | bit0 n ih => simp [encodePosNum, List.reverse_cons, value_append, value, ih, two_mul]
  | bit1 n ih => simp [encodePosNum, List.reverse_cons, value_append, value, ih, two_mul]

theorem value_encodeNat (n : ℕ) : value 0 (Computability.encodeNat n).reverse = n := by
  have h (m : Num) : value 0 (encodeNum m).reverse = (m : ℕ) := by
    cases m with
    | zero => rfl
    | pos m => exact value_encodePosNum m
  simpa [Computability.encodeNat] using h (n : Num)

def output (n : ℕ) (rest : List Bool) : List (Option Bool) :=
  if n ≤ rest.length then List.replicate n (some true) ++ none :: rest.map some else []

theorem init_eq (xs : List (Option Bool)) :
    initList computer xs = cfg (some .header) xs [] 0 0 0 [] [] := by
  unfold initList cfg; congr; funext k; cases k <;> rfl

theorem halt_eq (xs : List (Option Bool)) : haltList computer xs = halt xs := by
  unfold haltList halt cfg; congr; funext k; cases k <;> rfl

/-- Includes frame disposal, digit reversal, budget construction and cleanup. -/
def outputsInTime (n : ℕ) (rest : List Bool) :
    TM2OutputsInTime computer (input n rest) (some (output n rest))
      (10*((input n rest).length+1)^2) := by
  have hh := header_run (Computability.encodeNat n).length
    ((Computability.encodeNat n).map some ++ none :: rest.map some)
  have hd := digits_run (Computability.encodeNat n) [] rest
  have hp := payload_run rest (Computability.encodeNat n).reverse [] 0
  have hl := loop_run (Computability.encodeNat n).reverse rest.length 0 rest.reverse (by omega)
  simp only [List.append_nil, Nat.zero_add, Nat.sub_zero] at hd hp hl
  have h := seq hh (seq hd (seq hp hl))
  have he : result rest.length 0 (Computability.encodeNat n).reverse rest.reverse = output n rest := by
    simp [result, output, value_encodeNat, success]
  rw [he] at h
  have hi : (List.replicate (Computability.encodeNat n).length true).map some ++
      some false :: ((Computability.encodeNat n).map some ++ none :: rest.map some) = input n rest := by
    simp [input, BinaryNatLists.encodeNat, BinaryNatLists.frame, List.map_append, List.append_assoc]
  rw [hi] at h
  have hb : (Computability.encodeNat n).length + 1 +
      ((Computability.encodeNat n).length+1+(rest.length+1+
      loopTime rest.length (Computability.encodeNat n).reverse.length rest.reverse.length)) ≤
        10*((input n rest).length+1)^2 := by
    simp only [loopTime, input, BinaryNatLists.encodeNat, BinaryNatLists.frame,
      List.length_append, List.length_map, List.length_cons, List.length_replicate, List.length_reverse]
    nlinarith [sq_nonneg ((Computability.encodeNat n).length : ℤ),
      sq_nonneg (rest.length : ℤ)]
  simpa only [TM2OutputsInTime, init_eq, halt_eq, Option.map_some] using! mono h hb

def emptyOutputsInTime : TM2OutputsInTime computer [] (some []) 10 := by
  have h : Run (cfg (some .header) [] [] 0 0 0 [] []) (halt []) 1 := by
    apply one; unfold halt; machine_step
  simpa only [TM2OutputsInTime, init_eq, halt_eq, Option.map_some] using! mono h (by omega : 1 ≤ 10)

#print axioms outputsInTime
#print axioms loop_run
#print axioms round_overflow

end PhdThesisLean.BoundedBinaryCount.Machine
