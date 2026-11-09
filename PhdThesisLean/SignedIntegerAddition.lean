import PhdThesisLean.SignedAdditionBits

/-!
# Signed binary addition and subtraction in linear machine time

Both operands and the result use the original signed/framed Boolean integer
encoding. The machine parses both fields, compares while saving their digits,
restores them, performs a finite carry/borrow pass with the larger magnitude
first, removes high zeros, and writes the sign and frame. All stacks are emptied
and finite control reset. This arithmetic contract covers encoded pairs.
-/
namespace PhdThesisLean.SignedIntegerAddition

open Computability Turing StateTransition
open LeanNPHardness.MachinePrimitives
open BinarySubtraction (value)

set_option backward.isDefEq.respectTransparency false

structure Registers where
  negativeLeft : Bool
  negativeRight : Bool
  le : Bool
  carry : Bool
  seen : Bool
  deriving DecidableEq, Fintype

def initial : Registers := ⟨false, false, true, false, false⟩
def setSign (subtract right sign : Bool) (r : Registers) : Registers :=
  if right then {r with negativeRight := xor sign subtract} else {r with negativeLeft := sign}
def addMode (r : Registers) : Bool := r.negativeLeft == r.negativeRight
def negative (r : Registers) : Bool := if r.le then r.negativeRight else r.negativeLeft

def stepBits (r : Registers) (a b : Option Bool) : Bool × Bool :=
  if r.le then bitStep (addMode r) r.carry b a else bitStep (addMode r) r.carry a b

def arithmeticBits (r : Registers) (a b : List Bool) : List Bool :=
  if r.le then rawBits (addMode r) r.carry b a else rawBits (addMode r) r.carry a b

theorem arithmeticBits_length (r : Registers) (a b : List Bool) :
    (arithmeticBits r a b).length ≤ max a.length b.length + 1 := by
  unfold arithmeticBits; split
  · simpa [Nat.max_comm] using rawBits_length (addMode r) r.carry b a
  · exact rawBits_length (addMode r) r.carry a b

inductive Stack
  | input | count | work | magnitude (right : Bool) | output
  deriving DecidableEq, Fintype
inductive Label
  | sign (right : Bool) | header (right : Bool) | body (right : Bool)
  | reverse (right : Bool) | scan | recover (right : Bool) | arithmetic | normalize | prefix
  deriving DecidableEq, Fintype
structure State where
  regs : Registers
  a : Option Bool
  b : Option Bool
  deriving DecidableEq, Fintype

def state (r : Registers) : State := ⟨r, none, none⟩
def observe (s : State) (b : Option Bool) : State := {s with a := b}
def observeRight (s : State) (b : Option Bool) : State := {s with b := b}
def Alphabet (_ : Stack) : Type := Bool

def go (l : Label) (f : State → Registers) : TM2.Stmt Alphabet Label State :=
  .load (fun s => state (f s)) (.goto fun _ => l)

def program (subtract : Bool) : Label → TM2.Stmt Alphabet Label State
  | .sign d => .pop .input observe
      (go (.header d) (fun s => setSign subtract d (s.a.getD false) s.regs))
  | .header d => .pop .input observe <|
      .branch (fun s => s.a.getD false)
        (.push .count (fun _ => true) (go (.header d) State.regs))
        (go (.body d) State.regs)
  | .body d => .pop .count observe <|
      .branch (fun s => s.a.isSome)
        (.pop .input observe <|
          .push .work (fun s => s.a.getD false) (go (.body d) State.regs))
        (go (.reverse d) State.regs)
  | .reverse d => .pop .work observe <|
      .branch (fun s => s.a.isSome)
        (.push (.magnitude d) (fun s => s.a.getD false) (go (.reverse d) State.regs))
        (go (if d then .scan else .sign true) State.regs)
  | .scan => .pop (.magnitude false) observe <| .pop (.magnitude true) observeRight <|
      .branch (fun s => s.a.isSome || s.b.isSome)
        (.branch (fun s => s.a.isSome)
          (.push .work (fun s => s.a.getD false) <|
            .branch (fun s => s.b.isSome)
              (.push .count (fun s => s.b.getD false)
                (go .scan (fun s => {s.regs with le := binaryLEUpdate s.regs.le s.a s.b})))
              (go .scan (fun s => {s.regs with le := binaryLEUpdate s.regs.le s.a s.b})))
          (.push .count (fun s => s.b.getD false)
            (go .scan (fun s => {s.regs with le := binaryLEUpdate s.regs.le s.a s.b}))))
        (go (.recover false) State.regs)
  | .recover d => .pop (if d then .count else .work) observe <|
      .branch (fun s => s.a.isSome)
        (.push (.magnitude d) (fun s => s.a.getD false) (go (.recover d) State.regs))
        (go (if d then .arithmetic else .recover true) State.regs)
  | .arithmetic => .pop (.magnitude false) observe <| .pop (.magnitude true) observeRight <|
      .branch (fun s => s.a.isSome || s.b.isSome)
        (.push .work (fun s => (stepBits s.regs s.a s.b).1)
          (go .arithmetic (fun s => {s.regs with carry := (stepBits s.regs s.a s.b).2})))
        (.branch (fun s => addMode s.regs && s.regs.carry)
          (.push .work (fun _ => true) (go .normalize (fun s => {s.regs with carry := false})))
          (go .normalize (fun s => {s.regs with carry := false})))
  | .normalize => .pop .work observe <|
      .branch (fun s => s.a.isSome)
        (.branch (fun s => s.regs.seen || s.a.getD false)
          (.push .output (fun s => s.a.getD false) <| .push .count (fun _ => true)
            (go .normalize (fun s => {s.regs with seen := true})))
          (go .normalize State.regs))
        (.push .output (fun _ => false) (go .prefix State.regs))
  | .prefix => .pop .count observe <|
      .branch (fun s => s.a.isSome)
        (.push .output (fun _ => true) (go .prefix State.regs))
        (.push .output (fun s => negative s.regs && s.regs.seen)
          (.load (fun _ => state initial) .halt))

def computer (subtract : Bool) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .sign false
  σ := State
  initialState := state initial
  Γk₀Fin := Bool.fintype
  m := program subtract

def contents (input count work left right output : List Bool) : (k : Stack) → List (Alphabet k)
  | .input => input
  | .count => count
  | .work => work
  | .magnitude false => left
  | .magnitude true => right
  | .output => output

def cfg (l : Option Label) (r : Registers) (input count work left right output : List Bool) :
    (computer subtract).Cfg := ⟨l, state r, contents input count work left right output⟩

variable (subtract : Bool)

private theorem sign_step (d sign : Bool) (r : Registers) (input left right : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some (.sign d)) r (sign :: input) [] [] left right []) =
      some (cfg (subtract := subtract) (some (.header d)) (setSign subtract d sign r) input [] [] left right []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe]
  funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem header_true (d : Bool) (r : Registers) (input count left right : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some (.header d)) r (true :: input) count [] left right []) =
      some (cfg (subtract := subtract) (some (.header d)) r input (true :: count) [] left right []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
    Function.update]
  funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem header_false (d : Bool) (r : Registers) (input count left right : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some (.header d)) r (false :: input) count [] left right []) =
      some (cfg (subtract := subtract) (some (.body d)) r input count [] left right []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
    Function.update]
  funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

theorem header_run (d : Bool) (r : Registers) (n : ℕ) (input count left right : List Bool) :
    (fun q => q.bind (computer subtract).step)^[n + 1]
      (some (cfg (subtract := subtract) (some (.header d)) r (List.replicate n true ++ false :: input)
        count [] left right [])) =
    some (cfg (subtract := subtract) (some (.body d)) r input (List.replicate n true ++ count) [] left right []) := by
  induction n generalizing count with
  | zero => simpa using header_false subtract d r input count left right
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [Function.iterate_succ_apply, Option.bind_some, header_true subtract, ih]
      simp [replicate_true_append_cons]

private theorem body_cons (d bit : Bool) (r : Registers)
    (input count work left right : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some (.body d)) r (bit :: input) (true :: count) work left right []) =
      some (cfg (subtract := subtract) (some (.body d)) r input count (bit :: work) left right []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
    Function.update]
  funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem body_nil (d : Bool) (r : Registers) (input work left right : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some (.body d)) r input [] work left right []) =
      some (cfg (subtract := subtract) (some (.reverse d)) r input [] work left right []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
    Function.update]

theorem body_run (d : Bool) (r : Registers) (bits input work left right : List Bool) :
    (fun q => q.bind (computer subtract).step)^[bits.length + 1]
      (some (cfg (subtract := subtract) (some (.body d)) r (bits ++ input)
        (List.replicate bits.length true) work left right [])) =
    some (cfg (subtract := subtract) (some (.reverse d)) r input [] (bits.reverse ++ work) left right []) := by
  induction bits generalizing work with
  | nil => simpa using body_nil subtract d r input work left right
  | cons b bits ih =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append]
      rw [Function.iterate_succ_apply, Option.bind_some, body_cons subtract, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem reverse_cons (d bit : Bool) (r : Registers) (input work left right : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some (.reverse d)) r input [] (bit :: work) left right []) =
      some (cfg (subtract := subtract) (some (.reverse d)) r input [] work
        (if d then left else bit :: left) (if d then bit :: right else right) []) := by
  cases d <;>
    simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
      Function.update]
  all_goals funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem reverse_nil (d : Bool) (r : Registers) (input left right : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some (.reverse d)) r input [] [] left right []) =
      some (cfg (subtract := subtract) (some (if d then .scan else .sign true)) r input [] [] left right []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
    Function.update]

theorem reverse_run (d : Bool) (r : Registers) (input work left right : List Bool) :
    (fun q => q.bind (computer subtract).step)^[work.length + 1]
      (some (cfg (subtract := subtract) (some (.reverse d)) r input [] work left right [])) =
    some (cfg (subtract := subtract) (some (if d then .scan else .sign true)) r input [] []
      (if d then left else work.reverse ++ left)
      (if d then work.reverse ++ right else right) []) := by
  induction work generalizing left right with
  | nil => simpa using reverse_nil subtract d r input left right
  | cons bit work ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, reverse_cons subtract, ih]
      cases d <;> simp [List.reverse_cons, List.append_assoc]

/-- One framed integer is read and retained on its magnitude stack. All frame
marks and reversal scratch are emptied; the remaining input is preserved. -/
theorem field_run (d sign : Bool) (r : Registers) (bits input left right : List Bool) :
    (fun q => q.bind (computer subtract).step)^[3 * bits.length + 4]
      (some (cfg (subtract := subtract) (some (.sign d)) r
        (sign :: (LeanNPHardness.BinaryNatLists.frame bits ++ input)) [] [] left right [])) =
    some (cfg (subtract := subtract) (some (if d then .scan else .sign true)) (setSign subtract d sign r) input [] []
      (if d then left else bits ++ left) (if d then bits ++ right else right) []) := by
  rw [show 3 * bits.length + 4 = ((bits.length + 1) + (bits.length + 1) +
    (bits.length + 1)) + 1 by omega, Function.iterate_succ_apply, Option.bind_some, sign_step subtract]
  simp only [LeanNPHardness.BinaryNatLists.frame, List.append_assoc, List.cons_append]
  rw [Function.iterate_add_apply, header_run subtract]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply, body_run subtract]
  simp only [List.append_nil]
  have h := reverse_run subtract d (setSign subtract d sign r) input bits.reverse left right
  simpa using h


private theorem scan_step (r : Registers) (a b savedA savedB : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some .scan) r [] savedB savedA a b []) =
      some (if a.isEmpty && b.isEmpty then
        cfg (subtract := subtract) (some (.recover false)) r [] savedB savedA [] [] []
      else cfg (subtract := subtract) (some .scan)
        {r with le := binaryLEUpdate r.le a.head? b.head?}
        [] (b.take 1 ++ savedB) (a.take 1 ++ savedA) a.tail b.tail []) := by
  cases a <;> cases b <;>
    simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
      observeRight, Function.update]
  all_goals funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

/-- Magnitude comparison retains every digit, including unequal-width tails. -/
theorem scan_run (r : Registers) (a b savedA savedB : List Bool) :
    (fun q => q.bind (computer subtract).step)^[max a.length b.length + 1]
      (some (cfg (subtract := subtract) (some .scan) r [] savedB savedA a b [])) =
    some (cfg (subtract := subtract) (some (.recover false))
      {r with le := binaryLEBitsAux r.le a b}
      [] (b.reverse ++ savedB) (a.reverse ++ savedA) [] [] []) := by
  induction a generalizing r b savedA savedB with
  | nil =>
      induction b generalizing r savedA savedB with
      | nil => simpa [binaryLEBitsAux] using scan_step subtract r [] [] savedA savedB
      | cons bit b ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply, Option.bind_some, scan_step]
          simp only [List.isEmpty_nil, List.isEmpty_cons, Bool.true_and, Bool.false_eq_true,
            ↓reduceIte, List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
            List.take_nil, List.nil_append, List.take_succ_cons, List.take_zero, List.singleton_append]
          simp only [List.length_nil, Nat.zero_max] at ih
          rw [ih]
          simp [binaryLEBitsAux, List.reverse_cons, List.append_assoc]
  | cons bit a ih =>
      cases b with
      | nil =>
          simp only [List.length_nil, List.length_cons, Nat.max_zero]
          rw [Function.iterate_succ_apply, Option.bind_some, scan_step]
          simp only [List.isEmpty_nil, List.isEmpty_cons, Bool.false_and, Bool.false_eq_true,
            ↓reduceIte, List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
            List.take_nil, List.nil_append, List.take_succ_cons, List.take_zero, List.singleton_append]
          have h := ih {r with le := binaryLEUpdate r.le (some bit) none} [] (bit :: savedA) savedB
          simp only [List.length_nil, Nat.max_zero] at h
          rw [h]
          simp [binaryLEBitsAux, List.reverse_cons, List.append_assoc]
      | cons bit' b =>
          simp only [List.length_cons, Nat.succ_max_succ]
          rw [Function.iterate_succ_apply, Option.bind_some, scan_step]
          simp only [List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            List.head?_cons, List.tail_cons, List.take_succ_cons, List.take_zero, List.singleton_append]
          rw [ih]
          simp [binaryLEBitsAux, List.reverse_cons, List.append_assoc]

private theorem recover_left_cons (r : Registers) (bit : Bool) (bs savedB a b : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some (.recover false)) r [] savedB (bit :: bs) a b []) =
      some (cfg (subtract := subtract) (some (.recover false)) r [] savedB bs (bit :: a) b []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe, Function.update]
  funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem recover_left_nil (r : Registers) (savedB a b : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some (.recover false)) r [] savedB [] a b []) =
      some (cfg (subtract := subtract) (some (.recover true)) r [] savedB [] a b []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe, Function.update]

theorem recover_left_run (r : Registers) (bs savedB a b : List Bool) :
    (fun q => q.bind (computer subtract).step)^[bs.length + 1]
      (some (cfg (subtract := subtract) (some (.recover false)) r [] savedB bs a b [])) =
    some (cfg (subtract := subtract) (some (.recover true)) r [] savedB [] (bs.reverse ++ a) b []) := by
  induction bs generalizing a with
  | nil => simpa using recover_left_nil subtract r savedB a b
  | cons bit bs ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, recover_left_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem recover_right_cons (r : Registers) (bit : Bool) (bs a b : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some (.recover true)) r [] (bit :: bs) [] a b []) =
      some (cfg (subtract := subtract) (some (.recover true)) r [] bs [] a (bit :: b) []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe, Function.update]
  funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem recover_right_nil (r : Registers) (a b : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some (.recover true)) r [] [] [] a b []) =
      some (cfg (subtract := subtract) (some .arithmetic) r [] [] [] a b []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe, Function.update]

theorem recover_right_run (r : Registers) (bs a b : List Bool) :
    (fun q => q.bind (computer subtract).step)^[bs.length + 1]
      (some (cfg (subtract := subtract) (some (.recover true)) r [] bs [] a b [])) =
    some (cfg (subtract := subtract) (some .arithmetic) r [] [] [] a (bs.reverse ++ b) []) := by
  induction bs generalizing b with
  | nil => simpa using recover_right_nil subtract r a b
  | cons bit bs ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, recover_right_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem arithmetic_step (r : Registers) (a b work : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some .arithmetic) r [] [] work a b []) =
      some (if a.isEmpty && b.isEmpty then
        cfg (subtract := subtract) (some .normalize) {r with carry := false} [] []
          (if addMode r && r.carry then true :: work else work) [] [] []
      else cfg (subtract := subtract) (some .arithmetic)
        {r with carry := (stepBits r a.head? b.head?).2}
        [] [] ((stepBits r a.head? b.head?).1 :: work) a.tail b.tail []) := by
  cases hm : addMode r <;> cases hc : r.carry <;> cases a <;> cases b <;>
    simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
      observeRight, Function.update, hm, hc]
  all_goals funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

/-- One ripple pass. Its final carry is emitted only in addition mode. -/
theorem arithmetic_run (r : Registers) (a b work : List Bool) :
    (fun q => q.bind (computer subtract).step)^[max a.length b.length + 1]
      (some (cfg (subtract := subtract) (some .arithmetic) r [] [] work a b [])) =
    some (cfg (subtract := subtract) (some .normalize) {r with carry := false}
      [] [] ((arithmeticBits r a b).reverse ++ work) [] [] []) := by
  induction a generalizing r b work with
  | nil =>
      induction b generalizing r work with
      | nil =>
          have h := arithmetic_step subtract r [] [] work
          cases hl : r.le <;> cases hc : r.carry <;> cases hm : addMode r <;>
            simpa [arithmeticBits, rawBits, hl, hc, hm] using h
      | cons bit b ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply, Option.bind_some, arithmetic_step]
          simp only [List.isEmpty_nil, List.isEmpty_cons, Bool.true_and, Bool.false_eq_true,
            ↓reduceIte, List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons]
          simp only [List.length_nil, Nat.zero_max] at ih
          rw [ih]
          cases hl : r.le <;> simp [arithmeticBits, rawBits, stepBits, addMode, hl,
            List.reverse_cons, List.append_assoc]
  | cons bit a ih =>
      cases b with
      | nil =>
          simp only [List.length_nil, List.length_cons, Nat.max_zero]
          rw [Function.iterate_succ_apply, Option.bind_some, arithmetic_step]
          simp only [List.isEmpty_nil, List.isEmpty_cons, Bool.false_and, Bool.false_eq_true,
            ↓reduceIte, List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons]
          have h := ih {r with carry := (stepBits r (some bit) none).2} []
            ((stepBits r (some bit) none).1 :: work)
          simp only [List.length_nil, Nat.max_zero] at h
          rw [h]
          cases hl : r.le <;> simp [arithmeticBits, rawBits, stepBits, addMode, hl,
            List.reverse_cons, List.append_assoc]
      | cons bit' b =>
          simp only [List.length_cons, Nat.succ_max_succ]
          rw [Function.iterate_succ_apply, Option.bind_some, arithmetic_step]
          simp only [List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            List.head?_cons, List.tail_cons]
          rw [ih]
          cases hl : r.le <;> simp [arithmeticBits, rawBits, stepBits, addMode, hl,
            List.reverse_cons, List.append_assoc]

private theorem normalize_nil (r : Registers) (count output : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some .normalize) r [] count [] [] [] output) =
    some (cfg (subtract := subtract) (some .prefix) r [] count [] [] [] (false :: output)) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe, Function.update]
  funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem normalize_cons (r : Registers) (bit : Bool) (bs count output : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some .normalize) r [] count (bit :: bs) [] [] output) =
    some (cfg (subtract := subtract) (some .normalize) {r with seen := bit || r.seen} []
      (if bit || r.seen then true :: count else count) bs [] []
      (if bit || r.seen then bit :: output else output)) := by
  rcases r with ⟨sa, sb, le, carry, seen⟩
  cases bit <;> cases seen <;>
    simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe, Function.update]
  all_goals funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem normalize_encode_cons (r : Registers) (bit : Bool) (bs : List Bool) (n : ℕ) :
    (computer subtract).step (cfg (subtract := subtract) (some .normalize) {r with seen := decide (n ≠ 0)} []
      (List.replicate (encodeNat n).length true) (bit :: bs) [] [] (encodeNat n)) =
    some (cfg (subtract := subtract) (some .normalize) {r with seen := decide (bit.toNat + 2 * n ≠ 0)} []
      (List.replicate (encodeNat (bit.toNat + 2 * n)).length true) bs [] []
      (encodeNat (bit.toNat + 2 * n))) := by
  rw [normalize_cons, ← BinarySubtraction.pushBit_encode]
  by_cases hn : n = 0
  · subst n; cases bit <;> rfl
  · simp [BinarySubtraction.pushBit, BinarySubtraction.encode_isEmpty, hn,
      List.replicate_succ]

/-- Every raw bit is visited; only high zeros are dropped. The retained-bit
counter constructs the output's actual unary length frame. -/
theorem normalize_run (r : Registers) (bs : List Bool) (n : ℕ) :
    (fun q => q.bind (computer subtract).step)^[bs.length + 1]
      (some (cfg (subtract := subtract) (some .normalize) {r with seen := decide (n ≠ 0)} []
        (List.replicate (encodeNat n).length true) bs [] [] (encodeNat n))) =
    some (cfg (subtract := subtract) (some .prefix)
      {r with seen := decide (BinarySubtraction.restoreValue bs n ≠ 0)} []
      (List.replicate (encodeNat (BinarySubtraction.restoreValue bs n)).length true) [] [] []
      (false :: encodeNat (BinarySubtraction.restoreValue bs n))) := by
  induction bs generalizing n with
  | nil =>
      simpa [BinarySubtraction.restoreValue] using normalize_nil subtract
        {r with seen := decide (n ≠ 0)} (List.replicate (encodeNat n).length true) (encodeNat n)
  | cons bit bs ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, normalize_encode_cons, ih]
      rfl

private theorem prefix_cons (r : Registers) (count output : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some .prefix) r [] (true :: count) [] [] [] output) =
    some (cfg (subtract := subtract) (some .prefix) r [] count [] [] [] (true :: output)) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe, Function.update]
  funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem prefix_nil (r : Registers) (output : List Bool) :
    (computer subtract).step (cfg (subtract := subtract) (some .prefix) r [] [] [] [] [] output) =
    some (cfg (subtract := subtract) none initial [] [] [] [] [] ((negative r && r.seen) :: output)) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe, Function.update]
  funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

theorem prefix_run (r : Registers) (n : ℕ) (output : List Bool) :
    (fun q => q.bind (computer subtract).step)^[n + 1]
      (some (cfg (subtract := subtract) (some .prefix) r [] (List.replicate n true) [] [] [] output)) =
    some (cfg (subtract := subtract) none initial [] [] [] [] []
      ((negative r && r.seen) :: (List.replicate n true ++ output))) := by
  induction n generalizing output with
  | zero => simpa using prefix_nil subtract r output
  | succ n ih =>
      rw [List.replicate_succ, Function.iterate_succ_apply, Option.bind_some, prefix_cons, ih]
      simp [replicate_true_append_cons]

/-- Normalization and framing, including sign selection and control reset. -/
theorem finish_run (r : Registers) (bs : List Bool) (hs : r.seen = false) :
    (fun q => q.bind (computer subtract).step)^[bs.length + (value bs).size + 2]
      (some (cfg (subtract := subtract) (some .normalize) r [] [] bs.reverse [] [] [])) =
    some (cfg (subtract := subtract) none initial [] [] [] [] []
      (SmithEncoding.encodeInt (signed (negative r) (value bs)))) := by
  rw [show bs.length + (value bs).size + 2 = ((value bs).size + 1) + (bs.reverse.length + 1) by simp; omega,
    Function.iterate_add_apply]
  have hr : {r with seen := decide (0 ≠ 0)} = r := by cases r; simp_all
  have h := normalize_run subtract r bs.reverse 0
  simp only [BinarySubtraction.restoreValue_reverse, show encodeNat 0 = [] from rfl,
    List.length_nil, List.replicate_zero, hr] at h
  rw [h, ← LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size (value bs), prefix_run]
  simp [encode_signed, negative, LeanNPHardness.BinaryNatLists.encodeNat,
    LeanNPHardness.BinaryNatLists.frame]

/-- Control just after the comparison, including the selected arithmetic mode. -/
def ready (sa sb : Bool) (m n : ℕ) : Registers := ⟨sa, sb, decide (m ≤ n), false, false⟩

theorem arithmeticBits_ready (sa sb : Bool) (m n : ℕ) :
    value (arithmeticBits (ready sa sb m n) (encodeNat m) (encodeNat n)) = magnitude sa sb m n := by
  by_cases h : m ≤ n
  · simp only [arithmeticBits, ready, h, decide_true, ↓reduceIte, addMode]
    rw [rawBits_value _ n m (fun _ => h)]
    simp [magnitude, h, Nat.add_comm]
  · simp only [arithmeticBits, ready, h, decide_false, Bool.false_eq_true, ↓reduceIte, addMode]
    rw [rawBits_value _ m n (fun _ => by omega)]
    simp [magnitude, h]

/-- Raw arithmetic width and final magnitude width are charged independently. -/
theorem value_size_le (bs : List Bool) : (value bs).size ≤ bs.length :=
  (Nat.size_le).2 (BinarySubtraction.value_lt bs)

def resultBits (subtract : Bool) (a b : ℤ) : List Bool :=
  arithmeticBits (ready (decide (a < 0)) (xor (decide (b < 0)) subtract) a.natAbs b.natAbs)
    (encodeNat a.natAbs) (encodeNat b.natAbs)

def runtime (subtract : Bool) (a b : ℤ) : ℕ :=
  4 * (a.natAbs.size + b.natAbs.size) + 2 * max a.natAbs.size b.natAbs.size +
    (resultBits subtract a b).length + (value (resultBits subtract a b)).size + 14

/-- The full execution consumes the two original signed/framed words and
returns one word in that same encoding, with all scratch emptied. -/
theorem run (a b : ℤ) :
    (fun q => q.bind (computer subtract).step)^[runtime subtract a b]
      (some (cfg (subtract := subtract) (some (.sign false)) initial
        (SignedIntegerComparison.encode (a, b)) [] [] [] [] [])) =
    some (cfg (subtract := subtract) none initial [] [] [] [] []
      (SmithEncoding.encodeInt (operation subtract a b))) := by
  let sa := decide (a < 0)
  let sb := xor (decide (b < 0)) subtract
  let u := a.natAbs.size
  let v := b.natAbs.size
  let r := ready sa sb a.natAbs b.natAbs
  let raw := resultBits subtract a b
  have ha := field_run subtract false sa initial (encodeNat a.natAbs)
    (SmithEncoding.encodeInt b) [] []
  have hb := field_run subtract true (decide (b < 0)) (setSign subtract false sa initial)
    (encodeNat b.natAbs) [] (encodeNat a.natAbs) []
  simp only [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size,
    Bool.false_eq_true, ↓reduceIte, List.append_nil] at ha hb
  have time_eq : runtime subtract a b =
      raw.length + (value raw).size + 2 + (max u v + 1) +
        (v + 1) + (u + 1) + (max u v + 1) + (3 * v + 4) + (3 * u + 4) := by
    dsimp [runtime, raw, u, v]; omega
  rw [time_eq, Function.iterate_add_apply]
  change (fun q => q.bind (computer subtract).step)^[_]
    ((fun q => q.bind (computer subtract).step)^[3 * u + 4]
      (some (cfg (subtract := subtract) (some (.sign false)) initial
        (sa :: (LeanNPHardness.BinaryNatLists.frame (encodeNat a.natAbs) ++
          SmithEncoding.encodeInt b)) [] [] [] [] []))) = _
  rw [ha, Function.iterate_add_apply]
  have hb' : (fun q => q.bind (computer subtract).step)^[3 * v + 4]
      (some (cfg (subtract := subtract) (some (.sign true)) (setSign subtract false sa initial)
        (SmithEncoding.encodeInt b) [] [] (encodeNat a.natAbs) [] [])) =
      some (cfg (subtract := subtract) (some .scan) ⟨sa, sb, true, false, false⟩
        [] [] [] (encodeNat a.natAbs) (encodeNat b.natAbs) []) := by
    simpa [SmithEncoding.encodeInt, LeanNPHardness.BinaryNatLists.encodeNat,
      setSign, initial, v, sb] using hb
  rw [hb', Function.iterate_add_apply]
  have hc := scan_run subtract ⟨sa, sb, true, false, false⟩ (encodeNat a.natAbs) (encodeNat b.natAbs) [] []
  simp only [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size, List.append_nil,
    binaryLEBitsAux_encodeNat] at hc
  rw [hc, Function.iterate_add_apply]
  have hl := recover_left_run subtract r (encodeNat a.natAbs).reverse (encodeNat b.natAbs).reverse [] []
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil,
    LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size] at hl
  dsimp only [r, ready, u, v] at hl ⊢
  rw [hl, Function.iterate_add_apply]
  have hr := recover_right_run subtract r (encodeNat b.natAbs).reverse (encodeNat a.natAbs) []
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil,
    LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size] at hr
  dsimp only [r, ready] at hr
  rw [hr, Function.iterate_add_apply]
  have he := arithmetic_run subtract r (encodeNat a.natAbs) (encodeNat b.natAbs) []
  simp only [List.append_nil, LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size] at he
  dsimp only [r, ready] at he
  rw [he]
  have hf := finish_run subtract r raw rfl
  have hv : value raw = magnitude sa sb a.natAbs b.natAbs := arithmeticBits_ready sa sb a.natAbs b.natAbs
  have hn : negative r = resultSign sa sb a.natAbs b.natAbs := by simp [r, ready, negative, resultSign]
  rw [hv, hn] at hf
  dsimp only [sa, sb] at hf
  rw [← operation_eq_signed] at hf
  rw [hv]
  dsimp only [r, raw, resultBits, ready, sa, sb] at hf ⊢
  exact hf

/-- A bound in the complete original Boolean input length, charging signs,
frames, both comparisons/reversals, arithmetic, normalization and serialization. -/
theorem runtime_le (a b : ℤ) :
    runtime subtract a b ≤ 4 * (SignedIntegerComparison.encode (a, b)).length := by
  have hl := arithmeticBits_length
    (ready (decide (a < 0)) (xor (decide (b < 0)) subtract) a.natAbs b.natAbs)
    (encodeNat a.natAbs) (encodeNat b.natAbs)
  simp only [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size] at hl
  have hv := value_size_le (resultBits subtract a b)
  change (resultBits subtract a b).length ≤ max a.natAbs.size b.natAbs.size + 1 at hl
  rw [runtime, SignedIntegerComparison.encode_length]
  dsimp only [Prod.fst, Prod.snd]
  omega

private theorem init_eq (bits : List Bool) :
    initList (computer subtract) bits = cfg (subtract := subtract) (some (.sign false)) initial bits [] [] [] [] [] := by
  unfold initList cfg; congr; funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem halt_eq (bits : List Bool) :
    haltList (computer subtract) bits = cfg (subtract := subtract) none initial [] [] [] [] [] bits := by
  unfold haltList cfg; congr; funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

def outputsInTime (x : ℤ × ℤ) :
    TM2OutputsInTime (computer subtract) (SignedIntegerComparison.encode x)
      (some (SmithEncoding.encodeInt (operation subtract x.1 x.2)))
      (4 * (SignedIntegerComparison.encode x).length) where
  steps := runtime subtract x.1 x.2
  evals_in_steps := by
    change (fun q => q.bind (computer subtract).step)^[_]
      (some (initList (computer subtract) _)) = some (haltList (computer subtract) _)
    rw [init_eq, halt_eq]
    exact run subtract x.1 x.2
  steps_le_m := runtime_le subtract x.1 x.2

/-- Uniform finite-machine witness, with no arithmetic-cost or runtime premise.
The Boolean parameter selects addition (`false`) or subtraction (`true`). -/
noncomputable def computableInPolyTime :
    LeanNPHardness.TM2ComputableInPolyTime SignedIntegerComparison.encoding
      SignedIntegerMultiplication.integerEncoding (fun x => operation subtract x.1 x.2) where
  tm := computer subtract
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X
  outputsFun x := by
    simpa [SignedIntegerComparison.encoding, SignedIntegerMultiplication.integerEncoding,
      Equiv.refl, Polynomial.eval_mul, Polynomial.eval_X] using outputsInTime subtract x

noncomputable def additionComputableInPolyTime :
    LeanNPHardness.TM2ComputableInPolyTime SignedIntegerComparison.encoding
      SignedIntegerMultiplication.integerEncoding (fun x => x.1 + x.2) := computableInPolyTime false

noncomputable def subtractionComputableInPolyTime :
    LeanNPHardness.TM2ComputableInPolyTime SignedIntegerComparison.encoding
      SignedIntegerMultiplication.integerEncoding (fun x => x.1 - x.2) := computableInPolyTime true

/-- The complete signed/framed result is no longer than the two input words. -/
theorem output_length_le (a b : ℤ) :
    (SmithEncoding.encodeInt (operation subtract a b)).length ≤
      (SignedIntegerComparison.encode (a, b)).length := by
  have hr := arithmeticBits_ready (decide (a < 0)) (xor (decide (b < 0)) subtract) a.natAbs b.natAbs
  have hl := arithmeticBits_length
    (ready (decide (a < 0)) (xor (decide (b < 0)) subtract) a.natAbs b.natAbs)
    (encodeNat a.natAbs) (encodeNat b.natAbs)
  have hv := value_size_le (resultBits subtract a b)
  change value (resultBits subtract a b) = _ at hr
  change (resultBits subtract a b).length ≤ _ at hl
  rw [operation_eq_signed, encode_signed]
  simp only [List.length_cons, LeanNPHardness.BinaryNatLists.encodeNat_length,
    LeanNPHardness.BinaryNatLists.natWireSize,
    LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size,
    SignedIntegerComparison.encode_length]
  simp only [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size] at hl
  rw [hr] at hv
  omega

#print axioms rawBits_value
#print axioms signed_magnitude
#print axioms operation_eq_signed
#print axioms field_run
#print axioms scan_run
#print axioms arithmetic_run
#print axioms finish_run
#print axioms run
#print axioms runtime_le
#print axioms outputsInTime
#print axioms additionComputableInPolyTime
#print axioms subtractionComputableInPolyTime
#print axioms output_length_le

end PhdThesisLean.SignedIntegerAddition
