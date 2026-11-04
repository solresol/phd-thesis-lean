import PhdThesisLean.SmithEncoding
import LeanNPHardness.BinaryArithmetic

/-!
# Linear-time comparison of signed, framed binary integers

The input is the concatenation of the two existing `SmithEncoding.encodeInt`
words. A finite TM2 reads each length frame, reverses its magnitude into a
separate stack, and compares aligned bits. Negative pairs reverse the order;
mixed signs are handled separately. Parsing, all exhaustion transitions,
cleanup and control reset are included in the actual runtime.

The contract is for encoded integer pairs. This arithmetic component does not
validate arbitrary raw strings or compute the cross-products of fractions.
-/

namespace PhdThesisLean.SignedIntegerComparison

open Computability Turing StateTransition
open LeanNPHardness.MachinePrimitives

set_option backward.isDefEq.respectTransparency false

def encode (x : ℤ × ℤ) : List Bool :=
  SmithEncoding.encodeInt x.1 ++ SmithEncoding.encodeInt x.2

def decode (bits : List Bool) : Option (ℤ × ℤ) := do
  let (a, tail) ← SmithEncoding.decodeIntPrefix bits
  let (b, rest) ← SmithEncoding.decodeIntPrefix tail
  if rest.isEmpty then some (a, b) else none

@[simp] theorem decode_encode (x : ℤ × ℤ) : decode (encode x) = some x := by
  have h := SmithEncoding.decodeIntPrefix_encode_append x.2 []
  simp only [List.append_nil] at h
  simp [decode, encode, h]

def encoding : LeanNPHardness.FinEncoding (ℤ × ℤ) where
  Γ := Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

theorem encode_length (x : ℤ × ℤ) :
    (encode x).length = 2 * (x.1.natAbs.size + x.2.natAbs.size) + 4 := by
  simp only [encode, List.length_append, SmithEncoding.encodeInt_length,
    LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size]
  omega

structure Registers where
  negativeLeft : Bool
  negativeRight : Bool
  result : Bool
  deriving DecidableEq, Fintype

def initial : Registers := ⟨false, false, true⟩

def setSign (right sign : Bool) (r : Registers) : Registers :=
  if right then {r with negativeRight := sign} else {r with negativeLeft := sign}

def update (r : Registers) (a b : Option Bool) : Registers :=
  {r with result := if r.negativeLeft then binaryLEUpdate r.result b a
    else binaryLEUpdate r.result a b}

def answer (r : Registers) : Bool :=
  if r.negativeLeft == r.negativeRight then r.result else r.negativeLeft

def compareBits (r : Registers) (a b : List Bool) : Bool :=
  answer {r with result := if r.negativeLeft then binaryLEBitsAux r.result b a
    else binaryLEBitsAux r.result a b}

theorem compareBits_correct (a b : ℤ) :
    compareBits ⟨decide (a < 0), decide (b < 0), true⟩
      (encodeNat a.natAbs) (encodeNat b.natAbs) = decide (a ≤ b) := by
  by_cases ha : a < 0
  · by_cases hb : b < 0
    · have hm : b.natAbs ≤ a.natAbs ↔ a ≤ b := by
        rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs, Int.natCast_natAbs,
          abs_of_neg hb, abs_of_neg ha, neg_le_neg_iff]
      simp [compareBits, answer, ha, hb, hm]
    · have hab : a ≤ b := by omega
      simp [compareBits, answer, ha, hb, hab]
  · by_cases hb : b < 0
    · have hab : ¬a ≤ b := by omega
      simp [compareBits, answer, ha, hb, hab]
    · have hm : a.natAbs ≤ b.natAbs ↔ a ≤ b := by
        rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs, Int.natCast_natAbs,
          abs_of_nonneg (le_of_not_gt ha), abs_of_nonneg (le_of_not_gt hb)]
      simp [compareBits, answer, ha, hb, hm]


inductive Stack
  | input | count | work | magnitude (right : Bool) | output
  deriving DecidableEq, Fintype

inductive Label
  | sign (right : Bool) | header (right : Bool) | body (right : Bool)
  | reverse (right : Bool) | scan
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

def program : Label → TM2.Stmt Alphabet Label State
  | .sign d => .pop .input observe
      (go (.header d) (fun s => setSign d (s.a.getD false) s.regs))
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
  | .scan => .pop (.magnitude false) observe <|
      .pop (.magnitude true) observeRight <|
        .branch (fun s => s.a.isSome || s.b.isSome)
          (go .scan (fun s => update s.regs s.a s.b))
          (.push .output (fun s => answer s.regs) (.load (fun _ => state initial) .halt))

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .sign false
  σ := State
  initialState := state initial
  Γk₀Fin := Bool.fintype
  m := program

def contents (input count work left right output : List Bool) : (k : Stack) → List (Alphabet k)
  | .input => input
  | .count => count
  | .work => work
  | .magnitude false => left
  | .magnitude true => right
  | .output => output

def cfg (l : Option Label) (r : Registers) (input count work left right output : List Bool) :
    computer.Cfg := ⟨l, state r, contents input count work left right output⟩

private theorem sign_step (d sign : Bool) (r : Registers) (input left right : List Bool) :
    computer.step (cfg (some (.sign d)) r (sign :: input) [] [] left right []) =
      some (cfg (some (.header d)) (setSign d sign r) input [] [] left right []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe]
  funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem header_true (d : Bool) (r : Registers) (input count left right : List Bool) :
    computer.step (cfg (some (.header d)) r (true :: input) count [] left right []) =
      some (cfg (some (.header d)) r input (true :: count) [] left right []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
    Function.update]
  funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem header_false (d : Bool) (r : Registers) (input count left right : List Bool) :
    computer.step (cfg (some (.header d)) r (false :: input) count [] left right []) =
      some (cfg (some (.body d)) r input count [] left right []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
    Function.update]
  funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

theorem header_run (d : Bool) (r : Registers) (n : ℕ) (input count left right : List Bool) :
    (fun q => q.bind computer.step)^[n + 1]
      (some (cfg (some (.header d)) r (List.replicate n true ++ false :: input)
        count [] left right [])) =
    some (cfg (some (.body d)) r input (List.replicate n true ++ count) [] left right []) := by
  induction n generalizing count with
  | zero => simpa using header_false d r input count left right
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [Function.iterate_succ_apply, Option.bind_some, header_true, ih]
      simp [replicate_true_append_cons]

private theorem body_cons (d bit : Bool) (r : Registers)
    (input count work left right : List Bool) :
    computer.step (cfg (some (.body d)) r (bit :: input) (true :: count) work left right []) =
      some (cfg (some (.body d)) r input count (bit :: work) left right []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
    Function.update]
  funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem body_nil (d : Bool) (r : Registers) (input work left right : List Bool) :
    computer.step (cfg (some (.body d)) r input [] work left right []) =
      some (cfg (some (.reverse d)) r input [] work left right []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
    Function.update]

theorem body_run (d : Bool) (r : Registers) (bits input work left right : List Bool) :
    (fun q => q.bind computer.step)^[bits.length + 1]
      (some (cfg (some (.body d)) r (bits ++ input)
        (List.replicate bits.length true) work left right [])) =
    some (cfg (some (.reverse d)) r input [] (bits.reverse ++ work) left right []) := by
  induction bits generalizing work with
  | nil => simpa using body_nil d r input work left right
  | cons b bits ih =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append]
      rw [Function.iterate_succ_apply, Option.bind_some, body_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem reverse_cons (d bit : Bool) (r : Registers) (input work left right : List Bool) :
    computer.step (cfg (some (.reverse d)) r input [] (bit :: work) left right []) =
      some (cfg (some (.reverse d)) r input [] work
        (if d then left else bit :: left) (if d then bit :: right else right) []) := by
  cases d <;>
    simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
      Function.update]
  all_goals funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem reverse_nil (d : Bool) (r : Registers) (input left right : List Bool) :
    computer.step (cfg (some (.reverse d)) r input [] [] left right []) =
      some (cfg (some (if d then .scan else .sign true)) r input [] [] left right []) := by
  simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
    Function.update]

theorem reverse_run (d : Bool) (r : Registers) (input work left right : List Bool) :
    (fun q => q.bind computer.step)^[work.length + 1]
      (some (cfg (some (.reverse d)) r input [] work left right [])) =
    some (cfg (some (if d then .scan else .sign true)) r input [] []
      (if d then left else work.reverse ++ left)
      (if d then work.reverse ++ right else right) []) := by
  induction work generalizing left right with
  | nil => simpa using reverse_nil d r input left right
  | cons bit work ih =>
      rw [List.length_cons, Function.iterate_succ_apply, Option.bind_some, reverse_cons, ih]
      cases d <;> simp [List.reverse_cons, List.append_assoc]

/-- One framed integer is read and retained on its magnitude stack. All frame
marks and reversal scratch are emptied; the remaining input is preserved. -/
theorem field_run (d sign : Bool) (r : Registers) (bits input left right : List Bool) :
    (fun q => q.bind computer.step)^[3 * bits.length + 4]
      (some (cfg (some (.sign d)) r
        (sign :: (LeanNPHardness.BinaryNatLists.frame bits ++ input)) [] [] left right [])) =
    some (cfg (some (if d then .scan else .sign true)) (setSign d sign r) input [] []
      (if d then left else bits ++ left) (if d then bits ++ right else right) []) := by
  rw [show 3 * bits.length + 4 = ((bits.length + 1) + (bits.length + 1) +
    (bits.length + 1)) + 1 by omega, Function.iterate_succ_apply, Option.bind_some, sign_step]
  simp only [LeanNPHardness.BinaryNatLists.frame, List.append_assoc, List.cons_append]
  rw [Function.iterate_add_apply, header_run]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply, body_run]
  simp only [List.append_nil]
  have h := reverse_run d (setSign d sign r) input bits.reverse left right
  simpa using h

private theorem scan_step (r : Registers) (a b : List Bool) :
    computer.step (cfg (some .scan) r [] [] [] a b []) =
      some (if a.isEmpty && b.isEmpty then cfg none initial [] [] [] [] [] [answer r]
        else cfg (some .scan) (update r a.head? b.head?) [] [] [] a.tail b.tail []) := by
  cases a <;> cases b <;>
    simp [computer, FinTM2.step, cfg, program, go, state, contents, Alphabet, observe,
      observeRight, Function.update]
  all_goals funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

theorem scan_run (r : Registers) (a b : List Bool) :
    (fun q => q.bind computer.step)^[max a.length b.length + 1]
      (some (cfg (some .scan) r [] [] [] a b [])) =
    some (cfg none initial [] [] [] [] [] [compareBits r a b]) := by
  induction a generalizing r b with
  | nil =>
      induction b generalizing r with
      | nil => simpa [compareBits, binaryLEBitsAux] using scan_step r [] []
      | cons bit b ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply, Option.bind_some, scan_step]
          simp only [List.isEmpty_nil, List.isEmpty_cons, Bool.true_and, Bool.false_eq_true,
            ↓reduceIte, List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons]
          have h := ih (update r none (some bit))
          cases r with | mk sn sp le =>
            cases sn <;> simpa [compareBits, update, binaryLEBitsAux] using h
  | cons bit a ih =>
      cases b with
      | nil =>
          simp only [List.length_nil, List.length_cons, Nat.max_zero]
          rw [Function.iterate_succ_apply, Option.bind_some, scan_step]
          simp only [List.isEmpty_nil, List.isEmpty_cons, Bool.false_and, Bool.false_eq_true,
            ↓reduceIte, List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons]
          have h := ih (update r (some bit) none) []
          cases r with | mk sn sp le =>
            cases sn <;> simpa [compareBits, update, binaryLEBitsAux] using h
      | cons bit' b =>
          simp only [List.length_cons, Nat.succ_max_succ]
          rw [Function.iterate_succ_apply, Option.bind_some, scan_step]
          simp only [List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            List.head?_cons, List.tail_cons]
          rw [ih]
          cases r with | mk sn sp le =>
            cases sn <;> simp [compareBits, update, binaryLEBitsAux]

/-- Exact runtime, including both input frames and the final exhaustion step. -/
theorem run (a b : ℤ) :
    (fun q => q.bind computer.step)^[3 * (a.natAbs.size + b.natAbs.size) +
        max a.natAbs.size b.natAbs.size + 9]
      (some (cfg (some (.sign false)) initial (encode (a, b)) [] [] [] [] [])) =
    some (cfg none initial [] [] [] [] [] [decide (a ≤ b)]) := by
  have ha := field_run false (decide (a < 0)) initial (encodeNat a.natAbs)
    (SmithEncoding.encodeInt b) [] []
  have hb := field_run true (decide (b < 0))
    (setSign false (decide (a < 0)) initial) (encodeNat b.natAbs) [] (encodeNat a.natAbs) []
  simp only [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size,
    Bool.false_eq_true, ↓reduceIte, List.append_nil] at ha hb
  rw [show 3 * (a.natAbs.size + b.natAbs.size) + max a.natAbs.size b.natAbs.size + 9 =
    (max a.natAbs.size b.natAbs.size + 1 + (3 * b.natAbs.size + 4)) +
      (3 * a.natAbs.size + 4) by omega, Function.iterate_add_apply]
  change (fun q => q.bind computer.step)^[max a.natAbs.size b.natAbs.size + 1 + (3 * b.natAbs.size + 4)] ((fun q => q.bind computer.step)^[3 * a.natAbs.size + 4]
    (some (cfg (some (.sign false)) initial
      (decide (a < 0) :: (LeanNPHardness.BinaryNatLists.frame (encodeNat a.natAbs) ++
        SmithEncoding.encodeInt b)) [] [] [] [] []))) = _
  rw [ha, Function.iterate_add_apply]
  have hb' : (fun q => q.bind computer.step)^[3 * b.natAbs.size + 4]
      (some (cfg (some (.sign true)) (setSign false (decide (a < 0)) initial)
        (SmithEncoding.encodeInt b) [] [] (encodeNat a.natAbs) [] [])) =
      some (cfg (some .scan) ⟨decide (a < 0), decide (b < 0), true⟩
        [] [] [] (encodeNat a.natAbs) (encodeNat b.natAbs) []) := by
    simpa [SmithEncoding.encodeInt, LeanNPHardness.BinaryNatLists.encodeNat,
      setSign, initial] using hb
  rw [hb']
  have hs := scan_run ⟨decide (a < 0), decide (b < 0), true⟩
    (encodeNat a.natAbs) (encodeNat b.natAbs)
  simpa [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size, compareBits_correct] using hs

private theorem init_eq (bits : List Bool) :
    initList computer bits = cfg (some (.sign false)) initial bits [] [] [] [] [] := by
  unfold initList cfg; congr; funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

private theorem halt_eq (bits : List Bool) :
    haltList computer bits = cfg none initial [] [] [] [] [] bits := by
  unfold haltList cfg; congr; funext k; cases k <;> first | rfl | (rename_i d; cases d <;> rfl)

/-- Linear time in the actual signed/framed input bit length. -/
def outputsInTime (x : ℤ × ℤ) :
    TM2OutputsInTime computer (encode x) (some [decide (x.1 ≤ x.2)])
      (2 * (encode x).length + 1) where
  steps := 3 * (x.1.natAbs.size + x.2.natAbs.size) + max x.1.natAbs.size x.2.natAbs.size + 9
  evals_in_steps := by
    change (fun q => q.bind computer.step)^[_] (some (initList computer (encode x))) =
      some (haltList computer [decide (x.1 ≤ x.2)])
    rw [init_eq, halt_eq]
    exact run x.1 x.2
  steps_le_m := by rw [encode_length]; omega

noncomputable def computableInPolyTime :
    LeanNPHardness.TM2ComputableInPolyTime encoding LeanNPHardness.finEncodingBoolBool
      (fun x => decide (x.1 ≤ x.2)) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 1
  outputsFun x := by
    simpa [encoding, LeanNPHardness.finEncodingBoolBool, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using outputsInTime x

#print axioms compareBits_correct
#print axioms field_run
#print axioms scan_run
#print axioms run
#print axioms outputsInTime
#print axioms computableInPolyTime

end PhdThesisLean.SignedIntegerComparison
