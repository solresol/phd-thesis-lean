import PhdThesisLean.AllDifferentCSPEncoding
import LeanNPHardness.MachineCompositionExecution
import Mathlib.Computability.TMComputable

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability
open Turing
open PhdThesisLean.AllDifferentCSPEncoding
open PhdThesisLean.AllDifferentCSP.ExplicitSystem
open LeanNPHardness.MachineComposition

/-!
# Finite-machine encoding components for the all-different compiler

Every natural field in the runtime CSP and residual-objective formats is
encoded by applying `BinaryNatLists.frame` to mathlib's standard binary
natural encoding. This module constructs a concrete finite two-stack-machine
program (using four stacks) for that framing pass and proves that it runs in
linear time. A second three-stack machine traverses a stack-oriented reverse
stream of raw binary naturals and emits the exact length-prefixed framed list
format, also in linear time. A third machine performs the reverse traversal on
the standard nested-list input encoding, exposing every length and value field
as an explicitly delimited raw binary stream in linear time. A fourth finite
machine computes successor on mathlib's canonical binary natural encoding in
linear time. A fifth finite machine compares two aligned canonical binary
naturals in linear time. A sixth finite machine adds the same aligned binary
naturals by ripple carry in linear time. A seventh finite machine consumes a
unary scan bound and emits every natural in the Bertrand interval
`[q + 1, 2q]` in quadratic time; the unary interface records the eventual full
CSP invariant that the explicit input length is at least `q`. A companion
producer emits the same candidates in a checked unary-delimited stream in at
most `6(q+1)^2` steps, with stream length at most `2q^2+2q+1`, so the later
candidate-primality pass needs no binary-to-unary expansion. An eighth finite
machine decides divisibility on delimiter-separated unary-padded pairs in
linear time, including zero dividend and divisor cases. A ninth finite machine
emits the exact stack-oriented list of every padded pair `(n,d)` with
`2 ≤ d < n` in quadratic time. A tenth finite machine repeatedly applies the
divisibility program to a padded pair stream. An eleventh finite machine folds
a Boolean result stream in linear time and accepts exactly when none of the
proposed divisors divided the candidate. A fused twelfth machine performs both
passes with the Boolean fold kept in finite control, avoiding an intermediate
result stream in the eventual prime filter. A thirteenth machine composes the
quadratic pair generator with that fused pass and computes the candidate-only
primality bit in at most `64(n+1)^2` steps on unary input. The generated-stream
invariant proves that every emitted candidate is at least two and that
filtering with this machine predicate yields exactly the guarded semantic
prime-candidate list. A first-survivor driver selects from the checked unary
candidate stream, and a fourteenth machine composes that driver with the
Bertrand producer. It emits `selectPrimeAbove q` from unary `q` in at most
`1000(q+1)^6` steps, including the `q = 0,1` conventions.

These are checked components of the eventual compiler machine. They do not yet
establish polynomial time for CSP structural compilation, production of the
unary domain-entry bound, objective-row emission, or final compiler
assembly.
-/

namespace FramedNat

/-- Decode one framed natural and require that the complete input was used. -/
def decode (bits : List Bool) : Option ℕ := do
  let (n, rest) ← BinaryNatLists.decodeNatPrefix bits
  if rest = [] then some n else none

@[simp]
theorem decode_encode (n : ℕ) :
    decode (BinaryNatLists.encodeNat n) = some n := by
  have h := BinaryNatLists.decodeNatPrefix_encodeNat_append n []
  have h' : BinaryNatLists.decodeNatPrefix (BinaryNatLists.encodeNat n) =
      some (n, []) := by
    simpa using h
  rw [decode, h']
  rfl

/-- The self-delimiting binary natural encoding used inside the runtime CSP
wire format. -/
def finEncoding : FinEncoding ℕ where
  Γ := Bool
  encode := BinaryNatLists.encodeNat
  decode := decode
  decode_encode := decode_encode
  ΓFin := Bool.fintype

end FramedNat

namespace FramedNatList

/-- Decode one complete length-prefixed list of framed naturals. -/
def decode (bits : List Bool) : Option (List ℕ) := do
  let (xs, rest) ← BinaryNatLists.decodeNatListPrefix bits
  if rest = [] then some xs else none

@[simp]
theorem decode_encode (xs : List ℕ) :
    decode (BinaryNatLists.encodeNatList xs) = some xs := by
  have h := BinaryNatLists.decodeNatListPrefix_encode_append xs []
  have h' :
      BinaryNatLists.decodeNatListPrefix
          (BinaryNatLists.encodeNatList xs) = some (xs, []) := by
    simpa using h
  rw [decode, h']
  rfl

/-- The exact framed natural-list encoding used inside the runtime CSP wire
format. -/
def finEncoding : FinEncoding (List ℕ) where
  Γ := Bool
  encode := BinaryNatLists.encodeNatList
  decode := decode
  decode_encode := decode_encode
  ΓFin := Bool.fintype

end FramedNatList

namespace RawNatList

/-- One raw binary payload, reversed for stack consumption and terminated by
an explicit field marker. -/
def segment (bits : List Bool) : List (Option Bool) :=
  bits.reverse.map some ++ [none]

/-- The binary length field followed by the binary value fields. -/
def payloads (xs : List ℕ) : List (List Bool) :=
  Computability.encodeNat xs.length :: xs.map Computability.encodeNat

/-- A stack-oriented natural-list representation. Fields occur in reverse
order, and every field's bits occur in reverse order, so a stack traversal can
prepend the corresponding framed fields in their canonical order. -/
def encode (xs : List ℕ) : List (Option Bool) :=
  (payloads xs).reverse.flatMap segment

/-- Parse a raw field stream. `current` is accumulated by consing the reversed
input bits; completed fields are consed into `fields`, restoring both orders. -/
def parseAux :
    List (Option Bool) → List Bool → List (List Bool) →
      Option (List (List Bool))
  | [], [], fields => some fields
  | [], _ :: _, _ => none
  | none :: input, current, fields =>
      parseAux input [] (current :: fields)
  | some bit :: input, current, fields =>
      parseAux input (bit :: current) fields

/-- Parse the complete stack-oriented field stream. -/
def parse (input : List (Option Bool)) : Option (List (List Bool)) :=
  parseAux input [] []

private theorem parseAux_some_append
    (bits : List Bool) (input : List (Option Bool))
    (current : List Bool) (fields : List (List Bool)) :
    parseAux (bits.map some ++ input) current fields =
      parseAux input (bits.reverse ++ current) fields := by
  induction bits generalizing current with
  | nil => simp
  | cons bit bits ih =>
      simp [parseAux, ih, List.reverse_cons, List.append_assoc]

private theorem parseAux_segments
    (segments : List (List Bool)) (fields : List (List Bool)) :
    parseAux (segments.flatMap segment) [] fields =
      some (segments.reverse ++ fields) := by
  induction segments generalizing fields with
  | nil => simp [parseAux]
  | cons bits segments ih =>
      rw [List.flatMap_cons]
      simp only [segment, List.append_assoc]
      rw [parseAux_some_append]
      simp only [List.reverse_reverse]
      simp only [List.singleton_append, parseAux]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp]
theorem parse_encode (xs : List ℕ) :
    parse (encode xs) = some (payloads xs) := by
  rw [parse, encode, parseAux_segments]
  simp

/-- Decode the stack-oriented representation, checking its explicit field
count before accepting it. -/
def decode (input : List (Option Bool)) : Option (List ℕ) := do
  let fields ← parse input
  match fields with
  | [] => none
  | countBits :: valueBits =>
      if Computability.decodeNat countBits = valueBits.length then
        some (valueBits.map Computability.decodeNat)
      else
        none

@[simp]
theorem decode_encode (xs : List ℕ) : decode (encode xs) = some xs := by
  simp [decode, payloads, Function.comp_def]

/-- A checked finite encoding for the stack-oriented raw natural-list stream. -/
def finEncoding : FinEncoding (List ℕ) where
  Γ := Option Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

end RawNatList

namespace RawUnaryNatList

/-- One unary natural followed by a false field delimiter. -/
def segment (n : ℕ) : List Bool :=
  List.replicate n true ++ [false]

/-- The unary length field followed by the unary value fields. -/
def payloads (xs : List ℕ) : List ℕ :=
  xs.length :: xs

/-- A stack-oriented unary natural-list representation. Fields occur in
reverse order so a producer can prepend each successive field to its output
stack. -/
def encode (xs : List ℕ) : List Bool :=
  (payloads xs).reverse.flatMap segment

/-- Parse unary fields, accumulating the current field length and consing each
completed field so that the outer reversal is restored. -/
def parseAux : List Bool → ℕ → List ℕ → Option (List ℕ)
  | [], 0, fields => some fields
  | [], _ + 1, _ => none
  | false :: input, current, fields =>
      parseAux input 0 (current :: fields)
  | true :: input, current, fields =>
      parseAux input (current + 1) fields

def parse (input : List Bool) : Option (List ℕ) :=
  parseAux input 0 []

private theorem parseAux_replicate_true
    (n : ℕ) (input : List Bool) (current : ℕ) (fields : List ℕ) :
    parseAux (List.replicate n true ++ input) current fields =
      parseAux input (current + n) fields := by
  induction n generalizing current with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [List.cons_append, parseAux]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (current := current + 1)

private theorem parseAux_segments
    (segments : List ℕ) (fields : List ℕ) :
    parseAux (segments.flatMap segment) 0 fields =
      some (segments.reverse ++ fields) := by
  induction segments generalizing fields with
  | nil => simp [parseAux]
  | cons n segments ih =>
      rw [List.flatMap_cons]
      simp only [segment, List.append_assoc]
      rw [parseAux_replicate_true]
      simp only [List.singleton_append, parseAux, Nat.zero_add]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp]
theorem parse_encode (xs : List ℕ) :
    parse (encode xs) = some (payloads xs) := by
  rw [parse, encode, parseAux_segments]
  simp

/-- Decode the unary field stream, checking its explicit field count. -/
def decode (input : List Bool) : Option (List ℕ) := do
  let fields ← parse input
  match fields with
  | [] => none
  | count :: values =>
      if count = values.length then some values else none

@[simp]
theorem decode_encode (xs : List ℕ) : decode (encode xs) = some xs := by
  simp [decode, payloads]

/-- Checked finite encoding for a stack-oriented unary natural list. -/
def finEncoding : FinEncoding (List ℕ) where
  Γ := Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := Bool.fintype

@[simp]
theorem segment_length (n : ℕ) : (segment n).length = n + 1 := by
  simp [segment]

private theorem segments_length (ns : List ℕ) :
    (ns.flatMap segment).length = ns.sum + ns.length := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
      simp [segment, ih]
      omega

@[simp]
theorem encode_length (xs : List ℕ) :
    (encode xs).length = xs.sum + 2 * xs.length + 1 := by
  rw [encode, segments_length]
  simp [payloads]
  omega

end RawUnaryNatList

namespace RawNatLists

/-- Raw binary payloads underlying the standard nested-list encoding: the
outer length, then each inner length and its natural fields. -/
def payloads (xss : List (List ℕ)) : List (List Bool) :=
  Computability.encodeNat xss.length ::
    xss.flatMap fun xs =>
      Computability.encodeNat xs.length :: xs.map Computability.encodeNat

/-- A stack-oriented nested-list representation. Every raw field is reversed
and delimited, and the complete field sequence is reversed for stack
consumption. -/
def encode (xss : List (List ℕ)) : List (Option Bool) :=
  (payloads xss).reverse.flatMap RawNatList.segment

private theorem parseAux_some_append
    (bits : List Bool) (input : List (Option Bool))
    (current : List Bool) (fields : List (List Bool)) :
    RawNatList.parseAux (bits.map some ++ input) current fields =
      RawNatList.parseAux input (bits.reverse ++ current) fields := by
  induction bits generalizing current with
  | nil => simp
  | cons bit bits ih =>
      simp [RawNatList.parseAux, ih, List.reverse_cons, List.append_assoc]

private theorem parseAux_segments
    (segments : List (List Bool)) (fields : List (List Bool)) :
    RawNatList.parseAux
        (segments.flatMap RawNatList.segment) [] fields =
      some (segments.reverse ++ fields) := by
  induction segments generalizing fields with
  | nil => simp [RawNatList.parseAux]
  | cons bits segments ih =>
      rw [List.flatMap_cons]
      simp only [RawNatList.segment, List.append_assoc]
      rw [parseAux_some_append]
      simp only [List.reverse_reverse]
      simp only [List.singleton_append, RawNatList.parseAux]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp]
theorem parse_encode (xss : List (List ℕ)) :
    RawNatList.parse (encode xss) = some (payloads xss) := by
  rw [RawNatList.parse, encode, parseAux_segments]
  simp

private theorem innerPayloads_frame
    (xss : List (List ℕ)) :
    List.flatMap BinaryNatLists.frame
        (xss.flatMap fun xs =>
          Computability.encodeNat xs.length :: xs.map Computability.encodeNat) =
      xss.flatMap BinaryNatLists.encodeNatList := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
      simp only [List.flatMap_cons, List.flatMap_append,
        List.flatMap_cons, List.flatMap_map, ih]
      simp only [BinaryNatLists.encodeNatList]
      have hencode :
          (fun n => BinaryNatLists.frame (Computability.encodeNat n)) =
            BinaryNatLists.encodeNat := by
        funext n
        rfl
      rw [hencode]
      rfl

theorem payloads_frame_eq_encode (xss : List (List ℕ)) :
    (payloads xss).flatMap BinaryNatLists.frame =
      BinaryNatLists.encode xss := by
  rw [payloads, List.flatMap_cons, BinaryNatLists.encode,
    innerPayloads_frame]
  rfl

/-- Decode a raw field stream by restoring the standard nested-list frames. -/
def decode (input : List (Option Bool)) : Option (List (List ℕ)) := do
  let fields ← RawNatList.parse input
  BinaryNatLists.decode (fields.flatMap BinaryNatLists.frame)

@[simp]
theorem decode_encode (xss : List (List ℕ)) :
    decode (encode xss) = some xss := by
  simp [decode, payloads_frame_eq_encode]

/-- Checked raw-field encoding of nested natural-number lists. -/
def finEncoding : FinEncoding (List (List ℕ)) where
  Γ := Option Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

end RawNatLists

/-- Four Boolean stacks suffice to preserve the payload while prefixing its
length: input, reversed payload, unary counter, and output. -/
inductive FrameStack
  | input
  | scratch
  | count
  | output
  deriving DecidableEq, Fintype

/-- The three traversal phases of the framing program. -/
inductive FrameLabel
  | stash
  | restore
  | prefix
  deriving DecidableEq, Fintype

/-- The local state holds the bit most recently popped from a stack. -/
abbrev FrameState := Option Bool

private def poppedBit (_ : FrameState) (bit : Option Bool) : FrameState :=
  bit

private def heldBit : FrameState → Bool
  | some bit => bit
  | none => false

/-- The finite framing program.  `stash` reverses the payload and records its
unary length, `restore` restores the payload on the output stack and adds the
separator, and `prefix` moves the unary length in front of it. -/
def frameProgram :
    FrameLabel → TM2.Stmt (fun _ : FrameStack => Bool) FrameLabel FrameState
  | .stash =>
      .pop .input poppedBit <|
        .branch Option.isSome
          (.push .scratch heldBit <|
            .push .count (fun _ => true) <|
              .goto (fun _ => .stash))
          (.goto (fun _ => .restore))
  | .restore =>
      .pop .scratch poppedBit <|
        .branch Option.isSome
          (.push .output heldBit <|
            .goto (fun _ => .restore))
          (.push .output (fun _ => false) <|
            .goto (fun _ => .prefix))
  | .prefix =>
      .pop .count poppedBit <|
        .branch Option.isSome
          (.push .output (fun _ => true) <|
            .goto (fun _ => .prefix))
          .halt

/-- The concrete finite machine implementing `BinaryNatLists.frame`. -/
def frameComputer : FinTM2 where
  K := FrameStack
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := FrameLabel
  main := .stash
  σ := FrameState
  initialState := none
  Γk₀Fin := Bool.fintype
  m := frameProgram

private def stackContents
    (input scratch count output : List Bool) :
    FrameStack → List Bool
  | .input => input
  | .scratch => scratch
  | .count => count
  | .output => output

private def cfg (label : Option FrameLabel) (state : FrameState)
    (input scratch count output : List Bool) : frameComputer.Cfg where
  l := label
  var := state
  stk := stackContents input scratch count output

private theorem step_stash_cons (bit : Bool) (input scratch count output : List Bool)
    (state : FrameState) :
    frameComputer.step
        (cfg (some .stash) state (bit :: input) scratch count output) =
      some (cfg (some .stash) (some bit) input (bit :: scratch)
        (true :: count) output) := by
  simp [frameComputer, FinTM2.step, cfg, frameProgram, stackContents,
    poppedBit, heldBit, Function.update]
  funext index
  cases index <;> rfl

private theorem step_stash_nil (scratch count output : List Bool)
    (state : FrameState) :
    frameComputer.step (cfg (some .stash) state [] scratch count output) =
      some (cfg (some .restore) none [] scratch count output) := by
  simp [frameComputer, FinTM2.step, cfg, frameProgram, stackContents,
    poppedBit, Function.update]

private theorem step_restore_cons (bit : Bool) (scratch count output : List Bool)
    (state : FrameState) :
    frameComputer.step
        (cfg (some .restore) state [] (bit :: scratch) count output) =
      some (cfg (some .restore) (some bit) [] scratch count (bit :: output)) := by
  simp [frameComputer, FinTM2.step, cfg, frameProgram, stackContents,
    poppedBit, heldBit, Function.update]
  funext index
  cases index <;> rfl

private theorem step_restore_nil (count output : List Bool)
    (state : FrameState) :
    frameComputer.step (cfg (some .restore) state [] [] count output) =
      some (cfg (some .prefix) none [] [] count (false :: output)) := by
  simp [frameComputer, FinTM2.step, cfg, frameProgram, stackContents,
    poppedBit, Function.update]
  funext index
  cases index <;> rfl

private theorem step_prefix_cons (tick : Bool) (count output : List Bool)
    (state : FrameState) :
    frameComputer.step
        (cfg (some .prefix) state [] [] (tick :: count) output) =
      some (cfg (some .prefix) (some tick) [] [] count (true :: output)) := by
  simp [frameComputer, FinTM2.step, cfg, frameProgram, stackContents,
    poppedBit, Function.update]
  funext index
  cases index <;> rfl

private theorem step_prefix_nil (output : List Bool) (state : FrameState) :
    frameComputer.step (cfg (some .prefix) state [] [] [] output) =
      some (cfg none none [] [] [] output) := by
  simp [frameComputer, FinTM2.step, cfg, frameProgram, stackContents,
    poppedBit, Function.update]

private def evalsToInTimeOne
    {start finish : frameComputer.Cfg}
    (hstep : frameComputer.step start = some finish) :
    EvalsToInTime frameComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem replicate_true_append_cons (n : ℕ) (tail : List Bool) :
    List.replicate n true ++ true :: tail =
      true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private def stash_evals
    (input scratch count output : List Bool) (state : FrameState) :
    EvalsToInTime frameComputer.step
      (cfg (some .stash) state input scratch count output)
      (some (cfg (some .restore) none [] (input.reverse ++ scratch)
        (List.replicate input.length true ++ count) output))
      (input.length + 1) := by
  induction input generalizing scratch count state with
  | nil =>
      simpa using evalsToInTimeOne (step_stash_nil scratch count output state)
  | cons bit input ih =>
      let middle := cfg (some .stash) (some bit) input (bit :: scratch)
        (true :: count) output
      have hone : EvalsToInTime frameComputer.step
          (cfg (some .stash) state (bit :: input) scratch count output)
          (some middle) 1 :=
        evalsToInTimeOne (step_stash_cons bit input scratch count output state)
      have hrest := ih (bit :: scratch) (true :: count) (some bit)
      have htrans := EvalsToInTime.trans frameComputer.step 1
        (input.length + 1)
        (cfg (some .stash) state (bit :: input) scratch count output)
        middle
        (some (cfg (some .restore) none []
          ((bit :: input).reverse ++ scratch)
          (List.replicate (bit :: input).length true ++ count) output))
        hone
        (by
          simpa [middle, List.reverse_cons, List.replicate_succ,
            List.append_assoc, replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def restore_evals
    (scratch count output : List Bool) (state : FrameState) :
    EvalsToInTime frameComputer.step
      (cfg (some .restore) state [] scratch count output)
      (some (cfg (some .prefix) none [] [] count
        (false :: (scratch.reverse ++ output))))
      (scratch.length + 1) := by
  induction scratch generalizing output state with
  | nil =>
      simpa using evalsToInTimeOne (step_restore_nil count output state)
  | cons bit scratch ih =>
      let middle := cfg (some .restore) (some bit) [] scratch count
        (bit :: output)
      have hone : EvalsToInTime frameComputer.step
          (cfg (some .restore) state [] (bit :: scratch) count output)
          (some middle) 1 :=
        evalsToInTimeOne
          (step_restore_cons bit scratch count output state)
      have hrest := ih (bit :: output) (some bit)
      have htrans := EvalsToInTime.trans frameComputer.step 1
        (scratch.length + 1)
        (cfg (some .restore) state [] (bit :: scratch) count output)
        middle
        (some (cfg (some .prefix) none [] [] count
          (false :: ((bit :: scratch).reverse ++ output))))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def prefix_evals
    (count output : List Bool) (state : FrameState) :
    EvalsToInTime frameComputer.step
      (cfg (some .prefix) state [] [] count output)
      (some (cfg none none [] [] []
        (List.replicate count.length true ++ output)))
      (count.length + 1) := by
  induction count generalizing output state with
  | nil =>
      simpa using evalsToInTimeOne (step_prefix_nil output state)
  | cons tick count ih =>
      let middle := cfg (some .prefix) (some tick) [] [] count
        (true :: output)
      have hone : EvalsToInTime frameComputer.step
          (cfg (some .prefix) state [] [] (tick :: count) output)
          (some middle) 1 :=
        evalsToInTimeOne (step_prefix_cons tick count output state)
      have hrest := ih (true :: output) (some tick)
      have htrans := EvalsToInTime.trans frameComputer.step 1
        (count.length + 1)
        (cfg (some .prefix) state [] [] (tick :: count) output)
        middle
        (some (cfg none none [] [] []
          (List.replicate (tick :: count).length true ++ output)))
        hone
        (by
          simpa [middle, List.replicate_succ, List.append_assoc,
            replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private theorem initList_eq_cfg (bits : List Bool) :
    initList frameComputer bits = cfg (some .stash) none bits [] [] [] := by
  unfold initList cfg
  congr
  funext index
  cases index <;> rfl

private theorem haltList_eq_cfg (bits : List Bool) :
    haltList frameComputer bits = cfg none none [] [] [] bits := by
  unfold haltList cfg
  congr
  funext index
  cases index <;> rfl

/-- The framing machine emits the self-delimiting payload in exactly
`3 * bits.length + 3` machine steps. -/
def frame_outputsInTime (bits : List Bool) :
    TM2OutputsInTime frameComputer bits
      (some (BinaryNatLists.frame bits)) (3 * bits.length + 3) := by
  have hstash := stash_evals bits [] [] [] none
  have hrestore := restore_evals bits.reverse
    (List.replicate bits.length true) [] none
  have hprefix := prefix_evals (List.replicate bits.length true)
    (false :: bits) none
  have hfirst := EvalsToInTime.trans frameComputer.step
    (bits.length + 1) (bits.length + 1)
    (cfg (some .stash) none bits [] [] [])
    (cfg (some .restore) none [] bits.reverse
      (List.replicate bits.length true) [])
    (some (cfg (some .prefix) none [] []
      (List.replicate bits.length true) (false :: bits)))
    (by simpa using hstash)
    (by simpa using hrestore)
  have hall := EvalsToInTime.trans frameComputer.step
    ((bits.length + 1) + (bits.length + 1))
    (bits.length + 1)
    (cfg (some .stash) none bits [] [] [])
    (cfg (some .prefix) none [] []
      (List.replicate bits.length true) (false :: bits))
    (some (cfg none none [] [] [] (BinaryNatLists.frame bits)))
    hfirst
    (by simpa [BinaryNatLists.frame] using hprefix)
  rw [TM2OutputsInTime, initList_eq_cfg]
  simp only [Option.map_some]
  rw [haltList_eq_cfg]
  have htime :
      bits.length + 1 + (bits.length + 1 + (bits.length + 1)) =
        3 * bits.length + 3 := by
    omega
  simpa only [htime] using hall

/-- A genuine polynomial-time machine witness for changing the encoding of a
natural from mathlib's raw binary representation to the self-delimiting
framed representation used by the CSP wire format.  The computed mathematical
function is the identity; the machine performs the nontrivial encoding pass. -/
noncomputable def framedNatComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ ℕ Computability.finEncodingNatBool
      FramedNat.finEncoding id where
  tm := frameComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 3 * Polynomial.X + 3
  outputsFun n := by
    simpa [Computability.finEncodingNatBool,
      Computability.encodingNatBool, FramedNat.finEncoding,
      BinaryNatLists.encodeNat, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_X] using
        frame_outputsInTime (Computability.encodeNat n)

/-- Three stacks suffice for the list serializer: the raw field stream, a
unary counter for the current field, and the framed output. -/
inductive ListFrameStack
  | input
  | count
  | output
  deriving DecidableEq, Fintype

/-- The serializer alternates between scanning a field, prefixing its length,
and checking whether another field remains. -/
inductive ListFrameLabel
  | scan
  | prefix
  | next
  deriving DecidableEq, Fintype

/-- The finite control remembers the last raw symbol and the last unary-count
symbol popped from their heterogeneous stacks. -/
structure ListFrameState where
  raw : Option (Option Bool)
  tick : Option Bool
  deriving DecidableEq, Fintype

private def listFrameInitialState : ListFrameState :=
  ⟨none, none⟩

private def listPoppedRaw
    (state : ListFrameState) (symbol : Option (Option Bool)) :
    ListFrameState :=
  { state with raw := symbol }

private def listPoppedTick
    (state : ListFrameState) (tick : Option Bool) : ListFrameState :=
  { state with tick := tick }

private def listRawIsBit : ListFrameState → Bool
  | ⟨some (some _), _⟩ => true
  | _ => false

private def listRawPresent : ListFrameState → Bool
  | ⟨some _, _⟩ => true
  | _ => false

private def listHeldBit : ListFrameState → Bool
  | ⟨some (some bit), _⟩ => bit
  | _ => false

private def listTickPresent : ListFrameState → Bool
  | ⟨_, some _⟩ => true
  | _ => false

private def ListFrameAlphabet : ListFrameStack → Type
  | .input => Option Bool
  | .count => Bool
  | .output => Bool

/-- The finite list-framing program. Scanning reversed payload bits prepends
each payload in forward order. The delimiter adds `false`; the counter then
adds the unary length prefix. Since fields arrive in reverse order, the final
output has the canonical list order. -/
def listFrameProgram :
    ListFrameLabel →
      TM2.Stmt ListFrameAlphabet ListFrameLabel ListFrameState
  | .scan =>
      .pop .input listPoppedRaw <|
        .branch listRawIsBit
          (.push .output listHeldBit <|
            .push .count (fun _ => true) <|
              .goto (fun _ => .scan))
          (.push .output (fun _ => false) <|
            .goto (fun _ => .prefix))
  | .prefix =>
      .pop .count listPoppedTick <|
        .branch listTickPresent
          (.push .output (fun _ => true) <|
            .goto (fun _ => .prefix))
          (.goto (fun _ => .next))
  | .next =>
      .peek .input listPoppedRaw <|
        .branch listRawPresent
          (.goto (fun _ => .scan))
          .halt

/-- The concrete finite machine serializing stack-oriented natural lists. -/
def listFrameComputer : FinTM2 where
  K := ListFrameStack
  k₀ := .input
  k₁ := .output
  Γ := ListFrameAlphabet
  Λ := ListFrameLabel
  main := .scan
  σ := ListFrameState
  initialState := listFrameInitialState
  Γk₀Fin := by
    change Fintype (Option Bool)
    infer_instance
  m := listFrameProgram

private def listStackContents
    (input : List (Option Bool)) (count output : List Bool) :
    (index : ListFrameStack) → List (ListFrameAlphabet index)
  | .input => input
  | .count => count
  | .output => output

private def listCfg (label : Option ListFrameLabel)
    (state : ListFrameState) (input : List (Option Bool))
    (count output : List Bool) : listFrameComputer.Cfg where
  l := label
  var := state
  stk := listStackContents input count output

private theorem list_step_scan_bit (bit : Bool)
    (input : List (Option Bool)) (count output : List Bool)
    (state : ListFrameState) :
    listFrameComputer.step
        (listCfg (some .scan) state (some bit :: input) count output) =
      some (listCfg (some .scan)
        (listPoppedRaw state (some (some bit))) input
        (true :: count) (bit :: output)) := by
  simp [listFrameComputer, FinTM2.step, listCfg, listFrameProgram,
    listStackContents, ListFrameAlphabet, listPoppedRaw, listRawIsBit,
    listHeldBit, Function.update]
  funext index
  cases index <;> rfl

private theorem list_step_scan_delimiter
    (input : List (Option Bool)) (count output : List Bool)
    (state : ListFrameState) :
    listFrameComputer.step
        (listCfg (some .scan) state (none :: input) count output) =
      some (listCfg (some .prefix)
        (listPoppedRaw state (some none)) input count (false :: output)) := by
  simp [listFrameComputer, FinTM2.step, listCfg, listFrameProgram,
    listStackContents, ListFrameAlphabet, listPoppedRaw, listRawIsBit,
    Function.update]
  funext index
  cases index <;> rfl

private theorem list_step_prefix_cons (tick : Bool)
    (input : List (Option Bool)) (count output : List Bool)
    (state : ListFrameState) :
    listFrameComputer.step
        (listCfg (some .prefix) state input (tick :: count) output) =
      some (listCfg (some .prefix)
        (listPoppedTick state (some tick)) input count (true :: output)) := by
  simp [listFrameComputer, FinTM2.step, listCfg, listFrameProgram,
    listStackContents, ListFrameAlphabet, listPoppedTick,
    listTickPresent, Function.update]
  funext index
  cases index <;> rfl

private theorem list_step_prefix_nil (input : List (Option Bool))
    (output : List Bool) (state : ListFrameState) :
    listFrameComputer.step
        (listCfg (some .prefix) state input [] output) =
      some (listCfg (some .next) (listPoppedTick state none)
        input [] output) := by
  simp [listFrameComputer, FinTM2.step, listCfg, listFrameProgram,
    listStackContents, ListFrameAlphabet, listPoppedTick,
    listTickPresent, Function.update]

private theorem list_step_next_cons (symbol : Option Bool)
    (input : List (Option Bool)) (output : List Bool)
    (state : ListFrameState) :
    listFrameComputer.step
        (listCfg (some .next) state (symbol :: input) [] output) =
      some (listCfg (some .scan)
        (listPoppedRaw state (some symbol)) (symbol :: input) [] output) := by
  simp [listFrameComputer, FinTM2.step, listCfg, listFrameProgram,
    listStackContents, ListFrameAlphabet, listPoppedRaw, listRawPresent]

private theorem list_step_next_nil (output : List Bool)
    (raw : Option (Option Bool)) :
    listFrameComputer.step
        (listCfg (some .next) ⟨raw, none⟩ [] [] output) =
      some (listCfg none listFrameInitialState [] [] output) := by
  simp [listFrameComputer, FinTM2.step, listCfg, listFrameProgram,
    listStackContents, ListFrameAlphabet, listPoppedRaw, listRawPresent,
    listFrameInitialState]

private def evalsToInTimeMono {configuration : Type*}
    {step : configuration → Option configuration}
    {start : configuration} {finish : Option configuration} {m n : ℕ}
    (h : EvalsToInTime step start finish m) (hmn : m ≤ n) :
    EvalsToInTime step start finish n where
  toEvalsTo := h.toEvalsTo
  steps_le_m := h.steps_le_m.trans hmn

private def listEvalsToInTimeOne
    {start finish : listFrameComputer.Cfg}
    (hstep : listFrameComputer.step start = some finish) :
    EvalsToInTime listFrameComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def list_scanSegment_evals
    (reversedBits : List Bool) (input : List (Option Bool))
    (count output : List Bool) (state : ListFrameState) :
    EvalsToInTime listFrameComputer.step
      (listCfg (some .scan) state
        (reversedBits.map some ++ none :: input) count output)
      (some (listCfg (some .prefix)
        (listPoppedRaw state (some none)) input
        (List.replicate reversedBits.length true ++ count)
        (false :: (reversedBits.reverse ++ output))))
      (reversedBits.length + 1) := by
  induction reversedBits generalizing count output state with
  | nil =>
      simpa using listEvalsToInTimeOne
        (list_step_scan_delimiter input count output state)
  | cons bit reversedBits ih =>
      let middle := listCfg (some .scan)
        (listPoppedRaw state (some (some bit)))
        (reversedBits.map some ++ none :: input)
        (true :: count) (bit :: output)
      have hone : EvalsToInTime listFrameComputer.step
          (listCfg (some .scan) state
            ((bit :: reversedBits).map some ++ none :: input) count output)
          (some middle) 1 :=
        listEvalsToInTimeOne (by
          simpa [middle] using
            list_step_scan_bit bit
              (reversedBits.map some ++ none :: input) count output state)
      have hrest := ih (true :: count) (bit :: output)
        (listPoppedRaw state (some (some bit)))
      have htrans := EvalsToInTime.trans listFrameComputer.step
        1 (reversedBits.length + 1)
        (listCfg (some .scan) state
          ((bit :: reversedBits).map some ++ none :: input) count output)
        middle
        (some (listCfg (some .prefix)
          (listPoppedRaw state (some none)) input
          (List.replicate (bit :: reversedBits).length true ++ count)
          (false :: ((bit :: reversedBits).reverse ++ output))))
        hone
        (by
          simpa [middle, listPoppedRaw, List.reverse_cons,
            List.append_assoc, replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def list_prefix_evals
    (count : List Bool) (input : List (Option Bool))
    (output : List Bool) (state : ListFrameState) :
    EvalsToInTime listFrameComputer.step
      (listCfg (some .prefix) state input count output)
      (some (listCfg (some .next) (listPoppedTick state none)
        input [] (List.replicate count.length true ++ output)))
      (count.length + 1) := by
  induction count generalizing output state with
  | nil =>
      simpa using listEvalsToInTimeOne
        (list_step_prefix_nil input output state)
  | cons tick count ih =>
      let middle := listCfg (some .prefix)
        (listPoppedTick state (some tick)) input count (true :: output)
      have hone : EvalsToInTime listFrameComputer.step
          (listCfg (some .prefix) state input (tick :: count) output)
          (some middle) 1 :=
        listEvalsToInTimeOne
          (list_step_prefix_cons tick input count output state)
      have hrest := ih (true :: output) (listPoppedTick state (some tick))
      have htrans := EvalsToInTime.trans listFrameComputer.step
        1 (count.length + 1)
        (listCfg (some .prefix) state input (tick :: count) output)
        middle
        (some (listCfg (some .next) (listPoppedTick state none)
          input [] (List.replicate (tick :: count).length true ++ output)))
        hone
        (by
          simpa [middle, listPoppedTick, List.append_assoc,
            replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def list_next_present_evals
    (input : List (Option Bool)) (hinput : input ≠ [])
    (output : List Bool) (state : ListFrameState) :
    EvalsToInTime listFrameComputer.step
      (listCfg (some .next) state input [] output)
      (some (listCfg (some .scan)
        (listPoppedRaw state input.head?) input [] output)) 1 := by
  cases input with
  | nil => exact (hinput rfl).elim
  | cons symbol input =>
      simpa using listEvalsToInTimeOne
        (list_step_next_cons symbol input output state)

private theorem segment_nonempty (bits : List Bool) :
    RawNatList.segment bits ≠ [] := by
  simp [RawNatList.segment]

private theorem segments_flatMap_nonempty
    (bits : List Bool) (segments : List (List Bool)) :
    (bits :: segments).flatMap RawNatList.segment ≠ [] := by
  simp [RawNatList.segment]

private def list_segments_evals
    (segments : List (List Bool)) (hsegments : segments ≠ [])
    (output : List Bool) (state : ListFrameState) :
    EvalsToInTime listFrameComputer.step
      (listCfg (some .scan) state
        (segments.flatMap RawNatList.segment) [] output)
      (some (listCfg none listFrameInitialState [] []
        (segments.reverse.flatMap BinaryNatLists.frame ++ output)))
      (2 * (segments.flatMap RawNatList.segment).length + segments.length) := by
  induction segments generalizing output state with
  | nil => exact (hsegments rfl).elim
  | cons bits segments ih =>
      let tailInput := segments.flatMap RawNatList.segment
      have hscan := list_scanSegment_evals bits.reverse tailInput [] output state
      have hprefix := list_prefix_evals
        (List.replicate bits.length true) tailInput
        (false :: (bits ++ output))
        (listPoppedRaw state (some none))
      have hfirst := EvalsToInTime.trans listFrameComputer.step
        (bits.length + 1) (bits.length + 1)
        (listCfg (some .scan) state
          ((bits :: segments).flatMap RawNatList.segment) [] output)
        (listCfg (some .prefix) (listPoppedRaw state (some none))
          tailInput (List.replicate bits.length true)
          (false :: (bits ++ output)))
        (some (listCfg (some .next)
          (listPoppedTick (listPoppedRaw state (some none)) none)
          tailInput [] (BinaryNatLists.frame bits ++ output)))
        (by simpa [tailInput, RawNatList.segment] using hscan)
        (by
          simpa [BinaryNatLists.frame, listPoppedTick,
            List.append_assoc] using hprefix)
      cases segments with
      | nil =>
          have hnext := listEvalsToInTimeOne
            (list_step_next_nil (BinaryNatLists.frame bits ++ output)
              (listPoppedRaw state (some none)).raw)
          have hall := EvalsToInTime.trans listFrameComputer.step
            ((bits.length + 1) + (bits.length + 1)) 1
            (listCfg (some .scan) state
              ([bits].flatMap RawNatList.segment) [] output)
            (listCfg (some .next)
              (listPoppedTick (listPoppedRaw state (some none)) none)
              [] [] (BinaryNatLists.frame bits ++ output))
            (some (listCfg none listFrameInitialState [] []
              (BinaryNatLists.frame bits ++ output)))
            (by simpa [tailInput] using hfirst)
            (by simpa [listPoppedTick, listPoppedRaw] using hnext)
          refine evalsToInTimeMono (by
            simpa [RawNatList.segment] using hall) ?_
          change
            1 + ((bits.length + 1) + (bits.length + 1)) ≤
              2 * ([bits].flatMap RawNatList.segment).length + [bits].length
          simp [RawNatList.segment]
          omega
      | cons next segments =>
          let rest := next :: segments
          have htail :
              (rest.flatMap RawNatList.segment) ≠ [] :=
            segments_flatMap_nonempty next segments
          have hnext := list_next_present_evals
            (rest.flatMap RawNatList.segment) htail
            (BinaryNatLists.frame bits ++ output)
            (listPoppedTick (listPoppedRaw state (some none)) none)
          have hthroughNext := EvalsToInTime.trans listFrameComputer.step
            ((bits.length + 1) + (bits.length + 1)) 1
            (listCfg (some .scan) state
              ((bits :: rest).flatMap RawNatList.segment) [] output)
            (listCfg (some .next)
              (listPoppedTick (listPoppedRaw state (some none)) none)
              (rest.flatMap RawNatList.segment) []
              (BinaryNatLists.frame bits ++ output))
            (some (listCfg (some .scan)
              (listPoppedRaw
                (listPoppedTick (listPoppedRaw state (some none)) none)
                (rest.flatMap RawNatList.segment).head?)
              (rest.flatMap RawNatList.segment) []
              (BinaryNatLists.frame bits ++ output)))
            (by simpa [tailInput, rest] using hfirst)
            hnext
          have hrest := ih (by simp)
            (BinaryNatLists.frame bits ++ output)
            (listPoppedRaw
              (listPoppedTick (listPoppedRaw state (some none)) none)
              (rest.flatMap RawNatList.segment).head?)
          have hall := EvalsToInTime.trans listFrameComputer.step
            (1 + ((bits.length + 1) + (bits.length + 1)))
            (2 * (rest.flatMap RawNatList.segment).length + rest.length)
            (listCfg (some .scan) state
              ((bits :: rest).flatMap RawNatList.segment) [] output)
            (listCfg (some .scan)
              (listPoppedRaw
                (listPoppedTick (listPoppedRaw state (some none)) none)
                (rest.flatMap RawNatList.segment).head?)
              (rest.flatMap RawNatList.segment) []
              (BinaryNatLists.frame bits ++ output))
            (some (listCfg none listFrameInitialState [] []
              ((bits :: rest).reverse.flatMap BinaryNatLists.frame ++ output)))
            hthroughNext
            (by
              simpa [rest, List.reverse_cons, List.append_assoc] using hrest)
          refine evalsToInTimeMono (by
            simpa [rest, RawNatList.segment, List.reverse_cons,
              List.append_assoc] using hall) ?_
          simp [RawNatList.segment]
          omega

private theorem segments_length_le_raw_length
    (segments : List (List Bool)) :
    segments.length ≤ (segments.flatMap RawNatList.segment).length := by
  induction segments with
  | nil => simp
  | cons bits segments ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have hpositive : 0 < (RawNatList.segment bits).length := by
        simp [RawNatList.segment]
      omega

private theorem payloads_frame_eq_encodeNatList (xs : List ℕ) :
    (RawNatList.payloads xs).flatMap BinaryNatLists.frame =
      BinaryNatLists.encodeNatList xs := by
  rw [RawNatList.payloads, List.flatMap_cons,
    BinaryNatLists.encodeNatList]
  change
    BinaryNatLists.frame (Computability.encodeNat xs.length) ++
        (xs.map Computability.encodeNat).flatMap BinaryNatLists.frame =
      BinaryNatLists.frame (Computability.encodeNat xs.length) ++
        xs.flatMap
          (fun n => BinaryNatLists.frame (Computability.encodeNat n))
  rw [List.flatMap_map]

private theorem list_initList_eq_cfg (input : List (Option Bool)) :
    initList listFrameComputer input =
      listCfg (some .scan) listFrameInitialState input [] [] := by
  unfold initList listCfg
  congr
  funext index
  cases index <;> rfl

private theorem list_haltList_eq_cfg (output : List Bool) :
    haltList listFrameComputer output =
      listCfg none listFrameInitialState [] [] output := by
  unfold haltList listCfg
  congr
  funext index
  cases index <;> rfl

/-- The list serializer traverses every raw field and emits the exact canonical
length-prefixed framed list in at most three times the raw input length. -/
def listFrame_outputsInTime (xs : List ℕ) :
    TM2OutputsInTime listFrameComputer (RawNatList.encode xs)
      (some (BinaryNatLists.encodeNatList xs))
      (3 * (RawNatList.encode xs).length) := by
  have hpayloads : RawNatList.payloads xs ≠ [] := by
    simp [RawNatList.payloads]
  have hpayloadsReverse : (RawNatList.payloads xs).reverse ≠ [] := by
    intro hreverse
    apply hpayloads
    have := congrArg List.reverse hreverse
    simpa using this
  have hsegments := list_segments_evals
    (RawNatList.payloads xs).reverse
    hpayloadsReverse [] listFrameInitialState
  have hlength :=
    segments_length_le_raw_length (RawNatList.payloads xs).reverse
  have hbound :
      2 * (RawNatList.encode xs).length +
          (RawNatList.payloads xs).reverse.length ≤
        3 * (RawNatList.encode xs).length := by
    change (RawNatList.payloads xs).reverse.length ≤
      (RawNatList.encode xs).length at hlength
    omega
  have hmono := evalsToInTimeMono hsegments (by
    simpa [RawNatList.encode] using hbound)
  rw [TM2OutputsInTime, list_initList_eq_cfg]
  simp only [Option.map_some]
  rw [list_haltList_eq_cfg]
  simpa [RawNatList.encode, payloads_frame_eq_encodeNatList] using hmono

/-- A genuine linear-time finite-machine witness converting the natural
stack-stream representation into the exact framed list encoding used by the
runtime CSP compiler. -/
noncomputable def framedNatListComputableInPolyTime :
    @TM2ComputableInPolyTime (List ℕ) (List ℕ) RawNatList.finEncoding
      FramedNatList.finEncoding id where
  tm := listFrameComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := 3 * Polynomial.X
  outputsFun xs := by
    simpa [RawNatList.finEncoding, FramedNatList.finEncoding, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_X] using
        listFrame_outputsInTime xs

/-- Three heterogeneous stacks suffice to expose a framed input stream as
raw delimited fields: the canonical Boolean input, a unary field counter, and
the stack-oriented raw output. -/
inductive UnframeStack
  | input
  | count
  | output
  deriving DecidableEq, Fintype

/-- The input traversal scans a unary prefix, copies the counted payload, and
then checks whether another framed field remains. -/
inductive UnframeLabel
  | scan
  | payload
  | next
  deriving DecidableEq, Fintype

/-- Finite control remembers the latest input bit and unary counter symbol. -/
structure UnframeState where
  inputBit : Option Bool
  tick : Option Bool
  deriving DecidableEq, Fintype

private def unframeInitialState : UnframeState :=
  ⟨none, none⟩

private def unframePoppedInput
    (state : UnframeState) (bit : Option Bool) : UnframeState :=
  { state with inputBit := bit }

private def unframePoppedTick
    (state : UnframeState) (tick : Option Bool) : UnframeState :=
  { state with tick := tick }

private def unframeInputTrue : UnframeState → Bool
  | ⟨some true, _⟩ => true
  | _ => false

private def unframeInputPresent : UnframeState → Bool
  | ⟨some _, _⟩ => true
  | _ => false

private def unframeTickPresent : UnframeState → Bool
  | ⟨_, some _⟩ => true
  | _ => false

private def unframeHeldInput : UnframeState → Option Bool
  | ⟨some bit, _⟩ => some bit
  | _ => none

private def UnframeAlphabet : UnframeStack → Type
  | .input => Bool
  | .count => Bool
  | .output => Option Bool

/-- The finite unframing program. It consumes the unary length prefix, puts a
field delimiter on the output, and copies the counted payload. Stack pushes
reverse both the payload bits and the sequence of fields, producing exactly
the raw representation used by later compiler passes. -/
def unframeProgram :
    UnframeLabel → TM2.Stmt UnframeAlphabet UnframeLabel UnframeState
  | .scan =>
      .pop .input unframePoppedInput <|
        .branch unframeInputTrue
          (.push .count (fun _ => true) <|
            .goto (fun _ => .scan))
          (.push .output (fun _ => none) <|
            .goto (fun _ => .payload))
  | .payload =>
      .pop .count unframePoppedTick <|
        .branch unframeTickPresent
          (.pop .input unframePoppedInput <|
            .push .output unframeHeldInput <|
              .goto (fun _ => .payload))
          (.goto (fun _ => .next))
  | .next =>
      .peek .input unframePoppedInput <|
        .branch unframeInputPresent
          (.goto (fun _ => .scan))
          .halt

/-- Concrete finite machine converting canonical framed fields into the raw
stack stream used by subsequent passes. -/
def unframeComputer : FinTM2 where
  K := UnframeStack
  k₀ := .input
  k₁ := .output
  Γ := UnframeAlphabet
  Λ := UnframeLabel
  main := .scan
  σ := UnframeState
  initialState := unframeInitialState
  Γk₀Fin := Bool.fintype
  m := unframeProgram

private def unframeStackContents
    (input count : List Bool) (output : List (Option Bool)) :
    (index : UnframeStack) → List (UnframeAlphabet index)
  | .input => input
  | .count => count
  | .output => output

private def unframeCfg (label : Option UnframeLabel)
    (state : UnframeState) (input count : List Bool)
    (output : List (Option Bool)) : unframeComputer.Cfg where
  l := label
  var := state
  stk := unframeStackContents input count output

private theorem unframe_step_scan_true (input count : List Bool)
    (output : List (Option Bool)) (state : UnframeState) :
    unframeComputer.step
        (unframeCfg (some .scan) state (true :: input) count output) =
      some (unframeCfg (some .scan)
        (unframePoppedInput state (some true)) input
        (true :: count) output) := by
  simp [unframeComputer, FinTM2.step, unframeCfg, unframeProgram,
    unframeStackContents, UnframeAlphabet, unframePoppedInput,
    unframeInputTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem unframe_step_scan_false (input count : List Bool)
    (output : List (Option Bool)) (state : UnframeState) :
    unframeComputer.step
        (unframeCfg (some .scan) state (false :: input) count output) =
      some (unframeCfg (some .payload)
        (unframePoppedInput state (some false)) input count
        (none :: output)) := by
  simp [unframeComputer, FinTM2.step, unframeCfg, unframeProgram,
    unframeStackContents, UnframeAlphabet, unframePoppedInput,
    unframeInputTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem unframe_step_payload_cons (bit tick : Bool)
    (input count : List Bool) (output : List (Option Bool))
    (state : UnframeState) :
    unframeComputer.step
        (unframeCfg (some .payload) state (bit :: input)
          (tick :: count) output) =
      some (unframeCfg (some .payload)
        (unframePoppedInput (unframePoppedTick state (some tick))
          (some bit))
        input count (some bit :: output)) := by
  simp [unframeComputer, FinTM2.step, unframeCfg, unframeProgram,
    unframeStackContents, UnframeAlphabet, unframePoppedInput,
    unframePoppedTick, unframeTickPresent, unframeHeldInput,
    Function.update]
  funext index
  cases index <;> rfl

private theorem unframe_step_payload_nil (input : List Bool)
    (output : List (Option Bool)) (state : UnframeState) :
    unframeComputer.step
        (unframeCfg (some .payload) state input [] output) =
      some (unframeCfg (some .next)
        (unframePoppedTick state none) input [] output) := by
  simp [unframeComputer, FinTM2.step, unframeCfg, unframeProgram,
    unframeStackContents, UnframeAlphabet, unframePoppedTick,
    unframeTickPresent, Function.update]

private theorem unframe_step_next_cons (bit : Bool)
    (input : List Bool) (output : List (Option Bool))
    (state : UnframeState) :
    unframeComputer.step
        (unframeCfg (some .next) state (bit :: input) [] output) =
      some (unframeCfg (some .scan)
        (unframePoppedInput state (some bit))
        (bit :: input) [] output) := by
  simp [unframeComputer, FinTM2.step, unframeCfg, unframeProgram,
    unframeStackContents, UnframeAlphabet, unframePoppedInput,
    unframeInputPresent]

private theorem unframe_step_next_nil (output : List (Option Bool))
    (inputBit : Option Bool) :
    unframeComputer.step
        (unframeCfg (some .next) ⟨inputBit, none⟩ [] [] output) =
      some (unframeCfg none unframeInitialState [] [] output) := by
  simp [unframeComputer, FinTM2.step, unframeCfg, unframeProgram,
    unframeStackContents, UnframeAlphabet, unframePoppedInput,
    unframeInputPresent, unframeInitialState]

private def unframeEvalsToInTimeOne
    {start finish : unframeComputer.Cfg}
    (hstep : unframeComputer.step start = some finish) :
    EvalsToInTime unframeComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def unframe_scan_evals (prefixLength : ℕ) (input count : List Bool)
    (output : List (Option Bool)) (state : UnframeState) :
    EvalsToInTime unframeComputer.step
      (unframeCfg (some .scan) state
        (List.replicate prefixLength true ++ false :: input)
        count output)
      (some (unframeCfg (some .payload)
        (unframePoppedInput state (some false)) input
        (List.replicate prefixLength true ++ count) (none :: output)))
      (prefixLength + 1) := by
  induction prefixLength generalizing count state with
  | zero =>
      simpa using unframeEvalsToInTimeOne
        (unframe_step_scan_false input count output state)
  | succ prefixLength ih =>
      let middle := unframeCfg (some .scan)
        (unframePoppedInput state (some true))
        (List.replicate prefixLength true ++ false :: input)
        (true :: count) output
      have hone : EvalsToInTime unframeComputer.step
          (unframeCfg (some .scan) state
            (List.replicate (prefixLength + 1) true ++ false :: input)
            count output)
          (some middle) 1 :=
        unframeEvalsToInTimeOne (by
          simpa [middle, List.replicate_succ] using
            unframe_step_scan_true
              (List.replicate prefixLength true ++ false :: input)
              count output state)
      have hrest := ih (true :: count)
        (unframePoppedInput state (some true))
      have htrans := EvalsToInTime.trans unframeComputer.step
        1 (prefixLength + 1)
        (unframeCfg (some .scan) state
          (List.replicate (prefixLength + 1) true ++ false :: input)
          count output)
        middle
        (some (unframeCfg (some .payload)
          (unframePoppedInput state (some false)) input
          (List.replicate (prefixLength + 1) true ++ count)
          (none :: output)))
        hone
        (by
          simpa [middle, unframePoppedInput, List.replicate_succ,
            replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

/-- State after copying a payload. Only the last copied bit is retained, and
the exhausted unary counter is recorded as absent. -/
private def unframePayloadState (inputBit : Option Bool) :
    List Bool → UnframeState
  | [] => ⟨inputBit, none⟩
  | bit :: bits => unframePayloadState (some bit) bits

@[simp]
private theorem unframePayloadState_tick
    (inputBit : Option Bool) (bits : List Bool) :
    (unframePayloadState inputBit bits).tick = none := by
  induction bits generalizing inputBit with
  | nil => rfl
  | cons bit bits ih => exact ih (some bit)

private def unframe_payload_evals (bits input : List Bool)
    (output : List (Option Bool)) (state : UnframeState) :
    EvalsToInTime unframeComputer.step
      (unframeCfg (some .payload) state (bits ++ input)
        (List.replicate bits.length true) output)
      (some (unframeCfg (some .next)
        (unframePayloadState state.inputBit bits) input []
        (bits.reverse.map some ++ output)))
      (bits.length + 1) := by
  induction bits generalizing output state with
  | nil =>
      cases state with
      | mk inputBit tick =>
          simpa [unframePayloadState, unframePoppedTick] using
            unframeEvalsToInTimeOne
              (unframe_step_payload_nil input output ⟨inputBit, tick⟩)
  | cons bit bits ih =>
      let middle := unframeCfg (some .payload)
        (unframePoppedInput (unframePoppedTick state (some true))
          (some bit))
        (bits ++ input) (List.replicate bits.length true)
        (some bit :: output)
      have hone : EvalsToInTime unframeComputer.step
          (unframeCfg (some .payload) state
            ((bit :: bits) ++ input)
            (List.replicate (bit :: bits).length true) output)
          (some middle) 1 :=
        unframeEvalsToInTimeOne (by
          simpa [middle, List.replicate_succ] using
            unframe_step_payload_cons bit true
              (bits ++ input) (List.replicate bits.length true)
              output state)
      have hrest := ih (some bit :: output)
        (unframePoppedInput (unframePoppedTick state (some true))
          (some bit))
      have htrans := EvalsToInTime.trans unframeComputer.step
        1 (bits.length + 1)
        (unframeCfg (some .payload) state
          ((bit :: bits) ++ input)
          (List.replicate (bit :: bits).length true) output)
        middle
        (some (unframeCfg (some .next)
          (unframePayloadState state.inputBit (bit :: bits))
          input [] ((bit :: bits).reverse.map some ++ output)))
        hone
        (by
          simpa [middle, unframePayloadState, unframePoppedInput,
            unframePoppedTick, List.reverse_cons, List.map_append,
            List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def unframe_next_present_evals (input : List Bool)
    (hinput : input ≠ []) (output : List (Option Bool))
    (state : UnframeState) :
    EvalsToInTime unframeComputer.step
      (unframeCfg (some .next) state input [] output)
      (some (unframeCfg (some .scan)
        (unframePoppedInput state input.head?) input [] output)) 1 := by
  cases input with
  | nil => exact (hinput rfl).elim
  | cons bit input =>
      simpa using unframeEvalsToInTimeOne
        (unframe_step_next_cons bit input output state)

private def unframe_next_nil_evals (output : List (Option Bool))
    (state : UnframeState) (htick : state.tick = none) :
    EvalsToInTime unframeComputer.step
      (unframeCfg (some .next) state [] [] output)
      (some (unframeCfg none unframeInitialState [] [] output)) 1 := by
  cases state with
  | mk inputBit tick =>
      change tick = none at htick
      subst tick
      exact unframeEvalsToInTimeOne
        (unframe_step_next_nil output inputBit)

private theorem frames_flatMap_nonempty (bits : List Bool)
    (fields : List (List Bool)) :
    ((bits :: fields).flatMap BinaryNatLists.frame) ≠ [] := by
  simp [BinaryNatLists.frame]

private def unframe_fields_evals
    (fields : List (List Bool)) (hfields : fields ≠ [])
    (output : List (Option Bool)) (state : UnframeState) :
    EvalsToInTime unframeComputer.step
      (unframeCfg (some .scan) state
        (fields.flatMap BinaryNatLists.frame) [] output)
      (some (unframeCfg none unframeInitialState [] []
        (fields.reverse.flatMap RawNatList.segment ++ output)))
      ((fields.flatMap BinaryNatLists.frame).length + 2 * fields.length) := by
  induction fields generalizing output state with
  | nil => exact (hfields rfl).elim
  | cons bits fields ih =>
      let tailInput := fields.flatMap BinaryNatLists.frame
      have hscan := unframe_scan_evals bits.length
        (bits ++ tailInput) [] output state
      have hpayload := unframe_payload_evals bits tailInput
        (none :: output) (unframePoppedInput state (some false))
      have hfirst := EvalsToInTime.trans unframeComputer.step
        (bits.length + 1) (bits.length + 1)
        (unframeCfg (some .scan) state
          ((bits :: fields).flatMap BinaryNatLists.frame) [] output)
        (unframeCfg (some .payload)
          (unframePoppedInput state (some false))
          (bits ++ tailInput) (List.replicate bits.length true)
          (none :: output))
        (some (unframeCfg (some .next)
          (unframePayloadState
            (unframePoppedInput state (some false)).inputBit bits)
          tailInput [] (RawNatList.segment bits ++ output)))
        (by
          simpa [tailInput, BinaryNatLists.frame, List.append_assoc] using hscan)
        (by
          simpa [RawNatList.segment, List.append_assoc] using hpayload)
      cases fields with
      | nil =>
          have hnext := unframe_next_nil_evals
            (RawNatList.segment bits ++ output)
            (unframePayloadState
              (unframePoppedInput state (some false)).inputBit bits)
            (unframePayloadState_tick _ _)
          have hall := EvalsToInTime.trans unframeComputer.step
            ((bits.length + 1) + (bits.length + 1)) 1
            (unframeCfg (some .scan) state
              ([bits].flatMap BinaryNatLists.frame) [] output)
            (unframeCfg (some .next)
              (unframePayloadState
                (unframePoppedInput state (some false)).inputBit bits)
              [] [] (RawNatList.segment bits ++ output))
            (some (unframeCfg none unframeInitialState [] []
              (RawNatList.segment bits ++ output)))
            (by simpa [tailInput] using hfirst)
            hnext
          have htime :
              1 + ((bits.length + 1) + (bits.length + 1)) =
                ([bits].flatMap BinaryNatLists.frame).length +
                  2 * [bits].length := by
            simp [BinaryNatLists.frame]
            omega
          rw [htime] at hall
          simpa [RawNatList.segment] using hall
      | cons next fields =>
          let rest := next :: fields
          have htail :
              (rest.flatMap BinaryNatLists.frame) ≠ [] :=
            frames_flatMap_nonempty next fields
          have hnext := unframe_next_present_evals
            (rest.flatMap BinaryNatLists.frame) htail
            (RawNatList.segment bits ++ output)
            (unframePayloadState
              (unframePoppedInput state (some false)).inputBit bits)
          have hthroughNext := EvalsToInTime.trans unframeComputer.step
            ((bits.length + 1) + (bits.length + 1)) 1
            (unframeCfg (some .scan) state
              ((bits :: rest).flatMap BinaryNatLists.frame) [] output)
            (unframeCfg (some .next)
              (unframePayloadState
                (unframePoppedInput state (some false)).inputBit bits)
              (rest.flatMap BinaryNatLists.frame) []
              (RawNatList.segment bits ++ output))
            (some (unframeCfg (some .scan)
              (unframePoppedInput
                (unframePayloadState
                  (unframePoppedInput state (some false)).inputBit bits)
                (rest.flatMap BinaryNatLists.frame).head?)
              (rest.flatMap BinaryNatLists.frame) []
              (RawNatList.segment bits ++ output)))
            (by simpa [tailInput, rest] using hfirst)
            hnext
          have hrest := ih (by simp)
            (RawNatList.segment bits ++ output)
            (unframePoppedInput
              (unframePayloadState
                (unframePoppedInput state (some false)).inputBit bits)
              (rest.flatMap BinaryNatLists.frame).head?)
          have hall := EvalsToInTime.trans unframeComputer.step
            (1 + ((bits.length + 1) + (bits.length + 1)))
            ((rest.flatMap BinaryNatLists.frame).length +
              2 * rest.length)
            (unframeCfg (some .scan) state
              ((bits :: rest).flatMap BinaryNatLists.frame) [] output)
            (unframeCfg (some .scan)
              (unframePoppedInput
                (unframePayloadState
                  (unframePoppedInput state (some false)).inputBit bits)
                (rest.flatMap BinaryNatLists.frame).head?)
              (rest.flatMap BinaryNatLists.frame) []
              (RawNatList.segment bits ++ output))
            (some (unframeCfg none unframeInitialState [] []
              ((bits :: rest).reverse.flatMap RawNatList.segment ++ output)))
            hthroughNext
            (by
              simpa [rest, List.reverse_cons, List.append_assoc] using hrest)
          have htime :
              ((rest.flatMap BinaryNatLists.frame).length +
                  2 * rest.length) +
                  (1 + ((bits.length + 1) + (bits.length + 1))) =
                ((bits :: rest).flatMap BinaryNatLists.frame).length +
                  2 * (bits :: rest).length := by
            simp [BinaryNatLists.frame]
            omega
          rw [htime] at hall
          simpa [rest, List.append_assoc] using hall

private theorem fields_length_le_frames_length
    (fields : List (List Bool)) :
    fields.length ≤ (fields.flatMap BinaryNatLists.frame).length := by
  induction fields with
  | nil => simp
  | cons bits fields ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have hpositive : 0 < (BinaryNatLists.frame bits).length := by
        simp [BinaryNatLists.frame]
      omega

private theorem unframe_initList_eq_cfg (input : List Bool) :
    initList unframeComputer input =
      unframeCfg (some .scan) unframeInitialState input [] [] := by
  unfold initList unframeCfg
  congr
  funext index
  cases index <;> rfl

private theorem unframe_haltList_eq_cfg (output : List (Option Bool)) :
    haltList unframeComputer output =
      unframeCfg none unframeInitialState [] [] output := by
  unfold haltList unframeCfg
  congr
  funext index
  cases index <;> rfl

/-- The unframing traversal consumes the standard nested-list encoding and
emits its explicit stack-oriented raw fields in at most three times the input
length. -/
def unframe_outputsInTime (xss : List (List ℕ)) :
    TM2OutputsInTime unframeComputer (BinaryNatLists.encode xss)
      (some (RawNatLists.encode xss))
      (3 * (BinaryNatLists.encode xss).length) := by
  have hpayloads : RawNatLists.payloads xss ≠ [] := by
    simp [RawNatLists.payloads]
  have hfields := unframe_fields_evals
    (RawNatLists.payloads xss) hpayloads [] unframeInitialState
  have hlength :=
    fields_length_le_frames_length (RawNatLists.payloads xss)
  have hbound :
      ((RawNatLists.payloads xss).flatMap BinaryNatLists.frame).length +
          2 * (RawNatLists.payloads xss).length ≤
        3 * ((RawNatLists.payloads xss).flatMap
          BinaryNatLists.frame).length := by
    omega
  have hmono := evalsToInTimeMono hfields hbound
  have hinput :
      BinaryNatLists.encode xss =
        (RawNatLists.payloads xss).flatMap BinaryNatLists.frame :=
    (RawNatLists.payloads_frame_eq_encode xss).symm
  rw [TM2OutputsInTime, hinput, unframe_initList_eq_cfg]
  simp only [Option.map_some]
  rw [unframe_haltList_eq_cfg]
  simpa [RawNatLists.encode] using hmono

/-- A genuine linear-time finite-machine witness exposing every field of the
standard nested-list input as an explicitly delimited raw binary stack stream.
The mathematical function is the identity; the change of encoding supplies
the traversal interface used by later arithmetic and compiler passes. -/
noncomputable def unframedNatListsComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ)) (List (List ℕ))
      BinaryNatLists.finEncoding RawNatLists.finEncoding id where
  tm := unframeComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Option Bool)
  time := 3 * Polynomial.X
  outputsFun xss := by
    simpa [BinaryNatLists.finEncoding, RawNatLists.finEncoding, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_X] using
        unframe_outputsInTime xss

/-! ## Binary successor

The prime scan and several structural compiler passes need arithmetic on the
raw binary fields exposed above. The following machine supplies the first such
primitive: successor on mathlib's least-significant-bit-first natural-number
encoding. It propagates carry on the input stack, copies the untouched suffix,
and reverses one work stack into the canonical output order.
-/

/-- Increment a least-significant-bit-first binary word. On canonical
`encodeNat` words this is exactly natural-number successor. -/
def binarySuccBits : List Bool → List Bool
  | [] => [true]
  | false :: bits => true :: bits
  | true :: bits => false :: binarySuccBits bits

private theorem binarySuccBits_encodePosNum (n : PosNum) :
    binarySuccBits (encodePosNum n) = encodePosNum n.succ := by
  induction n with
  | one => rfl
  | bit0 n ih => rfl
  | bit1 n ih =>
      simp only [encodePosNum, binarySuccBits, PosNum.succ]
      rw [ih]

private theorem binarySuccBits_encodeNum (n : Num) :
    binarySuccBits (encodeNum n) = encodeNum n.succ := by
  cases n with
  | zero => rfl
  | pos n =>
      simp only [encodeNum, Num.succ, Num.succ']
      exact binarySuccBits_encodePosNum n

/-- The bit-level transformation agrees with successor on mathlib's canonical
binary natural encoding, including the empty encoding of zero. -/
@[simp]
theorem binarySuccBits_encodeNat (n : ℕ) :
    binarySuccBits (encodeNat n) = encodeNat (n + 1) := by
  unfold encodeNat
  rw [binarySuccBits_encodeNum]
  change encodeNum (Num.ofNat' n).succ = encodeNum (Num.ofNat' (n + 1))
  rw [Num.ofNat'_succ, Num.add_one]

private theorem binarySuccBits_length_le (bits : List Bool) :
    (binarySuccBits bits).length ≤ bits.length + 1 := by
  induction bits with
  | nil => simp [binarySuccBits]
  | cons bit bits ih =>
      cases bit <;> simp [binarySuccBits, ih]

/-- Input, reversal work, and canonical output stacks for binary successor. -/
inductive SuccStack
  | input
  | work
  | output
  deriving DecidableEq, Fintype

/-- Carry propagation, untouched-suffix copy, and output reversal phases. -/
inductive SuccLabel
  | carry
  | copy
  | reverse
  deriving DecidableEq, Fintype

/-- Finite control remembers the most recently popped bit. -/
structure SuccState where
  bit : Option Bool
  deriving DecidableEq, Fintype

private def succInitialState : SuccState :=
  ⟨none⟩

private def succPoppedBit (_state : SuccState) (bit : Option Bool) : SuccState :=
  ⟨bit⟩

private def succBitPresent : SuccState → Bool
  | ⟨some _⟩ => true
  | _ => false

private def succBitTrue : SuccState → Bool
  | ⟨some true⟩ => true
  | _ => false

private def succHeldBit : SuccState → Bool
  | ⟨some bit⟩ => bit
  | _ => false

private def SuccAlphabet (_index : SuccStack) : Type := Bool

/-- A finite three-stack successor program for least-significant-bit-first
binary words. -/
def binarySuccProgram :
    SuccLabel → TM2.Stmt SuccAlphabet SuccLabel SuccState
  | .carry =>
      .pop .input succPoppedBit <|
        .branch succBitPresent
          (.branch succBitTrue
            (.push .work (fun _ => false) <|
              .goto (fun _ => .carry))
            (.push .work (fun _ => true) <|
              .goto (fun _ => .copy)))
          (.push .work (fun _ => true) <|
            .goto (fun _ => .reverse))
  | .copy =>
      .pop .input succPoppedBit <|
        .branch succBitPresent
          (.push .work succHeldBit <|
            .goto (fun _ => .copy))
          (.goto (fun _ => .reverse))
  | .reverse =>
      .pop .work succPoppedBit <|
        .branch succBitPresent
          (.push .output succHeldBit <|
            .goto (fun _ => .reverse))
          .halt

/-- Concrete finite machine computing binary successor. -/
def binarySuccComputer : FinTM2 where
  K := SuccStack
  k₀ := .input
  k₁ := .output
  Γ := SuccAlphabet
  Λ := SuccLabel
  main := .carry
  σ := SuccState
  initialState := succInitialState
  Γk₀Fin := Bool.fintype
  m := binarySuccProgram

private def succStackContents
    (input work output : List Bool) :
    (index : SuccStack) → List (SuccAlphabet index)
  | .input => input
  | .work => work
  | .output => output

private def succCfg (label : Option SuccLabel) (state : SuccState)
    (input work output : List Bool) : binarySuccComputer.Cfg where
  l := label
  var := state
  stk := succStackContents input work output

private theorem succ_step_carry_nil (work output : List Bool)
    (state : SuccState) :
    binarySuccComputer.step
        (succCfg (some .carry) state [] work output) =
      some (succCfg (some .reverse) succInitialState []
        (true :: work) output) := by
  simp [binarySuccComputer, FinTM2.step, succCfg, binarySuccProgram,
    succStackContents, SuccAlphabet, succPoppedBit, succBitPresent,
    succInitialState, Function.update]
  funext index
  cases index <;> rfl

private theorem succ_step_carry_false (bits work output : List Bool)
    (state : SuccState) :
    binarySuccComputer.step
        (succCfg (some .carry) state (false :: bits) work output) =
      some (succCfg (some .copy) ⟨some false⟩ bits
        (true :: work) output) := by
  simp [binarySuccComputer, FinTM2.step, succCfg, binarySuccProgram,
    succStackContents, SuccAlphabet, succPoppedBit, succBitPresent,
    succBitTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem succ_step_carry_true (bits work output : List Bool)
    (state : SuccState) :
    binarySuccComputer.step
        (succCfg (some .carry) state (true :: bits) work output) =
      some (succCfg (some .carry) ⟨some true⟩ bits
        (false :: work) output) := by
  simp [binarySuccComputer, FinTM2.step, succCfg, binarySuccProgram,
    succStackContents, SuccAlphabet, succPoppedBit, succBitPresent,
    succBitTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem succ_step_copy_nil (work output : List Bool)
    (state : SuccState) :
    binarySuccComputer.step
        (succCfg (some .copy) state [] work output) =
      some (succCfg (some .reverse) succInitialState [] work output) := by
  simp [binarySuccComputer, FinTM2.step, succCfg, binarySuccProgram,
    succStackContents, SuccAlphabet, succPoppedBit, succBitPresent,
    succInitialState, Function.update]

private theorem succ_step_copy_cons (bit : Bool) (bits work output : List Bool)
    (state : SuccState) :
    binarySuccComputer.step
        (succCfg (some .copy) state (bit :: bits) work output) =
      some (succCfg (some .copy) ⟨some bit⟩ bits
        (bit :: work) output) := by
  cases bit <;>
    simp [binarySuccComputer, FinTM2.step, succCfg, binarySuccProgram,
      succStackContents, SuccAlphabet, succPoppedBit, succBitPresent,
      succHeldBit, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem succ_step_reverse_nil (output : List Bool)
    (state : SuccState) :
    binarySuccComputer.step
        (succCfg (some .reverse) state [] [] output) =
      some (succCfg none succInitialState [] [] output) := by
  simp [binarySuccComputer, FinTM2.step, succCfg, binarySuccProgram,
    succStackContents, SuccAlphabet, succPoppedBit, succBitPresent,
    succInitialState, Function.update]

private theorem succ_step_reverse_cons (bit : Bool)
    (work output : List Bool) (state : SuccState) :
    binarySuccComputer.step
        (succCfg (some .reverse) state [] (bit :: work) output) =
      some (succCfg (some .reverse) ⟨some bit⟩ [] work
        (bit :: output)) := by
  cases bit <;>
    simp [binarySuccComputer, FinTM2.step, succCfg, binarySuccProgram,
      succStackContents, SuccAlphabet, succPoppedBit, succBitPresent,
      succHeldBit, Function.update] <;>
    (funext index; cases index <;> rfl)

private def succEvalsToInTimeOne
    {start finish : binarySuccComputer.Cfg}
    (hstep : binarySuccComputer.step start = some finish) :
    EvalsToInTime binarySuccComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def succ_copy_evals (bits work output : List Bool)
    (state : SuccState) :
    EvalsToInTime binarySuccComputer.step
      (succCfg (some .copy) state bits work output)
      (some (succCfg (some .reverse) succInitialState []
        (bits.reverse ++ work) output))
      (bits.length + 1) := by
  induction bits generalizing work state with
  | nil =>
      simpa using succEvalsToInTimeOne
        (succ_step_copy_nil work output state)
  | cons bit bits ih =>
      let middle := succCfg (some .copy) ⟨some bit⟩ bits
        (bit :: work) output
      have hone : EvalsToInTime binarySuccComputer.step
          (succCfg (some .copy) state (bit :: bits) work output)
          (some middle) 1 :=
        succEvalsToInTimeOne (by
          simpa [middle] using succ_step_copy_cons bit bits work output state)
      have hrest := ih (bit :: work) ⟨some bit⟩
      have htrans := EvalsToInTime.trans binarySuccComputer.step
        1 (bits.length + 1)
        (succCfg (some .copy) state (bit :: bits) work output)
        middle
        (some (succCfg (some .reverse) succInitialState []
          ((bit :: bits).reverse ++ work) output))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def succ_carry_evals (bits work output : List Bool)
    (state : SuccState) :
    EvalsToInTime binarySuccComputer.step
      (succCfg (some .carry) state bits work output)
      (some (succCfg (some .reverse) succInitialState []
        ((binarySuccBits bits).reverse ++ work) output))
      (bits.length + 1) := by
  induction bits generalizing work state with
  | nil =>
      simpa [binarySuccBits] using succEvalsToInTimeOne
        (succ_step_carry_nil work output state)
  | cons bit bits ih =>
      cases bit with
      | false =>
          let middle := succCfg (some .copy) ⟨some false⟩ bits
            (true :: work) output
          have hone : EvalsToInTime binarySuccComputer.step
              (succCfg (some .carry) state (false :: bits) work output)
              (some middle) 1 :=
            succEvalsToInTimeOne (by
              simpa [middle] using succ_step_carry_false bits work output state)
          have hcopy := succ_copy_evals bits (true :: work) output ⟨some false⟩
          have htrans := EvalsToInTime.trans binarySuccComputer.step
            1 (bits.length + 1)
            (succCfg (some .carry) state (false :: bits) work output)
            middle
            (some (succCfg (some .reverse) succInitialState []
              ((binarySuccBits (false :: bits)).reverse ++ work) output))
            hone
            (by
              simpa [middle, binarySuccBits, List.reverse_cons,
                List.append_assoc] using hcopy)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans
      | true =>
          let middle := succCfg (some .carry) ⟨some true⟩ bits
            (false :: work) output
          have hone : EvalsToInTime binarySuccComputer.step
              (succCfg (some .carry) state (true :: bits) work output)
              (some middle) 1 :=
            succEvalsToInTimeOne (by
              simpa [middle] using succ_step_carry_true bits work output state)
          have hrest := ih (false :: work) ⟨some true⟩
          have htrans := EvalsToInTime.trans binarySuccComputer.step
            1 (bits.length + 1)
            (succCfg (some .carry) state (true :: bits) work output)
            middle
            (some (succCfg (some .reverse) succInitialState []
              ((binarySuccBits (true :: bits)).reverse ++ work) output))
            hone
            (by
              simpa [middle, binarySuccBits, List.reverse_cons,
                List.append_assoc] using hrest)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def succ_reverse_evals (work output : List Bool)
    (state : SuccState) :
    EvalsToInTime binarySuccComputer.step
      (succCfg (some .reverse) state [] work output)
      (some (succCfg none succInitialState [] []
        (work.reverse ++ output)))
      (work.length + 1) := by
  induction work generalizing output state with
  | nil =>
      simpa using succEvalsToInTimeOne
        (succ_step_reverse_nil output state)
  | cons bit work ih =>
      let middle := succCfg (some .reverse) ⟨some bit⟩ [] work
        (bit :: output)
      have hone : EvalsToInTime binarySuccComputer.step
          (succCfg (some .reverse) state [] (bit :: work) output)
          (some middle) 1 :=
        succEvalsToInTimeOne (by
          simpa [middle] using succ_step_reverse_cons bit work output state)
      have hrest := ih (bit :: output) ⟨some bit⟩
      have htrans := EvalsToInTime.trans binarySuccComputer.step
        1 (work.length + 1)
        (succCfg (some .reverse) state [] (bit :: work) output)
        middle
        (some (succCfg none succInitialState [] []
          ((bit :: work).reverse ++ output)))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private theorem succ_initList_eq_cfg (input : List Bool) :
    initList binarySuccComputer input =
      succCfg (some .carry) succInitialState input [] [] := by
  unfold initList succCfg
  congr
  funext index
  cases index <;> rfl

private theorem succ_haltList_eq_cfg (output : List Bool) :
    haltList binarySuccComputer output =
      succCfg none succInitialState [] [] output := by
  unfold haltList succCfg
  congr
  funext index
  cases index <;> rfl

/-- Binary successor runs in at most `2s + 3` steps on an arbitrary bit word
of length `s` and emits `binarySuccBits` of that word. -/
def binarySucc_outputsInTime (bits : List Bool) :
    TM2OutputsInTime binarySuccComputer bits
      (some (binarySuccBits bits)) (2 * bits.length + 3) := by
  have hcarry := succ_carry_evals bits [] [] succInitialState
  have hreverse := succ_reverse_evals
    (binarySuccBits bits).reverse [] succInitialState
  have hall := EvalsToInTime.trans binarySuccComputer.step
    (bits.length + 1) ((binarySuccBits bits).reverse.length + 1)
    (succCfg (some .carry) succInitialState bits [] [])
    (succCfg (some .reverse) succInitialState []
      (binarySuccBits bits).reverse [])
    (some (succCfg none succInitialState [] [] (binarySuccBits bits)))
    (by simpa using hcarry)
    (by simpa using hreverse)
  have hbound := binarySuccBits_length_le bits
  have hmono : EvalsToInTime binarySuccComputer.step
      (succCfg (some .carry) succInitialState bits [] [])
      (some (succCfg none succInitialState [] [] (binarySuccBits bits)))
      (2 * bits.length + 3) :=
    evalsToInTimeMono hall (by
      simp only [List.length_reverse]
      omega)
  rw [TM2OutputsInTime, succ_initList_eq_cfg]
  simp only [Option.map_some]
  rw [succ_haltList_eq_cfg]
  exact hmono

/-- A genuine linear-time finite-machine witness for successor on mathlib's
standard binary natural-number encoding. -/
noncomputable def binarySuccComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ ℕ finEncodingNatBool finEncodingNatBool
      (fun n => n + 1) where
  tm := binarySuccComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun n := by
    simpa [finEncodingNatBool, Equiv.refl, binarySuccBits_encodeNat,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_X] using binarySucc_outputsInTime (encodeNat n)

/-! ## Binary comparison

Bounded enumeration and the eventual prime scan need a checked comparison
primitive. Two canonical least-significant-bit-first words are aligned into a
finite paired alphabet. Missing bits are represented by `none`; this preserves
both words exactly while letting one finite-control pass visit corresponding
bit positions from least to most significant.
-/

namespace BinaryNatPair

/-- Align two bit strings, padding only the exhausted side with `none`. -/
def zipBits : List Bool → List Bool → List (Option Bool × Option Bool)
  | [], [] => []
  | left :: lefts, [] => (some left, none) :: zipBits lefts []
  | [], right :: rights => (none, some right) :: zipBits [] rights
  | left :: lefts, right :: rights =>
      (some left, some right) :: zipBits lefts rights

/-- Recover the left bit string from an aligned pair stream. -/
def leftBits : List (Option Bool × Option Bool) → List Bool
  | [] => []
  | (none, _) :: pairs => leftBits pairs
  | (some bit, _) :: pairs => bit :: leftBits pairs

/-- Recover the right bit string from an aligned pair stream. -/
def rightBits : List (Option Bool × Option Bool) → List Bool
  | [] => []
  | (_, none) :: pairs => rightBits pairs
  | (_, some bit) :: pairs => bit :: rightBits pairs

@[simp]
theorem leftBits_zipBits (left right : List Bool) :
    leftBits (zipBits left right) = left := by
  induction left generalizing right with
  | nil =>
      induction right with
      | nil => simp [zipBits, leftBits]
      | cons right rights ih =>
          simp [zipBits, leftBits, ih]
  | cons left lefts ih =>
      cases right with
      | nil => simp [zipBits, leftBits, ih]
      | cons right rights => simp [zipBits, leftBits, ih]

@[simp]
theorem rightBits_zipBits (left right : List Bool) :
    rightBits (zipBits left right) = right := by
  induction left generalizing right with
  | nil =>
      induction right with
      | nil => simp [zipBits, rightBits]
      | cons right rights ih =>
          simp [zipBits, rightBits, ih]
  | cons left lefts ih =>
      cases right with
      | nil => simp [zipBits, rightBits, ih]
      | cons right rights => simp [zipBits, rightBits, ih]

/-- Canonical paired binary encoding of two naturals. -/
def encode (pair : ℕ × ℕ) : List (Option Bool × Option Bool) :=
  zipBits (encodeNat pair.1) (encodeNat pair.2)

/-- Decode both projections of an aligned bit stream. -/
def decode (pairs : List (Option Bool × Option Bool)) : Option (ℕ × ℕ) :=
  some (decodeNat (leftBits pairs), decodeNat (rightBits pairs))

@[simp]
theorem decode_encode (pair : ℕ × ℕ) : decode (encode pair) = some pair := by
  rcases pair with ⟨left, right⟩
  simp [decode, encode]

/-- Checked finite encoding of a pair of canonical binary naturals. -/
def finEncoding : FinEncoding (ℕ × ℕ) where
  Γ := Option Bool × Option Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

end BinaryNatPair

/-- Update a less-than-or-equal decision with one more significant aligned
bit pair. A missing high bit makes that side shorter; unequal present bits
replace the decision made by all less significant positions. -/
def binaryLEUpdate (current : Bool) : Option Bool → Option Bool → Bool
  | none, none => current
  | none, some _ => true
  | some _, none => false
  | some false, some true => true
  | some true, some false => false
  | some false, some false => current
  | some true, some true => current

/-- Comparison directly on two least-significant-bit-first words. -/
def binaryLEBitsAux : Bool → List Bool → List Bool → Bool
  | current, [], [] => current
  | current, left :: lefts, [] =>
      binaryLEBitsAux (binaryLEUpdate current (some left) none) lefts []
  | current, [], right :: rights =>
      binaryLEBitsAux (binaryLEUpdate current none (some right)) [] rights
  | current, left :: lefts, right :: rights =>
      binaryLEBitsAux
        (binaryLEUpdate current (some left) (some right)) lefts rights

/-- Fold the same comparison update over the paired wire representation. -/
def binaryLEPairsAux : Bool → List (Option Bool × Option Bool) → Bool
  | current, [] => current
  | current, pair :: pairs =>
      binaryLEPairsAux (binaryLEUpdate current pair.1 pair.2) pairs

@[simp]
theorem binaryLEPairsAux_zipBits
    (current : Bool) (left right : List Bool) :
    binaryLEPairsAux current (BinaryNatPair.zipBits left right) =
      binaryLEBitsAux current left right := by
  induction left generalizing current right with
  | nil =>
      induction right generalizing current with
      | nil => simp [BinaryNatPair.zipBits, binaryLEPairsAux,
          binaryLEBitsAux]
      | cons right rights ih =>
          simp [BinaryNatPair.zipBits, binaryLEPairsAux,
            binaryLEBitsAux, ih]
  | cons left lefts ih =>
      cases right with
      | nil =>
          simp [BinaryNatPair.zipBits, binaryLEPairsAux,
            binaryLEBitsAux, ih]
      | cons right rights =>
          simp [BinaryNatPair.zipBits, binaryLEPairsAux,
            binaryLEBitsAux, ih]

/-- Translate a three-way comparison into a decision, retaining `current`
only when all inspected higher bits are equal. -/
def orderingLEResult (current : Bool) : Ordering → Bool
  | .lt => true
  | .eq => current
  | .gt => false

private theorem binaryLEBitsAux_true_left_nil (bits : List Bool) :
    binaryLEBitsAux true [] bits = true := by
  induction bits with
  | nil => simp [binaryLEBitsAux]
  | cons bit bits ih =>
      cases bit <;> simpa [binaryLEBitsAux, binaryLEUpdate] using ih

private theorem binaryLEBitsAux_false_right_nil (bits : List Bool) :
    binaryLEBitsAux false bits [] = false := by
  induction bits with
  | nil => simp [binaryLEBitsAux]
  | cons bit bits ih =>
      cases bit <;> simpa [binaryLEBitsAux, binaryLEUpdate] using ih

private theorem binaryLEBitsAux_left_nonempty
    (current bit : Bool) (bits : List Bool) :
    binaryLEBitsAux current [] (bit :: bits) = true := by
  cases bit <;>
    simpa [binaryLEBitsAux, binaryLEUpdate] using
      binaryLEBitsAux_true_left_nil bits

private theorem binaryLEBitsAux_right_nonempty
    (current bit : Bool) (bits : List Bool) :
    binaryLEBitsAux current (bit :: bits) [] = false := by
  cases bit <;>
    simpa [binaryLEBitsAux, binaryLEUpdate] using
      binaryLEBitsAux_false_right_nil bits

private theorem binaryLEBitsAux_left_of_nonempty
    (current : Bool) {bits : List Bool} (hbits : bits ≠ []) :
    binaryLEBitsAux current [] bits = true := by
  cases bits with
  | nil => exact (hbits rfl).elim
  | cons bit bits => exact binaryLEBitsAux_left_nonempty current bit bits

private theorem binaryLEBitsAux_right_of_nonempty
    (current : Bool) {bits : List Bool} (hbits : bits ≠ []) :
    binaryLEBitsAux current bits [] = false := by
  cases bits with
  | nil => exact (hbits rfl).elim
  | cons bit bits => exact binaryLEBitsAux_right_nonempty current bit bits

private theorem binaryLEBitsAux_encodePosNum
    (current : Bool) (left right : PosNum) :
    binaryLEBitsAux current (encodePosNum left) (encodePosNum right) =
      orderingLEResult current (PosNum.cmp left right) := by
  induction left generalizing current right with
  | one =>
      cases right with
      | one => simp [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
          orderingLEResult, PosNum.cmp]
      | bit1 right =>
          simp only [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
            orderingLEResult, PosNum.cmp]
          exact binaryLEBitsAux_left_of_nonempty current
            (encodePosNum_nonempty right)
      | bit0 right =>
          simp only [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
            orderingLEResult, PosNum.cmp]
          exact binaryLEBitsAux_left_of_nonempty false
            (encodePosNum_nonempty right)
  | bit1 left ih =>
      cases right with
      | one =>
          simp only [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
            orderingLEResult, PosNum.cmp]
          exact binaryLEBitsAux_right_of_nonempty current
            (encodePosNum_nonempty left)
      | bit1 right =>
          simpa [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
            PosNum.cmp] using ih current right
      | bit0 right =>
          have h := ih (binaryLEUpdate current (some true) (some false)) right
          cases hcmp : PosNum.cmp left right <;>
            simp [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
              PosNum.cmp, hcmp, orderingLEResult] at h ⊢ <;>
            exact h
  | bit0 left ih =>
      cases right with
      | one =>
          simp only [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
            orderingLEResult, PosNum.cmp]
          exact binaryLEBitsAux_right_of_nonempty true
            (encodePosNum_nonempty left)
      | bit1 right =>
          have h := ih (binaryLEUpdate current (some false) (some true)) right
          cases hcmp : PosNum.cmp left right <;>
            simp [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
              PosNum.cmp, hcmp, orderingLEResult] at h ⊢ <;>
            exact h
      | bit0 right =>
          simpa [encodePosNum, binaryLEBitsAux, binaryLEUpdate,
            PosNum.cmp] using ih current right

private theorem orderingLEResult_cmp_true (left right : PosNum) :
    orderingLEResult true (PosNum.cmp left right) =
      decide ((left : ℕ) ≤ (right : ℕ)) := by
  have hcmpNat := PosNum.cmp_to_nat left right
  cases hcmp : PosNum.cmp left right with
  | lt =>
      simp [hcmp] at hcmpNat
      have hlePos : left ≤ right := hcmpNat.le
      have hle : (left : ℕ) ≤ (right : ℕ) :=
        PosNum.le_to_nat.mpr hlePos
      simp [orderingLEResult, hle]
  | eq =>
      simp [hcmp] at hcmpNat
      subst right
      simp [orderingLEResult]
  | gt =>
      simp [hcmp] at hcmpNat
      have hlt : (right : ℕ) < (left : ℕ) :=
        PosNum.lt_to_nat.mpr hcmpNat
      have hnle : ¬(left : ℕ) ≤ (right : ℕ) := Nat.not_le_of_gt hlt
      simp [orderingLEResult, hnle]

/-- Bit comparison agrees with natural-number comparison on canonical binary
encodings, including zero on either side. -/
@[simp]
theorem binaryLEBitsAux_encodeNat (left right : ℕ) :
    binaryLEBitsAux true (encodeNat left) (encodeNat right) =
      decide (left ≤ right) := by
  unfold encodeNat
  cases hleft : (left : Num) with
  | zero =>
      cases hright : (right : Num) with
      | zero =>
          have hleftNat := congrArg (fun n : Num => (n : ℕ)) hleft
          have hrightNat := congrArg (fun n : Num => (n : ℕ)) hright
          simp at hleftNat hrightNat
          simp [hleftNat, hrightNat, encodeNum, binaryLEBitsAux]
      | pos rightPos =>
          have hleftNat := congrArg (fun n : Num => (n : ℕ)) hleft
          have hrightNat := congrArg (fun n : Num => (n : ℕ)) hright
          simp at hleftNat hrightNat
          have hcompare :
              binaryLEBitsAux true [] (encodePosNum rightPos) = true :=
            binaryLEBitsAux_left_of_nonempty true
              (encodePosNum_nonempty rightPos)
          simp [hleftNat, hrightNat, encodeNum, hcompare]
  | pos leftPos =>
      cases hright : (right : Num) with
      | zero =>
          have hleftNat := congrArg (fun n : Num => (n : ℕ)) hleft
          have hrightNat := congrArg (fun n : Num => (n : ℕ)) hright
          simp at hleftNat hrightNat
          have hleftPos : 0 < (leftPos : ℕ) := PosNum.to_nat_pos leftPos
          have hcompare :
              binaryLEBitsAux true (encodePosNum leftPos) [] = false :=
            binaryLEBitsAux_right_of_nonempty true
              (encodePosNum_nonempty leftPos)
          simp [hleftNat, hrightNat, encodeNum, hcompare,
            Nat.ne_of_gt hleftPos]
      | pos rightPos =>
          have hleftNat := congrArg (fun n : Num => (n : ℕ)) hleft
          have hrightNat := congrArg (fun n : Num => (n : ℕ)) hright
          simp at hleftNat hrightNat
          rw [show encodeNum (Num.pos leftPos) = encodePosNum leftPos by rfl,
            show encodeNum (Num.pos rightPos) = encodePosNum rightPos by rfl,
            binaryLEBitsAux_encodePosNum,
            orderingLEResult_cmp_true]
          simp [hleftNat, hrightNat]

/-- Input and single-bit output stacks for binary comparison. -/
inductive CompareStack
  | input
  | output
  deriving DecidableEq, Fintype

/-- The comparison program needs one scanning label. -/
inductive CompareLabel
  | scan
  deriving DecidableEq, Fintype

/-- Finite control stores the last aligned pair and the decision from all bit
positions inspected so far. -/
structure CompareState where
  pair : Option (Option Bool × Option Bool)
  result : Bool
  deriving DecidableEq, Fintype

private def compareInitialState : CompareState :=
  ⟨none, true⟩

private def comparePoppedPair
    (state : CompareState)
    (pair : Option (Option Bool × Option Bool)) : CompareState :=
  match pair with
  | none => { state with pair := none }
  | some bits =>
      ⟨some bits, binaryLEUpdate state.result bits.1 bits.2⟩

private def comparePairPresent : CompareState → Bool
  | ⟨some _, _⟩ => true
  | _ => false

private def compareResult (state : CompareState) : Bool :=
  state.result

private def CompareAlphabet : CompareStack → Type
  | .input => Option Bool × Option Bool
  | .output => Bool

/-- One-pass finite program for aligned binary comparison. -/
def binaryLEProgram :
    CompareLabel → TM2.Stmt CompareAlphabet CompareLabel CompareState
  | .scan =>
      .pop .input comparePoppedPair <|
        .branch comparePairPresent
          (.goto (fun _ => .scan))
          (.push .output compareResult <|
            .load (fun _ => compareInitialState) .halt)

/-- Concrete finite machine deciding less-than-or-equal on paired binary
naturals. -/
def binaryLEComputer : FinTM2 where
  K := CompareStack
  k₀ := .input
  k₁ := .output
  Γ := CompareAlphabet
  Λ := CompareLabel
  main := .scan
  σ := CompareState
  initialState := compareInitialState
  Γk₀Fin := by
    change Fintype (Option Bool × Option Bool)
    infer_instance
  m := binaryLEProgram

private def compareStackContents
    (input : List (Option Bool × Option Bool)) (output : List Bool) :
    (index : CompareStack) → List (CompareAlphabet index)
  | .input => input
  | .output => output

private def compareCfg (label : Option CompareLabel) (state : CompareState)
    (input : List (Option Bool × Option Bool)) (output : List Bool) :
    binaryLEComputer.Cfg where
  l := label
  var := state
  stk := compareStackContents input output

private theorem compare_step_cons
    (pair : Option Bool × Option Bool)
    (pairs : List (Option Bool × Option Bool)) (output : List Bool)
    (state : CompareState) :
    binaryLEComputer.step
        (compareCfg (some .scan) state (pair :: pairs) output) =
      some (compareCfg (some .scan)
        (comparePoppedPair state (some pair)) pairs output) := by
  rcases pair with ⟨left, right⟩
  rcases left with _ | left <;> rcases right with _ | right <;>
    simp [binaryLEComputer, FinTM2.step, compareCfg, binaryLEProgram,
      compareStackContents, CompareAlphabet, comparePoppedPair,
      comparePairPresent, binaryLEUpdate, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem compare_step_nil (output : List Bool)
    (state : CompareState) :
    binaryLEComputer.step
        (compareCfg (some .scan) state [] output) =
      some (compareCfg none compareInitialState []
        (state.result :: output)) := by
  rcases state with ⟨pair, result⟩
  simp [binaryLEComputer, FinTM2.step, compareCfg, binaryLEProgram,
    compareStackContents, CompareAlphabet, comparePoppedPair,
    comparePairPresent, compareResult, compareInitialState,
    Function.update]
  funext index
  cases index <;> rfl

private def compareEvalsToInTimeOne
    {start finish : binaryLEComputer.Cfg}
    (hstep : binaryLEComputer.step start = some finish) :
    EvalsToInTime binaryLEComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def compare_scan_evals
    (pairs : List (Option Bool × Option Bool)) (output : List Bool)
    (state : CompareState) :
    EvalsToInTime binaryLEComputer.step
      (compareCfg (some .scan) state pairs output)
      (some (compareCfg none compareInitialState []
        (binaryLEPairsAux state.result pairs :: output)))
      (pairs.length + 1) := by
  induction pairs generalizing state with
  | nil =>
      simpa [binaryLEPairsAux] using compareEvalsToInTimeOne
        (compare_step_nil output state)
  | cons pair pairs ih =>
      let middle := compareCfg (some .scan)
        (comparePoppedPair state (some pair)) pairs output
      have hone : EvalsToInTime binaryLEComputer.step
          (compareCfg (some .scan) state (pair :: pairs) output)
          (some middle) 1 :=
        compareEvalsToInTimeOne (by
          simpa [middle] using compare_step_cons pair pairs output state)
      have hrest := ih (comparePoppedPair state (some pair))
      have htrans := EvalsToInTime.trans binaryLEComputer.step
        1 (pairs.length + 1)
        (compareCfg (some .scan) state (pair :: pairs) output)
        middle
        (some (compareCfg none compareInitialState []
          (binaryLEPairsAux state.result (pair :: pairs) :: output)))
        hone
        (by
          simpa [middle, comparePoppedPair, binaryLEPairsAux] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private theorem compare_initList_eq_cfg
    (input : List (Option Bool × Option Bool)) :
    initList binaryLEComputer input =
      compareCfg (some .scan) compareInitialState input [] := by
  unfold initList compareCfg
  congr
  funext index
  cases index <;> rfl

private theorem compare_haltList_eq_cfg (output : List Bool) :
    haltList binaryLEComputer output =
      compareCfg none compareInitialState [] output := by
  unfold haltList compareCfg
  congr
  funext index
  cases index <;> rfl

/-- Binary comparison runs in exactly one scan plus the final output step. -/
def binaryLE_outputsInTime (pair : ℕ × ℕ) :
    TM2OutputsInTime binaryLEComputer (BinaryNatPair.encode pair)
      (some [decide (pair.1 ≤ pair.2)])
      ((BinaryNatPair.encode pair).length + 1) := by
  have hrun := compare_scan_evals (BinaryNatPair.encode pair) []
    compareInitialState
  rw [TM2OutputsInTime, compare_initList_eq_cfg]
  simp only [Option.map_some]
  rw [compare_haltList_eq_cfg]
  rcases pair with ⟨left, right⟩
  simpa [BinaryNatPair.encode, compareInitialState] using hrun

/-- A genuine linear-time finite-machine witness deciding comparison on two
canonical binary naturals. -/
noncomputable def binaryLEComputableInPolyTime :
    @TM2ComputableInPolyTime (ℕ × ℕ) Bool BinaryNatPair.finEncoding
      finEncodingBoolBool (fun pair => decide (pair.1 ≤ pair.2)) where
  tm := binaryLEComputer
  inputAlphabet := Equiv.refl (Option Bool × Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun pair := by
    simpa [BinaryNatPair.finEncoding, finEncodingBoolBool, encodeBool,
      Equiv.refl, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_X] using binaryLE_outputsInTime pair

/-! ## Binary addition

The Bertrand interval has upper endpoint `2 * q`, and bounded candidate
enumeration repeatedly advances binary values.  The following ripple-carry
pass complements successor and comparison with checked addition on the same
aligned-pair encoding.  Bits are visited least-significant first, so finite
control only needs the current carry.
-/

/-- One ripple-carry addition step.  The first component is the emitted bit;
the second is the carry into the next bit position. -/
def binaryAddStep (carry : Bool) (left right : Option Bool) : Bool × Bool :=
  match carry, left, right with
  | false, none, none => (false, false)
  | false, none, some false => (false, false)
  | false, some false, none => (false, false)
  | false, some false, some false => (false, false)
  | false, none, some true => (true, false)
  | false, some true, none => (true, false)
  | false, some false, some true => (true, false)
  | false, some true, some false => (true, false)
  | false, some true, some true => (false, true)
  | true, none, none => (true, false)
  | true, none, some false => (true, false)
  | true, some false, none => (true, false)
  | true, some false, some false => (true, false)
  | true, none, some true => (false, true)
  | true, some true, none => (false, true)
  | true, some false, some true => (false, true)
  | true, some true, some false => (false, true)
  | true, some true, some true => (true, true)

/-- Ripple-carry addition directly on two least-significant-bit-first words. -/
def binaryAddBitsAux : Bool → List Bool → List Bool → List Bool
  | carry, [], [] => if carry then [true] else []
  | carry, left :: lefts, [] =>
      let step := binaryAddStep carry (some left) none
      step.1 :: binaryAddBitsAux step.2 lefts []
  | carry, [], right :: rights =>
      let step := binaryAddStep carry none (some right)
      step.1 :: binaryAddBitsAux step.2 [] rights
  | carry, left :: lefts, right :: rights =>
      let step := binaryAddStep carry (some left) (some right)
      step.1 :: binaryAddBitsAux step.2 lefts rights

/-- The same addition fold over the aligned pair wire representation. -/
def binaryAddPairsAux : Bool →
    List (Option Bool × Option Bool) → List Bool
  | carry, [] => if carry then [true] else []
  | carry, pair :: pairs =>
      let step := binaryAddStep carry pair.1 pair.2
      step.1 :: binaryAddPairsAux step.2 pairs

@[simp]
theorem binaryAddPairsAux_zipBits
    (carry : Bool) (left right : List Bool) :
    binaryAddPairsAux carry (BinaryNatPair.zipBits left right) =
      binaryAddBitsAux carry left right := by
  induction left generalizing carry right with
  | nil =>
      induction right generalizing carry with
      | nil => simp [BinaryNatPair.zipBits, binaryAddPairsAux,
          binaryAddBitsAux]
      | cons right rights ih =>
          simp [BinaryNatPair.zipBits, binaryAddPairsAux,
            binaryAddBitsAux, ih]
  | cons left lefts ih =>
      cases right with
      | nil =>
          simp [BinaryNatPair.zipBits, binaryAddPairsAux,
            binaryAddBitsAux, ih]
      | cons right rights =>
          simp [BinaryNatPair.zipBits, binaryAddPairsAux,
            binaryAddBitsAux, ih]

private theorem binaryAddBitsAux_false_left_nil (bits : List Bool) :
    binaryAddBitsAux false [] bits = bits := by
  induction bits with
  | nil => simp [binaryAddBitsAux]
  | cons bit bits ih =>
      cases bit <;> simp [binaryAddBitsAux, binaryAddStep, ih]

private theorem binaryAddBitsAux_false_right_nil (bits : List Bool) :
    binaryAddBitsAux false bits [] = bits := by
  induction bits with
  | nil => simp [binaryAddBitsAux]
  | cons bit bits ih =>
      cases bit <;> simp [binaryAddBitsAux, binaryAddStep, ih]

private theorem binaryAddBitsAux_true_left_nil (bits : List Bool) :
    binaryAddBitsAux true [] bits = binarySuccBits bits := by
  induction bits with
  | nil => simp [binaryAddBitsAux, binarySuccBits]
  | cons bit bits ih =>
      cases bit <;> simp [binaryAddBitsAux, binaryAddStep,
        binarySuccBits, binaryAddBitsAux_false_left_nil, ih]

private theorem binaryAddBitsAux_true_right_nil (bits : List Bool) :
    binaryAddBitsAux true bits [] = binarySuccBits bits := by
  induction bits with
  | nil => simp [binaryAddBitsAux, binarySuccBits]
  | cons bit bits ih =>
      cases bit <;> simp [binaryAddBitsAux, binaryAddStep,
        binarySuccBits, binaryAddBitsAux_false_right_nil, ih]

private theorem binaryAddBitsAux_true_eq_succ
    (left right : List Bool) :
    binaryAddBitsAux true left right =
      binarySuccBits (binaryAddBitsAux false left right) := by
  induction left generalizing right with
  | nil =>
      rw [binaryAddBitsAux_true_left_nil,
        binaryAddBitsAux_false_left_nil]
  | cons left lefts ih =>
      cases right with
      | nil =>
          rw [binaryAddBitsAux_true_right_nil,
            binaryAddBitsAux_false_right_nil]
      | cons right rights =>
          cases left <;> cases right <;>
            simp [binaryAddBitsAux, binaryAddStep, binarySuccBits, ih]

private theorem binaryAddBitsAux_encodePosNum
    (left right : PosNum) :
    binaryAddBitsAux false (encodePosNum left) (encodePosNum right) =
      encodePosNum (left + right) := by
  induction left generalizing right with
  | one =>
      cases right with
      | one =>
          change binaryAddBitsAux false [true] [true] = [false, true]
          simp [binaryAddBitsAux, binaryAddStep]
      | bit1 right =>
          change binaryAddBitsAux false [true]
              (true :: encodePosNum right) =
            encodePosNum (PosNum.bit1 right).succ
          simp only [binaryAddBitsAux, binaryAddStep]
          rw [binaryAddBitsAux_true_left_nil,
            binarySuccBits_encodePosNum]
          change false :: encodePosNum right.succ =
            false :: encodePosNum right.succ
          rfl
      | bit0 right =>
          change binaryAddBitsAux false [true]
              (false :: encodePosNum right) =
            encodePosNum (PosNum.bit0 right).succ
          simp only [binaryAddBitsAux, binaryAddStep]
          rw [binaryAddBitsAux_false_left_nil]
          rfl
  | bit1 left ih =>
      cases right with
      | one =>
          change binaryAddBitsAux false (true :: encodePosNum left)
              [true] = encodePosNum (PosNum.bit1 left).succ
          simp only [binaryAddBitsAux, binaryAddStep]
          rw [binaryAddBitsAux_true_right_nil,
            binarySuccBits_encodePosNum]
          change false :: encodePosNum left.succ =
            false :: encodePosNum left.succ
          rfl
      | bit1 right =>
          change binaryAddBitsAux false (true :: encodePosNum left)
              (true :: encodePosNum right) =
            encodePosNum (PosNum.bit0 ((left + right).succ))
          simp only [binaryAddBitsAux, binaryAddStep, encodePosNum]
          rw [binaryAddBitsAux_true_eq_succ,
            ih, binarySuccBits_encodePosNum]
      | bit0 right =>
          change binaryAddBitsAux false (true :: encodePosNum left)
              (false :: encodePosNum right) =
            encodePosNum (PosNum.bit1 (left + right))
          simp only [binaryAddBitsAux, binaryAddStep, encodePosNum]
          rw [ih]
  | bit0 left ih =>
      cases right with
      | one =>
          change binaryAddBitsAux false (false :: encodePosNum left)
              [true] = encodePosNum (PosNum.bit0 left).succ
          simp only [binaryAddBitsAux, binaryAddStep]
          rw [binaryAddBitsAux_false_right_nil]
          rfl
      | bit1 right =>
          change binaryAddBitsAux false (false :: encodePosNum left)
              (true :: encodePosNum right) =
            encodePosNum (PosNum.bit1 (left + right))
          simp only [binaryAddBitsAux, binaryAddStep, encodePosNum]
          rw [ih]
      | bit0 right =>
          change binaryAddBitsAux false (false :: encodePosNum left)
              (false :: encodePosNum right) =
            encodePosNum (PosNum.bit0 (left + right))
          simp only [binaryAddBitsAux, binaryAddStep, encodePosNum]
          rw [ih]

private theorem binaryAddBitsAux_encodeNum (left right : Num) :
    binaryAddBitsAux false (encodeNum left) (encodeNum right) =
      encodeNum (left + right) := by
  cases left with
  | zero =>
      change binaryAddBitsAux false [] (encodeNum right) = encodeNum right
      exact binaryAddBitsAux_false_left_nil (encodeNum right)
  | pos left =>
      cases right with
      | zero =>
          change binaryAddBitsAux false (encodePosNum left) [] =
            encodePosNum left
          exact binaryAddBitsAux_false_right_nil (encodePosNum left)
      | pos right =>
          change binaryAddBitsAux false (encodePosNum left)
              (encodePosNum right) = encodePosNum (left + right)
          exact
            binaryAddBitsAux_encodePosNum left right

/-- Ripple-carry addition agrees with natural-number addition on mathlib's
canonical binary encodings, including zero on either side. -/
@[simp]
theorem binaryAddBitsAux_encodeNat (left right : ℕ) :
    binaryAddBitsAux false (encodeNat left) (encodeNat right) =
      encodeNat (left + right) := by
  unfold encodeNat
  rw [binaryAddBitsAux_encodeNum, ← Num.add_of_nat]

private theorem binaryAddPairsAux_length_le
    (carry : Bool) (pairs : List (Option Bool × Option Bool)) :
    (binaryAddPairsAux carry pairs).length ≤ pairs.length + 1 := by
  induction pairs generalizing carry with
  | nil => cases carry <;> simp [binaryAddPairsAux]
  | cons pair pairs ih =>
      simp only [binaryAddPairsAux, List.length_cons]
      exact Nat.succ_le_succ (ih (binaryAddStep carry pair.1 pair.2).2)

/-- Input, reverse-work, and canonical output stacks for binary addition. -/
inductive AddStack
  | input
  | work
  | output
  deriving DecidableEq, Fintype

/-- Ripple-carry scanning and output reversal phases. -/
inductive AddLabel
  | scan
  | reverse
  deriving DecidableEq, Fintype

/-- Finite control stores the latest aligned pair, its emitted bit, and the
carry into the next position. -/
structure AddState where
  pair : Option (Option Bool × Option Bool)
  bit : Option Bool
  carry : Bool
  deriving DecidableEq, Fintype

private def addInitialState : AddState :=
  ⟨none, none, false⟩

private def addPoppedPair
    (state : AddState)
    (pair : Option (Option Bool × Option Bool)) : AddState :=
  match pair with
  | none => { state with pair := none }
  | some bits =>
      let step := binaryAddStep state.carry bits.1 bits.2
      ⟨some bits, some step.1, step.2⟩

private def addPoppedWork
    (state : AddState) (bit : Option Bool) : AddState :=
  { state with bit := bit }

private def addPairPresent : AddState → Bool
  | ⟨some _, _, _⟩ => true
  | _ => false

private def addBitPresent : AddState → Bool
  | ⟨_, some _, _⟩ => true
  | _ => false

private def addCarry (state : AddState) : Bool :=
  state.carry

private def addEmittedBit : AddState → Bool
  | ⟨_, some bit, _⟩ => bit
  | _ => false

private def AddAlphabet : AddStack → Type
  | .input => Option Bool × Option Bool
  | .work => Bool
  | .output => Bool

/-- A finite ripple-carry adder.  Scanning pushes emitted bits onto a work
stack; the reverse phase restores least-significant-bit-first output order. -/
def binaryAddProgram :
    AddLabel → TM2.Stmt AddAlphabet AddLabel AddState
  | .scan =>
      .pop .input addPoppedPair <|
        .branch addPairPresent
          (.push .work addEmittedBit <|
            .goto (fun _ => .scan))
          (.branch addCarry
            (.push .work (fun _ => true) <|
              .goto (fun _ => .reverse))
            (.goto (fun _ => .reverse)))
  | .reverse =>
      .pop .work addPoppedWork <|
        .branch addBitPresent
          (.push .output addEmittedBit <|
            .goto (fun _ => .reverse))
          (.load (fun _ => addInitialState) .halt)

/-- Concrete finite machine adding two aligned canonical binary naturals. -/
def binaryAddComputer : FinTM2 where
  K := AddStack
  k₀ := .input
  k₁ := .output
  Γ := AddAlphabet
  Λ := AddLabel
  main := .scan
  σ := AddState
  initialState := addInitialState
  Γk₀Fin := by
    change Fintype (Option Bool × Option Bool)
    infer_instance
  m := binaryAddProgram

private def addStackContents
    (input : List (Option Bool × Option Bool))
    (work output : List Bool) :
    (index : AddStack) → List (AddAlphabet index)
  | .input => input
  | .work => work
  | .output => output

private def addCfg (label : Option AddLabel) (state : AddState)
    (input : List (Option Bool × Option Bool))
    (work output : List Bool) : binaryAddComputer.Cfg where
  l := label
  var := state
  stk := addStackContents input work output

private theorem add_step_scan_cons
    (pair : Option Bool × Option Bool)
    (pairs : List (Option Bool × Option Bool))
    (work output : List Bool) (state : AddState) :
    binaryAddComputer.step
        (addCfg (some .scan) state (pair :: pairs) work output) =
      some (addCfg (some .scan)
        (addPoppedPair state (some pair)) pairs
        ((binaryAddStep state.carry pair.1 pair.2).1 :: work) output) := by
  rcases state with ⟨heldPair, heldBit, carry⟩
  rcases pair with ⟨left, right⟩
  rcases left with _ | left <;> rcases right with _ | right <;>
    cases carry <;>
    simp [binaryAddComputer, FinTM2.step, addCfg, binaryAddProgram,
      addStackContents, AddAlphabet, addPoppedPair, addPairPresent,
      addEmittedBit, binaryAddStep, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem add_step_scan_nil_false
    (work output : List Bool) (pair : Option (Option Bool × Option Bool))
    (bit : Option Bool) :
    binaryAddComputer.step
        (addCfg (some .scan) ⟨pair, bit, false⟩ [] work output) =
      some (addCfg (some .reverse) ⟨none, bit, false⟩ [] work output) := by
  simp [binaryAddComputer, FinTM2.step, addCfg, binaryAddProgram,
    addStackContents, AddAlphabet, addPoppedPair, addPairPresent, addCarry,
    Function.update]

private theorem add_step_scan_nil_true
    (work output : List Bool) (pair : Option (Option Bool × Option Bool))
    (bit : Option Bool) :
    binaryAddComputer.step
        (addCfg (some .scan) ⟨pair, bit, true⟩ [] work output) =
      some (addCfg (some .reverse) ⟨none, bit, true⟩ []
        (true :: work) output) := by
  simp [binaryAddComputer, FinTM2.step, addCfg, binaryAddProgram,
    addStackContents, AddAlphabet, addPoppedPair, addPairPresent, addCarry,
    Function.update]
  funext index
  cases index <;> rfl

private theorem add_step_reverse_cons
    (bit : Bool) (work output : List Bool) (state : AddState) :
    binaryAddComputer.step
        (addCfg (some .reverse) state [] (bit :: work) output) =
      some (addCfg (some .reverse) (addPoppedWork state (some bit))
        [] work (bit :: output)) := by
  rcases state with ⟨pair, heldBit, carry⟩
  cases bit <;>
    simp [binaryAddComputer, FinTM2.step, addCfg, binaryAddProgram,
      addStackContents, AddAlphabet, addPoppedWork, addBitPresent,
      addEmittedBit, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem add_step_reverse_nil
    (output : List Bool) (state : AddState) :
    binaryAddComputer.step
        (addCfg (some .reverse) state [] [] output) =
      some (addCfg none addInitialState [] [] output) := by
  rcases state with ⟨pair, bit, carry⟩
  simp [binaryAddComputer, FinTM2.step, addCfg, binaryAddProgram,
    addStackContents, AddAlphabet, addPoppedWork, addBitPresent,
    addInitialState, Function.update]

private def addEvalsToInTimeOne
    {start finish : binaryAddComputer.Cfg}
    (hstep : binaryAddComputer.step start = some finish) :
    EvalsToInTime binaryAddComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def addFoldState :
    AddState → List (Option Bool × Option Bool) → AddState
  | state, [] => addPoppedPair state none
  | state, pair :: pairs =>
      addFoldState (addPoppedPair state (some pair)) pairs

private def add_scan_evals
    (pairs : List (Option Bool × Option Bool))
    (work output : List Bool) (state : AddState) :
    EvalsToInTime binaryAddComputer.step
      (addCfg (some .scan) state pairs work output)
      (some (addCfg (some .reverse) (addFoldState state pairs) []
        ((binaryAddPairsAux state.carry pairs).reverse ++ work) output))
      (pairs.length + 1) := by
  induction pairs generalizing work state with
  | nil =>
      rcases state with ⟨pair, bit, carry⟩
      cases carry with
      | false =>
          simpa [addFoldState, binaryAddPairsAux] using
            addEvalsToInTimeOne
              (add_step_scan_nil_false work output pair bit)
      | true =>
          simpa [addFoldState, binaryAddPairsAux] using
            addEvalsToInTimeOne
              (add_step_scan_nil_true work output pair bit)
  | cons pair pairs ih =>
      let nextState := addPoppedPair state (some pair)
      let step := binaryAddStep state.carry pair.1 pair.2
      let middle := addCfg (some .scan) nextState pairs
        (step.1 :: work) output
      have hone : EvalsToInTime binaryAddComputer.step
          (addCfg (some .scan) state (pair :: pairs) work output)
          (some middle) 1 :=
        addEvalsToInTimeOne (by
          simpa [middle, nextState, step] using
            add_step_scan_cons pair pairs work output state)
      have hrest := ih (step.1 :: work) nextState
      have htrans := EvalsToInTime.trans binaryAddComputer.step
        1 (pairs.length + 1)
        (addCfg (some .scan) state (pair :: pairs) work output)
        middle
        (some (addCfg (some .reverse)
          (addFoldState state (pair :: pairs)) []
          ((binaryAddPairsAux state.carry (pair :: pairs)).reverse ++ work)
          output))
        hone
        (by
          simpa [middle, nextState, step, addFoldState,
            binaryAddPairsAux, addPoppedPair, List.reverse_cons,
            List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def add_reverse_evals
    (work output : List Bool) (state : AddState) :
    EvalsToInTime binaryAddComputer.step
      (addCfg (some .reverse) state [] work output)
      (some (addCfg none addInitialState [] []
        (work.reverse ++ output)))
      (work.length + 1) := by
  induction work generalizing output state with
  | nil =>
      simpa using addEvalsToInTimeOne (add_step_reverse_nil output state)
  | cons bit work ih =>
      let nextState := addPoppedWork state (some bit)
      let middle := addCfg (some .reverse) nextState [] work
        (bit :: output)
      have hone : EvalsToInTime binaryAddComputer.step
          (addCfg (some .reverse) state [] (bit :: work) output)
          (some middle) 1 :=
        addEvalsToInTimeOne (by
          simpa [middle, nextState] using
            add_step_reverse_cons bit work output state)
      have hrest := ih (bit :: output) nextState
      have htrans := EvalsToInTime.trans binaryAddComputer.step
        1 (work.length + 1)
        (addCfg (some .reverse) state [] (bit :: work) output)
        middle
        (some (addCfg none addInitialState [] []
          ((bit :: work).reverse ++ output)))
        hone
        (by simpa [middle, nextState, List.reverse_cons,
          List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private theorem add_initList_eq_cfg
    (input : List (Option Bool × Option Bool)) :
    initList binaryAddComputer input =
      addCfg (some .scan) addInitialState input [] [] := by
  unfold initList addCfg
  congr
  funext index
  cases index <;> rfl

private theorem add_haltList_eq_cfg (output : List Bool) :
    haltList binaryAddComputer output =
      addCfg none addInitialState [] [] output := by
  unfold haltList addCfg
  congr
  funext index
  cases index <;> rfl

/-- Binary addition uses one aligned scan and one output reversal, taking at
most `2s + 3` steps for paired input length `s`. -/
def binaryAdd_outputsInTime (pair : ℕ × ℕ) :
    TM2OutputsInTime binaryAddComputer (BinaryNatPair.encode pair)
      (some (encodeNat (pair.1 + pair.2)))
      (2 * (BinaryNatPair.encode pair).length + 3) := by
  let input := BinaryNatPair.encode pair
  let result := binaryAddPairsAux false input
  have hscan := add_scan_evals input [] [] addInitialState
  have hreverse := add_reverse_evals result.reverse []
    (addFoldState addInitialState input)
  have hall := EvalsToInTime.trans binaryAddComputer.step
    (input.length + 1) (result.reverse.length + 1)
    (addCfg (some .scan) addInitialState input [] [])
    (addCfg (some .reverse) (addFoldState addInitialState input) []
      result.reverse [])
    (some (addCfg none addInitialState [] [] result))
    (by simpa [result] using hscan)
    (by simpa [result] using hreverse)
  have hlength := binaryAddPairsAux_length_le false input
  change result.length ≤ input.length + 1 at hlength
  have hmono : EvalsToInTime binaryAddComputer.step
      (addCfg (some .scan) addInitialState input [] [])
      (some (addCfg none addInitialState [] [] result))
      (2 * input.length + 3) :=
    evalsToInTimeMono hall (by
      simp only [List.length_reverse]
      omega)
  rw [TM2OutputsInTime, add_initList_eq_cfg]
  simp only [Option.map_some]
  rw [add_haltList_eq_cfg]
  rcases pair with ⟨left, right⟩
  simpa [input, result, BinaryNatPair.encode, addInitialState] using hmono

/-- A genuine linear-time finite-machine witness for addition on mathlib's
standard binary natural-number encoding. -/
noncomputable def binaryAddComputableInPolyTime :
    @TM2ComputableInPolyTime (ℕ × ℕ) ℕ BinaryNatPair.finEncoding
      finEncodingNatBool (fun pair => pair.1 + pair.2) where
  tm := binaryAddComputer
  inputAlphabet := Equiv.refl (Option Bool × Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun pair := by
    simpa [BinaryNatPair.finEncoding, finEncodingNatBool, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_X] using binaryAdd_outputsInTime pair

/-! ## Bertrand-interval candidate enumeration

The interval contains `q` candidates, so enumerating it cannot be polynomial
in the bit length of a standalone binary encoding of `q`.  The full CSP input
provides the needed padding: its explicit domain entries witness that
`q ≤ input length`.  The component below makes that invariant explicit by
using mathlib's unary encoding of the scan bound.  It emits the candidates in
the checked stack-oriented raw-natural-list encoding used by the serialization
pass above.  A later structural compiler pass will produce this unary bound
while deduplicating the domain symbols.
-/

/-- The next `count` naturals strictly above `current`. -/
def intervalFrom : ℕ → ℕ → List ℕ
  | 0, _ => []
  | count + 1, current => (current + 1) :: intervalFrom count (current + 1)

/-- The complete inclusive Bertrand scan interval `[q + 1, 2q]`. -/
def bertrandCandidates (q : ℕ) : List ℕ :=
  intervalFrom q q

@[simp]
theorem intervalFrom_length (count current : ℕ) :
    (intervalFrom count current).length = count := by
  induction count generalizing current with
  | zero => rfl
  | succ count ih => simp [intervalFrom, ih]

@[simp]
theorem bertrandCandidates_length (q : ℕ) :
    (bertrandCandidates q).length = q := by
  simp [bertrandCandidates]

theorem mem_intervalFrom_iff (value count current : ℕ) :
    value ∈ intervalFrom count current ↔
      current < value ∧ value ≤ current + count := by
  induction count generalizing current with
  | zero => simp [intervalFrom]
  | succ count ih =>
      simp only [intervalFrom, List.mem_cons, ih]
      omega

@[simp]
theorem mem_bertrandCandidates_iff (q value : ℕ) :
    value ∈ bertrandCandidates q ↔ q < value ∧ value ≤ 2 * q := by
  rw [bertrandCandidates, mem_intervalFrom_iff]
  omega

@[simp]
private theorem unaryEncodeNat_length (n : ℕ) :
    (unaryEncodeNat n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, ih]

/-- Input unary markers, a preserved unary copy, the current binary value,
binary work storage, and the stack-oriented raw-field output. -/
inductive EnumerateStack
  | input
  | unary
  | counter
  | work
  | output
  deriving DecidableEq, Fintype

/-- Counting, in-place increment, field emission, candidate iteration, and
final cleanup phases. -/
inductive EnumerateLabel
  | count
  | incCarry
  | incCopy
  | incRestore
  | emitStart
  | emitCopy
  | emitRestore
  | candidates
  | cleanup
  deriving DecidableEq, Fintype

/-- Finite control stores one popped bit and whether increment returns to
field emission rather than the initial unary-counting loop. -/
structure EnumerateState where
  bit : Option Bool
  returnToEmit : Bool
  deriving DecidableEq, Fintype

private def enumerateInitialState : EnumerateState :=
  ⟨none, false⟩

private def enumeratePoppedBit
    (state : EnumerateState) (bit : Option Bool) : EnumerateState :=
  { state with bit := bit }

private def enumerateSetReturn
    (returnToEmit : Bool) (_state : EnumerateState) : EnumerateState :=
  ⟨none, returnToEmit⟩

private def enumerateBitPresent : EnumerateState → Bool
  | ⟨some _, _⟩ => true
  | _ => false

private def enumerateBitTrue : EnumerateState → Bool
  | ⟨some true, _⟩ => true
  | _ => false

private def enumerateHeldBit : EnumerateState → Bool
  | ⟨some bit, _⟩ => bit
  | _ => false

private def enumerateHeldRawBit : EnumerateState → Option Bool
  | ⟨some bit, _⟩ => some bit
  | _ => none

private def enumerateReturnToEmit (state : EnumerateState) : Bool :=
  state.returnToEmit

private def EnumerateAlphabet : EnumerateStack → Type
  | .input => Bool
  | .unary => Bool
  | .counter => Bool
  | .work => Bool
  | .output => Option Bool

/-- A finite machine that counts a unary bound into binary, emits the count
field, then emits each candidate through `2q` while preserving the counter. -/
def bertrandCandidateProgram :
    EnumerateLabel → TM2.Stmt EnumerateAlphabet EnumerateLabel EnumerateState
  | .count =>
      .pop .input enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.push .unary (fun _ => true) <|
            .load (enumerateSetReturn false) <|
              .goto (fun _ => .incCarry))
          (.goto (fun _ => .emitStart))
  | .incCarry =>
      .pop .counter enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.branch enumerateBitTrue
            (.push .work (fun _ => false) <|
              .goto (fun _ => .incCarry))
            (.push .work (fun _ => true) <|
              .goto (fun _ => .incCopy)))
          (.push .work (fun _ => true) <|
            .goto (fun _ => .incRestore))
  | .incCopy =>
      .pop .counter enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.push .work enumerateHeldBit <|
            .goto (fun _ => .incCopy))
          (.goto (fun _ => .incRestore))
  | .incRestore =>
      .pop .work enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.push .counter enumerateHeldBit <|
            .goto (fun _ => .incRestore))
          (.branch enumerateReturnToEmit
            (.goto (fun _ => .emitStart))
            (.goto (fun _ => .count)))
  | .emitStart =>
      .push .output (fun _ => none) <|
        .goto (fun _ => .emitCopy)
  | .emitCopy =>
      .pop .counter enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.push .work enumerateHeldBit <|
            .push .output enumerateHeldRawBit <|
              .goto (fun _ => .emitCopy))
          (.goto (fun _ => .emitRestore))
  | .emitRestore =>
      .pop .work enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.push .counter enumerateHeldBit <|
            .goto (fun _ => .emitRestore))
          (.goto (fun _ => .candidates))
  | .candidates =>
      .pop .unary enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.load (enumerateSetReturn true) <|
            .goto (fun _ => .incCarry))
          (.goto (fun _ => .cleanup))
  | .cleanup =>
      .pop .counter enumeratePoppedBit <|
        .branch enumerateBitPresent
          (.goto (fun _ => .cleanup))
          (.load (fun _ => enumerateInitialState) .halt)

/-- Concrete finite machine enumerating the Bertrand interval from a unary
bound into `RawNatList.finEncoding`. -/
def bertrandCandidateComputer : FinTM2 where
  K := EnumerateStack
  k₀ := .input
  k₁ := .output
  Γ := EnumerateAlphabet
  Λ := EnumerateLabel
  main := .count
  σ := EnumerateState
  initialState := enumerateInitialState
  Γk₀Fin := Bool.fintype
  m := bertrandCandidateProgram

private def enumerateStackContents
    (input unary counter work : List Bool)
    (output : List (Option Bool)) :
    (index : EnumerateStack) → List (EnumerateAlphabet index)
  | .input => input
  | .unary => unary
  | .counter => counter
  | .work => work
  | .output => output

private def enumerateCfg (label : Option EnumerateLabel)
    (state : EnumerateState) (input unary counter work : List Bool)
    (output : List (Option Bool)) : bertrandCandidateComputer.Cfg where
  l := label
  var := state
  stk := enumerateStackContents input unary counter work output

private def enumerateEvalsToInTimeOne
    {start finish : bertrandCandidateComputer.Cfg}
    (hstep : bertrandCandidateComputer.step start = some finish) :
    EvalsToInTime bertrandCandidateComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem enumerate_step_count_cons
    (input unary counter : List Bool) (output : List (Option Bool)) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .count) enumerateInitialState
          (true :: input) unary counter [] output) =
      some (enumerateCfg (some .incCarry) enumerateInitialState
        input (true :: unary) counter [] output) := by
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateSetReturn,
    enumerateInitialState, Function.update]
  funext index
  cases index <;> rfl

private theorem enumerate_step_count_nil
    (unary counter : List Bool) (output : List (Option Bool)) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .count) enumerateInitialState
          [] unary counter [] output) =
      some (enumerateCfg (some .emitStart) enumerateInitialState
        [] unary counter [] output) := by
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateInitialState,
    Function.update]

private theorem enumerate_step_inc_carry_nil
    (input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incCarry) state input unary [] work output) =
      some (enumerateCfg (some .incRestore)
        (enumeratePoppedBit state none) input unary []
        (true :: work) output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, Function.update]
  funext index
  cases index <;> rfl

private theorem enumerate_step_inc_carry_false
    (bits input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incCarry) state input unary
          (false :: bits) work output) =
      some (enumerateCfg (some .incCopy)
        (enumeratePoppedBit state (some false)) input unary bits
        (true :: work) output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateBitTrue,
    Function.update]
  funext index
  cases index <;> rfl

private theorem enumerate_step_inc_carry_true
    (bits input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incCarry) state input unary
          (true :: bits) work output) =
      some (enumerateCfg (some .incCarry)
        (enumeratePoppedBit state (some true)) input unary bits
        (false :: work) output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateBitTrue,
    Function.update]
  funext index
  cases index <;> rfl

private theorem enumerate_step_inc_copy_nil
    (input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incCopy) state input unary [] work output) =
      some (enumerateCfg (some .incRestore)
        (enumeratePoppedBit state none) input unary [] work output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, Function.update]

private theorem enumerate_step_inc_copy_cons
    (bit : Bool) (bits input unary work : List Bool)
    (output : List (Option Bool)) (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incCopy) state input unary
          (bit :: bits) work output) =
      some (enumerateCfg (some .incCopy)
        (enumeratePoppedBit state (some bit)) input unary bits
        (bit :: work) output) := by
  rcases state with ⟨held, returnToEmit⟩
  cases bit <;>
    simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
      bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
      enumeratePoppedBit, enumerateBitPresent, enumerateHeldBit,
      Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem enumerate_step_inc_restore_cons
    (bit : Bool) (work input unary counter : List Bool)
    (output : List (Option Bool)) (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incRestore) state input unary counter
          (bit :: work) output) =
      some (enumerateCfg (some .incRestore)
        (enumeratePoppedBit state (some bit)) input unary
        (bit :: counter) work output) := by
  rcases state with ⟨held, returnToEmit⟩
  cases bit <;>
    simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
      bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
      enumeratePoppedBit, enumerateBitPresent, enumerateHeldBit,
      Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem enumerate_step_inc_restore_nil_false
    (input unary counter : List Bool) (output : List (Option Bool))
    (bit : Option Bool) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incRestore) ⟨bit, false⟩ input unary counter
          [] output) =
      some (enumerateCfg (some .count) enumerateInitialState
        input unary counter [] output) := by
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateReturnToEmit,
    enumerateInitialState, Function.update]

private theorem enumerate_step_inc_restore_nil_true
    (input unary counter : List Bool) (output : List (Option Bool))
    (bit : Option Bool) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .incRestore) ⟨bit, true⟩ input unary counter
          [] output) =
      some (enumerateCfg (some .emitStart) ⟨none, true⟩
        input unary counter [] output) := by
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateReturnToEmit,
    Function.update]

private theorem enumerate_step_emit_start
    (input unary counter work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .emitStart) state input unary counter work output) =
      some (enumerateCfg (some .emitCopy) state input unary counter work
        (none :: output)) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet]
  funext index
  cases index <;> rfl

private theorem enumerate_step_emit_copy_nil
    (input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .emitCopy) state input unary [] work output) =
      some (enumerateCfg (some .emitRestore)
        (enumeratePoppedBit state none) input unary [] work output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, Function.update]

private theorem enumerate_step_emit_copy_cons
    (bit : Bool) (bits input unary work : List Bool)
    (output : List (Option Bool)) (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .emitCopy) state input unary
          (bit :: bits) work output) =
      some (enumerateCfg (some .emitCopy)
        (enumeratePoppedBit state (some bit)) input unary bits
        (bit :: work) (some bit :: output)) := by
  rcases state with ⟨held, returnToEmit⟩
  cases bit <;>
    simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
      bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
      enumeratePoppedBit, enumerateBitPresent, enumerateHeldBit,
      enumerateHeldRawBit, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem enumerate_step_emit_restore_cons
    (bit : Bool) (work input unary counter : List Bool)
    (output : List (Option Bool)) (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .emitRestore) state input unary counter
          (bit :: work) output) =
      some (enumerateCfg (some .emitRestore)
        (enumeratePoppedBit state (some bit)) input unary
        (bit :: counter) work output) := by
  rcases state with ⟨held, returnToEmit⟩
  cases bit <;>
    simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
      bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
      enumeratePoppedBit, enumerateBitPresent, enumerateHeldBit,
      Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem enumerate_step_emit_restore_nil
    (input unary counter : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .emitRestore) state input unary counter [] output) =
      some (enumerateCfg (some .candidates)
        (enumeratePoppedBit state none) input unary counter [] output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, Function.update]

private theorem enumerate_step_candidates_cons
    (unary input counter : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .candidates) state input
          (true :: unary) counter [] output) =
      some (enumerateCfg (some .incCarry) ⟨none, true⟩
        input unary counter [] output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateSetReturn]
  funext index
  cases index <;> rfl

private theorem enumerate_step_candidates_nil
    (input counter : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .candidates) state input [] counter [] output) =
      some (enumerateCfg (some .cleanup)
        (enumeratePoppedBit state none) input [] counter [] output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent]

private theorem enumerate_step_cleanup_cons
    (bit : Bool) (bits : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .cleanup) state [] [] (bit :: bits) [] output) =
      some (enumerateCfg (some .cleanup)
        (enumeratePoppedBit state (some bit)) [] [] bits [] output) := by
  rcases state with ⟨held, returnToEmit⟩
  cases bit <;>
    simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
      bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
      enumeratePoppedBit, enumerateBitPresent] <;>
    (funext index; cases index <;> rfl)

private theorem enumerate_step_cleanup_nil
    (output : List (Option Bool)) (state : EnumerateState) :
    bertrandCandidateComputer.step
        (enumerateCfg (some .cleanup) state [] [] [] [] output) =
      some (enumerateCfg none enumerateInitialState [] [] [] [] output) := by
  rcases state with ⟨bit, returnToEmit⟩
  simp [bertrandCandidateComputer, FinTM2.step, enumerateCfg,
    bertrandCandidateProgram, enumerateStackContents, EnumerateAlphabet,
    enumeratePoppedBit, enumerateBitPresent, enumerateInitialState]

private def enumerate_inc_copy_evals
    (bits input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .incCopy) state input unary bits work output)
      (some (enumerateCfg (some .incRestore)
        ⟨none, state.returnToEmit⟩ input unary []
        (bits.reverse ++ work) output))
      (bits.length + 1) := by
  induction bits generalizing work state with
  | nil =>
      simpa using enumerateEvalsToInTimeOne
        (enumerate_step_inc_copy_nil input unary work output state)
  | cons bit bits ih =>
      let nextState := enumeratePoppedBit state (some bit)
      let middle := enumerateCfg (some .incCopy) nextState input unary bits
        (bit :: work) output
      have hone : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .incCopy) state input unary
            (bit :: bits) work output)
          (some middle) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [middle, nextState] using
            enumerate_step_inc_copy_cons bit bits input unary work output state)
      have hrest := ih (bit :: work) nextState
      have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (bits.length + 1)
        (enumerateCfg (some .incCopy) state input unary
          (bit :: bits) work output)
        middle
        (some (enumerateCfg (some .incRestore)
          ⟨none, state.returnToEmit⟩ input unary []
          ((bit :: bits).reverse ++ work) output))
        hone
        (by
          simpa [middle, nextState, enumeratePoppedBit,
            List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def enumerate_inc_carry_evals
    (bits input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .incCarry) state input unary bits work output)
      (some (enumerateCfg (some .incRestore)
        ⟨none, state.returnToEmit⟩ input unary []
        ((binarySuccBits bits).reverse ++ work) output))
      (bits.length + 1) := by
  induction bits generalizing work state with
  | nil =>
      simpa [binarySuccBits, enumeratePoppedBit] using
        enumerateEvalsToInTimeOne
          (enumerate_step_inc_carry_nil input unary work output state)
  | cons bit bits ih =>
      cases bit with
      | false =>
          let nextState := enumeratePoppedBit state (some false)
          let middle := enumerateCfg (some .incCopy) nextState input unary bits
            (true :: work) output
          have hone : EvalsToInTime bertrandCandidateComputer.step
              (enumerateCfg (some .incCarry) state input unary
                (false :: bits) work output)
              (some middle) 1 :=
            enumerateEvalsToInTimeOne (by
              simpa [middle, nextState] using
                enumerate_step_inc_carry_false bits input unary work output state)
          have hcopy :=
            enumerate_inc_copy_evals bits input unary (true :: work) output
              nextState
          have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
            1 (bits.length + 1)
            (enumerateCfg (some .incCarry) state input unary
              (false :: bits) work output)
            middle
            (some (enumerateCfg (some .incRestore)
              ⟨none, state.returnToEmit⟩ input unary []
              ((binarySuccBits (false :: bits)).reverse ++ work) output))
            hone
            (by
              simpa [middle, nextState, enumeratePoppedBit, binarySuccBits,
                List.reverse_cons, List.append_assoc] using hcopy)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans
      | true =>
          let nextState := enumeratePoppedBit state (some true)
          let middle := enumerateCfg (some .incCarry) nextState input unary bits
            (false :: work) output
          have hone : EvalsToInTime bertrandCandidateComputer.step
              (enumerateCfg (some .incCarry) state input unary
                (true :: bits) work output)
              (some middle) 1 :=
            enumerateEvalsToInTimeOne (by
              simpa [middle, nextState] using
                enumerate_step_inc_carry_true bits input unary work output state)
          have hrest := ih (false :: work) nextState
          have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
            1 (bits.length + 1)
            (enumerateCfg (some .incCarry) state input unary
              (true :: bits) work output)
            middle
            (some (enumerateCfg (some .incRestore)
              ⟨none, state.returnToEmit⟩ input unary []
              ((binarySuccBits (true :: bits)).reverse ++ work) output))
            hone
            (by
              simpa [middle, nextState, enumeratePoppedBit, binarySuccBits,
                List.reverse_cons, List.append_assoc] using hrest)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def enumerate_inc_restore_false_evals
    (work input unary counter : List Bool) (output : List (Option Bool))
    (bit : Option Bool) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .incRestore) ⟨bit, false⟩
        input unary counter work output)
      (some (enumerateCfg (some .count) enumerateInitialState
        input unary (work.reverse ++ counter) [] output))
      (work.length + 1) := by
  induction work generalizing counter bit with
  | nil =>
      simpa using enumerateEvalsToInTimeOne
        (enumerate_step_inc_restore_nil_false input unary counter output bit)
  | cons head tail ih =>
      let middle := enumerateCfg (some .incRestore) ⟨some head, false⟩
        input unary (head :: counter) tail output
      have hone : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .incRestore) ⟨bit, false⟩
            input unary counter (head :: tail) output)
          (some middle) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [middle, enumeratePoppedBit] using
            enumerate_step_inc_restore_cons head tail input unary counter
              output ⟨bit, false⟩)
      have hrest := ih (head :: counter) (some head)
      have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (tail.length + 1)
        (enumerateCfg (some .incRestore) ⟨bit, false⟩
          input unary counter (head :: tail) output)
        middle
        (some (enumerateCfg (some .count) enumerateInitialState
          input unary ((head :: tail).reverse ++ counter) [] output))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def enumerate_inc_restore_true_evals
    (work input unary counter : List Bool) (output : List (Option Bool))
    (bit : Option Bool) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .incRestore) ⟨bit, true⟩
        input unary counter work output)
      (some (enumerateCfg (some .emitStart) ⟨none, true⟩
        input unary (work.reverse ++ counter) [] output))
      (work.length + 1) := by
  induction work generalizing counter bit with
  | nil =>
      simpa using enumerateEvalsToInTimeOne
        (enumerate_step_inc_restore_nil_true input unary counter output bit)
  | cons head tail ih =>
      let middle := enumerateCfg (some .incRestore) ⟨some head, true⟩
        input unary (head :: counter) tail output
      have hone : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .incRestore) ⟨bit, true⟩
            input unary counter (head :: tail) output)
          (some middle) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [middle, enumeratePoppedBit] using
            enumerate_step_inc_restore_cons head tail input unary counter
              output ⟨bit, true⟩)
      have hrest := ih (head :: counter) (some head)
      have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (tail.length + 1)
        (enumerateCfg (some .incRestore) ⟨bit, true⟩
          input unary counter (head :: tail) output)
        middle
        (some (enumerateCfg (some .emitStart) ⟨none, true⟩
          input unary ((head :: tail).reverse ++ counter) [] output))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def enumerateIncrementTime (bits : List Bool) : ℕ :=
  (bits.length + 1) + ((binarySuccBits bits).length + 1)

private def enumerate_increment_false_evals
    (bits input unary : List Bool) (output : List (Option Bool)) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .incCarry) enumerateInitialState
        input unary bits [] output)
      (some (enumerateCfg (some .count) enumerateInitialState
        input unary (binarySuccBits bits) [] output))
      (enumerateIncrementTime bits) := by
  have hcarry := enumerate_inc_carry_evals bits input unary [] output
    enumerateInitialState
  have hrestore := enumerate_inc_restore_false_evals
    (binarySuccBits bits).reverse input unary [] output none
  have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
    (bits.length + 1) ((binarySuccBits bits).reverse.length + 1)
    (enumerateCfg (some .incCarry) enumerateInitialState
      input unary bits [] output)
    (enumerateCfg (some .incRestore) ⟨none, false⟩
      input unary [] (binarySuccBits bits).reverse output)
    (some (enumerateCfg (some .count) enumerateInitialState
      input unary (binarySuccBits bits) [] output))
    (by simpa [enumerateInitialState] using hcarry)
    (by simpa using hrestore)
  simpa [enumerateIncrementTime, Nat.add_comm] using htrans

private def enumerate_increment_true_evals
    (bits input unary : List Bool) (output : List (Option Bool)) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .incCarry) ⟨none, true⟩
        input unary bits [] output)
      (some (enumerateCfg (some .emitStart) ⟨none, true⟩
        input unary (binarySuccBits bits) [] output))
      (enumerateIncrementTime bits) := by
  have hcarry := enumerate_inc_carry_evals bits input unary [] output
    ⟨none, true⟩
  have hrestore := enumerate_inc_restore_true_evals
    (binarySuccBits bits).reverse input unary [] output none
  have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
    (bits.length + 1) ((binarySuccBits bits).reverse.length + 1)
    (enumerateCfg (some .incCarry) ⟨none, true⟩
      input unary bits [] output)
    (enumerateCfg (some .incRestore) ⟨none, true⟩
      input unary [] (binarySuccBits bits).reverse output)
    (some (enumerateCfg (some .emitStart) ⟨none, true⟩
      input unary (binarySuccBits bits) [] output))
    (by simpa using hcarry)
    (by simpa using hrestore)
  simpa [enumerateIncrementTime, Nat.add_comm] using htrans

private def enumerate_emit_copy_evals
    (bits input unary work : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .emitCopy) state input unary bits work output)
      (some (enumerateCfg (some .emitRestore)
        ⟨none, state.returnToEmit⟩ input unary []
        (bits.reverse ++ work)
        (bits.reverse.map some ++ output)))
      (bits.length + 1) := by
  induction bits generalizing work output state with
  | nil =>
      simpa using enumerateEvalsToInTimeOne
        (enumerate_step_emit_copy_nil input unary work output state)
  | cons bit bits ih =>
      let nextState := enumeratePoppedBit state (some bit)
      let middle := enumerateCfg (some .emitCopy) nextState input unary bits
        (bit :: work) (some bit :: output)
      have hone : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .emitCopy) state input unary
            (bit :: bits) work output)
          (some middle) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [middle, nextState] using
            enumerate_step_emit_copy_cons bit bits input unary work output state)
      have hrest := ih (bit :: work) (some bit :: output) nextState
      have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (bits.length + 1)
        (enumerateCfg (some .emitCopy) state input unary
          (bit :: bits) work output)
        middle
        (some (enumerateCfg (some .emitRestore)
          ⟨none, state.returnToEmit⟩ input unary []
          ((bit :: bits).reverse ++ work)
          ((bit :: bits).reverse.map some ++ output)))
        hone
        (by
          simpa [middle, nextState, enumeratePoppedBit,
            List.reverse_cons, List.map_append,
            List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def enumerate_emit_restore_evals
    (work input unary counter : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .emitRestore) state input unary counter work output)
      (some (enumerateCfg (some .candidates)
        ⟨none, state.returnToEmit⟩ input unary
        (work.reverse ++ counter) [] output))
      (work.length + 1) := by
  induction work generalizing counter state with
  | nil =>
      simpa using enumerateEvalsToInTimeOne
        (enumerate_step_emit_restore_nil input unary counter output state)
  | cons head tail ih =>
      let nextState := enumeratePoppedBit state (some head)
      let middle := enumerateCfg (some .emitRestore) nextState input unary
        (head :: counter) tail output
      have hone : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .emitRestore) state input unary counter
            (head :: tail) output)
          (some middle) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [middle, nextState] using
            enumerate_step_emit_restore_cons head tail input unary counter
              output state)
      have hrest := ih (head :: counter) nextState
      have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (tail.length + 1)
        (enumerateCfg (some .emitRestore) state input unary counter
          (head :: tail) output)
        middle
        (some (enumerateCfg (some .candidates)
          ⟨none, state.returnToEmit⟩ input unary
          ((head :: tail).reverse ++ counter) [] output))
        hone
        (by
          simpa [middle, nextState, enumeratePoppedBit,
            List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def enumerateEmitTime (bits : List Bool) : ℕ :=
  2 * bits.length + 3

private def enumerate_emit_evals
    (bits input unary : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .emitStart) state input unary bits [] output)
      (some (enumerateCfg (some .candidates)
        ⟨none, state.returnToEmit⟩ input unary bits []
        (RawNatList.segment bits ++ output)))
      (enumerateEmitTime bits) := by
  let afterStart := enumerateCfg (some .emitCopy) state input unary bits []
    (none :: output)
  have hstart : EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .emitStart) state input unary bits [] output)
      (some afterStart) 1 :=
    enumerateEvalsToInTimeOne (by
      simpa [afterStart] using
        enumerate_step_emit_start input unary bits [] output state)
  have hcopy := enumerate_emit_copy_evals bits input unary []
    (none :: output) state
  let afterCopy := enumerateCfg (some .emitRestore)
    ⟨none, state.returnToEmit⟩ input unary [] bits.reverse
    (bits.reverse.map some ++ none :: output)
  have hfirst := EvalsToInTime.trans bertrandCandidateComputer.step
    1 (bits.length + 1)
    (enumerateCfg (some .emitStart) state input unary bits [] output)
    afterStart
    (some afterCopy)
    hstart
    (by simpa [afterStart, afterCopy] using hcopy)
  have hrestore := enumerate_emit_restore_evals bits.reverse input unary []
    (bits.reverse.map some ++ none :: output)
    ⟨none, state.returnToEmit⟩
  have hall := EvalsToInTime.trans bertrandCandidateComputer.step
    (1 + (bits.length + 1)) (bits.reverse.length + 1)
    (enumerateCfg (some .emitStart) state input unary bits [] output)
    afterCopy
    (some (enumerateCfg (some .candidates)
      ⟨none, state.returnToEmit⟩ input unary bits []
      (RawNatList.segment bits ++ output)))
    (by simpa [Nat.add_comm] using hfirst)
    (by
      simpa [afterCopy, RawNatList.segment, List.append_assoc] using hrestore)
  simpa [enumerateEmitTime, two_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hall

private def enumerate_cleanup_evals
    (bits : List Bool) (output : List (Option Bool))
    (state : EnumerateState) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .cleanup) state [] [] bits [] output)
      (some (enumerateCfg none enumerateInitialState [] [] [] [] output))
      (bits.length + 1) := by
  induction bits generalizing state with
  | nil =>
      simpa using enumerateEvalsToInTimeOne
        (enumerate_step_cleanup_nil output state)
  | cons bit bits ih =>
      let nextState := enumeratePoppedBit state (some bit)
      let middle := enumerateCfg (some .cleanup) nextState
        [] [] bits [] output
      have hone : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .cleanup) state
            [] [] (bit :: bits) [] output)
          (some middle) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [middle, nextState] using
            enumerate_step_cleanup_cons bit bits output state)
      have hrest := ih nextState
      have htrans := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (bits.length + 1)
        (enumerateCfg (some .cleanup) state
          [] [] (bit :: bits) [] output)
        middle
        (some (enumerateCfg none enumerateInitialState [] [] [] [] output))
        hone
        (by simpa [middle] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def enumerateCountTime : ℕ → ℕ → ℕ
  | 0, _ => 1
  | remaining + 1, processed =>
      1 + enumerateIncrementTime (encodeNat processed) +
        enumerateCountTime remaining (processed + 1)

private def enumerate_count_evals
    (remaining processed : ℕ) (output : List (Option Bool)) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .count) enumerateInitialState
        (unaryEncodeNat remaining) (unaryEncodeNat processed)
        (encodeNat processed) [] output)
      (some (enumerateCfg (some .emitStart) enumerateInitialState
        [] (unaryEncodeNat (processed + remaining))
        (encodeNat (processed + remaining)) [] output))
      (enumerateCountTime remaining processed) := by
  induction remaining generalizing processed with
  | zero =>
      simpa [enumerateCountTime] using
        enumerateEvalsToInTimeOne
          (enumerate_step_count_nil (unaryEncodeNat processed)
            (encodeNat processed) output)
  | succ remaining ih =>
      let afterPop := enumerateCfg (some .incCarry) enumerateInitialState
        (unaryEncodeNat remaining) (unaryEncodeNat (processed + 1))
        (encodeNat processed) [] output
      have hpop : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .count) enumerateInitialState
            (unaryEncodeNat (remaining + 1)) (unaryEncodeNat processed)
            (encodeNat processed) [] output)
          (some afterPop) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [afterPop, unaryEncodeNat] using
            enumerate_step_count_cons (unaryEncodeNat remaining)
              (unaryEncodeNat processed) (encodeNat processed) output)
      have hinc := enumerate_increment_false_evals
        (encodeNat processed) (unaryEncodeNat remaining)
        (unaryEncodeNat (processed + 1)) output
      let afterInc := enumerateCfg (some .count) enumerateInitialState
        (unaryEncodeNat remaining) (unaryEncodeNat (processed + 1))
        (encodeNat (processed + 1)) [] output
      have hfirst := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (enumerateIncrementTime (encodeNat processed))
        (enumerateCfg (some .count) enumerateInitialState
          (unaryEncodeNat (remaining + 1)) (unaryEncodeNat processed)
          (encodeNat processed) [] output)
        afterPop
        (some afterInc)
        hpop
        (by
          simpa [afterPop, afterInc, binarySuccBits_encodeNat] using hinc)
      have hrest := ih (processed + 1)
      have hall := EvalsToInTime.trans bertrandCandidateComputer.step
        (1 + enumerateIncrementTime (encodeNat processed))
        (enumerateCountTime remaining (processed + 1))
        (enumerateCfg (some .count) enumerateInitialState
          (unaryEncodeNat (remaining + 1)) (unaryEncodeNat processed)
          (encodeNat processed) [] output)
        afterInc
        (some (enumerateCfg (some .emitStart) enumerateInitialState
          [] (unaryEncodeNat (processed + (remaining + 1)))
          (encodeNat (processed + (remaining + 1))) [] output))
        (by simpa [Nat.add_comm] using hfirst)
        (by
          simpa [afterInc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hrest)
      simpa [enumerateCountTime, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall

private def encodedIntervalSuffix (count current : ℕ) :
    List (Option Bool) :=
  (intervalFrom count current).reverse.flatMap
    (fun value => RawNatList.segment (encodeNat value))

private def enumerateCandidateTime : ℕ → ℕ → ℕ
  | 0, current => (encodeNat current).length + 2
  | count + 1, current =>
      1 + enumerateIncrementTime (encodeNat current) +
        enumerateEmitTime (encodeNat (current + 1)) +
        enumerateCandidateTime count (current + 1)

private def enumerate_candidates_evals
    (count current : ℕ) (output : List (Option Bool))
    (state : EnumerateState) :
    EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .candidates) state []
        (unaryEncodeNat count) (encodeNat current) [] output)
      (some (enumerateCfg none enumerateInitialState [] [] [] []
        (encodedIntervalSuffix count current ++ output)))
      (enumerateCandidateTime count current) := by
  induction count generalizing current output state with
  | zero =>
      let afterPop := enumerateCfg (some .cleanup)
        (enumeratePoppedBit state none) [] [] (encodeNat current) [] output
      have hpop : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .candidates) state [] []
            (encodeNat current) [] output)
          (some afterPop) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [afterPop] using
            enumerate_step_candidates_nil [] (encodeNat current) output state)
      have hcleanup := enumerate_cleanup_evals
        (encodeNat current) output (enumeratePoppedBit state none)
      have hall := EvalsToInTime.trans bertrandCandidateComputer.step
        1 ((encodeNat current).length + 1)
        (enumerateCfg (some .candidates) state [] []
          (encodeNat current) [] output)
        afterPop
        (some (enumerateCfg none enumerateInitialState [] [] [] [] output))
        hpop
        (by simpa [afterPop] using hcleanup)
      simpa [enumerateCandidateTime, encodedIntervalSuffix, intervalFrom,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall
  | succ count ih =>
      let afterPop := enumerateCfg (some .incCarry) ⟨none, true⟩
        [] (unaryEncodeNat count) (encodeNat current) [] output
      have hpop : EvalsToInTime bertrandCandidateComputer.step
          (enumerateCfg (some .candidates) state []
            (unaryEncodeNat (count + 1)) (encodeNat current) [] output)
          (some afterPop) 1 :=
        enumerateEvalsToInTimeOne (by
          simpa [afterPop, unaryEncodeNat] using
            enumerate_step_candidates_cons (unaryEncodeNat count) []
              (encodeNat current) output state)
      have hinc := enumerate_increment_true_evals
        (encodeNat current) [] (unaryEncodeNat count) output
      let afterInc := enumerateCfg (some .emitStart) ⟨none, true⟩
        [] (unaryEncodeNat count) (encodeNat (current + 1)) [] output
      have hfirst := EvalsToInTime.trans bertrandCandidateComputer.step
        1 (enumerateIncrementTime (encodeNat current))
        (enumerateCfg (some .candidates) state []
          (unaryEncodeNat (count + 1)) (encodeNat current) [] output)
        afterPop
        (some afterInc)
        hpop
        (by
          simpa [afterPop, afterInc, binarySuccBits_encodeNat] using hinc)
      have hemit := enumerate_emit_evals (encodeNat (current + 1)) []
        (unaryEncodeNat count) output ⟨none, true⟩
      let afterEmit := enumerateCfg (some .candidates) ⟨none, true⟩
        [] (unaryEncodeNat count) (encodeNat (current + 1)) []
        (RawNatList.segment (encodeNat (current + 1)) ++ output)
      have hsecond := EvalsToInTime.trans bertrandCandidateComputer.step
        (1 + enumerateIncrementTime (encodeNat current))
        (enumerateEmitTime (encodeNat (current + 1)))
        (enumerateCfg (some .candidates) state []
          (unaryEncodeNat (count + 1)) (encodeNat current) [] output)
        afterInc
        (some afterEmit)
        (by simpa [Nat.add_comm] using hfirst)
        (by simpa [afterInc, afterEmit] using hemit)
      have hrest := ih (current + 1)
        (RawNatList.segment (encodeNat (current + 1)) ++ output)
        ⟨none, true⟩
      have hall := EvalsToInTime.trans bertrandCandidateComputer.step
        ((1 + enumerateIncrementTime (encodeNat current)) +
          enumerateEmitTime (encodeNat (current + 1)))
        (enumerateCandidateTime count (current + 1))
        (enumerateCfg (some .candidates) state []
          (unaryEncodeNat (count + 1)) (encodeNat current) [] output)
        afterEmit
        (some (enumerateCfg none enumerateInitialState [] [] [] []
          (encodedIntervalSuffix (count + 1) current ++ output)))
        (by simpa [Nat.add_comm] using hsecond)
        (by
          simpa [afterEmit, encodedIntervalSuffix, intervalFrom,
            List.reverse_cons, List.flatMap_append,
            List.append_assoc] using hrest)
      simpa [enumerateCandidateTime, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall

private theorem enumerateIncrementTime_encodeNat_le (n : ℕ) :
    enumerateIncrementTime (encodeNat n) ≤ 2 * n + 3 := by
  have hbits := BinaryNatLists.encodeNat_length_le n
  have hsucc := binarySuccBits_length_le (encodeNat n)
  simp only [enumerateIncrementTime]
  omega

private theorem enumerateEmitTime_encodeNat_le (n : ℕ) :
    enumerateEmitTime (encodeNat n) ≤ 2 * n + 3 := by
  have hbits := BinaryNatLists.encodeNat_length_le n
  simp only [enumerateEmitTime]
  omega

private theorem enumerateCountTime_le (remaining processed : ℕ) :
    enumerateCountTime remaining processed ≤
      2 * remaining * (processed + remaining + 2) + 1 := by
  induction remaining generalizing processed with
  | zero => simp [enumerateCountTime]
  | succ remaining ih =>
      have hinc := enumerateIncrementTime_encodeNat_le processed
      have hrest := ih (processed + 1)
      rw [enumerateCountTime]
      calc
        1 + enumerateIncrementTime (encodeNat processed) +
            enumerateCountTime remaining (processed + 1) ≤
            1 + (2 * processed + 3) +
              (2 * remaining * (processed + 1 + remaining + 2) + 1) := by
                omega
        _ ≤ 2 * (remaining + 1) *
              (processed + (remaining + 1) + 2) + 1 := by
                nlinarith

private theorem enumerateCandidateTime_le (count current : ℕ) :
    enumerateCandidateTime count current ≤
      5 * (count + 1) * (current + count + 2) := by
  induction count generalizing current with
  | zero =>
      have hbits := BinaryNatLists.encodeNat_length_le current
      simp only [enumerateCandidateTime]
      nlinarith
  | succ count ih =>
      have hinc := enumerateIncrementTime_encodeNat_le current
      have hemit := enumerateEmitTime_encodeNat_le (current + 1)
      have hrest := ih (current + 1)
      rw [enumerateCandidateTime]
      calc
        1 + enumerateIncrementTime (encodeNat current) +
            enumerateEmitTime (encodeNat (current + 1)) +
            enumerateCandidateTime count (current + 1) ≤
            1 + (2 * current + 3) + (2 * (current + 1) + 3) +
              5 * (count + 1) * (current + 1 + count + 2) := by
                omega
        _ ≤ 5 * (count + 1 + 1) *
              (current + (count + 1) + 2) := by
                nlinarith

private theorem flatMap_segment_reverse_map_encode (xs : List ℕ) :
    (xs.map encodeNat).reverse.flatMap RawNatList.segment =
      xs.reverse.flatMap
        (fun value => RawNatList.segment (encodeNat value)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [List.reverse_cons, List.flatMap_append, ih]

private theorem rawNatList_encode_bertrandCandidates (q : ℕ) :
    RawNatList.encode (bertrandCandidates q) =
      encodedIntervalSuffix q q ++
        RawNatList.segment (encodeNat q) := by
  simp [RawNatList.encode, RawNatList.payloads, bertrandCandidates,
    encodedIntervalSuffix, List.reverse_cons,
    flatMap_segment_reverse_map_encode, List.flatMap_append]

private theorem enumerate_initList_eq_cfg (input : List Bool) :
    initList bertrandCandidateComputer input =
      enumerateCfg (some .count) enumerateInitialState input [] [] [] [] := by
  unfold initList enumerateCfg
  congr
  funext index
  cases index <;> rfl

private theorem enumerate_haltList_eq_cfg (output : List (Option Bool)) :
    haltList bertrandCandidateComputer output =
      enumerateCfg none enumerateInitialState [] [] [] [] output := by
  unfold haltList enumerateCfg
  congr
  funext index
  cases index <;> rfl

private def enumerateTotalTime (q : ℕ) : ℕ :=
  enumerateCountTime q 0 + enumerateEmitTime (encodeNat q) +
    enumerateCandidateTime q q

private theorem enumerateTotalTime_le (q : ℕ) :
    enumerateTotalTime q ≤ 16 * (q + 1) ^ 2 := by
  have hcount := enumerateCountTime_le q 0
  have hemit := enumerateEmitTime_encodeNat_le q
  have hcandidates := enumerateCandidateTime_le q q
  simp only [enumerateTotalTime]
  nlinarith [sq_nonneg (q : ℤ)]

/-- The concrete enumerator emits exactly `[q + 1, ..., 2q]` in at most
`16(q+1)^2` steps from the unary scan-bound encoding. -/
def bertrandCandidate_outputsInTime (q : ℕ) :
    TM2OutputsInTime bertrandCandidateComputer (unaryEncodeNat q)
      (some (RawNatList.encode (bertrandCandidates q)))
      (16 * (q + 1) ^ 2) := by
  have hcount := enumerate_count_evals q 0 []
  have hemit := enumerate_emit_evals (encodeNat q) []
    (unaryEncodeNat q) [] enumerateInitialState
  let afterCount := enumerateCfg (some .emitStart) enumerateInitialState
    [] (unaryEncodeNat q) (encodeNat q) [] []
  let afterEmit := enumerateCfg (some .candidates) enumerateInitialState
    [] (unaryEncodeNat q) (encodeNat q) []
    (RawNatList.segment (encodeNat q))
  have hfirst := EvalsToInTime.trans bertrandCandidateComputer.step
    (enumerateCountTime q 0) (enumerateEmitTime (encodeNat q))
    (enumerateCfg (some .count) enumerateInitialState
      (unaryEncodeNat q) [] [] [] [])
    afterCount
    (some afterEmit)
    (by
      simpa [afterCount, unaryEncodeNat, encodeNat, encodeNum] using hcount)
    (by simpa [afterCount, afterEmit, enumerateInitialState] using hemit)
  have hcandidates := enumerate_candidates_evals q q
    (RawNatList.segment (encodeNat q)) enumerateInitialState
  have hall := EvalsToInTime.trans bertrandCandidateComputer.step
    (enumerateCountTime q 0 + enumerateEmitTime (encodeNat q))
    (enumerateCandidateTime q q)
    (enumerateCfg (some .count) enumerateInitialState
      (unaryEncodeNat q) [] [] [] [])
    afterEmit
    (some (enumerateCfg none enumerateInitialState [] [] [] []
      (RawNatList.encode (bertrandCandidates q))))
    (by simpa [Nat.add_comm] using hfirst)
    (by
      rw [rawNatList_encode_bertrandCandidates]
      simpa [afterEmit, encodedIntervalSuffix] using hcandidates)
  have hmono : EvalsToInTime bertrandCandidateComputer.step
      (enumerateCfg (some .count) enumerateInitialState
        (unaryEncodeNat q) [] [] [] [])
      (some (enumerateCfg none enumerateInitialState [] [] [] []
        (RawNatList.encode (bertrandCandidates q))))
      (16 * (q + 1) ^ 2) :=
    evalsToInTimeMono
      (by simpa [enumerateTotalTime, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall)
      (enumerateTotalTime_le q)
  rw [TM2OutputsInTime, enumerate_initList_eq_cfg]
  simp only [Option.map_some]
  rw [enumerate_haltList_eq_cfg]
  exact hmono

/-- Genuine polynomial-time enumeration of the Bertrand interval.  Unary
input is intentional: the eventual full compiler establishes `q` by scanning
an explicit CSP input of length at least `q`. -/
noncomputable def bertrandCandidatesComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ (List ℕ) unaryFinEncodingNat
      RawNatList.finEncoding bertrandCandidates where
  tm := bertrandCandidateComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Option Bool)
  time := 16 * (Polynomial.X + 1) ^ 2
  outputsFun q := by
    simpa [unaryFinEncodingNat, RawNatList.finEncoding, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using
        bertrandCandidate_outputsInTime q

/-! ## Unary Bertrand-candidate stream

The candidate-primality machine below consumes unary naturals.  Converting the
binary fields emitted by `bertrandCandidateComputer` back to unary would add an
unnecessary adapter.  This companion producer keeps the original binary
enumerator intact for serialization while emitting the same semantic list in
`RawUnaryNatList.finEncoding` for the internal prime scan.
-/

/-- Unary input, a decreasing iteration counter, the current unary value,
scratch storage used to preserve that value while emitting it, and output. -/
inductive UnaryBertrandStack
  | input
  | remaining
  | current
  | work
  | output
  deriving DecidableEq, Fintype

/-- Copy the input twice, emit the count field, emit each larger candidate,
and erase all non-output stacks. -/
inductive UnaryBertrandLabel
  | count
  | emitStart
  | emitCopy
  | emitRestore
  | candidates
  | cleanup
  deriving DecidableEq, Fintype

abbrev UnaryBertrandState := Option Bool

private def unaryBertrandObserved
    (_state : UnaryBertrandState) (bit : Option Bool) :
    UnaryBertrandState :=
  bit

private def unaryBertrandMarkerPresent : UnaryBertrandState → Bool
  | some _ => true
  | none => false

private def unaryBertrandHeldBit : UnaryBertrandState → Bool
  | some bit => bit
  | none => false

private def UnaryBertrandAlphabet (_ : UnaryBertrandStack) : Type := Bool

/-- Generate the unary length field `q`, followed by the candidates
`q+1, ..., 2q`, in stack-oriented reverse-field order. -/
def unaryBertrandCandidateProgram :
    UnaryBertrandLabel →
      TM2.Stmt UnaryBertrandAlphabet UnaryBertrandLabel UnaryBertrandState
  | .count =>
      .pop .input unaryBertrandObserved <|
        .branch unaryBertrandMarkerPresent
          (.push .remaining unaryBertrandHeldBit <|
            .push .current unaryBertrandHeldBit <|
              .goto (fun _ => .count))
          (.goto (fun _ => .emitStart))
  | .emitStart =>
      .push .output (fun _ => false) <|
        .goto (fun _ => .emitCopy)
  | .emitCopy =>
      .pop .current unaryBertrandObserved <|
        .branch unaryBertrandMarkerPresent
          (.push .work unaryBertrandHeldBit <|
            .push .output unaryBertrandHeldBit <|
              .goto (fun _ => .emitCopy))
          (.goto (fun _ => .emitRestore))
  | .emitRestore =>
      .pop .work unaryBertrandObserved <|
        .branch unaryBertrandMarkerPresent
          (.push .current unaryBertrandHeldBit <|
            .goto (fun _ => .emitRestore))
          (.goto (fun _ => .candidates))
  | .candidates =>
      .pop .remaining unaryBertrandObserved <|
        .branch unaryBertrandMarkerPresent
          (.push .current unaryBertrandHeldBit <|
            .goto (fun _ => .emitStart))
          (.goto (fun _ => .cleanup))
  | .cleanup =>
      .pop .current unaryBertrandObserved <|
        .branch unaryBertrandMarkerPresent
          (.goto (fun _ => .cleanup))
          (.load (fun _ => none) .halt)

/-- Concrete producer for the unary-delimited Bertrand candidate stream. -/
def unaryBertrandCandidateComputer : FinTM2 where
  K := UnaryBertrandStack
  k₀ := .input
  k₁ := .output
  Γ := UnaryBertrandAlphabet
  Λ := UnaryBertrandLabel
  main := .count
  σ := UnaryBertrandState
  initialState := none
  Γk₀Fin := Bool.fintype
  m := unaryBertrandCandidateProgram

private def unaryBertrandStackContents
    (input remaining current work output : List Bool) :
    (index : UnaryBertrandStack) → List (UnaryBertrandAlphabet index)
  | .input => input
  | .remaining => remaining
  | .current => current
  | .work => work
  | .output => output

private def unaryBertrandCfg
    (label : Option UnaryBertrandLabel) (state : UnaryBertrandState)
    (input remaining current work output : List Bool) :
    unaryBertrandCandidateComputer.Cfg where
  l := label
  var := state
  stk := unaryBertrandStackContents input remaining current work output

private theorem unaryBertrand_step_count_cons
    (bit : Bool) (input remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .count) state (bit :: input) remaining
          current work output) =
      some (unaryBertrandCfg (some .count) (some bit) input
        (bit :: remaining) (bit :: current) work output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent, unaryBertrandHeldBit, Function.update]
  funext index
  cases index <;> rfl

private theorem unaryBertrand_step_count_nil
    (remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .count) state [] remaining current work
          output) =
      some (unaryBertrandCfg (some .emitStart) none [] remaining current work
        output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent]

private theorem unaryBertrand_step_emitStart
    (input remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .emitStart) state input remaining current work
          output) =
      some (unaryBertrandCfg (some .emitCopy) state input remaining current
        work (false :: output)) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet]
  funext index
  cases index <;> rfl

private theorem unaryBertrand_step_emitCopy_cons
    (bit : Bool) (input remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .emitCopy) state input remaining
          (bit :: current) work output) =
      some (unaryBertrandCfg (some .emitCopy) (some bit) input remaining
        current (bit :: work) (bit :: output)) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent, unaryBertrandHeldBit, Function.update]
  funext index
  cases index <;> rfl

private theorem unaryBertrand_step_emitCopy_nil
    (input remaining work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .emitCopy) state input remaining [] work
          output) =
      some (unaryBertrandCfg (some .emitRestore) none input remaining [] work
        output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent]

private theorem unaryBertrand_step_emitRestore_cons
    (bit : Bool) (input remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .emitRestore) state input remaining current
          (bit :: work) output) =
      some (unaryBertrandCfg (some .emitRestore) (some bit) input remaining
        (bit :: current) work output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent, unaryBertrandHeldBit, Function.update]
  funext index
  cases index <;> rfl

private theorem unaryBertrand_step_emitRestore_nil
    (input remaining current output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .emitRestore) state input remaining current []
          output) =
      some (unaryBertrandCfg (some .candidates) none input remaining current
        [] output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent]

private theorem unaryBertrand_step_candidates_cons
    (bit : Bool) (input remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .candidates) state input (bit :: remaining)
          current work output) =
      some (unaryBertrandCfg (some .emitStart) (some bit) input remaining
        (bit :: current) work output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent, unaryBertrandHeldBit, Function.update]
  funext index
  cases index <;> rfl

private theorem unaryBertrand_step_candidates_nil
    (input current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .candidates) state input [] current work
          output) =
      some (unaryBertrandCfg (some .cleanup) none input [] current work
        output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent]

private theorem unaryBertrand_step_cleanup_cons
    (bit : Bool) (input remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .cleanup) state input remaining
          (bit :: current) work output) =
      some (unaryBertrandCfg (some .cleanup) (some bit) input remaining
        current work output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent]
  funext index
  cases index <;> rfl

private theorem unaryBertrand_step_cleanup_nil
    (input remaining work output : List Bool)
    (state : UnaryBertrandState) :
    unaryBertrandCandidateComputer.step
        (unaryBertrandCfg (some .cleanup) state input remaining [] work
          output) =
      some (unaryBertrandCfg none none input remaining [] work output) := by
  simp [unaryBertrandCandidateComputer, FinTM2.step, unaryBertrandCfg,
    unaryBertrandCandidateProgram, unaryBertrandStackContents,
    UnaryBertrandAlphabet, unaryBertrandObserved,
    unaryBertrandMarkerPresent]

private def unaryBertrandEvalsToInTimeOne
    {start finish : unaryBertrandCandidateComputer.Cfg}
    (hstep : unaryBertrandCandidateComputer.step start = some finish) :
    EvalsToInTime unaryBertrandCandidateComputer.step start (some finish) 1
    where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def unaryBertrand_count_evals
    (input remaining current work output : List Bool)
    (state : UnaryBertrandState) :
    EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .count) state input remaining current work output)
      (some (unaryBertrandCfg (some .emitStart) none []
        (input.reverse ++ remaining) (input.reverse ++ current) work output))
      (input.length + 1) := by
  induction input generalizing remaining current state with
  | nil =>
      simpa using unaryBertrandEvalsToInTimeOne
        (unaryBertrand_step_count_nil remaining current work output state)
  | cons bit input ih =>
      let middle := unaryBertrandCfg (some .count) (some bit) input
        (bit :: remaining) (bit :: current) work output
      have hone : EvalsToInTime unaryBertrandCandidateComputer.step
          (unaryBertrandCfg (some .count) state (bit :: input) remaining
            current work output)
          (some middle) 1 :=
        unaryBertrandEvalsToInTimeOne (by
          simpa [middle] using unaryBertrand_step_count_cons bit input
            remaining current work output state)
      have hrest := ih (bit :: remaining) (bit :: current) (some bit)
      have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
        1 (input.length + 1)
        (unaryBertrandCfg (some .count) state (bit :: input) remaining
          current work output)
        middle
        (some (unaryBertrandCfg (some .emitStart) none []
          ((bit :: input).reverse ++ remaining)
          ((bit :: input).reverse ++ current) work output))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def unaryBertrand_emitCopy_evals
    (bits input remaining work output : List Bool)
    (state : UnaryBertrandState) :
    EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .emitCopy) state input remaining bits work output)
      (some (unaryBertrandCfg (some .emitRestore) none input remaining []
        (bits.reverse ++ work) (bits.reverse ++ output)))
      (bits.length + 1) := by
  induction bits generalizing work output state with
  | nil =>
      simpa using unaryBertrandEvalsToInTimeOne
        (unaryBertrand_step_emitCopy_nil input remaining work output state)
  | cons bit bits ih =>
      let middle := unaryBertrandCfg (some .emitCopy) (some bit) input
        remaining bits (bit :: work) (bit :: output)
      have hone : EvalsToInTime unaryBertrandCandidateComputer.step
          (unaryBertrandCfg (some .emitCopy) state input remaining
            (bit :: bits) work output)
          (some middle) 1 :=
        unaryBertrandEvalsToInTimeOne (by
          simpa [middle] using unaryBertrand_step_emitCopy_cons bit input
            remaining bits work output state)
      have hrest := ih (bit :: work) (bit :: output) (some bit)
      have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
        1 (bits.length + 1)
        (unaryBertrandCfg (some .emitCopy) state input remaining
          (bit :: bits) work output)
        middle
        (some (unaryBertrandCfg (some .emitRestore) none input remaining []
          ((bit :: bits).reverse ++ work)
          ((bit :: bits).reverse ++ output)))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def unaryBertrand_emitRestore_evals
    (work input remaining current output : List Bool)
    (state : UnaryBertrandState) :
    EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .emitRestore) state input remaining current work
        output)
      (some (unaryBertrandCfg (some .candidates) none input remaining
        (work.reverse ++ current) [] output))
      (work.length + 1) := by
  induction work generalizing current state with
  | nil =>
      simpa using unaryBertrandEvalsToInTimeOne
        (unaryBertrand_step_emitRestore_nil input remaining current output state)
  | cons bit work ih =>
      let middle := unaryBertrandCfg (some .emitRestore) (some bit) input
        remaining (bit :: current) work output
      have hone : EvalsToInTime unaryBertrandCandidateComputer.step
          (unaryBertrandCfg (some .emitRestore) state input remaining current
            (bit :: work) output)
          (some middle) 1 :=
        unaryBertrandEvalsToInTimeOne (by
          simpa [middle] using unaryBertrand_step_emitRestore_cons bit input
            remaining current work output state)
      have hrest := ih (bit :: current) (some bit)
      have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
        1 (work.length + 1)
        (unaryBertrandCfg (some .emitRestore) state input remaining current
          (bit :: work) output)
        middle
        (some (unaryBertrandCfg (some .candidates) none input remaining
          ((bit :: work).reverse ++ current) [] output))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def unaryBertrand_emit_evals
    (bits remaining output : List Bool) (state : UnaryBertrandState) :
    EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .emitStart) state [] remaining bits [] output)
      (some (unaryBertrandCfg (some .candidates) none [] remaining bits []
        (bits.reverse ++ false :: output)))
      (2 * bits.length + 3) := by
  let afterStart := unaryBertrandCfg (some .emitCopy) state [] remaining bits []
    (false :: output)
  have hstart : EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .emitStart) state [] remaining bits [] output)
      (some afterStart) 1 :=
    unaryBertrandEvalsToInTimeOne (by
      simpa [afterStart] using unaryBertrand_step_emitStart [] remaining bits
        [] output state)
  have hcopy := unaryBertrand_emitCopy_evals bits [] remaining []
    (false :: output) state
  let afterCopy := unaryBertrandCfg (some .emitRestore) none [] remaining []
    bits.reverse (bits.reverse ++ false :: output)
  have hfirst := EvalsToInTime.trans unaryBertrandCandidateComputer.step
    1 (bits.length + 1)
    (unaryBertrandCfg (some .emitStart) state [] remaining bits [] output)
    afterStart
    (some afterCopy)
    hstart
    (by simpa [afterStart, afterCopy] using hcopy)
  have hrestore := unaryBertrand_emitRestore_evals bits.reverse [] remaining []
    (bits.reverse ++ false :: output) none
  have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
    (1 + (bits.length + 1)) (bits.reverse.length + 1)
    (unaryBertrandCfg (some .emitStart) state [] remaining bits [] output)
    afterCopy
    (some (unaryBertrandCfg (some .candidates) none [] remaining bits []
      (bits.reverse ++ false :: output)))
    (by simpa [Nat.add_comm] using hfirst)
    (by simpa [afterCopy] using hrestore)
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def unaryBertrand_cleanup_evals
    (current input remaining work output : List Bool)
    (state : UnaryBertrandState) :
    EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .cleanup) state input remaining current work
        output)
      (some (unaryBertrandCfg none none input remaining [] work output))
      (current.length + 1) := by
  induction current generalizing state with
  | nil =>
      simpa using unaryBertrandEvalsToInTimeOne
        (unaryBertrand_step_cleanup_nil input remaining work output state)
  | cons bit current ih =>
      let middle := unaryBertrandCfg (some .cleanup) (some bit) input remaining
        current work output
      have hone : EvalsToInTime unaryBertrandCandidateComputer.step
          (unaryBertrandCfg (some .cleanup) state input remaining
            (bit :: current) work output)
          (some middle) 1 :=
        unaryBertrandEvalsToInTimeOne (by
          simpa [middle] using unaryBertrand_step_cleanup_cons bit input
            remaining current work output state)
      have hrest := ih (some bit)
      have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
        1 (current.length + 1)
        (unaryBertrandCfg (some .cleanup) state input remaining
          (bit :: current) work output)
        middle
        (some (unaryBertrandCfg none none input remaining [] work output))
        hone
        (by simpa [middle] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private theorem unaryEncodeNat_eq_replicate_true (n : ℕ) :
    unaryEncodeNat n = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [unaryEncodeNat, List.replicate_succ, ih]

private theorem unaryEncodeNat_reverse_eq (n : ℕ) :
    (unaryEncodeNat n).reverse = unaryEncodeNat n := by
  rw [unaryEncodeNat_eq_replicate_true, List.reverse_replicate]

private theorem unaryBertrand_segment_append (n : ℕ)
    (output : List Bool) :
    (unaryEncodeNat n).reverse ++ false :: output =
      RawUnaryNatList.segment n ++ output := by
  simp [RawUnaryNatList.segment, unaryEncodeNat_eq_replicate_true,
    List.append_assoc]

private def encodedUnaryIntervalSuffix (count current : ℕ) : List Bool :=
  (intervalFrom count current).reverse.flatMap RawUnaryNatList.segment

private theorem encodedUnaryIntervalSuffix_succ (count current : ℕ) :
    encodedUnaryIntervalSuffix (count + 1) current =
      encodedUnaryIntervalSuffix count (current + 1) ++
        RawUnaryNatList.segment (current + 1) := by
  simp [encodedUnaryIntervalSuffix, intervalFrom, List.reverse_cons,
    List.flatMap_append]

private def unaryBertrandLoopTime : ℕ → ℕ → ℕ
  | 0, current => current + 2
  | count + 1, current =>
      1 + (2 * (current + 1) + 3) +
        unaryBertrandLoopTime count (current + 1)

private def unaryBertrand_candidates_evals
    (count current : ℕ) (output : List Bool)
    (state : UnaryBertrandState) :
    EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .candidates) state [] (unaryEncodeNat count)
        (unaryEncodeNat current) [] output)
      (some (unaryBertrandCfg none none [] [] [] []
        (encodedUnaryIntervalSuffix count current ++ output)))
      (unaryBertrandLoopTime count current) := by
  induction count generalizing current output state with
  | zero =>
      let afterCandidates := unaryBertrandCfg (some .cleanup) none [] []
        (unaryEncodeNat current) [] output
      have hcandidates : EvalsToInTime unaryBertrandCandidateComputer.step
          (unaryBertrandCfg (some .candidates) state [] []
            (unaryEncodeNat current) [] output)
          (some afterCandidates) 1 :=
        unaryBertrandEvalsToInTimeOne (by
          simpa [afterCandidates] using unaryBertrand_step_candidates_nil []
            (unaryEncodeNat current) [] output state)
      have hcleanup := unaryBertrand_cleanup_evals
        (unaryEncodeNat current) [] [] [] output none
      have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
        1 ((unaryEncodeNat current).length + 1)
        (unaryBertrandCfg (some .candidates) state [] []
          (unaryEncodeNat current) [] output)
        afterCandidates
        (some (unaryBertrandCfg none none [] [] [] [] output))
        hcandidates
        (by simpa [afterCandidates] using hcleanup)
      simpa [unaryBertrandLoopTime, encodedUnaryIntervalSuffix,
        unaryEncodeNat_length, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall
  | succ count ih =>
      let afterCandidates := unaryBertrandCfg (some .emitStart) (some true) []
        (unaryEncodeNat count) (unaryEncodeNat (current + 1)) [] output
      have hcandidates : EvalsToInTime unaryBertrandCandidateComputer.step
          (unaryBertrandCfg (some .candidates) state []
            (unaryEncodeNat (count + 1)) (unaryEncodeNat current) [] output)
          (some afterCandidates) 1 :=
        unaryBertrandEvalsToInTimeOne (by
          simpa [afterCandidates, unaryEncodeNat] using
            unaryBertrand_step_candidates_cons true []
              (unaryEncodeNat count) (unaryEncodeNat current) [] output state)
      have hemit := unaryBertrand_emit_evals
        (unaryEncodeNat (current + 1)) (unaryEncodeNat count) output
        (some true)
      let afterEmit := unaryBertrandCfg (some .candidates) none []
        (unaryEncodeNat count) (unaryEncodeNat (current + 1)) []
        (RawUnaryNatList.segment (current + 1) ++ output)
      have hfirst := EvalsToInTime.trans unaryBertrandCandidateComputer.step
        1 (2 * (unaryEncodeNat (current + 1)).length + 3)
        (unaryBertrandCfg (some .candidates) state []
          (unaryEncodeNat (count + 1)) (unaryEncodeNat current) [] output)
        afterCandidates
        (some afterEmit)
        hcandidates
        (by
          simpa [afterCandidates, afterEmit, unaryBertrand_segment_append]
            using hemit)
      have hrest := ih (current + 1)
        (RawUnaryNatList.segment (current + 1) ++ output) none
      have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
        (1 + (2 * (unaryEncodeNat (current + 1)).length + 3))
        (unaryBertrandLoopTime count (current + 1))
        (unaryBertrandCfg (some .candidates) state []
          (unaryEncodeNat (count + 1)) (unaryEncodeNat current) [] output)
        afterEmit
        (some (unaryBertrandCfg none none [] [] [] []
          (encodedUnaryIntervalSuffix (count + 1) current ++ output)))
        (by simpa [Nat.add_comm] using hfirst)
        (by
          rw [encodedUnaryIntervalSuffix_succ]
          simpa [afterEmit, List.append_assoc] using hrest)
      simpa [unaryBertrandLoopTime, unaryEncodeNat_length, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hall

private theorem unaryBertrandLoopTime_eq (count current : ℕ) :
    unaryBertrandLoopTime count current =
      2 * count * current + count ^ 2 + 6 * count + current + 2 := by
  induction count generalizing current with
  | zero => simp [unaryBertrandLoopTime]
  | succ count ih =>
      rw [unaryBertrandLoopTime, ih (current + 1)]
      ring

private def unaryBertrandTotalTime (q : ℕ) : ℕ :=
  (q + 1) + (2 * q + 3) + unaryBertrandLoopTime q q

private theorem unaryBertrandTotalTime_le (q : ℕ) :
    unaryBertrandTotalTime q ≤ 6 * (q + 1) ^ 2 := by
  rw [unaryBertrandTotalTime, unaryBertrandLoopTime_eq]
  nlinarith

private theorem rawUnaryNatList_encode_bertrandCandidates (q : ℕ) :
    RawUnaryNatList.encode (bertrandCandidates q) =
      encodedUnaryIntervalSuffix q q ++ RawUnaryNatList.segment q := by
  simp [RawUnaryNatList.encode, RawUnaryNatList.payloads,
    bertrandCandidates, encodedUnaryIntervalSuffix, List.reverse_cons,
    List.flatMap_append]

private theorem unaryBertrand_initList_eq_cfg (input : List Bool) :
    initList unaryBertrandCandidateComputer input =
      unaryBertrandCfg (some .count) none input [] [] [] [] := by
  unfold initList unaryBertrandCfg
  congr
  funext index
  cases index <;> rfl

private theorem unaryBertrand_haltList_eq_cfg (output : List Bool) :
    haltList unaryBertrandCandidateComputer output =
      unaryBertrandCfg none none [] [] [] [] output := by
  unfold haltList unaryBertrandCfg
  congr
  funext index
  cases index <;> rfl

/-- The unary-stream producer emits exactly `[q+1, ..., 2q]` in at most
`6(q+1)^2` steps, including the empty `q = 0` stream. -/
def unaryBertrandCandidate_outputsInTime (q : ℕ) :
    TM2OutputsInTime unaryBertrandCandidateComputer (unaryEncodeNat q)
      (some (RawUnaryNatList.encode (bertrandCandidates q)))
      (6 * (q + 1) ^ 2) := by
  have hcount := unaryBertrand_count_evals (unaryEncodeNat q) [] [] [] [] none
  let afterCount := unaryBertrandCfg (some .emitStart) none []
    (unaryEncodeNat q) (unaryEncodeNat q) [] []
  have hcount' : EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .count) none (unaryEncodeNat q) [] [] [] [])
      (some afterCount) (q + 1) := by
    simpa [afterCount, unaryEncodeNat_length, unaryEncodeNat_reverse_eq] using
      hcount
  have hemit := unaryBertrand_emit_evals (unaryEncodeNat q)
    (unaryEncodeNat q) [] none
  let afterEmit := unaryBertrandCfg (some .candidates) none []
    (unaryEncodeNat q) (unaryEncodeNat q) []
    (RawUnaryNatList.segment q)
  have hemit' : EvalsToInTime unaryBertrandCandidateComputer.step
      afterCount (some afterEmit) (2 * q + 3) := by
    simpa [afterCount, afterEmit, unaryEncodeNat_length,
      unaryBertrand_segment_append] using hemit
  have hfirst := EvalsToInTime.trans unaryBertrandCandidateComputer.step
    (q + 1) (2 * q + 3)
    (unaryBertrandCfg (some .count) none (unaryEncodeNat q) [] [] [] [])
    afterCount
    (some afterEmit)
    hcount' hemit'
  have hcandidates := unaryBertrand_candidates_evals q q
    (RawUnaryNatList.segment q) none
  have hall := EvalsToInTime.trans unaryBertrandCandidateComputer.step
    ((q + 1) + (2 * q + 3)) (unaryBertrandLoopTime q q)
    (unaryBertrandCfg (some .count) none (unaryEncodeNat q) [] [] [] [])
    afterEmit
    (some (unaryBertrandCfg none none [] [] [] []
      (RawUnaryNatList.encode (bertrandCandidates q))))
    (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst)
    (by
      rw [rawUnaryNatList_encode_bertrandCandidates]
      simpa [afterEmit] using hcandidates)
  have hmono : EvalsToInTime unaryBertrandCandidateComputer.step
      (unaryBertrandCfg (some .count) none (unaryEncodeNat q) [] [] [] [])
      (some (unaryBertrandCfg none none [] [] [] []
        (RawUnaryNatList.encode (bertrandCandidates q))))
      (6 * (q + 1) ^ 2) :=
    evalsToInTimeMono
      (by
        simpa [unaryBertrandTotalTime, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hall)
      (unaryBertrandTotalTime_le q)
  rw [TM2OutputsInTime, unaryBertrand_initList_eq_cfg]
  simp only [Option.map_some]
  rw [unaryBertrand_haltList_eq_cfg]
  exact hmono

/-- Genuine quadratic-time generation of the internal unary candidate stream
from the unary full-input bound. -/
noncomputable def unaryBertrandCandidatesComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ (List ℕ) unaryFinEncodingNat
      RawUnaryNatList.finEncoding bertrandCandidates where
  tm := unaryBertrandCandidateComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 6 * (Polynomial.X + 1) ^ 2
  outputsFun q := by
    simpa [unaryFinEncodingNat, RawUnaryNatList.finEncoding, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using
        unaryBertrandCandidate_outputsInTime q

/-- The complete unary candidate stream remains quadratic in the unary scan
bound. -/
theorem unaryBertrandCandidateStream_length_le (q : ℕ) :
    (RawUnaryNatList.encode (bertrandCandidates q)).length ≤
      2 * q ^ 2 + 2 * q + 1 := by
  have hsum := List.sum_le_card_nsmul (bertrandCandidates q) (2 * q) (by
    intro value hvalue
    exact (mem_bertrandCandidates_iff q value).mp hvalue |>.2)
  have hsum' : (bertrandCandidates q).sum ≤ 2 * q ^ 2 := by
    simpa [bertrandCandidates_length, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, pow_two] using hsum
  rw [RawUnaryNatList.encode_length, bertrandCandidates_length]
  nlinarith [hsum']

/-! ## Unary-padded divisibility

The eventual prime scan works under the full-input invariant `q ≤ s`, where
`s` is the bit length of the explicit CSP.  Consequently every candidate and
trial divisor is at most linear in `s`.  The following paired unary interface
records that padding explicitly.  It is deliberately not a polynomial-time
claim for standalone binary inputs.
-/

namespace UnaryNatPair

/-- Two unary naturals separated by a single false delimiter. -/
def encode (pair : ℕ × ℕ) : List Bool :=
  List.replicate pair.1 true ++ false :: List.replicate pair.2 true

/-- Decoder for the canonical delimiter-separated unary pair syntax. -/
def decodeAux : List Bool → ℕ × ℕ
  | [] => (0, 0)
  | false :: bits => (0, bits.length)
  | true :: bits =>
      let decoded := decodeAux bits
      (decoded.1 + 1, decoded.2)

def decode (input : List Bool) : Option (ℕ × ℕ) :=
  some (decodeAux input)

private theorem decodeAux_replicate (left right : ℕ) :
    decodeAux
        (List.replicate left true ++ false :: List.replicate right true) =
      (left, right) := by
  induction left with
  | zero => simp [decodeAux]
  | succ left ih =>
      simp [List.replicate_succ, decodeAux, ih]

@[simp]
theorem decode_encode (pair : ℕ × ℕ) :
    decode (encode pair) = some pair := by
  rcases pair with ⟨left, right⟩
  simp [decode, encode, decodeAux_replicate]

/-- Checked finite encoding of a unary-padded pair of naturals. -/
def finEncoding : FinEncoding (ℕ × ℕ) where
  Γ := Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := Bool.fintype

@[simp]
theorem encode_length (pair : ℕ × ℕ) :
    (encode pair).length = pair.1 + pair.2 + 1 := by
  simp [encode]
  omega

end UnaryNatPair

/-! ## Deterministic trial-division specification

The existing divisibility machine supplies the Boolean test needed for each
pair below.  This section fixes the exact finite computation that the next
machine pass must realize: test every divisor in `[2, n)`, retain exactly the
prime Bertrand candidates, and take the first survivor.  The specification is
executable, but no polynomial-time claim is made merely from these list
definitions.  The unary-pair and aggregate-size bounds expose the padding that
the finite-machine proof will use.
-/

/-- Every possible nontrivial proper divisor of `n`, in increasing order. -/
def trialDivisors (n : ℕ) : List ℕ :=
  List.range' 2 (n - 2)

@[simp]
theorem trialDivisors_length (n : ℕ) :
    (trialDivisors n).length = n - 2 := by
  simp [trialDivisors]

@[simp]
theorem mem_trialDivisors_iff (n d : ℕ) :
    d ∈ trialDivisors n ↔ 2 ≤ d ∧ d < n := by
  simp [trialDivisors]
  omega

/-- Bounded trial division as an executable Boolean predicate. -/
def trialPrime (n : ℕ) : Bool :=
  decide (2 ≤ n) &&
    (trialDivisors n).all fun d => decide (¬ d ∣ n)

/-- Testing all and only the divisors in `[2, n)` decides natural primality. -/
theorem trialPrime_eq_true_iff (n : ℕ) :
    trialPrime n = true ↔ n.Prime := by
  rw [Nat.prime_def_lt']
  simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  constructor
  · rintro ⟨hn, htrial⟩
    exact ⟨hn, fun d hd2 hdn =>
      htrial d ((mem_trialDivisors_iff n d).2 ⟨hd2, hdn⟩)⟩
  · rintro ⟨hn, hprime⟩
    exact ⟨hn, fun d hd => hprime d
      ((mem_trialDivisors_iff n d).1 hd).1
      ((mem_trialDivisors_iff n d).1 hd).2⟩

/-- The exact sequence of padded divisibility inputs used to test `n`. -/
def trialDivisionPairs (n : ℕ) : List (ℕ × ℕ) :=
  (trialDivisors n).map fun d => (n, d)

@[simp]
theorem trialDivisionPairs_length (n : ℕ) :
    (trialDivisionPairs n).length = n - 2 := by
  simp [trialDivisionPairs]

theorem mem_trialDivisionPairs_iff (n : ℕ) (pair : ℕ × ℕ) :
    pair ∈ trialDivisionPairs n ↔
      pair.1 = n ∧ 2 ≤ pair.2 ∧ pair.2 < n := by
  constructor
  · intro hp
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
    exact ⟨rfl, (mem_trialDivisors_iff n d).mp hd⟩
  · rintro ⟨hfirst, hd2, hdlt⟩
    exact List.mem_map.mpr ⟨pair.2,
      (mem_trialDivisors_iff n pair.2).mpr ⟨hd2, hdlt⟩,
      Prod.ext hfirst.symm rfl⟩

/-- Each trial pair has unary length at most twice its candidate. -/
theorem unaryPair_length_le_two_mul_of_mem_trialDivisionPairs
    {n : ℕ} {pair : ℕ × ℕ} (hp : pair ∈ trialDivisionPairs n) :
    (UnaryNatPair.encode pair).length ≤ 2 * n := by
  rw [UnaryNatPair.encode_length]
  have h := (mem_trialDivisionPairs_iff n pair).mp hp
  omega

/-- Total unary cells in the complete list of trial pairs for one candidate. -/
def trialDivisionInputSize (n : ℕ) : ℕ :=
  ((trialDivisionPairs n).map fun pair =>
    (UnaryNatPair.encode pair).length).sum

/-- The complete padded trial-division input for one candidate is quadratic. -/
theorem trialDivisionInputSize_le (n : ℕ) :
    trialDivisionInputSize n ≤ 2 * n * (n - 2) := by
  have hsum := List.sum_le_card_nsmul
    ((trialDivisionPairs n).map fun pair =>
      (UnaryNatPair.encode pair).length) (2 * n) (by
        intro length hlength
        obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hlength
        exact unaryPair_length_le_two_mul_of_mem_trialDivisionPairs hpair)
  simpa [trialDivisionInputSize, trialDivisionPairs_length,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

/-- The checked Bertrand interval after deterministic trial-division
filtering. -/
def bertrandPrimeCandidates (q : ℕ) : List ℕ :=
  (bertrandCandidates q).filter trialPrime

theorem pairwise_lt_intervalFrom (count current : ℕ) :
    (intervalFrom count current).Pairwise (· < ·) := by
  induction count generalizing current with
  | zero => simp [intervalFrom]
  | succ count ih =>
      rw [intervalFrom, List.pairwise_cons]
      constructor
      · intro value hvalue
        have hbounds :=
          (mem_intervalFrom_iff value count (current + 1)).mp hvalue
        omega
      · exact ih (current + 1)

theorem pairwise_lt_bertrandPrimeCandidates (q : ℕ) :
    (bertrandPrimeCandidates q).Pairwise (· < ·) := by
  exact (pairwise_lt_intervalFrom q q).filter trialPrime

@[simp]
theorem mem_bertrandPrimeCandidates_iff (q value : ℕ) :
    value ∈ bertrandPrimeCandidates q ↔
      value.Prime ∧ q < value ∧ value ≤ 2 * q := by
  rw [bertrandPrimeCandidates, List.mem_filter]
  rw [trialPrime_eq_true_iff, mem_bertrandCandidates_iff]
  tauto

theorem selectPrimeAbove_mem_bertrandPrimeCandidates
    {q : ℕ} (hq : q ≠ 0) :
    selectPrimeAbove q ∈ bertrandPrimeCandidates q := by
  rw [mem_bertrandPrimeCandidates_iff]
  exact (mem_primeCandidates_iff q (selectPrimeAbove q)).mp
    (selectPrimeAbove_mem_primeCandidates hq)

theorem bertrandPrimeCandidates_ne_nil {q : ℕ} (hq : q ≠ 0) :
    bertrandPrimeCandidates q ≠ [] := by
  intro hempty
  have hmem := selectPrimeAbove_mem_bertrandPrimeCandidates hq
  rw [hempty] at hmem
  simp at hmem

/-- Select the first candidate surviving bounded trial division, with the
same explicit `q = 0` convention as the semantic compiler. -/
def firstBertrandPrime (q : ℕ) : ℕ :=
  if hq : q = 0 then 2
  else (bertrandPrimeCandidates q).head (bertrandPrimeCandidates_ne_nil hq)

@[simp]
theorem firstBertrandPrime_zero : firstBertrandPrime 0 = 2 := by
  simp [firstBertrandPrime]

theorem firstBertrandPrime_mem {q : ℕ} (hq : q ≠ 0) :
    firstBertrandPrime q ∈ bertrandPrimeCandidates q := by
  rw [firstBertrandPrime, dif_neg hq]
  exact List.head_mem _

private theorem head_le_of_pairwise_lt {xs : List ℕ} (hne : xs ≠ [])
    (hsorted : xs.Pairwise (· < ·)) {value : ℕ} (hvalue : value ∈ xs) :
    xs.head hne ≤ value := by
  cases xs with
  | nil => simp at hne
  | cons first rest =>
      rw [List.pairwise_cons] at hsorted
      rcases List.mem_cons.mp hvalue with hfirst | hrest
      · subst value
        exact le_rfl
      · exact (hsorted.1 value hrest).le

/-- The executable first-survivor scan returns exactly the least prime used by
the already checked semantic compiler. -/
theorem firstBertrandPrime_eq_selectPrimeAbove (q : ℕ) :
    firstBertrandPrime q = selectPrimeAbove q := by
  by_cases hq : q = 0
  · subst q
    simp
  · apply Nat.le_antisymm
    · rw [firstBertrandPrime, dif_neg hq]
      exact head_le_of_pairwise_lt (bertrandPrimeCandidates_ne_nil hq)
        (pairwise_lt_bertrandPrimeCandidates q)
        (selectPrimeAbove_mem_bertrandPrimeCandidates hq)
    · rw [selectPrimeAbove, dif_neg hq]
      exact Finset.min'_le (primeCandidates q) (firstBertrandPrime q)
        ((mem_bertrandPrimeCandidates_iff q (firstBertrandPrime q)).mp
          (firstBertrandPrime_mem hq) |>
            (mem_primeCandidates_iff q (firstBertrandPrime q)).mpr)

theorem firstBertrandPrime_prime (q : ℕ) :
    (firstBertrandPrime q).Prime := by
  rw [firstBertrandPrime_eq_selectPrimeAbove]
  exact selectPrimeAbove_prime q

theorem lt_firstBertrandPrime (q : ℕ) :
    q < firstBertrandPrime q := by
  rw [firstBertrandPrime_eq_selectPrimeAbove]
  exact lt_selectPrimeAbove q

theorem firstBertrandPrime_le_two_mul {q : ℕ} (hq : q ≠ 0) :
    firstBertrandPrime q ≤ 2 * q := by
  rw [firstBertrandPrime_eq_selectPrimeAbove]
  exact selectPrimeAbove_le_two_mul hq

theorem firstBertrandPrime_lt_two_mul {q : ℕ} (hq : 1 < q) :
    firstBertrandPrime q < 2 * q := by
  rw [firstBertrandPrime_eq_selectPrimeAbove]
  exact selectPrimeAbove_lt_two_mul hq

@[simp]
theorem firstBertrandPrime_one : firstBertrandPrime 1 = 2 := by
  rw [firstBertrandPrime_eq_selectPrimeAbove]
  exact selectPrimeAbove_one

/-! ## Stack-oriented trial-pair lists

The finite prime filter feeds the existing divisibility checker one unary pair
at a time.  This encoding keeps every complete `UnaryNatPair` payload intact,
reverses both the list of pairs and each payload for stack consumption, and
separates payloads by a symbol outside the Boolean input alphabet.
-/

namespace RawUnaryPairList

/-- Stack-oriented encoding of a list of unary-padded natural pairs. -/
def encode (pairs : List (ℕ × ℕ)) : List (Option Bool) :=
  (pairs.map UnaryNatPair.encode).reverse.flatMap RawNatList.segment

private theorem parseAux_some_append
    (bits : List Bool) (input : List (Option Bool))
    (current : List Bool) (fields : List (List Bool)) :
    RawNatList.parseAux (bits.map some ++ input) current fields =
      RawNatList.parseAux input (bits.reverse ++ current) fields := by
  induction bits generalizing current with
  | nil => simp
  | cons bit bits ih =>
      simp [RawNatList.parseAux, ih, List.reverse_cons, List.append_assoc]

private theorem parseAux_segments
    (segments : List (List Bool)) (fields : List (List Bool)) :
    RawNatList.parseAux
        (segments.flatMap RawNatList.segment) [] fields =
      some (segments.reverse ++ fields) := by
  induction segments generalizing fields with
  | nil => simp [RawNatList.parseAux]
  | cons bits segments ih =>
      rw [List.flatMap_cons]
      simp only [RawNatList.segment, List.append_assoc]
      rw [parseAux_some_append]
      simp only [List.reverse_reverse]
      simp only [List.singleton_append, RawNatList.parseAux]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp]
theorem parse_encode (pairs : List (ℕ × ℕ)) :
    RawNatList.parse (encode pairs) =
      some (pairs.map UnaryNatPair.encode) := by
  rw [RawNatList.parse, encode, parseAux_segments]
  simp

/-- Decode every complete pair payload in a parsed field list. -/
def decodeFields : List (List Bool) → Option (List (ℕ × ℕ))
  | [] => some []
  | field :: fields => do
      let pair ← UnaryNatPair.decode field
      let pairs ← decodeFields fields
      some (pair :: pairs)

@[simp]
theorem decodeFields_map_encode (pairs : List (ℕ × ℕ)) :
    decodeFields (pairs.map UnaryNatPair.encode) = some pairs := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih => simp [decodeFields, ih]

/-- Decode a complete stack-oriented list of unary pairs. -/
def decode (input : List (Option Bool)) : Option (List (ℕ × ℕ)) := do
  let fields ← RawNatList.parse input
  decodeFields fields

@[simp]
theorem decode_encode (pairs : List (ℕ × ℕ)) :
    decode (encode pairs) = some pairs := by
  simp [decode]

/-- Checked finite encoding for a stack-oriented list of padded trial pairs. -/
def finEncoding : FinEncoding (List (ℕ × ℕ)) where
  Γ := Option Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

end RawUnaryPairList

/-- Input, the unary dividend, the unconsumed and consumed parts of the
divisor, and the Boolean output. -/
inductive DvdStack
  | input
  | dividend
  | remaining
  | used
  | output
  deriving DecidableEq, Fintype

/-- Parsing, cyclic divisor consumption, restoration, decision, and cleanup
phases of the unary divisibility checker. -/
inductive DvdLabel
  | scanDividend
  | scanDivisor
  | start
  | consume
  | restore
  | check
  | finish
  | clearDividend
  | clearRemaining
  | clearUsed
  deriving DecidableEq, Fintype

/-- Finite control stores the most recently observed marker and the decision
bit once it is known. -/
structure DvdState where
  marker : Option Bool
  result : Bool
  deriving DecidableEq, Fintype

private def dvdInitialState : DvdState :=
  ⟨none, false⟩

private def dvdObserved
    (state : DvdState) (marker : Option Bool) : DvdState :=
  { state with marker := marker }

private def dvdSetResult (result : Bool) (_state : DvdState) : DvdState :=
  ⟨none, result⟩

private def dvdMarkerPresent : DvdState → Bool
  | ⟨some _, _⟩ => true
  | _ => false

private def dvdMarkerTrue : DvdState → Bool
  | ⟨some true, _⟩ => true
  | _ => false

private def dvdResult (state : DvdState) : Bool :=
  state.result

private def DvdAlphabet (_index : DvdStack) : Type :=
  Bool

/-- A cyclic unary divisibility program.  For a positive divisor, the
`remaining` and `used` stacks partition one divisor-length cycle. -/
def unaryDvdProgram :
    DvdLabel → TM2.Stmt DvdAlphabet DvdLabel DvdState
  | .scanDividend =>
      .pop .input dvdObserved <|
        .branch dvdMarkerPresent
          (.branch dvdMarkerTrue
            (.push .dividend (fun _ => true) <|
              .goto (fun _ => .scanDividend))
            (.goto (fun _ => .scanDivisor)))
          (.goto (fun _ => .scanDivisor))
  | .scanDivisor =>
      .pop .input dvdObserved <|
        .branch dvdMarkerPresent
          (.push .remaining (fun _ => true) <|
            .goto (fun _ => .scanDivisor))
          (.goto (fun _ => .start))
  | .start =>
      .peek .dividend dvdObserved <|
        .branch dvdMarkerPresent
          (.peek .remaining dvdObserved <|
            .branch dvdMarkerPresent
              (.goto (fun _ => .consume))
              (.load (dvdSetResult false) <|
                .goto (fun _ => .finish)))
          (.load (dvdSetResult true) <|
            .goto (fun _ => .finish))
  | .consume =>
      .peek .dividend dvdObserved <|
        .branch dvdMarkerPresent
          (.peek .remaining dvdObserved <|
            .branch dvdMarkerPresent
              (.pop .dividend dvdObserved <|
                .pop .remaining dvdObserved <|
                  .push .used (fun _ => true) <|
                    .goto (fun _ => .consume))
              (.goto (fun _ => .restore)))
          (.goto (fun _ => .check))
  | .restore =>
      .pop .used dvdObserved <|
        .branch dvdMarkerPresent
          (.push .remaining (fun _ => true) <|
            .goto (fun _ => .restore))
          (.goto (fun _ => .consume))
  | .check =>
      .peek .remaining dvdObserved <|
        .branch dvdMarkerPresent
          (.load (dvdSetResult false) <|
            .goto (fun _ => .finish))
          (.load (dvdSetResult true) <|
            .goto (fun _ => .finish))
  | .finish =>
      .push .output dvdResult <|
        .goto (fun _ => .clearDividend)
  | .clearDividend =>
      .pop .dividend dvdObserved <|
        .branch dvdMarkerPresent
          (.goto (fun _ => .clearDividend))
          (.goto (fun _ => .clearRemaining))
  | .clearRemaining =>
      .pop .remaining dvdObserved <|
        .branch dvdMarkerPresent
          (.goto (fun _ => .clearRemaining))
          (.goto (fun _ => .clearUsed))
  | .clearUsed =>
      .pop .used dvdObserved <|
        .branch dvdMarkerPresent
          (.goto (fun _ => .clearUsed))
          (.load (fun _ => dvdInitialState) .halt)

/-- Concrete finite machine deciding divisibility on unary-padded inputs. -/
def unaryDvdComputer : FinTM2 where
  K := DvdStack
  k₀ := .input
  k₁ := .output
  Γ := DvdAlphabet
  Λ := DvdLabel
  main := .scanDividend
  σ := DvdState
  initialState := dvdInitialState
  Γk₀Fin := Bool.fintype
  m := unaryDvdProgram

private def dvdStackContents
    (input dividend remaining used output : List Bool) :
    (index : DvdStack) → List (DvdAlphabet index)
  | .input => input
  | .dividend => dividend
  | .remaining => remaining
  | .used => used
  | .output => output

private def dvdCfg (label : Option DvdLabel) (state : DvdState)
    (input dividend remaining used output : List Bool) :
    unaryDvdComputer.Cfg where
  l := label
  var := state
  stk := dvdStackContents input dividend remaining used output

private def dvdEvalsToInTimeOne
    {start finish : unaryDvdComputer.Cfg}
    (hstep : unaryDvdComputer.step start = some finish) :
    EvalsToInTime unaryDvdComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem dvd_step_scanDividend_true
    (input dividend remaining used output : List Bool)
    (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .scanDividend) state (true :: input)
          dividend remaining used output) =
      some (dvdCfg (some .scanDividend)
        (dvdObserved state (some true)) input (true :: dividend)
        remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    dvdMarkerTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem dvd_step_scanDividend_false
    (input dividend remaining used output : List Bool)
    (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .scanDividend) state (false :: input)
          dividend remaining used output) =
      some (dvdCfg (some .scanDivisor)
        (dvdObserved state (some false)) input dividend
        remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    dvdMarkerTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem dvd_step_scanDivisor_true
    (input dividend remaining used output : List Bool)
    (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .scanDivisor) state (true :: input)
          dividend remaining used output) =
      some (dvdCfg (some .scanDivisor)
        (dvdObserved state (some true)) input dividend
        (true :: remaining) used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    Function.update]
  funext index
  cases index <;> rfl

private theorem dvd_step_scanDivisor_nil
    (dividend remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .scanDivisor) state [] dividend remaining used output) =
      some (dvdCfg (some .start) (dvdObserved state none) []
        dividend remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    Function.update]

private theorem dvd_step_start_zero
    (remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .start) state [] [] remaining used output) =
      some (dvdCfg (some .finish) (dvdSetResult true state) [] []
        remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    dvdSetResult]

private theorem dvd_step_start_positive_zero
    (dividend : List Bool) (used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .start) state [] (true :: dividend) [] used output) =
      some (dvdCfg (some .finish) (dvdSetResult false state) []
        (true :: dividend) [] used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    dvdSetResult]

private theorem dvd_step_start_positive_positive
    (dividend remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .start) state [] (true :: dividend)
          (true :: remaining) used output) =
      some (dvdCfg (some .consume)
        (dvdObserved (dvdObserved state (some true)) (some true)) []
        (true :: dividend) (true :: remaining) used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]

private theorem dvd_step_consume_both
    (dividend remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .consume) state [] (true :: dividend)
          (true :: remaining) used output) =
      some (dvdCfg (some .consume)
        (dvdObserved (dvdObserved (dvdObserved
          (dvdObserved state (some true)) (some true)) (some true))
          (some true)) [] dividend remaining (true :: used) output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    Function.update]
  funext index
  cases index <;> rfl

private theorem dvd_step_consume_dividend_nil
    (remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .consume) state [] [] remaining used output) =
      some (dvdCfg (some .check) (dvdObserved state none) [] []
        remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]

private theorem dvd_step_consume_remaining_nil
    (dividend used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .consume) state [] (true :: dividend) [] used output) =
      some (dvdCfg (some .restore)
        (dvdObserved (dvdObserved state (some true)) none) []
        (true :: dividend) [] used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]

private theorem dvd_step_restore_cons
    (dividend remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .restore) state [] dividend remaining
          (true :: used) output) =
      some (dvdCfg (some .restore) (dvdObserved state (some true)) []
        dividend (true :: remaining) used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    Function.update]
  funext index
  cases index <;> rfl

private theorem dvd_step_restore_nil
    (dividend remaining output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .restore) state [] dividend remaining [] output) =
      some (dvdCfg (some .consume) (dvdObserved state none) []
        dividend remaining [] output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    Function.update]

private theorem dvd_step_check_cons
    (remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .check) state [] [] (true :: remaining) used output) =
      some (dvdCfg (some .finish) (dvdSetResult false state) [] []
        (true :: remaining) used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    dvdSetResult]

private theorem dvd_step_check_nil
    (used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .check) state [] [] [] used output) =
      some (dvdCfg (some .finish) (dvdSetResult true state) [] [] []
        used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    dvdSetResult]

private theorem dvd_step_finish
    (input dividend remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .finish) state input dividend remaining used output) =
      some (dvdCfg (some .clearDividend) state input dividend remaining used
        (state.result :: output)) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdResult]
  funext index
  cases index <;> rfl

private theorem dvd_step_clearDividend_cons
    (input dividend remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .clearDividend) state input (true :: dividend)
          remaining used output) =
      some (dvdCfg (some .clearDividend) (dvdObserved state (some true))
        input dividend remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]
  funext index
  cases index <;> rfl

private theorem dvd_step_clearDividend_nil
    (input remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .clearDividend) state input [] remaining used output) =
      some (dvdCfg (some .clearRemaining) (dvdObserved state none)
        input [] remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]

private theorem dvd_step_clearRemaining_cons
    (input remaining used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .clearRemaining) state input []
          (true :: remaining) used output) =
      some (dvdCfg (some .clearRemaining) (dvdObserved state (some true))
        input [] remaining used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]
  funext index
  cases index <;> rfl

private theorem dvd_step_clearRemaining_nil
    (input used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .clearRemaining) state input [] [] used output) =
      some (dvdCfg (some .clearUsed) (dvdObserved state none)
        input [] [] used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]

private theorem dvd_step_clearUsed_cons
    (input used output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .clearUsed) state input [] [] (true :: used) output) =
      some (dvdCfg (some .clearUsed) (dvdObserved state (some true))
        input [] [] used output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]
  funext index
  cases index <;> rfl

private theorem dvd_step_clearUsed_nil
    (output : List Bool) (state : DvdState) :
    unaryDvdComputer.step
        (dvdCfg (some .clearUsed) state [] [] [] [] output) =
      some (dvdCfg none dvdInitialState [] [] [] [] output) := by
  rcases state with ⟨marker, result⟩
  simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
    dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent,
    dvdInitialState]

private def dvd_scanDividend_evals
    (left : ℕ) (input dividend remaining used output : List Bool)
    (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .scanDividend) state
        (List.replicate left true ++ false :: input)
        dividend remaining used output)
      (some (dvdCfg (some .scanDivisor)
        (dvdObserved state (some false)) input
        (List.replicate left true ++ dividend) remaining used output))
      (left + 1) := by
  induction left generalizing state dividend with
  | zero =>
      simpa using dvdEvalsToInTimeOne
        (dvd_step_scanDividend_false input dividend remaining used output state)
  | succ left ih =>
      let nextState := dvdObserved state (some true)
      let middle := dvdCfg (some .scanDividend) nextState
        (List.replicate left true ++ false :: input)
        (true :: dividend) remaining used output
      have hone : EvalsToInTime unaryDvdComputer.step
          (dvdCfg (some .scanDividend) state
            (List.replicate (left + 1) true ++ false :: input)
            dividend remaining used output)
          (some middle) 1 :=
        dvdEvalsToInTimeOne (by
          simpa [middle, nextState, List.replicate_succ] using
            dvd_step_scanDividend_true
              (List.replicate left true ++ false :: input)
              dividend remaining used output state)
      have hrest := ih (true :: dividend) nextState
      have htrans := EvalsToInTime.trans unaryDvdComputer.step
        1 (left + 1)
        (dvdCfg (some .scanDividend) state
          (List.replicate (left + 1) true ++ false :: input)
          dividend remaining used output)
        middle
        (some (dvdCfg (some .scanDivisor)
          (dvdObserved state (some false)) input
          (List.replicate (left + 1) true ++ dividend)
          remaining used output))
        hone
        (by
          simpa [middle, nextState, dvdObserved, List.replicate_succ,
            replicate_true_append_cons]
            using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def dvd_scanDivisor_evals
    (right : ℕ) (dividend remaining used output : List Bool)
    (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .scanDivisor) state (List.replicate right true)
        dividend remaining used output)
      (some (dvdCfg (some .start) (dvdObserved state none) [] dividend
        (List.replicate right true ++ remaining) used output))
      (right + 1) := by
  induction right generalizing state remaining with
  | zero =>
      simpa using dvdEvalsToInTimeOne
        (dvd_step_scanDivisor_nil dividend remaining used output state)
  | succ right ih =>
      let nextState := dvdObserved state (some true)
      let middle := dvdCfg (some .scanDivisor) nextState
        (List.replicate right true) dividend (true :: remaining) used output
      have hone : EvalsToInTime unaryDvdComputer.step
          (dvdCfg (some .scanDivisor) state
            (List.replicate (right + 1) true)
            dividend remaining used output)
          (some middle) 1 :=
        dvdEvalsToInTimeOne (by
          simpa [middle, nextState, List.replicate_succ] using
            dvd_step_scanDivisor_true (List.replicate right true)
              dividend remaining used output state)
      have hrest := ih (true :: remaining) nextState
      have htrans := EvalsToInTime.trans unaryDvdComputer.step
        1 (right + 1)
        (dvdCfg (some .scanDivisor) state
          (List.replicate (right + 1) true)
          dividend remaining used output)
        middle
        (some (dvdCfg (some .start) (dvdObserved state none) [] dividend
          (List.replicate (right + 1) true ++ remaining) used output))
        hone
        (by
          simpa [middle, nextState, dvdObserved, List.replicate_succ,
            replicate_true_append_cons]
            using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def dvdAfterConsume (state : DvdState) : DvdState :=
  dvdObserved (dvdObserved (dvdObserved
    (dvdObserved state (some true)) (some true)) (some true)) (some true)

private def dvdConsumeState : DvdState → ℕ → DvdState
  | state, 0 => state
  | state, count + 1 => dvdConsumeState (dvdAfterConsume state) count

private def dvd_consume_prefix_evals
    (count : ℕ) (dividend remaining used output : List Bool)
    (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .consume) state []
        (List.replicate count true ++ dividend)
        (List.replicate count true ++ remaining) used output)
      (some (dvdCfg (some .consume) (dvdConsumeState state count) []
        dividend remaining (List.replicate count true ++ used) output))
      count := by
  induction count generalizing state used with
  | zero =>
      simpa [dvdConsumeState] using EvalsToInTime.refl
        unaryDvdComputer.step
        (dvdCfg (some .consume) state [] dividend remaining used output)
  | succ count ih =>
      let nextState := dvdAfterConsume state
      let middle := dvdCfg (some .consume) nextState []
        (List.replicate count true ++ dividend)
        (List.replicate count true ++ remaining) (true :: used) output
      have hone : EvalsToInTime unaryDvdComputer.step
          (dvdCfg (some .consume) state []
            (List.replicate (count + 1) true ++ dividend)
            (List.replicate (count + 1) true ++ remaining) used output)
          (some middle) 1 :=
        dvdEvalsToInTimeOne (by
          simpa [middle, nextState, dvdAfterConsume,
            List.replicate_succ] using
              dvd_step_consume_both
                (List.replicate count true ++ dividend)
                (List.replicate count true ++ remaining) used output state)
      have hrest := ih (true :: used) nextState
      have htrans := EvalsToInTime.trans unaryDvdComputer.step
        1 count
        (dvdCfg (some .consume) state []
          (List.replicate (count + 1) true ++ dividend)
          (List.replicate (count + 1) true ++ remaining) used output)
        middle
        (some (dvdCfg (some .consume)
          (dvdConsumeState state (count + 1)) [] dividend remaining
          (List.replicate (count + 1) true ++ used) output))
        hone
        (by
          simpa [middle, nextState, dvdConsumeState, dvdAfterConsume,
            List.replicate_succ, replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def dvdRestoreState : DvdState → ℕ → DvdState
  | state, 0 => dvdObserved state none
  | state, count + 1 => dvdRestoreState (dvdObserved state (some true)) count

private def dvd_restore_evals
    (count : ℕ) (dividend remaining output : List Bool)
    (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .restore) state [] dividend remaining
        (List.replicate count true) output)
      (some (dvdCfg (some .consume) (dvdRestoreState state count) []
        dividend (List.replicate count true ++ remaining) [] output))
      (count + 1) := by
  induction count generalizing state remaining with
  | zero =>
      simpa [dvdRestoreState] using dvdEvalsToInTimeOne
        (dvd_step_restore_nil dividend remaining output state)
  | succ count ih =>
      let nextState := dvdObserved state (some true)
      let middle := dvdCfg (some .restore) nextState [] dividend
        (true :: remaining) (List.replicate count true) output
      have hone : EvalsToInTime unaryDvdComputer.step
          (dvdCfg (some .restore) state [] dividend remaining
            (List.replicate (count + 1) true) output)
          (some middle) 1 :=
        dvdEvalsToInTimeOne (by
          simpa [middle, nextState, List.replicate_succ] using
            dvd_step_restore_cons dividend remaining
              (List.replicate count true) output state)
      have hrest := ih (true :: remaining) nextState
      have htrans := EvalsToInTime.trans unaryDvdComputer.step
        1 (count + 1)
        (dvdCfg (some .restore) state [] dividend remaining
          (List.replicate (count + 1) true) output)
        middle
        (some (dvdCfg (some .consume) (dvdRestoreState state (count + 1)) []
          dividend (List.replicate (count + 1) true ++ remaining) [] output))
        hone
        (by
          simpa [middle, nextState, dvdRestoreState, dvdObserved,
            List.replicate_succ, replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def dvd_clearUsed_evals
    (used output : List Bool) (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .clearUsed) state [] [] [] used output)
      (some (dvdCfg none dvdInitialState [] [] [] [] output))
      (used.length + 1) := by
  induction used generalizing state with
  | nil =>
      simpa using dvdEvalsToInTimeOne
        (dvd_step_clearUsed_nil output state)
  | cons marker used ih =>
      cases marker
      · simp only [List.length_cons]
        have hstep : unaryDvdComputer.step
            (dvdCfg (some .clearUsed) state [] [] [] (false :: used) output) =
          some (dvdCfg (some .clearUsed) (dvdObserved state (some false))
            [] [] [] used output) := by
          rcases state with ⟨held, result⟩
          simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
            dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]
          funext index
          cases index <;> rfl
        have hone := dvdEvalsToInTimeOne hstep
        have hrest := ih (dvdObserved state (some false))
        have htrans := EvalsToInTime.trans unaryDvdComputer.step
          1 (used.length + 1)
          (dvdCfg (some .clearUsed) state [] [] [] (false :: used) output)
          (dvdCfg (some .clearUsed) (dvdObserved state (some false))
            [] [] [] used output)
          (some (dvdCfg none dvdInitialState [] [] [] [] output))
          hone hrest
        omega
      · have hone := dvdEvalsToInTimeOne
          (dvd_step_clearUsed_cons [] used output state)
        have hrest := ih (dvdObserved state (some true))
        have htrans := EvalsToInTime.trans unaryDvdComputer.step
          1 (used.length + 1)
          (dvdCfg (some .clearUsed) state [] [] [] (true :: used) output)
          (dvdCfg (some .clearUsed) (dvdObserved state (some true))
            [] [] [] used output)
          (some (dvdCfg none dvdInitialState [] [] [] [] output))
          hone hrest
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def dvd_clearRemaining_evals
    (remaining used output : List Bool) (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .clearRemaining) state [] [] remaining used output)
      (some (dvdCfg none dvdInitialState [] [] [] [] output))
      (remaining.length + used.length + 2) := by
  induction remaining generalizing state with
  | nil =>
      have hone := dvdEvalsToInTimeOne
        (dvd_step_clearRemaining_nil [] used output state)
      have hrest := dvd_clearUsed_evals used output (dvdObserved state none)
      have htrans := EvalsToInTime.trans unaryDvdComputer.step
        1 (used.length + 1)
        (dvdCfg (some .clearRemaining) state [] [] [] used output)
        (dvdCfg (some .clearUsed) (dvdObserved state none) [] [] [] used output)
        (some (dvdCfg none dvdInitialState [] [] [] [] output))
        hone hrest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans
  | cons marker remaining ih =>
      cases marker
      · have hstep : unaryDvdComputer.step
            (dvdCfg (some .clearRemaining) state [] []
              (false :: remaining) used output) =
          some (dvdCfg (some .clearRemaining)
            (dvdObserved state (some false)) [] [] remaining used output) := by
          rcases state with ⟨held, result⟩
          simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
            dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]
          funext index
          cases index <;> rfl
        have hone := dvdEvalsToInTimeOne hstep
        have hrest := ih (dvdObserved state (some false))
        have htrans := EvalsToInTime.trans unaryDvdComputer.step
          1 (remaining.length + used.length + 2)
          (dvdCfg (some .clearRemaining) state [] []
            (false :: remaining) used output)
          (dvdCfg (some .clearRemaining) (dvdObserved state (some false))
            [] [] remaining used output)
          (some (dvdCfg none dvdInitialState [] [] [] [] output))
          hone hrest
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans
      · have hone := dvdEvalsToInTimeOne
          (dvd_step_clearRemaining_cons [] remaining used output state)
        have hrest := ih (dvdObserved state (some true))
        have htrans := EvalsToInTime.trans unaryDvdComputer.step
          1 (remaining.length + used.length + 2)
          (dvdCfg (some .clearRemaining) state [] []
            (true :: remaining) used output)
          (dvdCfg (some .clearRemaining) (dvdObserved state (some true))
            [] [] remaining used output)
          (some (dvdCfg none dvdInitialState [] [] [] [] output))
          hone hrest
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def dvd_clearDividend_evals
    (dividend remaining used output : List Bool) (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .clearDividend) state [] dividend remaining used output)
      (some (dvdCfg none dvdInitialState [] [] [] [] output))
      (dividend.length + remaining.length + used.length + 3) := by
  induction dividend generalizing state with
  | nil =>
      have hone := dvdEvalsToInTimeOne
        (dvd_step_clearDividend_nil [] remaining used output state)
      have hrest := dvd_clearRemaining_evals remaining used output
        (dvdObserved state none)
      have htrans := EvalsToInTime.trans unaryDvdComputer.step
        1 (remaining.length + used.length + 2)
        (dvdCfg (some .clearDividend) state [] [] remaining used output)
        (dvdCfg (some .clearRemaining) (dvdObserved state none)
          [] [] remaining used output)
        (some (dvdCfg none dvdInitialState [] [] [] [] output))
        hone hrest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans
  | cons marker dividend ih =>
      cases marker
      · have hstep : unaryDvdComputer.step
            (dvdCfg (some .clearDividend) state [] (false :: dividend)
              remaining used output) =
          some (dvdCfg (some .clearDividend)
            (dvdObserved state (some false)) [] dividend remaining used output) := by
          rcases state with ⟨held, result⟩
          simp [unaryDvdComputer, FinTM2.step, dvdCfg, unaryDvdProgram,
            dvdStackContents, DvdAlphabet, dvdObserved, dvdMarkerPresent]
          funext index
          cases index <;> rfl
        have hone := dvdEvalsToInTimeOne hstep
        have hrest := ih (dvdObserved state (some false))
        have htrans := EvalsToInTime.trans unaryDvdComputer.step
          1 (dividend.length + remaining.length + used.length + 3)
          (dvdCfg (some .clearDividend) state [] (false :: dividend)
            remaining used output)
          (dvdCfg (some .clearDividend) (dvdObserved state (some false))
            [] dividend remaining used output)
          (some (dvdCfg none dvdInitialState [] [] [] [] output))
          hone hrest
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans
      · have hone := dvdEvalsToInTimeOne
          (dvd_step_clearDividend_cons [] dividend remaining used output state)
        have hrest := ih (dvdObserved state (some true))
        have htrans := EvalsToInTime.trans unaryDvdComputer.step
          1 (dividend.length + remaining.length + used.length + 3)
          (dvdCfg (some .clearDividend) state [] (true :: dividend)
            remaining used output)
          (dvdCfg (some .clearDividend) (dvdObserved state (some true))
            [] dividend remaining used output)
          (some (dvdCfg none dvdInitialState [] [] [] [] output))
          hone hrest
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def dvd_finish_evals
    (dividend remaining used output : List Bool) (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .finish) state [] dividend remaining used output)
      (some (dvdCfg none dvdInitialState [] [] [] []
        (state.result :: output)))
      (dividend.length + remaining.length + used.length + 4) := by
  have hone := dvdEvalsToInTimeOne
    (dvd_step_finish [] dividend remaining used output state)
  have hrest := dvd_clearDividend_evals dividend remaining used
    (state.result :: output) state
  have htrans := EvalsToInTime.trans unaryDvdComputer.step
    1 (dividend.length + remaining.length + used.length + 3)
    (dvdCfg (some .finish) state [] dividend remaining used output)
    (dvdCfg (some .clearDividend) state [] dividend remaining used
      (state.result :: output))
    (some (dvdCfg none dvdInitialState [] [] [] []
      (state.result :: output)))
    hone hrest
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private noncomputable def dvd_consume_evals
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (output : List Bool) (state : DvdState) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .consume) state []
        (List.replicate n true) (List.replicate d true) [] output)
      (some (dvdCfg none dvdInitialState [] [] [] []
        (decide (d ∣ n) :: output)))
      (4 * n + d + 8) := by
  induction n using Nat.strongRecOn generalizing state with
  | ind n ih =>
      by_cases hle : n ≤ d
      · have hsplit :
            List.replicate d true =
              List.replicate n true ++ List.replicate (d - n) true := by
          calc
            List.replicate d true =
                List.replicate (n + (d - n)) true := by
              rw [Nat.add_sub_of_le hle]
            _ = List.replicate n true ++
                List.replicate (d - n) true :=
              List.replicate_add n (d - n) true
        have hprefix := dvd_consume_prefix_evals n []
          (List.replicate (d - n) true) [] output state
        have hprefix' : EvalsToInTime unaryDvdComputer.step
            (dvdCfg (some .consume) state []
              (List.replicate n true) (List.replicate d true) [] output)
            (some (dvdCfg (some .consume) (dvdConsumeState state n) [] []
              (List.replicate (d - n) true)
              (List.replicate n true) output)) n := by
          simpa only [List.append_nil, ← hsplit] using hprefix
        have hempty := dvdEvalsToInTimeOne
          (dvd_step_consume_dividend_nil
            (List.replicate (d - n) true) (List.replicate n true)
            output (dvdConsumeState state n))
        have htoCheck := EvalsToInTime.trans unaryDvdComputer.step
          n 1
          (dvdCfg (some .consume) state []
            (List.replicate n true) (List.replicate d true) [] output)
          (dvdCfg (some .consume) (dvdConsumeState state n) [] []
            (List.replicate (d - n) true)
            (List.replicate n true) output)
          (some (dvdCfg (some .check)
            (dvdObserved (dvdConsumeState state n) none) [] []
            (List.replicate (d - n) true)
            (List.replicate n true) output))
          hprefix' hempty
        by_cases heq : n = d
        · subst d
          have hcheck := dvdEvalsToInTimeOne
            (dvd_step_check_nil (List.replicate n true) output
              (dvdObserved (dvdConsumeState state n) none))
          have hfinish := dvd_finish_evals [] []
            (List.replicate n true) output
            (dvdSetResult true
              (dvdObserved (dvdConsumeState state n) none))
          have hthroughCheck := EvalsToInTime.trans unaryDvdComputer.step
            (1 + n) 1
            (dvdCfg (some .consume) state []
              (List.replicate n true) (List.replicate n true) [] output)
            (dvdCfg (some .check)
              (dvdObserved (dvdConsumeState state n) none) [] [] []
              (List.replicate n true) output)
            (some (dvdCfg (some .finish)
              (dvdSetResult true
                (dvdObserved (dvdConsumeState state n) none))
              [] [] [] (List.replicate n true) output))
            (by simpa using htoCheck)
            hcheck
          have hall := EvalsToInTime.trans unaryDvdComputer.step
            (1 + (1 + n)) (n + 4)
            (dvdCfg (some .consume) state []
              (List.replicate n true) (List.replicate n true) [] output)
            (dvdCfg (some .finish)
              (dvdSetResult true
                (dvdObserved (dvdConsumeState state n) none))
              [] [] [] (List.replicate n true) output)
            (some (dvdCfg none dvdInitialState [] [] [] []
              (decide (n ∣ n) :: output)))
            hthroughCheck
            (by simpa [dvdSetResult] using hfinish)
          exact evalsToInTimeMono hall (by omega)
        · have hlt : n < d := lt_of_le_of_ne hle heq
          have hsubpos : 0 < d - n := Nat.sub_pos_of_lt hlt
          let rest := (d - n).pred
          have hrest : d - n = rest + 1 := by
            exact (Nat.succ_pred_eq_of_pos hsubpos).symm
          have hcheck := dvdEvalsToInTimeOne
            (dvd_step_check_cons (List.replicate rest true)
              (List.replicate n true) output
              (dvdObserved (dvdConsumeState state n) none))
          have hfinish := dvd_finish_evals []
            (List.replicate (d - n) true)
            (List.replicate n true) output
            (dvdSetResult false
              (dvdObserved (dvdConsumeState state n) none))
          have hnot : ¬d ∣ n :=
            Nat.not_dvd_of_pos_of_lt hn hlt
          have hthroughCheck := EvalsToInTime.trans unaryDvdComputer.step
            (1 + n) 1
            (dvdCfg (some .consume) state []
              (List.replicate n true) (List.replicate d true) [] output)
            (dvdCfg (some .check)
              (dvdObserved (dvdConsumeState state n) none) [] []
              (List.replicate (d - n) true)
              (List.replicate n true) output)
            (some (dvdCfg (some .finish)
              (dvdSetResult false
                (dvdObserved (dvdConsumeState state n) none))
              [] [] (List.replicate (d - n) true)
              (List.replicate n true) output))
            htoCheck
            (by simpa [hrest, List.replicate_succ] using hcheck)
          have hall := EvalsToInTime.trans unaryDvdComputer.step
            (1 + (1 + n)) ((d - n) + n + 4)
            (dvdCfg (some .consume) state []
              (List.replicate n true) (List.replicate d true) [] output)
            (dvdCfg (some .finish)
              (dvdSetResult false
                (dvdObserved (dvdConsumeState state n) none))
              [] [] (List.replicate (d - n) true)
              (List.replicate n true) output)
            (some (dvdCfg none dvdInitialState [] [] [] []
              (decide (d ∣ n) :: output)))
            hthroughCheck
            (by simpa [dvdSetResult, hnot] using hfinish)
          exact evalsToInTimeMono hall (by omega)
      · have hlt : d < n := lt_of_not_ge hle
        have hdle : d ≤ n := Nat.le_of_lt hlt
        have hsplit :
            List.replicate n true =
              List.replicate d true ++ List.replicate (n - d) true := by
          calc
            List.replicate n true =
                List.replicate (d + (n - d)) true := by
              rw [Nat.add_sub_of_le hdle]
            _ = List.replicate d true ++
                List.replicate (n - d) true :=
              List.replicate_add d (n - d) true
        have hprefix := dvd_consume_prefix_evals d
          (List.replicate (n - d) true) [] [] output state
        have hprefix' : EvalsToInTime unaryDvdComputer.step
            (dvdCfg (some .consume) state []
              (List.replicate n true) (List.replicate d true) [] output)
            (some (dvdCfg (some .consume) (dvdConsumeState state d) []
              (List.replicate (n - d) true) []
              (List.replicate d true) output)) d := by
          simpa only [List.append_nil, ← hsplit] using hprefix
        have hsubpos : 0 < n - d := Nat.sub_pos_of_lt hlt
        let tail := (n - d).pred
        have htail : n - d = tail + 1 := by
          exact (Nat.succ_pred_eq_of_pos hsubpos).symm
        have hboundary := dvdEvalsToInTimeOne
          (dvd_step_consume_remaining_nil (List.replicate tail true)
            (List.replicate d true) output (dvdConsumeState state d))
        have htoRestore := EvalsToInTime.trans unaryDvdComputer.step
          d 1
          (dvdCfg (some .consume) state []
            (List.replicate n true) (List.replicate d true) [] output)
          (dvdCfg (some .consume) (dvdConsumeState state d) []
            (List.replicate (n - d) true) []
            (List.replicate d true) output)
          (some (dvdCfg (some .restore)
            (dvdObserved (dvdObserved (dvdConsumeState state d) (some true)) none)
            [] (List.replicate (n - d) true) []
            (List.replicate d true) output))
          hprefix'
          (by simpa [htail, List.replicate_succ] using hboundary)
        have hrestore := dvd_restore_evals d
          (List.replicate (n - d) true) [] output
          (dvdObserved (dvdObserved (dvdConsumeState state d) (some true)) none)
        have hrestore' : EvalsToInTime unaryDvdComputer.step
            (dvdCfg (some .restore)
              (dvdObserved
                (dvdObserved (dvdConsumeState state d) (some true)) none)
              [] (List.replicate (n - d) true) []
              (List.replicate d true) output)
            (some (dvdCfg (some .consume)
              (dvdRestoreState
                (dvdObserved
                  (dvdObserved (dvdConsumeState state d) (some true)) none) d)
              [] (List.replicate (n - d) true)
              (List.replicate d true) [] output)) (d + 1) := by
          simpa only [List.append_nil] using hrestore
        have hcycle := EvalsToInTime.trans unaryDvdComputer.step
          (1 + d) (d + 1)
          (dvdCfg (some .consume) state []
            (List.replicate n true) (List.replicate d true) [] output)
          (dvdCfg (some .restore)
            (dvdObserved (dvdObserved (dvdConsumeState state d) (some true)) none)
            [] (List.replicate (n - d) true) []
            (List.replicate d true) output)
          (some (dvdCfg (some .consume)
            (dvdRestoreState
              (dvdObserved
                (dvdObserved (dvdConsumeState state d) (some true)) none) d)
            [] (List.replicate (n - d) true)
            (List.replicate d true) [] output))
          (by simpa [Nat.add_comm] using htoRestore)
          hrestore'
        have hrec := ih (n - d) (Nat.sub_lt hn hd)
          hsubpos
          (dvdRestoreState
            (dvdObserved
              (dvdObserved (dvdConsumeState state d) (some true)) none) d)
        have hdvd : d ∣ n - d ↔ d ∣ n :=
          Nat.dvd_sub_iff_left hdle (Nat.dvd_refl d)
        have hall := EvalsToInTime.trans unaryDvdComputer.step
          ((d + 1) + (1 + d)) (4 * (n - d) + d + 8)
          (dvdCfg (some .consume) state []
            (List.replicate n true) (List.replicate d true) [] output)
          (dvdCfg (some .consume)
            (dvdRestoreState
              (dvdObserved
                (dvdObserved (dvdConsumeState state d) (some true)) none) d)
            [] (List.replicate (n - d) true)
            (List.replicate d true) [] output)
          (some (dvdCfg none dvdInitialState [] [] [] []
            (decide (d ∣ n) :: output)))
          hcycle
          (by simpa only [hdvd] using hrec)
        exact evalsToInTimeMono hall (by omega)

private def dvd_parse_evals (n d : ℕ) (output : List Bool) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .scanDividend) dvdInitialState
        (UnaryNatPair.encode (n, d)) [] [] [] output)
      (some (dvdCfg (some .start)
        (dvdObserved (dvdObserved dvdInitialState (some false)) none)
        [] (List.replicate n true) (List.replicate d true) [] output))
      (n + d + 2) := by
  have hleft := dvd_scanDividend_evals n
    (List.replicate d true) [] [] [] output dvdInitialState
  have hright := dvd_scanDivisor_evals d
    (List.replicate n true) [] [] output
    (dvdObserved dvdInitialState (some false))
  have hall := EvalsToInTime.trans unaryDvdComputer.step
    (n + 1) (d + 1)
    (dvdCfg (some .scanDividend) dvdInitialState
      (UnaryNatPair.encode (n, d)) [] [] [] output)
    (dvdCfg (some .scanDivisor)
      (dvdObserved dvdInitialState (some false))
      (List.replicate d true) (List.replicate n true) [] [] output)
    (some (dvdCfg (some .start)
      (dvdObserved (dvdObserved dvdInitialState (some false)) none)
      [] (List.replicate n true) (List.replicate d true) [] output))
    (by simpa [UnaryNatPair.encode] using hleft)
    (by simpa using hright)
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private theorem dvd_initList_eq_cfg (input : List Bool) :
    initList unaryDvdComputer input =
      dvdCfg (some .scanDividend) dvdInitialState input [] [] [] [] := by
  unfold initList dvdCfg
  congr
  funext index
  cases index <;> rfl

private theorem dvd_haltList_eq_cfg (output : List Bool) :
    haltList unaryDvdComputer output =
      dvdCfg none dvdInitialState [] [] [] [] output := by
  unfold haltList dvdCfg
  congr
  funext index
  cases index <;> rfl

private noncomputable def unaryDvd_evals_with_output
    (pair : ℕ × ℕ) (output : List Bool) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .scanDividend) dvdInitialState
        (UnaryNatPair.encode pair) [] [] [] output)
      (some (dvdCfg none dvdInitialState [] [] [] []
        (decide (pair.2 ∣ pair.1) :: output)))
      (6 * (UnaryNatPair.encode pair).length + 16) := by
  rcases pair with ⟨n, d⟩
  have hparse := dvd_parse_evals n d output
  cases n with
  | zero =>
      let parsedState :=
        dvdObserved (dvdObserved dvdInitialState (some false)) none
      have hstart := dvdEvalsToInTimeOne
        (dvd_step_start_zero (List.replicate d true) [] output parsedState)
      have hfinish := dvd_finish_evals [] (List.replicate d true) [] output
        (dvdSetResult true parsedState)
      have hthroughStart := EvalsToInTime.trans unaryDvdComputer.step
        (d + 2) 1
        (dvdCfg (some .scanDividend) dvdInitialState
          (UnaryNatPair.encode (0, d)) [] [] [] output)
        (dvdCfg (some .start) parsedState [] []
          (List.replicate d true) [] output)
        (some (dvdCfg (some .finish) (dvdSetResult true parsedState)
          [] [] (List.replicate d true) [] output))
        (by simpa [parsedState] using hparse)
        hstart
      have hall := EvalsToInTime.trans unaryDvdComputer.step
        (1 + (d + 2)) (d + 4)
        (dvdCfg (some .scanDividend) dvdInitialState
          (UnaryNatPair.encode (0, d)) [] [] [] output)
        (dvdCfg (some .finish) (dvdSetResult true parsedState)
          [] [] (List.replicate d true) [] output)
        (some (dvdCfg none dvdInitialState [] [] [] []
          (decide (d ∣ 0) :: output)))
        hthroughStart
        (by simpa [dvdSetResult] using hfinish)
      have hbound :
          (d + 4) + (1 + (d + 2)) ≤
            6 * (UnaryNatPair.encode (0, d)).length + 16 := by
        simp [UnaryNatPair.encode]
        omega
      exact evalsToInTimeMono hall hbound
  | succ n =>
      cases d with
      | zero =>
          let parsedState :=
            dvdObserved (dvdObserved dvdInitialState (some false)) none
          have hstart := dvdEvalsToInTimeOne
            (dvd_step_start_positive_zero (List.replicate n true) []
              output parsedState)
          have hfinish := dvd_finish_evals
            (List.replicate (n + 1) true) [] [] output
            (dvdSetResult false parsedState)
          have hthroughStart := EvalsToInTime.trans unaryDvdComputer.step
            (n + 1 + 0 + 2) 1
            (dvdCfg (some .scanDividend) dvdInitialState
              (UnaryNatPair.encode (n + 1, 0)) [] [] [] output)
            (dvdCfg (some .start) parsedState []
              (List.replicate (n + 1) true) [] [] output)
            (some (dvdCfg (some .finish) (dvdSetResult false parsedState)
              [] (List.replicate (n + 1) true) [] [] output))
            (by simpa [parsedState] using hparse)
            (by simpa [List.replicate_succ] using hstart)
          have hall := EvalsToInTime.trans unaryDvdComputer.step
            (1 + (n + 1 + 0 + 2)) (n + 1 + 4)
            (dvdCfg (some .scanDividend) dvdInitialState
              (UnaryNatPair.encode (n + 1, 0)) [] [] [] output)
            (dvdCfg (some .finish) (dvdSetResult false parsedState)
              [] (List.replicate (n + 1) true) [] [] output)
            (some (dvdCfg none dvdInitialState [] [] [] []
              (decide (0 ∣ n + 1) :: output)))
            hthroughStart
            (by simpa [dvdSetResult] using hfinish)
          have hbound :
              (n + 1 + 4) + (1 + (n + 1 + 0 + 2)) ≤
                6 * (UnaryNatPair.encode (n + 1, 0)).length + 16 := by
            simp [UnaryNatPair.encode]
            omega
          exact evalsToInTimeMono hall hbound
      | succ d =>
          let parsedState :=
            dvdObserved (dvdObserved dvdInitialState (some false)) none
          let consumeState :=
            dvdObserved (dvdObserved parsedState (some true)) (some true)
          have hstart := dvdEvalsToInTimeOne
            (dvd_step_start_positive_positive
              (List.replicate n true) (List.replicate d true) [] output
              parsedState)
          have hconsume := dvd_consume_evals (n + 1) (d + 1)
            (Nat.succ_pos n) (Nat.succ_pos d) output consumeState
          have hthroughStart := EvalsToInTime.trans unaryDvdComputer.step
            (n + 1 + (d + 1) + 2) 1
            (dvdCfg (some .scanDividend) dvdInitialState
              (UnaryNatPair.encode (n + 1, d + 1)) [] [] [] output)
            (dvdCfg (some .start) parsedState []
              (List.replicate (n + 1) true)
              (List.replicate (d + 1) true) [] output)
            (some (dvdCfg (some .consume) consumeState []
              (List.replicate (n + 1) true)
              (List.replicate (d + 1) true) [] output))
            (by simpa [parsedState] using hparse)
            (by simpa [consumeState, List.replicate_succ] using hstart)
          have hall := EvalsToInTime.trans unaryDvdComputer.step
            (1 + (n + 1 + (d + 1) + 2))
            (4 * (n + 1) + (d + 1) + 8)
            (dvdCfg (some .scanDividend) dvdInitialState
              (UnaryNatPair.encode (n + 1, d + 1)) [] [] [] output)
            (dvdCfg (some .consume) consumeState []
              (List.replicate (n + 1) true)
              (List.replicate (d + 1) true) [] output)
            (some (dvdCfg none dvdInitialState [] [] [] []
              (decide (d + 1 ∣ n + 1) :: output)))
            hthroughStart
            (by simpa using hconsume)
          have hbound :
              (4 * (n + 1) + (d + 1) + 8) +
                  (1 + (n + 1 + (d + 1) + 2)) ≤
                6 * (UnaryNatPair.encode (n + 1, d + 1)).length + 16 := by
            simp [UnaryNatPair.encode]
            omega
          exact evalsToInTimeMono hall hbound

/-- The unary-padded checker decides natural-number divisibility in at most
`6s + 16` steps, where `s = n + d + 1` is its actual encoded input length. -/
noncomputable def unaryDvd_outputsInTime (pair : ℕ × ℕ) :
    TM2OutputsInTime unaryDvdComputer (UnaryNatPair.encode pair)
      (some (encodeBool (decide (pair.2 ∣ pair.1))))
      (6 * (UnaryNatPair.encode pair).length + 16) := by
  have hrun := unaryDvd_evals_with_output pair []
  rw [TM2OutputsInTime, dvd_initList_eq_cfg]
  simp only [Option.map_some, encodeBool, List.pure_def]
  rw [dvd_haltList_eq_cfg]
  simpa using hrun

/-- Genuine polynomial-time divisibility on the unary-padded interface used
by the future bounded prime scan. -/
noncomputable def unaryDvdComputableInPolyTime :
    @TM2ComputableInPolyTime (ℕ × ℕ) Bool UnaryNatPair.finEncoding
      finEncodingBoolBool (fun pair => decide (pair.2 ∣ pair.1)) where
  tm := unaryDvdComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 6 * Polynomial.X + 16
  outputsFun pair := by
    simpa [UnaryNatPair.finEncoding, finEncodingBoolBool, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_X] using unaryDvd_outputsInTime pair

/-! ## Finite-machine generation of padded trial pairs

The next machine consumes unary `n` and emits, in stack order, exactly the
inputs `(n, 2), ..., (n, n - 1)` required by bounded trial division.  Its
quadratic output is polynomial in this deliberately padded input interface.
-/

/-- Input, a preserved dividend, remaining divisor iterations, the current
divisor, copy work storage, and the raw pair-list output. -/
inductive TrialPairStack
  | input
  | dividend
  | remaining
  | divisor
  | work
  | output
  deriving DecidableEq, Fintype

/-- Counting, initial trimming, pair emission, iteration, and cleanup phases. -/
inductive TrialPairLabel
  | scan
  | trimFirst
  | trimSecond
  | loop
  | emitStart
  | copyDividend
  | restoreDividend
  | copyDivisor
  | restoreDivisor
  | cleanupDivisor
  | cleanupDividend
  deriving DecidableEq, Fintype

/-- Finite control holds the most recently popped Boolean symbol. -/
structure TrialPairState where
  marker : Option Bool
  deriving DecidableEq, Fintype

private def trialPairInitialState : TrialPairState :=
  ⟨none⟩

private def trialPairObserved
    (_state : TrialPairState) (marker : Option Bool) : TrialPairState :=
  ⟨marker⟩

private def trialPairMarkerPresent : TrialPairState → Bool
  | ⟨some _⟩ => true
  | _ => false

private def trialPairHeldBit : TrialPairState → Bool
  | ⟨some bit⟩ => bit
  | _ => false

private def trialPairHeldRawBit : TrialPairState → Option Bool
  | ⟨some bit⟩ => some bit
  | _ => none

private def TrialPairAlphabet : TrialPairStack → Type
  | .input => Bool
  | .dividend => Bool
  | .remaining => Bool
  | .divisor => Bool
  | .work => Bool
  | .output => Option Bool

/-- Generate every padded pair `(n,d)` for `2 ≤ d < n`. -/
def trialDivisionPairProgram :
    TrialPairLabel →
      TM2.Stmt TrialPairAlphabet TrialPairLabel TrialPairState
  | .scan =>
      .pop .input trialPairObserved <|
        .branch trialPairMarkerPresent
          (.push .dividend trialPairHeldBit <|
            .push .remaining trialPairHeldBit <|
              .goto (fun _ => .scan))
          (.goto (fun _ => .trimFirst))
  | .trimFirst =>
      .pop .remaining trialPairObserved <|
        .branch trialPairMarkerPresent
          (.goto (fun _ => .trimSecond))
          (.goto (fun _ => .cleanupDivisor))
  | .trimSecond =>
      .pop .remaining trialPairObserved <|
        .branch trialPairMarkerPresent
          (.push .divisor (fun _ => true) <|
            .push .divisor (fun _ => true) <|
              .goto (fun _ => .loop))
          (.goto (fun _ => .cleanupDivisor))
  | .loop =>
      .pop .remaining trialPairObserved <|
        .branch trialPairMarkerPresent
          (.goto (fun _ => .emitStart))
          (.goto (fun _ => .cleanupDivisor))
  | .emitStart =>
      .push .output (fun _ => none) <|
        .goto (fun _ => .copyDividend)
  | .copyDividend =>
      .pop .dividend trialPairObserved <|
        .branch trialPairMarkerPresent
          (.push .work trialPairHeldBit <|
            .push .output trialPairHeldRawBit <|
              .goto (fun _ => .copyDividend))
          (.goto (fun _ => .restoreDividend))
  | .restoreDividend =>
      .pop .work trialPairObserved <|
        .branch trialPairMarkerPresent
          (.push .dividend trialPairHeldBit <|
            .goto (fun _ => .restoreDividend))
          (.push .output (fun _ => some false) <|
            .goto (fun _ => .copyDivisor))
  | .copyDivisor =>
      .pop .divisor trialPairObserved <|
        .branch trialPairMarkerPresent
          (.push .work trialPairHeldBit <|
            .push .output trialPairHeldRawBit <|
              .goto (fun _ => .copyDivisor))
          (.goto (fun _ => .restoreDivisor))
  | .restoreDivisor =>
      .pop .work trialPairObserved <|
        .branch trialPairMarkerPresent
          (.push .divisor trialPairHeldBit <|
            .goto (fun _ => .restoreDivisor))
          (.push .divisor (fun _ => true) <|
            .goto (fun _ => .loop))
  | .cleanupDivisor =>
      .pop .divisor trialPairObserved <|
        .branch trialPairMarkerPresent
          (.goto (fun _ => .cleanupDivisor))
          (.goto (fun _ => .cleanupDividend))
  | .cleanupDividend =>
      .pop .dividend trialPairObserved <|
        .branch trialPairMarkerPresent
          (.goto (fun _ => .cleanupDividend))
          (.load (fun _ => trialPairInitialState) .halt)

/-- Concrete finite machine producing `RawUnaryPairList.finEncoding`. -/
def trialDivisionPairComputer : FinTM2 where
  K := TrialPairStack
  k₀ := .input
  k₁ := .output
  Γ := TrialPairAlphabet
  Λ := TrialPairLabel
  main := .scan
  σ := TrialPairState
  initialState := trialPairInitialState
  Γk₀Fin := Bool.fintype
  m := trialDivisionPairProgram

private def trialPairStackContents
    (input dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) :
    (index : TrialPairStack) → List (TrialPairAlphabet index)
  | .input => input
  | .dividend => dividend
  | .remaining => remaining
  | .divisor => divisor
  | .work => work
  | .output => output

private def trialPairCfg (label : Option TrialPairLabel)
    (state : TrialPairState)
    (input dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) : trialDivisionPairComputer.Cfg where
  l := label
  var := state
  stk := trialPairStackContents input dividend remaining divisor work output

private def trialPairEvalsToInTimeOne
    {start finish : trialDivisionPairComputer.Cfg}
    (hstep : trialDivisionPairComputer.step start = some finish) :
    EvalsToInTime trialDivisionPairComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem trialPair_step_scan_cons
    (bit : Bool) (input dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .scan) state (bit :: input) dividend remaining
          divisor work output) =
      some (trialPairCfg (some .scan) ⟨some bit⟩ input
        (bit :: dividend) (bit :: remaining) divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, trialPairHeldBit,
    Function.update]
  funext index
  cases index <;> rfl

private theorem trialPair_step_scan_nil
    (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .scan) state [] dividend remaining divisor work
          output) =
      some (trialPairCfg (some .trimFirst) ⟨none⟩ [] dividend remaining
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]

private theorem trialPair_step_trimFirst_cons
    (bit : Bool) (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .trimFirst) state [] dividend
          (bit :: remaining) divisor work output) =
      some (trialPairCfg (some .trimSecond) ⟨some bit⟩ [] dividend remaining
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]
  funext index
  cases index <;> rfl

private theorem trialPair_step_trimFirst_nil
    (dividend divisor work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .trimFirst) state [] dividend [] divisor work
          output) =
      some (trialPairCfg (some .cleanupDivisor) ⟨none⟩ [] dividend []
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]

private theorem trialPair_step_trimSecond_cons
    (bit : Bool) (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .trimSecond) state [] dividend
          (bit :: remaining) divisor work output) =
      some (trialPairCfg (some .loop) ⟨some bit⟩ [] dividend remaining
        (true :: true :: divisor) work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]
  funext index
  cases index <;> rfl

private theorem trialPair_step_trimSecond_nil
    (dividend divisor work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .trimSecond) state [] dividend [] divisor work
          output) =
      some (trialPairCfg (some .cleanupDivisor) ⟨none⟩ [] dividend []
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, Function.update]

private theorem trialPair_step_loop_cons
    (bit : Bool) (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .loop) state [] dividend (bit :: remaining)
          divisor work output) =
      some (trialPairCfg (some .emitStart) ⟨some bit⟩ [] dividend remaining
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]
  funext index
  cases index <;> rfl

private theorem trialPair_step_loop_nil
    (dividend divisor work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .loop) state [] dividend [] divisor work output) =
      some (trialPairCfg (some .cleanupDivisor) ⟨none⟩ [] dividend []
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]

private theorem trialPair_step_emitStart
    (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .emitStart) state [] dividend remaining divisor
          work output) =
      some (trialPairCfg (some .copyDividend) state [] dividend remaining
        divisor work (none :: output)) := by
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet]
  funext index
  cases index <;> rfl

private theorem trialPair_step_copyDividend_cons
    (bit : Bool) (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .copyDividend) state [] (bit :: dividend)
          remaining divisor work output) =
      some (trialPairCfg (some .copyDividend) ⟨some bit⟩ [] dividend
        remaining divisor (bit :: work) (some bit :: output)) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, trialPairHeldBit,
    trialPairHeldRawBit, Function.update]
  funext index
  cases index <;> rfl

private theorem trialPair_step_copyDividend_nil
    (remaining divisor work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .copyDividend) state [] [] remaining divisor work
          output) =
      some (trialPairCfg (some .restoreDividend) ⟨none⟩ [] [] remaining
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]

private theorem trialPair_step_restoreDividend_cons
    (bit : Bool) (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .restoreDividend) state [] dividend remaining
          divisor (bit :: work) output) =
      some (trialPairCfg (some .restoreDividend) ⟨some bit⟩ []
        (bit :: dividend) remaining divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, trialPairHeldBit,
    Function.update]
  funext index
  cases index <;> rfl

private theorem trialPair_step_restoreDividend_nil
    (dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .restoreDividend) state [] dividend remaining
          divisor [] output) =
      some (trialPairCfg (some .copyDivisor) ⟨none⟩ [] dividend remaining
        divisor [] (some false :: output)) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]
  funext index
  cases index <;> rfl

private theorem trialPair_step_copyDivisor_cons
    (bit : Bool) (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .copyDivisor) state [] dividend remaining
          (bit :: divisor) work output) =
      some (trialPairCfg (some .copyDivisor) ⟨some bit⟩ [] dividend
        remaining divisor (bit :: work) (some bit :: output)) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, trialPairHeldBit,
    trialPairHeldRawBit, Function.update]
  funext index
  cases index <;> rfl

private theorem trialPair_step_copyDivisor_nil
    (dividend remaining work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .copyDivisor) state [] dividend remaining [] work
          output) =
      some (trialPairCfg (some .restoreDivisor) ⟨none⟩ [] dividend remaining
        [] work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]

private theorem trialPair_step_restoreDivisor_cons
    (bit : Bool) (dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .restoreDivisor) state [] dividend remaining
          divisor (bit :: work) output) =
      some (trialPairCfg (some .restoreDivisor) ⟨some bit⟩ [] dividend
        remaining (bit :: divisor) work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, trialPairHeldBit,
    Function.update]
  funext index
  cases index <;> rfl

private theorem trialPair_step_restoreDivisor_nil
    (dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .restoreDivisor) state [] dividend remaining
          divisor [] output) =
      some (trialPairCfg (some .loop) ⟨none⟩ [] dividend remaining
        (true :: divisor) [] output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, Function.update]
  funext index
  cases index <;> rfl

private theorem trialPair_step_cleanupDivisor_cons
    (bit : Bool) (dividend divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .cleanupDivisor) state [] dividend []
          (bit :: divisor) work output) =
      some (trialPairCfg (some .cleanupDivisor) ⟨some bit⟩ [] dividend []
        divisor work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]
  funext index
  cases index <;> rfl

private theorem trialPair_step_cleanupDivisor_nil
    (dividend work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .cleanupDivisor) state [] dividend [] [] work
          output) =
      some (trialPairCfg (some .cleanupDividend) ⟨none⟩ [] dividend [] []
        work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]

private theorem trialPair_step_cleanupDividend_cons
    (bit : Bool) (dividend work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .cleanupDividend) state [] (bit :: dividend) []
          [] work output) =
      some (trialPairCfg (some .cleanupDividend) ⟨some bit⟩ [] dividend []
        [] work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent]
  funext index
  cases index <;> rfl

private theorem trialPair_step_cleanupDividend_nil
    (work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    trialDivisionPairComputer.step
        (trialPairCfg (some .cleanupDividend) state [] [] [] [] work output) =
      some (trialPairCfg none trialPairInitialState [] [] [] [] work output) := by
  rcases state with ⟨marker⟩
  simp [trialDivisionPairComputer, FinTM2.step, trialPairCfg,
    trialDivisionPairProgram, trialPairStackContents, TrialPairAlphabet,
    trialPairObserved, trialPairMarkerPresent, trialPairInitialState]

private def trialPair_scan_evals
    (input dividend remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .scan) state input dividend remaining divisor work
        output)
      (some (trialPairCfg (some .trimFirst) ⟨none⟩ []
        (input.reverse ++ dividend) (input.reverse ++ remaining)
        divisor work output))
      (input.length + 1) := by
  induction input generalizing dividend remaining state with
  | nil =>
      simpa using trialPairEvalsToInTimeOne
        (trialPair_step_scan_nil dividend remaining divisor work output state)
  | cons bit input ih =>
      let middle := trialPairCfg (some .scan) ⟨some bit⟩ input
        (bit :: dividend) (bit :: remaining) divisor work output
      have hone : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .scan) state (bit :: input) dividend remaining
            divisor work output)
          (some middle) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [middle] using trialPair_step_scan_cons bit input dividend
            remaining divisor work output state)
      have hrest := ih (bit :: dividend) (bit :: remaining) ⟨some bit⟩
      have htrans := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (input.length + 1)
        (trialPairCfg (some .scan) state (bit :: input) dividend remaining
          divisor work output)
        middle
        (some (trialPairCfg (some .trimFirst) ⟨none⟩ []
          ((bit :: input).reverse ++ dividend)
          ((bit :: input).reverse ++ remaining) divisor work output))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def trialPair_copyDividend_evals
    (bits remaining divisor work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .copyDividend) state [] bits remaining divisor work
        output)
      (some (trialPairCfg (some .restoreDividend) ⟨none⟩ [] [] remaining
        divisor (bits.reverse ++ work) (bits.reverse.map some ++ output)))
      (bits.length + 1) := by
  induction bits generalizing work output state with
  | nil =>
      simpa using trialPairEvalsToInTimeOne
        (trialPair_step_copyDividend_nil remaining divisor work output state)
  | cons bit bits ih =>
      let middle := trialPairCfg (some .copyDividend) ⟨some bit⟩ [] bits
        remaining divisor (bit :: work) (some bit :: output)
      have hone : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .copyDividend) state [] (bit :: bits)
            remaining divisor work output)
          (some middle) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [middle] using trialPair_step_copyDividend_cons bit bits
            remaining divisor work output state)
      have hrest := ih (bit :: work) (some bit :: output) ⟨some bit⟩
      have htrans := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (bits.length + 1)
        (trialPairCfg (some .copyDividend) state [] (bit :: bits)
          remaining divisor work output)
        middle
        (some (trialPairCfg (some .restoreDividend) ⟨none⟩ [] [] remaining
          divisor ((bit :: bits).reverse ++ work)
          ((bit :: bits).reverse.map some ++ output)))
        hone
        (by simpa [middle, List.reverse_cons, List.map_append,
          List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def trialPair_restoreDividend_evals
    (work dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .restoreDividend) state [] dividend remaining
        divisor work output)
      (some (trialPairCfg (some .copyDivisor) ⟨none⟩ []
        (work.reverse ++ dividend) remaining divisor []
        (some false :: output)))
      (work.length + 1) := by
  induction work generalizing dividend state with
  | nil =>
      simpa using trialPairEvalsToInTimeOne
        (trialPair_step_restoreDividend_nil dividend remaining divisor output
          state)
  | cons bit work ih =>
      let middle := trialPairCfg (some .restoreDividend) ⟨some bit⟩ []
        (bit :: dividend) remaining divisor work output
      have hone : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .restoreDividend) state [] dividend remaining
            divisor (bit :: work) output)
          (some middle) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [middle] using trialPair_step_restoreDividend_cons bit
            dividend remaining divisor work output state)
      have hrest := ih (bit :: dividend) ⟨some bit⟩
      have htrans := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (work.length + 1)
        (trialPairCfg (some .restoreDividend) state [] dividend remaining
          divisor (bit :: work) output)
        middle
        (some (trialPairCfg (some .copyDivisor) ⟨none⟩ []
          ((bit :: work).reverse ++ dividend) remaining divisor []
          (some false :: output)))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def trialPair_copyDivisor_evals
    (bits dividend remaining work : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .copyDivisor) state [] dividend remaining bits work
        output)
      (some (trialPairCfg (some .restoreDivisor) ⟨none⟩ [] dividend
        remaining [] (bits.reverse ++ work)
        (bits.reverse.map some ++ output)))
      (bits.length + 1) := by
  induction bits generalizing work output state with
  | nil =>
      simpa using trialPairEvalsToInTimeOne
        (trialPair_step_copyDivisor_nil dividend remaining work output state)
  | cons bit bits ih =>
      let middle := trialPairCfg (some .copyDivisor) ⟨some bit⟩ [] dividend
        remaining bits (bit :: work) (some bit :: output)
      have hone : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .copyDivisor) state [] dividend remaining
            (bit :: bits) work output)
          (some middle) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [middle] using trialPair_step_copyDivisor_cons bit dividend
            remaining bits work output state)
      have hrest := ih (bit :: work) (some bit :: output) ⟨some bit⟩
      have htrans := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (bits.length + 1)
        (trialPairCfg (some .copyDivisor) state [] dividend remaining
          (bit :: bits) work output)
        middle
        (some (trialPairCfg (some .restoreDivisor) ⟨none⟩ [] dividend
          remaining [] ((bit :: bits).reverse ++ work)
          ((bit :: bits).reverse.map some ++ output)))
        hone
        (by simpa [middle, List.reverse_cons, List.map_append,
          List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def trialPair_restoreDivisor_evals
    (work dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .restoreDivisor) state [] dividend remaining divisor
        work output)
      (some (trialPairCfg (some .loop) ⟨none⟩ [] dividend remaining
        (true :: work.reverse ++ divisor) [] output))
      (work.length + 1) := by
  induction work generalizing divisor state with
  | nil =>
      simpa using trialPairEvalsToInTimeOne
        (trialPair_step_restoreDivisor_nil dividend remaining divisor output
          state)
  | cons bit work ih =>
      let middle := trialPairCfg (some .restoreDivisor) ⟨some bit⟩ []
        dividend remaining (bit :: divisor) work output
      have hone : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .restoreDivisor) state [] dividend remaining
            divisor (bit :: work) output)
          (some middle) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [middle] using trialPair_step_restoreDivisor_cons bit dividend
            remaining divisor work output state)
      have hrest := ih (bit :: divisor) ⟨some bit⟩
      have htrans := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (work.length + 1)
        (trialPairCfg (some .restoreDivisor) state [] dividend remaining
          divisor (bit :: work) output)
        middle
        (some (trialPairCfg (some .loop) ⟨none⟩ [] dividend remaining
          (true :: (bit :: work).reverse ++ divisor) [] output))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def trialPairEmitTime (dividend divisor : List Bool) : ℕ :=
  2 * dividend.length + 2 * divisor.length + 5

private theorem trialPair_segment_append
    (dividend divisor : List Bool) (output : List (Option Bool)) :
    divisor.reverse.map some ++ some false ::
        dividend.reverse.map some ++ none :: output =
      RawNatList.segment (dividend ++ false :: divisor) ++ output := by
  simp [RawNatList.segment, List.reverse_append, List.map_append,
    List.append_assoc]

private def trialPair_emit_copyDividend_evals
    (dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
        output)
      (some (trialPairCfg (some .restoreDividend) ⟨none⟩ [] [] remaining
        divisor dividend.reverse
        (dividend.reverse.map some ++ none :: output)))
      (dividend.length + 2) := by
  let afterStart := trialPairCfg (some .copyDividend) state [] dividend
    remaining divisor [] (none :: output)
  have hstart : EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
        output)
      (some afterStart) 1 :=
    trialPairEvalsToInTimeOne (by
      simpa [afterStart] using trialPair_step_emitStart dividend remaining
        divisor [] output state)
  have hcopy := trialPair_copyDividend_evals dividend remaining divisor []
    (none :: output) state
  have hall := EvalsToInTime.trans trialDivisionPairComputer.step
    1 (dividend.length + 1)
    (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
      output)
    afterStart
    (some (trialPairCfg (some .restoreDividend) ⟨none⟩ [] [] remaining
      divisor dividend.reverse
      (dividend.reverse.map some ++ none :: output)))
    hstart
    (by simpa [afterStart] using hcopy)
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def trialPair_emit_restoreDividend_evals
    (dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
        output)
      (some (trialPairCfg (some .copyDivisor) ⟨none⟩ [] dividend remaining
        divisor [] (some false :: dividend.reverse.map some ++ none :: output)))
      (2 * dividend.length + 3) := by
  have hfirst := trialPair_emit_copyDividend_evals dividend remaining divisor
    output state
  have hrestore := trialPair_restoreDividend_evals dividend.reverse []
    remaining divisor (dividend.reverse.map some ++ none :: output) ⟨none⟩
  have hall := EvalsToInTime.trans trialDivisionPairComputer.step
    (dividend.length + 2) (dividend.reverse.length + 1)
    (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
      output)
    (trialPairCfg (some .restoreDividend) ⟨none⟩ [] [] remaining divisor
      dividend.reverse (dividend.reverse.map some ++ none :: output))
    (some (trialPairCfg (some .copyDivisor) ⟨none⟩ [] dividend remaining
      divisor [] (some false :: dividend.reverse.map some ++ none :: output)))
    hfirst
    (by simpa using hrestore)
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def trialPair_emit_copyDivisor_evals
    (dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
        output)
      (some (trialPairCfg (some .restoreDivisor) ⟨none⟩ [] dividend remaining
        [] divisor.reverse
        (divisor.reverse.map some ++ some false ::
          dividend.reverse.map some ++ none :: output)))
      (2 * dividend.length + divisor.length + 4) := by
  have hfirst := trialPair_emit_restoreDividend_evals dividend remaining divisor
    output state
  have hcopy := trialPair_copyDivisor_evals divisor dividend remaining []
    (some false :: dividend.reverse.map some ++ none :: output) ⟨none⟩
  have hall := EvalsToInTime.trans trialDivisionPairComputer.step
    (2 * dividend.length + 3) (divisor.length + 1)
    (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
      output)
    (trialPairCfg (some .copyDivisor) ⟨none⟩ [] dividend remaining divisor []
      (some false :: dividend.reverse.map some ++ none :: output))
    (some (trialPairCfg (some .restoreDivisor) ⟨none⟩ [] dividend remaining
      [] divisor.reverse
      (divisor.reverse.map some ++ some false ::
        dividend.reverse.map some ++ none :: output)))
    hfirst
    (by simpa [List.append_assoc] using hcopy)
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def trialPair_emit_restoreDivisor_evals
    (dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
        output)
      (some (trialPairCfg (some .loop) ⟨none⟩ [] dividend remaining
        (true :: divisor) []
        (RawNatList.segment (dividend ++ false :: divisor) ++ output)))
      (2 * dividend.length + 2 * divisor.length + 5) := by
  have hfirst := trialPair_emit_copyDivisor_evals dividend remaining divisor
    output state
  have hrestore := trialPair_restoreDivisor_evals divisor.reverse dividend
    remaining []
    (divisor.reverse.map some ++ some false ::
      dividend.reverse.map some ++ none :: output) ⟨none⟩
  have hall := EvalsToInTime.trans trialDivisionPairComputer.step
    (2 * dividend.length + divisor.length + 4)
    (divisor.reverse.length + 1)
    (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
      output)
    (trialPairCfg (some .restoreDivisor) ⟨none⟩ [] dividend remaining []
      divisor.reverse
      (divisor.reverse.map some ++ some false ::
        dividend.reverse.map some ++ none :: output))
    (some (trialPairCfg (some .loop) ⟨none⟩ [] dividend remaining
      (true :: divisor) []
      (RawNatList.segment (dividend ++ false :: divisor) ++ output)))
    hfirst
    (by
      rw [← trialPair_segment_append dividend divisor output]
      simpa using hrestore)
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def trialPair_emit_evals
    (dividend remaining divisor : List Bool)
    (output : List (Option Bool)) (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .emitStart) state [] dividend remaining divisor []
        output)
      (some (trialPairCfg (some .loop) ⟨none⟩ [] dividend remaining
        (true :: divisor) []
        (RawNatList.segment (dividend ++ false :: divisor) ++ output)))
      (trialPairEmitTime dividend divisor) := by
  simpa [trialPairEmitTime] using
    trialPair_emit_restoreDivisor_evals dividend remaining divisor output state

private def trialPair_cleanupDivisor_evals
    (divisor dividend work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .cleanupDivisor) state [] dividend [] divisor work
        output)
      (some (trialPairCfg (some .cleanupDividend) ⟨none⟩ [] dividend [] []
        work output))
      (divisor.length + 1) := by
  induction divisor generalizing state with
  | nil =>
      simpa using trialPairEvalsToInTimeOne
        (trialPair_step_cleanupDivisor_nil dividend work output state)
  | cons bit divisor ih =>
      let middle := trialPairCfg (some .cleanupDivisor) ⟨some bit⟩ []
        dividend [] divisor work output
      have hone : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .cleanupDivisor) state [] dividend []
            (bit :: divisor) work output)
          (some middle) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [middle] using trialPair_step_cleanupDivisor_cons bit dividend
            divisor work output state)
      have hrest := ih ⟨some bit⟩
      have htrans := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (divisor.length + 1)
        (trialPairCfg (some .cleanupDivisor) state [] dividend []
          (bit :: divisor) work output)
        middle
        (some (trialPairCfg (some .cleanupDividend) ⟨none⟩ [] dividend [] []
          work output))
        hone
        (by simpa [middle] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private def trialPair_cleanupDividend_evals
    (dividend work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .cleanupDividend) state [] dividend [] [] work
        output)
      (some (trialPairCfg none trialPairInitialState [] [] [] [] work output))
      (dividend.length + 1) := by
  induction dividend generalizing state with
  | nil =>
      simpa using trialPairEvalsToInTimeOne
        (trialPair_step_cleanupDividend_nil work output state)
  | cons bit dividend ih =>
      let middle := trialPairCfg (some .cleanupDividend) ⟨some bit⟩ []
        dividend [] [] work output
      have hone : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .cleanupDividend) state [] (bit :: dividend) []
            [] work output)
          (some middle) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [middle] using trialPair_step_cleanupDividend_cons bit
            dividend work output state)
      have hrest := ih ⟨some bit⟩
      have htrans := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (dividend.length + 1)
        (trialPairCfg (some .cleanupDividend) state [] (bit :: dividend) []
          [] work output)
        middle
        (some (trialPairCfg none trialPairInitialState [] [] [] [] work
          output))
        hone
        (by simpa [middle] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

/-- The consecutive pair suffix beginning at divisor `first`. -/
def trialPairsFrom : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, _n, _first => []
  | count + 1, n, first =>
      (n, first) :: trialPairsFrom count n (first + 1)

theorem trialPairsFrom_eq_range (count n first : ℕ) :
    trialPairsFrom count n first =
      (List.range' first count).map fun divisor => (n, divisor) := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
      simp [trialPairsFrom, List.range'_succ, ih]

@[simp]
theorem trialPairsFrom_sub_two (n : ℕ) :
    trialPairsFrom (n - 2) n 2 = trialDivisionPairs n := by
  rw [trialPairsFrom_eq_range]
  rfl

private def encodedTrialPairSuffix (count n first : ℕ) :
    List (Option Bool) :=
  RawUnaryPairList.encode (trialPairsFrom count n first)

private theorem encodedTrialPairSuffix_succ (count n first : ℕ) :
    encodedTrialPairSuffix (count + 1) n first =
      encodedTrialPairSuffix count n (first + 1) ++
        RawNatList.segment (UnaryNatPair.encode (n, first)) := by
  simp [encodedTrialPairSuffix, trialPairsFrom, RawUnaryPairList.encode,
    List.reverse_cons, List.flatMap_append]

private def trialPairLoopTime : ℕ → ℕ → ℕ → ℕ
  | 0, n, first => n + first + 3
  | count + 1, n, first =>
      1 + trialPairEmitTime (unaryEncodeNat n) (unaryEncodeNat first) +
        trialPairLoopTime count n (first + 1)

private theorem unaryEncodeNat_eq_replicate (n : ℕ) :
    unaryEncodeNat n = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [unaryEncodeNat, List.replicate_succ, ih]

private def trialPair_loop_evals
    (count n first : ℕ) (output : List (Option Bool))
    (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .loop) state [] (unaryEncodeNat n)
        (unaryEncodeNat count) (unaryEncodeNat first) [] output)
      (some (trialPairCfg none trialPairInitialState [] [] [] [] []
        (encodedTrialPairSuffix count n first ++ output)))
      (trialPairLoopTime count n first) := by
  induction count generalizing first output state with
  | zero =>
      let afterLoop := trialPairCfg (some .cleanupDivisor) ⟨none⟩ []
        (unaryEncodeNat n) [] (unaryEncodeNat first) [] output
      have hloop : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .loop) state [] (unaryEncodeNat n) []
            (unaryEncodeNat first) [] output)
          (some afterLoop) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [afterLoop] using trialPair_step_loop_nil
            (unaryEncodeNat n) (unaryEncodeNat first) [] output state)
      have hcleanupDivisor := trialPair_cleanupDivisor_evals
        (unaryEncodeNat first) (unaryEncodeNat n) [] output ⟨none⟩
      let afterDivisor := trialPairCfg (some .cleanupDividend) ⟨none⟩ []
        (unaryEncodeNat n) [] [] [] output
      have hfirst := EvalsToInTime.trans trialDivisionPairComputer.step
        1 ((unaryEncodeNat first).length + 1)
        (trialPairCfg (some .loop) state [] (unaryEncodeNat n) []
          (unaryEncodeNat first) [] output)
        afterLoop
        (some afterDivisor)
        hloop
        (by simpa [afterLoop, afterDivisor] using hcleanupDivisor)
      have hcleanupDividend := trialPair_cleanupDividend_evals
        (unaryEncodeNat n) [] output ⟨none⟩
      have hall := EvalsToInTime.trans trialDivisionPairComputer.step
        (1 + ((unaryEncodeNat first).length + 1))
        ((unaryEncodeNat n).length + 1)
        (trialPairCfg (some .loop) state [] (unaryEncodeNat n) []
          (unaryEncodeNat first) [] output)
        afterDivisor
        (some (trialPairCfg none trialPairInitialState [] [] [] [] []
          output))
        (by simpa [Nat.add_comm] using hfirst)
        (by simpa [afterDivisor] using hcleanupDividend)
      simpa [trialPairLoopTime, encodedTrialPairSuffix,
        trialPairInitialState, unaryEncodeNat_length, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hall
  | succ count ih =>
      let afterLoop := trialPairCfg (some .emitStart) ⟨some true⟩ []
        (unaryEncodeNat n) (unaryEncodeNat count)
        (unaryEncodeNat first) [] output
      have hloop : EvalsToInTime trialDivisionPairComputer.step
          (trialPairCfg (some .loop) state [] (unaryEncodeNat n)
            (unaryEncodeNat (count + 1)) (unaryEncodeNat first) [] output)
          (some afterLoop) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [afterLoop, unaryEncodeNat] using trialPair_step_loop_cons true
            (unaryEncodeNat n) (unaryEncodeNat count)
            (unaryEncodeNat first) [] output state)
      have hemit := trialPair_emit_evals (unaryEncodeNat n)
        (unaryEncodeNat count) (unaryEncodeNat first) output ⟨some true⟩
      let afterEmit := trialPairCfg (some .loop) ⟨none⟩ []
        (unaryEncodeNat n) (unaryEncodeNat count)
        (unaryEncodeNat (first + 1)) []
        (RawNatList.segment (UnaryNatPair.encode (n, first)) ++ output)
      have hfirst := EvalsToInTime.trans trialDivisionPairComputer.step
        1 (trialPairEmitTime (unaryEncodeNat n) (unaryEncodeNat first))
        (trialPairCfg (some .loop) state [] (unaryEncodeNat n)
          (unaryEncodeNat (count + 1)) (unaryEncodeNat first) [] output)
        afterLoop
        (some afterEmit)
        hloop
        (by
          simpa [afterLoop, afterEmit, UnaryNatPair.encode,
            unaryEncodeNat_eq_replicate]
            using hemit)
      have hrest := ih (first + 1)
        (RawNatList.segment (UnaryNatPair.encode (n, first)) ++ output)
        ⟨none⟩
      have hall := EvalsToInTime.trans trialDivisionPairComputer.step
        (1 + trialPairEmitTime (unaryEncodeNat n) (unaryEncodeNat first))
        (trialPairLoopTime count n (first + 1))
        (trialPairCfg (some .loop) state [] (unaryEncodeNat n)
          (unaryEncodeNat (count + 1)) (unaryEncodeNat first) [] output)
        afterEmit
        (some (trialPairCfg none trialPairInitialState [] [] [] [] []
          (encodedTrialPairSuffix (count + 1) n first ++ output)))
        (by simpa [Nat.add_comm] using hfirst)
        (by
          rw [encodedTrialPairSuffix_succ]
          simpa [afterEmit, List.append_assoc] using hrest)
      simpa [trialPairLoopTime, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall

private theorem trialPairLoopTime_le (count n first : ℕ) :
    trialPairLoopTime count n first ≤
      count * (2 * n + 2 * (first + count) + 6) +
        n + (first + count) + 3 := by
  induction count generalizing first with
  | zero => simp [trialPairLoopTime]
  | succ count ih =>
      have hrest := ih (first + 1)
      simp only [trialPairLoopTime, trialPairEmitTime,
        unaryEncodeNat_length]
      nlinarith

private def trialPair_prepare_evals
    (count n : ℕ) (output : List (Option Bool))
    (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .trimFirst) state [] (unaryEncodeNat n)
        (unaryEncodeNat (count + 2)) [] [] output)
      (some (trialPairCfg (some .loop) ⟨some true⟩ [] (unaryEncodeNat n)
        (unaryEncodeNat count) (unaryEncodeNat 2) [] output))
      2 := by
  let middle := trialPairCfg (some .trimSecond) ⟨some true⟩ []
    (unaryEncodeNat n) (unaryEncodeNat (count + 1)) [] [] output
  have hfirst : EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .trimFirst) state [] (unaryEncodeNat n)
        (unaryEncodeNat (count + 2)) [] [] output)
      (some middle) 1 :=
    trialPairEvalsToInTimeOne (by
      simpa [middle, unaryEncodeNat] using trialPair_step_trimFirst_cons true
        (unaryEncodeNat n) (unaryEncodeNat (count + 1)) [] [] output state)
  have hsecond : EvalsToInTime trialDivisionPairComputer.step
      middle
      (some (trialPairCfg (some .loop) ⟨some true⟩ [] (unaryEncodeNat n)
        (unaryEncodeNat count) (unaryEncodeNat 2) [] output)) 1 :=
    trialPairEvalsToInTimeOne (by
      simpa [middle, unaryEncodeNat] using trialPair_step_trimSecond_cons true
        (unaryEncodeNat n) (unaryEncodeNat count) [] [] output ⟨some true⟩)
  simpa using EvalsToInTime.trans trialDivisionPairComputer.step 1 1
    (trialPairCfg (some .trimFirst) state [] (unaryEncodeNat n)
      (unaryEncodeNat (count + 2)) [] [] output)
    middle
    (some (trialPairCfg (some .loop) ⟨some true⟩ [] (unaryEncodeNat n)
      (unaryEncodeNat count) (unaryEncodeNat 2) [] output))
    hfirst hsecond

private def trialPair_cleanup_evals
    (divisor dividend work : List Bool) (output : List (Option Bool))
    (state : TrialPairState) :
    EvalsToInTime trialDivisionPairComputer.step
      (trialPairCfg (some .cleanupDivisor) state [] dividend [] divisor work
        output)
      (some (trialPairCfg none trialPairInitialState [] [] [] [] work output))
      (divisor.length + dividend.length + 2) := by
  have hdivisor := trialPair_cleanupDivisor_evals divisor dividend work output
    state
  have hdividend := trialPair_cleanupDividend_evals dividend work output ⟨none⟩
  have hall := EvalsToInTime.trans trialDivisionPairComputer.step
    (divisor.length + 1) (dividend.length + 1)
    (trialPairCfg (some .cleanupDivisor) state [] dividend [] divisor work
      output)
    (trialPairCfg (some .cleanupDividend) ⟨none⟩ [] dividend [] [] work
      output)
    (some (trialPairCfg none trialPairInitialState [] [] [] [] work output))
    hdivisor hdividend
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private theorem unaryEncodeNat_reverse (n : ℕ) :
    (unaryEncodeNat n).reverse = unaryEncodeNat n := by
  rw [unaryEncodeNat_eq_replicate, List.reverse_replicate]

private theorem trialPair_initList_eq_cfg (input : List Bool) :
    initList trialDivisionPairComputer input =
      trialPairCfg (some .scan) trialPairInitialState input [] [] [] [] [] := by
  unfold initList trialPairCfg
  congr
  funext index
  cases index <;> rfl

private theorem trialPair_haltList_eq_cfg (output : List (Option Bool)) :
    haltList trialDivisionPairComputer output =
      trialPairCfg none trialPairInitialState [] [] [] [] [] output := by
  unfold haltList trialPairCfg
  congr
  funext index
  cases index <;> rfl

/-- The concrete generator emits every padded trial pair in at most
`8(n+1)^2` steps from unary input `n`. -/
def trialDivisionPairs_outputsInTime (n : ℕ) :
    TM2OutputsInTime trialDivisionPairComputer (unaryEncodeNat n)
      (some (RawUnaryPairList.encode (trialDivisionPairs n)))
      (8 * (n + 1) ^ 2) := by
  cases n with
  | zero =>
      have hscan := trialPair_scan_evals [] [] [] [] [] []
        trialPairInitialState
      let afterScan := trialPairCfg (some .trimFirst) ⟨none⟩ [] [] [] [] [] []
      have htrim : EvalsToInTime trialDivisionPairComputer.step afterScan
          (some (trialPairCfg (some .cleanupDivisor) ⟨none⟩ [] [] [] [] []
            [])) 1 :=
        trialPairEvalsToInTimeOne (by
          simpa [afterScan] using trialPair_step_trimFirst_nil [] [] [] []
            ⟨none⟩)
      have hcleanup := trialPair_cleanup_evals [] [] [] [] ⟨none⟩
      have hfirst := EvalsToInTime.trans trialDivisionPairComputer.step 1 1
        (trialPairCfg (some .scan) trialPairInitialState [] [] [] [] [] [])
        afterScan
        (some (trialPairCfg (some .cleanupDivisor) ⟨none⟩ [] [] [] [] []
          []))
        (by simpa [afterScan] using hscan)
        htrim
      have hall := EvalsToInTime.trans trialDivisionPairComputer.step 2 2
        (trialPairCfg (some .scan) trialPairInitialState [] [] [] [] [] [])
        (trialPairCfg (some .cleanupDivisor) ⟨none⟩ [] [] [] [] [] [])
        (some (trialPairCfg none trialPairInitialState [] [] [] [] [] []))
        (by simpa using hfirst)
        (by simpa using hcleanup)
      have hmono := evalsToInTimeMono hall (by norm_num : 4 ≤ 8 * (0 + 1) ^ 2)
      rw [TM2OutputsInTime, trialPair_initList_eq_cfg]
      simp only [Option.map_some]
      rw [trialPair_haltList_eq_cfg]
      simpa [trialDivisionPairs, trialDivisors, RawUnaryPairList.encode] using
        hmono
  | succ n =>
      cases n with
      | zero =>
          have hscan := trialPair_scan_evals (unaryEncodeNat 1) [] [] [] [] []
            trialPairInitialState
          let afterScan := trialPairCfg (some .trimFirst) ⟨none⟩ []
            (unaryEncodeNat 1) (unaryEncodeNat 1) [] [] []
          let afterFirst := trialPairCfg (some .trimSecond) ⟨some true⟩ []
            (unaryEncodeNat 1) [] [] [] []
          let afterSecond := trialPairCfg (some .cleanupDivisor) ⟨none⟩ []
            (unaryEncodeNat 1) [] [] [] []
          have hfirstTrim : EvalsToInTime trialDivisionPairComputer.step
              afterScan (some afterFirst) 1 :=
            trialPairEvalsToInTimeOne (by
              simpa [afterScan, afterFirst, unaryEncodeNat] using
                trialPair_step_trimFirst_cons true (unaryEncodeNat 1) [] []
                  [] [] ⟨none⟩)
          have hsecondTrim : EvalsToInTime trialDivisionPairComputer.step
              afterFirst (some afterSecond) 1 :=
            trialPairEvalsToInTimeOne (by
              simpa [afterFirst, afterSecond] using
                trialPair_step_trimSecond_nil (unaryEncodeNat 1) [] [] []
                  ⟨some true⟩)
          have hcleanup := trialPair_cleanup_evals [] (unaryEncodeNat 1) [] []
            ⟨none⟩
          have hthroughFirst := EvalsToInTime.trans
            trialDivisionPairComputer.step 2 1
            (trialPairCfg (some .scan) trialPairInitialState
              (unaryEncodeNat 1) [] [] [] [] [])
            afterScan
            (some afterFirst)
            (by
              simpa [afterScan, unaryEncodeNat_reverse] using hscan)
            hfirstTrim
          have hthroughSecond := EvalsToInTime.trans
            trialDivisionPairComputer.step 3 1
            (trialPairCfg (some .scan) trialPairInitialState
              (unaryEncodeNat 1) [] [] [] [] [])
            afterFirst
            (some afterSecond)
            (by simpa using hthroughFirst)
            hsecondTrim
          have hall := EvalsToInTime.trans trialDivisionPairComputer.step 4 3
            (trialPairCfg (some .scan) trialPairInitialState
              (unaryEncodeNat 1) [] [] [] [] [])
            afterSecond
            (some (trialPairCfg none trialPairInitialState [] [] [] [] [] []))
            (by simpa using hthroughSecond)
            (by simpa [afterSecond, unaryEncodeNat_length] using hcleanup)
          have hmono := evalsToInTimeMono hall
            (by norm_num : 7 ≤ 8 * (1 + 1) ^ 2)
          rw [TM2OutputsInTime, trialPair_initList_eq_cfg]
          simp only [Option.map_some]
          rw [trialPair_haltList_eq_cfg]
          simpa [trialDivisionPairs, trialDivisors, RawUnaryPairList.encode]
            using hmono
      | succ count =>
          let value := count + 2
          have hscan := trialPair_scan_evals (unaryEncodeNat value) [] [] []
            [] [] trialPairInitialState
          let afterScan := trialPairCfg (some .trimFirst) ⟨none⟩ []
            (unaryEncodeNat value) (unaryEncodeNat value) [] [] []
          have hprepare := trialPair_prepare_evals count value [] ⟨none⟩
          let afterPrepare := trialPairCfg (some .loop) ⟨some true⟩ []
            (unaryEncodeNat value) (unaryEncodeNat count)
            (unaryEncodeNat 2) [] []
          have hfirst := EvalsToInTime.trans trialDivisionPairComputer.step
            ((unaryEncodeNat value).length + 1) 2
            (trialPairCfg (some .scan) trialPairInitialState
              (unaryEncodeNat value) [] [] [] [] [])
            afterScan
            (some afterPrepare)
            (by
              simpa [afterScan, unaryEncodeNat_reverse] using hscan)
            (by simpa [afterScan, afterPrepare, value] using hprepare)
          have hloop := trialPair_loop_evals count value 2 [] ⟨some true⟩
          have hpairs :
              trialPairsFrom count value 2 = trialDivisionPairs value := by
            simpa [value] using trialPairsFrom_sub_two value
          have hall := EvalsToInTime.trans trialDivisionPairComputer.step
            (((unaryEncodeNat value).length + 1) + 2)
            (trialPairLoopTime count value 2)
            (trialPairCfg (some .scan) trialPairInitialState
              (unaryEncodeNat value) [] [] [] [] [])
            afterPrepare
            (some (trialPairCfg none trialPairInitialState [] [] [] [] []
              (RawUnaryPairList.encode (trialDivisionPairs value))))
            (by simpa [Nat.add_comm] using hfirst)
            (by
              simpa [afterPrepare, encodedTrialPairSuffix, hpairs]
                using hloop)
          have hloopBound := trialPairLoopTime_le count value 2
          have hbound :
              ((unaryEncodeNat value).length + 1 + 2) +
                  trialPairLoopTime count value 2 ≤
                8 * (value + 1) ^ 2 := by
            simp only [unaryEncodeNat_length, value] at hloopBound ⊢
            nlinarith
          have hmono := evalsToInTimeMono
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hall)
            hbound
          rw [TM2OutputsInTime, trialPair_initList_eq_cfg]
          simp only [Option.map_some]
          rw [trialPair_haltList_eq_cfg]
          simpa [value] using hmono

/-- Genuine polynomial-time production of all unary-padded inputs needed to
test one candidate by bounded trial division. -/
noncomputable def trialDivisionPairsComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ (List (ℕ × ℕ)) unaryFinEncodingNat
      RawUnaryPairList.finEncoding trialDivisionPairs where
  tm := trialDivisionPairComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Option Bool)
  time := 8 * (Polynomial.X + 1) ^ 2
  outputsFun n := by
    simpa [unaryFinEncodingNat, RawUnaryPairList.finEncoding, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using
        trialDivisionPairs_outputsInTime n

/-! ## Boolean aggregation of trial-division results

The repeated divisibility driver will emit one Boolean for every padded trial
pair, with `true` meaning that the proposed divisor divides the candidate.  The
following finite machine folds that result stream to `true` exactly when no
test succeeded.  This keeps Boolean aggregation separate from the still-open
machine that repeatedly invokes `unaryDvdComputer` on the padded pair stream.
-/

namespace RawBoolList

/-- The literal Boolean stream encoding used between the future repeated
divisibility driver and the checked aggregation pass. -/
def finEncoding : FinEncoding (List Bool) where
  Γ := Bool
  encode := id
  decode := some
  decode_encode := fun _ => rfl
  ΓFin := Bool.fintype

@[simp]
theorem encode_eq (results : List Bool) :
    finEncoding.encode results = results :=
  rfl

end RawBoolList

/-! ## Repeated padded divisibility

The pair generator emits a stack-oriented list of complete unary-pair fields.
The driver below restores one field at a time on the existing divisibility
machine's input stack, runs that checked program, and resumes scanning after
the component halt.  Processing the reversed field stream while pushing each
Boolean result restores the source pair order on the output stack.
-/

/-- Apply the divisibility predicate to every pair in source order. -/
def pairDivisionResults (pairs : List (ℕ × ℕ)) : List Bool :=
  pairs.map fun pair => decide (pair.2 ∣ pair.1)

/-- The raw outer input plus every stack of the existing divisibility
machine. -/
abbrev PairDvdStack := Unit ⊕ DvdStack

/-- Outer field scanning or execution of one divisibility-machine label. -/
inductive PairDvdLabel
  | scan
  | dvd (label : DvdLabel)
  deriving DecidableEq, Fintype

/-- The outer scanner remembers its last pop; the component state is kept
unchanged while a raw field is restored. -/
structure PairDvdState where
  observed : Option (Option Bool)
  dvd : DvdState
  deriving DecidableEq, Fintype

private def pairDvdInitialState : PairDvdState :=
  ⟨none, dvdInitialState⟩

private def pairDvdObserve
    (state : PairDvdState) (observed : Option (Option Bool)) : PairDvdState :=
  { state with observed := observed }

private def pairDvdResetObserved (state : PairDvdState) : PairDvdState :=
  { state with observed := none }

private def pairDvdSetComponent
    (state : PairDvdState) (dvd : DvdState) : PairDvdState :=
  { state with dvd := dvd }

private def pairDvdObservedPresent : PairDvdState → Bool
  | ⟨some _, _⟩ => true
  | _ => false

private def pairDvdObservedSymbol : PairDvdState → Bool
  | ⟨some (some _), _⟩ => true
  | _ => false

private def pairDvdObservedBit : PairDvdState → Bool
  | ⟨some (some bit), _⟩ => bit
  | _ => false

private def PairDvdAlphabet : PairDvdStack → Type
  | .inl _ => Option Bool
  | .inr index => DvdAlphabet index

/-- Lift a statement of the checked divisibility machine.  Reaching its halt
resets the outer observation and returns to the raw-field scanner. -/
private def liftDvdStmt :
    TM2.Stmt DvdAlphabet DvdLabel DvdState →
      TM2.Stmt PairDvdAlphabet PairDvdLabel PairDvdState
  | .push index write next =>
      .push (.inr index) (fun state => write state.dvd) (liftDvdStmt next)
  | .peek index read next =>
      .peek (.inr index)
        (fun state observed => pairDvdSetComponent state (read state.dvd observed))
        (liftDvdStmt next)
  | .pop index read next =>
      .pop (.inr index)
        (fun state observed => pairDvdSetComponent state (read state.dvd observed))
        (liftDvdStmt next)
  | .load update next =>
      .load (fun state => pairDvdSetComponent state (update state.dvd))
        (liftDvdStmt next)
  | .branch test yes no =>
      .branch (fun state => test state.dvd) (liftDvdStmt yes) (liftDvdStmt no)
  | .goto next => .goto (fun state => .dvd (next state.dvd))
  | .halt =>
      .load pairDvdResetObserved (.goto fun _ => .scan)

/-- Scan one reversed raw field into the component input stack, or halt when
the complete outer stream is exhausted. -/
def pairDvdProgram :
    PairDvdLabel → TM2.Stmt PairDvdAlphabet PairDvdLabel PairDvdState
  | .scan =>
      .pop (.inl ()) pairDvdObserve <|
        .branch pairDvdObservedPresent
          (.branch pairDvdObservedSymbol
            (.push (.inr .input) pairDvdObservedBit <|
              .load pairDvdResetObserved <|
                .goto fun _ => .scan)
            (.load pairDvdResetObserved <|
              .goto fun _ => .dvd .scanDividend))
          .halt
  | .dvd label => liftDvdStmt (unaryDvdProgram label)

/-- Concrete finite machine mapping a padded pair stream to its divisibility
result stream. -/
def pairDvdComputer : FinTM2 where
  K := PairDvdStack
  k₀ := .inl ()
  k₁ := .inr .output
  Γ := PairDvdAlphabet
  Λ := PairDvdLabel
  main := .scan
  σ := PairDvdState
  initialState := pairDvdInitialState
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := pairDvdProgram

private def pairDvdStackContents
    (input : List (Option Bool))
    (contents : (index : DvdStack) → List (DvdAlphabet index)) :
    (index : PairDvdStack) → List (PairDvdAlphabet index)
  | .inl _ => input
  | .inr index => contents index

/-- Embed a component configuration while fixing the unconsumed raw stream.
A component halt is represented by the outer scan label. -/
private def pairDvdLiftCfg (input : List (Option Bool))
    (cfg : unaryDvdComputer.Cfg) : pairDvdComputer.Cfg where
  l := match cfg.l with
    | none => some .scan
    | some label => some (.dvd label)
  var := ⟨none, cfg.var⟩
  stk := pairDvdStackContents input cfg.stk

private theorem pairDvdStackContents_update
    (input : List (Option Bool))
    (contents : (index : DvdStack) → List (DvdAlphabet index))
    (index : DvdStack) (value : List (DvdAlphabet index)) :
    Function.update (pairDvdStackContents input contents) (.inr index) value =
      pairDvdStackContents input (Function.update contents index value) := by
  funext target
  cases target with
  | inl _ =>
      simp [pairDvdStackContents, Function.update]
  | inr other =>
      by_cases h : other = index
      · subst other
        simp [pairDvdStackContents, Function.update]
      · simp [pairDvdStackContents, Function.update, h]

private theorem liftDvd_stepAux
    (stmt : TM2.Stmt DvdAlphabet DvdLabel DvdState)
    (state : DvdState)
    (contents : (index : DvdStack) → List (DvdAlphabet index))
    (input : List (Option Bool)) :
    TM2.stepAux (liftDvdStmt stmt) ⟨none, state⟩
        (pairDvdStackContents input contents) =
      pairDvdLiftCfg input (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push index write next ih =>
      simp only [liftDvdStmt, TM2.stepAux]
      rw [pairDvdStackContents_update]
      exact ih _ _
  | peek index read next ih =>
      simpa only [liftDvdStmt, TM2.stepAux, pairDvdStackContents,
        pairDvdSetComponent] using
          ih (read state (contents index).head?) contents
  | pop index read next ih =>
      simp only [liftDvdStmt, TM2.stepAux, pairDvdStackContents,
        pairDvdSetComponent]
      rw [pairDvdStackContents_update]
      exact ih _ _
  | load update next ih =>
      simpa only [liftDvdStmt, TM2.stepAux, pairDvdSetComponent] using
        ih (update state) contents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftDvdStmt, TM2.stepAux, h, cond_true] using
          ihYes state contents
      · simpa only [liftDvdStmt, TM2.stepAux, h, cond_false] using
          ihNo state contents
  | goto next =>
      rfl
  | halt =>
      rfl

private theorem pairDvd_lift_step
    (input : List (Option Bool)) (label : DvdLabel) (state : DvdState)
    (contents : (index : DvdStack) → List (DvdAlphabet index)) :
    pairDvdComputer.step
        (pairDvdLiftCfg input ⟨some label, state, contents⟩) =
      some (pairDvdLiftCfg input
        (TM2.stepAux (unaryDvdProgram label) state contents)) := by
  simp only [pairDvdComputer, FinTM2.step, pairDvdLiftCfg,
    pairDvdProgram, unaryDvdComputer, TM2.step]
  exact congrArg some (liftDvd_stepAux _ _ _ _)

private theorem unaryDvd_iterate_none (steps : ℕ) :
    (flip Option.bind unaryDvdComputer.step)^[steps]
        (none : Option unaryDvdComputer.Cfg) = none := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      rfl

private theorem pairDvd_iterate_lift
    (steps : ℕ) (input : List (Option Bool))
    (start finish : unaryDvdComputer.Cfg)
    (hrun :
      (flip Option.bind unaryDvdComputer.step)^[steps] (some start) =
        some finish) :
    (flip Option.bind pairDvdComputer.step)^[steps]
        (some (pairDvdLiftCfg input start)) =
      some (pairDvdLiftCfg input finish) := by
  induction steps generalizing start with
  | zero =>
      simpa using congrArg (Option.map (pairDvdLiftCfg input)) hrun
  | succ steps ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      change (flip Option.bind unaryDvdComputer.step)^[steps]
          (unaryDvdComputer.step start) = some finish at hrun
      change (flip Option.bind pairDvdComputer.step)^[steps]
          (pairDvdComputer.step (pairDvdLiftCfg input start)) =
        some (pairDvdLiftCfg input finish)
      cases hlabel : start.l with
      | none =>
          have hnone : unaryDvdComputer.step start = none := by
            rcases start with ⟨current, state, contents⟩
            change current = none at hlabel
            subst current
            rfl
          rw [hnone] at hrun
          rw [unaryDvd_iterate_none] at hrun
          contradiction
      | some label =>
          let middle := TM2.stepAux (unaryDvdProgram label) start.var start.stk
          have hstep : unaryDvdComputer.step start = some middle := by
            rcases start with ⟨current, state, contents⟩
            simp [unaryDvdComputer, FinTM2.step] at hlabel ⊢
            subst current
            rfl
          rw [hstep] at hrun
          have hcfg :
              start = ⟨some label, start.var, start.stk⟩ := by
            rcases start with ⟨current, state, contents⟩
            change current = some label at hlabel
            subst current
            rfl
          rw [show pairDvdComputer.step (pairDvdLiftCfg input start) =
              some (pairDvdLiftCfg input middle) by
            rw [hcfg]
            simpa [middle] using
              pairDvd_lift_step input label start.var start.stk]
          exact ih middle hrun

private def pairDvd_lift_evals
    (input : List (Option Bool)) {start finish : unaryDvdComputer.Cfg}
    {bound : ℕ}
    (hrun : EvalsToInTime unaryDvdComputer.step start (some finish) bound) :
    EvalsToInTime pairDvdComputer.step
      (pairDvdLiftCfg input start) (some (pairDvdLiftCfg input finish)) bound where
  steps := hrun.steps
  evals_in_steps := pairDvd_iterate_lift hrun.steps input start finish
    hrun.evals_in_steps
  steps_le_m := hrun.steps_le_m

private def pairDvdEvalsToInTimeOne
    {start finish : pairDvdComputer.Cfg}
    (hstep : pairDvdComputer.step start = some finish) :
    EvalsToInTime pairDvdComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem pairDvd_step_scan_some
    (bit : Bool) (input : List (Option Bool)) (field output : List Bool) :
    pairDvdComputer.step
        (pairDvdLiftCfg (some bit :: input)
          (dvdCfg none dvdInitialState field [] [] [] output)) =
      some (pairDvdLiftCfg input
        (dvdCfg none dvdInitialState (bit :: field) [] [] [] output)) := by
  simp [pairDvdComputer, FinTM2.step, pairDvdLiftCfg, pairDvdProgram,
    pairDvdStackContents, dvdCfg, dvdStackContents, PairDvdAlphabet,
    pairDvdInitialState, pairDvdObserve, pairDvdObservedPresent,
    pairDvdObservedSymbol, pairDvdObservedBit, pairDvdResetObserved,
    Function.update]
  funext index
  cases index with
  | inl _ => rfl
  | inr index =>
      cases index <;> rfl

private theorem pairDvd_step_scan_separator
    (input : List (Option Bool)) (field output : List Bool) :
    pairDvdComputer.step
        (pairDvdLiftCfg (none :: input)
          (dvdCfg none dvdInitialState field [] [] [] output)) =
      some (pairDvdLiftCfg input
        (dvdCfg (some .scanDividend) dvdInitialState
          field [] [] [] output)) := by
  simp [pairDvdComputer, FinTM2.step, pairDvdLiftCfg, pairDvdProgram,
    pairDvdStackContents, dvdCfg, dvdStackContents, PairDvdAlphabet,
    pairDvdInitialState, pairDvdObserve, pairDvdObservedPresent,
    pairDvdObservedSymbol, pairDvdResetObserved, Function.update]
  funext index
  cases index with
  | inl _ => rfl
  | inr index =>
      cases index <;> rfl

private def pairDvd_scan_bits_evals
    (bits : List Bool) (input : List (Option Bool))
    (field output : List Bool) :
    EvalsToInTime pairDvdComputer.step
      (pairDvdLiftCfg (bits.map some ++ input)
        (dvdCfg none dvdInitialState field [] [] [] output))
      (some (pairDvdLiftCfg input
        (dvdCfg none dvdInitialState
          (bits.reverse ++ field) [] [] [] output)))
      bits.length := by
  induction bits generalizing field with
  | nil =>
      exact
        { steps := 0
          evals_in_steps := rfl
          steps_le_m := Nat.le_refl 0 }
  | cons bit bits ih =>
      let middle := pairDvdLiftCfg (bits.map some ++ input)
        (dvdCfg none dvdInitialState (bit :: field) [] [] [] output)
      have hone : EvalsToInTime pairDvdComputer.step
          (pairDvdLiftCfg ((bit :: bits).map some ++ input)
            (dvdCfg none dvdInitialState field [] [] [] output))
          (some middle) 1 :=
        pairDvdEvalsToInTimeOne (by
          simpa [middle] using pairDvd_step_scan_some bit
            (bits.map some ++ input) field output)
      have hrest := ih (bit :: field)
      have htrans := EvalsToInTime.trans pairDvdComputer.step
        1 bits.length
        (pairDvdLiftCfg ((bit :: bits).map some ++ input)
          (dvdCfg none dvdInitialState field [] [] [] output))
        middle
        (some (pairDvdLiftCfg input
          (dvdCfg none dvdInitialState
            ((bit :: bits).reverse ++ field) [] [] [] output)))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_comm] using htrans

private def pairDvd_parse_segment_evals
    (bits : List Bool) (input : List (Option Bool)) (output : List Bool) :
    EvalsToInTime pairDvdComputer.step
      (pairDvdLiftCfg (RawNatList.segment bits ++ input)
        (dvdCfg none dvdInitialState [] [] [] [] output))
      (some (pairDvdLiftCfg input
        (dvdCfg (some .scanDividend) dvdInitialState
          bits [] [] [] output)))
      (bits.length + 1) := by
  let middle := pairDvdLiftCfg (none :: input)
    (dvdCfg none dvdInitialState bits [] [] [] output)
  have hbits := pairDvd_scan_bits_evals bits.reverse (none :: input) [] output
  have hseparator := pairDvdEvalsToInTimeOne
    (pairDvd_step_scan_separator input bits output)
  have htrans := EvalsToInTime.trans pairDvdComputer.step
    bits.length 1
    (pairDvdLiftCfg (RawNatList.segment bits ++ input)
      (dvdCfg none dvdInitialState [] [] [] [] output))
    middle
    (some (pairDvdLiftCfg input
      (dvdCfg (some .scanDividend) dvdInitialState
        bits [] [] [] output)))
    (by simpa [middle, RawNatList.segment] using hbits)
    (by simpa [middle] using hseparator)
  exact evalsToInTimeMono htrans (by omega)

private noncomputable def pairDvd_pair_evals
    (pair : ℕ × ℕ) (input : List (Option Bool)) (output : List Bool) :
    EvalsToInTime pairDvdComputer.step
      (pairDvdLiftCfg
        (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
        (dvdCfg none dvdInitialState [] [] [] [] output))
      (some (pairDvdLiftCfg input
        (dvdCfg none dvdInitialState [] [] [] []
          (decide (pair.2 ∣ pair.1) :: output))))
      (7 * (UnaryNatPair.encode pair).length + 17) := by
  have hparse := pairDvd_parse_segment_evals
    (UnaryNatPair.encode pair) input output
  have hcomponent := pairDvd_lift_evals input
    (unaryDvd_evals_with_output pair output)
  have htrans := EvalsToInTime.trans pairDvdComputer.step
    ((UnaryNatPair.encode pair).length + 1)
    (6 * (UnaryNatPair.encode pair).length + 16)
    (pairDvdLiftCfg
      (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
      (dvdCfg none dvdInitialState [] [] [] [] output))
    (pairDvdLiftCfg input
      (dvdCfg (some .scanDividend) dvdInitialState
        (UnaryNatPair.encode pair) [] [] [] output))
    (some (pairDvdLiftCfg input
      (dvdCfg none dvdInitialState [] [] [] []
        (decide (pair.2 ∣ pair.1) :: output))))
    hparse hcomponent
  exact evalsToInTimeMono htrans (by omega)

@[simp]
theorem RawUnaryPairList.encode_cons
    (pair : ℕ × ℕ) (pairs : List (ℕ × ℕ)) :
    RawUnaryPairList.encode (pair :: pairs) =
      RawUnaryPairList.encode pairs ++
        RawNatList.segment (UnaryNatPair.encode pair) := by
  simp [RawUnaryPairList.encode, List.reverse_cons, List.flatMap_append]

@[simp]
theorem RawUnaryPairList.encode_length (pairs : List (ℕ × ℕ)) :
    (RawUnaryPairList.encode pairs).length =
      ((pairs.map fun pair => (UnaryNatPair.encode pair).length).sum +
        pairs.length) := by
  induction pairs with
  | nil => simp [RawUnaryPairList.encode]
  | cons pair pairs ih =>
      rw [RawUnaryPairList.encode_cons, List.length_append, ih]
      simp [RawNatList.segment]
      omega

/-- Including one separator per pair, the complete driver input for candidate
`n` remains quadratic in the padded candidate. -/
theorem trialDivisionPairStream_length_le (n : ℕ) :
    (RawUnaryPairList.encode (trialDivisionPairs n)).length ≤
      (2 * n + 1) * (n - 2) := by
  rw [RawUnaryPairList.encode_length, trialDivisionPairs_length]
  calc
    ((trialDivisionPairs n).map fun pair =>
        (UnaryNatPair.encode pair).length).sum + (n - 2) =
        trialDivisionInputSize n + (n - 2) := by
          rfl
    _ ≤ 2 * n * (n - 2) + (n - 2) :=
      Nat.add_le_add_right (trialDivisionInputSize_le n) (n - 2)
    _ = (2 * n + 1) * (n - 2) := by ring

private noncomputable def pairDvd_pairs_evals
    (pairs : List (ℕ × ℕ)) (input : List (Option Bool))
    (output : List Bool) :
    EvalsToInTime pairDvdComputer.step
      (pairDvdLiftCfg (RawUnaryPairList.encode pairs ++ input)
        (dvdCfg none dvdInitialState [] [] [] [] output))
      (some (pairDvdLiftCfg input
        (dvdCfg none dvdInitialState [] [] [] []
          (pairDivisionResults pairs ++ output))))
      (17 * (RawUnaryPairList.encode pairs).length) := by
  induction pairs generalizing input output with
  | nil =>
      exact
        { steps := 0
          evals_in_steps := rfl
          steps_le_m := Nat.le_refl 0 }
  | cons pair pairs ih =>
      let middle := pairDvdLiftCfg
        (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
        (dvdCfg none dvdInitialState [] [] [] []
          (pairDivisionResults pairs ++ output))
      have hfirst : EvalsToInTime pairDvdComputer.step
          (pairDvdLiftCfg
            (RawUnaryPairList.encode (pair :: pairs) ++ input)
            (dvdCfg none dvdInitialState [] [] [] [] output))
          (some middle)
          (17 * (RawUnaryPairList.encode pairs).length) := by
        simpa [middle, RawUnaryPairList.encode_cons, List.append_assoc] using
          ih (RawNatList.segment (UnaryNatPair.encode pair) ++ input) output
      have hsecond : EvalsToInTime pairDvdComputer.step middle
          (some (pairDvdLiftCfg input
            (dvdCfg none dvdInitialState [] [] [] []
              (pairDivisionResults (pair :: pairs) ++ output))))
          (7 * (UnaryNatPair.encode pair).length + 17) := by
        simpa [middle, pairDivisionResults, List.append_assoc] using
          pairDvd_pair_evals pair input
            (pairDivisionResults pairs ++ output)
      have htrans := EvalsToInTime.trans pairDvdComputer.step
        (17 * (RawUnaryPairList.encode pairs).length)
        (7 * (UnaryNatPair.encode pair).length + 17)
        (pairDvdLiftCfg
          (RawUnaryPairList.encode (pair :: pairs) ++ input)
          (dvdCfg none dvdInitialState [] [] [] [] output))
        middle
        (some (pairDvdLiftCfg input
          (dvdCfg none dvdInitialState [] [] [] []
            (pairDivisionResults (pair :: pairs) ++ output))))
        hfirst hsecond
      apply evalsToInTimeMono htrans
      simp [RawUnaryPairList.encode_cons, RawNatList.segment]
      omega

private theorem pairDvd_step_scan_nil (output : List Bool) :
    pairDvdComputer.step
        (pairDvdLiftCfg []
          (dvdCfg none dvdInitialState [] [] [] [] output)) =
      some (haltList pairDvdComputer output) := by
  simp [pairDvdComputer, FinTM2.step, pairDvdLiftCfg, pairDvdProgram,
    pairDvdStackContents, dvdCfg, dvdStackContents, PairDvdAlphabet,
    pairDvdInitialState, pairDvdObserve, pairDvdObservedPresent,
    haltList, Function.update]
  funext index
  cases index with
  | inl _ => rfl
  | inr index =>
      cases index <;> rfl

private theorem pairDvd_initList_eq_cfg (input : List (Option Bool)) :
    initList pairDvdComputer input =
      pairDvdLiftCfg input
        (dvdCfg none dvdInitialState [] [] [] [] []) := by
  unfold initList pairDvdLiftCfg pairDvdComputer pairDvdInitialState dvdCfg
  congr
  funext index
  cases index with
  | inl _ => rfl
  | inr index =>
      cases index <;> rfl

/-- The repeated driver maps every padded pair field to its divisibility bit
in at most `17s + 1` steps for actual stream length `s`. -/
noncomputable def pairDvd_outputsInTime (pairs : List (ℕ × ℕ)) :
    TM2OutputsInTime pairDvdComputer (RawUnaryPairList.encode pairs)
      (some (pairDivisionResults pairs))
      (17 * (RawUnaryPairList.encode pairs).length + 1) := by
  have hpairs := pairDvd_pairs_evals pairs [] []
  have hfinal := pairDvdEvalsToInTimeOne
    (pairDvd_step_scan_nil (pairDivisionResults pairs))
  have htrans := EvalsToInTime.trans pairDvdComputer.step
    (17 * (RawUnaryPairList.encode pairs).length) 1
    (pairDvdLiftCfg (RawUnaryPairList.encode pairs)
      (dvdCfg none dvdInitialState [] [] [] [] []))
    (pairDvdLiftCfg []
      (dvdCfg none dvdInitialState [] [] [] []
        (pairDivisionResults pairs)))
    (some (haltList pairDvdComputer (pairDivisionResults pairs)))
    (by simpa using hpairs) hfinal
  rw [TM2OutputsInTime, pairDvd_initList_eq_cfg]
  simp only [Option.map_some]
  exact evalsToInTimeMono htrans (by omega)

/-- Genuine linear time in the padded pair-stream representation.  Combined
with the separate quadratic stream-size bound, this is the repeated
divisibility stage needed by bounded trial division. -/
noncomputable def pairDivisionResultsComputableInPolyTime :
    @TM2ComputableInPolyTime (List (ℕ × ℕ)) (List Bool)
      RawUnaryPairList.finEncoding RawBoolList.finEncoding
      pairDivisionResults where
  tm := pairDvdComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := 17 * Polynomial.X + 1
  outputsFun pairs := by
    simpa [RawUnaryPairList.finEncoding, RawBoolList.finEncoding, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_natCast, Polynomial.eval_X] using
        pairDvd_outputsInTime pairs

/-- Fold a stream of divisibility results into the assertion that every result
is false.  The accumulator form matches the finite-machine invariant. -/
def allFalseFrom : Bool → List Bool → Bool
  | aggregate, [] => aggregate
  | aggregate, result :: results =>
      allFalseFrom (aggregate && !result) results

/-- `true` exactly when the input stream contains no `true` result. -/
def allFalse (results : List Bool) : Bool :=
  allFalseFrom true results

@[simp]
theorem allFalseFrom_false (results : List Bool) :
    allFalseFrom false results = false := by
  induction results with
  | nil => rfl
  | cons result results ih => simp [allFalseFrom, ih]

/-- The exact Boolean result stream produced by applying divisibility to every
padded trial pair for `n`. -/
def trialDivisionResults (n : ℕ) : List Bool :=
  (trialDivisionPairs n).map fun pair => decide (pair.2 ∣ pair.1)

@[simp]
theorem pairDivisionResults_trialDivisionPairs (n : ℕ) :
    pairDivisionResults (trialDivisionPairs n) = trialDivisionResults n :=
  rfl

private theorem allFalse_map_dvd (n : ℕ) (divisors : List ℕ) :
    allFalse (divisors.map fun d => decide (d ∣ n)) =
      divisors.all fun d => decide (¬d ∣ n) := by
  induction divisors with
  | nil => rfl
  | cons d divisors ih =>
      by_cases hd : d ∣ n
      · simp [allFalse, allFalseFrom, hd, allFalseFrom_false]
      · simpa [allFalse, allFalseFrom, hd] using ih

/-- Folding the concrete divisibility-result stream is the Boolean
proper-divisor test used by `trialPrime`. -/
theorem allFalse_trialDivisionResults (n : ℕ) :
    allFalse (trialDivisionResults n) =
      (trialDivisors n).all fun d => decide (¬d ∣ n) := by
  rw [trialDivisionResults, trialDivisionPairs, List.map_map]
  simpa [Function.comp_def] using allFalse_map_dvd n (trialDivisors n)

/-- The executable prime predicate separates the lower-bound check from the
checked Boolean aggregation of all divisibility results. -/
theorem trialPrime_eq_lowerBound_and_allFalse (n : ℕ) :
    trialPrime n =
      (decide (2 ≤ n) && allFalse (trialDivisionResults n)) := by
  rw [trialPrime, allFalse_trialDivisionResults]

/-- Bertrand candidates are at least two, so their trial-prime decision is
exactly the aggregate of their divisibility results. -/
theorem trialPrime_eq_allFalse_trialDivisionResults
    {n : ℕ} (hn : 2 ≤ n) :
    trialPrime n = allFalse (trialDivisionResults n) := by
  rw [trialPrime_eq_lowerBound_and_allFalse]
  simp [hn]

/-- On candidates at least two, the Boolean fold accepts exactly the natural
primes. -/
theorem allFalse_trialDivisionResults_eq_true_iff
    {n : ℕ} (hn : 2 ≤ n) :
    allFalse (trialDivisionResults n) = true ↔ n.Prime := by
  rw [← trialPrime_eq_allFalse_trialDivisionResults hn]
  exact trialPrime_eq_true_iff n

/-- Input and output stacks for the Boolean result fold. -/
inductive AllFalseStack
  | input
  | output
  deriving DecidableEq, Fintype

/-- The fold needs a single scanning label. -/
inductive AllFalseLabel
  | scan
  deriving DecidableEq, Fintype

/-- Finite control records the most recent pop and the running conjunction. -/
structure AllFalseState where
  observed : Option Bool
  aggregate : Bool
  deriving DecidableEq, Fintype

private def allFalseInitialState : AllFalseState :=
  ⟨none, true⟩

private def allFalseObserve
    (state : AllFalseState) : Option Bool → AllFalseState
  | some result => ⟨some result, state.aggregate && !result⟩
  | none => ⟨none, state.aggregate⟩

private def allFalseObservedPresent : AllFalseState → Bool
  | ⟨some _, _⟩ => true
  | _ => false

private def allFalseAggregate (state : AllFalseState) : Bool :=
  state.aggregate

private def AllFalseAlphabet (_index : AllFalseStack) : Type :=
  Bool

/-- Scan the result stream once, conjoin the negated results in finite control,
and emit the final Boolean. -/
def allFalseProgram :
    AllFalseLabel → TM2.Stmt AllFalseAlphabet AllFalseLabel AllFalseState
  | .scan =>
      .pop .input allFalseObserve <|
        .branch allFalseObservedPresent
          (.goto fun _ => .scan)
          (.push .output allFalseAggregate <|
            .load (fun _ => allFalseInitialState) .halt)

/-- Concrete two-stack finite machine for Boolean result aggregation. -/
def allFalseComputer : FinTM2 where
  K := AllFalseStack
  k₀ := .input
  k₁ := .output
  Γ := AllFalseAlphabet
  Λ := AllFalseLabel
  main := .scan
  σ := AllFalseState
  initialState := allFalseInitialState
  Γk₀Fin := Bool.fintype
  m := allFalseProgram

private def allFalseStackContents
    (input output : List Bool) :
    (index : AllFalseStack) → List (AllFalseAlphabet index)
  | .input => input
  | .output => output

private def allFalseCfg (label : Option AllFalseLabel)
    (state : AllFalseState) (input output : List Bool) :
    allFalseComputer.Cfg where
  l := label
  var := state
  stk := allFalseStackContents input output

private def allFalseEvalsToInTimeOne
    {start finish : allFalseComputer.Cfg}
    (hstep : allFalseComputer.step start = some finish) :
    EvalsToInTime allFalseComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem allFalse_step_cons
    (result : Bool) (results output : List Bool) (state : AllFalseState) :
    allFalseComputer.step
        (allFalseCfg (some .scan) state (result :: results) output) =
      some (allFalseCfg (some .scan)
        (allFalseObserve state (some result)) results output) := by
  rcases state with ⟨observed, aggregate⟩
  simp [allFalseComputer, FinTM2.step, allFalseCfg, allFalseProgram,
    allFalseStackContents, AllFalseAlphabet, allFalseObserve,
    allFalseObservedPresent, Function.update]
  funext index
  cases index <;> rfl

private theorem allFalse_step_nil
    (output : List Bool) (state : AllFalseState) :
    allFalseComputer.step
        (allFalseCfg (some .scan) state [] output) =
      some (allFalseCfg none allFalseInitialState []
        (state.aggregate :: output)) := by
  rcases state with ⟨observed, aggregate⟩
  simp [allFalseComputer, FinTM2.step, allFalseCfg, allFalseProgram,
    allFalseStackContents, AllFalseAlphabet, allFalseObserve,
    allFalseObservedPresent, allFalseAggregate, allFalseInitialState,
    Function.update]
  funext index
  cases index <;> rfl

private def allFalse_scan_evals
    (results output : List Bool) (state : AllFalseState) :
    EvalsToInTime allFalseComputer.step
      (allFalseCfg (some .scan) state results output)
      (some (allFalseCfg none allFalseInitialState []
        (allFalseFrom state.aggregate results :: output)))
      (results.length + 1) := by
  induction results generalizing state with
  | nil =>
      simpa [allFalseFrom] using allFalseEvalsToInTimeOne
        (allFalse_step_nil output state)
  | cons result results ih =>
      let middle := allFalseCfg (some .scan)
        (allFalseObserve state (some result)) results output
      have hone : EvalsToInTime allFalseComputer.step
          (allFalseCfg (some .scan) state (result :: results) output)
          (some middle) 1 :=
        allFalseEvalsToInTimeOne (by
          simpa [middle] using allFalse_step_cons result results output state)
      have hrest := ih (allFalseObserve state (some result))
      have htrans := EvalsToInTime.trans allFalseComputer.step
        1 (results.length + 1)
        (allFalseCfg (some .scan) state (result :: results) output)
        middle
        (some (allFalseCfg none allFalseInitialState []
          (allFalseFrom state.aggregate (result :: results) :: output)))
        hone
        (by
          simpa [middle, allFalseFrom, allFalseObserve] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrans

private theorem allFalse_initList_eq_cfg (results : List Bool) :
    initList allFalseComputer results =
      allFalseCfg (some .scan) allFalseInitialState results [] := by
  unfold initList allFalseCfg
  congr
  funext index
  cases index <;> rfl

private theorem allFalse_haltList_eq_cfg (result : Bool) :
    haltList allFalseComputer [result] =
      allFalseCfg none allFalseInitialState [] [result] := by
  unfold haltList allFalseCfg
  congr
  funext index
  cases index <;> rfl

/-- Boolean aggregation takes at most one scan step per result plus the final
empty-input step. -/
def allFalse_outputsInTime (results : List Bool) :
    TM2OutputsInTime allFalseComputer results
      (some (encodeBool (allFalse results))) (results.length + 1) := by
  have hscan := allFalse_scan_evals results [] allFalseInitialState
  rw [TM2OutputsInTime, allFalse_initList_eq_cfg]
  simp only [Option.map_some, encodeBool, List.pure_def]
  rw [allFalse_haltList_eq_cfg]
  simpa [allFalse, allFalseInitialState, encodeBool] using hscan

/-- Genuine linear-time finite-machine aggregation of a Boolean result list. -/
noncomputable def allFalseComputableInPolyTime :
    @TM2ComputableInPolyTime (List Bool) Bool RawBoolList.finEncoding
      finEncodingBoolBool allFalse where
  tm := allFalseComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun results := by
    simpa [RawBoolList.finEncoding, finEncodingBoolBool, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X] using
        allFalse_outputsInTime results

/-! ## Fused repeated divisibility and Boolean aggregation

The standalone repeated-divisibility and Boolean-fold machines expose useful
component contracts. For the prime filter it is cheaper to fuse them: after
each invocation of `unaryDvdComputer`, consume its one-bit output immediately
and retain only the running conjunction in finite control. This avoids an
intermediate result list while preserving the exact padded-pair input syntax.
-/

/-- The Boolean accepted by the fused padded-pair divisibility pass. -/
def allFalseDivisibilityResults (pairs : List (ℕ × ℕ)) : Bool :=
  allFalse (pairDivisionResults pairs)

/-- On the exact trial-pair stream for a candidate at least two, the fused
pass accepts exactly the natural primes. -/
theorem allFalseDivisibilityResults_trialDivisionPairs_eq_true_iff
    {n : ℕ} (hn : 2 ≤ n) :
    allFalseDivisibilityResults (trialDivisionPairs n) = true ↔ n.Prime := by
  simpa [allFalseDivisibilityResults,
    pairDivisionResults_trialDivisionPairs] using
      allFalse_trialDivisionResults_eq_true_iff hn

/-- The fused machine uses the repeated driver's raw input and divisibility
stacks. The divisibility output stack is reused as the final Boolean output
after every intermediate result has been consumed. -/
abbrev PairAllFalseStack := PairDvdStack

/-- Raw-field scanning, one divisibility invocation, and result aggregation. -/
inductive PairAllFalseLabel
  | scan
  | dvd (label : DvdLabel)
  | aggregate
  deriving DecidableEq, Fintype

/-- Finite control combines the outer raw-field observation, the component
state, and the running assertion that no processed divisor succeeded. -/
structure PairAllFalseState where
  observed : Option (Option Bool)
  dvd : DvdState
  aggregate : Bool
  deriving DecidableEq, Fintype

private def pairAllFalseInitialState : PairAllFalseState :=
  ⟨none, dvdInitialState, true⟩

private def pairAllFalseObserve
    (state : PairAllFalseState)
    (observed : Option (Option Bool)) : PairAllFalseState :=
  { state with observed := observed }

private def pairAllFalseResetObserved
    (state : PairAllFalseState) : PairAllFalseState :=
  { state with observed := none }

private def pairAllFalseSetComponent
    (state : PairAllFalseState) (dvd : DvdState) : PairAllFalseState :=
  { state with dvd := dvd }

private def pairAllFalseObserveResult
    (state : PairAllFalseState) : Option Bool → PairAllFalseState
  | some result =>
      { state with
        observed := none
        aggregate := state.aggregate && !result }
  | none => { state with observed := none }

private def pairAllFalseObservedPresent : PairAllFalseState → Bool
  | ⟨some _, _, _⟩ => true
  | _ => false

private def pairAllFalseObservedSymbol : PairAllFalseState → Bool
  | ⟨some (some _), _, _⟩ => true
  | _ => false

private def pairAllFalseObservedBit : PairAllFalseState → Bool
  | ⟨some (some bit), _, _⟩ => bit
  | _ => false

private def pairAllFalseAggregate (state : PairAllFalseState) : Bool :=
  state.aggregate

private def PairAllFalseAlphabet : PairAllFalseStack → Type :=
  PairDvdAlphabet

/-- Lift the checked unary divisibility program, redirecting its halt to the
one-step aggregate phase rather than accumulating a result list. -/
private def liftDvdAllFalseStmt :
    TM2.Stmt DvdAlphabet DvdLabel DvdState →
      TM2.Stmt PairAllFalseAlphabet PairAllFalseLabel PairAllFalseState
  | .push index write next =>
      .push (.inr index) (fun state => write state.dvd)
        (liftDvdAllFalseStmt next)
  | .peek index read next =>
      .peek (.inr index)
        (fun state observed =>
          pairAllFalseSetComponent state (read state.dvd observed))
        (liftDvdAllFalseStmt next)
  | .pop index read next =>
      .pop (.inr index)
        (fun state observed =>
          pairAllFalseSetComponent state (read state.dvd observed))
        (liftDvdAllFalseStmt next)
  | .load update next =>
      .load (fun state =>
        pairAllFalseSetComponent state (update state.dvd))
        (liftDvdAllFalseStmt next)
  | .branch test yes no =>
      .branch (fun state => test state.dvd)
        (liftDvdAllFalseStmt yes) (liftDvdAllFalseStmt no)
  | .goto next => .goto (fun state => .dvd (next state.dvd))
  | .halt => .goto fun _ => .aggregate

/-- Repeatedly restore one padded pair, run divisibility, fold its output bit,
and finally emit the single aggregate Boolean. -/
def pairAllFalseProgram :
    PairAllFalseLabel →
      TM2.Stmt PairAllFalseAlphabet PairAllFalseLabel PairAllFalseState
  | .scan =>
      .pop (.inl ()) pairAllFalseObserve <|
        .branch pairAllFalseObservedPresent
          (.branch pairAllFalseObservedSymbol
            (.push (.inr .input) pairAllFalseObservedBit <|
              .load pairAllFalseResetObserved <|
                .goto fun _ => .scan)
            (.load pairAllFalseResetObserved <|
              .goto fun _ => .dvd .scanDividend))
          (.push (.inr .output) pairAllFalseAggregate <|
            .load (fun _ => pairAllFalseInitialState) .halt)
  | .dvd label => liftDvdAllFalseStmt (unaryDvdProgram label)
  | .aggregate =>
      .pop (.inr .output) pairAllFalseObserveResult <|
        .goto fun _ => .scan

/-- Concrete finite machine fusing repeated padded divisibility with the
Boolean no-divisor fold. -/
def pairAllFalseComputer : FinTM2 where
  K := PairAllFalseStack
  k₀ := .inl ()
  k₁ := .inr .output
  Γ := PairAllFalseAlphabet
  Λ := PairAllFalseLabel
  main := .scan
  σ := PairAllFalseState
  initialState := pairAllFalseInitialState
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := pairAllFalseProgram

private def pairAllFalseStackContents
    (input : List (Option Bool))
    (contents : (index : DvdStack) → List (DvdAlphabet index)) :
    (index : PairAllFalseStack) → List (PairAllFalseAlphabet index) :=
  pairDvdStackContents input contents

private def pairAllFalseCfg (label : Option PairAllFalseLabel)
    (state : PairAllFalseState) (input : List (Option Bool))
    (contents : (index : DvdStack) → List (DvdAlphabet index)) :
    pairAllFalseComputer.Cfg where
  l := label
  var := state
  stk := pairAllFalseStackContents input contents

private def pairAllFalseScanCfg
    (input : List (Option Bool)) (aggregate : Bool)
    (field output : List Bool) : pairAllFalseComputer.Cfg :=
  pairAllFalseCfg (some .scan) ⟨none, dvdInitialState, aggregate⟩ input
    (dvdStackContents field [] [] [] output)

/-- Embed a divisibility configuration while fixing the raw stream and the
running aggregate. A component halt enters the aggregate phase. -/
private def pairAllFalseLiftCfg (input : List (Option Bool))
    (aggregate : Bool) (cfg : unaryDvdComputer.Cfg) :
    pairAllFalseComputer.Cfg where
  l := match cfg.l with
    | none => some .aggregate
    | some label => some (.dvd label)
  var := ⟨none, cfg.var, aggregate⟩
  stk := pairAllFalseStackContents input cfg.stk

private theorem pairAllFalseStackContents_update
    (input : List (Option Bool))
    (contents : (index : DvdStack) → List (DvdAlphabet index))
    (index : DvdStack) (value : List (DvdAlphabet index)) :
    Function.update (pairAllFalseStackContents input contents)
        (.inr index) value =
      pairAllFalseStackContents input
        (Function.update contents index value) := by
  exact pairDvdStackContents_update input contents index value

private theorem liftDvdAllFalse_stepAux
    (stmt : TM2.Stmt DvdAlphabet DvdLabel DvdState)
    (state : DvdState)
    (contents : (index : DvdStack) → List (DvdAlphabet index))
    (input : List (Option Bool)) (aggregate : Bool) :
    TM2.stepAux (liftDvdAllFalseStmt stmt) ⟨none, state, aggregate⟩
        (pairAllFalseStackContents input contents) =
      pairAllFalseLiftCfg input aggregate
        (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push index write next ih =>
      simp only [liftDvdAllFalseStmt, TM2.stepAux]
      rw [pairAllFalseStackContents_update]
      exact ih _ _
  | peek index read next ih =>
      simpa only [liftDvdAllFalseStmt, TM2.stepAux,
        pairAllFalseStackContents, pairDvdStackContents,
        pairAllFalseSetComponent] using
          ih (read state (contents index).head?) contents
  | pop index read next ih =>
      simp only [liftDvdAllFalseStmt, TM2.stepAux,
        pairAllFalseStackContents, pairDvdStackContents,
        pairAllFalseSetComponent]
      rw [pairDvdStackContents_update]
      simpa only [pairAllFalseStackContents] using ih _ _
  | load update next ih =>
      simpa only [liftDvdAllFalseStmt, TM2.stepAux,
        pairAllFalseSetComponent] using ih (update state) contents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftDvdAllFalseStmt, TM2.stepAux, h, cond_true] using
          ihYes state contents
      · simpa only [liftDvdAllFalseStmt, TM2.stepAux, h, cond_false] using
          ihNo state contents
  | goto next => rfl
  | halt => rfl

private theorem pairAllFalse_lift_step
    (input : List (Option Bool)) (aggregate : Bool)
    (label : DvdLabel) (state : DvdState)
    (contents : (index : DvdStack) → List (DvdAlphabet index)) :
    pairAllFalseComputer.step
        (pairAllFalseLiftCfg input aggregate
          ⟨some label, state, contents⟩) =
      some (pairAllFalseLiftCfg input aggregate
        (TM2.stepAux (unaryDvdProgram label) state contents)) := by
  simp only [pairAllFalseComputer, FinTM2.step, pairAllFalseLiftCfg,
    pairAllFalseProgram, unaryDvdComputer, TM2.step]
  exact congrArg some (liftDvdAllFalse_stepAux _ _ _ _ _)

private theorem pairAllFalse_iterate_lift
    (steps : ℕ) (input : List (Option Bool)) (aggregate : Bool)
    (start finish : unaryDvdComputer.Cfg)
    (hrun :
      (flip Option.bind unaryDvdComputer.step)^[steps] (some start) =
        some finish) :
    (flip Option.bind pairAllFalseComputer.step)^[steps]
        (some (pairAllFalseLiftCfg input aggregate start)) =
      some (pairAllFalseLiftCfg input aggregate finish) := by
  induction steps generalizing start with
  | zero =>
      simpa using congrArg
        (Option.map (pairAllFalseLiftCfg input aggregate)) hrun
  | succ steps ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      change (flip Option.bind unaryDvdComputer.step)^[steps]
          (unaryDvdComputer.step start) = some finish at hrun
      change (flip Option.bind pairAllFalseComputer.step)^[steps]
          (pairAllFalseComputer.step
            (pairAllFalseLiftCfg input aggregate start)) =
        some (pairAllFalseLiftCfg input aggregate finish)
      cases hlabel : start.l with
      | none =>
          have hnone : unaryDvdComputer.step start = none := by
            rcases start with ⟨current, state, contents⟩
            change current = none at hlabel
            subst current
            rfl
          rw [hnone] at hrun
          rw [unaryDvd_iterate_none] at hrun
          contradiction
      | some label =>
          let middle :=
            TM2.stepAux (unaryDvdProgram label) start.var start.stk
          have hstep : unaryDvdComputer.step start = some middle := by
            rcases start with ⟨current, state, contents⟩
            simp [unaryDvdComputer, FinTM2.step] at hlabel ⊢
            subst current
            rfl
          rw [hstep] at hrun
          have hcfg :
              start = ⟨some label, start.var, start.stk⟩ := by
            rcases start with ⟨current, state, contents⟩
            change current = some label at hlabel
            subst current
            rfl
          rw [show pairAllFalseComputer.step
              (pairAllFalseLiftCfg input aggregate start) =
                some (pairAllFalseLiftCfg input aggregate middle) by
            rw [hcfg]
            simpa [middle] using pairAllFalse_lift_step input aggregate
              label start.var start.stk]
          exact ih middle hrun

private def pairAllFalse_lift_evals
    (input : List (Option Bool)) (aggregate : Bool)
    {start finish : unaryDvdComputer.Cfg} {bound : ℕ}
    (hrun : EvalsToInTime unaryDvdComputer.step start
      (some finish) bound) :
    EvalsToInTime pairAllFalseComputer.step
      (pairAllFalseLiftCfg input aggregate start)
      (some (pairAllFalseLiftCfg input aggregate finish)) bound where
  steps := hrun.steps
  evals_in_steps := pairAllFalse_iterate_lift hrun.steps input aggregate
    start finish hrun.evals_in_steps
  steps_le_m := hrun.steps_le_m

private def pairAllFalseEvalsToInTimeOne
    {start finish : pairAllFalseComputer.Cfg}
    (hstep : pairAllFalseComputer.step start = some finish) :
    EvalsToInTime pairAllFalseComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem pairAllFalse_step_scan_some
    (bit : Bool) (input : List (Option Bool))
    (aggregate : Bool) (field output : List Bool) :
    pairAllFalseComputer.step
        (pairAllFalseScanCfg (some bit :: input) aggregate field output) =
      some (pairAllFalseScanCfg input aggregate (bit :: field) output) := by
  simp [pairAllFalseComputer, FinTM2.step, pairAllFalseScanCfg,
    pairAllFalseCfg, pairAllFalseProgram, pairAllFalseStackContents,
    pairDvdStackContents, dvdStackContents, PairAllFalseAlphabet,
    PairDvdAlphabet, pairAllFalseObserve, pairAllFalseObservedPresent,
    pairAllFalseObservedSymbol, pairAllFalseObservedBit,
    pairAllFalseResetObserved, Function.update]
  funext index
  cases index with
  | inl _ => rfl
  | inr index => cases index <;> rfl

private theorem pairAllFalse_step_scan_separator
    (input : List (Option Bool)) (aggregate : Bool)
    (field output : List Bool) :
    pairAllFalseComputer.step
        (pairAllFalseScanCfg (none :: input) aggregate field output) =
      some (pairAllFalseLiftCfg input aggregate
        (dvdCfg (some .scanDividend) dvdInitialState
          field [] [] [] output)) := by
  simp [pairAllFalseComputer, FinTM2.step, pairAllFalseScanCfg,
    pairAllFalseCfg, pairAllFalseLiftCfg, pairAllFalseProgram,
    pairAllFalseStackContents, pairDvdStackContents, dvdCfg,
    dvdStackContents, PairAllFalseAlphabet, PairDvdAlphabet,
    pairAllFalseObserve, pairAllFalseObservedPresent,
    pairAllFalseObservedSymbol, pairAllFalseResetObserved, Function.update]
  funext index
  cases index with
  | inl _ => rfl
  | inr index => cases index <;> rfl

private def pairAllFalse_scan_bits_evals
    (bits : List Bool) (input : List (Option Bool))
    (aggregate : Bool) (field output : List Bool) :
    EvalsToInTime pairAllFalseComputer.step
      (pairAllFalseScanCfg (bits.map some ++ input) aggregate field output)
      (some (pairAllFalseScanCfg input aggregate
        (bits.reverse ++ field) output)) bits.length := by
  induction bits generalizing field with
  | nil => exact EvalsToInTime.refl _ _
  | cons bit bits ih =>
      let middle := pairAllFalseScanCfg (bits.map some ++ input)
        aggregate (bit :: field) output
      have hone : EvalsToInTime pairAllFalseComputer.step
          (pairAllFalseScanCfg ((bit :: bits).map some ++ input)
            aggregate field output)
          (some middle) 1 :=
        pairAllFalseEvalsToInTimeOne (by
          simpa [middle] using pairAllFalse_step_scan_some bit
            (bits.map some ++ input) aggregate field output)
      have hrest := ih (bit :: field)
      have htrans := EvalsToInTime.trans pairAllFalseComputer.step
        1 bits.length
        (pairAllFalseScanCfg ((bit :: bits).map some ++ input)
          aggregate field output)
        middle
        (some (pairAllFalseScanCfg input aggregate
          ((bit :: bits).reverse ++ field) output))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_comm] using htrans

private def pairAllFalse_parse_segment_evals
    (bits : List Bool) (input : List (Option Bool))
    (aggregate : Bool) (output : List Bool) :
    EvalsToInTime pairAllFalseComputer.step
      (pairAllFalseScanCfg (RawNatList.segment bits ++ input)
        aggregate [] output)
      (some (pairAllFalseLiftCfg input aggregate
        (dvdCfg (some .scanDividend) dvdInitialState
          bits [] [] [] output)))
      (bits.length + 1) := by
  let middle := pairAllFalseScanCfg (none :: input) aggregate bits output
  have hbits := pairAllFalse_scan_bits_evals bits.reverse (none :: input)
    aggregate [] output
  have hseparator := pairAllFalseEvalsToInTimeOne
    (pairAllFalse_step_scan_separator input aggregate bits output)
  have htrans := EvalsToInTime.trans pairAllFalseComputer.step
    bits.length 1
    (pairAllFalseScanCfg (RawNatList.segment bits ++ input)
      aggregate [] output)
    middle
    (some (pairAllFalseLiftCfg input aggregate
      (dvdCfg (some .scanDividend) dvdInitialState
        bits [] [] [] output)))
    (by simpa [middle, RawNatList.segment] using hbits)
    (by simpa [middle] using hseparator)
  exact evalsToInTimeMono htrans (by omega)

private theorem pairAllFalse_step_aggregate
    (input : List (Option Bool)) (aggregate result : Bool) :
    pairAllFalseComputer.step
        (pairAllFalseLiftCfg input aggregate
          (dvdCfg none dvdInitialState [] [] [] [] [result])) =
      some (pairAllFalseScanCfg input (aggregate && !result) [] []) := by
  simp [pairAllFalseComputer, FinTM2.step, pairAllFalseLiftCfg,
    pairAllFalseScanCfg, pairAllFalseCfg, pairAllFalseProgram,
    pairAllFalseStackContents, pairDvdStackContents, dvdCfg,
    dvdStackContents, PairAllFalseAlphabet, PairDvdAlphabet,
    pairAllFalseObserveResult]
  funext index
  cases index with
  | inl _ => rfl
  | inr index => cases index <;> rfl

private noncomputable def pairAllFalse_pair_evals
    (pair : ℕ × ℕ) (input : List (Option Bool)) (aggregate : Bool) :
    EvalsToInTime pairAllFalseComputer.step
      (pairAllFalseScanCfg
        (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
        aggregate [] [])
      (some (pairAllFalseScanCfg input
        (aggregate && !decide (pair.2 ∣ pair.1)) [] []))
      (7 * (UnaryNatPair.encode pair).length + 18) := by
  let componentStart := pairAllFalseLiftCfg input aggregate
    (dvdCfg (some .scanDividend) dvdInitialState
      (UnaryNatPair.encode pair) [] [] [] [])
  let componentFinish := pairAllFalseLiftCfg input aggregate
    (dvdCfg none dvdInitialState [] [] [] []
      [decide (pair.2 ∣ pair.1)])
  have hparse := pairAllFalse_parse_segment_evals
    (UnaryNatPair.encode pair) input aggregate []
  have hcomponent := pairAllFalse_lift_evals input aggregate
    (unaryDvd_evals_with_output pair [])
  have haggregate := pairAllFalseEvalsToInTimeOne
    (pairAllFalse_step_aggregate input aggregate
      (decide (pair.2 ∣ pair.1)))
  have hfirst := EvalsToInTime.trans pairAllFalseComputer.step
    ((UnaryNatPair.encode pair).length + 1)
    (6 * (UnaryNatPair.encode pair).length + 16)
    (pairAllFalseScanCfg
      (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
      aggregate [] [])
    componentStart (some componentFinish)
    (by simpa [componentStart] using hparse)
    (by simpa [componentStart, componentFinish] using hcomponent)
  have htrans := EvalsToInTime.trans pairAllFalseComputer.step
    (7 * (UnaryNatPair.encode pair).length + 17) 1
    (pairAllFalseScanCfg
      (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
      aggregate [] [])
    componentFinish
    (some (pairAllFalseScanCfg input
      (aggregate && !decide (pair.2 ∣ pair.1)) [] []))
    (evalsToInTimeMono hfirst (by omega))
    (by simpa [componentFinish] using haggregate)
  exact evalsToInTimeMono htrans (by omega)

private theorem allFalseFrom_eq_and_allFalse
    (aggregate : Bool) (results : List Bool) :
    allFalseFrom aggregate results =
      (aggregate && allFalse results) := by
  cases aggregate with
  | false => exact allFalseFrom_false results
  | true => rfl

private theorem allFalse_cons (result : Bool) (results : List Bool) :
    allFalse (result :: results) = (!result && allFalse results) := by
  simpa [allFalse, allFalseFrom] using
    allFalseFrom_eq_and_allFalse (!result) results

private noncomputable def pairAllFalse_pairs_evals
    (pairs : List (ℕ × ℕ)) (input : List (Option Bool))
    (aggregate : Bool) :
    EvalsToInTime pairAllFalseComputer.step
      (pairAllFalseScanCfg (RawUnaryPairList.encode pairs ++ input)
        aggregate [] [])
      (some (pairAllFalseScanCfg input
        (aggregate && allFalse (pairDivisionResults pairs)) [] []))
      (18 * (RawUnaryPairList.encode pairs).length) := by
  induction pairs generalizing input aggregate with
  | nil =>
      simpa [RawUnaryPairList.encode, pairDivisionResults,
        allFalse, allFalseFrom] using
        (EvalsToInTime.refl pairAllFalseComputer.step
          (pairAllFalseScanCfg input aggregate [] []))
  | cons pair pairs ih =>
      let tailAggregate :=
        aggregate && allFalse (pairDivisionResults pairs)
      let middle := pairAllFalseScanCfg
        (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
        tailAggregate [] []
      have hfirst : EvalsToInTime pairAllFalseComputer.step
          (pairAllFalseScanCfg
            (RawUnaryPairList.encode (pair :: pairs) ++ input)
            aggregate [] [])
          (some middle)
          (18 * (RawUnaryPairList.encode pairs).length) := by
        simpa [middle, tailAggregate, RawUnaryPairList.encode_cons,
          List.append_assoc] using
            ih (RawNatList.segment (UnaryNatPair.encode pair) ++ input)
              aggregate
      have hsecond : EvalsToInTime pairAllFalseComputer.step middle
          (some (pairAllFalseScanCfg input
            (aggregate && allFalse
              (pairDivisionResults (pair :: pairs))) [] []))
          (7 * (UnaryNatPair.encode pair).length + 18) := by
        have hpair := pairAllFalse_pair_evals pair input tailAggregate
        simpa [middle, tailAggregate, pairDivisionResults, allFalse_cons,
          Bool.and_assoc, Bool.and_comm, Bool.and_left_comm] using hpair
      have htrans := EvalsToInTime.trans pairAllFalseComputer.step
        (18 * (RawUnaryPairList.encode pairs).length)
        (7 * (UnaryNatPair.encode pair).length + 18)
        (pairAllFalseScanCfg
          (RawUnaryPairList.encode (pair :: pairs) ++ input)
          aggregate [] [])
        middle
        (some (pairAllFalseScanCfg input
          (aggregate && allFalse
            (pairDivisionResults (pair :: pairs))) [] []))
        hfirst hsecond
      apply evalsToInTimeMono htrans
      simp [RawUnaryPairList.encode_cons, RawNatList.segment]
      omega

private theorem pairAllFalse_step_scan_nil (aggregate : Bool) :
    pairAllFalseComputer.step
        (pairAllFalseScanCfg [] aggregate [] []) =
      some (haltList pairAllFalseComputer [aggregate]) := by
  simp [pairAllFalseComputer, FinTM2.step, pairAllFalseScanCfg,
    pairAllFalseCfg, pairAllFalseProgram, pairAllFalseStackContents,
    pairDvdStackContents, dvdStackContents, PairAllFalseAlphabet,
    PairDvdAlphabet, pairAllFalseObserve, pairAllFalseObservedPresent,
    pairAllFalseAggregate, pairAllFalseInitialState, haltList,
    Function.update]
  funext index
  cases index with
  | inl _ => rfl
  | inr index => cases index <;> rfl

private theorem pairAllFalse_initList_eq_cfg
    (input : List (Option Bool)) :
    initList pairAllFalseComputer input =
      pairAllFalseScanCfg input true [] [] := by
  unfold initList pairAllFalseScanCfg pairAllFalseCfg
    pairAllFalseComputer pairAllFalseInitialState
  congr
  funext index
  cases index with
  | inl _ => rfl
  | inr index => cases index <;> rfl

/-- The fused machine decides whether every padded pair is nondividing in at
most `18s + 1` steps for actual raw stream length `s`. -/
noncomputable def pairAllFalse_outputsInTime
    (pairs : List (ℕ × ℕ)) :
    TM2OutputsInTime pairAllFalseComputer (RawUnaryPairList.encode pairs)
      (some (encodeBool (allFalseDivisibilityResults pairs)))
      (18 * (RawUnaryPairList.encode pairs).length + 1) := by
  have hpairs := pairAllFalse_pairs_evals pairs [] true
  have hfinal := pairAllFalseEvalsToInTimeOne
    (pairAllFalse_step_scan_nil (allFalse (pairDivisionResults pairs)))
  have htrans := EvalsToInTime.trans pairAllFalseComputer.step
    (18 * (RawUnaryPairList.encode pairs).length) 1
    (pairAllFalseScanCfg (RawUnaryPairList.encode pairs) true [] [])
    (pairAllFalseScanCfg []
      (allFalse (pairDivisionResults pairs)) [] [])
    (some (haltList pairAllFalseComputer
      [allFalse (pairDivisionResults pairs)]))
    (by simpa using hpairs) hfinal
  rw [TM2OutputsInTime, pairAllFalse_initList_eq_cfg]
  simp only [Option.map_some, encodeBool, List.pure_def]
  simpa [allFalseDivisibilityResults, Nat.add_comm] using htrans

/-- Genuine linear time for the fused repeated-divisibility/no-divisor pass. -/
noncomputable def allFalseDivisibilityResultsComputableInPolyTime :
    @TM2ComputableInPolyTime (List (ℕ × ℕ)) Bool
      RawUnaryPairList.finEncoding finEncodingBoolBool
      allFalseDivisibilityResults where
  tm := pairAllFalseComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := 18 * Polynomial.X + 1
  outputsFun pairs := by
    simpa [RawUnaryPairList.finEncoding, finEncodingBoolBool, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_natCast, Polynomial.eval_X] using
        pairAllFalse_outputsInTime pairs

/-! ## Unary candidate primality composition

The checked generic control and order-preserving transfer machinery from
`lean-np-hardness` composes the trial-pair generator with the fused
no-divisor pass.  The concrete machine below chooses the second component's
reset state as its external halt state.  Its first generator statement
immediately installs the generator's initial state, so this state choice does
not alter the component execution and makes the final configuration satisfy
mathlib's `haltList` convention.
-/

private def trialDivisionPairsAux :
    TM2ComputableAux Bool (Option Bool) where
  tm := trialDivisionPairComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Option Bool)

private def pairAllFalseAux :
    TM2ComputableAux (Option Bool) Bool where
  tm := pairAllFalseComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl Bool

/-- Concrete sequential machine for generating every padded divisor test and
then accepting exactly when none of them divides the candidate. -/
def unaryCandidatePrimeComputer : FinTM2 :=
  { compositionMachine trialDivisionPairsAux pairAllFalseAux with
      initialState := rightState trialDivisionPairsAux pairAllFalseAux
        pairAllFalseAux.tm.initialState }

private def unaryCandidatePrimeStartCfg
    (state : ControlState trialDivisionPairsAux pairAllFalseAux)
    (input : List Bool) : unaryCandidatePrimeComputer.Cfg where
  l := some (leftLabel trialDivisionPairsAux pairAllFalseAux .scan)
  var := state
  stk := transferLeftStacks trialDivisionPairsAux pairAllFalseAux
    (trialPairStackContents input [] [] [] [] [])

private theorem unaryCandidatePrime_initList_eq_cfg (input : List Bool) :
    initList unaryCandidatePrimeComputer input =
      unaryCandidatePrimeStartCfg
        (rightState trialDivisionPairsAux pairAllFalseAux
          pairAllFalseAux.tm.initialState) input := by
  unfold initList unaryCandidatePrimeComputer compositionMachine
    unaryCandidatePrimeStartCfg trialDivisionPairsAux pairAllFalseAux
    trialDivisionPairComputer pairAllFalseComputer transferLeftStacks
    trialPairStackContents extendStacks leftStacks transferLeftIndex
  congr 2
  funext index
  rcases index with (index | index)
  · rcases index with (index | index)
    · cases index <;> rfl
    · rfl
  · cases index
    rfl

private theorem unaryCandidatePrime_left_init_eq_cfg (input : List Bool) :
    liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
        (liftLeftControlCfg trialDivisionPairsAux pairAllFalseAux
          (initList trialDivisionPairsAux.tm input)) =
      unaryCandidatePrimeStartCfg
        (leftState trialDivisionPairsAux pairAllFalseAux
          trialDivisionPairsAux.tm.initialState) input := by
  simp only [trialDivisionPairsAux]
  rw [trialPair_initList_eq_cfg]
  rfl

private theorem unaryCandidatePrime_start_step (input : List Bool) :
    unaryCandidatePrimeComputer.step
        (unaryCandidatePrimeStartCfg
          (rightState trialDivisionPairsAux pairAllFalseAux
            pairAllFalseAux.tm.initialState) input) =
      unaryCandidatePrimeComputer.step
        (unaryCandidatePrimeStartCfg
          (leftState trialDivisionPairsAux pairAllFalseAux
            trialDivisionPairsAux.tm.initialState) input) := by
  cases input with
  | nil =>
      rfl
  | cons bit input =>
      rfl

private theorem unaryCandidatePrime_init_step (input : List Bool) :
    unaryCandidatePrimeComputer.step
        (initList unaryCandidatePrimeComputer input) =
      unaryCandidatePrimeComputer.step
        (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
          (liftLeftControlCfg trialDivisionPairsAux pairAllFalseAux
            (initList trialDivisionPairsAux.tm input))) := by
  rw [unaryCandidatePrime_initList_eq_cfg,
    unaryCandidatePrime_left_init_eq_cfg]
  exact unaryCandidatePrime_start_step input

private theorem unaryCandidatePrime_haltList_eq (result : Bool) :
    haltList unaryCandidatePrimeComputer [result] =
      rightPhaseCfg trialDivisionPairsAux pairAllFalseAux (fun _ => []) []
        (haltList pairAllFalseAux.tm [result]) := by
  unfold unaryCandidatePrimeComputer compositionMachine haltList rightPhaseCfg
    trialDivisionPairsAux pairAllFalseAux pairAllFalseComputer
  congr 2
  funext index
  rcases index with (index | index)
  · rcases index with (index | index)
    · cases index <;> simp [extendStacks, rightPhaseStacks,
        transferRightIndex]
      all_goals
        intro h
        cases h
    · rcases index with (index | index)
      · cases index
        simp [extendStacks, rightPhaseStacks, transferRightIndex]
        intro h
        cases h
      · cases index <;> simp [extendStacks, rightPhaseStacks,
          transferRightIndex]
        all_goals
          intro h
          cases h
  · cases index
    simp [extendStacks, transferRightIndex]

private theorem unaryCandidatePrime_iterate_init
    (steps : ℕ) (hsteps : 0 < steps) (input : List Bool) :
    (flip Option.bind unaryCandidatePrimeComputer.step)^[steps]
        (some (initList unaryCandidatePrimeComputer input)) =
      (flip Option.bind unaryCandidatePrimeComputer.step)^[steps]
        (some (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
          (liftLeftControlCfg trialDivisionPairsAux pairAllFalseAux
            (initList trialDivisionPairsAux.tm input)))) := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hsteps)
  rw [Function.iterate_succ_apply]
  change
    (flip Option.bind unaryCandidatePrimeComputer.step)^[remaining]
        (unaryCandidatePrimeComputer.step
          (initList unaryCandidatePrimeComputer input)) =
      (flip Option.bind unaryCandidatePrimeComputer.step)^[remaining]
        (unaryCandidatePrimeComputer.step
          (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
            (liftLeftControlCfg trialDivisionPairsAux pairAllFalseAux
              (initList trialDivisionPairsAux.tm input))))
  rw [unaryCandidatePrime_init_step]

private noncomputable def unaryCandidatePrime_generator_evals (n : ℕ) :
    EvalsToInTime unaryCandidatePrimeComputer.step
      (initList unaryCandidatePrimeComputer (unaryEncodeNat n))
      (some (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
        (leftTransferEntryCfg trialDivisionPairsAux pairAllFalseAux
          (haltList trialDivisionPairsAux.tm
            (RawUnaryPairList.encode (trialDivisionPairs n))).var
          (haltList trialDivisionPairsAux.tm
            (RawUnaryPairList.encode (trialDivisionPairs n))).stk)))
      (8 * (n + 1) ^ 2) := by
  let output := RawUnaryPairList.encode (trialDivisionPairs n)
  have hgenerator :
      EvalsToInTime trialDivisionPairsAux.tm.step
        (initList trialDivisionPairsAux.tm (unaryEncodeNat n))
        (some (haltList trialDivisionPairsAux.tm output))
        (8 * (n + 1) ^ 2) := by
    simpa [trialDivisionPairsAux, output] using
      trialDivisionPairs_outputsInTime n
  have hpositive : 0 < hgenerator.steps := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have heq := hgenerator.evals_in_steps
    rw [hzero, Function.iterate_zero_apply] at heq
    injection heq with hcfg
    have hlabels := congrArg
      (fun cfg : trialDivisionPairsAux.tm.Cfg => cfg.l) hcfg
    simp [initList, haltList] at hlabels
  have hleftRun := compositionProgram_left_run_to_transfer
    trialDivisionPairsAux pairAllFalseAux hgenerator.steps
    (initList trialDivisionPairsAux.tm (unaryEncodeNat n))
    (haltList trialDivisionPairsAux.tm output)
    trialDivisionPairsAux.tm.main [] rfl hgenerator.evals_in_steps rfl
  refine
    { steps := hgenerator.steps
      evals_in_steps := ?_
      steps_le_m := hgenerator.steps_le_m }
  rw [show unaryCandidatePrimeComputer.step =
      TM2.step (compositionProgram trialDivisionPairsAux pairAllFalseAux) by
    rfl]
  calc
    (flip Option.bind
        (TM2.step (compositionProgram trialDivisionPairsAux pairAllFalseAux)))^[
          hgenerator.steps]
        (some (initList unaryCandidatePrimeComputer (unaryEncodeNat n))) =
      (flip Option.bind unaryCandidatePrimeComputer.step)^[hgenerator.steps]
        (some (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
          (liftLeftControlCfg trialDivisionPairsAux pairAllFalseAux
            (initList trialDivisionPairsAux.tm (unaryEncodeNat n))))) := by
        exact unaryCandidatePrime_iterate_init hgenerator.steps hpositive _
    _ = some (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
        (leftTransferEntryCfg trialDivisionPairsAux pairAllFalseAux
          (haltList trialDivisionPairsAux.tm output).var
          (haltList trialDivisionPairsAux.tm output).stk)) :=
      hleftRun

private def unaryCandidatePrimeRightContents
    (input : List (Option Bool)) :
    (index : StackIndex trialDivisionPairsAux.tm pairAllFalseAux.tm) →
      List (StackAlphabet trialDivisionPairsAux.tm pairAllFalseAux.tm index) :=
  rightStacks trialDivisionPairsAux.tm pairAllFalseAux.tm
    (initList pairAllFalseAux.tm input).stk

private theorem unaryCandidatePrime_rightEntryMachineCfg
    (input : List (Option Bool)) :
    rightEntryMachineCfg trialDivisionPairsAux pairAllFalseAux
        (unaryCandidatePrimeRightContents input) =
      initList pairAllFalseAux.tm input := by
  rfl

private theorem unaryCandidatePrime_transferStart_eq
    (output : List (Option Bool)) :
    liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
        (leftTransferEntryCfg trialDivisionPairsAux pairAllFalseAux
          (haltList trialDivisionPairsAux.tm output).var
          (haltList trialDivisionPairsAux.tm output).stk) =
      transferActionCfg trialDivisionPairsAux pairAllFalseAux
        (.phase .reverseOutput)
        (leftState trialDivisionPairsAux pairAllFalseAux
          trialDivisionPairsAux.tm.initialState)
        (Function.update
          (Function.update (fun _ => []) (Sum.inr pairAllFalseAux.tm.k₀) [])
          (Sum.inl trialDivisionPairsAux.tm.k₁) output) [] := by
  simp only [trialDivisionPairsAux]
  rw [trialPair_haltList_eq_cfg]
  unfold liftScratchCfg leftTransferEntryCfg transferActionCfg trialPairCfg
    trialPairStackContents pairAllFalseAux pairAllFalseComputer leftStacks
    extendStacks
  congr 2
  funext index
  rcases index with (index | index)
  · rcases index with (index | index)
    · cases index <;> rfl
    · rcases index with (index | index)
      · cases index
        rfl
      · cases index <;> rfl
  · cases index
    rfl

private theorem unaryCandidatePrime_transferFinish_eq
    (output : List (Option Bool)) :
    rightEntryCfg trialDivisionPairsAux pairAllFalseAux
        (unaryCandidatePrimeRightContents output) [] =
      rightEntryCfg trialDivisionPairsAux pairAllFalseAux
        (Function.update
          (Function.update (fun _ => []) (Sum.inl trialDivisionPairsAux.tm.k₁) [])
          (Sum.inr pairAllFalseAux.tm.k₀)
          (output.map (middleAlphabetEquiv trialDivisionPairsAux
            pairAllFalseAux) ++ [])) [] := by
  congr 2
  unfold unaryCandidatePrimeRightContents
  simp only [pairAllFalseAux]
  rw [pairAllFalse_initList_eq_cfg]
  unfold pairAllFalseScanCfg pairAllFalseCfg pairAllFalseStackContents
    pairDvdStackContents dvdStackContents rightStacks middleAlphabetEquiv
    trialDivisionPairsAux pairAllFalseComputer trialDivisionPairComputer
  funext index
  rcases index with (index | index)
  · cases index <;> rfl
  · rcases index with (index | index)
    · cases index
      simp [Function.update]
      change output = output.map id
      simp
    · cases index <;> rfl

private def unaryCandidatePrime_transfer_evals (n : ℕ) :
    EvalsToInTime unaryCandidatePrimeComputer.step
      (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
        (leftTransferEntryCfg trialDivisionPairsAux pairAllFalseAux
          (haltList trialDivisionPairsAux.tm
            (RawUnaryPairList.encode (trialDivisionPairs n))).var
          (haltList trialDivisionPairsAux.tm
            (RawUnaryPairList.encode (trialDivisionPairs n))).stk))
      (some (rightEntryCfg trialDivisionPairsAux pairAllFalseAux
        (unaryCandidatePrimeRightContents
          (RawUnaryPairList.encode (trialDivisionPairs n))) []))
      (4 * (RawUnaryPairList.encode (trialDivisionPairs n)).length + 4) := by
  let output := RawUnaryPairList.encode (trialDivisionPairs n)
  refine
    { steps := 4 * output.length + 4
      evals_in_steps := ?_
      steps_le_m := Nat.le_refl _ }
  rw [unaryCandidatePrime_transferStart_eq output,
    unaryCandidatePrime_transferFinish_eq output]
  exact compositionProgram_transfer_whole_list trialDivisionPairsAux
      pairAllFalseAux
      (leftState trialDivisionPairsAux pairAllFalseAux
        trialDivisionPairsAux.tm.initialState)
      (fun _ => []) output []

/-- Candidate-only primality bit.  This omits the lower-bound guard because
every generated Bertrand candidate is at least two. -/
def unaryCandidatePrime (n : ℕ) : Bool :=
  allFalseDivisibilityResults (trialDivisionPairs n)

theorem unaryCandidatePrime_eq_true_iff
    {n : ℕ} (hn : 2 ≤ n) :
    unaryCandidatePrime n = true ↔ n.Prime := by
  exact allFalseDivisibilityResults_trialDivisionPairs_eq_true_iff hn

/-- Every value emitted by the Bertrand enumerator is a valid input for the
candidate-only primality machine.  This includes the edge cases: the interval
is empty at `q = 0`, while its sole value at `q = 1` is `2`. -/
theorem two_le_of_mem_bertrandCandidates
    {q n : ℕ} (hn : n ∈ bertrandCandidates q) :
    2 ≤ n := by
  have hbounds := (mem_bertrandCandidates_iff q n).mp hn
  omega

/-- On the generated candidate stream, the composed machine predicate agrees
exactly with the guarded trial-division specification.  Thus the lower-bound
guard is supplied by the enumerator invariant rather than by another machine
pass. -/
theorem unaryCandidatePrime_eq_trialPrime_of_mem_bertrandCandidates
    {q n : ℕ} (hn : n ∈ bertrandCandidates q) :
    unaryCandidatePrime n = trialPrime n := by
  rw [Bool.eq_iff_iff,
    unaryCandidatePrime_eq_true_iff
      (two_le_of_mem_bertrandCandidates hn),
    trialPrime_eq_true_iff]

/-- Filtering the checked Bertrand enumeration with the composed machine's
candidate predicate yields exactly the semantic prime-candidate list. -/
theorem filter_unaryCandidatePrime_bertrandCandidates (q : ℕ) :
    (bertrandCandidates q).filter unaryCandidatePrime =
      bertrandPrimeCandidates q := by
  rw [bertrandPrimeCandidates]
  exact List.filter_congr fun _ hn =>
    unaryCandidatePrime_eq_trialPrime_of_mem_bertrandCandidates hn

private theorem unaryCandidatePrime_rightEntry_eq
    (input : List (Option Bool)) :
    rightEntryCfg trialDivisionPairsAux pairAllFalseAux
        (unaryCandidatePrimeRightContents input) [] =
      rightPhaseCfg trialDivisionPairsAux pairAllFalseAux (fun _ => []) []
        (initList pairAllFalseAux.tm input) := by
  rw [rightEntryCfg_eq_rightPhaseCfg,
    unaryCandidatePrime_rightEntryMachineCfg]
  congr 1

private noncomputable def unaryCandidatePrime_second_evals (n : ℕ) :
    EvalsToInTime unaryCandidatePrimeComputer.step
      (rightEntryCfg trialDivisionPairsAux pairAllFalseAux
        (unaryCandidatePrimeRightContents
          (RawUnaryPairList.encode (trialDivisionPairs n))) [])
      (some (haltList unaryCandidatePrimeComputer
        (encodeBool (unaryCandidatePrime n))))
      (18 * (RawUnaryPairList.encode (trialDivisionPairs n)).length + 1) := by
  let input := RawUnaryPairList.encode (trialDivisionPairs n)
  let result := unaryCandidatePrime n
  have hsecond : EvalsToInTime pairAllFalseAux.tm.step
      (initList pairAllFalseAux.tm input)
      (some (haltList pairAllFalseAux.tm (encodeBool result)))
      (18 * input.length + 1) := by
    simpa [pairAllFalseAux, input, result, unaryCandidatePrime] using
      pairAllFalse_outputsInTime (trialDivisionPairs n)
  have hrightRun := compositionProgram_right_run trialDivisionPairsAux
    pairAllFalseAux hsecond.steps
    (initList pairAllFalseAux.tm input)
    (haltList pairAllFalseAux.tm (encodeBool result))
    (fun _ => []) [] hsecond.evals_in_steps
  refine
    { steps := hsecond.steps
      evals_in_steps := ?_
      steps_le_m := hsecond.steps_le_m }
  rw [unaryCandidatePrime_rightEntry_eq]
  change (flip Option.bind unaryCandidatePrimeComputer.step)^[hsecond.steps]
      (some (rightPhaseCfg trialDivisionPairsAux pairAllFalseAux
        (fun _ => []) [] (initList pairAllFalseAux.tm input))) =
    some (haltList unaryCandidatePrimeComputer [result])
  rw [unaryCandidatePrime_haltList_eq]
  exact hrightRun

/-- The composed machine generates the complete padded trial stream, transfers
it in source order, and runs the fused no-divisor pass in quadratic time in
the unary candidate length. -/
noncomputable def unaryCandidatePrime_outputsInTime (n : ℕ) :
    TM2OutputsInTime unaryCandidatePrimeComputer (unaryEncodeNat n)
      (some (encodeBool (unaryCandidatePrime n)))
      (64 * (n + 1) ^ 2) := by
  let stream := RawUnaryPairList.encode (trialDivisionPairs n)
  have hgenerator := unaryCandidatePrime_generator_evals n
  have htransfer := unaryCandidatePrime_transfer_evals n
  have hsecond := unaryCandidatePrime_second_evals n
  have hfirst := EvalsToInTime.trans unaryCandidatePrimeComputer.step
    (8 * (n + 1) ^ 2) (4 * stream.length + 4)
    (initList unaryCandidatePrimeComputer (unaryEncodeNat n))
    (liftScratchCfg trialDivisionPairsAux pairAllFalseAux []
      (leftTransferEntryCfg trialDivisionPairsAux pairAllFalseAux
        (haltList trialDivisionPairsAux.tm stream).var
        (haltList trialDivisionPairsAux.tm stream).stk))
    (some (rightEntryCfg trialDivisionPairsAux pairAllFalseAux
      (unaryCandidatePrimeRightContents stream) []))
    (by simpa [stream] using hgenerator)
    (by simpa [stream] using htransfer)
  have hall := EvalsToInTime.trans unaryCandidatePrimeComputer.step
    (4 * stream.length + 4 + 8 * (n + 1) ^ 2)
    (18 * stream.length + 1)
    (initList unaryCandidatePrimeComputer (unaryEncodeNat n))
    (rightEntryCfg trialDivisionPairsAux pairAllFalseAux
      (unaryCandidatePrimeRightContents stream) [])
    (some (haltList unaryCandidatePrimeComputer
      (encodeBool (unaryCandidatePrime n))))
    (by simpa [Nat.add_comm] using hfirst)
    (by simpa [stream] using hsecond)
  have hstream := trialDivisionPairStream_length_le n
  have hbound :
      (18 * stream.length + 1) +
          (4 * stream.length + 4 + 8 * (n + 1) ^ 2) ≤
        64 * (n + 1) ^ 2 := by
    cases n with
    | zero =>
        norm_num [stream, trialDivisionPairs, trialDivisors,
          RawUnaryPairList.encode]
    | succ n =>
        cases n with
        | zero =>
            norm_num [stream, trialDivisionPairs, trialDivisors,
              RawUnaryPairList.encode]
        | succ k =>
            simp only [stream] at hstream ⊢
            have hsub : k + 1 + 1 - 2 = k := by omega
            rw [hsub] at hstream
            nlinarith
  exact evalsToInTimeMono hall hbound

/-- Genuine polynomial-time finite-machine computation of the candidate-only
primality bit on unary input.  The enumerator supplies the lower-bound
invariant, so `filter_unaryCandidatePrime_bertrandCandidates` connects this
predicate directly to the guarded semantic filter. -/
noncomputable def unaryCandidatePrimeComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ Bool unaryFinEncodingNat
      finEncodingBoolBool unaryCandidatePrime where
  tm := unaryCandidatePrimeComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 64 * (Polynomial.X + 1) ^ 2
  outputsFun n := by
    simpa [unaryFinEncodingNat, finEncodingBoolBool, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using
        unaryCandidatePrime_outputsInTime n

/-! ## First-prime selection from the unary candidate stream

The outer driver below scans the stack-oriented candidate fields from largest
to smallest.  Whenever the checked candidate-primality component accepts, the
driver overwrites its saved value.  The last accepted value is therefore the
first accepted value in the source-order list.  The trailing length field is
recognized by one-symbol lookahead and discarded without a primality test.
-/

/-- The first candidate accepted by the checked candidate-primality predicate. -/
def firstUnaryCandidatePrime? : List ℕ → Option ℕ
  | [] => none
  | candidate :: candidates =>
      if unaryCandidatePrime candidate then some candidate
      else firstUnaryCandidatePrime? candidates

/-- The selected candidate, using the compiler's explicit empty-list
convention `2`. -/
def selectUnaryCandidatePrime (candidates : List ℕ) : ℕ :=
  (firstUnaryCandidatePrime? candidates).getD 2

@[simp]
theorem firstUnaryCandidatePrime?_eq_head?_filter (candidates : List ℕ) :
    firstUnaryCandidatePrime? candidates =
      (candidates.filter unaryCandidatePrime).head? := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates ih =>
      by_cases hprime : unaryCandidatePrime candidate
      · simp [firstUnaryCandidatePrime?, hprime]
      · simp [firstUnaryCandidatePrime?, hprime, ih]

theorem firstUnaryCandidatePrime?_mem {candidates : List ℕ} {candidate : ℕ}
    (hselected : firstUnaryCandidatePrime? candidates = some candidate) :
    candidate ∈ candidates := by
  induction candidates with
  | nil => simp [firstUnaryCandidatePrime?] at hselected
  | cons head tail ih =>
      by_cases hprime : unaryCandidatePrime head
      · simp [firstUnaryCandidatePrime?, hprime] at hselected
        simpa [hselected]
      · simp only [firstUnaryCandidatePrime?, hprime, ↓reduceIte] at hselected
        exact List.mem_cons_of_mem head (ih hselected)

private theorem head?_getD_eq_head {candidates : List ℕ}
    (hne : candidates ≠ []) (fallback : ℕ) :
    candidates.head?.getD fallback = candidates.head hne := by
  cases candidates with
  | nil => contradiction
  | cons candidate candidates => rfl

/-- The native unary scan selects the semantic first Bertrand prime. -/
theorem selectUnaryCandidatePrime_bertrandCandidates (q : ℕ) :
    selectUnaryCandidatePrime (bertrandCandidates q) = firstBertrandPrime q := by
  rw [selectUnaryCandidatePrime, firstUnaryCandidatePrime?_eq_head?_filter,
    filter_unaryCandidatePrime_bertrandCandidates]
  by_cases hq : q = 0
  · subst q
    simp [firstBertrandPrime, bertrandPrimeCandidates,
      bertrandCandidates, intervalFrom]
  · rw [firstBertrandPrime, dif_neg hq]
    exact head?_getD_eq_head (bertrandPrimeCandidates_ne_nil hq) 2

private instance primeSelectorComponentKDecidableEq :
    DecidableEq unaryCandidatePrimeComputer.K :=
  unaryCandidatePrimeComputer.kDecidableEq

private instance primeSelectorComponentKFintype :
    Fintype unaryCandidatePrimeComputer.K :=
  unaryCandidatePrimeComputer.kFin

private instance primeSelectorComponentLabelFintype :
    Fintype unaryCandidatePrimeComputer.Λ :=
  unaryCandidatePrimeComputer.ΛFin

private instance primeSelectorComponentStateFintype :
    Fintype unaryCandidatePrimeComputer.σ :=
  unaryCandidatePrimeComputer.σFin

/-- Driver-owned stacks plus all stacks of the checked candidate-primality
component. -/
inductive PrimeSelectorOuterStack
  | input
  | candidate
  | output
  deriving DecidableEq, Fintype

abbrev PrimeSelectorStack :=
  PrimeSelectorOuterStack ⊕ unaryCandidatePrimeComputer.K

/-- Outer parsing, component execution, result handling, and final cleanup. -/
inductive PrimeSelectorLabel
  | scan
  | lookahead
  | prime (label : unaryCandidatePrimeComputer.Λ)
  | result
  | clearCandidate
  | clearSelected
  | moveCandidate
  | discardCount
  | finalize
  deriving Fintype

/-- Finite control remembers the most recent outer pop, the component state,
and whether an accepted candidate has been saved. -/
structure PrimeSelectorState where
  observed : Option Bool
  prime : unaryCandidatePrimeComputer.σ
  found : Bool
  deriving Fintype

private def primeSelectorInitialState : PrimeSelectorState :=
  ⟨none, unaryCandidatePrimeComputer.initialState, false⟩

private def primeSelectorObserve
    (state : PrimeSelectorState) (observed : Option Bool) :
    PrimeSelectorState :=
  { state with observed := observed }

private def primeSelectorResetObserved
    (state : PrimeSelectorState) : PrimeSelectorState :=
  { state with observed := none }

private def primeSelectorSetComponent
    (state : PrimeSelectorState) (prime : unaryCandidatePrimeComputer.σ) :
    PrimeSelectorState :=
  { state with prime := prime }

private def primeSelectorSetFound
    (state : PrimeSelectorState) : PrimeSelectorState :=
  { state with observed := none, found := true }

private def primeSelectorObservedPresent : PrimeSelectorState → Bool
  | ⟨some _, _, _⟩ => true
  | _ => false

private def primeSelectorObservedBit : PrimeSelectorState → Bool
  | ⟨some bit, _, _⟩ => bit
  | _ => false

private def PrimeSelectorAlphabet : PrimeSelectorStack → Type
  | .inl _ => Bool
  | .inr index => unaryCandidatePrimeComputer.Γ index

/-- Lift one statement of the checked candidate-primality component.  Its halt
is redirected to the outer result handler. -/
private def liftCandidatePrimeStmt :
    TM2.Stmt unaryCandidatePrimeComputer.Γ
      unaryCandidatePrimeComputer.Λ unaryCandidatePrimeComputer.σ →
      TM2.Stmt PrimeSelectorAlphabet PrimeSelectorLabel PrimeSelectorState
  | .push index write next =>
      .push (.inr index) (fun state => write state.prime)
        (liftCandidatePrimeStmt next)
  | .peek index read next =>
      .peek (.inr index)
        (fun state observed =>
          primeSelectorSetComponent state (read state.prime observed))
        (liftCandidatePrimeStmt next)
  | .pop index read next =>
      .pop (.inr index)
        (fun state observed =>
          primeSelectorSetComponent state (read state.prime observed))
        (liftCandidatePrimeStmt next)
  | .load update next =>
      .load (fun state => primeSelectorSetComponent state (update state.prime))
        (liftCandidatePrimeStmt next)
  | .branch test yes no =>
      .branch (fun state => test state.prime)
        (liftCandidatePrimeStmt yes) (liftCandidatePrimeStmt no)
  | .goto next => .goto (fun state => .prime (next state.prime))
  | .halt => .goto (fun _ => .result)

/-- Scan unary fields, invoke candidate primality once per value field, keep
the first source-order survivor, discard the trailing count, and emit a unary
natural. -/
def primeSelectorProgram :
    PrimeSelectorLabel →
      TM2.Stmt PrimeSelectorAlphabet PrimeSelectorLabel PrimeSelectorState
  | .scan =>
      .pop (.inl .input) primeSelectorObserve <|
        .branch primeSelectorObservedPresent
          (.branch primeSelectorObservedBit
            (.push (.inl .candidate) (fun _ => true) <|
              .push (.inr unaryCandidatePrimeComputer.k₀) (fun _ => true) <|
                .load primeSelectorResetObserved <|
                  .goto fun _ => .scan)
            (.load primeSelectorResetObserved <|
              .goto fun _ => .lookahead))
          (.load primeSelectorResetObserved <|
            .goto fun _ => .discardCount)
  | .lookahead =>
      .pop (.inl .input) primeSelectorObserve <|
        .branch primeSelectorObservedPresent
          (.push (.inl .input) primeSelectorObservedBit <|
            .load primeSelectorResetObserved <|
              .goto fun _ => .prime unaryCandidatePrimeComputer.main)
          (.load primeSelectorResetObserved <|
            .goto fun _ => .discardCount)
  | .prime label =>
      liftCandidatePrimeStmt (unaryCandidatePrimeComputer.m label)
  | .result =>
      .pop (.inr unaryCandidatePrimeComputer.k₁) primeSelectorObserve <|
        .branch primeSelectorObservedBit
          (.load primeSelectorSetFound <| .goto fun _ => .clearSelected)
          (.load primeSelectorResetObserved <|
            .goto fun _ => .clearCandidate)
  | .clearCandidate =>
      .pop (.inl .candidate) primeSelectorObserve <|
        .branch primeSelectorObservedPresent
          (.load primeSelectorResetObserved <|
            .goto fun _ => .clearCandidate)
          (.load primeSelectorResetObserved <| .goto fun _ => .scan)
  | .clearSelected =>
      .pop (.inl .output) primeSelectorObserve <|
        .branch primeSelectorObservedPresent
          (.load primeSelectorResetObserved <|
            .goto fun _ => .clearSelected)
          (.load primeSelectorResetObserved <|
            .goto fun _ => .moveCandidate)
  | .moveCandidate =>
      .pop (.inl .candidate) primeSelectorObserve <|
        .branch primeSelectorObservedPresent
          (.push (.inl .output) primeSelectorObservedBit <|
            .load primeSelectorResetObserved <|
              .goto fun _ => .moveCandidate)
          (.load primeSelectorResetObserved <| .goto fun _ => .scan)
  | .discardCount =>
      .pop (.inl .candidate) primeSelectorObserve <|
        .branch primeSelectorObservedPresent
          (.pop (.inr unaryCandidatePrimeComputer.k₀)
            (fun state _ => primeSelectorResetObserved state) <|
              .goto fun _ => .discardCount)
          (.load primeSelectorResetObserved <| .goto fun _ => .finalize)
  | .finalize =>
      .branch (fun state => state.found)
        (.load (fun _ => primeSelectorInitialState) .halt)
        (.push (.inl .output) (fun _ => true) <|
          .push (.inl .output) (fun _ => true) <|
            .load (fun _ => primeSelectorInitialState) .halt)

/-- Concrete finite machine selecting the first accepted candidate from a
checked `RawUnaryNatList` stream. -/
def primeSelectorComputer : FinTM2 where
  K := PrimeSelectorStack
  k₀ := .inl .input
  k₁ := .inl .output
  Γ := PrimeSelectorAlphabet
  Λ := PrimeSelectorLabel
  main := .scan
  σ := PrimeSelectorState
  initialState := primeSelectorInitialState
  Γk₀Fin := Bool.fintype
  m := primeSelectorProgram

private def primeSelectorStackContents
    (input candidate output : List Bool)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index)) :
    (index : PrimeSelectorStack) → List (PrimeSelectorAlphabet index)
  | .inl .input => input
  | .inl .candidate => candidate
  | .inl .output => output
  | .inr index => contents index

private def primeSelectorCfg (label : Option PrimeSelectorLabel)
    (state : PrimeSelectorState) (input candidate output : List Bool)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index)) :
    primeSelectorComputer.Cfg where
  l := label
  var := state
  stk := primeSelectorStackContents input candidate output contents

private def primeSelectorIdleCfg (label : PrimeSelectorLabel)
    (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.Cfg :=
  primeSelectorCfg (some label)
    ⟨none, unaryCandidatePrimeComputer.initialState, found⟩
    input candidate output (fun _ => [])

private def primeSelectorScanCfg
    (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.Cfg :=
  primeSelectorCfg (some .scan)
    ⟨none, unaryCandidatePrimeComputer.initialState, found⟩
    input candidate output (initList unaryCandidatePrimeComputer candidate).stk

private def primeSelectorLookaheadCfg
    (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.Cfg :=
  primeSelectorCfg (some .lookahead)
    ⟨none, unaryCandidatePrimeComputer.initialState, found⟩
    input candidate output (initList unaryCandidatePrimeComputer candidate).stk

private def primeSelectorDiscardCfg
    (candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.Cfg :=
  primeSelectorCfg (some .discardCount)
    ⟨none, unaryCandidatePrimeComputer.initialState, found⟩
    [] candidate output (initList unaryCandidatePrimeComputer candidate).stk

private def primeSelectorLiftCfg (input candidate output : List Bool)
    (found : Bool) (cfg : unaryCandidatePrimeComputer.Cfg) :
    primeSelectorComputer.Cfg :=
  primeSelectorCfg
    (match cfg.l with
      | none => some .result
      | some label => some (.prime label))
    ⟨none, cfg.var, found⟩ input candidate output cfg.stk

@[simp]
private theorem primeSelectorStackContents_update
    (input candidate output : List Bool)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index))
    (index : unaryCandidatePrimeComputer.K)
    (value : List (unaryCandidatePrimeComputer.Γ index)) :
    Function.update
        (primeSelectorStackContents input candidate output contents)
        (.inr index) value =
      primeSelectorStackContents input candidate output
        (Function.update contents index value) := by
  funext target
  cases target with
  | inl outer =>
      cases outer <;> simp [primeSelectorStackContents, Function.update]
  | inr other =>
      by_cases h : other = index
      · subst other
        simp [primeSelectorStackContents, Function.update]
      · simp [primeSelectorStackContents, Function.update, h]

@[simp]
private theorem primeSelectorStackContents_update_input
    (input candidate output value : List Bool)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index)) :
    Function.update
        (primeSelectorStackContents input candidate output contents)
        (.inl .input) value =
      primeSelectorStackContents value candidate output contents := by
  funext target
  rcases target with outer | index
  · cases outer <;> simp [primeSelectorStackContents, Function.update]
  · simp [primeSelectorStackContents, Function.update]

@[simp]
private theorem primeSelectorStackContents_update_candidate
    (input candidate output value : List Bool)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index)) :
    Function.update
        (primeSelectorStackContents input candidate output contents)
        (.inl .candidate) value =
      primeSelectorStackContents input value output contents := by
  funext target
  rcases target with outer | index
  · cases outer <;> simp [primeSelectorStackContents, Function.update]
  · simp [primeSelectorStackContents, Function.update]

@[simp]
private theorem primeSelectorStackContents_update_output
    (input candidate output value : List Bool)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index)) :
    Function.update
        (primeSelectorStackContents input candidate output contents)
        (.inl .output) value =
      primeSelectorStackContents input candidate value contents := by
  funext target
  rcases target with outer | index
  · cases outer <;> simp [primeSelectorStackContents, Function.update]
  · simp [primeSelectorStackContents, Function.update]

private theorem liftCandidatePrime_stepAux
    (stmt : TM2.Stmt unaryCandidatePrimeComputer.Γ
      unaryCandidatePrimeComputer.Λ unaryCandidatePrimeComputer.σ)
    (state : unaryCandidatePrimeComputer.σ)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index))
    (input candidate output : List Bool) (found : Bool) :
    TM2.stepAux (liftCandidatePrimeStmt stmt) ⟨none, state, found⟩
        (primeSelectorStackContents input candidate output contents) =
      primeSelectorLiftCfg input candidate output found
        (TM2.stepAux stmt state contents) := by
  induction stmt generalizing state contents with
  | push index write next ih =>
      simp only [liftCandidatePrimeStmt, TM2.stepAux]
      rw [primeSelectorStackContents_update]
      exact ih _ _
  | peek index read next ih =>
      simpa only [liftCandidatePrimeStmt, TM2.stepAux,
        primeSelectorStackContents, primeSelectorSetComponent] using
          ih (read state (contents index).head?) contents
  | pop index read next ih =>
      simp only [liftCandidatePrimeStmt, TM2.stepAux,
        primeSelectorStackContents, primeSelectorSetComponent]
      rw [primeSelectorStackContents_update]
      exact ih _ _
  | load update next ih =>
      simpa only [liftCandidatePrimeStmt, TM2.stepAux,
        primeSelectorSetComponent] using ih (update state) contents
  | branch test yes no ihYes ihNo =>
      by_cases h : test state
      · simpa only [liftCandidatePrimeStmt, TM2.stepAux, h, cond_true] using
          ihYes state contents
      · simpa only [liftCandidatePrimeStmt, TM2.stepAux, h, cond_false] using
          ihNo state contents
  | goto next => rfl
  | halt => rfl

private theorem primeSelector_lift_step
    (input candidate output : List Bool) (found : Bool)
    (label : unaryCandidatePrimeComputer.Λ)
    (state : unaryCandidatePrimeComputer.σ)
    (contents : (index : unaryCandidatePrimeComputer.K) →
      List (unaryCandidatePrimeComputer.Γ index)) :
    primeSelectorComputer.step
        (primeSelectorLiftCfg input candidate output found
          ⟨some label, state, contents⟩) =
      some (primeSelectorLiftCfg input candidate output found
        (TM2.stepAux (unaryCandidatePrimeComputer.m label) state contents)) := by
  simp only [primeSelectorComputer, FinTM2.step, primeSelectorLiftCfg,
    primeSelectorProgram, TM2.step]
  exact congrArg some
    (liftCandidatePrime_stepAux _ _ _ _ _ _ _)

private theorem candidatePrime_iterate_none (steps : ℕ) :
    (flip Option.bind unaryCandidatePrimeComputer.step)^[steps]
        (none : Option unaryCandidatePrimeComputer.Cfg) = none := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      rfl

private theorem primeSelector_iterate_lift
    (steps : ℕ) (input candidate output : List Bool) (found : Bool)
    (start finish : unaryCandidatePrimeComputer.Cfg)
    (hrun :
      (flip Option.bind unaryCandidatePrimeComputer.step)^[steps]
          (some start) = some finish) :
    (flip Option.bind primeSelectorComputer.step)^[steps]
        (some (primeSelectorLiftCfg input candidate output found start)) =
      some (primeSelectorLiftCfg input candidate output found finish) := by
  induction steps generalizing start with
  | zero =>
      simpa using congrArg
        (Option.map (primeSelectorLiftCfg input candidate output found)) hrun
  | succ steps ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      change (flip Option.bind unaryCandidatePrimeComputer.step)^[steps]
          (unaryCandidatePrimeComputer.step start) = some finish at hrun
      change (flip Option.bind primeSelectorComputer.step)^[steps]
          (primeSelectorComputer.step
            (primeSelectorLiftCfg input candidate output found start)) =
        some (primeSelectorLiftCfg input candidate output found finish)
      cases hlabel : start.l with
      | none =>
          have hnone : unaryCandidatePrimeComputer.step start = none := by
            rcases start with ⟨current, state, contents⟩
            change current = none at hlabel
            subst current
            rfl
          rw [hnone] at hrun
          rw [candidatePrime_iterate_none] at hrun
          contradiction
      | some label =>
          let middle := TM2.stepAux
            (unaryCandidatePrimeComputer.m label) start.var start.stk
          have hstep : unaryCandidatePrimeComputer.step start = some middle := by
            rcases start with ⟨current, state, contents⟩
            simp [unaryCandidatePrimeComputer, FinTM2.step] at hlabel ⊢
            subst current
            rfl
          rw [hstep] at hrun
          have hcfg : start = ⟨some label, start.var, start.stk⟩ := by
            rcases start with ⟨current, state, contents⟩
            change current = some label at hlabel
            subst current
            rfl
          rw [show primeSelectorComputer.step
              (primeSelectorLiftCfg input candidate output found start) =
                some (primeSelectorLiftCfg input candidate output found middle) by
            rw [hcfg]
            simpa [middle] using primeSelector_lift_step input candidate output
              found label start.var start.stk]
          exact ih middle hrun

private def primeSelector_lift_evals
    (input candidate output : List Bool) (found : Bool)
    {start finish : unaryCandidatePrimeComputer.Cfg} {bound : ℕ}
    (hrun : EvalsToInTime unaryCandidatePrimeComputer.step start
      (some finish) bound) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorLiftCfg input candidate output found start)
      (some (primeSelectorLiftCfg input candidate output found finish))
      bound where
  steps := hrun.steps
  evals_in_steps := primeSelector_iterate_lift hrun.steps input candidate
    output found start finish hrun.evals_in_steps
  steps_le_m := hrun.steps_le_m

private def primeSelectorEvalsToInTimeOne
    {start finish : primeSelectorComputer.Cfg}
    (hstep : primeSelectorComputer.step start = some finish) :
    EvalsToInTime primeSelectorComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem primeSelector_step_scan_true
    (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorScanCfg (true :: input) candidate output found) =
      some (primeSelectorScanCfg input (true :: candidate) output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorScanCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorObserve, primeSelectorObservedPresent,
    primeSelectorObservedBit, primeSelectorResetObserved,
    initList, haltList, Function.update]
  funext index
  rcases index with outer | index
  · cases outer <;> simp [primeSelectorStackContents, Function.update]
  · by_cases h : index = unaryCandidatePrimeComputer.k₀
    · subst index
      simp [primeSelectorStackContents, Function.update]
    · simp [primeSelectorStackContents, Function.update, h]

private theorem primeSelector_step_scan_false
    (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorScanCfg (false :: input) candidate output found) =
      some (primeSelectorLookaheadCfg input candidate output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorScanCfg,
    primeSelectorLookaheadCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedPresent, primeSelectorObservedBit,
    primeSelectorResetObserved, initList, haltList, Function.update]

private theorem primeSelector_step_lookahead_present
    (bit : Bool) (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorLookaheadCfg (bit :: input) candidate output found) =
      some (primeSelectorLiftCfg (bit :: input) candidate output found
        (initList unaryCandidatePrimeComputer candidate)) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorLookaheadCfg,
    primeSelectorLiftCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedPresent, primeSelectorObservedBit,
    primeSelectorResetObserved, initList, Function.update]

private theorem primeSelector_step_lookahead_nil
    (candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorLookaheadCfg [] candidate output found) =
      some (primeSelectorDiscardCfg candidate output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorLookaheadCfg,
    primeSelectorDiscardCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedPresent, primeSelectorResetObserved,
    initList, haltList, Function.update]

private def encodePrimeSelection : Option ℕ → List Bool
  | none => []
  | some candidate => unaryEncodeNat candidate

private def primeSelectionFound : Option ℕ → Bool
  | none => false
  | some _ => true

@[simp]
private theorem candidatePrime_initList_empty_stacks :
    (initList unaryCandidatePrimeComputer []).stk = (fun _ => []) := by
  funext index
  by_cases h : index = unaryCandidatePrimeComputer.k₀
  · subst index
    simp [initList]
  · simp [initList, h]

@[simp]
private theorem candidatePrime_initList_pop_input
    (bit : Bool) (input : List Bool) :
    Function.update (initList unaryCandidatePrimeComputer (bit :: input)).stk
        unaryCandidatePrimeComputer.k₀ input =
      (initList unaryCandidatePrimeComputer input).stk := by
  funext index
  by_cases h : index = unaryCandidatePrimeComputer.k₀
  · subst index
    simp [initList, Function.update]
  · simp [initList, Function.update, h]

@[simp]
private theorem candidatePrime_haltList_pop_result (result : Bool) :
    Function.update (haltList unaryCandidatePrimeComputer [result]).stk
        unaryCandidatePrimeComputer.k₁ [] = (fun _ => []) := by
  funext index
  by_cases h : index = unaryCandidatePrimeComputer.k₁
  · subst index
    simp [haltList, Function.update]
  · simp [haltList, Function.update, h]

private theorem primeSelector_haltList_eq_cfg (output : List Bool) :
    haltList primeSelectorComputer output =
      primeSelectorCfg none primeSelectorInitialState [] [] output
        (fun _ => []) := by
  unfold haltList primeSelectorCfg primeSelectorComputer
  congr 2
  funext index
  rcases index with outer | index
  · cases outer <;> simp [primeSelectorStackContents]
  · simp [primeSelectorStackContents]

private theorem primeSelector_step_result_true
    (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorLiftCfg input candidate output found
          (haltList unaryCandidatePrimeComputer [true])) =
      some (primeSelectorIdleCfg .clearSelected input candidate output true) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorLiftCfg,
    primeSelectorIdleCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedBit, primeSelectorSetFound, haltList,
    Function.update]
  funext index
  rcases index with outer | index
  · cases outer <;> simp [primeSelectorStackContents, Function.update]
  · by_cases h : index = unaryCandidatePrimeComputer.k₁
    · subst index
      simp [primeSelectorStackContents, Function.update]
    · simp [primeSelectorStackContents, Function.update, h]

private theorem primeSelector_step_result_false
    (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorLiftCfg input candidate output found
          (haltList unaryCandidatePrimeComputer [false])) =
      some (primeSelectorIdleCfg .clearCandidate input candidate output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorLiftCfg,
    primeSelectorIdleCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedBit, primeSelectorResetObserved, haltList,
    Function.update]
  funext index
  rcases index with outer | index
  · cases outer <;> simp [primeSelectorStackContents, Function.update]
  · by_cases h : index = unaryCandidatePrimeComputer.k₁
    · subst index
      simp [primeSelectorStackContents, Function.update]
    · simp [primeSelectorStackContents, Function.update, h]

private theorem primeSelector_step_clearCandidate_cons
    (bit : Bool) (input candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .clearCandidate input (bit :: candidate)
          output found) =
      some (primeSelectorIdleCfg .clearCandidate input candidate output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorObserve, primeSelectorObservedPresent,
    primeSelectorResetObserved, haltList, Function.update]

private theorem primeSelector_step_clearCandidate_nil
    (input output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .clearCandidate input [] output found) =
      some (primeSelectorScanCfg input [] output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorScanCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedPresent, primeSelectorResetObserved,
    Function.update]
  rw [candidatePrime_initList_empty_stacks]

private theorem primeSelector_step_clearSelected_cons
    (bit : Bool) (input candidate output : List Bool) :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .clearSelected input candidate (bit :: output)
          true) =
      some (primeSelectorIdleCfg .clearSelected input candidate output true) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorObserve, primeSelectorObservedPresent,
    primeSelectorResetObserved, haltList, Function.update]

private theorem primeSelector_step_clearSelected_nil
    (input candidate : List Bool) :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .clearSelected input candidate [] true) =
      some (primeSelectorIdleCfg .moveCandidate input candidate [] true) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorObserve, primeSelectorObservedPresent,
    primeSelectorResetObserved, haltList, Function.update]

private theorem primeSelector_step_moveCandidate_cons
    (bit : Bool) (input candidate output : List Bool) :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .moveCandidate input (bit :: candidate)
          output true) =
      some (primeSelectorIdleCfg .moveCandidate input candidate
        (bit :: output) true) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorObserve, primeSelectorObservedPresent,
    primeSelectorObservedBit, primeSelectorResetObserved, haltList,
    Function.update]

private theorem primeSelector_step_moveCandidate_nil
    (input output : List Bool) :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .moveCandidate input [] output true) =
      some (primeSelectorScanCfg input [] output true) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorScanCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedPresent, primeSelectorResetObserved,
    Function.update]
  rw [candidatePrime_initList_empty_stacks]

private theorem primeSelector_step_discardCount_cons
    (bit : Bool) (candidate output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorDiscardCfg (bit :: candidate) output found) =
      some (primeSelectorDiscardCfg candidate output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorDiscardCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorObserve, primeSelectorObservedPresent,
    primeSelectorResetObserved, Function.update]
  rw [show ((initList unaryCandidatePrimeComputer
      (bit :: candidate)).stk unaryCandidatePrimeComputer.k₀).tail =
        candidate by simp [initList]]
  rw [candidatePrime_initList_pop_input]

private theorem primeSelector_step_discardCount_nil
    (output : List Bool) (found : Bool) :
    primeSelectorComputer.step
        (primeSelectorDiscardCfg [] output found) =
      some (primeSelectorIdleCfg .finalize [] [] output found) := by
  simp [primeSelectorComputer, FinTM2.step, primeSelectorDiscardCfg,
    primeSelectorIdleCfg, primeSelectorCfg, primeSelectorProgram,
    primeSelectorStackContents, primeSelectorObserve,
    primeSelectorObservedPresent, primeSelectorResetObserved,
    Function.update]
  rw [candidatePrime_initList_empty_stacks]

private theorem primeSelector_step_finalize_found (output : List Bool) :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .finalize [] [] output true) =
      some (haltList primeSelectorComputer output) := by
  rw [primeSelector_haltList_eq_cfg]
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorInitialState, Function.update]

private theorem primeSelector_step_finalize_none :
    primeSelectorComputer.step
        (primeSelectorIdleCfg .finalize [] [] [] false) =
      some (haltList primeSelectorComputer (unaryEncodeNat 2)) := by
  rw [primeSelector_haltList_eq_cfg]
  simp [primeSelectorComputer, FinTM2.step, primeSelectorIdleCfg,
    primeSelectorCfg, primeSelectorProgram, primeSelectorStackContents,
    primeSelectorInitialState, unaryEncodeNat, Function.update]

private def primeSelector_scan_unary_evals
    (n : ℕ) (input candidate output : List Bool) (found : Bool) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg
        (List.replicate n true ++ input) candidate output found)
      (some (primeSelectorScanCfg input
        (List.replicate n true ++ candidate) output found)) n := by
  induction n generalizing candidate with
  | zero =>
      exact EvalsToInTime.refl primeSelectorComputer.step _
  | succ n ih =>
      let middle := primeSelectorScanCfg
        (List.replicate n true ++ input) (true :: candidate) output found
      have hone : EvalsToInTime primeSelectorComputer.step
          (primeSelectorScanCfg
            (List.replicate (n + 1) true ++ input) candidate output found)
          (some middle) 1 :=
        primeSelectorEvalsToInTimeOne (by
          simpa [middle, List.replicate_succ] using
            primeSelector_step_scan_true
              (List.replicate n true ++ input) candidate output found)
      have hrest := ih (true :: candidate)
      have htrans := EvalsToInTime.trans primeSelectorComputer.step
        1 n
        (primeSelectorScanCfg
          (List.replicate (n + 1) true ++ input) candidate output found)
        middle
        (some (primeSelectorScanCfg input
          (List.replicate (n + 1) true ++ candidate) output found))
        hone
        (by
          simpa [middle, List.replicate_succ', List.replicate_add,
            List.append_assoc] using hrest)
      simpa [Nat.add_comm] using htrans

private def primeSelector_clearCandidate_evals
    (candidate input output : List Bool) (found : Bool) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorIdleCfg .clearCandidate input candidate output found)
      (some (primeSelectorScanCfg input [] output found))
      (candidate.length + 1) := by
  induction candidate with
  | nil =>
      exact primeSelectorEvalsToInTimeOne
        (primeSelector_step_clearCandidate_nil input output found)
  | cons bit candidate ih =>
      let middle := primeSelectorIdleCfg .clearCandidate input candidate
        output found
      have hone := primeSelectorEvalsToInTimeOne
        (primeSelector_step_clearCandidate_cons bit input candidate output found)
      have htrans := EvalsToInTime.trans primeSelectorComputer.step
        1 (candidate.length + 1)
        (primeSelectorIdleCfg .clearCandidate input (bit :: candidate)
          output found)
        middle
        (some (primeSelectorScanCfg input [] output found))
        (by simpa [middle] using hone)
        (by simpa [middle] using ih)
      simpa [Nat.add_assoc, Nat.add_comm] using htrans

private def primeSelector_clearSelected_evals
    (output input candidate : List Bool) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorIdleCfg .clearSelected input candidate output true)
      (some (primeSelectorIdleCfg .moveCandidate input candidate [] true))
      (output.length + 1) := by
  induction output with
  | nil =>
      exact primeSelectorEvalsToInTimeOne
        (primeSelector_step_clearSelected_nil input candidate)
  | cons bit output ih =>
      let middle := primeSelectorIdleCfg .clearSelected input candidate
        output true
      have hone := primeSelectorEvalsToInTimeOne
        (primeSelector_step_clearSelected_cons bit input candidate output)
      have htrans := EvalsToInTime.trans primeSelectorComputer.step
        1 (output.length + 1)
        (primeSelectorIdleCfg .clearSelected input candidate (bit :: output)
          true)
        middle
        (some (primeSelectorIdleCfg .moveCandidate input candidate [] true))
        (by simpa [middle] using hone)
        (by simpa [middle] using ih)
      simpa [Nat.add_assoc, Nat.add_comm] using htrans

private def primeSelector_moveCandidate_evals
    (candidate input output : List Bool) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorIdleCfg .moveCandidate input candidate output true)
      (some (primeSelectorScanCfg input [] (candidate.reverse ++ output) true))
      (candidate.length + 1) := by
  induction candidate generalizing output with
  | nil =>
      simpa using primeSelectorEvalsToInTimeOne
        (primeSelector_step_moveCandidate_nil input output)
  | cons bit candidate ih =>
      let middle := primeSelectorIdleCfg .moveCandidate input candidate
        (bit :: output) true
      have hone := primeSelectorEvalsToInTimeOne
        (primeSelector_step_moveCandidate_cons bit input candidate output)
      have hrest := ih (bit :: output)
      have htrans := EvalsToInTime.trans primeSelectorComputer.step
        1 (candidate.length + 1)
        (primeSelectorIdleCfg .moveCandidate input (bit :: candidate)
          output true)
        middle
        (some (primeSelectorScanCfg input []
          ((bit :: candidate).reverse ++ output) true))
        (by simpa [middle] using hone)
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm] using htrans

private def primeSelector_discardCount_evals
    (candidate output : List Bool) (found : Bool) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorDiscardCfg candidate output found)
      (some (primeSelectorIdleCfg .finalize [] [] output found))
      (candidate.length + 1) := by
  induction candidate with
  | nil =>
      exact primeSelectorEvalsToInTimeOne
        (primeSelector_step_discardCount_nil output found)
  | cons bit candidate ih =>
      let middle := primeSelectorDiscardCfg candidate output found
      have hone := primeSelectorEvalsToInTimeOne
        (primeSelector_step_discardCount_cons bit candidate output found)
      have htrans := EvalsToInTime.trans primeSelectorComputer.step
        1 (candidate.length + 1)
        (primeSelectorDiscardCfg (bit :: candidate) output found)
        middle
        (some (primeSelectorIdleCfg .finalize [] [] output found))
        (by simpa [middle] using hone)
        (by simpa [middle] using ih)
      simpa [Nat.add_assoc, Nat.add_comm] using htrans

private def primeSelectorFinalizeEvals (selection : Option ℕ) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorIdleCfg .finalize [] []
        (encodePrimeSelection selection) (primeSelectionFound selection))
      (some (haltList primeSelectorComputer
        (unaryEncodeNat (selection.getD 2)))) 1 := by
  cases selection with
  | none =>
      simpa [encodePrimeSelection, primeSelectionFound] using
        primeSelectorEvalsToInTimeOne primeSelector_step_finalize_none
  | some candidate =>
      simpa [encodePrimeSelection, primeSelectionFound] using
        primeSelectorEvalsToInTimeOne
          (primeSelector_step_finalize_found (unaryEncodeNat candidate))

/-- A coarse exact stage budget.  The old selected value is included because
an accepted candidate first erases that output before installing itself. -/
private def primeSelectorCandidateTime
    (candidate : ℕ) (selection : Option ℕ) : ℕ :=
  64 * (candidate + 1) ^ 2 + 2 * candidate +
    (encodePrimeSelection selection).length + 5

private noncomputable def primeSelector_candidate_evals
    (candidate : ℕ) (input : List Bool) (hinput : input ≠ [])
    (selection : Option ℕ) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg
        (RawUnaryNatList.segment candidate ++ input) []
        (encodePrimeSelection selection) (primeSelectionFound selection))
      (some (primeSelectorScanCfg input []
        (encodePrimeSelection
          (if unaryCandidatePrime candidate then some candidate else selection))
        (primeSelectionFound
          (if unaryCandidatePrime candidate then some candidate else selection))))
      (primeSelectorCandidateTime candidate selection) := by
  rcases input with _ | ⟨bit, input⟩
  · contradiction
  let output := encodePrimeSelection selection
  let found := primeSelectionFound selection
  have hscan := primeSelector_scan_unary_evals candidate
    (false :: bit :: input) [] output found
  let afterScan := primeSelectorScanCfg (false :: bit :: input)
    (unaryEncodeNat candidate) output found
  have hscan' : EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg
        (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
      (some afterScan) candidate := by
    simpa [afterScan, RawUnaryNatList.segment,
      unaryEncodeNat_eq_replicate_true] using hscan
  have hseparator := primeSelectorEvalsToInTimeOne
    (primeSelector_step_scan_false (bit :: input)
      (unaryEncodeNat candidate) output found)
  let afterSeparator := primeSelectorLookaheadCfg (bit :: input)
    (unaryEncodeNat candidate) output found
  have hlookahead := primeSelectorEvalsToInTimeOne
    (primeSelector_step_lookahead_present bit input
      (unaryEncodeNat candidate) output found)
  let componentStart := primeSelectorLiftCfg (bit :: input)
    (unaryEncodeNat candidate) output found
    (initList unaryCandidatePrimeComputer (unaryEncodeNat candidate))
  have hparseFirst := EvalsToInTime.trans primeSelectorComputer.step
    candidate 1
    (primeSelectorScanCfg
      (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
    afterScan (some afterSeparator)
    hscan' (by simpa [afterScan, afterSeparator] using hseparator)
  have hparseFirst' : EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg
        (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
      (some afterSeparator) (candidate + 1) :=
    evalsToInTimeMono hparseFirst (by omega)
  have hparse := EvalsToInTime.trans primeSelectorComputer.step
    (candidate + 1) 1
    (primeSelectorScanCfg
      (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
    afterSeparator (some componentStart)
    hparseFirst'
    (by simpa [afterSeparator, componentStart] using hlookahead)
  have hparse' : EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg
        (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
      (some componentStart) (candidate + 2) :=
    evalsToInTimeMono hparse (by omega)
  have hcomponentBase : EvalsToInTime unaryCandidatePrimeComputer.step
      (initList unaryCandidatePrimeComputer (unaryEncodeNat candidate))
      (some (haltList unaryCandidatePrimeComputer
        [unaryCandidatePrime candidate]))
      (64 * (candidate + 1) ^ 2) := by
    simpa [TM2OutputsInTime, encodeBool, List.pure_def] using
      unaryCandidatePrime_outputsInTime candidate
  have hcomponent := primeSelector_lift_evals
    (bit :: input) (unaryEncodeNat candidate) output found hcomponentBase
  have hfirst := EvalsToInTime.trans primeSelectorComputer.step
    (candidate + 2) (64 * (candidate + 1) ^ 2)
    (primeSelectorScanCfg
      (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
    componentStart
    (some (primeSelectorLiftCfg (bit :: input)
      (unaryEncodeNat candidate) output found
      (haltList unaryCandidatePrimeComputer [unaryCandidatePrime candidate])))
    hparse'
    (by simpa [componentStart] using hcomponent)
  by_cases hprime : unaryCandidatePrime candidate
  · have hfirstTrue : EvalsToInTime primeSelectorComputer.step
        (primeSelectorScanCfg
          (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
        (some (primeSelectorLiftCfg (bit :: input)
          (unaryEncodeNat candidate) output found
          (haltList unaryCandidatePrimeComputer [true])))
        (64 * (candidate + 1) ^ 2 + (candidate + 2)) := by
      simpa [hprime] using hfirst
    have hresult := primeSelectorEvalsToInTimeOne
      (primeSelector_step_result_true (bit :: input)
        (unaryEncodeNat candidate) output found)
    have hclear := primeSelector_clearSelected_evals output
      (bit :: input) (unaryEncodeNat candidate)
    have hmove := primeSelector_moveCandidate_evals
      (unaryEncodeNat candidate) (bit :: input) []
    have hsecond := EvalsToInTime.trans primeSelectorComputer.step
      1 (output.length + 1)
      (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
        output found (haltList unaryCandidatePrimeComputer [true]))
      (primeSelectorIdleCfg .clearSelected (bit :: input)
        (unaryEncodeNat candidate) output true)
      (some (primeSelectorIdleCfg .moveCandidate (bit :: input)
        (unaryEncodeNat candidate) [] true))
      (by simpa using hresult) (by simpa using hclear)
    have hsecond' : EvalsToInTime primeSelectorComputer.step
        (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
          output found (haltList unaryCandidatePrimeComputer [true]))
        (some (primeSelectorIdleCfg .moveCandidate (bit :: input)
          (unaryEncodeNat candidate) [] true))
        (output.length + 2) :=
      evalsToInTimeMono hsecond (by omega)
    have hcleanup := EvalsToInTime.trans primeSelectorComputer.step
      (output.length + 2) (candidate + 1)
      (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
        output found (haltList unaryCandidatePrimeComputer [true]))
      (primeSelectorIdleCfg .moveCandidate (bit :: input)
        (unaryEncodeNat candidate) [] true)
      (some (primeSelectorScanCfg (bit :: input) []
        (unaryEncodeNat candidate) true))
      hsecond'
      (by simpa [unaryEncodeNat_length, unaryEncodeNat_reverse] using hmove)
    have hcleanup' : EvalsToInTime primeSelectorComputer.step
        (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
          output found (haltList unaryCandidatePrimeComputer [true]))
        (some (primeSelectorScanCfg (bit :: input) []
          (unaryEncodeNat candidate) true))
        (candidate + output.length + 3) :=
      evalsToInTimeMono hcleanup (by omega)
    have hall := EvalsToInTime.trans primeSelectorComputer.step
      (64 * (candidate + 1) ^ 2 + (candidate + 2))
      (candidate + output.length + 3)
      (primeSelectorScanCfg
        (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
      (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
        output found (haltList unaryCandidatePrimeComputer [true]))
      (some (primeSelectorScanCfg (bit :: input) []
        (unaryEncodeNat candidate) true))
      hfirstTrue hcleanup'
    have hmono : EvalsToInTime primeSelectorComputer.step
        (primeSelectorScanCfg
          (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
        (some (primeSelectorScanCfg (bit :: input) []
          (unaryEncodeNat candidate) true))
        (primeSelectorCandidateTime candidate selection) :=
      evalsToInTimeMono hall (by
        unfold primeSelectorCandidateTime
        simp only [output]
        omega)
    simpa [output, found, hprime, encodePrimeSelection,
      primeSelectionFound] using hmono
  · have hfirstFalse : EvalsToInTime primeSelectorComputer.step
        (primeSelectorScanCfg
          (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
        (some (primeSelectorLiftCfg (bit :: input)
          (unaryEncodeNat candidate) output found
          (haltList unaryCandidatePrimeComputer [false])))
        (64 * (candidate + 1) ^ 2 + (candidate + 2)) := by
      simpa [hprime] using hfirst
    have hresult := primeSelectorEvalsToInTimeOne
      (primeSelector_step_result_false (bit :: input)
        (unaryEncodeNat candidate) output found)
    have hclear := primeSelector_clearCandidate_evals
      (unaryEncodeNat candidate) (bit :: input) output found
    have hcleanup := EvalsToInTime.trans primeSelectorComputer.step
      1 (candidate + 1)
      (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
        output found (haltList unaryCandidatePrimeComputer [false]))
      (primeSelectorIdleCfg .clearCandidate (bit :: input)
        (unaryEncodeNat candidate) output found)
      (some (primeSelectorScanCfg (bit :: input) [] output found))
      (by simpa using hresult)
      (by simpa [unaryEncodeNat_length] using hclear)
    have hcleanup' : EvalsToInTime primeSelectorComputer.step
        (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
          output found (haltList unaryCandidatePrimeComputer [false]))
        (some (primeSelectorScanCfg (bit :: input) [] output found))
        (candidate + 2) :=
      evalsToInTimeMono hcleanup (by omega)
    have hall := EvalsToInTime.trans primeSelectorComputer.step
      (64 * (candidate + 1) ^ 2 + (candidate + 2))
      (candidate + 2)
      (primeSelectorScanCfg
        (RawUnaryNatList.segment candidate ++ bit :: input) [] output found)
      (primeSelectorLiftCfg (bit :: input) (unaryEncodeNat candidate)
        output found (haltList unaryCandidatePrimeComputer [false]))
      (some (primeSelectorScanCfg (bit :: input) [] output found))
      hfirstFalse hcleanup'
    exact evalsToInTimeMono
      (by simpa [output, found, hprime] using hall)
      (by simp [primeSelectorCandidateTime]; omega)

private def encodedUnaryCandidateFields (candidates : List ℕ) : List Bool :=
  candidates.reverse.flatMap RawUnaryNatList.segment

@[simp]
private theorem encodedUnaryCandidateFields_cons
    (candidate : ℕ) (candidates : List ℕ) :
    encodedUnaryCandidateFields (candidate :: candidates) =
      encodedUnaryCandidateFields candidates ++
        RawUnaryNatList.segment candidate := by
  simp [encodedUnaryCandidateFields, List.reverse_cons, List.flatMap_append]

private def primeSelectorCandidatesTime : List ℕ → ℕ
  | [] => 0
  | candidate :: candidates =>
      primeSelectorCandidateTime candidate
          (firstUnaryCandidatePrime? candidates) +
        primeSelectorCandidatesTime candidates

private noncomputable def primeSelector_candidates_evals
    (candidates : List ℕ) (input : List Bool) (hinput : input ≠ []) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg
        (encodedUnaryCandidateFields candidates ++ input) [] [] false)
      (some (primeSelectorScanCfg input []
        (encodePrimeSelection (firstUnaryCandidatePrime? candidates))
        (primeSelectionFound (firstUnaryCandidatePrime? candidates))))
      (primeSelectorCandidatesTime candidates) := by
  induction candidates generalizing input with
  | nil =>
      exact EvalsToInTime.refl primeSelectorComputer.step _
  | cons candidate candidates ih =>
      let fieldInput := RawUnaryNatList.segment candidate ++ input
      have hfieldInput : fieldInput ≠ [] := by
        simp [fieldInput, RawUnaryNatList.segment]
      have hrest := ih fieldInput hfieldInput
      let selection := firstUnaryCandidatePrime? candidates
      let middle := primeSelectorScanCfg fieldInput []
        (encodePrimeSelection selection) (primeSelectionFound selection)
      have hcandidate := primeSelector_candidate_evals
        candidate input hinput selection
      have htrans := EvalsToInTime.trans primeSelectorComputer.step
        (primeSelectorCandidatesTime candidates)
        (primeSelectorCandidateTime candidate selection)
        (primeSelectorScanCfg
          (encodedUnaryCandidateFields (candidate :: candidates) ++ input)
          [] [] false)
        middle
        (some (primeSelectorScanCfg input []
          (encodePrimeSelection
            (firstUnaryCandidatePrime? (candidate :: candidates)))
          (primeSelectionFound
            (firstUnaryCandidatePrime? (candidate :: candidates)))))
        (by
          simpa [middle, fieldInput, encodedUnaryCandidateFields_cons,
            List.append_assoc, selection] using hrest)
        (by
          by_cases hprime : unaryCandidatePrime candidate
          · simpa [middle, fieldInput, selection, firstUnaryCandidatePrime?,
              hprime] using hcandidate
          · simpa [middle, fieldInput, selection, firstUnaryCandidatePrime?,
              hprime] using hcandidate)
      simpa [primeSelectorCandidatesTime, selection, Nat.add_comm] using htrans

private noncomputable def primeSelector_count_evals
    (count : ℕ) (selection : Option ℕ) :
    EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg (RawUnaryNatList.segment count) []
        (encodePrimeSelection selection) (primeSelectionFound selection))
      (some (haltList primeSelectorComputer
        (unaryEncodeNat (selection.getD 2))))
      (2 * count + 4) := by
  let output := encodePrimeSelection selection
  let found := primeSelectionFound selection
  have hscan := primeSelector_scan_unary_evals count [false] [] output found
  let afterScan := primeSelectorScanCfg [false]
    (unaryEncodeNat count) output found
  have hscan' : EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
      (some afterScan) count := by
    simpa [afterScan, RawUnaryNatList.segment,
      unaryEncodeNat_eq_replicate_true] using hscan
  have hseparator := primeSelectorEvalsToInTimeOne
    (primeSelector_step_scan_false [] (unaryEncodeNat count) output found)
  let afterSeparator := primeSelectorLookaheadCfg []
    (unaryEncodeNat count) output found
  have hlookahead := primeSelectorEvalsToInTimeOne
    (primeSelector_step_lookahead_nil (unaryEncodeNat count) output found)
  let afterLookahead := primeSelectorDiscardCfg (unaryEncodeNat count)
    output found
  have hdiscard := primeSelector_discardCount_evals
    (unaryEncodeNat count) output found
  let beforeFinalize := primeSelectorIdleCfg .finalize [] [] output found
  have hfinal := primeSelectorFinalizeEvals selection
  have hfirst := EvalsToInTime.trans primeSelectorComputer.step
    count 1
    (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
    afterScan (some afterSeparator)
    hscan' (by simpa [afterScan, afterSeparator] using hseparator)
  have hfirst' : EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
      (some afterSeparator) (count + 1) :=
    evalsToInTimeMono hfirst (by omega)
  have hsecond := EvalsToInTime.trans primeSelectorComputer.step
    (count + 1) 1
    (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
    afterSeparator (some afterLookahead)
    hfirst' (by simpa [afterSeparator, afterLookahead] using hlookahead)
  have hsecond' : EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
      (some afterLookahead) (count + 2) :=
    evalsToInTimeMono hsecond (by omega)
  have hthird := EvalsToInTime.trans primeSelectorComputer.step
    (count + 2) (count + 1)
    (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
    afterLookahead (some beforeFinalize)
    (by simpa [afterLookahead] using hsecond')
    (by simpa [afterLookahead, beforeFinalize, unaryEncodeNat_length] using
      hdiscard)
  have hthird' : EvalsToInTime primeSelectorComputer.step
      (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
      (some beforeFinalize) (2 * count + 3) :=
    evalsToInTimeMono hthird (by omega)
  have hall := EvalsToInTime.trans primeSelectorComputer.step
    (2 * count + 3) 1
    (primeSelectorScanCfg (RawUnaryNatList.segment count) [] output found)
    beforeFinalize
    (some (haltList primeSelectorComputer
      (unaryEncodeNat (selection.getD 2))))
    (by simpa [beforeFinalize] using hthird')
    (by simpa [beforeFinalize, output, found] using hfinal)
  exact evalsToInTimeMono
    (by simpa [output, found] using hall) (by omega)

private theorem rawUnaryNatList_encode_eq_fields (candidates : List ℕ) :
    RawUnaryNatList.encode candidates =
      encodedUnaryCandidateFields candidates ++
        RawUnaryNatList.segment candidates.length := by
  simp [RawUnaryNatList.encode, RawUnaryNatList.payloads,
    encodedUnaryCandidateFields, List.reverse_cons, List.flatMap_append]

private theorem primeSelector_initList_eq_scanCfg (input : List Bool) :
    initList primeSelectorComputer input =
      primeSelectorScanCfg input [] [] false := by
  unfold initList primeSelectorScanCfg primeSelectorCfg
    primeSelectorComputer primeSelectorInitialState
  congr 2
  funext index
  rcases index with outer | index
  · cases outer <;> rfl
  · rw [primeSelectorStackContents, candidatePrime_initList_empty_stacks]
    rfl

/-- The driver computes the first accepted unary candidate with a concrete
stage-sensitive runtime bound. -/
noncomputable def primeSelector_outputsInTime (candidates : List ℕ) :
    TM2OutputsInTime primeSelectorComputer
      (RawUnaryNatList.encode candidates)
      (some (unaryEncodeNat (selectUnaryCandidatePrime candidates)))
      (primeSelectorCandidatesTime candidates + 2 * candidates.length + 4) := by
  let countInput := RawUnaryNatList.segment candidates.length
  have hcountInput : countInput ≠ [] := by
    simp [countInput, RawUnaryNatList.segment]
  have hcandidates := primeSelector_candidates_evals
    candidates countInput hcountInput
  let selection := firstUnaryCandidatePrime? candidates
  have hcount := primeSelector_count_evals candidates.length selection
  have htrans := EvalsToInTime.trans primeSelectorComputer.step
    (primeSelectorCandidatesTime candidates) (2 * candidates.length + 4)
    (primeSelectorScanCfg (RawUnaryNatList.encode candidates) [] [] false)
    (primeSelectorScanCfg countInput []
      (encodePrimeSelection selection) (primeSelectionFound selection))
    (some (haltList primeSelectorComputer
      (unaryEncodeNat (selectUnaryCandidatePrime candidates))))
    (by
      rw [rawUnaryNatList_encode_eq_fields]
      simpa [countInput, selection] using hcandidates)
    (by simpa [countInput, selection, selectUnaryCandidatePrime] using hcount)
  rw [TM2OutputsInTime, primeSelector_initList_eq_scanCfg]
  simp only [Option.map_some]
  exact evalsToInTimeMono htrans (by omega)

private theorem nat_le_list_sum_of_mem {value : ℕ} {values : List ℕ}
    (hvalue : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => simp at hvalue
  | cons head tail ih =>
      rcases List.mem_cons.mp hvalue with rfl | htail
      · simp
      · have hle := ih htail
        simp only [List.sum_cons]
        omega

private theorem encodePrimeSelection_firstUnaryCandidatePrime?_length_le
    (candidates : List ℕ) (bound : ℕ)
    (hbound : ∀ candidate ∈ candidates, candidate ≤ bound) :
    (encodePrimeSelection
      (firstUnaryCandidatePrime? candidates)).length ≤ bound := by
  cases hselection : firstUnaryCandidatePrime? candidates with
  | none => simp [encodePrimeSelection]
  | some candidate =>
      have hmem := firstUnaryCandidatePrime?_mem hselection
      simpa [encodePrimeSelection, unaryEncodeNat_length] using
        hbound candidate hmem

private theorem primeSelectorCandidateTime_le
    (candidate bound : ℕ) (selection : Option ℕ)
    (hcandidate : candidate ≤ bound)
    (hselection : (encodePrimeSelection selection).length ≤ bound) :
    primeSelectorCandidateTime candidate selection ≤
      70 * (bound + 1) ^ 2 := by
  have hpow : (candidate + 1) ^ 2 ≤ (bound + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  unfold primeSelectorCandidateTime
  nlinarith

private theorem primeSelectorCandidatesTime_le
    (candidates : List ℕ) (bound : ℕ)
    (hbound : ∀ candidate ∈ candidates, candidate ≤ bound) :
    primeSelectorCandidatesTime candidates ≤
      candidates.length * (70 * (bound + 1) ^ 2) := by
  induction candidates with
  | nil => simp [primeSelectorCandidatesTime]
  | cons candidate candidates ih =>
      have hcandidate : candidate ≤ bound :=
        hbound candidate (List.mem_cons_self)
      have htail : ∀ value ∈ candidates, value ≤ bound := by
        intro value hvalue
        exact hbound value (List.mem_cons_of_mem candidate hvalue)
      have hselection :=
        encodePrimeSelection_firstUnaryCandidatePrime?_length_le
          candidates bound htail
      have hstep := primeSelectorCandidateTime_le candidate bound
        (firstUnaryCandidatePrime? candidates) hcandidate hselection
      have hrest := ih htail
      simp only [primeSelectorCandidatesTime, List.length_cons]
      nlinarith

private theorem primeSelectorTime_le_cubic (candidates : List ℕ) :
    primeSelectorCandidatesTime candidates + 2 * candidates.length + 4 ≤
      80 * ((RawUnaryNatList.encode candidates).length + 1) ^ 3 := by
  let size := (RawUnaryNatList.encode candidates).length
  have hsum : candidates.sum ≤ size := by
    simp only [size, RawUnaryNatList.encode_length]
    omega
  have hlength : candidates.length ≤ size := by
    simp only [size, RawUnaryNatList.encode_length]
    omega
  have hvalues : ∀ candidate ∈ candidates, candidate ≤ size := by
    intro candidate hcandidate
    exact (nat_le_list_sum_of_mem hcandidate).trans hsum
  have hfields := primeSelectorCandidatesTime_le candidates size hvalues
  have hfields' : primeSelectorCandidatesTime candidates ≤
      size * (70 * (size + 1) ^ 2) :=
    hfields.trans (Nat.mul_le_mul_right (70 * (size + 1) ^ 2) hlength)
  have hone : 1 ≤ (size + 1) ^ 2 := by
    exact Nat.one_le_pow' 2 size
  calc
    primeSelectorCandidatesTime candidates + 2 * candidates.length + 4
        ≤ size * (70 * (size + 1) ^ 2) + 2 * size + 4 := by omega
    _ ≤ 80 * (size + 1) ^ 3 := by
      rw [show (size + 1) ^ 3 = (size + 1) * (size + 1) ^ 2 by ring]
      nlinarith

/-- Genuine polynomial time in the complete unary-list wire length for the
first-survivor driver.  This is independent of the separate producer/runtime
composition still needed by the full compiler. -/
noncomputable def primeSelectorComputableInPolyTime :
    @TM2ComputableInPolyTime (List ℕ) ℕ RawUnaryNatList.finEncoding
      unaryFinEncodingNat selectUnaryCandidatePrime where
  tm := primeSelectorComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 80 * (Polynomial.X + 1) ^ 3
  outputsFun candidates := by
    have hrun := primeSelector_outputsInTime candidates
    have hmono := evalsToInTimeMono hrun
      (primeSelectorTime_le_cubic candidates)
    simpa [RawUnaryNatList.finEncoding, unaryFinEncodingNat, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using
        hmono

/-- On the checked Bertrand stream, the driver emits exactly the selected
compiler prime. -/
theorem primeSelector_selects_firstBertrandPrime (q : ℕ) :
    selectUnaryCandidatePrime (bertrandCandidates q) =
      firstBertrandPrime q :=
  selectUnaryCandidatePrime_bertrandCandidates q

/-! ## Compiler-selected prime composition

The final prime-selection pass composes the native unary Bertrand producer
with the checked first-survivor selector.  The intermediate stream is
quadratic in the unary bound, so the selector's cubic wire-length bound gives
a degree-six bound in that bound.  This remains separate from the structural
CSP pass that must produce the unary distinct-symbol count.
-/

private def unaryBertrandCandidateAux :
    TM2ComputableAux Bool Bool where
  tm := unaryBertrandCandidateComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool

private def primeSelectorAux :
    TM2ComputableAux Bool Bool where
  tm := primeSelectorComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool

/-- Concrete sequential machine that chooses the compiler prime from a unary
distinct-symbol bound. -/
def selectedPrimeComputer : FinTM2 :=
  { compositionMachine unaryBertrandCandidateAux primeSelectorAux with
      initialState := rightState unaryBertrandCandidateAux primeSelectorAux
        primeSelectorAux.tm.initialState }

private def selectedPrimeStartCfg
    (state : ControlState unaryBertrandCandidateAux primeSelectorAux)
    (input : List Bool) : selectedPrimeComputer.Cfg where
  l := some (leftLabel unaryBertrandCandidateAux primeSelectorAux .count)
  var := state
  stk := transferLeftStacks unaryBertrandCandidateAux primeSelectorAux
    (unaryBertrandStackContents input [] [] [] [])

private theorem selectedPrime_initList_eq_cfg (input : List Bool) :
    initList selectedPrimeComputer input =
      selectedPrimeStartCfg
        (rightState unaryBertrandCandidateAux primeSelectorAux
          primeSelectorAux.tm.initialState) input := by
  unfold initList selectedPrimeComputer compositionMachine
    selectedPrimeStartCfg unaryBertrandCandidateAux primeSelectorAux
    unaryBertrandCandidateComputer primeSelectorComputer transferLeftStacks
    unaryBertrandStackContents extendStacks leftStacks transferLeftIndex
  congr 2
  funext index
  rcases index with (index | index)
  · rcases index with (index | index)
    · cases index <;> rfl
    · rfl
  · cases index
    rfl

private theorem selectedPrime_left_init_eq_cfg (input : List Bool) :
    liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
        (liftLeftControlCfg unaryBertrandCandidateAux primeSelectorAux
          (initList unaryBertrandCandidateAux.tm input)) =
      selectedPrimeStartCfg
        (leftState unaryBertrandCandidateAux primeSelectorAux
          unaryBertrandCandidateAux.tm.initialState) input := by
  simp only [unaryBertrandCandidateAux]
  rw [unaryBertrand_initList_eq_cfg]
  rfl

private theorem selectedPrime_start_step (input : List Bool) :
    selectedPrimeComputer.step
        (selectedPrimeStartCfg
          (rightState unaryBertrandCandidateAux primeSelectorAux
            primeSelectorAux.tm.initialState) input) =
      selectedPrimeComputer.step
        (selectedPrimeStartCfg
          (leftState unaryBertrandCandidateAux primeSelectorAux
            unaryBertrandCandidateAux.tm.initialState) input) := by
  cases input <;> rfl

private theorem selectedPrime_init_step (input : List Bool) :
    selectedPrimeComputer.step (initList selectedPrimeComputer input) =
      selectedPrimeComputer.step
        (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
          (liftLeftControlCfg unaryBertrandCandidateAux primeSelectorAux
            (initList unaryBertrandCandidateAux.tm input))) := by
  rw [selectedPrime_initList_eq_cfg, selectedPrime_left_init_eq_cfg]
  exact selectedPrime_start_step input

private theorem selectedPrime_haltList_eq (output : List Bool) :
    haltList selectedPrimeComputer output =
      rightPhaseCfg unaryBertrandCandidateAux primeSelectorAux (fun _ => []) []
        (haltList primeSelectorAux.tm output) := by
  unfold selectedPrimeComputer compositionMachine haltList rightPhaseCfg
    unaryBertrandCandidateAux primeSelectorAux unaryBertrandCandidateComputer
    primeSelectorComputer
  congr 2
  funext index
  rcases index with (index | index)
  · rcases index with (index | index)
    · cases index <;> simp [extendStacks, rightPhaseStacks,
        transferRightIndex]
      all_goals
        intro h
        cases h
    · rcases index with (outer | component)
      · cases outer <;> simp [extendStacks, rightPhaseStacks,
          transferRightIndex]
        all_goals
          intro h
          cases h
      · simp [extendStacks, rightPhaseStacks, transferRightIndex]
        intro h
        cases h
  · cases index
    simp [extendStacks, transferRightIndex]

private theorem selectedPrime_iterate_init
    (steps : ℕ) (hsteps : 0 < steps) (input : List Bool) :
    (flip Option.bind selectedPrimeComputer.step)^[steps]
        (some (initList selectedPrimeComputer input)) =
      (flip Option.bind selectedPrimeComputer.step)^[steps]
        (some (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
          (liftLeftControlCfg unaryBertrandCandidateAux primeSelectorAux
            (initList unaryBertrandCandidateAux.tm input)))) := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hsteps)
  rw [Function.iterate_succ_apply]
  change
    (flip Option.bind selectedPrimeComputer.step)^[remaining]
        (selectedPrimeComputer.step (initList selectedPrimeComputer input)) =
      (flip Option.bind selectedPrimeComputer.step)^[remaining]
        (selectedPrimeComputer.step
          (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
            (liftLeftControlCfg unaryBertrandCandidateAux primeSelectorAux
              (initList unaryBertrandCandidateAux.tm input))))
  rw [selectedPrime_init_step]

private noncomputable def selectedPrime_generator_evals (q : ℕ) :
    EvalsToInTime selectedPrimeComputer.step
      (initList selectedPrimeComputer (unaryEncodeNat q))
      (some (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
        (leftTransferEntryCfg unaryBertrandCandidateAux primeSelectorAux
          (haltList unaryBertrandCandidateAux.tm
            (RawUnaryNatList.encode (bertrandCandidates q))).var
          (haltList unaryBertrandCandidateAux.tm
            (RawUnaryNatList.encode (bertrandCandidates q))).stk)))
      (6 * (q + 1) ^ 2) := by
  let output := RawUnaryNatList.encode (bertrandCandidates q)
  have hgenerator : EvalsToInTime unaryBertrandCandidateAux.tm.step
      (initList unaryBertrandCandidateAux.tm (unaryEncodeNat q))
      (some (haltList unaryBertrandCandidateAux.tm output))
      (6 * (q + 1) ^ 2) := by
    simpa [unaryBertrandCandidateAux, output] using
      unaryBertrandCandidate_outputsInTime q
  have hpositive : 0 < hgenerator.steps := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have heq := hgenerator.evals_in_steps
    rw [hzero, Function.iterate_zero_apply] at heq
    injection heq with hcfg
    have hlabels := congrArg
      (fun cfg : unaryBertrandCandidateAux.tm.Cfg => cfg.l) hcfg
    simp [initList, haltList] at hlabels
  have hleftRun := compositionProgram_left_run_to_transfer
    unaryBertrandCandidateAux primeSelectorAux hgenerator.steps
    (initList unaryBertrandCandidateAux.tm (unaryEncodeNat q))
    (haltList unaryBertrandCandidateAux.tm output)
    unaryBertrandCandidateAux.tm.main [] rfl hgenerator.evals_in_steps rfl
  refine
    { steps := hgenerator.steps
      evals_in_steps := ?_
      steps_le_m := hgenerator.steps_le_m }
  rw [show selectedPrimeComputer.step =
      TM2.step (compositionProgram unaryBertrandCandidateAux primeSelectorAux) by
    rfl]
  calc
    (flip Option.bind
        (TM2.step
          (compositionProgram unaryBertrandCandidateAux primeSelectorAux)))^[
            hgenerator.steps]
        (some (initList selectedPrimeComputer (unaryEncodeNat q))) =
      (flip Option.bind selectedPrimeComputer.step)^[hgenerator.steps]
        (some (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
          (liftLeftControlCfg unaryBertrandCandidateAux primeSelectorAux
            (initList unaryBertrandCandidateAux.tm
              (unaryEncodeNat q))))) := by
        exact selectedPrime_iterate_init hgenerator.steps hpositive _
    _ = some (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
        (leftTransferEntryCfg unaryBertrandCandidateAux primeSelectorAux
          (haltList unaryBertrandCandidateAux.tm output).var
          (haltList unaryBertrandCandidateAux.tm output).stk)) := hleftRun

private def selectedPrimeRightContents (input : List Bool) :
    (index : StackIndex unaryBertrandCandidateAux.tm primeSelectorAux.tm) →
      List (StackAlphabet unaryBertrandCandidateAux.tm primeSelectorAux.tm
        index) :=
  rightStacks unaryBertrandCandidateAux.tm primeSelectorAux.tm
    (initList primeSelectorAux.tm input).stk

private theorem selectedPrime_rightEntryMachineCfg (input : List Bool) :
    rightEntryMachineCfg unaryBertrandCandidateAux primeSelectorAux
        (selectedPrimeRightContents input) =
      initList primeSelectorAux.tm input := by
  rfl

private theorem selectedPrime_transferStart_eq (output : List Bool) :
    liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
        (leftTransferEntryCfg unaryBertrandCandidateAux primeSelectorAux
          (haltList unaryBertrandCandidateAux.tm output).var
          (haltList unaryBertrandCandidateAux.tm output).stk) =
      transferActionCfg unaryBertrandCandidateAux primeSelectorAux
        (.phase .reverseOutput)
        (leftState unaryBertrandCandidateAux primeSelectorAux
          unaryBertrandCandidateAux.tm.initialState)
        (Function.update
          (Function.update (fun _ => []) (Sum.inr primeSelectorAux.tm.k₀) [])
          (Sum.inl unaryBertrandCandidateAux.tm.k₁) output) [] := by
  simp only [unaryBertrandCandidateAux]
  rw [unaryBertrand_haltList_eq_cfg]
  unfold liftScratchCfg leftTransferEntryCfg transferActionCfg
    unaryBertrandCfg unaryBertrandStackContents primeSelectorAux
    primeSelectorComputer leftStacks extendStacks
  congr 2
  funext index
  rcases index with (index | index)
  · rcases index with (index | index)
    · cases index <;> rfl
    · rcases index with (outer | component)
      · cases outer <;> rfl
      · rfl
  · cases index
    rfl

private theorem selectedPrime_transferFinish_eq (output : List Bool) :
    rightEntryCfg unaryBertrandCandidateAux primeSelectorAux
        (selectedPrimeRightContents output) [] =
      rightEntryCfg unaryBertrandCandidateAux primeSelectorAux
        (Function.update
          (Function.update (fun _ => [])
            (Sum.inl unaryBertrandCandidateAux.tm.k₁) [])
          (Sum.inr primeSelectorAux.tm.k₀)
          (output.map (middleAlphabetEquiv unaryBertrandCandidateAux
            primeSelectorAux) ++ [])) [] := by
  congr 2
  unfold selectedPrimeRightContents
  unfold rightStacks middleAlphabetEquiv unaryBertrandCandidateAux
    unaryBertrandCandidateComputer primeSelectorAux primeSelectorComputer
  funext index
  rcases index with (index | index)
  · simp [Function.update]
    intro h
    cases h
    rfl
  · by_cases hindex : index = (Sum.inl PrimeSelectorOuterStack.input)
    · subst index
      simp [initList, Function.update]
      induction output with
      | nil => rfl
      | cons head tail ih =>
          simp only [List.map_cons]
          exact congrArg (fun xs : List Bool => head :: xs) ih
    · simp [initList, Function.update, hindex]
      intro h
      exact (hindex (Sum.inr.inj h)).elim

private def selectedPrime_transfer_evals (q : ℕ) :
    EvalsToInTime selectedPrimeComputer.step
      (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
        (leftTransferEntryCfg unaryBertrandCandidateAux primeSelectorAux
          (haltList unaryBertrandCandidateAux.tm
            (RawUnaryNatList.encode (bertrandCandidates q))).var
          (haltList unaryBertrandCandidateAux.tm
            (RawUnaryNatList.encode (bertrandCandidates q))).stk))
      (some (rightEntryCfg unaryBertrandCandidateAux primeSelectorAux
        (selectedPrimeRightContents
          (RawUnaryNatList.encode (bertrandCandidates q))) []))
      (4 * (RawUnaryNatList.encode (bertrandCandidates q)).length + 4) := by
  let output := RawUnaryNatList.encode (bertrandCandidates q)
  refine
    { steps := 4 * output.length + 4
      evals_in_steps := ?_
      steps_le_m := Nat.le_refl _ }
  rw [selectedPrime_transferStart_eq output,
    selectedPrime_transferFinish_eq output]
  exact compositionProgram_transfer_whole_list unaryBertrandCandidateAux
    primeSelectorAux
    (leftState unaryBertrandCandidateAux primeSelectorAux
      unaryBertrandCandidateAux.tm.initialState)
    (fun _ => []) output []

private theorem selectedPrime_rightEntry_eq (input : List Bool) :
    rightEntryCfg unaryBertrandCandidateAux primeSelectorAux
        (selectedPrimeRightContents input) [] =
      rightPhaseCfg unaryBertrandCandidateAux primeSelectorAux (fun _ => []) []
        (initList primeSelectorAux.tm input) := by
  rw [rightEntryCfg_eq_rightPhaseCfg,
    selectedPrime_rightEntryMachineCfg]
  congr 1

private noncomputable def selectedPrime_second_evals (q : ℕ) :
    EvalsToInTime selectedPrimeComputer.step
      (rightEntryCfg unaryBertrandCandidateAux primeSelectorAux
        (selectedPrimeRightContents
          (RawUnaryNatList.encode (bertrandCandidates q))) [])
      (some (haltList selectedPrimeComputer
        (unaryEncodeNat (selectPrimeAbove q))))
      (80 *
        ((RawUnaryNatList.encode (bertrandCandidates q)).length + 1) ^ 3) := by
  let input := RawUnaryNatList.encode (bertrandCandidates q)
  let selected := selectUnaryCandidatePrime (bertrandCandidates q)
  have hsecondExact : EvalsToInTime primeSelectorAux.tm.step
      (initList primeSelectorAux.tm input)
      (some (haltList primeSelectorAux.tm (unaryEncodeNat selected)))
      (primeSelectorCandidatesTime (bertrandCandidates q) + 2 * q + 4) := by
    simpa [primeSelectorAux, input, selected, bertrandCandidates_length] using
      primeSelector_outputsInTime (bertrandCandidates q)
  have hsecond : EvalsToInTime primeSelectorAux.tm.step
      (initList primeSelectorAux.tm input)
      (some (haltList primeSelectorAux.tm (unaryEncodeNat selected)))
      (80 * (input.length + 1) ^ 3) :=
    evalsToInTimeMono hsecondExact (by
      simpa [input, bertrandCandidates_length] using
        primeSelectorTime_le_cubic (bertrandCandidates q))
  have hrightRun := compositionProgram_right_run unaryBertrandCandidateAux
    primeSelectorAux hsecond.steps
    (initList primeSelectorAux.tm input)
    (haltList primeSelectorAux.tm (unaryEncodeNat selected))
    (fun _ => []) [] hsecond.evals_in_steps
  refine
    { steps := hsecond.steps
      evals_in_steps := ?_
      steps_le_m := hsecond.steps_le_m }
  rw [selectedPrime_rightEntry_eq]
  change (flip Option.bind selectedPrimeComputer.step)^[hsecond.steps]
      (some (rightPhaseCfg unaryBertrandCandidateAux primeSelectorAux
        (fun _ => []) [] (initList primeSelectorAux.tm input))) =
    some (haltList selectedPrimeComputer (unaryEncodeNat (selectPrimeAbove q)))
  rw [selectedPrime_haltList_eq]
  simpa [input, selected, primeSelector_selects_firstBertrandPrime,
    firstBertrandPrime_eq_selectPrimeAbove] using hrightRun

private theorem selectedPrimeTime_le_degreeSix (q : ℕ) :
    (80 * ((RawUnaryNatList.encode (bertrandCandidates q)).length + 1) ^ 3) +
        (4 * (RawUnaryNatList.encode (bertrandCandidates q)).length + 4 +
          6 * (q + 1) ^ 2) ≤
      1000 * (q + 1) ^ 6 := by
  have hstream := unaryBertrandCandidateStream_length_le q
  have hstream' :
      (RawUnaryNatList.encode (bertrandCandidates q)).length + 1 ≤
        2 * (q + 1) ^ 2 := by
    nlinarith
  have hcubic := Nat.pow_le_pow_left hstream' 3
  have hlinear :
      (RawUnaryNatList.encode (bertrandCandidates q)).length ≤
        2 * (q + 1) ^ 2 := by
    omega
  calc
    80 * ((RawUnaryNatList.encode (bertrandCandidates q)).length + 1) ^ 3 +
          (4 * (RawUnaryNatList.encode (bertrandCandidates q)).length + 4 +
            6 * (q + 1) ^ 2)
        ≤ 80 * (2 * (q + 1) ^ 2) ^ 3 +
          (4 * (2 * (q + 1) ^ 2) + 4 + 6 * (q + 1) ^ 2) := by
            omega
    _ ≤ 1000 * (q + 1) ^ 6 := by
      rw [show (2 * (q + 1) ^ 2) ^ 3 = 8 * (q + 1) ^ 6 by ring]
      have hqpow : (q + 1) ^ 2 ≤ (q + 1) ^ 6 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hpone : 1 ≤ (q + 1) ^ 6 := Nat.one_le_pow' 6 q
      have hrest :
          4 * (2 * (q + 1) ^ 2) + 4 + 6 * (q + 1) ^ 2 ≤
            18 * (q + 1) ^ 6 := by
        calc
          4 * (2 * (q + 1) ^ 2) + 4 + 6 * (q + 1) ^ 2 =
              14 * (q + 1) ^ 2 + 4 := by ring
          _ ≤ 14 * (q + 1) ^ 6 + 4 :=
            Nat.add_le_add_right (Nat.mul_le_mul_left 14 hqpow) 4
          _ ≤ 18 * (q + 1) ^ 6 := by omega
      omega

/-- The composed machine emits the compiler-selected prime in polynomial time
from the unary distinct-symbol bound, including the explicit `q = 0, 1`
conventions. -/
noncomputable def selectedPrime_outputsInTime (q : ℕ) :
    TM2OutputsInTime selectedPrimeComputer (unaryEncodeNat q)
      (some (unaryEncodeNat (selectPrimeAbove q)))
      (1000 * (q + 1) ^ 6) := by
  let stream := RawUnaryNatList.encode (bertrandCandidates q)
  have hgenerator := selectedPrime_generator_evals q
  have htransfer := selectedPrime_transfer_evals q
  have hsecond := selectedPrime_second_evals q
  have hfirst := EvalsToInTime.trans selectedPrimeComputer.step
    (6 * (q + 1) ^ 2) (4 * stream.length + 4)
    (initList selectedPrimeComputer (unaryEncodeNat q))
    (liftScratchCfg unaryBertrandCandidateAux primeSelectorAux []
      (leftTransferEntryCfg unaryBertrandCandidateAux primeSelectorAux
        (haltList unaryBertrandCandidateAux.tm stream).var
        (haltList unaryBertrandCandidateAux.tm stream).stk))
    (some (rightEntryCfg unaryBertrandCandidateAux primeSelectorAux
      (selectedPrimeRightContents stream) []))
    (by simpa [stream] using hgenerator)
    (by simpa [stream] using htransfer)
  have hall := EvalsToInTime.trans selectedPrimeComputer.step
    (4 * stream.length + 4 + 6 * (q + 1) ^ 2)
    (80 * (stream.length + 1) ^ 3)
    (initList selectedPrimeComputer (unaryEncodeNat q))
    (rightEntryCfg unaryBertrandCandidateAux primeSelectorAux
      (selectedPrimeRightContents stream) [])
    (some (haltList selectedPrimeComputer
      (unaryEncodeNat (selectPrimeAbove q))))
    (by simpa [Nat.add_comm] using hfirst)
    (by simpa [stream] using hsecond)
  exact evalsToInTimeMono (by simpa [stream] using hall)
    (selectedPrimeTime_le_degreeSix q)

/-- Genuine polynomial-time compiler-owned selection of the prime used by the
p-adic objective. -/
noncomputable def selectedPrimeComputableInPolyTime :
    @TM2ComputableInPolyTime ℕ ℕ unaryFinEncodingNat
      unaryFinEncodingNat selectPrimeAbove where
  tm := selectedPrimeComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1000 * (Polynomial.X + 1) ^ 6
  outputsFun q := by
    simpa [unaryFinEncodingNat, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using
        selectedPrime_outputsInTime q







#print axioms FramedNat.decode_encode
#print axioms frame_outputsInTime
#print axioms framedNatComputableInPolyTime
#print axioms RawNatList.decode_encode
#print axioms listFrame_outputsInTime
#print axioms framedNatListComputableInPolyTime
#print axioms RawNatLists.decode_encode
#print axioms unframe_outputsInTime
#print axioms unframedNatListsComputableInPolyTime
#print axioms binarySuccBits_encodeNat
#print axioms binarySucc_outputsInTime
#print axioms binarySuccComputableInPolyTime
#print axioms BinaryNatPair.decode_encode
#print axioms binaryLEBitsAux_encodeNat
#print axioms binaryLE_outputsInTime
#print axioms binaryLEComputableInPolyTime
#print axioms binaryAddBitsAux_encodeNat
#print axioms binaryAdd_outputsInTime
#print axioms binaryAddComputableInPolyTime
#print axioms mem_bertrandCandidates_iff
#print axioms bertrandCandidate_outputsInTime
#print axioms bertrandCandidatesComputableInPolyTime
#print axioms RawUnaryNatList.decode_encode
#print axioms RawUnaryNatList.encode_length
#print axioms unaryBertrandCandidate_outputsInTime
#print axioms unaryBertrandCandidatesComputableInPolyTime
#print axioms unaryBertrandCandidateStream_length_le
#print axioms UnaryNatPair.decode_encode
#print axioms trialPrime_eq_true_iff
#print axioms trialDivisionInputSize_le
#print axioms mem_bertrandPrimeCandidates_iff
#print axioms firstBertrandPrime_eq_selectPrimeAbove
#print axioms unaryDvd_outputsInTime
#print axioms unaryDvdComputableInPolyTime
#print axioms RawUnaryPairList.decode_encode
#print axioms trialPairsFrom_sub_two
#print axioms trialDivisionPairs_outputsInTime
#print axioms trialDivisionPairsComputableInPolyTime
#print axioms RawUnaryPairList.encode_length
#print axioms trialDivisionPairStream_length_le
#print axioms pairDvd_outputsInTime
#print axioms pairDivisionResultsComputableInPolyTime
#print axioms allFalse_trialDivisionResults_eq_true_iff
#print axioms allFalse_outputsInTime
#print axioms allFalseComputableInPolyTime
#print axioms allFalseDivisibilityResults_trialDivisionPairs_eq_true_iff
#print axioms pairAllFalse_outputsInTime
#print axioms allFalseDivisibilityResultsComputableInPolyTime
#print axioms unaryCandidatePrime_eq_true_iff
#print axioms two_le_of_mem_bertrandCandidates
#print axioms unaryCandidatePrime_eq_trialPrime_of_mem_bertrandCandidates
#print axioms filter_unaryCandidatePrime_bertrandCandidates
#print axioms unaryCandidatePrime_outputsInTime
#print axioms unaryCandidatePrimeComputableInPolyTime
#print axioms selectUnaryCandidatePrime_bertrandCandidates
#print axioms primeSelector_outputsInTime
#print axioms primeSelectorComputableInPolyTime
#print axioms primeSelector_selects_firstBertrandPrime
#print axioms selectedPrime_outputsInTime
#print axioms selectedPrimeComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
