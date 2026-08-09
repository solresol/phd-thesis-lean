import PhdThesisLean.AllDifferentCSPEncoding
import Mathlib.Computability.TMComputable

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability
open Turing
open PhdThesisLean.AllDifferentCSPEncoding
open PhdThesisLean.AllDifferentCSP.ExplicitSystem

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
CSP invariant that the explicit input length is at least `q`. An eighth finite
machine decides divisibility on delimiter-separated unary-padded pairs in
linear time, including zero dividend and divisor cases.  The executable
trial-division specification below enumerates exactly the proper divisors,
filters the checked Bertrand candidates, and proves that its first survivor is
the prime already selected by the semantic compiler.

These are checked components of the eventual compiler machine. They do not yet
establish polynomial time for CSP structural compilation, production of the
unary distinct-symbol bound and padded trial inputs, finite-machine realization
of the trial-division filter and selection pass, or final compiler assembly.
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

private def dvd_parse_evals (n d : ℕ) :
    EvalsToInTime unaryDvdComputer.step
      (dvdCfg (some .scanDividend) dvdInitialState
        (UnaryNatPair.encode (n, d)) [] [] [] [])
      (some (dvdCfg (some .start)
        (dvdObserved (dvdObserved dvdInitialState (some false)) none)
        [] (List.replicate n true) (List.replicate d true) [] []))
      (n + d + 2) := by
  have hleft := dvd_scanDividend_evals n
    (List.replicate d true) [] [] [] [] dvdInitialState
  have hright := dvd_scanDivisor_evals d
    (List.replicate n true) [] [] []
    (dvdObserved dvdInitialState (some false))
  have hall := EvalsToInTime.trans unaryDvdComputer.step
    (n + 1) (d + 1)
    (dvdCfg (some .scanDividend) dvdInitialState
      (UnaryNatPair.encode (n, d)) [] [] [] [])
    (dvdCfg (some .scanDivisor)
      (dvdObserved dvdInitialState (some false))
      (List.replicate d true) (List.replicate n true) [] [] [])
    (some (dvdCfg (some .start)
      (dvdObserved (dvdObserved dvdInitialState (some false)) none)
      [] (List.replicate n true) (List.replicate d true) [] []))
    (by simpa [UnaryNatPair.encode] using hleft)
    (by simpa using hright)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

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

/-- The unary-padded checker decides natural-number divisibility in at most
`6s + 16` steps, where `s = n + d + 1` is its actual encoded input length. -/
noncomputable def unaryDvd_outputsInTime (pair : ℕ × ℕ) :
    TM2OutputsInTime unaryDvdComputer (UnaryNatPair.encode pair)
      (some (encodeBool (decide (pair.2 ∣ pair.1))))
      (6 * (UnaryNatPair.encode pair).length + 16) := by
  rcases pair with ⟨n, d⟩
  have hparse := dvd_parse_evals n d
  cases n with
  | zero =>
      let parsedState :=
        dvdObserved (dvdObserved dvdInitialState (some false)) none
      have hstart := dvdEvalsToInTimeOne
        (dvd_step_start_zero (List.replicate d true) [] [] parsedState)
      have hfinish := dvd_finish_evals [] (List.replicate d true) [] []
        (dvdSetResult true parsedState)
      have hthroughStart := EvalsToInTime.trans unaryDvdComputer.step
        (d + 2) 1
        (dvdCfg (some .scanDividend) dvdInitialState
          (UnaryNatPair.encode (0, d)) [] [] [] [])
        (dvdCfg (some .start) parsedState [] []
          (List.replicate d true) [] [])
        (some (dvdCfg (some .finish) (dvdSetResult true parsedState)
          [] [] (List.replicate d true) [] []))
        (by simpa [parsedState] using hparse)
        hstart
      have hall := EvalsToInTime.trans unaryDvdComputer.step
        (1 + (d + 2)) (d + 4)
        (dvdCfg (some .scanDividend) dvdInitialState
          (UnaryNatPair.encode (0, d)) [] [] [] [])
        (dvdCfg (some .finish) (dvdSetResult true parsedState)
          [] [] (List.replicate d true) [] [])
        (some (dvdCfg none dvdInitialState [] [] [] []
          (encodeBool (decide (d ∣ 0)))))
        hthroughStart
        (by simpa [encodeBool, dvdSetResult] using hfinish)
      have hbound :
          (d + 4) + (1 + (d + 2)) ≤
            6 * (UnaryNatPair.encode (0, d)).length + 16 := by
        simp [UnaryNatPair.encode]
        omega
      have hmono := evalsToInTimeMono hall hbound
      rw [TM2OutputsInTime, dvd_initList_eq_cfg]
      simp only [Option.map_some]
      rw [dvd_haltList_eq_cfg]
      exact hmono
  | succ n =>
      cases d with
      | zero =>
          let parsedState :=
            dvdObserved (dvdObserved dvdInitialState (some false)) none
          have hstart := dvdEvalsToInTimeOne
            (dvd_step_start_positive_zero (List.replicate n true) [] []
              parsedState)
          have hfinish := dvd_finish_evals
            (List.replicate (n + 1) true) [] [] []
            (dvdSetResult false parsedState)
          have hthroughStart := EvalsToInTime.trans unaryDvdComputer.step
            (n + 1 + 0 + 2) 1
            (dvdCfg (some .scanDividend) dvdInitialState
              (UnaryNatPair.encode (n + 1, 0)) [] [] [] [])
            (dvdCfg (some .start) parsedState []
              (List.replicate (n + 1) true) [] [] [])
            (some (dvdCfg (some .finish) (dvdSetResult false parsedState)
              [] (List.replicate (n + 1) true) [] [] []))
            (by simpa [parsedState] using hparse)
            (by simpa [List.replicate_succ] using hstart)
          have hall := EvalsToInTime.trans unaryDvdComputer.step
            (1 + (n + 1 + 0 + 2)) (n + 1 + 4)
            (dvdCfg (some .scanDividend) dvdInitialState
              (UnaryNatPair.encode (n + 1, 0)) [] [] [] [])
            (dvdCfg (some .finish) (dvdSetResult false parsedState)
              [] (List.replicate (n + 1) true) [] [] [])
            (some (dvdCfg none dvdInitialState [] [] [] []
              (encodeBool (decide (0 ∣ n + 1)))))
            hthroughStart
            (by simpa [encodeBool, dvdSetResult] using hfinish)
          have hbound :
              (n + 1 + 4) + (1 + (n + 1 + 0 + 2)) ≤
                6 * (UnaryNatPair.encode (n + 1, 0)).length + 16 := by
            simp [UnaryNatPair.encode]
            omega
          have hmono := evalsToInTimeMono hall hbound
          rw [TM2OutputsInTime, dvd_initList_eq_cfg]
          simp only [Option.map_some]
          rw [dvd_haltList_eq_cfg]
          exact hmono
      | succ d =>
          let parsedState :=
            dvdObserved (dvdObserved dvdInitialState (some false)) none
          let consumeState :=
            dvdObserved (dvdObserved parsedState (some true)) (some true)
          have hstart := dvdEvalsToInTimeOne
            (dvd_step_start_positive_positive
              (List.replicate n true) (List.replicate d true) [] []
              parsedState)
          have hconsume := dvd_consume_evals (n + 1) (d + 1)
            (Nat.succ_pos n) (Nat.succ_pos d) [] consumeState
          have hthroughStart := EvalsToInTime.trans unaryDvdComputer.step
            (n + 1 + (d + 1) + 2) 1
            (dvdCfg (some .scanDividend) dvdInitialState
              (UnaryNatPair.encode (n + 1, d + 1)) [] [] [] [])
            (dvdCfg (some .start) parsedState []
              (List.replicate (n + 1) true)
              (List.replicate (d + 1) true) [] [])
            (some (dvdCfg (some .consume) consumeState []
              (List.replicate (n + 1) true)
              (List.replicate (d + 1) true) [] []))
            (by simpa [parsedState] using hparse)
            (by simpa [consumeState, List.replicate_succ] using hstart)
          have hall := EvalsToInTime.trans unaryDvdComputer.step
            (1 + (n + 1 + (d + 1) + 2))
            (4 * (n + 1) + (d + 1) + 8)
            (dvdCfg (some .scanDividend) dvdInitialState
              (UnaryNatPair.encode (n + 1, d + 1)) [] [] [] [])
            (dvdCfg (some .consume) consumeState []
              (List.replicate (n + 1) true)
              (List.replicate (d + 1) true) [] [])
            (some (dvdCfg none dvdInitialState [] [] [] []
              (encodeBool (decide (d + 1 ∣ n + 1)))))
            hthroughStart
            (by simpa [encodeBool] using hconsume)
          have hbound :
              (4 * (n + 1) + (d + 1) + 8) +
                  (1 + (n + 1 + (d + 1) + 2)) ≤
                6 * (UnaryNatPair.encode (n + 1, d + 1)).length + 16 := by
            simp [UnaryNatPair.encode]
            omega
          have hmono := evalsToInTimeMono hall hbound
          rw [TM2OutputsInTime, dvd_initList_eq_cfg]
          simp only [Option.map_some]
          rw [dvd_haltList_eq_cfg]
          exact hmono

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
#print axioms UnaryNatPair.decode_encode
#print axioms trialPrime_eq_true_iff
#print axioms trialDivisionInputSize_le
#print axioms mem_bertrandPrimeCandidates_iff
#print axioms firstBertrandPrime_eq_selectPrimeAbove
#print axioms unaryDvd_outputsInTime
#print axioms unaryDvdComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
