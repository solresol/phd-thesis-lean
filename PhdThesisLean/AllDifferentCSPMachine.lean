import LeanNPHardness.FramingMachine
import LeanNPHardness.SourceOrderMachine
import LeanNPHardness.BinaryArithmetic
import LeanNPHardness.CountedRowMachine
import LeanNPHardness.BooleanListMachine
import LeanNPHardness.PrimeSelectionMachine
import PhdThesisLean.AllDifferentCSPEncoding
import LeanNPHardness.MachineCompositionRuntime
import Mathlib.Computability.TMComputable

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability
open Turing
open PhdThesisLean.AllDifferentCSPEncoding
open PhdThesisLean.AllDifferentCSP.ExplicitSystem
open LeanNPHardness.MachineComposition

/-!
# CSP-specific machines and compatibility exports for reusable components

The reusable codecs, framing/arithmetic machines, counted-row utilities,
Boolean fold, and unary-bounded prime construction now live in the
`lean-np-hardness` dependency. Compatibility exports below retain their
existing thesis-facing names. The local implementations handle only the
CSP-specific source payload, indexed domain records, scope records, and
composition with the runtime-system semantics.

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
linear time; its predecessor companion supplies saturated canonical countdown
in the same bound. A fifth finite machine compares two aligned canonical binary
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
The compiler-facing Boolean input adds a decoder-checked unary domain-entry
header. A fifteenth finite machine extracts that exact count in one more step
than the complete input length, and the checked generic composition API maps
the encoded runtime system to its semantic `domainEntryPrime`. A sixteenth
finite machine removes that checked header in linear time while preserving the
compact nested-list payload byte-for-byte; composing it with the existing
unframing traversal exposes the complete runtime CSP as raw structural fields.
The encoding layer separately defines `RuntimeStructuralView`, the exact
tagged target for the next structural transducer: indexed domain occurrences,
intact scopes, and an explicit variable-count header. A checked raw-field
encoding now gives that transducer its direct output contract, and the existing
finite serializer converts the raw structural view to its exact canonical
Boolean encoding in linear time. A further checked linear pass reverses the
raw compact-system stream into semantic source order, so the outer length and
domain-count separator precede the domain and scope fields consumed by the
next structural emitter. A checked binary predecessor machine supplies that
emitter's remaining-domain and remaining-value countdown primitive in at most
`2s + 3` steps, including zero, one, powers of two, and arbitrary borrow
chains.
`StructuralFieldStream` now fixes the emitter's exact executable field-level
contract: domain occurrences expand to `[3, 0, index, value]`, scopes remain
intact as `[|S|+1, 1, ...S]`, and reversing the semantic-order stream is proved
to be exactly the checked raw structural encoding. `SourceOrderRawFields`
checks uncounted semantic-order field sequences, and
`domainOccurrenceBlockComputableInPolyTime` is the first finite component of
the structural emitter: it turns arbitrary current-index and value fields into
the exact `[3, 0, index, value]` block in at most `2s + 2` steps.
`scopeFieldBlockComputableInPolyTime` supplies the other local record branch:
from a count-checked source scope it increments the row length, inserts tag
`1`, and copies all entries unchanged in at most `3s + 8` steps, including
empty and singleton scopes.
`domainFieldRowComputableInPolyTime` closes the inner repeated-record loop:
from a count-checked row `[index, |D|, ...D]`, it emits every exact
`[3, 0, index, value]` block in at most `20(s+1)^2` steps, including empty
and singleton domains, and halts with every non-output stack empty.
`DomainFieldSection.inputFinEncoding` now checks the complete counted domain
section, including its outer row count and every inner value count;
`occurrences_indexedRowsFrom` makes consecutive index advancement explicit,
and `outputEncode_eq_structuralFields` proves that concatenating the checked
row outputs is exactly `StructuralFieldStream.domainFieldsFrom`. The concrete
`domainRowPayloadComputableInPolyTime` pass removes only the checked outer
domain count and preserves every count-prefixed row cell in source order in at
most `2s + 1` steps. `DomainFieldSection.rowPayloadFinEncoding` now decodes
that exhaustion-delimited output back to the structured domain list, rechecks
every row count, and preserves empty rows; the same finite machine is therefore
also packaged as `domainRowPayloadStructuredComputableInPolyTime`. The separate
`AllDifferentCSPStructuralMachine` module consumes that checked payload through
exhaustion, advances a canonical binary index across every row including empty
ones, and emits the exact tagged domain-occurrence stream in cubic bit-level
time. Its composed `completeDomainSectionComputableInPolyTime` machine starts
from the complete counted section, so the intermediate payload is checked and
constructed internally.
`AllDifferentCSPScopeSection` reuses the same counted-row encodings and linear
header-removal machine for scopes, checks the exact tagged scope output with
a linear raw-wire-size bound, and proves the full header/section assembly
identities, including the reversal into the checked raw structural view.
`AllDifferentCSPScopeMachine` implements the complete scope loop in quadratic
bit-level time and composes it with checked outer-count removal.
`AllDifferentCSPSourceSections` now splits the complete source with binary
row/value countdowns and composes domain expansion while retaining every scope
through the pinned generic pair-left machine. `AllDifferentCSPProcessedSections`
exchanges the sections in linear time and reuses the same adapter to process
scopes, then restores the original order; its complete composition starts at
the actual Boolean compiler input and emits both exact tagged sections.

`AllDifferentCSPVariableHeader` now copies the variable count and preserves
the entire source in linear time, with a composition from the actual compiler
input. `AllDifferentCSPCountedSections` carries that count through the source
split and both section passes, yielding the exact occurrence/scope/count tuple.
These are checked components of the eventual compiler machine. They do not yet
establish executable record-count staging,
or construction of the full tagged structural view; canonical
relabelling and edge construction, objective-row emission, and final compiler
assembly also remain.
-/

namespace FramedNat
export LeanNPHardness.FramedNat
  (decode decode_encode finEncoding)
end FramedNat
namespace FramedNatList
export LeanNPHardness.FramedNatList
  (decode decode_encode finEncoding)
end FramedNatList
namespace RawNatList
export LeanNPHardness.RawNatList
  (segment payloads encode parseAux parse
   parse_segments parse_encode decode decode_encode finEncoding)
end RawNatList
namespace RawUnaryNatList
export LeanNPHardness.RawUnaryNatList
  (segment payloads encode parseAux parse
   parse_encode decode decode_encode finEncoding segment_length
   encode_length)
end RawUnaryNatList
namespace RawNatLists
export LeanNPHardness.RawNatLists
  (payloads encode parse_encode payloads_frame_eq_encode decode
   decode_encode finEncoding)
end RawNatLists
namespace SourceOrderRawNatLists
export LeanNPHardness.SourceOrderRawNatLists
  (encode decode decode_encode encode_eq_payloads finEncoding)
end SourceOrderRawNatLists
namespace SourceOrderRawFields
export LeanNPHardness.SourceOrderRawFields
  (encode decode decode_encode finEncoding)
end SourceOrderRawFields


/-! ## Exact structural emitter field stream

The next finite machine consumes the source-order compact-system fields and
stages the tagged structural records before it can prefix the final record
count.  The definitions below fix the exact natural-field stream that this
machine must emit.  Keeping this specification at field level exposes the
domain index, local tags, record lengths, and final stack reversal separately
from binary counter manipulation.
-/

namespace StructuralFieldStream

/-- Flatten nested natural lists to their outer length, then each inner length
and its entries, all in semantic source order. -/
def flatten (xss : List (List ℕ)) : List ℕ :=
  xss.length :: xss.flatMap fun xs => xs.length :: xs

/-- Fields for every domain occurrence, starting at the supplied variable
index.  Each occurrence becomes the complete row `[3, 0, index, value]`: the
row length followed by the locally tagged record. -/
def domainFieldsFrom : ℕ → List (List ℕ) → List ℕ
  | _, [] => []
  | index, domain :: domains =>
      domain.flatMap (fun value => [3, 0, index, value]) ++
        domainFieldsFrom (index + 1) domains

/-- Fields for intact scope records.  A scope `entries` becomes its row length
`entries.length + 1`, tag `1`, and the unchanged entries. -/
def scopeFields (scopes : List (List ℕ)) : List ℕ :=
  scopes.flatMap fun entries => (entries.length + 1) :: 1 :: entries

/-- Exact semantic-order natural fields emitted for a runtime system.  The
outer count includes the singleton variable-count header. -/
def ofRuntimeSystem (C : RuntimeSystem) : List ℕ :=
  (1 + C.domainEntryCount + C.scopes.length) ::
    1 :: C.domains.length ::
      (domainFieldsFrom 0 C.domains ++ scopeFields C.scopes)

/-- Binary source-order form of `ofRuntimeSystem`.  Every field begins with an
explicit delimiter and then its canonical least-significant-bit-first bits. -/
def encode (C : RuntimeSystem) : List (Option Bool) :=
  (ofRuntimeSystem C).flatMap fun field =>
    none :: (Computability.encodeNat field).map some

private theorem domainFieldsFrom_eq_records
    (start : ℕ) (domains : List (List ℕ)) :
    domainFieldsFrom start domains =
      ((RuntimeStructuralView.indexedDomainOccurrencesFrom start domains).map
        fun occurrence => RuntimeStructuralRecord.domainOccurrence
          occurrence.1 occurrence.2).flatMap fun record =>
            record.toNatList.length :: record.toNatList := by
  induction domains generalizing start with
  | nil => simp [domainFieldsFrom,
      RuntimeStructuralView.indexedDomainOccurrencesFrom]
  | cons domain domains ih =>
      simp [domainFieldsFrom,
        RuntimeStructuralView.indexedDomainOccurrencesFrom,
        RuntimeStructuralRecord.toNatList, List.flatMap_map,
        Function.comp_def, ih]

private theorem scopeFields_eq_records (scopes : List (List ℕ)) :
    scopeFields scopes =
      (scopes.map RuntimeStructuralRecord.scope).flatMap fun record =>
        record.toNatList.length :: record.toNatList := by
  simp [scopeFields, RuntimeStructuralRecord.toNatList,
    List.flatMap_map]

/-- The explicit emitter fields are exactly the flattened natural fields of
the checked tagged structural view. -/
theorem ofRuntimeSystem_eq_flatten (C : RuntimeSystem) :
    ofRuntimeSystem C =
      flatten (RuntimeStructuralView.ofRuntimeSystem C).toNatLists := by
  rw [ofRuntimeSystem, flatten, RuntimeStructuralView.toNatLists]
  simp only [List.length_cons, List.length_map, List.flatMap_cons]
  rw [RuntimeStructuralView.ofRuntimeSystem_records_length]
  simp only [RuntimeStructuralView.ofRuntimeSystem]
  rw [domainFieldsFrom_eq_records, scopeFields_eq_records]
  simp [RuntimeStructuralView.domainRecords, List.flatMap_map,
    RuntimeStructuralView.indexedDomainOccurrences, Function.comp_def,
    Nat.add_comm, Nat.add_left_comm]

private theorem payloads_eq_map_flatten (xss : List (List ℕ)) :
    RawNatLists.payloads xss =
      (flatten xss).map Computability.encodeNat := by
  simp [RawNatLists.payloads, flatten, List.map_flatMap]

/-- The field-level specification is exactly the checked source-order raw
encoding of the target structural view. -/
theorem encode_eq_sourceOrderRawNatLists (C : RuntimeSystem) :
    encode C = SourceOrderRawNatLists.encode
      (RuntimeStructuralView.ofRuntimeSystem C).toNatLists := by
  rw [SourceOrderRawNatLists.encode_eq_payloads]
  rw [payloads_eq_map_flatten]
  rw [← ofRuntimeSystem_eq_flatten]
  simp [encode, List.flatMap_map]

/-- Reversing the semantic-order emitter stream gives exactly the checked raw
stack encoding required by `RuntimeStructuralView.rawFinEncoding`. -/
theorem encode_reverse_eq_raw (C : RuntimeSystem) :
    (encode C).reverse = RawNatLists.encode
      (RuntimeStructuralView.ofRuntimeSystem C).toNatLists := by
  rw [encode_eq_sourceOrderRawNatLists]
  simp [SourceOrderRawNatLists.encode]

end StructuralFieldStream

namespace RuntimeStructuralView

/-- Checked stack-oriented raw-field encoding of the tagged structural view.

This is the natural output interface for the structural scan: the machine can
emit the outer length and every record field in reverse stack order, without
also having to construct the canonical self-delimiting Boolean frames.  The
separate framing machine below converts this representation to
`RuntimeStructuralView.finEncoding` in linear time. -/
def rawFinEncoding : FinEncoding RuntimeStructuralView where
  Γ := Option Bool
  encode view := RawNatLists.encode view.toNatLists
  decode bits := (RawNatLists.decode bits).bind
    AllDifferentCSPEncoding.RuntimeStructuralView.ofNatLists
  decode_encode view := by simp
  ΓFin := inferInstance

end RuntimeStructuralView

/-- The exact reversed emitter stream is accepted by the checked raw
structural decoder, including zero-variable, empty-domain, singleton, and
empty-scope cases covered by the general definitions. -/
theorem StructuralFieldStream.raw_decode_encode_reverse (C : RuntimeSystem) :
    RuntimeStructuralView.rawFinEncoding.toEncoding.decode
        (StructuralFieldStream.encode C).reverse =
      some (RuntimeStructuralView.ofRuntimeSystem C) := by
  rw [StructuralFieldStream.encode_reverse_eq_raw]
  simp [RuntimeStructuralView.rawFinEncoding]

/-! ## Tagged domain-occurrence field blocks

The complete structural scan repeatedly turns a current variable index and a
domain value into the field block `[3, 0, index, value]`.  The machine below
checks that local transformation independently of the still-pending outer
domain/scope parser.  It preserves arbitrary binary index and value payloads,
including zero, and adds only the fixed row-length and domain-tag fields.
-/

namespace DomainOccurrenceFieldBlock

/-- Source-order input fields for one current variable index and value. -/
def inputEncode (occurrence : ℕ × ℕ) : List (Option Bool) :=
  SourceOrderRawFields.encode [occurrence.1, occurrence.2]

/-- Decode exactly two source-order natural fields. -/
def inputDecode (input : List (Option Bool)) : Option (ℕ × ℕ) := do
  match ← SourceOrderRawFields.decode input with
  | [index, value] => some (index, value)
  | _ => none

@[simp]
theorem inputDecode_encode (occurrence : ℕ × ℕ) :
    inputDecode (inputEncode occurrence) = some occurrence := by
  simp [inputDecode, inputEncode]

/-- Checked two-field input encoding for the local domain emitter. -/
def inputFinEncoding : FinEncoding (ℕ × ℕ) where
  Γ := Option Bool
  encode := inputEncode
  decode := inputDecode
  decode_encode := inputDecode_encode
  ΓFin := inferInstance

/-- Source-order output fields for one complete tagged domain record. -/
def outputEncode (occurrence : ℕ × ℕ) : List (Option Bool) :=
  SourceOrderRawFields.encode [3, 0, occurrence.1, occurrence.2]

/-- Decode exactly one complete domain-occurrence field block. -/
def outputDecode (input : List (Option Bool)) : Option (ℕ × ℕ) := do
  match ← SourceOrderRawFields.decode input with
  | [3, 0, index, value] => some (index, value)
  | _ => none

@[simp]
theorem outputDecode_encode (occurrence : ℕ × ℕ) :
    outputDecode (outputEncode occurrence) = some occurrence := by
  simp [outputDecode, outputEncode]

/-- Checked output encoding whose wire form is the exact structural domain
record field block. -/
def outputFinEncoding : FinEncoding (ℕ × ℕ) where
  Γ := Option Bool
  encode := outputEncode
  decode := outputDecode
  decode_encode := outputDecode_encode
  ΓFin := inferInstance

/-- The constant source-order cells for row length `3` and domain tag `0`. -/
def headerPrefix : List (Option Bool) :=
  [none, some true, some true, none]

private theorem encodeNat_three :
    Computability.encodeNat 3 = [true, true] := by
  unfold Computability.encodeNat
  change Computability.encodeNum (Num.ofNat' 3) = [true, true]
  rw [show (3 : ℕ) = Nat.bit true 1 by norm_num [Nat.bit], Num.ofNat'_bit,
    Num.ofNat'_one]
  rfl

private theorem encodeNat_zero :
    Computability.encodeNat 0 = [] := by
  unfold Computability.encodeNat
  change Computability.encodeNum (Num.ofNat' 0) = []
  rw [Num.ofNat'_zero]
  rfl

@[simp]
theorem outputEncode_eq_prefix (occurrence : ℕ × ℕ) :
    outputEncode occurrence = headerPrefix ++ inputEncode occurrence := by
  simp [outputEncode, inputEncode, SourceOrderRawFields.encode, headerPrefix,
    encodeNat_three, encodeNat_zero]

/-- The emitted semantic fields are exactly the length-prefixed tagged record
used by `RuntimeStructuralView`. -/
theorem fields_eq_record (occurrence : ℕ × ℕ) :
    [3, 0, occurrence.1, occurrence.2] =
      (RuntimeStructuralRecord.domainOccurrence occurrence.1
        occurrence.2).toNatList.length ::
      (RuntimeStructuralRecord.domainOccurrence occurrence.1
        occurrence.2).toNatList := by
  rfl

end DomainOccurrenceFieldBlock

/-- Input, reversal work, and output stacks for the local domain-record
emitter. -/
inductive DomainOccurrenceBlockStack
  | input
  | scratch
  | output
  deriving DecidableEq, Fintype

/-- Reversal and restoration phases of the local domain-record emitter. -/
inductive DomainOccurrenceBlockLabel
  | stash
  | restore
  deriving DecidableEq, Fintype

/-- Finite control remembers the most recently popped raw-field cell. -/
abbrev DomainOccurrenceBlockState := Option (Option Bool)

private def domainOccurrenceBlockPopped
    (_state : DomainOccurrenceBlockState)
    (symbol : Option (Option Bool)) : DomainOccurrenceBlockState :=
  symbol

private def domainOccurrenceBlockPresent :
    DomainOccurrenceBlockState → Bool
  | some _ => true
  | none => false

private def domainOccurrenceBlockHeld :
    DomainOccurrenceBlockState → Option Bool
  | some symbol => symbol
  | none => none

private def DomainOccurrenceBlockAlphabet
    (_index : DomainOccurrenceBlockStack) : Type :=
  Option Bool

/-- A finite program that preserves the two arbitrary source fields and then
prefixes the fixed row length and domain-record tag. -/
def domainOccurrenceBlockProgram :
    DomainOccurrenceBlockLabel →
      TM2.Stmt DomainOccurrenceBlockAlphabet DomainOccurrenceBlockLabel
        DomainOccurrenceBlockState
  | .stash =>
      .pop .input domainOccurrenceBlockPopped <|
        .branch domainOccurrenceBlockPresent
          (.push .scratch domainOccurrenceBlockHeld <|
            .goto (fun _ => .stash))
          (.goto (fun _ => .restore))
  | .restore =>
      .pop .scratch domainOccurrenceBlockPopped <|
        .branch domainOccurrenceBlockPresent
          (.push .output domainOccurrenceBlockHeld <|
            .goto (fun _ => .restore))
          (.push .output (fun _ => (none : Option Bool)) <|
            .push .output (fun _ => some true) <|
              .push .output (fun _ => some true) <|
                .push .output (fun _ => (none : Option Bool)) <|
                  .halt)

/-- Concrete finite machine for one tagged domain-occurrence block. -/
def domainOccurrenceBlockComputer : FinTM2 where
  K := DomainOccurrenceBlockStack
  k₀ := .input
  k₁ := .output
  Γ := DomainOccurrenceBlockAlphabet
  Λ := DomainOccurrenceBlockLabel
  main := .stash
  σ := DomainOccurrenceBlockState
  initialState := none
  Γk₀Fin := show Fintype (Option Bool) from inferInstance
  m := domainOccurrenceBlockProgram

private def domainOccurrenceBlockStacks
    (input scratch output : List (Option Bool)) :
    (index : DomainOccurrenceBlockStack) →
      List (DomainOccurrenceBlockAlphabet index)
  | .input => input
  | .scratch => scratch
  | .output => output

private def domainOccurrenceBlockCfg
    (label : Option DomainOccurrenceBlockLabel)
    (state : DomainOccurrenceBlockState)
    (input scratch output : List (Option Bool)) :
    domainOccurrenceBlockComputer.Cfg where
  l := label
  var := state
  stk := domainOccurrenceBlockStacks input scratch output

private theorem domainOccurrenceBlock_step_stash_cons
    (symbol : Option Bool) (input scratch output : List (Option Bool))
    (state : DomainOccurrenceBlockState) :
    domainOccurrenceBlockComputer.step
        (domainOccurrenceBlockCfg (some .stash) state
          (symbol :: input) scratch output) =
      some (domainOccurrenceBlockCfg (some .stash) (some symbol)
        input (symbol :: scratch) output) := by
  simp [domainOccurrenceBlockComputer, FinTM2.step,
    domainOccurrenceBlockCfg, domainOccurrenceBlockProgram,
    domainOccurrenceBlockStacks, DomainOccurrenceBlockAlphabet,
    domainOccurrenceBlockPopped, domainOccurrenceBlockPresent,
    domainOccurrenceBlockHeld, Function.update]
  funext index
  cases index <;> rfl

private theorem domainOccurrenceBlock_step_stash_nil
    (scratch output : List (Option Bool))
    (state : DomainOccurrenceBlockState) :
    domainOccurrenceBlockComputer.step
        (domainOccurrenceBlockCfg (some .stash) state [] scratch output) =
      some (domainOccurrenceBlockCfg (some .restore) none
        [] scratch output) := by
  simp [domainOccurrenceBlockComputer, FinTM2.step,
    domainOccurrenceBlockCfg, domainOccurrenceBlockProgram,
    domainOccurrenceBlockStacks, DomainOccurrenceBlockAlphabet,
    domainOccurrenceBlockPopped, domainOccurrenceBlockPresent,
    Function.update]

private theorem domainOccurrenceBlock_step_restore_cons
    (symbol : Option Bool) (scratch output : List (Option Bool))
    (state : DomainOccurrenceBlockState) :
    domainOccurrenceBlockComputer.step
        (domainOccurrenceBlockCfg (some .restore) state []
          (symbol :: scratch) output) =
      some (domainOccurrenceBlockCfg (some .restore) (some symbol)
        [] scratch (symbol :: output)) := by
  simp [domainOccurrenceBlockComputer, FinTM2.step,
    domainOccurrenceBlockCfg, domainOccurrenceBlockProgram,
    domainOccurrenceBlockStacks, DomainOccurrenceBlockAlphabet,
    domainOccurrenceBlockPopped, domainOccurrenceBlockPresent,
    domainOccurrenceBlockHeld, Function.update]
  funext index
  cases index <;> rfl

private theorem domainOccurrenceBlock_step_restore_nil
    (output : List (Option Bool))
    (state : DomainOccurrenceBlockState) :
    domainOccurrenceBlockComputer.step
        (domainOccurrenceBlockCfg (some .restore) state [] [] output) =
      some (domainOccurrenceBlockCfg none none [] []
        (DomainOccurrenceFieldBlock.headerPrefix ++ output)) := by
  simp [domainOccurrenceBlockComputer, FinTM2.step,
    domainOccurrenceBlockCfg, domainOccurrenceBlockProgram,
    domainOccurrenceBlockStacks, DomainOccurrenceBlockAlphabet,
    domainOccurrenceBlockPopped, domainOccurrenceBlockPresent,
    DomainOccurrenceFieldBlock.headerPrefix, Function.update]
  funext index
  cases index <;> rfl

private def domainOccurrenceBlockEvalsToInTimeOne
    {start finish : domainOccurrenceBlockComputer.Cfg}
    (hstep : domainOccurrenceBlockComputer.step start = some finish) :
    EvalsToInTime domainOccurrenceBlockComputer.step
      start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def domainOccurrenceBlock_stash_evals
    (input scratch output : List (Option Bool))
    (state : DomainOccurrenceBlockState) :
    EvalsToInTime domainOccurrenceBlockComputer.step
      (domainOccurrenceBlockCfg (some .stash) state input scratch output)
      (some (domainOccurrenceBlockCfg (some .restore) none []
        (input.reverse ++ scratch) output))
      (input.length + 1) := by
  induction input generalizing scratch state with
  | nil =>
      simpa using domainOccurrenceBlockEvalsToInTimeOne
        (domainOccurrenceBlock_step_stash_nil scratch output state)
  | cons symbol input ih =>
      let middle := domainOccurrenceBlockCfg (some .stash) (some symbol)
        input (symbol :: scratch) output
      have hone : EvalsToInTime domainOccurrenceBlockComputer.step
          (domainOccurrenceBlockCfg (some .stash) state
            (symbol :: input) scratch output)
          (some middle) 1 :=
        domainOccurrenceBlockEvalsToInTimeOne (by
          simpa [middle] using domainOccurrenceBlock_step_stash_cons
            symbol input scratch output state)
      have hrest := ih (symbol :: scratch) (some symbol)
      have hall := EvalsToInTime.trans domainOccurrenceBlockComputer.step
        1 (input.length + 1)
        (domainOccurrenceBlockCfg (some .stash) state
          (symbol :: input) scratch output)
        middle
        (some (domainOccurrenceBlockCfg (some .restore) none []
          ((symbol :: input).reverse ++ scratch) output))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainOccurrenceBlock_restore_evals
    (scratch output : List (Option Bool))
    (state : DomainOccurrenceBlockState) :
    EvalsToInTime domainOccurrenceBlockComputer.step
      (domainOccurrenceBlockCfg (some .restore) state [] scratch output)
      (some (domainOccurrenceBlockCfg none none [] []
        (DomainOccurrenceFieldBlock.headerPrefix ++ scratch.reverse ++ output)))
      (scratch.length + 1) := by
  induction scratch generalizing output state with
  | nil =>
      simpa using domainOccurrenceBlockEvalsToInTimeOne
        (domainOccurrenceBlock_step_restore_nil output state)
  | cons symbol scratch ih =>
      let middle := domainOccurrenceBlockCfg (some .restore) (some symbol)
        [] scratch (symbol :: output)
      have hone : EvalsToInTime domainOccurrenceBlockComputer.step
          (domainOccurrenceBlockCfg (some .restore) state []
            (symbol :: scratch) output)
          (some middle) 1 :=
        domainOccurrenceBlockEvalsToInTimeOne (by
          simpa [middle] using domainOccurrenceBlock_step_restore_cons
            symbol scratch output state)
      have hrest := ih (symbol :: output) (some symbol)
      have hall := EvalsToInTime.trans domainOccurrenceBlockComputer.step
        1 (scratch.length + 1)
        (domainOccurrenceBlockCfg (some .restore) state []
          (symbol :: scratch) output)
        middle
        (some (domainOccurrenceBlockCfg none none [] []
          (DomainOccurrenceFieldBlock.headerPrefix ++
            (symbol :: scratch).reverse ++ output)))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private theorem domainOccurrenceBlock_initList_eq_cfg
    (input : List (Option Bool)) :
    initList domainOccurrenceBlockComputer input =
      domainOccurrenceBlockCfg (some .stash) none input [] [] := by
  unfold initList domainOccurrenceBlockCfg
  congr
  funext index
  cases index <;> rfl

private theorem domainOccurrenceBlock_haltList_eq_cfg
    (output : List (Option Bool)) :
    haltList domainOccurrenceBlockComputer output =
      domainOccurrenceBlockCfg none none [] [] output := by
  unfold haltList domainOccurrenceBlockCfg
  congr
  funext index
  cases index <;> rfl

/-- The local finite transducer emits one exact tagged domain-occurrence field
block in at most twice the source-pair wire length plus two steps. -/
def domainOccurrenceBlock_outputsInTime (occurrence : ℕ × ℕ) :
    TM2OutputsInTime domainOccurrenceBlockComputer
      (DomainOccurrenceFieldBlock.inputEncode occurrence)
      (some (DomainOccurrenceFieldBlock.outputEncode occurrence))
      (2 * (DomainOccurrenceFieldBlock.inputEncode occurrence).length + 2) := by
  let input := DomainOccurrenceFieldBlock.inputEncode occurrence
  have hstash := domainOccurrenceBlock_stash_evals input [] [] none
  have hrestore := domainOccurrenceBlock_restore_evals input.reverse [] none
  have hall := EvalsToInTime.trans domainOccurrenceBlockComputer.step
    (input.length + 1) (input.reverse.length + 1)
    (domainOccurrenceBlockCfg (some .stash) none input [] [])
    (domainOccurrenceBlockCfg (some .restore) none [] input.reverse [])
    (some (domainOccurrenceBlockCfg none none [] []
      (DomainOccurrenceFieldBlock.headerPrefix ++ input)))
    (by simpa using hstash)
    (by simpa [List.reverse_reverse] using hrestore)
  have htime :
      (input.reverse.length + 1) + (input.length + 1) =
        2 * input.length + 2 := by
    simp
    omega
  rw [htime] at hall
  rw [TM2OutputsInTime, domainOccurrenceBlock_initList_eq_cfg]
  simp only [Option.map_some]
  rw [domainOccurrenceBlock_haltList_eq_cfg]
  simpa [input, DomainOccurrenceFieldBlock.outputEncode_eq_prefix,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

/-- A genuine linear-time finite-machine witness for emitting one complete
tagged domain-occurrence field block. -/
noncomputable def domainOccurrenceBlockComputableInPolyTime :
    @TM2ComputableInPolyTime (ℕ × ℕ) (ℕ × ℕ)
      DomainOccurrenceFieldBlock.inputFinEncoding
      DomainOccurrenceFieldBlock.outputFinEncoding id where
  tm := domainOccurrenceBlockComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl (Option Bool)
  time := 2 * Polynomial.X + 2
  outputsFun occurrence := by
    simpa [DomainOccurrenceFieldBlock.inputFinEncoding,
      DomainOccurrenceFieldBlock.outputFinEncoding, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_X] using
        domainOccurrenceBlock_outputsInTime occurrence

export LeanNPHardness.MachinePrimitives
  (FrameStack FrameLabel FrameState heldBit frameProgram
   frameComputer cfg frame_outputsInTime framedNatComputableInPolyTime ListFrameStack
   ListFrameLabel ListFrameState listFrameProgram listFrameComputer listFrame_outputsInTime
   nestedListFrame_outputsInTime framedNatListComputableInPolyTime UnframeStack UnframeLabel UnframeState
   unframeProgram unframeComputer unframe_outputsInTime unframedNatListsComputableInPolyTime)

export LeanNPHardness.MachinePrimitives (evalsToInTimeMono replicate_true_append_cons)

/-- A genuine linear-time finite-machine bridge from the stack-oriented raw
structural stream to the exact checked Boolean encoding of that structural
view.  This keeps structural emission and canonical field framing as separate
compiler passes. -/
noncomputable def runtimeStructuralViewFramingComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeStructuralView RuntimeStructuralView
      RuntimeStructuralView.rawFinEncoding
      RuntimeStructuralView.finEncoding id where
  tm := listFrameComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := 3 * Polynomial.X
  outputsFun view := by
    simpa [RuntimeStructuralView.rawFinEncoding,
      RuntimeStructuralView.finEncoding, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_X] using
        nestedListFrame_outputsInTime view.toNatLists



/-! ## Runtime domain-entry bound

The compiler-facing input encoding carries the explicit domain-entry count as
a decoder-checked unary header in front of the compact nested-list payload.
The following two-stack machine copies that header to its output and consumes
the remaining payload.  Since the decoder checks the header against the
decoded system, its output is exactly `RuntimeSystem.domainEntryCount`, not an
untrusted supplied bound.
-/

inductive DomainCountStack
  | input
  | output
  deriving DecidableEq, Fintype

inductive DomainCountLabel
  | header
  | payload
  deriving DecidableEq, Fintype

abbrev DomainCountState := Option Bool

private def domainCountPopped
    (_state : DomainCountState) (bit : Option Bool) : DomainCountState :=
  bit

private def domainCountTrue : DomainCountState → Bool
  | some true => true
  | _ => false

private def domainCountPresent : DomainCountState → Bool
  | some _ => true
  | none => false

private def DomainCountAlphabet (_ : DomainCountStack) : Type := Bool

/-- Copy the unary header, consume its `false` delimiter, discard the compact
payload, and halt with only the copied unary count on the output stack. -/
def domainEntryCountProgram :
    DomainCountLabel →
      TM2.Stmt DomainCountAlphabet DomainCountLabel DomainCountState
  | .header =>
      .pop .input domainCountPopped <|
        .branch domainCountTrue
          (.push .output (fun _ => true) <|
            .goto (fun _ => .header))
          (.goto (fun _ => .payload))
  | .payload =>
      .pop .input domainCountPopped <|
        .branch domainCountPresent
          (.goto (fun _ => .payload))
          .halt

def domainEntryCountComputer : FinTM2 where
  K := DomainCountStack
  k₀ := .input
  k₁ := .output
  Γ := DomainCountAlphabet
  Λ := DomainCountLabel
  main := .header
  σ := DomainCountState
  initialState := none
  Γk₀Fin := Bool.fintype
  m := domainEntryCountProgram

private def domainEntryCountStackContents
    (input output : List Bool) :
    (index : DomainCountStack) → List (DomainCountAlphabet index)
  | .input => input
  | .output => output

private def domainEntryCountCfg (label : Option DomainCountLabel)
    (state : DomainCountState) (input output : List Bool) :
    domainEntryCountComputer.Cfg where
  l := label
  var := state
  stk := domainEntryCountStackContents input output

private theorem domainEntryCount_step_header_true
    (input output : List Bool) (state : DomainCountState) :
    domainEntryCountComputer.step
        (domainEntryCountCfg (some .header) state
          (true :: input) output) =
      some (domainEntryCountCfg (some .header) (some true)
        input (true :: output)) := by
  simp [domainEntryCountComputer, FinTM2.step, domainEntryCountCfg,
    domainEntryCountProgram, domainEntryCountStackContents,
    DomainCountAlphabet, domainCountPopped, domainCountTrue,
    Function.update]
  funext index
  cases index <;> rfl

private theorem domainEntryCount_step_header_false
    (input output : List Bool) (state : DomainCountState) :
    domainEntryCountComputer.step
        (domainEntryCountCfg (some .header) state
          (false :: input) output) =
      some (domainEntryCountCfg (some .payload) (some false)
        input output) := by
  simp [domainEntryCountComputer, FinTM2.step, domainEntryCountCfg,
    domainEntryCountProgram, domainEntryCountStackContents,
    DomainCountAlphabet, domainCountPopped, domainCountTrue,
    Function.update]
  funext index
  cases index <;> rfl

private theorem domainEntryCount_step_payload_cons
    (bit : Bool) (input output : List Bool) (state : DomainCountState) :
    domainEntryCountComputer.step
        (domainEntryCountCfg (some .payload) state
          (bit :: input) output) =
      some (domainEntryCountCfg (some .payload) (some bit)
        input output) := by
  simp [domainEntryCountComputer, FinTM2.step, domainEntryCountCfg,
    domainEntryCountProgram, domainEntryCountStackContents,
    DomainCountAlphabet, domainCountPopped, domainCountPresent]
  funext index
  cases index <;> rfl

private theorem domainEntryCount_step_payload_nil
    (output : List Bool) (state : DomainCountState) :
    domainEntryCountComputer.step
        (domainEntryCountCfg (some .payload) state [] output) =
      some (domainEntryCountCfg none none [] output) := by
  simp [domainEntryCountComputer, FinTM2.step, domainEntryCountCfg,
    domainEntryCountProgram, domainEntryCountStackContents,
    DomainCountAlphabet, domainCountPopped, domainCountPresent]

private def domainEntryCountEvalsToInTimeOne
    {start finish : domainEntryCountComputer.Cfg}
    (hstep : domainEntryCountComputer.step start = some finish) :
    EvalsToInTime domainEntryCountComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def domainEntryCount_header_evals
    (count : ℕ) (payload output : List Bool) (state : DomainCountState) :
    EvalsToInTime domainEntryCountComputer.step
      (domainEntryCountCfg (some .header) state
        (List.replicate count true ++ false :: payload) output)
      (some (domainEntryCountCfg (some .payload) (some false)
        payload (List.replicate count true ++ output)))
      (count + 1) := by
  induction count generalizing output state with
  | zero =>
      simpa using domainEntryCountEvalsToInTimeOne
        (domainEntryCount_step_header_false payload output state)
  | succ count ih =>
      let middle := domainEntryCountCfg (some .header) (some true)
        (List.replicate count true ++ false :: payload) (true :: output)
      have hone : EvalsToInTime domainEntryCountComputer.step
          (domainEntryCountCfg (some .header) state
            (List.replicate (count + 1) true ++ false :: payload) output)
          (some middle) 1 :=
        domainEntryCountEvalsToInTimeOne (by
          simpa [middle, List.replicate_succ] using
            domainEntryCount_step_header_true
              (List.replicate count true ++ false :: payload) output state)
      have hrest := ih (true :: output) (some true)
      have hall := EvalsToInTime.trans domainEntryCountComputer.step
        1 (count + 1)
        (domainEntryCountCfg (some .header) state
          (List.replicate (count + 1) true ++ false :: payload) output)
        middle
        (some (domainEntryCountCfg (some .payload) (some false)
          payload (List.replicate (count + 1) true ++ output)))
        hone
        (by
          simpa [middle, List.replicate_succ,
            replicate_true_append_cons] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainEntryCount_payload_evals
    (payload output : List Bool) (state : DomainCountState) :
    EvalsToInTime domainEntryCountComputer.step
      (domainEntryCountCfg (some .payload) state payload output)
      (some (domainEntryCountCfg none none [] output))
      (payload.length + 1) := by
  induction payload generalizing state with
  | nil =>
      simpa using domainEntryCountEvalsToInTimeOne
        (domainEntryCount_step_payload_nil output state)
  | cons bit payload ih =>
      let middle := domainEntryCountCfg (some .payload) (some bit)
        payload output
      have hone : EvalsToInTime domainEntryCountComputer.step
          (domainEntryCountCfg (some .payload) state
            (bit :: payload) output)
          (some middle) 1 :=
        domainEntryCountEvalsToInTimeOne (by
          simpa [middle] using
            domainEntryCount_step_payload_cons bit payload output state)
      have hrest := ih (some bit)
      have hall := EvalsToInTime.trans domainEntryCountComputer.step
        1 (payload.length + 1)
        (domainEntryCountCfg (some .payload) state
          (bit :: payload) output)
        middle
        (some (domainEntryCountCfg none none [] output))
        hone
        (by simpa [middle] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private theorem domainEntryCount_initList_eq_cfg (input : List Bool) :
    initList domainEntryCountComputer input =
      domainEntryCountCfg (some .header) none input [] := by
  unfold initList domainEntryCountCfg
  congr
  funext index
  cases index <;> rfl

private theorem domainEntryCount_haltList_eq_cfg (output : List Bool) :
    haltList domainEntryCountComputer output =
      domainEntryCountCfg none none [] output := by
  unfold haltList domainEntryCountCfg
  congr
  funext index
  cases index <;> rfl

private theorem domainEntryCount_unaryEncodeNat_eq (count : ℕ) :
    unaryEncodeNat count = List.replicate count true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [unaryEncodeNat, List.replicate_succ, ih]

/-- The compiler-input header is extracted exactly in one more step than the
complete encoded input length. -/
def domainEntryCount_outputsInTime (C : RuntimeSystem) :
    TM2OutputsInTime domainEntryCountComputer
      (RuntimeCompilerInput.encode C)
      (some (unaryEncodeNat C.domainEntryCount))
      ((RuntimeCompilerInput.encode C).length + 1) := by
  let payload := RuntimeSystem.finEncoding.encode C
  have hheader := domainEntryCount_header_evals
    C.domainEntryCount payload [] none
  have hpayload := domainEntryCount_payload_evals payload
    (List.replicate C.domainEntryCount true) (some false)
  have hall := EvalsToInTime.trans domainEntryCountComputer.step
    (C.domainEntryCount + 1) (payload.length + 1)
    (domainEntryCountCfg (some .header) none
      (List.replicate C.domainEntryCount true ++ false :: payload) [])
    (domainEntryCountCfg (some .payload) (some false) payload
      (List.replicate C.domainEntryCount true))
    (some (domainEntryCountCfg none none []
      (List.replicate C.domainEntryCount true)))
    (by simpa using hheader) hpayload
  rw [TM2OutputsInTime, domainEntryCount_initList_eq_cfg]
  simp only [Option.map_some]
  rw [domainEntryCount_unaryEncodeNat_eq,
    domainEntryCount_haltList_eq_cfg]
  simpa [RuntimeCompilerInput.encode, payload, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hall

/-- Genuine linear-time production of the explicit domain-occurrence bound
from the checked compiler input encoding. -/
noncomputable def domainEntryCountComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem ℕ
      RuntimeCompilerInput.finEncoding unaryFinEncodingNat
      RuntimeSystem.domainEntryCount where
  tm := domainEntryCountComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun C := by
    simpa [RuntimeCompilerInput.finEncoding, unaryFinEncodingNat, Equiv.refl,
      Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X] using
        domainEntryCount_outputsInTime C

/-! ## Runtime structural payload

The prime-selection pass consumes the checked unary header, but structural row
construction needs the compact nested-list payload that follows it.  The
machine below discards exactly that header and its delimiter, reverses the
remaining payload onto a scratch stack, and restores it byte-for-byte on the
output stack.  Composing this pass with `unframeComputer` exposes all of the
runtime system's raw length and value fields to later compiler passes.
-/

inductive CompilerPayloadStack
  | input
  | scratch
  | output
  deriving DecidableEq, Fintype

inductive CompilerPayloadLabel
  | header
  | stash
  | restore
  deriving DecidableEq, Fintype

abbrev CompilerPayloadState := Option Bool

private def compilerPayloadPopped
    (_state : CompilerPayloadState) (bit : Option Bool) :
    CompilerPayloadState :=
  bit

private def compilerPayloadTrue : CompilerPayloadState → Bool
  | some true => true
  | _ => false

private def compilerPayloadPresent : CompilerPayloadState → Bool
  | some _ => true
  | none => false

private def compilerPayloadHeld : CompilerPayloadState → Bool
  | some bit => bit
  | none => false

private def CompilerPayloadAlphabet (_ : CompilerPayloadStack) : Type := Bool

/-- Discard the unary occurrence header, preserve the compact payload on a
scratch stack, and restore the payload in its original order. -/
def compilerPayloadProgram :
    CompilerPayloadLabel →
      TM2.Stmt CompilerPayloadAlphabet CompilerPayloadLabel
        CompilerPayloadState
  | .header =>
      .pop .input compilerPayloadPopped <|
        .branch compilerPayloadTrue
          (.goto (fun _ => .header))
          (.branch compilerPayloadPresent
            (.goto (fun _ => .stash))
            .halt)
  | .stash =>
      .pop .input compilerPayloadPopped <|
        .branch compilerPayloadPresent
          (.push .scratch compilerPayloadHeld <|
            .goto (fun _ => .stash))
          (.goto (fun _ => .restore))
  | .restore =>
      .pop .scratch compilerPayloadPopped <|
        .branch compilerPayloadPresent
          (.push .output compilerPayloadHeld <|
            .goto (fun _ => .restore))
          .halt

def compilerPayloadComputer : FinTM2 where
  K := CompilerPayloadStack
  k₀ := .input
  k₁ := .output
  Γ := CompilerPayloadAlphabet
  Λ := CompilerPayloadLabel
  main := .header
  σ := CompilerPayloadState
  initialState := none
  Γk₀Fin := Bool.fintype
  m := compilerPayloadProgram

private def compilerPayloadStackContents
    (input scratch output : List Bool) :
    (index : CompilerPayloadStack) → List (CompilerPayloadAlphabet index)
  | .input => input
  | .scratch => scratch
  | .output => output

private def compilerPayloadCfg (label : Option CompilerPayloadLabel)
    (state : CompilerPayloadState) (input scratch output : List Bool) :
    compilerPayloadComputer.Cfg where
  l := label
  var := state
  stk := compilerPayloadStackContents input scratch output

private theorem compilerPayload_step_header_true
    (input scratch output : List Bool) (state : CompilerPayloadState) :
    compilerPayloadComputer.step
        (compilerPayloadCfg (some .header) state
          (true :: input) scratch output) =
      some (compilerPayloadCfg (some .header) (some true)
        input scratch output) := by
  simp [compilerPayloadComputer, FinTM2.step, compilerPayloadCfg,
    compilerPayloadProgram, compilerPayloadStackContents,
    CompilerPayloadAlphabet, compilerPayloadPopped, compilerPayloadTrue]
  funext index
  cases index <;> rfl

private theorem compilerPayload_step_header_false
    (input scratch output : List Bool) (state : CompilerPayloadState) :
    compilerPayloadComputer.step
        (compilerPayloadCfg (some .header) state
          (false :: input) scratch output) =
      some (compilerPayloadCfg (some .stash) (some false)
        input scratch output) := by
  simp [compilerPayloadComputer, FinTM2.step, compilerPayloadCfg,
    compilerPayloadProgram, compilerPayloadStackContents,
    CompilerPayloadAlphabet, compilerPayloadPopped, compilerPayloadTrue,
    compilerPayloadPresent]
  funext index
  cases index <;> rfl

private theorem compilerPayload_step_stash_cons
    (bit : Bool) (input scratch output : List Bool)
    (state : CompilerPayloadState) :
    compilerPayloadComputer.step
        (compilerPayloadCfg (some .stash) state
          (bit :: input) scratch output) =
      some (compilerPayloadCfg (some .stash) (some bit)
        input (bit :: scratch) output) := by
  simp [compilerPayloadComputer, FinTM2.step, compilerPayloadCfg,
    compilerPayloadProgram, compilerPayloadStackContents,
    CompilerPayloadAlphabet, compilerPayloadPopped,
    compilerPayloadPresent, compilerPayloadHeld, Function.update]
  funext index
  cases index <;> rfl

private theorem compilerPayload_step_stash_nil
    (scratch output : List Bool) (state : CompilerPayloadState) :
    compilerPayloadComputer.step
        (compilerPayloadCfg (some .stash) state [] scratch output) =
      some (compilerPayloadCfg (some .restore) none
        [] scratch output) := by
  simp [compilerPayloadComputer, FinTM2.step, compilerPayloadCfg,
    compilerPayloadProgram, compilerPayloadStackContents,
    CompilerPayloadAlphabet, compilerPayloadPopped,
    compilerPayloadPresent]

private theorem compilerPayload_step_restore_cons
    (bit : Bool) (scratch output : List Bool)
    (state : CompilerPayloadState) :
    compilerPayloadComputer.step
        (compilerPayloadCfg (some .restore) state
          [] (bit :: scratch) output) =
      some (compilerPayloadCfg (some .restore) (some bit)
        [] scratch (bit :: output)) := by
  simp [compilerPayloadComputer, FinTM2.step, compilerPayloadCfg,
    compilerPayloadProgram, compilerPayloadStackContents,
    CompilerPayloadAlphabet, compilerPayloadPopped,
    compilerPayloadPresent, compilerPayloadHeld, Function.update]
  funext index
  cases index <;> rfl

private theorem compilerPayload_step_restore_nil
    (output : List Bool) (state : CompilerPayloadState) :
    compilerPayloadComputer.step
        (compilerPayloadCfg (some .restore) state [] [] output) =
      some (compilerPayloadCfg none none [] [] output) := by
  simp [compilerPayloadComputer, FinTM2.step, compilerPayloadCfg,
    compilerPayloadProgram, compilerPayloadStackContents,
    CompilerPayloadAlphabet, compilerPayloadPopped,
    compilerPayloadPresent]

private def compilerPayloadEvalsToInTimeOne
    {start finish : compilerPayloadComputer.Cfg}
    (hstep : compilerPayloadComputer.step start = some finish) :
    EvalsToInTime compilerPayloadComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def compilerPayload_header_evals
    (count : ℕ) (payload scratch output : List Bool)
    (state : CompilerPayloadState) :
    EvalsToInTime compilerPayloadComputer.step
      (compilerPayloadCfg (some .header) state
        (List.replicate count true ++ false :: payload) scratch output)
      (some (compilerPayloadCfg (some .stash) (some false)
        payload scratch output))
      (count + 1) := by
  induction count generalizing state with
  | zero =>
      simpa using compilerPayloadEvalsToInTimeOne
        (compilerPayload_step_header_false payload scratch output state)
  | succ count ih =>
      let middle := compilerPayloadCfg (some .header) (some true)
        (List.replicate count true ++ false :: payload) scratch output
      have hone : EvalsToInTime compilerPayloadComputer.step
          (compilerPayloadCfg (some .header) state
            (List.replicate (count + 1) true ++ false :: payload)
            scratch output)
          (some middle) 1 :=
        compilerPayloadEvalsToInTimeOne (by
          simpa [middle, List.replicate_succ] using
            compilerPayload_step_header_true
              (List.replicate count true ++ false :: payload)
              scratch output state)
      have hrest := ih (some true)
      have hall := EvalsToInTime.trans compilerPayloadComputer.step
        1 (count + 1)
        (compilerPayloadCfg (some .header) state
          (List.replicate (count + 1) true ++ false :: payload)
          scratch output)
        middle
        (some (compilerPayloadCfg (some .stash) (some false)
          payload scratch output))
        hone
        (by simpa [middle, List.replicate_succ] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def compilerPayload_stash_evals
    (payload scratch output : List Bool) (state : CompilerPayloadState) :
    EvalsToInTime compilerPayloadComputer.step
      (compilerPayloadCfg (some .stash) state payload scratch output)
      (some (compilerPayloadCfg (some .restore) none []
        (payload.reverse ++ scratch) output))
      (payload.length + 1) := by
  induction payload generalizing scratch state with
  | nil =>
      simpa using compilerPayloadEvalsToInTimeOne
        (compilerPayload_step_stash_nil scratch output state)
  | cons bit payload ih =>
      let middle := compilerPayloadCfg (some .stash) (some bit)
        payload (bit :: scratch) output
      have hone : EvalsToInTime compilerPayloadComputer.step
          (compilerPayloadCfg (some .stash) state
            (bit :: payload) scratch output)
          (some middle) 1 :=
        compilerPayloadEvalsToInTimeOne (by
          simpa [middle] using compilerPayload_step_stash_cons
            bit payload scratch output state)
      have hrest := ih (bit :: scratch) (some bit)
      have hall := EvalsToInTime.trans compilerPayloadComputer.step
        1 (payload.length + 1)
        (compilerPayloadCfg (some .stash) state
          (bit :: payload) scratch output)
        middle
        (some (compilerPayloadCfg (some .restore) none []
          ((bit :: payload).reverse ++ scratch) output))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def compilerPayload_restore_evals
    (scratch output : List Bool) (state : CompilerPayloadState) :
    EvalsToInTime compilerPayloadComputer.step
      (compilerPayloadCfg (some .restore) state [] scratch output)
      (some (compilerPayloadCfg none none [] []
        (scratch.reverse ++ output)))
      (scratch.length + 1) := by
  induction scratch generalizing output state with
  | nil =>
      simpa using compilerPayloadEvalsToInTimeOne
        (compilerPayload_step_restore_nil output state)
  | cons bit scratch ih =>
      let middle := compilerPayloadCfg (some .restore) (some bit)
        [] scratch (bit :: output)
      have hone : EvalsToInTime compilerPayloadComputer.step
          (compilerPayloadCfg (some .restore) state
            [] (bit :: scratch) output)
          (some middle) 1 :=
        compilerPayloadEvalsToInTimeOne (by
          simpa [middle] using compilerPayload_step_restore_cons
            bit scratch output state)
      have hrest := ih (bit :: output) (some bit)
      have hall := EvalsToInTime.trans compilerPayloadComputer.step
        1 (scratch.length + 1)
        (compilerPayloadCfg (some .restore) state
          [] (bit :: scratch) output)
        middle
        (some (compilerPayloadCfg none none [] []
          ((bit :: scratch).reverse ++ output)))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private theorem compilerPayload_initList_eq_cfg (input : List Bool) :
    initList compilerPayloadComputer input =
      compilerPayloadCfg (some .header) none input [] [] := by
  unfold initList compilerPayloadCfg
  congr
  funext index
  cases index <;> rfl

private theorem compilerPayload_haltList_eq_cfg (output : List Bool) :
    haltList compilerPayloadComputer output =
      compilerPayloadCfg none none [] [] output := by
  unfold haltList compilerPayloadCfg
  congr
  funext index
  cases index <;> rfl

/-- The header-removal pass emits the compact runtime-system payload unchanged
in at most twice the complete compiler-input length plus one step. -/
def compilerPayload_outputsInTime (C : RuntimeSystem) :
    TM2OutputsInTime compilerPayloadComputer
      (RuntimeCompilerInput.encode C)
      (some (RuntimeSystem.finEncoding.encode C))
      (2 * (RuntimeCompilerInput.encode C).length + 1) := by
  let payload := RuntimeSystem.finEncoding.encode C
  have hheader := compilerPayload_header_evals
    C.domainEntryCount payload [] [] none
  have hstash := compilerPayload_stash_evals payload [] [] (some false)
  have hfirst := EvalsToInTime.trans compilerPayloadComputer.step
    (C.domainEntryCount + 1) (payload.length + 1)
    (compilerPayloadCfg (some .header) none
      (List.replicate C.domainEntryCount true ++ false :: payload) [] [])
    (compilerPayloadCfg (some .stash) (some false) payload [] [])
    (some (compilerPayloadCfg (some .restore) none [] payload.reverse []))
    (by simpa using hheader)
    (by simpa using hstash)
  have hrestore := compilerPayload_restore_evals payload.reverse [] none
  have hall := EvalsToInTime.trans compilerPayloadComputer.step
    ((payload.length + 1) + (C.domainEntryCount + 1))
    (payload.reverse.length + 1)
    (compilerPayloadCfg (some .header) none
      (List.replicate C.domainEntryCount true ++ false :: payload) [] [])
    (compilerPayloadCfg (some .restore) none [] payload.reverse [])
    (some (compilerPayloadCfg none none [] [] payload))
    (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst)
    (by simpa using hrestore)
  have htime :
      (payload.reverse.length + 1) +
          ((payload.length + 1) + (C.domainEntryCount + 1)) ≤
        2 * (RuntimeCompilerInput.encode C).length + 1 := by
    simp [RuntimeCompilerInput.encode, payload]
    omega
  have hmono := evalsToInTimeMono hall htime
  rw [TM2OutputsInTime, compilerPayload_initList_eq_cfg]
  simp only [Option.map_some]
  rw [compilerPayload_haltList_eq_cfg]
  simpa [RuntimeCompilerInput.encode, payload] using hmono

/-- Genuine linear-time removal of the decoder-checked unary header.  The
computed runtime system is unchanged; only its finite encoding changes from
the compiler-facing form to the compact nested-list form. -/
noncomputable def compilerPayloadComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem RuntimeSystem
      RuntimeCompilerInput.finEncoding RuntimeSystem.finEncoding id where
  tm := compilerPayloadComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 1
  outputsFun C := by
    simpa [RuntimeCompilerInput.finEncoding, RuntimeSystem.finEncoding,
      Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using
        compilerPayload_outputsInTime C

/-- The existing unframing traversal, specialized to the compact runtime-
system encoding, exposes its exact semantic nested-list representation. -/
noncomputable def runtimeSystemUnframedComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem (List (List ℕ))
      RuntimeSystem.finEncoding RawNatLists.finEncoding
      RuntimeSystem.toNatLists where
  tm := unframeComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Option Bool)
  time := 3 * Polynomial.X
  outputsFun C := by
    simpa [RuntimeSystem.finEncoding, RawNatLists.finEncoding, Equiv.refl,
      Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_X] using
        unframe_outputsInTime C.toNatLists

private noncomputable def runtimeCompilerRawFieldsComposition :
    @TM2ComputableInPolyTime RuntimeSystem (List (List ℕ))
      RuntimeCompilerInput.finEncoding RawNatLists.finEncoding
      (RuntimeSystem.toNatLists ∘ id) :=
  compositionComputableInPolyTime
    RuntimeCompilerInput.finEncoding RuntimeSystem.finEncoding
    RawNatLists.finEncoding id RuntimeSystem.toNatLists
    compilerPayloadComputableInPolyTime
    runtimeSystemUnframedComputableInPolyTime

/-- From the actual checked compiler input, a concrete composed polynomial-
time machine emits the raw outer length, inner lengths, and value fields of
the complete runtime CSP payload. -/
noncomputable def runtimeCompilerRawFieldsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem (List (List ℕ))
      RuntimeCompilerInput.finEncoding RawNatLists.finEncoding
      RuntimeSystem.toNatLists := by
  let composed := runtimeCompilerRawFieldsComposition
  exact { composed with
    outputsFun := fun C => by
      simpa [Function.comp_def] using composed.outputsFun C }

/-! ## Source-order runtime fields

The stack-oriented raw encoding above exposes the final CSP field first.  The
structural producer instead needs the outer length and domain-count separator
before it sees the domains and scopes.  A single whole-stream reversal changes
only the raw representation, not the decoded nested lists.  It places fields
in semantic source order and puts each field delimiter before its canonical
binary payload.
-/

export LeanNPHardness.MachinePrimitives
  (SourceOrderRawFieldStack SourceOrderRawFieldLabel SourceOrderRawFieldState sourceOrderRawFieldProgram sourceOrderRawFieldComputer
   sourceOrderRawFields_outputsInTime sourceOrderRawFieldsComputableInPolyTime)

private noncomputable def runtimeCompilerSourceOrderFieldsComposition :
    @TM2ComputableInPolyTime RuntimeSystem (List (List ℕ))
      RuntimeCompilerInput.finEncoding SourceOrderRawNatLists.finEncoding
      (id ∘ RuntimeSystem.toNatLists) :=
  compositionComputableInPolyTime
    RuntimeCompilerInput.finEncoding RawNatLists.finEncoding
    SourceOrderRawNatLists.finEncoding RuntimeSystem.toNatLists id
    runtimeCompilerRawFieldsComputableInPolyTime
    sourceOrderRawFieldsComputableInPolyTime

/-- From the actual checked compiler input, a composed polynomial-time machine
emits the outer length and domain-count header before every domain and scope
field.  This is the input contract for the next tagged structural emitter. -/
noncomputable def runtimeCompilerSourceOrderFieldsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem (List (List ℕ))
      RuntimeCompilerInput.finEncoding SourceOrderRawNatLists.finEncoding
      RuntimeSystem.toNatLists := by
  let composed := runtimeCompilerSourceOrderFieldsComposition
  exact { composed with
    outputsFun := fun C => by
      simpa [Function.comp_def] using composed.outputsFun C }

/-! ## Binary successor

The prime scan and several structural compiler passes need arithmetic on the
raw binary fields exposed above. The following machine supplies the first such
primitive: successor on mathlib's least-significant-bit-first natural-number
encoding. It propagates carry on the input stack, copies the untouched suffix,
and reverses one work stack into the canonical output order.
-/

export LeanNPHardness.MachinePrimitives
  (binarySuccBits binarySuccBits_encodeNat binarySuccBits_length_le SuccStack SuccLabel
   SuccState binarySuccProgram binarySuccComputer binarySucc_outputsInTime binarySuccComputableInPolyTime
   binaryPredBits binaryPredBits_encodeNat PredStack PredLabel PredState
   binaryPredProgram binaryPredComputer binaryPred_outputsInTime binaryPredComputableInPolyTime binaryLEUpdate
   binaryLEBitsAux binaryLEPairsAux binaryLEPairsAux_zipBits orderingLEResult binaryLEBitsAux_encodeNat
   CompareStack CompareLabel CompareState binaryLEProgram binaryLEComputer
   binaryLE_outputsInTime binaryLEComputableInPolyTime binaryAddStep binaryAddBitsAux binaryAddPairsAux
   binaryAddPairsAux_zipBits binaryAddBitsAux_encodeNat AddStack AddLabel AddState
   binaryAddProgram binaryAddComputer binaryAdd_outputsInTime binaryAddComputableInPolyTime)
namespace BinaryNatPair
export LeanNPHardness.MachinePrimitives.BinaryNatPair
  (zipBits leftBits rightBits leftBits_zipBits rightBits_zipBits
   encode decode decode_encode finEncoding)
end BinaryNatPair


/-! ## Tagged scope field blocks

The source-order compact stream presents each scope as its entry count followed
by the entries themselves.  The structural target retains those entries
verbatim, increments the row length to account for the local tag, and inserts
tag `1`.  The following fused finite machine performs that whole local pass.
It propagates successor only across the first binary field, copies the
remaining scope fields unchanged, and stages the result through one reversal
so that the output remains in semantic source order.
-/

namespace ScopeFieldBlock

/-- One source-order natural field, including its leading delimiter. -/
def fieldSegment (field : ℕ) : List (Option Bool) :=
  none :: (encodeNat field).map some

/-- The fixed source-order field for scope tag `1`. -/
def tagSegment : List (Option Bool) :=
  [none, some true]

private theorem encodeNat_zero : encodeNat 0 = [] := by
  unfold encodeNat
  change encodeNum (Num.ofNat' 0) = []
  rw [Num.ofNat'_zero]
  rfl

private theorem encodeNat_one : encodeNat 1 = [true] := by
  unfold encodeNat
  change encodeNum (Num.ofNat' 1) = [true]
  rw [Num.ofNat'_one]
  rfl

/-- A source scope arrives as its entry count followed by every entry. -/
def inputEncode (entries : List ℕ) : List (Option Bool) :=
  SourceOrderRawFields.encode (entries.length :: entries)

/-- Decode one count-checked source scope. -/
def inputDecode (input : List (Option Bool)) : Option (List ℕ) := do
  match ← SourceOrderRawFields.decode input with
  | count :: entries =>
      if count = entries.length then some entries else none
  | [] => none

@[simp]
theorem inputDecode_encode (entries : List ℕ) :
    inputDecode (inputEncode entries) = some entries := by
  simp [inputDecode, inputEncode]

/-- Checked local input encoding for one complete scope. -/
def inputFinEncoding : FinEncoding (List ℕ) where
  Γ := Option Bool
  encode := inputEncode
  decode := inputDecode
  decode_encode := inputDecode_encode
  ΓFin := inferInstance

/-- The exact structural scope block: row length, tag, and unchanged entries. -/
def outputEncode (entries : List ℕ) : List (Option Bool) :=
  SourceOrderRawFields.encode ((entries.length + 1) :: 1 :: entries)

/-- Decode one checked tagged scope block. -/
def outputDecode (input : List (Option Bool)) : Option (List ℕ) := do
  match ← SourceOrderRawFields.decode input with
  | rowLength :: tag :: entries =>
      if tag = 1 ∧ rowLength = entries.length + 1 then some entries else none
  | _ => none

@[simp]
theorem outputDecode_encode (entries : List ℕ) :
    outputDecode (outputEncode entries) = some entries := by
  simp [outputDecode, outputEncode]

/-- Checked local output encoding for one complete tagged scope. -/
def outputFinEncoding : FinEncoding (List ℕ) where
  Γ := Option Bool
  encode := outputEncode
  decode := outputDecode
  decode_encode := outputDecode_encode
  ΓFin := inferInstance

theorem inputEncode_eq (entries : List ℕ) :
    inputEncode entries =
      fieldSegment entries.length ++ SourceOrderRawFields.encode entries := by
  simp [inputEncode, fieldSegment, SourceOrderRawFields.encode]

theorem outputEncode_eq (entries : List ℕ) :
    outputEncode entries =
      fieldSegment (entries.length + 1) ++ tagSegment ++
        SourceOrderRawFields.encode entries := by
  simp [outputEncode, fieldSegment, tagSegment,
    SourceOrderRawFields.encode, encodeNat_one]

/-- The semantic output fields are exactly the length-prefixed tagged record
used by `RuntimeStructuralView`. -/
theorem fields_eq_record (entries : List ℕ) :
    (entries.length + 1) :: 1 :: entries =
      (RuntimeStructuralRecord.scope entries).toNatList.length ::
        (RuntimeStructuralRecord.scope entries).toNatList := by
  simp [RuntimeStructuralRecord.toNatList]

theorem outputEncode_length_le (entries : List ℕ) :
    (outputEncode entries).length ≤ (inputEncode entries).length + 3 := by
  have hsucc := binarySuccBits_length_le (encodeNat entries.length)
  rw [binarySuccBits_encodeNat] at hsucc
  rw [inputEncode_eq, outputEncode_eq]
  simp only [List.length_append, fieldSegment, tagSegment, List.length_cons,
    List.length_nil, List.length_map]
  omega

end ScopeFieldBlock

/-- Input, reversed staging, and source-order output stacks for one scope. -/
inductive ScopeFieldBlockStack
  | input
  | scratch
  | output
  deriving DecidableEq, Fintype

/-- First-field successor, suffix copying, and output-restoration phases. -/
inductive ScopeFieldBlockLabel
  | start
  | carry
  | copyLength
  | copyRest
  | restore
  deriving DecidableEq, Fintype

/-- Finite control remembers the most recently popped raw-field cell. -/
abbrev ScopeFieldBlockState := Option (Option Bool)

private def scopeFieldBlockPopped
    (_state : ScopeFieldBlockState)
    (symbol : Option (Option Bool)) : ScopeFieldBlockState :=
  symbol

private def scopeFieldBlockPresent : ScopeFieldBlockState → Bool
  | some _ => true
  | none => false

private def scopeFieldBlockIsBit : ScopeFieldBlockState → Bool
  | some (some _) => true
  | _ => false

private def scopeFieldBlockBitTrue : ScopeFieldBlockState → Bool
  | some (some true) => true
  | _ => false

private def scopeFieldBlockHeld : ScopeFieldBlockState → Option Bool
  | some symbol => symbol
  | none => none

private def ScopeFieldBlockAlphabet
    (_index : ScopeFieldBlockStack) : Type :=
  Option Bool

/-- A fused finite program that increments the source row length, inserts the
scope tag, and copies every scope-entry field unchanged. -/
def scopeFieldBlockProgram :
    ScopeFieldBlockLabel →
      TM2.Stmt ScopeFieldBlockAlphabet ScopeFieldBlockLabel
        ScopeFieldBlockState
  | .start =>
      .pop .input scopeFieldBlockPopped <|
        .push .scratch (fun _ => (none : Option Bool)) <|
          .goto (fun _ => .carry)
  | .carry =>
      .pop .input scopeFieldBlockPopped <|
        .branch scopeFieldBlockPresent
          (.branch scopeFieldBlockIsBit
            (.branch scopeFieldBlockBitTrue
              (.push .scratch (fun _ => some false) <|
                .goto (fun _ => .carry))
              (.push .scratch (fun _ => some true) <|
                .goto (fun _ => .copyLength)))
            (.push .scratch (fun _ => some true) <|
              .push .scratch (fun _ => (none : Option Bool)) <|
                .push .scratch (fun _ => some true) <|
                  .push .scratch (fun _ => (none : Option Bool)) <|
                    .goto (fun _ => .copyRest)))
          (.push .scratch (fun _ => some true) <|
            .push .scratch (fun _ => (none : Option Bool)) <|
              .push .scratch (fun _ => some true) <|
                .goto (fun _ => .restore))
  | .copyLength =>
      .pop .input scopeFieldBlockPopped <|
        .branch scopeFieldBlockPresent
          (.branch scopeFieldBlockIsBit
            (.push .scratch scopeFieldBlockHeld <|
              .goto (fun _ => .copyLength))
            (.push .scratch (fun _ => (none : Option Bool)) <|
              .push .scratch (fun _ => some true) <|
                .push .scratch (fun _ => (none : Option Bool)) <|
                  .goto (fun _ => .copyRest)))
          (.push .scratch (fun _ => (none : Option Bool)) <|
            .push .scratch (fun _ => some true) <|
              .goto (fun _ => .restore))
  | .copyRest =>
      .pop .input scopeFieldBlockPopped <|
        .branch scopeFieldBlockPresent
          (.push .scratch scopeFieldBlockHeld <|
            .goto (fun _ => .copyRest))
          (.goto (fun _ => .restore))
  | .restore =>
      .pop .scratch scopeFieldBlockPopped <|
        .branch scopeFieldBlockPresent
          (.push .output scopeFieldBlockHeld <|
            .goto (fun _ => .restore))
          .halt

/-- Concrete finite machine for one complete tagged scope block. -/
def scopeFieldBlockComputer : FinTM2 where
  K := ScopeFieldBlockStack
  k₀ := .input
  k₁ := .output
  Γ := ScopeFieldBlockAlphabet
  Λ := ScopeFieldBlockLabel
  main := .start
  σ := ScopeFieldBlockState
  initialState := none
  Γk₀Fin := show Fintype (Option Bool) from inferInstance
  m := scopeFieldBlockProgram

private def scopeFieldBlockStacks
    (input scratch output : List (Option Bool)) :
    (index : ScopeFieldBlockStack) →
      List (ScopeFieldBlockAlphabet index)
  | .input => input
  | .scratch => scratch
  | .output => output

private def scopeFieldBlockCfg
    (label : Option ScopeFieldBlockLabel)
    (state : ScopeFieldBlockState)
    (input scratch output : List (Option Bool)) :
    scopeFieldBlockComputer.Cfg where
  l := label
  var := state
  stk := scopeFieldBlockStacks input scratch output

private theorem scopeFieldBlock_step_start
    (input scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    scopeFieldBlockComputer.step
        (scopeFieldBlockCfg (some .start) state
          (none :: input) scratch output) =
      some (scopeFieldBlockCfg (some .carry) (some none)
        input (none :: scratch) output) := by
  simp [scopeFieldBlockComputer, FinTM2.step, scopeFieldBlockCfg,
    scopeFieldBlockProgram, scopeFieldBlockStacks, ScopeFieldBlockAlphabet,
    scopeFieldBlockPopped, Function.update]
  funext index
  cases index <;> rfl

private theorem scopeFieldBlock_step_carry_true
    (input scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    scopeFieldBlockComputer.step
        (scopeFieldBlockCfg (some .carry) state
          (some true :: input) scratch output) =
      some (scopeFieldBlockCfg (some .carry) (some (some true))
        input (some false :: scratch) output) := by
  simp [scopeFieldBlockComputer, FinTM2.step, scopeFieldBlockCfg,
    scopeFieldBlockProgram, scopeFieldBlockStacks, ScopeFieldBlockAlphabet,
    scopeFieldBlockPopped, scopeFieldBlockPresent, scopeFieldBlockIsBit,
    scopeFieldBlockBitTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem scopeFieldBlock_step_carry_false
    (input scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    scopeFieldBlockComputer.step
        (scopeFieldBlockCfg (some .carry) state
          (some false :: input) scratch output) =
      some (scopeFieldBlockCfg (some .copyLength) (some (some false))
        input (some true :: scratch) output) := by
  simp [scopeFieldBlockComputer, FinTM2.step, scopeFieldBlockCfg,
    scopeFieldBlockProgram, scopeFieldBlockStacks, ScopeFieldBlockAlphabet,
    scopeFieldBlockPopped, scopeFieldBlockPresent, scopeFieldBlockIsBit,
    scopeFieldBlockBitTrue, Function.update]
  funext index
  cases index <;> rfl

private theorem scopeFieldBlock_step_carry_delimiter
    (input scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    scopeFieldBlockComputer.step
        (scopeFieldBlockCfg (some .carry) state
          (none :: input) scratch output) =
      some (scopeFieldBlockCfg (some .copyRest) (some none) input
        (none :: some true :: none :: some true :: scratch) output) := by
  simp [scopeFieldBlockComputer, FinTM2.step, scopeFieldBlockCfg,
    scopeFieldBlockProgram, scopeFieldBlockStacks, ScopeFieldBlockAlphabet,
    scopeFieldBlockPopped, scopeFieldBlockPresent, scopeFieldBlockIsBit,
    Function.update]
  funext index
  cases index <;> rfl

private theorem scopeFieldBlock_step_carry_nil
    (scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    scopeFieldBlockComputer.step
        (scopeFieldBlockCfg (some .carry) state [] scratch output) =
      some (scopeFieldBlockCfg (some .restore) none []
        (some true :: none :: some true :: scratch) output) := by
  simp [scopeFieldBlockComputer, FinTM2.step, scopeFieldBlockCfg,
    scopeFieldBlockProgram, scopeFieldBlockStacks, ScopeFieldBlockAlphabet,
    scopeFieldBlockPopped, scopeFieldBlockPresent, Function.update]
  funext index
  cases index <;> rfl

private theorem scopeFieldBlock_step_copyLength_bit
    (bit : Bool) (input scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    scopeFieldBlockComputer.step
        (scopeFieldBlockCfg (some .copyLength) state
          (some bit :: input) scratch output) =
      some (scopeFieldBlockCfg (some .copyLength) (some (some bit))
        input (some bit :: scratch) output) := by
  cases bit <;>
    simp [scopeFieldBlockComputer, FinTM2.step, scopeFieldBlockCfg,
      scopeFieldBlockProgram, scopeFieldBlockStacks, ScopeFieldBlockAlphabet,
      scopeFieldBlockPopped, scopeFieldBlockPresent, scopeFieldBlockIsBit,
      scopeFieldBlockHeld, Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem scopeFieldBlock_step_copyLength_delimiter
    (input scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    scopeFieldBlockComputer.step
        (scopeFieldBlockCfg (some .copyLength) state
          (none :: input) scratch output) =
      some (scopeFieldBlockCfg (some .copyRest) (some none) input
        (none :: some true :: none :: scratch) output) := by
  simp [scopeFieldBlockComputer, FinTM2.step, scopeFieldBlockCfg,
    scopeFieldBlockProgram, scopeFieldBlockStacks, ScopeFieldBlockAlphabet,
    scopeFieldBlockPopped, scopeFieldBlockPresent, scopeFieldBlockIsBit,
    Function.update]
  funext index
  cases index <;> rfl

private theorem scopeFieldBlock_step_copyLength_nil
    (scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    scopeFieldBlockComputer.step
        (scopeFieldBlockCfg (some .copyLength) state [] scratch output) =
      some (scopeFieldBlockCfg (some .restore) none []
        (some true :: none :: scratch) output) := by
  simp [scopeFieldBlockComputer, FinTM2.step, scopeFieldBlockCfg,
    scopeFieldBlockProgram, scopeFieldBlockStacks, ScopeFieldBlockAlphabet,
    scopeFieldBlockPopped, scopeFieldBlockPresent, Function.update]
  funext index
  cases index <;> rfl

private theorem scopeFieldBlock_step_copyRest_cons
    (symbol : Option Bool) (input scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    scopeFieldBlockComputer.step
        (scopeFieldBlockCfg (some .copyRest) state
          (symbol :: input) scratch output) =
      some (scopeFieldBlockCfg (some .copyRest) (some symbol)
        input (symbol :: scratch) output) := by
  cases symbol <;>
    simp [scopeFieldBlockComputer, FinTM2.step, scopeFieldBlockCfg,
      scopeFieldBlockProgram, scopeFieldBlockStacks, ScopeFieldBlockAlphabet,
      scopeFieldBlockPopped, scopeFieldBlockPresent, scopeFieldBlockHeld,
      Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem scopeFieldBlock_step_copyRest_nil
    (scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    scopeFieldBlockComputer.step
        (scopeFieldBlockCfg (some .copyRest) state [] scratch output) =
      some (scopeFieldBlockCfg (some .restore) none [] scratch output) := by
  simp [scopeFieldBlockComputer, FinTM2.step, scopeFieldBlockCfg,
    scopeFieldBlockProgram, scopeFieldBlockStacks, ScopeFieldBlockAlphabet,
    scopeFieldBlockPopped, scopeFieldBlockPresent, Function.update]

private theorem scopeFieldBlock_step_restore_cons
    (symbol : Option Bool) (scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    scopeFieldBlockComputer.step
        (scopeFieldBlockCfg (some .restore) state []
          (symbol :: scratch) output) =
      some (scopeFieldBlockCfg (some .restore) (some symbol)
        [] scratch (symbol :: output)) := by
  cases symbol <;>
    simp [scopeFieldBlockComputer, FinTM2.step, scopeFieldBlockCfg,
      scopeFieldBlockProgram, scopeFieldBlockStacks, ScopeFieldBlockAlphabet,
      scopeFieldBlockPopped, scopeFieldBlockPresent, scopeFieldBlockHeld,
      Function.update] <;>
    (funext index; cases index <;> rfl)

private theorem scopeFieldBlock_step_restore_nil
    (output : List (Option Bool)) (state : ScopeFieldBlockState) :
    scopeFieldBlockComputer.step
        (scopeFieldBlockCfg (some .restore) state [] [] output) =
      some (scopeFieldBlockCfg none none [] [] output) := by
  simp [scopeFieldBlockComputer, FinTM2.step, scopeFieldBlockCfg,
    scopeFieldBlockProgram, scopeFieldBlockStacks, ScopeFieldBlockAlphabet,
    scopeFieldBlockPopped, scopeFieldBlockPresent, Function.update]

private def scopeFieldBlockEvalsToInTimeOne
    {start finish : scopeFieldBlockComputer.Cfg}
    (hstep : scopeFieldBlockComputer.step start = some finish) :
    EvalsToInTime scopeFieldBlockComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def scopeFieldBlock_copyRest_evals
    (input scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    EvalsToInTime scopeFieldBlockComputer.step
      (scopeFieldBlockCfg (some .copyRest) state input scratch output)
      (some (scopeFieldBlockCfg (some .restore) none []
        (input.reverse ++ scratch) output))
      (input.length + 1) := by
  induction input generalizing scratch state with
  | nil =>
      simpa using scopeFieldBlockEvalsToInTimeOne
        (scopeFieldBlock_step_copyRest_nil scratch output state)
  | cons symbol input ih =>
      let middle := scopeFieldBlockCfg (some .copyRest) (some symbol)
        input (symbol :: scratch) output
      have hone : EvalsToInTime scopeFieldBlockComputer.step
          (scopeFieldBlockCfg (some .copyRest) state
            (symbol :: input) scratch output)
          (some middle) 1 :=
        scopeFieldBlockEvalsToInTimeOne (by
          simpa [middle] using scopeFieldBlock_step_copyRest_cons
            symbol input scratch output state)
      have hrest := ih (symbol :: scratch) (some symbol)
      have hall := EvalsToInTime.trans scopeFieldBlockComputer.step
        1 (input.length + 1)
        (scopeFieldBlockCfg (some .copyRest) state
          (symbol :: input) scratch output)
        middle
        (some (scopeFieldBlockCfg (some .restore) none []
          ((symbol :: input).reverse ++ scratch) output))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def scopeFieldBlock_restore_evals
    (scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    EvalsToInTime scopeFieldBlockComputer.step
      (scopeFieldBlockCfg (some .restore) state [] scratch output)
      (some (scopeFieldBlockCfg none none [] []
        (scratch.reverse ++ output)))
      (scratch.length + 1) := by
  induction scratch generalizing output state with
  | nil =>
      simpa using scopeFieldBlockEvalsToInTimeOne
        (scopeFieldBlock_step_restore_nil output state)
  | cons symbol scratch ih =>
      let middle := scopeFieldBlockCfg (some .restore) (some symbol)
        [] scratch (symbol :: output)
      have hone : EvalsToInTime scopeFieldBlockComputer.step
          (scopeFieldBlockCfg (some .restore) state []
            (symbol :: scratch) output)
          (some middle) 1 :=
        scopeFieldBlockEvalsToInTimeOne (by
          simpa [middle] using scopeFieldBlock_step_restore_cons
            symbol scratch output state)
      have hrest := ih (symbol :: output) (some symbol)
      have hall := EvalsToInTime.trans scopeFieldBlockComputer.step
        1 (scratch.length + 1)
        (scopeFieldBlockCfg (some .restore) state []
          (symbol :: scratch) output)
        middle
        (some (scopeFieldBlockCfg none none [] []
          ((symbol :: scratch).reverse ++ output)))
        hone
        (by simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def scopeFieldBlock_copyLength_evals
    (bits : List Bool) (tail scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    EvalsToInTime scopeFieldBlockComputer.step
      (scopeFieldBlockCfg (some .copyLength) state
        (bits.map some ++ none :: tail) scratch output)
      (some (scopeFieldBlockCfg (some .restore) none []
        ((bits.map some ++ ScopeFieldBlock.tagSegment ++ none :: tail).reverse ++
          scratch) output))
      (bits.length + tail.length + 2) := by
  induction bits generalizing scratch state with
  | nil =>
      have hone := scopeFieldBlockEvalsToInTimeOne
        (scopeFieldBlock_step_copyLength_delimiter tail scratch output state)
      have hrest := scopeFieldBlock_copyRest_evals tail
        (none :: some true :: none :: scratch) output (some none)
      have hall := EvalsToInTime.trans scopeFieldBlockComputer.step
        1 (tail.length + 1)
        (scopeFieldBlockCfg (some .copyLength) state
          (none :: tail) scratch output)
        (scopeFieldBlockCfg (some .copyRest) (some none) tail
          (none :: some true :: none :: scratch) output)
        (some (scopeFieldBlockCfg (some .restore) none []
          (tail.reverse ++ none :: some true :: none :: scratch) output))
        (by simpa using hone)
        (by simpa using hrest)
      simpa [ScopeFieldBlock.tagSegment, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall
  | cons bit bits ih =>
      let middle := scopeFieldBlockCfg (some .copyLength) (some (some bit))
        (bits.map some ++ none :: tail) (some bit :: scratch) output
      have hone : EvalsToInTime scopeFieldBlockComputer.step
          (scopeFieldBlockCfg (some .copyLength) state
            ((bit :: bits).map some ++ none :: tail) scratch output)
          (some middle) 1 :=
        scopeFieldBlockEvalsToInTimeOne (by
          simpa [middle] using scopeFieldBlock_step_copyLength_bit bit
            (bits.map some ++ none :: tail) scratch output state)
      have hrest := ih (some bit :: scratch) (some (some bit))
      have hall := EvalsToInTime.trans scopeFieldBlockComputer.step
        1 (bits.length + tail.length + 2)
        (scopeFieldBlockCfg (some .copyLength) state
          ((bit :: bits).map some ++ none :: tail) scratch output)
        middle
        (some (scopeFieldBlockCfg (some .restore) none []
          (((bit :: bits).map some ++ ScopeFieldBlock.tagSegment ++
            none :: tail).reverse ++ scratch) output))
        hone
        (by
          simpa [middle, List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def scopeFieldBlock_carry_evals
    (bits : List Bool) (tail scratch output : List (Option Bool))
    (state : ScopeFieldBlockState) :
    EvalsToInTime scopeFieldBlockComputer.step
      (scopeFieldBlockCfg (some .carry) state
        (bits.map some ++ none :: tail) scratch output)
      (some (scopeFieldBlockCfg (some .restore) none []
        (((binarySuccBits bits).map some ++ ScopeFieldBlock.tagSegment ++
          none :: tail).reverse ++ scratch) output))
      (bits.length + tail.length + 2) := by
  induction bits generalizing scratch state with
  | nil =>
      have hone := scopeFieldBlockEvalsToInTimeOne
        (scopeFieldBlock_step_carry_delimiter tail scratch output state)
      have hrest := scopeFieldBlock_copyRest_evals tail
        (none :: some true :: none :: some true :: scratch) output (some none)
      have hall := EvalsToInTime.trans scopeFieldBlockComputer.step
        1 (tail.length + 1)
        (scopeFieldBlockCfg (some .carry) state (none :: tail) scratch output)
        (scopeFieldBlockCfg (some .copyRest) (some none) tail
          (none :: some true :: none :: some true :: scratch) output)
        (some (scopeFieldBlockCfg (some .restore) none []
          (tail.reverse ++ none :: some true :: none :: some true :: scratch)
          output))
        (by simpa using hone)
        (by simpa using hrest)
      simpa [binarySuccBits, ScopeFieldBlock.tagSegment, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall
  | cons bit bits ih =>
      cases bit with
      | false =>
          let middle := scopeFieldBlockCfg (some .copyLength)
            (some (some false)) (bits.map some ++ none :: tail)
            (some true :: scratch) output
          have hone : EvalsToInTime scopeFieldBlockComputer.step
              (scopeFieldBlockCfg (some .carry) state
                ((false :: bits).map some ++ none :: tail) scratch output)
              (some middle) 1 :=
            scopeFieldBlockEvalsToInTimeOne (by
              simpa [middle] using scopeFieldBlock_step_carry_false
                (bits.map some ++ none :: tail) scratch output state)
          have hrest := scopeFieldBlock_copyLength_evals bits tail
            (some true :: scratch) output (some (some false))
          have hall := EvalsToInTime.trans scopeFieldBlockComputer.step
            1 (bits.length + tail.length + 2)
            (scopeFieldBlockCfg (some .carry) state
              ((false :: bits).map some ++ none :: tail) scratch output)
            middle
            (some (scopeFieldBlockCfg (some .restore) none []
              (((binarySuccBits (false :: bits)).map some ++
                ScopeFieldBlock.tagSegment ++ none :: tail).reverse ++ scratch)
              output))
            hone
            (by
              simpa [middle, binarySuccBits, List.reverse_cons,
                List.append_assoc] using hrest)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall
      | true =>
          let middle := scopeFieldBlockCfg (some .carry) (some (some true))
            (bits.map some ++ none :: tail) (some false :: scratch) output
          have hone : EvalsToInTime scopeFieldBlockComputer.step
              (scopeFieldBlockCfg (some .carry) state
                ((true :: bits).map some ++ none :: tail) scratch output)
              (some middle) 1 :=
            scopeFieldBlockEvalsToInTimeOne (by
              simpa [middle] using scopeFieldBlock_step_carry_true
                (bits.map some ++ none :: tail) scratch output state)
          have hrest := ih (some false :: scratch) (some (some true))
          have hall := EvalsToInTime.trans scopeFieldBlockComputer.step
            1 (bits.length + tail.length + 2)
            (scopeFieldBlockCfg (some .carry) state
              ((true :: bits).map some ++ none :: tail) scratch output)
            middle
            (some (scopeFieldBlockCfg (some .restore) none []
              (((binarySuccBits (true :: bits)).map some ++
                ScopeFieldBlock.tagSegment ++ none :: tail).reverse ++ scratch)
              output))
            hone
            (by
              simpa [middle, binarySuccBits, List.reverse_cons,
                List.append_assoc] using hrest)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private theorem scopeFieldBlock_initList_eq_cfg
    (input : List (Option Bool)) :
    initList scopeFieldBlockComputer input =
      scopeFieldBlockCfg (some .start) none input [] [] := by
  unfold initList scopeFieldBlockCfg
  congr
  funext index
  cases index <;> rfl

private theorem scopeFieldBlock_haltList_eq_cfg
    (output : List (Option Bool)) :
    haltList scopeFieldBlockComputer output =
      scopeFieldBlockCfg none none [] [] output := by
  unfold haltList scopeFieldBlockCfg
  congr
  funext index
  cases index <;> rfl

/-- The fused local scope transducer emits the exact tagged scope block in
linear time in the complete source-scope field encoding. -/
def scopeFieldBlock_outputsInTime (entries : List ℕ) :
    TM2OutputsInTime scopeFieldBlockComputer
      (ScopeFieldBlock.inputEncode entries)
      (some (ScopeFieldBlock.outputEncode entries))
      (3 * (ScopeFieldBlock.inputEncode entries).length + 8) := by
  cases entries with
  | nil =>
      have hstart := scopeFieldBlockEvalsToInTimeOne
        (scopeFieldBlock_step_start [] [] [] none)
      have hcarry := scopeFieldBlockEvalsToInTimeOne
        (scopeFieldBlock_step_carry_nil [none] [] (some none))
      have hfirst := EvalsToInTime.trans scopeFieldBlockComputer.step
        1 1
        (scopeFieldBlockCfg (some .start) none [none] [] [])
        (scopeFieldBlockCfg (some .carry) (some none) [] [none] [])
        (some (scopeFieldBlockCfg (some .restore) none []
          [some true, none, some true, none] []))
        (by simpa using hstart)
        (by simpa using hcarry)
      have hrestore := scopeFieldBlock_restore_evals
        [some true, none, some true, none] [] none
      have hall := EvalsToInTime.trans scopeFieldBlockComputer.step
        2 5
        (scopeFieldBlockCfg (some .start) none [none] [] [])
        (scopeFieldBlockCfg (some .restore) none []
          [some true, none, some true, none] [])
        (some (scopeFieldBlockCfg none none [] []
          [none, some true, none, some true]))
        (by simpa using hfirst)
        (by simpa using hrestore)
      have hmono : EvalsToInTime scopeFieldBlockComputer.step
          (scopeFieldBlockCfg (some .start) none [none] [] [])
          (some (scopeFieldBlockCfg none none [] []
            [none, some true, none, some true]))
          (3 * (ScopeFieldBlock.inputEncode []).length + 8) :=
        evalsToInTimeMono hall (by
          simp [ScopeFieldBlock.inputEncode,
            SourceOrderRawFields.encode])
      rw [TM2OutputsInTime, scopeFieldBlock_initList_eq_cfg]
      simp only [Option.map_some]
      rw [scopeFieldBlock_haltList_eq_cfg]
      simpa [ScopeFieldBlock.inputEncode, ScopeFieldBlock.outputEncode,
        SourceOrderRawFields.encode, ScopeFieldBlock.encodeNat_zero,
        ScopeFieldBlock.encodeNat_one] using hmono
  | cons entry entries =>
      let bits := encodeNat (entry :: entries).length
      let tail := (encodeNat entry).map some ++
        SourceOrderRawFields.encode entries
      have hinput : ScopeFieldBlock.inputEncode (entry :: entries) =
          none :: bits.map some ++ none :: tail := by
        simp [ScopeFieldBlock.inputEncode_eq, ScopeFieldBlock.fieldSegment,
          SourceOrderRawFields.encode, bits, tail]
      have houtput : ScopeFieldBlock.outputEncode (entry :: entries) =
          none :: (binarySuccBits bits).map some ++
            ScopeFieldBlock.tagSegment ++ none :: tail := by
        rw [ScopeFieldBlock.outputEncode_eq]
        simp [ScopeFieldBlock.fieldSegment, SourceOrderRawFields.encode,
          bits, tail, binarySuccBits_encodeNat]
      have hstart := scopeFieldBlockEvalsToInTimeOne
        (scopeFieldBlock_step_start
          (bits.map some ++ none :: tail) [] [] none)
      have hcarry := scopeFieldBlock_carry_evals bits tail [none] [] (some none)
      have hfirst := EvalsToInTime.trans scopeFieldBlockComputer.step
        1 (bits.length + tail.length + 2)
        (scopeFieldBlockCfg (some .start) none
          (none :: bits.map some ++ none :: tail) [] [])
        (scopeFieldBlockCfg (some .carry) (some none)
          (bits.map some ++ none :: tail) [none] [])
        (some (scopeFieldBlockCfg (some .restore) none []
          ((none :: (binarySuccBits bits).map some ++
            ScopeFieldBlock.tagSegment ++ none :: tail).reverse) []))
        (by simpa using hstart)
        (by
          simpa [List.reverse_cons, List.append_assoc] using hcarry)
      have hrestore := scopeFieldBlock_restore_evals
        (none :: (binarySuccBits bits).map some ++
          ScopeFieldBlock.tagSegment ++ none :: tail).reverse [] none
      have hall := EvalsToInTime.trans scopeFieldBlockComputer.step
        (1 + (bits.length + tail.length + 2))
        ((none :: (binarySuccBits bits).map some ++
          ScopeFieldBlock.tagSegment ++ none :: tail).reverse.length + 1)
        (scopeFieldBlockCfg (some .start) none
          (none :: bits.map some ++ none :: tail) [] [])
        (scopeFieldBlockCfg (some .restore) none []
          (none :: (binarySuccBits bits).map some ++
            ScopeFieldBlock.tagSegment ++ none :: tail).reverse [])
        (some (scopeFieldBlockCfg none none [] []
          (none :: (binarySuccBits bits).map some ++
            ScopeFieldBlock.tagSegment ++ none :: tail)))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst)
        (by simpa using hrestore)
      have hsize := ScopeFieldBlock.outputEncode_length_le (entry :: entries)
      have hsize' := hsize
      rw [hinput, houtput] at hsize'
      have hmono : EvalsToInTime scopeFieldBlockComputer.step
          (scopeFieldBlockCfg (some .start) none
            (ScopeFieldBlock.inputEncode (entry :: entries)) [] [])
          (some (scopeFieldBlockCfg none none [] []
            (ScopeFieldBlock.outputEncode (entry :: entries))))
          (3 * (ScopeFieldBlock.inputEncode (entry :: entries)).length + 8) := by
        rw [hinput, houtput]
        apply evalsToInTimeMono hall
        simp only [List.length_reverse, List.length_cons, List.length_append,
          List.length_map, ScopeFieldBlock.tagSegment] at hsize' ⊢
        omega
      rw [TM2OutputsInTime, scopeFieldBlock_initList_eq_cfg]
      simp only [Option.map_some]
      rw [scopeFieldBlock_haltList_eq_cfg]
      exact hmono

/-- A genuine linear-time finite-machine witness for constructing one intact
tagged scope record, including empty and singleton scopes. -/
noncomputable def scopeFieldBlockComputableInPolyTime :
    @TM2ComputableInPolyTime (List ℕ) (List ℕ)
      ScopeFieldBlock.inputFinEncoding ScopeFieldBlock.outputFinEncoding id where
  tm := scopeFieldBlockComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl (Option Bool)
  time := 3 * Polynomial.X + 8
  outputsFun entries := by
    simpa [ScopeFieldBlock.inputFinEncoding, ScopeFieldBlock.outputFinEncoding,
      Equiv.refl, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_natCast, Polynomial.eval_X] using
        scopeFieldBlock_outputsInTime entries

/-! ## Complete domain-row occurrence expansion

The pending outer structural driver receives one explicitly counted domain at
a time. The machine below closes its inner repeated-record loop: from a
current variable index and the complete source-order domain row, it emits one
exact tagged occurrence block for every listed value. The checked input
decoder verifies the supplied row count, so the finite program traverses the
actual row fields rather than treating a binary number as a unit-cost loop
bound.
-/

namespace DomainFieldRow

/-- Every explicitly listed value paired with the current variable index. -/
def occurrences (row : ℕ × List ℕ) : List (ℕ × ℕ) :=
  row.2.map fun value => (row.1, value)

/-- Source-order row input: current index, checked value count, then values. -/
def inputEncode (row : ℕ × List ℕ) : List (Option Bool) :=
  SourceOrderRawFields.encode (row.1 :: row.2.length :: row.2)

/-- Decode a complete row and check its explicit value count. -/
def inputDecode (input : List (Option Bool)) : Option (ℕ × List ℕ) := do
  match ← SourceOrderRawFields.decode input with
  | index :: count :: values =>
      if count = values.length then some (index, values) else none
  | _ => none

@[simp]
theorem inputDecode_encode (row : ℕ × List ℕ) :
    inputDecode (inputEncode row) = some row := by
  rcases row with ⟨index, values⟩
  simp [inputDecode, inputEncode]

/-- Checked source-order encoding for one indexed domain row. -/
def inputFinEncoding : FinEncoding (ℕ × List ℕ) where
  Γ := Option Bool
  encode := inputEncode
  decode := inputDecode
  decode_encode := inputDecode_encode
  ΓFin := inferInstance

/-- Parse a sequence of complete `[3, 0, index, value]` field groups. -/
def parseOccurrenceFields : List ℕ → Option (List (ℕ × ℕ))
  | [] => some []
  | 3 :: 0 :: index :: value :: rest => do
      pure ((index, value) :: (← parseOccurrenceFields rest))
  | _ => none

/-- Exact concatenation of the local domain-occurrence block encodings. -/
def outputEncode (occurrences : List (ℕ × ℕ)) : List (Option Bool) :=
  occurrences.flatMap DomainOccurrenceFieldBlock.outputEncode

/-- Decode only complete tagged occurrence blocks. -/
def outputDecode (output : List (Option Bool)) :
    Option (List (ℕ × ℕ)) := do
  parseOccurrenceFields (← SourceOrderRawFields.decode output)

@[simp]
theorem parseOccurrenceFields_flatten
    (occurrences : List (ℕ × ℕ)) :
    parseOccurrenceFields
        (occurrences.flatMap fun occurrence =>
          [3, 0, occurrence.1, occurrence.2]) = some occurrences := by
  induction occurrences with
  | nil => rfl
  | cons occurrence occurrences ih =>
      rcases occurrence with ⟨index, value⟩
      simp [parseOccurrenceFields, ih]

@[simp]
theorem outputDecode_encode (occurrences : List (ℕ × ℕ)) :
    outputDecode (outputEncode occurrences) = some occurrences := by
  rw [outputDecode, outputEncode]
  have hfields :
      occurrences.flatMap DomainOccurrenceFieldBlock.outputEncode =
        SourceOrderRawFields.encode
          (occurrences.flatMap fun occurrence =>
            [3, 0, occurrence.1, occurrence.2]) := by
    induction occurrences with
    | nil => rfl
    | cons occurrence occurrences ih =>
        simp only [List.flatMap_cons]
        rw [ih]
        simp [DomainOccurrenceFieldBlock.outputEncode,
          SourceOrderRawFields.encode]
  rw [hfields]
  simp

/-- Checked output encoding for complete tagged domain occurrences. -/
def outputFinEncoding : FinEncoding (List (ℕ × ℕ)) where
  Γ := Option Bool
  encode := outputEncode
  decode := outputDecode
  decode_encode := outputDecode_encode
  ΓFin := inferInstance

theorem outputEncode_occurrences (index : ℕ) (values : List ℕ) :
    outputEncode (occurrences (index, values)) =
      values.flatMap fun value =>
        DomainOccurrenceFieldBlock.outputEncode (index, value) := by
  simp [outputEncode, occurrences, List.flatMap_map]

theorem inputEncode_length (index : ℕ) (values : List ℕ) :
    (inputEncode (index, values)).length =
      (encodeNat index).length + (encodeNat values.length).length +
        values.length + (values.map fun value => (encodeNat value).length).sum +
          2 := by
  simp [inputEncode, SourceOrderRawFields.encode]
  omega

theorem outputEncode_occurrences_length (index : ℕ) (values : List ℕ) :
    (outputEncode (occurrences (index, values))).length =
      values.length * ((encodeNat index).length + 6) +
        (values.map fun value => (encodeNat value).length).sum := by
  rw [outputEncode_occurrences]
  induction values with
  | nil => simp
  | cons value values ih =>
      simp [DomainOccurrenceFieldBlock.outputEncode_eq_prefix,
        DomainOccurrenceFieldBlock.inputEncode,
        DomainOccurrenceFieldBlock.headerPrefix,
        SourceOrderRawFields.encode]
      ring

end DomainFieldRow

/-- Stacks for the source, persistent index, index-copy work, reversed output,
and final output. -/
inductive DomainFieldRowStack
  | input
  | index
  | work
  | scratch
  | output
  deriving DecidableEq, Fintype

/-- Control phases for expanding one complete domain row. -/
inductive DomainFieldRowLabel
  | start
  | readIndex
  | restoreInitialIndex
  | skipCount
  | beginValue
  | copyIndex
  | copyValue
  | restoreIndexNext
  | restoreIndexFinish
  | finish
  | clearIndex
  deriving DecidableEq, Fintype

/-- The outer option distinguishes stack exhaustion from an inner field
delimiter. -/
abbrev DomainFieldRowState := Option (Option Bool)

private def domainFieldRowPopped
    (_state : DomainFieldRowState)
    (symbol : Option (Option Bool)) : DomainFieldRowState :=
  symbol

private def domainFieldRowPresent : DomainFieldRowState → Bool
  | some _ => true
  | none => false

private def domainFieldRowIsBit : DomainFieldRowState → Bool
  | some (some _) => true
  | _ => false

private def domainFieldRowHeld : DomainFieldRowState → Option Bool
  | some symbol => symbol
  | none => none

private def DomainFieldRowAlphabet (_index : DomainFieldRowStack) : Type :=
  Option Bool

/-- Finite repeated-record program for one indexed domain row. -/
def domainFieldRowProgram :
    DomainFieldRowLabel →
      TM2.Stmt DomainFieldRowAlphabet DomainFieldRowLabel DomainFieldRowState
  | .start =>
      .pop .input domainFieldRowPopped <|
        .goto (fun _ => .readIndex)
  | .readIndex =>
      .pop .input domainFieldRowPopped <|
        .branch domainFieldRowPresent
          (.branch domainFieldRowIsBit
            (.push .work domainFieldRowHeld <|
              .goto (fun _ => .readIndex))
            (.goto (fun _ => .restoreInitialIndex)))
          (.goto (fun _ => .restoreInitialIndex))
  | .restoreInitialIndex =>
      .pop .work domainFieldRowPopped <|
        .branch domainFieldRowPresent
          (.push .index domainFieldRowHeld <|
            .goto (fun _ => .restoreInitialIndex))
          (.goto (fun _ => .skipCount))
  | .skipCount =>
      .pop .input domainFieldRowPopped <|
        .branch domainFieldRowPresent
          (.branch domainFieldRowIsBit
            (.goto (fun _ => .skipCount))
            (.goto (fun _ => .beginValue)))
          (.goto (fun _ => .finish))
  | .beginValue =>
      .push .scratch (fun _ => (none : Option Bool)) <|
        .push .scratch (fun _ => some true) <|
          .push .scratch (fun _ => some true) <|
            .push .scratch (fun _ => (none : Option Bool)) <|
              .push .scratch (fun _ => (none : Option Bool)) <|
                .goto (fun _ => .copyIndex)
  | .copyIndex =>
      .pop .index domainFieldRowPopped <|
        .branch domainFieldRowPresent
          (.push .work domainFieldRowHeld <|
            .push .scratch domainFieldRowHeld <|
              .goto (fun _ => .copyIndex))
          (.push .scratch (fun _ => (none : Option Bool)) <|
            .goto (fun _ => .copyValue))
  | .copyValue =>
      .pop .input domainFieldRowPopped <|
        .branch domainFieldRowPresent
          (.branch domainFieldRowIsBit
            (.push .scratch domainFieldRowHeld <|
              .goto (fun _ => .copyValue))
            (.goto (fun _ => .restoreIndexNext)))
          (.goto (fun _ => .restoreIndexFinish))
  | .restoreIndexNext =>
      .pop .work domainFieldRowPopped <|
        .branch domainFieldRowPresent
          (.push .index domainFieldRowHeld <|
            .goto (fun _ => .restoreIndexNext))
          (.goto (fun _ => .beginValue))
  | .restoreIndexFinish =>
      .pop .work domainFieldRowPopped <|
        .branch domainFieldRowPresent
          (.push .index domainFieldRowHeld <|
            .goto (fun _ => .restoreIndexFinish))
          (.goto (fun _ => .finish))
  | .finish =>
      .pop .scratch domainFieldRowPopped <|
        .branch domainFieldRowPresent
          (.push .output domainFieldRowHeld <|
            .goto (fun _ => .finish))
          (.goto (fun _ => .clearIndex))
  | .clearIndex =>
      .pop .index domainFieldRowPopped <|
        .branch domainFieldRowPresent
          (.goto (fun _ => .clearIndex))
          .halt

/-- Concrete five-stack finite machine expanding one complete domain. -/
def domainFieldRowComputer : FinTM2 where
  K := DomainFieldRowStack
  k₀ := .input
  k₁ := .output
  Γ := DomainFieldRowAlphabet
  Λ := DomainFieldRowLabel
  main := .start
  σ := DomainFieldRowState
  initialState := none
  Γk₀Fin := show Fintype (Option Bool) from inferInstance
  m := domainFieldRowProgram

private def domainFieldRowStacks
    (input index work scratch output : List (Option Bool)) :
    (stack : DomainFieldRowStack) → List (DomainFieldRowAlphabet stack)
  | .input => input
  | .index => index
  | .work => work
  | .scratch => scratch
  | .output => output

private def domainFieldRowCfg
    (label : Option DomainFieldRowLabel) (state : DomainFieldRowState)
    (input index work scratch output : List (Option Bool)) :
    domainFieldRowComputer.Cfg where
  l := label
  var := state
  stk := domainFieldRowStacks input index work scratch output

private def domainFieldRowEvalsToInTimeOne
    {start finish : domainFieldRowComputer.Cfg}
    (hstep : domainFieldRowComputer.step start = some finish) :
    EvalsToInTime domainFieldRowComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private theorem domainFieldRow_step_start
    (input index work scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .start) state
          (none :: input) index work scratch output) =
      some (domainFieldRowCfg (some .readIndex) (some none)
        input index work scratch output) := by
  simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
    domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
    domainFieldRowPopped]
  funext stack
  cases stack <;> rfl

private theorem domainFieldRow_step_readIndex_bit
    (bit : Bool) (input index work scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .readIndex) state
          (some bit :: input) index work scratch output) =
      some (domainFieldRowCfg (some .readIndex) (some (some bit))
        input index (some bit :: work) scratch output) := by
  cases bit <;>
    simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
      domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
      domainFieldRowPopped, domainFieldRowPresent, domainFieldRowIsBit,
      domainFieldRowHeld, Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainFieldRow_step_readIndex_delimiter
    (input index work scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .readIndex) state
          (none :: input) index work scratch output) =
      some (domainFieldRowCfg (some .restoreInitialIndex) (some none)
        input index work scratch output) := by
  simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
    domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
    domainFieldRowPopped, domainFieldRowPresent, domainFieldRowIsBit]
  funext stack
  cases stack <;> rfl

private theorem domainFieldRow_step_restoreInitial_cons
    (symbol : Option Bool) (input index work scratch output :
      List (Option Bool)) (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .restoreInitialIndex) state input index
          (symbol :: work) scratch output) =
      some (domainFieldRowCfg (some .restoreInitialIndex) (some symbol)
        input (symbol :: index) work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
      domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
      domainFieldRowPopped, domainFieldRowPresent, domainFieldRowHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainFieldRow_step_restoreInitial_nil
    (input index scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .restoreInitialIndex) state input index []
          scratch output) =
      some (domainFieldRowCfg (some .skipCount) none input index []
        scratch output) := by
  simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
    domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
    domainFieldRowPopped, domainFieldRowPresent, Function.update]

private theorem domainFieldRow_step_skipCount_bit
    (bit : Bool) (input index scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .skipCount) state (some bit :: input)
          index [] scratch output) =
      some (domainFieldRowCfg (some .skipCount) (some (some bit)) input
        index [] scratch output) := by
  cases bit <;>
    simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
      domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
      domainFieldRowPopped, domainFieldRowPresent, domainFieldRowIsBit] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainFieldRow_step_skipCount_delimiter
    (input index scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .skipCount) state (none :: input)
          index [] scratch output) =
      some (domainFieldRowCfg (some .beginValue) (some none) input
        index [] scratch output) := by
  simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
    domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
    domainFieldRowPopped, domainFieldRowPresent, domainFieldRowIsBit]
  funext stack
  cases stack <;> rfl

private theorem domainFieldRow_step_skipCount_nil
    (index scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .skipCount) state [] index [] scratch output) =
      some (domainFieldRowCfg (some .finish) none [] index [] scratch output) := by
  simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
    domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
    domainFieldRowPopped, domainFieldRowPresent]

private theorem domainFieldRow_step_beginValue
    (input index scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .beginValue) state input index [] scratch
          output) =
      some (domainFieldRowCfg (some .copyIndex) state input index []
        (none :: none :: some true :: some true :: none :: scratch)
        output) := by
  simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
    domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
    Function.update]
  funext stack
  cases stack <;> rfl

private theorem domainFieldRow_step_copyIndex_cons
    (symbol : Option Bool) (input index work scratch output :
      List (Option Bool)) (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .copyIndex) state input
          (symbol :: index) work scratch output) =
      some (domainFieldRowCfg (some .copyIndex) (some symbol) input index
        (symbol :: work) (symbol :: scratch) output) := by
  rcases symbol with _ | bit <;>
    simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
      domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
      domainFieldRowPopped, domainFieldRowPresent, domainFieldRowHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainFieldRow_step_copyIndex_nil
    (input work scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .copyIndex) state input [] work scratch
          output) =
      some (domainFieldRowCfg (some .copyValue) none input [] work
        (none :: scratch) output) := by
  simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
    domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
    domainFieldRowPopped, domainFieldRowPresent, Function.update]
  funext stack
  cases stack <;> rfl

private theorem domainFieldRow_step_copyValue_bit
    (bit : Bool) (input work scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .copyValue) state (some bit :: input) []
          work scratch output) =
      some (domainFieldRowCfg (some .copyValue) (some (some bit)) input []
        work (some bit :: scratch) output) := by
  cases bit <;>
    simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
      domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
      domainFieldRowPopped, domainFieldRowPresent, domainFieldRowIsBit,
      domainFieldRowHeld, Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainFieldRow_step_copyValue_delimiter
    (input work scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .copyValue) state (none :: input) [] work
          scratch output) =
      some (domainFieldRowCfg (some .restoreIndexNext) (some none) input []
        work scratch output) := by
  simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
    domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
    domainFieldRowPopped, domainFieldRowPresent, domainFieldRowIsBit]
  funext stack
  cases stack <;> rfl

private theorem domainFieldRow_step_copyValue_nil
    (work scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .copyValue) state [] [] work scratch output) =
      some (domainFieldRowCfg (some .restoreIndexFinish) none [] [] work
        scratch output) := by
  simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
    domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
    domainFieldRowPopped, domainFieldRowPresent]

private theorem domainFieldRow_step_restoreNext_cons
    (symbol : Option Bool) (input index work scratch output :
      List (Option Bool)) (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .restoreIndexNext) state input index
          (symbol :: work) scratch output) =
      some (domainFieldRowCfg (some .restoreIndexNext) (some symbol) input
        (symbol :: index) work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
      domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
      domainFieldRowPopped, domainFieldRowPresent, domainFieldRowHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainFieldRow_step_restoreNext_nil
    (input index scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .restoreIndexNext) state input index []
          scratch output) =
      some (domainFieldRowCfg (some .beginValue) none input index [] scratch
        output) := by
  simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
    domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
    domainFieldRowPopped, domainFieldRowPresent]

private theorem domainFieldRow_step_restoreFinish_cons
    (symbol : Option Bool) (index work scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .restoreIndexFinish) state [] index
          (symbol :: work) scratch output) =
      some (domainFieldRowCfg (some .restoreIndexFinish) (some symbol) []
        (symbol :: index) work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
      domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
      domainFieldRowPopped, domainFieldRowPresent, domainFieldRowHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainFieldRow_step_restoreFinish_nil
    (index scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .restoreIndexFinish) state [] index []
          scratch output) =
      some (domainFieldRowCfg (some .finish) none [] index [] scratch
        output) := by
  simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
    domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
    domainFieldRowPopped, domainFieldRowPresent]

private theorem domainFieldRow_step_finish_cons
    (symbol : Option Bool) (scratch output index : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .finish) state [] index []
          (symbol :: scratch) output) =
      some (domainFieldRowCfg (some .finish) (some symbol) [] index [] scratch
        (symbol :: output)) := by
  rcases symbol with _ | bit <;>
    simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
      domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
      domainFieldRowPopped, domainFieldRowPresent, domainFieldRowHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainFieldRow_step_finish_nil
    (index output : List (Option Bool)) (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .finish) state [] index [] [] output) =
      some (domainFieldRowCfg (some .clearIndex) none [] index [] []
        output) := by
  simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
    domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
    domainFieldRowPopped, domainFieldRowPresent, Function.update]

private theorem domainFieldRow_step_clearIndex_cons
    (symbol : Option Bool) (index output : List (Option Bool))
    (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .clearIndex) state [] (symbol :: index) [] []
          output) =
      some (domainFieldRowCfg (some .clearIndex) (some symbol) [] index [] []
        output) := by
  rcases symbol with _ | bit <;>
    simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
      domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
      domainFieldRowPopped, domainFieldRowPresent] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainFieldRow_step_clearIndex_nil
    (output : List (Option Bool)) (state : DomainFieldRowState) :
    domainFieldRowComputer.step
        (domainFieldRowCfg (some .clearIndex) state [] [] [] [] output) =
      some (domainFieldRowCfg none none [] [] [] [] output) := by
  simp [domainFieldRowComputer, FinTM2.step, domainFieldRowCfg,
    domainFieldRowProgram, domainFieldRowStacks, DomainFieldRowAlphabet,
    domainFieldRowPopped, domainFieldRowPresent]

private def domainFieldRow_readIndex_evals
    (bits : List Bool) (input index work scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    EvalsToInTime domainFieldRowComputer.step
      (domainFieldRowCfg (some .readIndex) state
        (bits.map some ++ none :: input) index work scratch output)
      (some (domainFieldRowCfg (some .restoreInitialIndex) (some none) input
        index (bits.reverse.map some ++ work) scratch output))
      (bits.length + 1) := by
  induction bits generalizing work state with
  | nil =>
      simpa using domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_readIndex_delimiter input index work scratch
          output state)
  | cons bit bits ih =>
      let middle := domainFieldRowCfg (some .readIndex) (some (some bit))
        (bits.map some ++ none :: input) index (some bit :: work) scratch
        output
      have hone : EvalsToInTime domainFieldRowComputer.step
          (domainFieldRowCfg (some .readIndex) state
            ((bit :: bits).map some ++ none :: input) index work scratch
            output)
          (some middle) 1 :=
        domainFieldRowEvalsToInTimeOne (by
          simpa [middle] using domainFieldRow_step_readIndex_bit bit
            (bits.map some ++ none :: input) index work scratch output state)
      have hrest := ih (some bit :: work) (some (some bit))
      have hall := EvalsToInTime.trans domainFieldRowComputer.step
        1 (bits.length + 1)
        (domainFieldRowCfg (some .readIndex) state
          ((bit :: bits).map some ++ none :: input) index work scratch output)
        middle
        (some (domainFieldRowCfg (some .restoreInitialIndex) (some none)
          input index ((bit :: bits).reverse.map some ++ work) scratch output))
        hone
        (by simpa [middle, List.reverse_cons, List.map_append,
          List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainFieldRow_restoreInitial_evals
    (work input index scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    EvalsToInTime domainFieldRowComputer.step
      (domainFieldRowCfg (some .restoreInitialIndex) state input index work
        scratch output)
      (some (domainFieldRowCfg (some .skipCount) none input
        (work.reverse ++ index) [] scratch output))
      (work.length + 1) := by
  induction work generalizing index state with
  | nil =>
      simpa using domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_restoreInitial_nil input index scratch output state)
  | cons symbol work ih =>
      have hone := domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_restoreInitial_cons symbol input index work
          scratch output state)
      have hrest := ih (symbol :: index) (some symbol)
      have hall := EvalsToInTime.trans domainFieldRowComputer.step
        1 (work.length + 1)
        (domainFieldRowCfg (some .restoreInitialIndex) state input index
          (symbol :: work) scratch output)
        (domainFieldRowCfg (some .restoreInitialIndex) (some symbol) input
          (symbol :: index) work scratch output)
        (some (domainFieldRowCfg (some .skipCount) none input
          ((symbol :: work).reverse ++ index) [] scratch output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainFieldRow_skipCount_present_evals
    (bits : List Bool) (input index scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    EvalsToInTime domainFieldRowComputer.step
      (domainFieldRowCfg (some .skipCount) state
        (bits.map some ++ none :: input) index [] scratch output)
      (some (domainFieldRowCfg (some .beginValue) (some none) input index []
        scratch output))
      (bits.length + 1) := by
  induction bits generalizing state with
  | nil =>
      simpa using domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_skipCount_delimiter input index scratch output
          state)
  | cons bit bits ih =>
      have hone := domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_skipCount_bit bit
          (bits.map some ++ none :: input) index scratch output state)
      have hrest := ih (some (some bit))
      exact EvalsToInTime.trans domainFieldRowComputer.step
        1 (bits.length + 1)
        (domainFieldRowCfg (some .skipCount) state
          ((bit :: bits).map some ++ none :: input) index [] scratch output)
        (domainFieldRowCfg (some .skipCount) (some (some bit))
          (bits.map some ++ none :: input) index [] scratch output)
        (some (domainFieldRowCfg (some .beginValue) (some none) input index []
          scratch output))
        (by simpa using hone) hrest

private def domainFieldRow_skipCount_nil_evals
    (bits : List Bool) (index scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    EvalsToInTime domainFieldRowComputer.step
      (domainFieldRowCfg (some .skipCount) state (bits.map some) index []
        scratch output)
      (some (domainFieldRowCfg (some .finish) none [] index [] scratch output))
      (bits.length + 1) := by
  induction bits generalizing state with
  | nil =>
      simpa using domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_skipCount_nil index scratch output state)
  | cons bit bits ih =>
      have hone := domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_skipCount_bit bit (bits.map some) index scratch
          output state)
      have hrest := ih (some (some bit))
      exact EvalsToInTime.trans domainFieldRowComputer.step
        1 (bits.length + 1)
        (domainFieldRowCfg (some .skipCount) state
          ((bit :: bits).map some) index [] scratch output)
        (domainFieldRowCfg (some .skipCount) (some (some bit))
          (bits.map some) index [] scratch output)
        (some (domainFieldRowCfg (some .finish) none [] index [] scratch
          output))
        (by simpa using hone) hrest

private def domainFieldRow_copyIndex_evals
    (index input work scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    EvalsToInTime domainFieldRowComputer.step
      (domainFieldRowCfg (some .copyIndex) state input index work scratch output)
      (some (domainFieldRowCfg (some .copyValue) none input []
        (index.reverse ++ work) (none :: index.reverse ++ scratch) output))
      (index.length + 1) := by
  induction index generalizing work scratch state with
  | nil =>
      simpa using domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_copyIndex_nil input work scratch output state)
  | cons symbol index ih =>
      have hone := domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_copyIndex_cons symbol input index work scratch
          output state)
      have hrest := ih (symbol :: work) (symbol :: scratch) (some symbol)
      have hall := EvalsToInTime.trans domainFieldRowComputer.step
        1 (index.length + 1)
        (domainFieldRowCfg (some .copyIndex) state input (symbol :: index)
          work scratch output)
        (domainFieldRowCfg (some .copyIndex) (some symbol) input index
          (symbol :: work) (symbol :: scratch) output)
        (some (domainFieldRowCfg (some .copyValue) none input []
          ((symbol :: index).reverse ++ work)
          (none :: (symbol :: index).reverse ++ scratch) output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainFieldRow_copyValue_next_evals
    (bits : List Bool) (input work scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    EvalsToInTime domainFieldRowComputer.step
      (domainFieldRowCfg (some .copyValue) state
        (bits.map some ++ none :: input) [] work scratch output)
      (some (domainFieldRowCfg (some .restoreIndexNext) (some none) input []
        work (bits.reverse.map some ++ scratch) output))
      (bits.length + 1) := by
  induction bits generalizing scratch state with
  | nil =>
      simpa using domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_copyValue_delimiter input work scratch output
          state)
  | cons bit bits ih =>
      have hone := domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_copyValue_bit bit
          (bits.map some ++ none :: input) work scratch output state)
      have hrest := ih (some bit :: scratch) (some (some bit))
      have hall := EvalsToInTime.trans domainFieldRowComputer.step
        1 (bits.length + 1)
        (domainFieldRowCfg (some .copyValue) state
          ((bit :: bits).map some ++ none :: input) [] work scratch output)
        (domainFieldRowCfg (some .copyValue) (some (some bit))
          (bits.map some ++ none :: input) [] work (some bit :: scratch)
          output)
        (some (domainFieldRowCfg (some .restoreIndexNext) (some none) input []
          work ((bit :: bits).reverse.map some ++ scratch) output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.map_append,
          List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainFieldRow_copyValue_finish_evals
    (bits : List Bool) (work scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    EvalsToInTime domainFieldRowComputer.step
      (domainFieldRowCfg (some .copyValue) state (bits.map some) [] work
        scratch output)
      (some (domainFieldRowCfg (some .restoreIndexFinish) none [] [] work
        (bits.reverse.map some ++ scratch) output))
      (bits.length + 1) := by
  induction bits generalizing scratch state with
  | nil =>
      simpa using domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_copyValue_nil work scratch output state)
  | cons bit bits ih =>
      have hone := domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_copyValue_bit bit (bits.map some) work scratch
          output state)
      have hrest := ih (some bit :: scratch) (some (some bit))
      have hall := EvalsToInTime.trans domainFieldRowComputer.step
        1 (bits.length + 1)
        (domainFieldRowCfg (some .copyValue) state
          ((bit :: bits).map some) [] work scratch output)
        (domainFieldRowCfg (some .copyValue) (some (some bit))
          (bits.map some) [] work (some bit :: scratch) output)
        (some (domainFieldRowCfg (some .restoreIndexFinish) none [] [] work
          ((bit :: bits).reverse.map some ++ scratch) output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.map_append,
          List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainFieldRow_restoreNext_evals
    (work input index scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    EvalsToInTime domainFieldRowComputer.step
      (domainFieldRowCfg (some .restoreIndexNext) state input index work
        scratch output)
      (some (domainFieldRowCfg (some .beginValue) none input
        (work.reverse ++ index) [] scratch output))
      (work.length + 1) := by
  induction work generalizing index state with
  | nil =>
      simpa using domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_restoreNext_nil input index scratch output state)
  | cons symbol work ih =>
      have hone := domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_restoreNext_cons symbol input index work scratch
          output state)
      have hrest := ih (symbol :: index) (some symbol)
      have hall := EvalsToInTime.trans domainFieldRowComputer.step
        1 (work.length + 1)
        (domainFieldRowCfg (some .restoreIndexNext) state input index
          (symbol :: work) scratch output)
        (domainFieldRowCfg (some .restoreIndexNext) (some symbol) input
          (symbol :: index) work scratch output)
        (some (domainFieldRowCfg (some .beginValue) none input
          ((symbol :: work).reverse ++ index) [] scratch output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainFieldRow_restoreFinish_evals
    (work index scratch output : List (Option Bool))
    (state : DomainFieldRowState) :
    EvalsToInTime domainFieldRowComputer.step
      (domainFieldRowCfg (some .restoreIndexFinish) state [] index work
        scratch output)
      (some (domainFieldRowCfg (some .finish) none []
        (work.reverse ++ index) [] scratch output))
      (work.length + 1) := by
  induction work generalizing index state with
  | nil =>
      simpa using domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_restoreFinish_nil index scratch output state)
  | cons symbol work ih =>
      have hone := domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_restoreFinish_cons symbol index work scratch
          output state)
      have hrest := ih (symbol :: index) (some symbol)
      have hall := EvalsToInTime.trans domainFieldRowComputer.step
        1 (work.length + 1)
        (domainFieldRowCfg (some .restoreIndexFinish) state [] index
          (symbol :: work) scratch output)
        (domainFieldRowCfg (some .restoreIndexFinish) (some symbol) []
          (symbol :: index) work scratch output)
        (some (domainFieldRowCfg (some .finish) none []
          ((symbol :: work).reverse ++ index) [] scratch output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainFieldRow_finish_evals
    (scratch output index : List (Option Bool))
    (state : DomainFieldRowState) :
    EvalsToInTime domainFieldRowComputer.step
      (domainFieldRowCfg (some .finish) state [] index [] scratch output)
      (some (domainFieldRowCfg (some .clearIndex) none [] index [] []
        (scratch.reverse ++ output)))
      (scratch.length + 1) := by
  induction scratch generalizing output state with
  | nil =>
      simpa using domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_finish_nil index output state)
  | cons symbol scratch ih =>
      have hone := domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_finish_cons symbol scratch output index state)
      have hrest := ih (symbol :: output) (some symbol)
      have hall := EvalsToInTime.trans domainFieldRowComputer.step
        1 (scratch.length + 1)
        (domainFieldRowCfg (some .finish) state [] index []
          (symbol :: scratch) output)
        (domainFieldRowCfg (some .finish) (some symbol) [] index [] scratch
          (symbol :: output))
        (some (domainFieldRowCfg (some .clearIndex) none [] index [] []
          ((symbol :: scratch).reverse ++ output)))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainFieldRow_clearIndex_evals
    (index output : List (Option Bool)) (state : DomainFieldRowState) :
    EvalsToInTime domainFieldRowComputer.step
      (domainFieldRowCfg (some .clearIndex) state [] index [] [] output)
      (some (domainFieldRowCfg none none [] [] [] [] output))
      (index.length + 1) := by
  induction index generalizing state with
  | nil =>
      simpa using domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_clearIndex_nil output state)
  | cons symbol index ih =>
      have hone := domainFieldRowEvalsToInTimeOne
        (domainFieldRow_step_clearIndex_cons symbol index output state)
      have hrest := ih (some symbol)
      exact EvalsToInTime.trans domainFieldRowComputer.step
        1 (index.length + 1)
        (domainFieldRowCfg (some .clearIndex) state [] (symbol :: index) [] []
          output)
        (domainFieldRowCfg (some .clearIndex) (some symbol) [] index [] []
          output)
        (some (domainFieldRowCfg none none [] [] [] [] output))
        (by simpa using hone) hrest

/-- Exact work before the final output reversal. -/
def domainFieldRowValuesTime (index : ℕ) : List ℕ → ℕ
  | [] => 0
  | value :: values =>
      2 * (encodeNat index).length + (encodeNat value).length + 4 +
        domainFieldRowValuesTime index values

theorem domainFieldRowValuesTime_eq (index : ℕ) (values : List ℕ) :
    domainFieldRowValuesTime index values =
      values.length * (2 * (encodeNat index).length + 4) +
        (values.map fun value => (encodeNat value).length).sum := by
  induction values with
  | nil => simp [domainFieldRowValuesTime]
  | cons value values ih =>
      simp [domainFieldRowValuesTime, ih]
      ring

private theorem domainFieldRow_block_reverse_append
    (index value : ℕ) (scratch : List (Option Bool)) :
    (DomainOccurrenceFieldBlock.outputEncode (index, value)).reverse ++
        scratch =
      (encodeNat value).reverse.map some ++
        none :: (encodeNat index).reverse.map some ++
          none :: none :: some true :: some true :: none :: scratch := by
  rw [DomainOccurrenceFieldBlock.outputEncode_eq_prefix]
  simp [DomainOccurrenceFieldBlock.inputEncode,
    DomainOccurrenceFieldBlock.headerPrefix, SourceOrderRawFields.encode,
    List.reverse_append, List.map_reverse, List.append_assoc]

private theorem domainFieldRow_occurrences_cons_reverse_append
    (index value : ℕ) (values : List ℕ)
    (scratch : List (Option Bool)) :
    (DomainFieldRow.outputEncode
        (DomainFieldRow.occurrences (index, value :: values))).reverse ++
        scratch =
      (DomainFieldRow.outputEncode
        (DomainFieldRow.occurrences (index, values))).reverse ++
        (DomainOccurrenceFieldBlock.outputEncode (index, value)).reverse ++
          scratch := by
  simp [DomainFieldRow.outputEncode, DomainFieldRow.occurrences,
    List.reverse_append, List.append_assoc]

private def domainFieldRow_values_evals
    (index value : ℕ) (values : List ℕ)
    (scratch output : List (Option Bool)) (state : DomainFieldRowState) :
    EvalsToInTime domainFieldRowComputer.step
      (domainFieldRowCfg (some .beginValue) state
        ((encodeNat value).map some ++ SourceOrderRawFields.encode values)
        ((encodeNat index).map some) [] scratch output)
      (some (domainFieldRowCfg (some .finish) none []
        ((encodeNat index).map some) []
        ((DomainFieldRow.outputEncode
          (DomainFieldRow.occurrences (index, value :: values))).reverse ++
            scratch) output))
      (domainFieldRowValuesTime index (value :: values)) := by
  let prefixScratch : List (Option Bool) :=
    none :: none :: some true :: some true :: none :: scratch
  have hbegin := domainFieldRowEvalsToInTimeOne
    (domainFieldRow_step_beginValue
      ((encodeNat value).map some ++ SourceOrderRawFields.encode values)
      ((encodeNat index).map some) scratch output state)
  have hindex := domainFieldRow_copyIndex_evals
    ((encodeNat index).map some)
    ((encodeNat value).map some ++ SourceOrderRawFields.encode values)
    [] prefixScratch output state
  have hfirst := EvalsToInTime.trans domainFieldRowComputer.step
    1 ((encodeNat index).length + 1)
    (domainFieldRowCfg (some .beginValue) state
      ((encodeNat value).map some ++ SourceOrderRawFields.encode values)
      ((encodeNat index).map some) [] scratch output)
    (domainFieldRowCfg (some .copyIndex) state
      ((encodeNat value).map some ++ SourceOrderRawFields.encode values)
      ((encodeNat index).map some) [] prefixScratch output)
    (some (domainFieldRowCfg (some .copyValue) none
      ((encodeNat value).map some ++ SourceOrderRawFields.encode values)
      [] ((encodeNat index).reverse.map some)
      (none :: (encodeNat index).reverse.map some ++ prefixScratch) output))
    (by simpa [prefixScratch] using hbegin)
    (by simpa [prefixScratch, List.map_reverse] using hindex)
  cases values with
  | nil =>
      have hvalue := domainFieldRow_copyValue_finish_evals
        (encodeNat value) ((encodeNat index).reverse.map some)
        (none :: (encodeNat index).reverse.map some ++ prefixScratch)
        output none
      have hrestore := domainFieldRow_restoreFinish_evals
        ((encodeNat index).reverse.map some) []
        ((encodeNat value).reverse.map some ++
          none :: (encodeNat index).reverse.map some ++ prefixScratch)
        output none
      have hscratch :
          (encodeNat value).reverse.map some ++
              none :: (encodeNat index).reverse.map some ++ prefixScratch =
            (DomainOccurrenceFieldBlock.outputEncode
              (index, value)).reverse ++ scratch := by
        rw [domainFieldRow_block_reverse_append]
      have hthroughValue := EvalsToInTime.trans
        domainFieldRowComputer.step
        (1 + ((encodeNat index).length + 1))
        ((encodeNat value).length + 1)
        (domainFieldRowCfg (some .beginValue) state
          ((encodeNat value).map some)
          ((encodeNat index).map some) [] scratch output)
        (domainFieldRowCfg (some .copyValue) none
          ((encodeNat value).map some) []
          ((encodeNat index).reverse.map some)
          (none :: (encodeNat index).reverse.map some ++ prefixScratch)
          output)
        (some (domainFieldRowCfg (some .restoreIndexFinish) none [] []
          ((encodeNat index).reverse.map some)
          ((encodeNat value).reverse.map some ++
            none :: (encodeNat index).reverse.map some ++ prefixScratch)
          output))
        (by
          simpa [SourceOrderRawFields.encode, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hfirst)
        (by simpa using hvalue)
      have hall := EvalsToInTime.trans domainFieldRowComputer.step
        ((encodeNat value).length + 1 +
          (1 + ((encodeNat index).length + 1)))
        ((encodeNat index).length + 1)
        (domainFieldRowCfg (some .beginValue) state
          ((encodeNat value).map some)
          ((encodeNat index).map some) [] scratch output)
        (domainFieldRowCfg (some .restoreIndexFinish) none [] []
          ((encodeNat index).reverse.map some)
          ((encodeNat value).reverse.map some ++
            none :: (encodeNat index).reverse.map some ++ prefixScratch)
          output)
        (some (domainFieldRowCfg (some .finish) none []
          ((encodeNat index).map some) []
          ((encodeNat value).reverse.map some ++
            none :: (encodeNat index).reverse.map some ++ prefixScratch)
          output))
        (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hthroughValue)
        (by
          simpa [List.map_reverse] using hrestore)
      have htime :
          (encodeNat index).length + 1 +
              ((encodeNat value).length + 1 +
                (1 + ((encodeNat index).length + 1))) =
            domainFieldRowValuesTime index [value] := by
        simp [domainFieldRowValuesTime]
        omega
      rw [htime] at hall
      have houtputScratch :
          (DomainFieldRow.outputEncode
            (DomainFieldRow.occurrences (index, [value]))).reverse ++
              scratch =
            (encodeNat value).reverse.map some ++
              none :: (encodeNat index).reverse.map some ++ prefixScratch := by
        simpa only [DomainFieldRow.outputEncode, DomainFieldRow.occurrences,
          List.map, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.reverse_append, List.reverse_nil, List.nil_append] using
            hscratch.symm
      rw [houtputScratch]
      simpa [SourceOrderRawFields.encode] using hall
  | cons next values =>
      have hvalue := domainFieldRow_copyValue_next_evals (encodeNat value)
        ((encodeNat next).map some ++ SourceOrderRawFields.encode values)
        ((encodeNat index).reverse.map some)
        (none :: (encodeNat index).reverse.map some ++ prefixScratch)
        output none
      have hrestore := domainFieldRow_restoreNext_evals
        ((encodeNat index).reverse.map some)
        ((encodeNat next).map some ++ SourceOrderRawFields.encode values) []
        ((encodeNat value).reverse.map some ++
          none :: (encodeNat index).reverse.map some ++ prefixScratch)
        output (some none)
      have hscratch :
          (encodeNat value).reverse.map some ++
              none :: (encodeNat index).reverse.map some ++ prefixScratch =
            (DomainOccurrenceFieldBlock.outputEncode
              (index, value)).reverse ++ scratch := by
        rw [domainFieldRow_block_reverse_append]
      have hrest := domainFieldRow_values_evals index next values
        ((DomainOccurrenceFieldBlock.outputEncode (index, value)).reverse ++
          scratch) output none
      have hthroughValue := EvalsToInTime.trans
        domainFieldRowComputer.step
        (1 + ((encodeNat index).length + 1))
        ((encodeNat value).length + 1)
        (domainFieldRowCfg (some .beginValue) state
          ((encodeNat value).map some ++ none ::
            (encodeNat next).map some ++ SourceOrderRawFields.encode values)
          ((encodeNat index).map some) [] scratch output)
        (domainFieldRowCfg (some .copyValue) none
          ((encodeNat value).map some ++ none ::
            (encodeNat next).map some ++ SourceOrderRawFields.encode values)
          [] ((encodeNat index).reverse.map some)
          (none :: (encodeNat index).reverse.map some ++ prefixScratch)
          output)
        (some (domainFieldRowCfg (some .restoreIndexNext) (some none)
          ((encodeNat next).map some ++ SourceOrderRawFields.encode values)
          [] ((encodeNat index).reverse.map some)
          ((encodeNat value).reverse.map some ++
            none :: (encodeNat index).reverse.map some ++ prefixScratch)
          output))
        (by
          simpa [SourceOrderRawFields.encode, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hfirst)
        (by simpa using hvalue)
      have hthroughRestore := EvalsToInTime.trans
        domainFieldRowComputer.step
        ((encodeNat value).length + 1 +
          (1 + ((encodeNat index).length + 1)))
        ((encodeNat index).length + 1)
        (domainFieldRowCfg (some .beginValue) state
          ((encodeNat value).map some ++ none ::
            (encodeNat next).map some ++ SourceOrderRawFields.encode values)
          ((encodeNat index).map some) [] scratch output)
        (domainFieldRowCfg (some .restoreIndexNext) (some none)
          ((encodeNat next).map some ++ SourceOrderRawFields.encode values)
          [] ((encodeNat index).reverse.map some)
          ((encodeNat value).reverse.map some ++
            none :: (encodeNat index).reverse.map some ++ prefixScratch)
          output)
        (some (domainFieldRowCfg (some .beginValue) none
          ((encodeNat next).map some ++ SourceOrderRawFields.encode values)
          ((encodeNat index).map some) []
          ((encodeNat value).reverse.map some ++
            none :: (encodeNat index).reverse.map some ++ prefixScratch)
          output))
        (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hthroughValue)
        (by
          simpa [List.map_reverse] using hrestore)
      have hthroughRestore' : EvalsToInTime domainFieldRowComputer.step
          (domainFieldRowCfg (some .beginValue) state
            ((encodeNat value).map some ++ SourceOrderRawFields.encode
              (next :: values))
            ((encodeNat index).map some) [] scratch output)
          (some (domainFieldRowCfg (some .beginValue) none
            ((encodeNat next).map some ++ SourceOrderRawFields.encode values)
            ((encodeNat index).map some) []
            ((DomainOccurrenceFieldBlock.outputEncode
              (index, value)).reverse ++ scratch) output))
          ((encodeNat index).length + 1 +
            ((encodeNat value).length + 1 +
              (1 + ((encodeNat index).length + 1)))) := by
        rw [← hscratch]
        simpa [SourceOrderRawFields.encode, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hthroughRestore
      have hall := EvalsToInTime.trans domainFieldRowComputer.step
        ((encodeNat index).length + 1 +
          ((encodeNat value).length + 1 +
            (1 + ((encodeNat index).length + 1))))
        (domainFieldRowValuesTime index (next :: values))
        (domainFieldRowCfg (some .beginValue) state
          ((encodeNat value).map some ++ SourceOrderRawFields.encode
            (next :: values))
          ((encodeNat index).map some) [] scratch output)
        (domainFieldRowCfg (some .beginValue) none
          ((encodeNat next).map some ++ SourceOrderRawFields.encode values)
          ((encodeNat index).map some) []
          ((DomainOccurrenceFieldBlock.outputEncode (index, value)).reverse ++
            scratch) output)
        (some (domainFieldRowCfg (some .finish) none []
          ((encodeNat index).map some) []
          ((DomainFieldRow.outputEncode
            (DomainFieldRow.occurrences
              (index, value :: next :: values))).reverse ++ scratch)
          output))
        (by
          exact hthroughRestore')
        (by
          rw [domainFieldRow_occurrences_cons_reverse_append]
          simpa [List.append_assoc] using hrest)
      have htime :
          domainFieldRowValuesTime index (next :: values) +
              ((encodeNat index).length + 1 +
                ((encodeNat value).length + 1 +
                  (1 + ((encodeNat index).length + 1)))) =
            domainFieldRowValuesTime index (value :: next :: values) := by
        simp [domainFieldRowValuesTime]
        omega
      rw [htime] at hall
      simpa using hall

private theorem domainFieldRow_initList_eq_cfg
    (input : List (Option Bool)) :
    initList domainFieldRowComputer input =
      domainFieldRowCfg (some .start) none input [] [] [] [] := by
  unfold initList domainFieldRowCfg
  congr
  funext stack
  cases stack <;> rfl

private theorem domainFieldRow_haltList_eq_cfg
    (output : List (Option Bool)) :
    haltList domainFieldRowComputer output =
      domainFieldRowCfg none none [] [] [] [] output := by
  unfold haltList domainFieldRowCfg
  congr
  funext stack
  cases stack <;> rfl

private def domainFieldRow_run_evals (index : ℕ) (values : List ℕ) :
    EvalsToInTime domainFieldRowComputer.step
      (domainFieldRowCfg (some .start) none
        (DomainFieldRow.inputEncode (index, values)) [] [] [] [])
      (some (domainFieldRowCfg none none [] [] [] []
        (DomainFieldRow.outputEncode
          (DomainFieldRow.occurrences (index, values)))))
      (3 * (encodeNat index).length + (encodeNat values.length).length +
        domainFieldRowValuesTime index values +
        (DomainFieldRow.outputEncode
          (DomainFieldRow.occurrences (index, values))).length + 6) := by
  let indexBits := encodeNat index
  let countBits := encodeNat values.length
  have hinput : DomainFieldRow.inputEncode (index, values) =
      none :: indexBits.map some ++ none :: countBits.map some ++
        SourceOrderRawFields.encode values := by
    simp [DomainFieldRow.inputEncode, SourceOrderRawFields.encode,
      indexBits, countBits, List.append_assoc]
  have hstart := domainFieldRowEvalsToInTimeOne
    (domainFieldRow_step_start
      (indexBits.map some ++ none :: countBits.map some ++
        SourceOrderRawFields.encode values) [] [] [] [] none)
  have hread := domainFieldRow_readIndex_evals indexBits
    (countBits.map some ++ SourceOrderRawFields.encode values) [] [] [] []
    (some none)
  have hfirst := EvalsToInTime.trans domainFieldRowComputer.step
    1 (indexBits.length + 1)
    (domainFieldRowCfg (some .start) none
      (none :: indexBits.map some ++ none :: countBits.map some ++
        SourceOrderRawFields.encode values) [] [] [] [])
    (domainFieldRowCfg (some .readIndex) (some none)
      (indexBits.map some ++ none :: countBits.map some ++
        SourceOrderRawFields.encode values) [] [] [] [])
    (some (domainFieldRowCfg (some .restoreInitialIndex) (some none)
      (countBits.map some ++ SourceOrderRawFields.encode values) []
      (indexBits.reverse.map some) [] []))
    (by simpa using hstart)
    (by simpa [List.append_assoc] using hread)
  have hrestore := domainFieldRow_restoreInitial_evals
    (indexBits.reverse.map some)
    (countBits.map some ++ SourceOrderRawFields.encode values) [] [] []
    (some none)
  have hheader := EvalsToInTime.trans domainFieldRowComputer.step
    (indexBits.length + 2) (indexBits.length + 1)
    (domainFieldRowCfg (some .start) none
      (none :: indexBits.map some ++ none :: countBits.map some ++
        SourceOrderRawFields.encode values) [] [] [] [])
    (domainFieldRowCfg (some .restoreInitialIndex) (some none)
      (countBits.map some ++ SourceOrderRawFields.encode values) []
      (indexBits.reverse.map some) [] [])
    (some (domainFieldRowCfg (some .skipCount) none
      (countBits.map some ++ SourceOrderRawFields.encode values)
      (indexBits.map some) [] [] []))
    (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst)
    (by simpa [List.map_reverse] using hrestore)
  rw [show indexBits.length + 1 + (indexBits.length + 2) =
    2 * indexBits.length + 3 by omega] at hheader
  cases values with
  | nil =>
      have hcount := domainFieldRow_skipCount_nil_evals countBits
        (indexBits.map some) [] [] none
      have hthroughCount := EvalsToInTime.trans domainFieldRowComputer.step
        (2 * indexBits.length + 3) (countBits.length + 1)
        (domainFieldRowCfg (some .start) none
          (none :: indexBits.map some ++ none :: countBits.map some) [] [] []
          [])
        (domainFieldRowCfg (some .skipCount) none (countBits.map some)
          (indexBits.map some) [] [] [])
        (some (domainFieldRowCfg (some .finish) none []
          (indexBits.map some) [] [] []))
        (by
          simpa [SourceOrderRawFields.encode, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hheader)
        (by simpa using hcount)
      rw [show countBits.length + 1 + (2 * indexBits.length + 3) =
        2 * indexBits.length + countBits.length + 4 by omega] at hthroughCount
      have hfinish := domainFieldRow_finish_evals [] []
        (indexBits.map some) none
      have hthroughFinish := EvalsToInTime.trans domainFieldRowComputer.step
        (2 * indexBits.length + countBits.length + 4) 1
        (domainFieldRowCfg (some .start) none
          (none :: indexBits.map some ++ none :: countBits.map some) [] [] []
          [])
        (domainFieldRowCfg (some .finish) none [] (indexBits.map some) [] []
          [])
        (some (domainFieldRowCfg (some .clearIndex) none []
          (indexBits.map some) [] [] []))
        (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hthroughCount)
        (by simpa using hfinish)
      rw [show 1 + (2 * indexBits.length + countBits.length + 4) =
        2 * indexBits.length + countBits.length + 5 by omega] at hthroughFinish
      have hclear := domainFieldRow_clearIndex_evals
        (indexBits.map some) [] none
      have hall := EvalsToInTime.trans domainFieldRowComputer.step
        (2 * indexBits.length + countBits.length + 5)
        (indexBits.length + 1)
        (domainFieldRowCfg (some .start) none
          (none :: indexBits.map some ++ none :: countBits.map some) [] [] []
          [])
        (domainFieldRowCfg (some .clearIndex) none [] (indexBits.map some) []
          [] [])
        (some (domainFieldRowCfg none none [] [] [] [] []))
        (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hthroughFinish)
        (by simpa using hclear)
      rw [show indexBits.length + 1 +
          (2 * indexBits.length + countBits.length + 5) =
        3 * indexBits.length + countBits.length + 6 by omega] at hall
      rw [hinput]
      simpa [indexBits, countBits, DomainFieldRow.occurrences,
        DomainFieldRow.outputEncode, domainFieldRowValuesTime,
        SourceOrderRawFields.encode, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall
  | cons value values =>
      have hcount := domainFieldRow_skipCount_present_evals countBits
        ((encodeNat value).map some ++ SourceOrderRawFields.encode values)
        (indexBits.map some) [] [] none
      have hthroughCount := EvalsToInTime.trans domainFieldRowComputer.step
        (2 * indexBits.length + 3) (countBits.length + 1)
        (domainFieldRowCfg (some .start) none
          (none :: indexBits.map some ++ none :: countBits.map some ++
            SourceOrderRawFields.encode (value :: values)) [] [] [] [])
        (domainFieldRowCfg (some .skipCount) none
          (countBits.map some ++ SourceOrderRawFields.encode (value :: values))
          (indexBits.map some) [] [] [])
        (some (domainFieldRowCfg (some .beginValue) (some none)
          ((encodeNat value).map some ++ SourceOrderRawFields.encode values)
          (indexBits.map some) [] [] []))
        (by
          simpa [SourceOrderRawFields.encode, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hheader)
        (by simpa using hcount)
      rw [show countBits.length + 1 + (2 * indexBits.length + 3) =
        2 * indexBits.length + countBits.length + 4 by omega] at hthroughCount
      have hvalues := domainFieldRow_values_evals index value values [] []
        (some none)
      have hthroughValues := EvalsToInTime.trans domainFieldRowComputer.step
        (2 * indexBits.length + countBits.length + 4)
        (domainFieldRowValuesTime index (value :: values))
        (domainFieldRowCfg (some .start) none
          (none :: indexBits.map some ++ none :: countBits.map some ++
            SourceOrderRawFields.encode (value :: values)) [] [] [] [])
        (domainFieldRowCfg (some .beginValue) (some none)
          ((encodeNat value).map some ++ SourceOrderRawFields.encode values)
          (indexBits.map some) [] [] [])
        (some (domainFieldRowCfg (some .finish) none []
          (indexBits.map some) []
          ((DomainFieldRow.outputEncode
            (DomainFieldRow.occurrences (index, value :: values))).reverse)
          []))
        (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hthroughCount)
        (by simpa [indexBits] using hvalues)
      let outputBits := DomainFieldRow.outputEncode
        (DomainFieldRow.occurrences (index, value :: values))
      have hfinish := domainFieldRow_finish_evals outputBits.reverse []
        (indexBits.map some) none
      have hthroughFinish := EvalsToInTime.trans domainFieldRowComputer.step
        (2 * indexBits.length + countBits.length + 4 +
          domainFieldRowValuesTime index (value :: values))
        (outputBits.length + 1)
        (domainFieldRowCfg (some .start) none
          (none :: indexBits.map some ++ none :: countBits.map some ++
            SourceOrderRawFields.encode (value :: values)) [] [] [] [])
        (domainFieldRowCfg (some .finish) none [] (indexBits.map some) []
          outputBits.reverse [])
        (some (domainFieldRowCfg (some .clearIndex) none []
          (indexBits.map some) [] [] outputBits))
        (by
          simpa [outputBits, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hthroughValues)
        (by simpa [List.reverse_reverse] using hfinish)
      rw [show outputBits.length + 1 +
          (2 * indexBits.length + countBits.length + 4 +
            domainFieldRowValuesTime index (value :: values)) =
        2 * indexBits.length + countBits.length + 5 +
          domainFieldRowValuesTime index (value :: values) +
            outputBits.length by omega] at hthroughFinish
      have hclear := domainFieldRow_clearIndex_evals
        (indexBits.map some) outputBits none
      have hall := EvalsToInTime.trans domainFieldRowComputer.step
        (2 * indexBits.length + countBits.length + 5 +
          domainFieldRowValuesTime index (value :: values) + outputBits.length)
        (indexBits.length + 1)
        (domainFieldRowCfg (some .start) none
          (none :: indexBits.map some ++ none :: countBits.map some ++
            SourceOrderRawFields.encode (value :: values)) [] [] [] [])
        (domainFieldRowCfg (some .clearIndex) none [] (indexBits.map some) []
          [] outputBits)
        (some (domainFieldRowCfg none none [] [] [] [] outputBits))
        (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hthroughFinish)
        (by simpa using hclear)
      rw [show indexBits.length + 1 +
          (2 * indexBits.length + countBits.length + 5 +
            domainFieldRowValuesTime index (value :: values) +
              outputBits.length) =
        3 * indexBits.length + countBits.length +
          domainFieldRowValuesTime index (value :: values) +
            outputBits.length + 6 by omega] at hall
      rw [hinput]
      simpa [indexBits, countBits, outputBits, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall

/-- One complete counted domain row expands to all of its indexed occurrence
blocks in quadratic time in the checked bit-level row encoding. -/
def domainFieldRow_outputsInTime (row : ℕ × List ℕ) :
    TM2OutputsInTime domainFieldRowComputer
      (DomainFieldRow.inputEncode row)
      (some (DomainFieldRow.outputEncode (DomainFieldRow.occurrences row)))
      (20 * ((DomainFieldRow.inputEncode row).length + 1) ^ 2) := by
  rcases row with ⟨index, values⟩
  have hrun := domainFieldRow_run_evals index values
  have hn : (encodeNat index).length ≤
      (encodeNat index).length + (encodeNat values.length).length +
        values.length +
          (values.map fun value => (encodeNat value).length).sum + 2 := by
    omega
  have hm : values.length ≤
      (encodeNat index).length + (encodeNat values.length).length +
        values.length +
          (values.map fun value => (encodeNat value).length).sum + 2 := by
    omega
  have hproduct := Nat.mul_le_mul hm hn
  have hmono : EvalsToInTime domainFieldRowComputer.step
      (domainFieldRowCfg (some .start) none
        (DomainFieldRow.inputEncode (index, values)) [] [] [] [])
      (some (domainFieldRowCfg none none [] [] [] []
        (DomainFieldRow.outputEncode
          (DomainFieldRow.occurrences (index, values)))))
      (20 * ((DomainFieldRow.inputEncode (index, values)).length + 1) ^ 2) :=
    evalsToInTimeMono hrun (by
      rw [DomainFieldRow.inputEncode_length,
        DomainFieldRow.outputEncode_occurrences_length,
        domainFieldRowValuesTime_eq]
      nlinarith)
  rw [TM2OutputsInTime, domainFieldRow_initList_eq_cfg]
  simp only [Option.map_some]
  rw [domainFieldRow_haltList_eq_cfg]
  exact hmono

/-- A finite-machine polynomial-time witness for expanding every explicitly
listed value in one counted domain while preserving its current index. -/
noncomputable def domainFieldRowComputableInPolyTime :
    @TM2ComputableInPolyTime (ℕ × List ℕ) (List (ℕ × ℕ))
      DomainFieldRow.inputFinEncoding DomainFieldRow.outputFinEncoding
      DomainFieldRow.occurrences where
  tm := domainFieldRowComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl (Option Bool)
  time := 20 * (Polynomial.X + 1) ^ 2
  outputsFun row := by
    simpa [DomainFieldRow.inputFinEncoding,
      DomainFieldRow.outputFinEncoding, Equiv.refl, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_natCast,
      Polynomial.eval_one, Polynomial.eval_X] using
        domainFieldRow_outputsInTime row

/-! ## Complete domain-section contract

The next outer finite driver must traverse all counted domain rows, not just
one row in isolation.  This section fixes a checked interface for that pass.
The input is exactly the source-order raw encoding of the nested domain list:
its first field is the number of domains and each row begins with its value
count.  The decoder checks both levels of counts and rejects leftover fields.

`indexedRowsFrom` makes the required index advance explicit, including across
empty domains.  The output lemmas then identify the concatenation of the
already checked row outputs with `StructuralFieldStream.domainFieldsFrom`, the
domain portion of the eventual structural compiler output.  A future machine
for this interface therefore has a complete typed contract rather than an
informal repeated-row invariant.
-/

namespace DomainFieldSection

export LeanNPHardness.CountedNatRows
  (rowFields inputFields inputEncode inputEncode_eq_sourceOrderRawNatLists parseRows
   parseRows_rowFields inputDecode inputDecode_encode inputFinEncoding rowPayloadEncode
   parseRowPayload parseRowPayload_rowFields rowFields_injective rowPayloadDecode rowPayloadDecode_encode
   rowPayloadEncode_injective rowPayloadFinEncoding rowPayloadEncode_length_le_inputEncode_length)

/-- Compatibility with the CSP structural field specification. -/
theorem inputFields_eq_flatten (domains : List (List ℕ)) :
    inputFields domains = StructuralFieldStream.flatten domains := rfl

/-- Attach consecutive variable indices to every domain row. -/
def indexedRowsFrom : ℕ → List (List ℕ) → List (ℕ × List ℕ)
  | _, [] => []
  | index, domain :: domains =>
      (index, domain) :: indexedRowsFrom (index + 1) domains

@[simp]
theorem indexedRowsFrom_length (start : ℕ) (domains : List (List ℕ)) :
    (indexedRowsFrom start domains).length = domains.length := by
  induction domains generalizing start with
  | nil => rfl
  | cons domain domains ih => simp [indexedRowsFrom, ih]

/-- Expanding the indexed rows gives exactly the structural view's occurrence
stream.  Empty rows still advance the following row's index. -/
theorem occurrences_indexedRowsFrom (start : ℕ)
    (domains : List (List ℕ)) :
    (indexedRowsFrom start domains).flatMap DomainFieldRow.occurrences =
      RuntimeStructuralView.indexedDomainOccurrencesFrom start domains := by
  induction domains generalizing start with
  | nil => rfl
  | cons domain domains ih =>
      simp [indexedRowsFrom, DomainFieldRow.occurrences,
        RuntimeStructuralView.indexedDomainOccurrencesFrom, ih]

/-- Concatenation of the checked per-row inputs after indices are attached. -/
def rowInputEncode (domains : List (List ℕ)) : List (Option Bool) :=
  (indexedRowsFrom 0 domains).flatMap DomainFieldRow.inputEncode

/-- Exact occurrence-block output required from the domain-section pass. -/
def outputEncode (domains : List (List ℕ)) : List (Option Bool) :=
  DomainFieldRow.outputEncode
    (RuntimeStructuralView.indexedDomainOccurrences domains)

/-- The domain-section output is the concatenation of all checked local row
outputs in source order. -/
theorem outputEncode_eq_row_outputs (domains : List (List ℕ)) :
    outputEncode domains =
      (indexedRowsFrom 0 domains).flatMap fun row =>
        DomainFieldRow.outputEncode (DomainFieldRow.occurrences row) := by
  rw [outputEncode, RuntimeStructuralView.indexedDomainOccurrences,
    ← occurrences_indexedRowsFrom]
  simp [DomainFieldRow.outputEncode, List.flatMap_assoc]

private theorem outputEncodeFrom_eq_structuralFields (start : ℕ)
    (domains : List (List ℕ)) :
    DomainFieldRow.outputEncode
        (RuntimeStructuralView.indexedDomainOccurrencesFrom start domains) =
      SourceOrderRawFields.encode
        (StructuralFieldStream.domainFieldsFrom start domains) := by
  induction domains generalizing start with
  | nil => rfl
  | cons domain domains ih =>
      simp only [RuntimeStructuralView.indexedDomainOccurrencesFrom,
        StructuralFieldStream.domainFieldsFrom,
        DomainFieldRow.outputEncode, List.flatMap_append]
      have ih' := ih (start + 1)
      rw [DomainFieldRow.outputEncode, SourceOrderRawFields.encode] at ih'
      rw [SourceOrderRawFields.encode, List.flatMap_append, ih']
      congr 1
      induction domain with
      | nil => rfl
      | cons value values ihValues =>
          simp [DomainOccurrenceFieldBlock.outputEncode,
            SourceOrderRawFields.encode, ihValues]

/-- The section output is exactly the domain portion of the complete
`StructuralFieldStream` target. -/
theorem outputEncode_eq_structuralFields (domains : List (List ℕ)) :
    outputEncode domains =
      SourceOrderRawFields.encode
        (StructuralFieldStream.domainFieldsFrom 0 domains) := by
  exact outputEncodeFrom_eq_structuralFields 0 domains

end DomainFieldSection

noncomputable abbrev DomainRowPayloadStack := @LeanNPHardness.MachinePrimitives.CountedRowPayloadStack

noncomputable abbrev DomainRowPayloadLabel := @LeanNPHardness.MachinePrimitives.CountedRowPayloadLabel

noncomputable abbrev DomainRowPayloadState := @LeanNPHardness.MachinePrimitives.CountedRowPayloadState

noncomputable abbrev domainRowPayloadProgram := @LeanNPHardness.MachinePrimitives.countedRowPayloadProgram

noncomputable abbrev domainRowPayloadComputer := @LeanNPHardness.MachinePrimitives.countedRowPayloadComputer

noncomputable abbrev domainRowPayload_outputsInTime := @LeanNPHardness.MachinePrimitives.countedRowPayload_outputsInTime

noncomputable abbrev domainRowPayloadComputableInPolyTime := @LeanNPHardness.MachinePrimitives.countedRowPayloadComputableInPolyTime

noncomputable abbrev domainRowPayloadStructuredComputableInPolyTime := @LeanNPHardness.MachinePrimitives.countedRowPayloadStructuredComputableInPolyTime

export LeanNPHardness.MachinePrimitives
  (intervalFrom bertrandCandidates intervalFrom_length bertrandCandidates_length mem_intervalFrom_iff
   mem_bertrandCandidates_iff unaryEncodeNat_length EnumerateStack EnumerateLabel EnumerateState
   bertrandCandidateProgram bertrandCandidateComputer bertrandCandidate_outputsInTime bertrandCandidatesComputableInPolyTime UnaryBertrandStack
   UnaryBertrandLabel UnaryBertrandState unaryBertrandCandidateProgram unaryBertrandCandidateComputer unaryBertrandStackContents
   unaryBertrandCfg unaryEncodeNat_eq_replicate_true unaryBertrand_initList_eq_cfg unaryBertrand_haltList_eq_cfg unaryBertrandCandidate_outputsInTime
   unaryBertrandCandidatesComputableInPolyTime unaryBertrandCandidateStream_length_le)

namespace UnaryNatPair
export LeanNPHardness.MachinePrimitives.UnaryNatPair
  (encode decodeAux decode decode_encode finEncoding
   encode_length)
end UnaryNatPair
export LeanNPHardness.MachinePrimitives
  (trialDivisors trialDivisors_length mem_trialDivisors_iff trialPrime trialPrime_eq_true_iff
   trialDivisionPairs trialDivisionPairs_length mem_trialDivisionPairs_iff unaryPair_length_le_two_mul_of_mem_trialDivisionPairs trialDivisionInputSize
   trialDivisionInputSize_le bertrandPrimeCandidates pairwise_lt_intervalFrom pairwise_lt_bertrandPrimeCandidates mem_bertrandPrimeCandidates_iff
   selectPrimeAbove_mem_bertrandPrimeCandidates bertrandPrimeCandidates_ne_nil firstBertrandPrime firstBertrandPrime_zero firstBertrandPrime_mem
   firstBertrandPrime_eq_selectPrimeAbove firstBertrandPrime_prime lt_firstBertrandPrime firstBertrandPrime_le_two_mul firstBertrandPrime_lt_two_mul
   firstBertrandPrime_one DvdStack DvdLabel DvdState dvdInitialState
   DvdAlphabet unaryDvdProgram unaryDvdComputer dvdStackContents dvdCfg
   unaryDvd_evals_with_output unaryDvd_outputsInTime unaryDvdComputableInPolyTime TrialPairStack TrialPairLabel
   TrialPairState trialDivisionPairProgram trialDivisionPairComputer trialPairStackContents trialPairCfg
   trialPairsFrom trialPairsFrom_eq_range trialPairsFrom_sub_two unaryEncodeNat_reverse trialPair_initList_eq_cfg
   trialPair_haltList_eq_cfg trialDivisionPairs_outputsInTime trialDivisionPairsComputableInPolyTime)
namespace RawUnaryPairList
export LeanNPHardness.MachinePrimitives.RawUnaryPairList
  (encode parse_encode decodeFields decodeFields_map_encode decode
   decode_encode finEncoding)
end RawUnaryPairList

namespace RawBoolList
export LeanNPHardness.MachinePrimitives.RawBoolList
  (finEncoding encode_eq)
end RawBoolList
export LeanNPHardness.MachinePrimitives
  (allFalseFrom allFalse allFalseFrom_false AllFalseStack AllFalseLabel
   AllFalseState allFalseProgram allFalseComputer allFalse_outputsInTime allFalseComputableInPolyTime)

export LeanNPHardness.MachinePrimitives
  (pairDivisionResults PairDvdStack PairDvdLabel PairDvdState pairDvdProgram
   pairDvdComputer trialDivisionPairStream_length_le pairDvd_outputsInTime pairDivisionResultsComputableInPolyTime trialDivisionResults
   pairDivisionResults_trialDivisionPairs allFalse_trialDivisionResults trialPrime_eq_lowerBound_and_allFalse trialPrime_eq_allFalse_trialDivisionResults allFalse_trialDivisionResults_eq_true_iff
   allFalseDivisibilityResults allFalseDivisibilityResults_trialDivisionPairs_eq_true_iff PairAllFalseStack PairAllFalseLabel PairAllFalseState
   pairAllFalseProgram pairAllFalseComputer pairAllFalse_outputsInTime allFalseDivisibilityResultsComputableInPolyTime unaryCandidatePrimeComputer
   unaryCandidatePrime unaryCandidatePrime_eq_true_iff two_le_of_mem_bertrandCandidates unaryCandidatePrime_eq_trialPrime_of_mem_bertrandCandidates filter_unaryCandidatePrime_bertrandCandidates
   unaryCandidatePrime_outputsInTime unaryCandidatePrimeComputableInPolyTime firstUnaryCandidatePrime? selectUnaryCandidatePrime firstUnaryCandidatePrime?_eq_head?_filter
   firstUnaryCandidatePrime?_mem head?_getD_eq_head selectUnaryCandidatePrime_bertrandCandidates PrimeSelectorOuterStack PrimeSelectorStack
   PrimeSelectorLabel PrimeSelectorState primeSelectorProgram primeSelectorComputer primeSelector_outputsInTime
   primeSelectorComputableInPolyTime primeSelector_selects_firstBertrandPrime selectedPrimeComputer selectedPrime_outputsInTime selectedPrimeComputableInPolyTime)
namespace RawUnaryPairList
export LeanNPHardness.MachinePrimitives.RawUnaryPairList
  (encode_cons encode_length)
end RawUnaryPairList


/-! ## Runtime-system prime selection

The generic checked sequential-composition API now connects occurrence-count
production from the compiler input to the existing selected-prime machine.
-/

private noncomputable def runtimeDomainEntryPrimeComposition :
    @TM2ComputableInPolyTime RuntimeSystem ℕ
      RuntimeCompilerInput.finEncoding unaryFinEncodingNat
      (selectPrimeAbove ∘ RuntimeSystem.domainEntryCount) :=
  compositionComputableInPolyTime
    RuntimeCompilerInput.finEncoding unaryFinEncodingNat unaryFinEncodingNat
    RuntimeSystem.domainEntryCount selectPrimeAbove
    domainEntryCountComputableInPolyTime selectedPrimeComputableInPolyTime

/-- A genuine polynomial-time machine from the checked compiler input to the
same prime used by `compileUsingDomainEntryBound`. -/
noncomputable def runtimeDomainEntryPrimeComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem ℕ
      RuntimeCompilerInput.finEncoding unaryFinEncodingNat
      RuntimeSystem.domainEntryPrime := by
  let composed := runtimeDomainEntryPrimeComposition
  exact { composed with
    outputsFun := fun C => by
      simpa [Function.comp_def, RuntimeSystem.domainEntryPrime] using
        composed.outputsFun C }







#print axioms FramedNat.decode_encode
#print axioms frame_outputsInTime
#print axioms framedNatComputableInPolyTime
#print axioms RawNatList.decode_encode
#print axioms listFrame_outputsInTime
#print axioms RuntimeStructuralView.rawFinEncoding
#print axioms nestedListFrame_outputsInTime
#print axioms runtimeStructuralViewFramingComputableInPolyTime
#print axioms framedNatListComputableInPolyTime
#print axioms RawNatLists.decode_encode
#print axioms unframe_outputsInTime
#print axioms unframedNatListsComputableInPolyTime
#print axioms domainEntryCount_outputsInTime
#print axioms domainEntryCountComputableInPolyTime
#print axioms compilerPayload_outputsInTime
#print axioms compilerPayloadComputableInPolyTime
#print axioms runtimeSystemUnframedComputableInPolyTime
#print axioms runtimeCompilerRawFieldsComputableInPolyTime
#print axioms SourceOrderRawNatLists.decode_encode
#print axioms SourceOrderRawNatLists.encode_eq_payloads
#print axioms sourceOrderRawFields_outputsInTime
#print axioms sourceOrderRawFieldsComputableInPolyTime
#print axioms runtimeCompilerSourceOrderFieldsComputableInPolyTime
#print axioms StructuralFieldStream.ofRuntimeSystem_eq_flatten
#print axioms StructuralFieldStream.encode_eq_sourceOrderRawNatLists
#print axioms StructuralFieldStream.encode_reverse_eq_raw
#print axioms StructuralFieldStream.raw_decode_encode_reverse
#print axioms SourceOrderRawFields.decode_encode
#print axioms DomainOccurrenceFieldBlock.fields_eq_record
#print axioms domainOccurrenceBlock_outputsInTime
#print axioms domainOccurrenceBlockComputableInPolyTime
#print axioms runtimeDomainEntryPrimeComputableInPolyTime
#print axioms binarySuccBits_encodeNat
#print axioms binarySucc_outputsInTime
#print axioms binarySuccComputableInPolyTime
#print axioms ScopeFieldBlock.fields_eq_record
#print axioms scopeFieldBlock_outputsInTime
#print axioms scopeFieldBlockComputableInPolyTime
#print axioms DomainFieldRow.outputDecode_encode
#print axioms domainFieldRow_outputsInTime
#print axioms domainFieldRowComputableInPolyTime
#print axioms DomainFieldSection.inputFinEncoding
#print axioms DomainFieldSection.inputEncode_eq_sourceOrderRawNatLists
#print axioms DomainFieldSection.parseRowPayload_rowFields
#print axioms DomainFieldSection.rowFields_injective
#print axioms DomainFieldSection.rowPayloadFinEncoding
#print axioms DomainFieldSection.rowPayloadEncode_injective
#print axioms DomainFieldSection.rowPayloadEncode_length_le_inputEncode_length
#print axioms DomainFieldSection.occurrences_indexedRowsFrom
#print axioms DomainFieldSection.outputEncode_eq_row_outputs
#print axioms DomainFieldSection.outputEncode_eq_structuralFields
#print axioms domainRowPayload_outputsInTime
#print axioms domainRowPayloadComputableInPolyTime
#print axioms domainRowPayloadStructuredComputableInPolyTime
#print axioms binaryPredBits_encodeNat
#print axioms binaryPred_outputsInTime
#print axioms binaryPredComputableInPolyTime
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
