import PhdThesisLean.AllDifferentCSP
import Mathlib.Computability.Encoding

namespace PhdThesisLean.AllDifferentCSPEncoding

open Computability
open PhdThesisLean.AllDifferentCSP

/-!
# Binary encodings for explicit all-different CSP compilation

This module supplies runtime-sized, nondependent input and output syntax for
the all-different compiler and checked `FinEncoding`s over the binary alphabet
`Bool`.

Natural numbers use mathlib's standard least-significant-bit-first
`Computability.encodeNat`. Each bit string is made self-delimiting by prefixing
its length in unary. Lists carry a self-delimiting binary length followed by
their elements. Consequently, nested lists need no unbounded alphabet or
implicit delimiter convention.

These encodings establish the finite binary representation layer. Exact
encoded-length formulae are kept separate from the later polynomial bound and
machine-running-time proof.
-/

namespace BinaryNatLists

/-- A self-delimiting binary frame: unary payload length, a zero separator,
then the payload bits. -/
def frame (bits : List Bool) : List Bool :=
  List.replicate bits.length true ++ false :: bits

/-- A self-delimiting form of mathlib's standard binary natural encoding. -/
def encodeNat (n : ℕ) : List Bool :=
  frame (Computability.encodeNat n)

/-- Read a unary count terminated by `false`. -/
def readUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, tail) ← readUnary rest
      pure (n + 1, tail)

/-- Read exactly `count` bits, returning the unconsumed suffix. -/
def readBits : ℕ → List Bool → Option (List Bool × List Bool)
  | 0, input => some ([], input)
  | _ + 1, [] => none
  | count + 1, bit :: input => do
      let (bits, rest) ← readBits count input
      pure (bit :: bits, rest)

/-- Decode one framed natural and return the unconsumed suffix. -/
def decodeNatPrefix (input : List Bool) : Option (ℕ × List Bool) := do
  let (count, payload) ← readUnary input
  let (bits, rest) ← readBits count payload
  pure (Computability.decodeNat bits, rest)

@[simp]
theorem readUnary_replicate (count : ℕ) (rest : List Bool) :
    readUnary (List.replicate count true ++ false :: rest) =
      some (count, rest) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [List.replicate_succ, readUnary, ih]

@[simp]
theorem readBits_append (bits rest : List Bool) :
    readBits bits.length (bits ++ rest) = some (bits, rest) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simp [readBits, ih]

@[simp]
theorem decodeNatPrefix_encodeNat_append (n : ℕ) (rest : List Bool) :
    decodeNatPrefix (encodeNat n ++ rest) = some (n, rest) := by
  simp [decodeNatPrefix, encodeNat, frame, List.append_assoc]

/-- Decode exactly `count` framed naturals. -/
def decodeNats : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (n, rest) ← decodeNatPrefix input
      let (ns, tail) ← decodeNats count rest
      pure (n :: ns, tail)

/-- Encode a list of naturals as its binary length and framed elements. -/
def encodeNatList (xs : List ℕ) : List Bool :=
  encodeNat xs.length ++ xs.flatMap encodeNat

/-- Decode a length-prefixed list of naturals. -/
def decodeNatListPrefix (input : List Bool) :
    Option (List ℕ × List Bool) := do
  let (count, rest) ← decodeNatPrefix input
  decodeNats count rest

@[simp]
theorem decodeNats_flatMap_append (xs : List ℕ) (rest : List Bool) :
    decodeNats xs.length (xs.flatMap encodeNat ++ rest) =
      some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [decodeNats, List.append_assoc, ih]

@[simp]
theorem decodeNatListPrefix_encode_append
    (xs : List ℕ) (rest : List Bool) :
    decodeNatListPrefix (encodeNatList xs ++ rest) = some (xs, rest) := by
  simp [decodeNatListPrefix, encodeNatList, List.append_assoc]

/-- Decode exactly `count` binary natural-number lists. -/
def decodeLists : ℕ → List Bool → Option (List (List ℕ) × List Bool)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (xs, rest) ← decodeNatListPrefix input
      let (xss, tail) ← decodeLists count rest
      pure (xs :: xss, tail)

/-- Encode nested natural-number lists using binary length prefixes. -/
def encode (xss : List (List ℕ)) : List Bool :=
  encodeNat xss.length ++ xss.flatMap encodeNatList

/-- Decode a complete nested-list binary string, rejecting trailing bits. -/
def decode (input : List Bool) : Option (List (List ℕ)) := do
  let (count, rest) ← decodeNatPrefix input
  let (xss, tail) ← decodeLists count rest
  if tail = [] then some xss else none

@[simp]
theorem decodeLists_flatMap_append
    (xss : List (List ℕ)) (rest : List Bool) :
    decodeLists xss.length (xss.flatMap encodeNatList ++ rest) =
      some (xss, rest) := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
      simp [decodeLists, List.append_assoc, ih]

@[simp]
theorem decode_encode (xss : List (List ℕ)) :
    decode (encode xss) = some xss := by
  have hdecode :
      decodeLists xss.length (xss.flatMap encodeNatList) =
        some (xss, []) := by
    simpa using decodeLists_flatMap_append xss []
  simp [decode, encode, hdecode]

/-- A checked binary `FinEncoding` for nested natural-number lists. -/
def finEncoding : FinEncoding (List (List ℕ)) where
  Γ := Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := Bool.fintype

/-- Number of bits used by one framed natural. -/
def natWireSize (n : ℕ) : ℕ :=
  2 * (Computability.encodeNat n).length + 1

/-- Number of bits used by one length-prefixed natural-number list. -/
def listWireSize (xs : List ℕ) : ℕ :=
  natWireSize xs.length + (xs.map natWireSize).sum

/-- Number of bits used by one length-prefixed nested list. -/
def wireSize (xss : List (List ℕ)) : ℕ :=
  natWireSize xss.length + (xss.map listWireSize).sum

@[simp]
theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  simp [frame]
  omega

@[simp]
theorem encodeNat_length (n : ℕ) :
    (encodeNat n).length = natWireSize n := by
  simp [encodeNat, natWireSize]

@[simp]
theorem encodeNatList_length (xs : List ℕ) :
    (encodeNatList xs).length = listWireSize xs := by
  simp [encodeNatList, listWireSize, Nat.add_comm]

@[simp]
theorem encode_length (xss : List (List ℕ)) :
    (encode xss).length = wireSize xss := by
  simp [encode, wireSize, Nat.add_comm]

theorem natWireSize_pos (n : ℕ) : 0 < natWireSize n := by
  simp [natWireSize]

theorem length_le_listWireSize (xs : List ℕ) :
    xs.length ≤ listWireSize xs := by
  have hsum : xs.length ≤ (xs.map natWireSize).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have hx := natWireSize_pos x
        omega
  exact hsum.trans (Nat.le_add_left _ _)

theorem length_le_wireSize (xss : List (List ℕ)) :
    xss.length ≤ wireSize xss := by
  have hsum : xss.length ≤ (xss.map listWireSize).sum := by
    induction xss with
    | nil => simp
    | cons xs xss ih =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have hxs : 0 < listWireSize xs :=
          (natWireSize_pos xs.length).trans_le (Nat.le_add_right _ _)
        omega
  exact hsum.trans (Nat.le_add_left _ _)

theorem sum_lengths_le_wireSize (xss : List (List ℕ)) :
    (xss.map List.length).sum ≤ wireSize xss := by
  have hsum :
      (xss.map List.length).sum ≤ (xss.map listWireSize).sum := by
    induction xss with
    | nil => simp
    | cons xs xss ih =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (length_le_listWireSize xs) ih
  exact hsum.trans (Nat.le_add_left _ _)

end BinaryNatLists

/-- Runtime-sized explicitly encoded all-different syntax.

The number of variables is `domains.length`; every scope entry is a natural
variable index. Repeated domain values and repeated scope indices have the
same set semantics as `ExplicitSystem`. -/
structure RuntimeSystem where
  domains : List (List ℕ)
  scopes : List (List ℕ)
  deriving DecidableEq, Repr

namespace RuntimeSystem

/-- Syntactic well-formedness before conversion to range-checked indices. -/
def WellFormed (C : RuntimeSystem) : Prop :=
  (∀ domain ∈ C.domains, domain ≠ []) ∧
    ∀ scope ∈ C.scopes, ∀ index ∈ scope, index < C.domains.length

/-- Convert a natural-index scope to the range-checked finite-set syntax.
Out-of-range entries are rejected by `WellFormed` but are filtered here so the
conversion is total on runtime syntax. -/
def scopeFinset (n : ℕ) (scope : List ℕ) : Finset (Fin n) :=
  (scope.filterMap fun index =>
    if h : index < n then some ⟨index, h⟩ else none).toFinset

/-- Convert runtime syntax to the already checked dependent semantic syntax. -/
def toExplicitSystem (C : RuntimeSystem) :
    AllDifferentCSP.ExplicitSystem C.domains.length where
  domains i := (C.domains.get i).toFinset
  scopes := C.scopes.map (scopeFinset C.domains.length)

theorem toExplicitSystem_wellFormed (C : RuntimeSystem)
    (hC : C.WellFormed) :
    C.toExplicitSystem.WellFormed := by
  intro i
  have hmem : C.domains.get i ∈ C.domains := List.get_mem _ _
  have hne := hC.1 _ hmem
  cases hdomain : C.domains.get i with
  | nil => exact (hne hdomain).elim
  | cons value values =>
      refine ⟨value, ?_⟩
      change value ∈ (C.domains.get i).toFinset
      rw [hdomain]
      simp

/-- A nested-list representation with an explicit domain-list count separating
the domain and scope sections. -/
def toNatLists (C : RuntimeSystem) : List (List ℕ) :=
  [C.domains.length] :: (C.domains ++ C.scopes)

/-- Parse the nested-list representation of a runtime system. -/
def ofNatLists : List (List ℕ) → Option RuntimeSystem
  | [domainCount] :: rest =>
      if domainCount ≤ rest.length then
        some {
          domains := rest.take domainCount
          scopes := rest.drop domainCount
        }
      else
        none
  | _ => none

@[simp]
theorem ofNatLists_toNatLists (C : RuntimeSystem) :
    ofNatLists C.toNatLists = some C := by
  simp [ofNatLists, toNatLists]

/-- Standard binary `FinEncoding` for runtime-sized explicit systems. -/
def finEncoding : FinEncoding RuntimeSystem where
  Γ := Bool
  encode C := BinaryNatLists.encode C.toNatLists
  decode bits := (BinaryNatLists.decode bits).bind ofNatLists
  decode_encode C := by
    simp
  ΓFin := Bool.fintype

/-- Actual binary input length under `RuntimeSystem.finEncoding`. -/
def encodedSize (C : RuntimeSystem) : ℕ :=
  (finEncoding.toEncoding.encode C).length

theorem encodedSize_eq_wireSize (C : RuntimeSystem) :
    C.encodedSize = BinaryNatLists.wireSize C.toNatLists := by
  simp [encodedSize, finEncoding]

/-- Number of explicitly supplied domain entries, before finite-set
deduplication. -/
def domainEntryCount (C : RuntimeSystem) : ℕ :=
  (C.domains.map List.length).sum

/-- Number of explicitly supplied scope entries, before finite-set
deduplication. -/
def scopeEntryCount (C : RuntimeSystem) : ℕ :=
  (C.scopes.map List.length).sum

theorem variableCount_le_encodedSize (C : RuntimeSystem) :
    C.domains.length ≤ C.encodedSize := by
  rw [C.encodedSize_eq_wireSize]
  exact (by
    calc
      C.domains.length ≤ C.toNatLists.length := by
        simp only [toNatLists, List.length_cons, List.length_append]
        omega
      _ ≤ BinaryNatLists.wireSize C.toNatLists :=
        BinaryNatLists.length_le_wireSize C.toNatLists)

theorem domainEntryCount_le_encodedSize (C : RuntimeSystem) :
    C.domainEntryCount ≤ C.encodedSize := by
  rw [C.encodedSize_eq_wireSize]
  calc
    C.domainEntryCount ≤ (C.toNatLists.map List.length).sum := by
      simp only [domainEntryCount, toNatLists, List.map_cons,
        List.map_append, List.sum_cons, List.sum_append, List.length_singleton]
      omega
    _ ≤ BinaryNatLists.wireSize C.toNatLists :=
      BinaryNatLists.sum_lengths_le_wireSize C.toNatLists

theorem scopeEntryCount_le_encodedSize (C : RuntimeSystem) :
    C.scopeEntryCount ≤ C.encodedSize := by
  rw [C.encodedSize_eq_wireSize]
  calc
    C.scopeEntryCount ≤ (C.toNatLists.map List.length).sum := by
      simp only [scopeEntryCount, toNatLists, List.map_cons,
        List.map_append, List.sum_cons, List.sum_append, List.length_singleton]
      omega
    _ ≤ BinaryNatLists.wireSize C.toNatLists :=
      BinaryNatLists.sum_lengths_le_wireSize C.toNatLists

end RuntimeSystem

/-- Runtime-sized residual-row output, with finite indices erased to natural
numbers for serialization. -/
inductive RuntimeResidualRow where
  | pin (index target weight : ℕ)
  | unequal (left right : ℕ)
  deriving DecidableEq, Repr

namespace RuntimeResidualRow

def ofResidualRow {n : ℕ} :
    AllDifferentCSP.ExplicitSystem.ResidualRow n → RuntimeResidualRow
  | .pin index target weight => .pin index.1 target weight
  | .unequal left right => .unequal left.1 right.1

def toNatList : RuntimeResidualRow → List ℕ
  | .pin index target weight => [0, index, target, weight]
  | .unequal left right => [1, left, right]

def ofNatList : List ℕ → Option RuntimeResidualRow
  | [0, index, target, weight] => some (.pin index target weight)
  | [1, left, right] => some (.unequal left right)
  | _ => none

@[simp]
theorem ofNatList_toNatList (row : RuntimeResidualRow) :
    ofNatList row.toNatList = some row := by
  cases row <;> rfl

end RuntimeResidualRow

/-- Runtime-sized selected-prime sparse objective output. -/
structure RuntimeObjective where
  variableCount : ℕ
  prime : ℕ
  rows : List RuntimeResidualRow
  deriving DecidableEq, Repr

namespace RuntimeObjective

def ofCompiled {n : ℕ}
    (objective : AllDifferentCSP.ExplicitSystem.CompiledObjective n) :
    RuntimeObjective where
  variableCount := n
  prime := objective.prime
  rows := objective.rows.map RuntimeResidualRow.ofResidualRow

/-- Header row followed by one tagged natural-number list per residual row. -/
def toNatLists (objective : RuntimeObjective) : List (List ℕ) :=
  [objective.variableCount, objective.prime] ::
    objective.rows.map RuntimeResidualRow.toNatList

private def decodeRows :
    List (List ℕ) → Option (List RuntimeResidualRow)
  | [] => some []
  | code :: codes => do
      let row ← RuntimeResidualRow.ofNatList code
      let rows ← decodeRows codes
      pure (row :: rows)

private theorem decodeRows_map_toNatList
    (rows : List RuntimeResidualRow) :
    decodeRows (rows.map RuntimeResidualRow.toNatList) = some rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp [decodeRows, ih]

def ofNatLists : List (List ℕ) → Option RuntimeObjective
  | [variableCount, prime] :: rowCodes => do
      let rows ← decodeRows rowCodes
      some { variableCount, prime, rows }
  | _ => none

@[simp]
theorem ofNatLists_toNatLists (objective : RuntimeObjective) :
    ofNatLists objective.toNatLists = some objective := by
  simp [ofNatLists, toNatLists, decodeRows_map_toNatList]

/-- Standard binary `FinEncoding` for runtime-sized compiled objectives. -/
def finEncoding : FinEncoding RuntimeObjective where
  Γ := Bool
  encode objective := BinaryNatLists.encode objective.toNatLists
  decode bits := (BinaryNatLists.decode bits).bind ofNatLists
  decode_encode objective := by
    simp
  ΓFin := Bool.fintype

/-- Actual binary output length under `RuntimeObjective.finEncoding`. -/
def encodedSize (objective : RuntimeObjective) : ℕ :=
  (finEncoding.toEncoding.encode objective).length

theorem encodedSize_eq_wireSize (objective : RuntimeObjective) :
    objective.encodedSize =
      BinaryNatLists.wireSize objective.toNatLists := by
  simp [encodedSize, finEncoding]

end RuntimeObjective

/-- The runtime-sized compiler obtained by erasing the checked dependent
compiler's finite indices after compilation. -/
def compile (C : RuntimeSystem) : RuntimeObjective :=
  RuntimeObjective.ofCompiled C.toExplicitSystem.compileObjective

@[simp]
theorem compile_variableCount (C : RuntimeSystem) :
    (compile C).variableCount = C.domains.length :=
  rfl

@[simp]
theorem compile_prime (C : RuntimeSystem) :
    (compile C).prime = C.toExplicitSystem.compilerPrime :=
  rfl

@[simp]
theorem compile_rows_length (C : RuntimeSystem) :
    (compile C).rows.length =
      C.toExplicitSystem.compileObjective.rows.length := by
  simp [compile, RuntimeObjective.ofCompiled]

private theorem sum_toFinset_card_le_sum_length :
    ∀ domains : List (List ℕ),
      (∑ i : Fin domains.length, (domains.get i).toFinset.card) ≤
        (domains.map List.length).sum
  | [] => by simp
  | domain :: domains => by
      simpa [Fin.sum_univ_succ] using
        Nat.add_le_add (List.toFinset_card_le domain)
          (sum_toFinset_card_le_sum_length domains)

/-- Sparse row count bounded by a quadratic in the actual binary input
length. This is a row-count theorem, not yet the total encoded-output-size or
machine-running-time theorem. -/
theorem compile_rows_length_le_encodedSize_polynomial (C : RuntimeSystem) :
    (compile C).rows.length ≤ C.encodedSize + C.encodedSize ^ 2 := by
  calc
    (compile C).rows.length =
        C.toExplicitSystem.compileObjective.rows.length :=
      compile_rows_length C
    _ ≤ (∑ i, (C.toExplicitSystem.domains i).card) +
        C.domains.length ^ 2 :=
      C.toExplicitSystem.compileObjective_rows_length_le
    _ ≤ C.domainEntryCount + C.domains.length ^ 2 := by
      apply Nat.add_le_add_right
      simpa [RuntimeSystem.toExplicitSystem,
        RuntimeSystem.domainEntryCount] using
        sum_toFinset_card_le_sum_length C.domains
    _ ≤ C.encodedSize + C.encodedSize ^ 2 := by
      exact Nat.add_le_add C.domainEntryCount_le_encodedSize
        (Nat.pow_le_pow_left C.variableCount_le_encodedSize 2)

#print axioms BinaryNatLists.decode_encode
#print axioms RuntimeSystem.toExplicitSystem_wellFormed
#print axioms RuntimeSystem.ofNatLists_toNatLists
#print axioms RuntimeSystem.encodedSize_eq_wireSize
#print axioms RuntimeObjective.ofNatLists_toNatLists
#print axioms RuntimeObjective.encodedSize_eq_wireSize
#print axioms compile_rows_length_le_encodedSize_polynomial

end PhdThesisLean.AllDifferentCSPEncoding
