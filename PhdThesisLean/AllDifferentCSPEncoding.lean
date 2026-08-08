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
encoded-length formulae and a complete quartic output-size bound are kept
separate from the machine-running-time proof. `AllDifferentCSPMachine` proves
linear-time construction of each framed natural from its raw binary payload
and linear-time serialization of a stack-oriented raw-natural stream into the
exact framed natural-list format. It also proves a linear-time traversal from
this module's standard nested-list encoding to an explicit raw-field stream,
plus linear-time successor and less-than-or-equal passes on canonical binary
naturals, a linear-time ripple-carry addition pass on aligned pairs, and a
quadratic-time unary-bound enumerator for the complete Bertrand interval. Its
delimiter-separated unary-pair encoding and divisibility machine also supply a
linear-time padded trial-division primitive for the future prime scan.
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

private theorem encodePosNum_length_le (n : PosNum) :
    (Computability.encodePosNum n).length ≤ (n : ℕ) := by
  induction n with
  | one => simp [Computability.encodePosNum]
  | bit1 n ih =>
      simp only [Computability.encodePosNum, List.length_cons]
      simp only [PosNum.cast_bit1]
      omega
  | bit0 n ih =>
      simp only [Computability.encodePosNum, List.length_cons]
      simp only [PosNum.cast_bit0]
      have hn : 0 < (n : ℕ) := PosNum.cast_pos n
      omega

/-- The standard binary representation of a natural has at most `n` bits.
This deliberately coarse linear estimate is enough for the polynomial output
bound below. -/
theorem encodeNat_length_le (n : ℕ) :
    (Computability.encodeNat n).length ≤ n := by
  rw [Computability.encodeNat]
  cases h : (n : Num) with
  | zero => simp [Computability.encodeNum]
  | pos p =>
      rw [Computability.encodeNum]
      have hp := encodePosNum_length_le p
      have hn : n = (p : ℕ) := by
        have h' := congrArg (fun m : Num => (m : ℕ)) h
        simpa using h'
      simpa [hn] using hp

theorem natWireSize_le_two_mul_add_one (n : ℕ) :
    natWireSize n ≤ 2 * n + 1 := by
  rw [natWireSize]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 (encodeNat_length_le n)) 1

theorem sum_natWireSize_le (xs : List ℕ) (bound : ℕ)
    (hxs : ∀ x ∈ xs, x ≤ bound) :
    (xs.map natWireSize).sum ≤ xs.length * (2 * bound + 1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      calc
        ((x :: xs).map natWireSize).sum =
            natWireSize x + (xs.map natWireSize).sum := by simp
        _ ≤ (2 * bound + 1) + xs.length * (2 * bound + 1) :=
          Nat.add_le_add
            ((natWireSize_le_two_mul_add_one x).trans
              (Nat.add_le_add_right
                (Nat.mul_le_mul_left 2 (hxs x (by simp))) 1))
            (ih fun y hy => hxs y (by simp [hy]))
        _ = (x :: xs).length * (2 * bound + 1) := by
          simp [Nat.succ_mul, Nat.add_comm]

theorem listWireSize_le (xs : List ℕ) (bound : ℕ)
    (hxs : ∀ x ∈ xs, x ≤ bound) :
    listWireSize xs ≤
      (2 * xs.length + 1) + xs.length * (2 * bound + 1) := by
  exact Nat.add_le_add (natWireSize_le_two_mul_add_one xs.length)
    (sum_natWireSize_le xs bound hxs)

/-- A code containing at most four naturals bounded by `bound` has this
uniform framed size bound. -/
theorem listWireSize_le_sixteen (xs : List ℕ) (bound : ℕ)
    (hlength : xs.length ≤ 4) (hxs : ∀ x ∈ xs, x ≤ bound) :
    listWireSize xs ≤ 16 * (bound + 1) := by
  have h := listWireSize_le xs bound hxs
  have hmul : xs.length * (2 * bound + 1) ≤ 4 * (2 * bound + 1) :=
    Nat.mul_le_mul_right (2 * bound + 1) hlength
  omega

theorem sum_listWireSize_le (xss : List (List ℕ)) (bound : ℕ)
    (hlength : ∀ xs ∈ xss, xs.length ≤ 4)
    (hxs : ∀ xs ∈ xss, ∀ x ∈ xs, x ≤ bound) :
    (xss.map listWireSize).sum ≤
      xss.length * (16 * (bound + 1)) := by
  induction xss with
  | nil => simp
  | cons xs xss ih =>
      calc
        (((xs :: xss).map listWireSize).sum) =
            listWireSize xs + (xss.map listWireSize).sum := by simp
        _ ≤ (16 * (bound + 1)) +
            xss.length * (16 * (bound + 1)) :=
          Nat.add_le_add
            (listWireSize_le_sixteen xs bound
              (hlength xs (by simp)) (hxs xs (by simp)))
            (ih (fun ys hys => hlength ys (by simp [hys]))
              (fun ys hys => hxs ys (by simp [hys])))
        _ = (xs :: xss).length * (16 * (bound + 1)) := by
          simp [Nat.succ_mul, Nat.add_comm]

/-- A nested code with four-field inner rows and uniformly bounded numeric
fields has a linear-in-row-count wire-size bound. -/
theorem wireSize_le (xss : List (List ℕ)) (bound : ℕ)
    (hlength : ∀ xs ∈ xss, xs.length ≤ 4)
    (hxs : ∀ xs ∈ xss, ∀ x ∈ xs, x ≤ bound) :
    wireSize xss ≤
      (2 * xss.length + 1) +
        xss.length * (16 * (bound + 1)) := by
  exact Nat.add_le_add (natWireSize_le_two_mul_add_one xss.length)
    (sum_listWireSize_le xss bound hlength hxs)

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

private theorem pinningRow_fields_le {n : ℕ}
    (C : ExplicitSystem n) (index : Fin n) (target weight : ℕ)
    (hrow : ExplicitSystem.ResidualRow.pin index target weight ∈
      C.pinningRows) :
    target ≤ C.symbolCount ∧ weight = C.pinningWeight := by
  simp only [ExplicitSystem.pinningRows, List.mem_flatMap,
    List.mem_map] at hrow
  obtain ⟨sourceIndex, _hsourceIndex, sourceTarget, hsourceTarget, heq⟩ := hrow
  simp only [Finset.mem_sort] at hsourceTarget
  injection heq with hindex htarget hweight
  subst index
  subst target
  subst weight
  have hvalue : sourceTarget ∈ C.relabeled.domainValues :=
    (C.relabeled.mem_domainValues_iff sourceTarget).2
      ⟨sourceIndex, by simpa using hsourceTarget⟩
  rw [C.domainValues_relabeled_eq_Icc] at hvalue
  exact ⟨(Finset.mem_Icc.mp hvalue).2, rfl⟩

private theorem compiledRow_fields_le {n : ℕ}
    (C : ExplicitSystem n) (row : ExplicitSystem.ResidualRow n)
    (hrow : row ∈ C.compileObjective.rows) :
    match row with
    | .pin index target weight =>
        index.1 < n ∧ target ≤ C.symbolCount ∧
          weight ≤ C.primalEdges.card + 1
    | .unequal left right => left.1 < n ∧ right.1 < n := by
  cases row with
  | pin index target weight =>
      rw [ExplicitSystem.compileObjective] at hrow
      simp only [List.mem_append] at hrow
      rcases hrow with hpin | hneq
      · have h := pinningRow_fields_le C index target weight hpin
        exact ⟨index.isLt, h.1, by
          simpa [ExplicitSystem.pinningWeight] using h.2.le⟩
      · simp [ExplicitSystem.unequalRows] at hneq
  | unequal left right =>
      rw [ExplicitSystem.compileObjective] at hrow
      simp only [List.mem_append] at hrow
      rcases hrow with hpin | hneq
      · simp [ExplicitSystem.pinningRows] at hpin
      · simp only [ExplicitSystem.unequalRows, List.mem_map,
          Finset.mem_sort] at hneq
        obtain ⟨edge, _hedge, heq⟩ := hneq
        injection heq with hleft hright
        subst left
        subst right
        exact ⟨edge.1.isLt, edge.2.isLt⟩

private theorem symbolCount_le_encodedSize (C : RuntimeSystem) :
    C.toExplicitSystem.symbolCount ≤ C.encodedSize := by
  calc
    C.toExplicitSystem.symbolCount ≤
        ∑ i, (C.toExplicitSystem.domains i).card :=
      C.toExplicitSystem.symbolCount_le_sum_domain_card
    _ ≤ C.domainEntryCount := by
      simpa [RuntimeSystem.toExplicitSystem,
        RuntimeSystem.domainEntryCount] using
        sum_toFinset_card_le_sum_length C.domains
    _ ≤ C.encodedSize := C.domainEntryCount_le_encodedSize

private theorem compile_prime_le_fieldBound (C : RuntimeSystem) :
    (compile C).prime ≤ 2 * (C.encodedSize + 1) ^ 2 := by
  rw [compile_prime]
  by_cases hq : C.toExplicitSystem.symbolCount = 0
  · rw [ExplicitSystem.compilerPrime, hq, ExplicitSystem.selectPrimeAbove_zero]
    have hk2 : 1 ≤ (C.encodedSize + 1) ^ 2 :=
      Nat.one_le_pow' 2 C.encodedSize
    simpa using Nat.mul_le_mul_left 2 hk2
  · calc
      C.toExplicitSystem.compilerPrime =
          ExplicitSystem.selectPrimeAbove C.toExplicitSystem.symbolCount := rfl
      _ ≤ 2 * C.toExplicitSystem.symbolCount :=
        ExplicitSystem.selectPrimeAbove_le_two_mul hq
      _ ≤ 2 * C.encodedSize :=
        Nat.mul_le_mul_left 2 (symbolCount_le_encodedSize C)
      _ ≤ 2 * (C.encodedSize + 1) ^ 2 := by nlinarith

private theorem compile_row_entry_le_fieldBound
    (C : RuntimeSystem) (row : RuntimeResidualRow)
    (hrow : row ∈ (compile C).rows) (entry : ℕ)
    (hentry : entry ∈ row.toNatList) :
    entry ≤ 2 * (C.encodedSize + 1) ^ 2 := by
  let D := C.toExplicitSystem
  have hn : C.domains.length ≤ C.encodedSize :=
    C.variableCount_le_encodedSize
  have hq : D.symbolCount ≤ C.encodedSize := by
    simpa [D] using symbolCount_le_encodedSize C
  change row ∈
    (D.compileObjective.rows.map RuntimeResidualRow.ofResidualRow) at hrow
  obtain ⟨sourceRow, hsourceRow, rfl⟩ := List.mem_map.mp hrow
  have hfields := compiledRow_fields_le D sourceRow hsourceRow
  cases sourceRow with
  | pin index target weight =>
      simp only [RuntimeResidualRow.ofResidualRow,
        RuntimeResidualRow.toNatList, List.mem_cons, List.not_mem_nil,
        or_false] at hentry
      rcases hentry with rfl | rfl | rfl | rfl
      · nlinarith
      · have hi := hfields.1
        change index.1 < C.domains.length at hi
        nlinarith
      · exact hfields.2.1.trans (hq.trans (by nlinarith))
      · have hedge : D.primalEdges.card ≤ C.domains.length ^ 2 :=
          D.primalEdges_card_le_square
        have hw : entry ≤ C.domains.length ^ 2 + 1 :=
          hfields.2.2.trans (Nat.add_le_add_right hedge 1)
        calc
          entry ≤ C.domains.length ^ 2 + 1 := hw
          _ ≤ C.encodedSize ^ 2 + 1 :=
            Nat.add_le_add_right (Nat.pow_le_pow_left hn 2) 1
          _ ≤ 2 * (C.encodedSize + 1) ^ 2 := by nlinarith
  | unequal left right =>
      simp only [RuntimeResidualRow.ofResidualRow,
        RuntimeResidualRow.toNatList, List.mem_cons, List.not_mem_nil,
        or_false] at hentry
      rcases hentry with rfl | rfl | rfl
      · nlinarith
      · have hl := hfields.1
        change left.1 < C.domains.length at hl
        nlinarith
      · have hr := hfields.2
        change right.1 < C.domains.length at hr
        nlinarith

private theorem compile_toNatLists_inner_length_le_four
    (C : RuntimeSystem) (code : List ℕ)
    (hcode : code ∈ (compile C).toNatLists) :
    code.length ≤ 4 := by
  simp only [RuntimeObjective.toNatLists, List.mem_cons,
    List.mem_map] at hcode
  rcases hcode with rfl | ⟨row, _hrow, rfl⟩
  · simp
  · cases row <;> simp [RuntimeResidualRow.toNatList]

private theorem compile_toNatLists_entry_le_fieldBound
    (C : RuntimeSystem) (code : List ℕ)
    (hcode : code ∈ (compile C).toNatLists)
    (entry : ℕ) (hentry : entry ∈ code) :
    entry ≤ 2 * (C.encodedSize + 1) ^ 2 := by
  simp only [RuntimeObjective.toNatLists, List.mem_cons,
    List.mem_map] at hcode
  rcases hcode with rfl | ⟨row, hrow, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
    rcases hentry with rfl | rfl
    · rw [compile_variableCount]
      have hn := C.variableCount_le_encodedSize
      nlinarith
    · exact compile_prime_le_fieldBound C
  · exact compile_row_entry_le_fieldBound C row hrow entry hentry

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

private theorem compile_toNatLists_length_le (C : RuntimeSystem) :
    (compile C).toNatLists.length ≤ (C.encodedSize + 1) ^ 2 := by
  have hrows := compile_rows_length_le_encodedSize_polynomial C
  simp only [RuntimeObjective.toNatLists, List.length_cons, List.length_map]
  nlinarith

/-- A field-sensitive polynomial bound for the complete binary output,
including the selected prime, canonical targets, pinning weights, endpoints,
tags, row framing, and outer framing. -/
theorem compile_encodedSize_le_polynomial (C : RuntimeSystem) :
    (compile C).encodedSize ≤
      (2 * (C.encodedSize + 1) ^ 2 + 1) +
        (C.encodedSize + 1) ^ 2 *
          (16 * (2 * (C.encodedSize + 1) ^ 2 + 1)) := by
  rw [(compile C).encodedSize_eq_wireSize]
  let countBound := (C.encodedSize + 1) ^ 2
  let fieldBound := 2 * countBound
  have hwire := BinaryNatLists.wireSize_le
    (compile C).toNatLists fieldBound
    (compile_toNatLists_inner_length_le_four C)
    (compile_toNatLists_entry_le_fieldBound C)
  calc
    BinaryNatLists.wireSize (compile C).toNatLists ≤
        (2 * (compile C).toNatLists.length + 1) +
          (compile C).toNatLists.length * (16 * (fieldBound + 1)) :=
      hwire
    _ ≤ (2 * countBound + 1) +
          countBound * (16 * (fieldBound + 1)) := by
      exact Nat.add_le_add
        (Nat.add_le_add_right
          (Nat.mul_le_mul_left 2 (compile_toNatLists_length_le C)) 1)
        (Nat.mul_le_mul_right (16 * (fieldBound + 1))
          (compile_toNatLists_length_le C))
    _ = (2 * (C.encodedSize + 1) ^ 2 + 1) +
        (C.encodedSize + 1) ^ 2 *
          (16 * (2 * (C.encodedSize + 1) ^ 2 + 1)) := rfl

/-- The complete encoded compiler output is bounded by an explicit quartic
in the actual encoded input length. This is an output-size theorem, not yet a
`TM2ComputableInPolyTime` theorem for constructing that output. -/
theorem compile_encodedSize_le_quartic (C : RuntimeSystem) :
    (compile C).encodedSize ≤ 64 * (C.encodedSize + 1) ^ 4 := by
  apply (compile_encodedSize_le_polynomial C).trans
  let square := (C.encodedSize + 1) ^ 2
  have hsquare : 1 ≤ square := by
    exact Nat.one_le_pow' 2 C.encodedSize
  have hbound :
      (2 * square + 1) + square * (16 * (2 * square + 1)) ≤
        64 * square ^ 2 := by
    nlinarith
  simpa [square, ← pow_mul] using hbound

#print axioms BinaryNatLists.decode_encode
#print axioms RuntimeSystem.toExplicitSystem_wellFormed
#print axioms RuntimeSystem.ofNatLists_toNatLists
#print axioms RuntimeSystem.encodedSize_eq_wireSize
#print axioms RuntimeObjective.ofNatLists_toNatLists
#print axioms RuntimeObjective.encodedSize_eq_wireSize
#print axioms compile_rows_length_le_encodedSize_polynomial
#print axioms compile_encodedSize_le_quartic

end PhdThesisLean.AllDifferentCSPEncoding
