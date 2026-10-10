import PhdThesisLean.AllDifferentCSPPositiveRows

/-!
# Count retained occurrences for the positive-row scan

Reuse the checked counted-row machine on the exact tagged occurrence wire.
The count includes repeated domain entries and is constructed inside the
compiler. Nested pair adapters preserve both the unary variable count and
all scopes, negative rows and binary weight. No positive scan is claimed here.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace OccurrenceCount

abbrev Value := List (ℕ × ℕ) × ℕ

def finEncoding : FinEncoding Value :=
  LeanNPHardness.PairEncoding.finEncoding DomainFieldRow.outputFinEncoding unaryFinEncodingNat

def retain (occurrences : List (ℕ × ℕ)) : Value := (occurrences, occurrences.length)

/-- The existing occurrence wire is already a stream of counted tagged rows. -/
theorem occurrenceWire_eq_rows (occurrences : List (ℕ × ℕ)) :
    DomainFieldRow.outputEncode occurrences =
      DomainFieldSection.rowPayloadEncode (occurrences.map fun pair => [0, pair.1, pair.2]) := by
  simp only [DomainFieldRow.outputEncode, DomainFieldSection.rowPayloadEncode,
    DomainFieldSection.rowFields, List.flatMap_map]
  simp only [SourceOrderRawFields.encode, List.flatMap_assoc]
  apply List.flatMap_congr
  intro pair _
  simp [DomainOccurrenceFieldBlock.outputEncode, SourceOrderRawFields.encode]

@[simp]
theorem encode_retain (occurrences : List (ℕ × ℕ)) :
    finEncoding.encode (retain occurrences) =
      (DomainFieldRow.outputEncode occurrences).map Sum.inl ++
        List.replicate occurrences.length (.inr true) := by
  simp [finEncoding, retain, DomainFieldRow.outputFinEncoding, unaryFinEncodingNat,
    unaryEncodeNat_eq_replicate_true]

theorem encode_retain_length (occurrences : List (ℕ × ℕ)) :
    (finEncoding.encode (retain occurrences)).length =
      (DomainFieldRow.outputEncode occurrences).length + occurrences.length := by
  rw [encode_retain]
  simp

theorem encode_retain_length_le (occurrences : List (ℕ × ℕ)) :
    (finEncoding.encode (retain occurrences)).length ≤
      2 * (DomainFieldRow.outputEncode occurrences).length := by
  rw [encode_retain_length]
  have h := PositiveEnumeration.occurrenceCount_le_wire occurrences
  omega

/-- The imported traversal counts records, retains every bit and clears its scratch stacks. -/
def outputsInTime (occurrences : List (ℕ × ℕ)) :
    TM2OutputsInTime StructuralRowCountMachine.computer
      (DomainFieldRow.outputEncode occurrences)
      (some (finEncoding.encode (retain occurrences)))
      (20 * ((DomainFieldRow.outputEncode occurrences).length + 1) ^ 2) := by
  simpa only [DomainCountedPayload.encode_retain, List.length_map,
    ← occurrenceWire_eq_rows, encode_retain] using
      domainVariableCount_outputsInTime (occurrences.map fun pair => [0, pair.1, pair.2])

noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime (List (ℕ × ℕ)) Value DomainFieldRow.outputFinEncoding
      finEncoding retain where
  tm := StructuralRowCountMachine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 20 * (Polynomial.X + 1) ^ 2
  outputsFun occurrences := by
    simpa [DomainFieldRow.outputFinEncoding, Equiv.refl, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_natCast,
      Polynomial.eval_one, Polynomial.eval_X] using outputsInTime occurrences

end OccurrenceCount

namespace CountedPositiveSections

abbrev Domains := OccurrenceCount.Value × ℕ
abbrev Sections := Domains × List (List ℕ)
abbrev Value := Sections × EdgeCount.Value

def domainsFinEncoding : FinEncoding Domains :=
  LeanNPHardness.PairEncoding.finEncoding OccurrenceCount.finEncoding unaryFinEncodingNat

def sectionsFinEncoding : FinEncoding Sections :=
  LeanNPHardness.PairEncoding.finEncoding domainsFinEncoding ScopeFieldSection.rowPayloadFinEncoding

def finEncoding : FinEncoding Value :=
  LeanNPHardness.PairEncoding.finEncoding sectionsFinEncoding PinningWeight.negativeFinEncoding

def retain (value : WeightedGraphSections.Value) : Value :=
  (((OccurrenceCount.retain value.1.1.1, value.1.1.2), value.1.2), value.2)

def forget (value : Value) : WeightedGraphSections.Value :=
  (((value.1.1.1.1, value.1.1.2), value.1.2), value.2)

def ofRuntimeSystem (C : RuntimeSystem) : Value := retain (WeightedGraphSections.ofRuntimeSystem C)

@[simp]
theorem forget_retain (value : WeightedGraphSections.Value) : forget (retain value) = value := rfl

/-- The bound is the original number of entries, before any positive-row deduplication. -/
theorem count_eq (C : RuntimeSystem) :
    (ofRuntimeSystem C).1.1.1.2 = C.domainEntryCount :=
  PositiveEnumeration.retained_length C

theorem encode_length (value : Value) :
    (finEncoding.encode value).length =
      (WeightedGraphSections.finEncoding.encode (forget value)).length + value.1.1.1.2 := by
  simp [finEncoding, sectionsFinEncoding, domainsFinEncoding, OccurrenceCount.finEncoding,
    WeightedGraphSections.finEncoding, BoundedRelabelledSections.finEncoding,
    BoundedRelabelledSections.domainsFinEncoding, forget, unaryFinEncodingNat,
    unaryEncodeNat_eq_replicate_true, Nat.add_comm, Nat.add_left_comm]

theorem count_le_encode_length (value : Value) :
    value.1.1.1.2 ≤ (finEncoding.encode value).length := by
  rw [encode_length]
  omega

theorem variableCount_le_encode_length (value : Value) :
    value.1.1.2 ≤ (finEncoding.encode value).length := by
  have h := BoundedRelabelledSections.variableCount_le_encode_length (forget value).1
  rw [encode_length]
  simp only [WeightedGraphSections.finEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length]
  exact h.trans (by omega)

/-- Both numerical scan dimensions are small for every encoded intermediate value. -/
theorem gridSize_le_wire_quadratic (value : Value) :
    value.1.1.2 * (value.1.1.1.2 + 1) ≤
      (finEncoding.encode value).length * ((finEncoding.encode value).length + 1) :=
  Nat.mul_le_mul (variableCount_le_encode_length value)
    (Nat.add_le_add_right (count_le_encode_length value) 1)

theorem encode_retain_length_le (value : WeightedGraphSections.Value) :
    (finEncoding.encode (retain value)).length ≤
      2 * (WeightedGraphSections.finEncoding.encode value).length := by
  rw [encode_length, forget_retain]
  have h := PositiveEnumeration.occurrenceCount_le_wire value.1.1.1
  have hb := BoundedRelabelledSections.encode_length value.1
  have hw : (WeightedGraphSections.finEncoding.encode value).length =
      (BoundedRelabelledSections.finEncoding.encode value.1).length +
        (PinningWeight.negativeFinEncoding.encode value.2).length := by
    simp [WeightedGraphSections.finEncoding]
  dsimp only [retain, OccurrenceCount.retain]
  omega

theorem positiveRows_eq (C : RuntimeSystem) :
    (PositiveRows.ofWeightedSections (forget (ofRuntimeSystem C))).map PositiveRows.row =
      C.toExplicitSystem.pinningRows.map RuntimeResidualRow.ofResidualRow :=
  PositiveRows.rows_ofRuntimeSystem C

example : (ofRuntimeSystem ⟨[[], []], [[]]⟩).1.1 = (([], 0), 2) := by decide
example : (ofRuntimeSystem ⟨[[100, 7, 100], [], [42, 7]], [[0, 2], [2, 0, 2]]⟩).1.1 =
    (([(0, 3), (0, 1), (0, 3), (2, 2), (2, 1)], 5), 3) := by decide

end CountedPositiveSections

/-- Construct the tally while retaining both prior bounds, scopes, rows and weight. -/
noncomputable def countedPositiveSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime WeightedGraphSections.Value CountedPositiveSections.Value
      WeightedGraphSections.finEncoding CountedPositiveSections.finEncoding
      CountedPositiveSections.retain :=
  LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    BoundedRelabelledSections.finEncoding CountedPositiveSections.sectionsFinEncoding
    PinningWeight.negativeFinEncoding _
    (LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
      BoundedRelabelledSections.domainsFinEncoding CountedPositiveSections.domainsFinEncoding
      ScopeFieldSection.rowPayloadFinEncoding _
      (LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
        DomainFieldRow.outputFinEncoding OccurrenceCount.finEncoding unaryFinEncodingNat _
        OccurrenceCount.computableInPolyTime))

/-- The occurrence bound is computed from the actual Boolean compiler input. -/
noncomputable def runtimeCompilerCountedPositiveSectionsComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem CountedPositiveSections.Value
      RuntimeCompilerInput.finEncoding CountedPositiveSections.finEncoding
      CountedPositiveSections.ofRuntimeSystem := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerWeightedNegativeSectionsComputableInPolyTime
    countedPositiveSectionsComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa only [Function.comp_def, CountedPositiveSections.ofRuntimeSystem]
        using composed.outputsFun C }

#print axioms OccurrenceCount.occurrenceWire_eq_rows
#print axioms OccurrenceCount.outputsInTime
#print axioms OccurrenceCount.computableInPolyTime
#print axioms CountedPositiveSections.count_eq
#print axioms CountedPositiveSections.gridSize_le_wire_quadratic
#print axioms CountedPositiveSections.encode_retain_length_le
#print axioms CountedPositiveSections.positiveRows_eq
#print axioms runtimeCompilerCountedPositiveSectionsComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
