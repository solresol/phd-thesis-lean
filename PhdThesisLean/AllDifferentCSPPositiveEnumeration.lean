import PhdThesisLean.AllDifferentCSPBoundedSections

/-!
# Exact ordered positive rows from retained ranked occurrences

Scan variable indices and the input-length-bounded rank interval, testing
membership in the retained occurrence stream. Each pair is visited once, so
repeated domain entries produce one positive row. The correspondence is an
equality of ordered lists with the semantic compiler, not just of sets.
This module specifies the executable scan; its finite-machine implementation
and runtime are separate obligations.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open PhdThesisLean.AllDifferentCSPEncoding
open PhdThesisLean.AllDifferentCSP

namespace PositiveEnumeration

/-- Every variable/rank candidate in the order used by the positive-row scan. -/
def candidates (n : ℕ) (occurrences : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun index =>
    (List.range (occurrences.length + 1)).map fun value => (index, value)

theorem candidates_length (n : ℕ) (occurrences : List (ℕ × ℕ)) :
    (candidates n occurrences).length = n * (occurrences.length + 1) := by
  simp [candidates, List.length_flatMap]

/-- Visit ranks in increasing order, retaining exactly the listed pairs. -/
def values (occurrences : List (ℕ × ℕ)) (index : ℕ) : List ℕ :=
  (List.range (occurrences.length + 1)).filter fun value => occurrences.contains (index, value)

/-- A rectangular scan uses the number of stored occurrences, never a symbol's magnitude. -/
def enumerate (n : ℕ) (occurrences : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun index => (values occurrences index).map fun value => (index, value)

theorem enumerate_eq_filter (n : ℕ) (occurrences : List (ℕ × ℕ)) :
    enumerate n occurrences = (candidates n occurrences).filter occurrences.contains := by
  simp [enumerate, candidates, values, List.filter_flatMap, List.filter_map, Function.comp_def]

@[simp]
theorem mem_values (occurrences : List (ℕ × ℕ)) (index value : ℕ) :
    value ∈ values occurrences index ↔ value ≤ occurrences.length ∧ (index, value) ∈ occurrences := by
  simp [values, Nat.lt_succ_iff]

@[simp]
theorem mem_enumerate (n : ℕ) (occurrences : List (ℕ × ℕ)) (index value : ℕ) :
    (index, value) ∈ enumerate n occurrences ↔
      index < n ∧ value ≤ occurrences.length ∧ (index, value) ∈ occurrences := by
  simp [enumerate]

theorem enumerate_pairwise (n : ℕ) (occurrences : List (ℕ × ℕ)) :
    (enumerate n occurrences).Pairwise (Prod.Lex (· < ·) (· < ·)) := by
  rw [enumerate, List.pairwise_flatMap]
  constructor
  · intro index _
    rw [List.pairwise_map]
    exact (List.pairwise_lt_range.filter _).imp fun h => Prod.Lex.right _ h
  · apply List.pairwise_lt_range.imp
    intro i j hij a ha b hb
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
    exact Prod.Lex.left _ _ hij

theorem enumerate_nodup (n : ℕ) (occurrences : List (ℕ × ℕ)) :
    (enumerate n occurrences).Nodup := (enumerate_pairwise n occurrences).nodup

/-- Deduplication cannot increase the number of stored occurrences. -/
theorem enumerate_length_le (n : ℕ) (occurrences : List (ℕ × ℕ)) :
    (enumerate n occurrences).length ≤ occurrences.length := by
  rw [← List.toFinset_card_of_nodup (enumerate_nodup n occurrences)]
  apply (Finset.card_le_card ?_).trans (List.toFinset_card_le (l := occurrences))
  intro pair hp
  exact List.mem_toFinset.mpr ((mem_enumerate n occurrences pair.1 pair.2).mp
    (List.mem_toFinset.mp hp)).2.2

theorem occurrenceCount_le_wire (occurrences : List (ℕ × ℕ)) :
    occurrences.length ≤ (DomainFieldRow.outputEncode occurrences).length := by
  induction occurrences with
  | nil => simp [DomainFieldRow.outputEncode]
  | cons pair occurrences ih =>
    simp only [DomainFieldRow.outputEncode, List.flatMap_cons, List.length_append,
      List.length_cons] at *
    rw [DomainOccurrenceFieldBlock.outputEncode_eq_prefix, List.length_append]
    have hp : DomainOccurrenceFieldBlock.headerPrefix.length = 4 := rfl
    omega

/-- Both scan dimensions are bounded by actual retained-section wire length. -/
theorem candidates_length_le_wire_quadratic (sections : BoundedRelabelledSections.Value) :
    (candidates sections.1.2 sections.1.1).length ≤
      (BoundedRelabelledSections.finEncoding.encode sections).length *
        ((BoundedRelabelledSections.finEncoding.encode sections).length + 1) := by
  rw [candidates_length]
  apply Nat.mul_le_mul (BoundedRelabelledSections.variableCount_le_encode_length sections)
  have hc := occurrenceCount_le_wire sections.1.1
  rw [BoundedRelabelledSections.encode_length]
  omega

private theorem index_ge_start (domains : List (List ℕ)) (start : ℕ)
    (pair : ℕ × ℕ)
    (h : pair ∈ RuntimeStructuralView.indexedDomainOccurrencesFrom start domains) :
    start ≤ pair.1 := by
  induction domains generalizing start with
  | nil => simp [RuntimeStructuralView.indexedDomainOccurrencesFrom] at h
  | cons domain domains ih =>
    simp only [RuntimeStructuralView.indexedDomainOccurrencesFrom, List.mem_append,
      List.mem_map] at h
    rcases h with ⟨value, _, rfl⟩ | h
    · exact le_rfl
    · exact (Nat.le_succ start).trans (ih (start + 1) h)

/-- Exact membership at an offset index, including empty rows before it. -/
theorem mem_indexedFrom (domains : List (List ℕ)) (start : ℕ)
    (index : Fin domains.length) (value : ℕ) :
    (start + index.val, value) ∈ RuntimeStructuralView.indexedDomainOccurrencesFrom start domains ↔
      value ∈ domains.get index := by
  induction domains generalizing start with
  | nil => exact Fin.elim0 index
  | cons domain domains ih =>
    refine Fin.cases ?_ (fun index => ?_) index
    · simp [RuntimeStructuralView.indexedDomainOccurrencesFrom]
      intro h
      have bound := index_ge_start domains (start + 1) (start, value) h
      omega
    · simpa [RuntimeStructuralView.indexedDomainOccurrencesFrom, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using ih (start + 1) index

theorem retained_occurrences (C : RuntimeSystem) :
    (BoundedRelabelledSections.ofRuntimeSystem C).1.1 =
      (RuntimeStructuralView.indexedDomainOccurrences C.domains).map
        (fun pair => (pair.1, C.toExplicitSystem.relabelValue pair.2)) :=
  CountedRelabelledSections.domains_ofRuntimeSystem C

theorem retained_length (C : RuntimeSystem) :
    (BoundedRelabelledSections.ofRuntimeSystem C).1.1.length = C.domainEntryCount := by
  rw [retained_occurrences, List.length_map, RuntimeStructuralView.indexedDomainOccurrences_length]
  rfl

/-- The retained stream and semantic relabelled domain have exactly the same members. -/
theorem retained_mem (C : RuntimeSystem) (index : Fin C.domains.length) (value : ℕ) :
    (index.val, value) ∈ (BoundedRelabelledSections.ofRuntimeSystem C).1.1 ↔
      value ∈ C.toExplicitSystem.relabeledDomain index := by
  rw [retained_occurrences]
  simp only [List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨i, a⟩, ha, hi, hv⟩
    dsimp at hi hv
    subst i
    subst value
    apply Finset.mem_image.mpr
    refine ⟨a, ?_, rfl⟩
    change a ∈ (C.domains.get index).toFinset
    exact List.mem_toFinset.mpr ((mem_indexedFrom C.domains 0 index a).mp (by simpa using ha))
  · rintro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    refine ⟨(index.val, a), ?_, rfl, rfl⟩
    change a ∈ (C.domains.get index).toFinset at ha
    simpa using (mem_indexedFrom C.domains 0 index a).mpr (List.mem_toFinset.mp ha)

/-- The scan bound includes every semantic rank, without depending on raw symbol magnitude. -/
theorem rank_le_retained_length (C : RuntimeSystem) (index : Fin C.domains.length)
    {value : ℕ} (h : value ∈ C.toExplicitSystem.relabeledDomain index) :
    value ≤ (BoundedRelabelledSections.ofRuntimeSystem C).1.1.length := by
  rw [retained_length]
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
  exact (C.toExplicitSystem.relabelValue_le_symbolCount
    ((ExplicitSystem.mem_domainValues_iff _ _).mpr ⟨index, ha⟩)).trans
      C.symbolCount_le_domainEntryCount

theorem values_eq_sorted_domain (C : RuntimeSystem) (index : Fin C.domains.length) :
    values (BoundedRelabelledSections.ofRuntimeSystem C).1.1 index.val =
      (C.toExplicitSystem.relabeledDomain index).sort (· ≤ ·) := by
  have hset : (values (BoundedRelabelledSections.ofRuntimeSystem C).1.1 index.val).toFinset =
      C.toExplicitSystem.relabeledDomain index := by
    ext value
    simp only [List.mem_toFinset, mem_values, retained_mem]
    exact ⟨And.right, fun h => ⟨rank_le_retained_length C index h, h⟩⟩
  rw [← hset]
  symm
  apply (List.toFinset_sort (· ≤ ·) (List.nodup_range.filter _)).mpr
  exact (List.pairwise_lt_range.filter _).imp fun h => h.le

def rows (n : ℕ) (occurrences : List (ℕ × ℕ)) (weight : ℕ) : List RuntimeResidualRow :=
  (enumerate n occurrences).map fun pair => .pin pair.1 pair.2 weight

/-- Exact row order and multiplicity, with the weight computed by the checked graph pass. -/
theorem rows_eq_pinningRows (C : RuntimeSystem) :
    rows C.domains.length (BoundedRelabelledSections.ofRuntimeSystem C).1.1
      ((PrimalEdgeEnumeration.ofRuntimeSystem C).length + 1) =
      C.toExplicitSystem.pinningRows.map RuntimeResidualRow.ofResidualRow := by
  rw [rows, enumerate, ← NegativeRows.pinningWeight_eq_edgeCount,
    ← List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def,
    ExplicitSystem.pinningRows, Fin.sort_univ]
  apply List.flatMap_congr
  intro index _
  rw [values_eq_sorted_domain]
  rfl

example : enumerate 4 [(0, 3), (0, 1), (0, 3), (2, 2), (2, 1), (2, 1)] =
    [(0, 1), (0, 3), (2, 1), (2, 2)] := by decide
example : enumerate 3 [] = [] := by decide
example : rows 0 [] 1 = [] := rfl
example : let C : RuntimeSystem := ⟨[[100, 7, 100], [], [42, 7], []], [[0, 2], [2, 0, 2]]⟩
    rows C.domains.length (BoundedRelabelledSections.ofRuntimeSystem C).1.1
      ((PrimalEdgeEnumeration.ofRuntimeSystem C).length + 1) =
      [.pin 0 1 2, .pin 0 3 2, .pin 2 1 2, .pin 2 2 2] := by decide

#print axioms enumerate_eq_filter
#print axioms enumerate_nodup
#print axioms enumerate_length_le
#print axioms candidates_length_le_wire_quadratic
#print axioms retained_mem
#print axioms values_eq_sorted_domain
#print axioms rows_eq_pinningRows

end PositiveEnumeration

end PhdThesisLean.AllDifferentCSPMachine
