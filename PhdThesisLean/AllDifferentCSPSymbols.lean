import PhdThesisLean.AllDifferentCSPEncoding

namespace PhdThesisLean.AllDifferentCSPEncoding

/-!
# Domain-symbol extraction and the canonical rank contract

The structural machine preserves every occurrence. Relabelling must instead
count each distinct symbol once, even when it occurs in several domains.
These executable list operations specify the next machine target and connect
it to the existing semantic compiler. They do not assert a machine time bound
for list deduplication or rank computation.
-/

namespace DomainSymbols

/-- Preserve source order and repetitions while dropping variable indices. -/
def extract (occurrences : List (ℕ × ℕ)) : List ℕ := occurrences.map Prod.snd

/-- Count the distinct smaller symbols, then use a one-based rank. -/
def rank (symbols : List ℕ) (value : ℕ) : ℕ :=
  ((symbols.filter fun symbol => decide (symbol < value)).dedup).length + 1

theorem extract_indexedDomainOccurrences (domains : List (List ℕ)) :
    extract (RuntimeStructuralView.indexedDomainOccurrences domains) = domains.flatten :=
  RuntimeStructuralView.indexedDomainOccurrences_values domains

theorem extract_ofRuntimeSystem (C : RuntimeSystem) :
    extract (RuntimeStructuralView.ofRuntimeSystem C).domainOccurrences = C.domains.flatten := by
  rw [RuntimeStructuralView.ofRuntimeSystem_domainOccurrences, extract_indexedDomainOccurrences]

/-- Repetitions within and between domains have exactly the existing set semantics. -/
theorem flatten_toFinset (C : RuntimeSystem) :
    C.domains.flatten.toFinset = C.toExplicitSystem.domainValues := by
  ext value
  simp only [List.mem_toFinset, List.mem_flatten,
    AllDifferentCSP.ExplicitSystem.mem_domainValues_iff]
  change (∃ domain ∈ C.domains, value ∈ domain) ↔
    ∃ index, value ∈ (C.domains.get index).toFinset
  simp only [List.mem_toFinset, List.exists_mem_iff_get]

theorem extract_toFinset (C : RuntimeSystem) :
    (extract (RuntimeStructuralView.ofRuntimeSystem C).domainOccurrences).toFinset =
      C.toExplicitSystem.domainValues := by
  rw [extract_ofRuntimeSystem, flatten_toFinset]

/-- The executable list rank counts a set of smaller values, not occurrences. -/
theorem rank_eq_card_filter (symbols : List ℕ) (value : ℕ) :
    rank symbols value = (symbols.toFinset.filter fun symbol => symbol < value).card + 1 := by
  rw [rank, ← List.toFinset_card_of_nodup (List.nodup_dedup _)]
  congr 2
  ext symbol
  simp

theorem rank_flatten_eq_relabelValue (C : RuntimeSystem) (value : ℕ) :
    rank C.domains.flatten value = C.toExplicitSystem.relabelValue value := by
  rw [rank_eq_card_filter, flatten_toFinset]
  rfl

/-- The structural occurrence stream determines exactly the semantic rank. -/
theorem rank_extract_eq_relabelValue (C : RuntimeSystem) (value : ℕ) :
    rank (extract (RuntimeStructuralView.ofRuntimeSystem C).domainOccurrences) value =
      C.toExplicitSystem.relabelValue value := by
  rw [extract_ofRuntimeSystem, rank_flatten_eq_relabelValue]

theorem rank_eq_iff (C : RuntimeSystem) {a b : ℕ}
    (ha : a ∈ C.domains.flatten) (hb : b ∈ C.domains.flatten) :
    rank C.domains.flatten a = rank C.domains.flatten b ↔ a = b := by
  rw [rank_flatten_eq_relabelValue, rank_flatten_eq_relabelValue]
  apply C.toExplicitSystem.relabelValue_eq_iff
  · rw [← flatten_toFinset]; exact List.mem_toFinset.mpr ha
  · rw [← flatten_toFinset]; exact List.mem_toFinset.mpr hb

/-- A rank emitted for an actual occurrence fits below the chosen prime. -/
theorem rank_lt_domainEntryPrime (C : RuntimeSystem) {value : ℕ}
    (hvalue : value ∈ C.domains.flatten) :
    rank C.domains.flatten value < C.domainEntryPrime := by
  rw [rank_flatten_eq_relabelValue]
  apply lt_of_le_of_lt (C.toExplicitSystem.relabelValue_le_symbolCount ?_)
    C.symbolCount_lt_domainEntryPrime
  rw [← flatten_toFinset]
  exact List.mem_toFinset.mpr hvalue

/-- Mapping a concrete domain by these list ranks gives exactly the compiler's
relabeled domain; duplicated entries disappear only at the set boundary. -/
theorem relabeled_domain (C : RuntimeSystem) (index : Fin C.domains.length) :
    ((C.domains.get index).map (rank C.domains.flatten)).toFinset =
      C.toExplicitSystem.relabeledDomain index := by
  ext value
  simp [AllDifferentCSP.ExplicitSystem.relabeledDomain,
    RuntimeSystem.toExplicitSystem, rank_flatten_eq_relabelValue]

/-- Regression example: two shared symbols keep their ranks across domains. -/
example : ([100, 7, 100, 42, 7].map (rank [100, 7, 100, 42, 7])) = [3, 1, 3, 2, 1] := by
  decide

#print axioms extract_toFinset
#print axioms rank_extract_eq_relabelValue
#print axioms rank_eq_iff
#print axioms rank_lt_domainEntryPrime
#print axioms relabeled_domain

end DomainSymbols

end PhdThesisLean.AllDifferentCSPEncoding
