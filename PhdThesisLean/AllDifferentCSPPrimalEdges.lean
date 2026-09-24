import PhdThesisLean.AllDifferentCSPRelabelling

/-!
# Ordered primal-edge enumeration from retained scopes

Scan the bounded variable-pair grid in lexicographic order. A pair survives
exactly when its endpoints increase and occur together in a scope. The scan
emits each edge once even when scopes or entries repeat, with no sorting or
deduplication pass. These executable definitions and correspondence lemmas
specify the finite-machine target; they do not claim a machine runtime bound.
-/

namespace PhdThesisLean.AllDifferentCSPEncoding

open AllDifferentCSP

namespace PrimalEdgeEnumeration

/-- Test co-occurrence in the original scope lists, retaining their set semantics. -/
def adjacent (scopes : List (List ℕ)) (i j : ℕ) : Bool :=
  scopes.any fun scope => scope.contains i && scope.contains j

@[simp]
theorem adjacent_eq_true (scopes : List (List ℕ)) (i j : ℕ) :
    adjacent scopes i j = true ↔ ∃ scope ∈ scopes, i ∈ scope ∧ j ∈ scope := by
  simp [adjacent]

/-- Every bounded pair in increasing lexicographic scan order. -/
def candidates (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i => (List.range n).map fun j => (i, j)

@[simp]
theorem mem_candidates (n i j : ℕ) :
    (i, j) ∈ candidates n ↔ i < n ∧ j < n := by
  simp [candidates]

theorem candidates_length (n : ℕ) : (candidates n).length = n ^ 2 := by
  simp [candidates, List.length_flatMap, pow_two]

/-- Each candidate is tested once, independently of scope repetitions. -/
def enumerate (n : ℕ) (scopes : List (List ℕ)) : List (ℕ × ℕ) :=
  (candidates n).filter fun edge => decide (edge.1 < edge.2) && adjacent scopes edge.1 edge.2

@[simp]
theorem mem_enumerate (n : ℕ) (scopes : List (List ℕ)) (i j : ℕ) :
    (i, j) ∈ enumerate n scopes ↔
      i < n ∧ j < n ∧ i < j ∧ ∃ scope ∈ scopes, i ∈ scope ∧ j ∈ scope := by
  simp [enumerate, and_assoc]

/-- The grid is strictly ordered, so a filtered scan never repeats a pair. -/
theorem candidates_pairwise (n : ℕ) :
    (candidates n).Pairwise (Prod.Lex (· < ·) (· < ·)) := by
  rw [candidates, List.pairwise_flatMap]
  constructor
  · intro i _
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun h => Prod.Lex.right _ h
  · apply List.pairwise_lt_range.imp
    intro i j hij a ha b hb
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
    exact Prod.Lex.left _ _ hij

theorem enumerate_pairwise (n : ℕ) (scopes : List (List ℕ)) :
    (enumerate n scopes).Pairwise (Prod.Lex (· < ·) (· < ·)) :=
  (candidates_pairwise n).filter _

theorem enumerate_nodup (n : ℕ) (scopes : List (List ℕ)) :
    (enumerate n scopes).Nodup :=
  (enumerate_pairwise n scopes).nodup

theorem enumerate_length_le (n : ℕ) (scopes : List (List ℕ)) :
    (enumerate n scopes).length ≤ n ^ 2 := by
  exact (List.length_filter_le _ _).trans_eq (candidates_length n)

/-- Range-filtering in the semantic front end agrees even on malformed scopes. -/
@[simp]
theorem mem_scopeFinset (n : ℕ) (scope : List ℕ) (i : Fin n) :
    i ∈ RuntimeSystem.scopeFinset n scope ↔ i.val ∈ scope := by
  simp only [RuntimeSystem.scopeFinset, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, heq⟩
    split at heq
    · cases Option.some.inj heq
      exact hj
    · cases heq
  · intro hi
    exact ⟨i.val, hi, by simp [i.isLt]⟩

/-- Exact membership correspondence with the thesis's deduplicated graph. -/
theorem mem_enumerate_iff_primalEdges (C : RuntimeSystem)
    (i j : Fin C.domains.length) :
    (i.val, j.val) ∈ enumerate C.domains.length C.scopes ↔
      (i, j) ∈ C.toExplicitSystem.primalEdges := by
  rw [mem_enumerate, ExplicitSystem.mem_primalEdges_iff]
  simp only [i.isLt, j.isLt, true_and, RuntimeSystem.toExplicitSystem,
    List.mem_map, exists_exists_and_eq_and, mem_scopeFinset]
  rfl

/-- Erase finite endpoint proofs without identifying different edges. -/
def eraseEdge (n : ℕ) : (Fin n × Fin n) ↪ (ℕ × ℕ) where
  toFun edge := (edge.1.val, edge.2.val)
  inj' := by
    intro a b h
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst h)
    · exact Fin.ext (congrArg Prod.snd h)

theorem enumerate_toFinset (C : RuntimeSystem) :
    (enumerate C.domains.length C.scopes).toFinset =
      C.toExplicitSystem.primalEdges.map (eraseEdge C.domains.length) := by
  ext ⟨i, j⟩
  simp only [List.mem_toFinset, Finset.mem_map]
  constructor
  · intro h
    have hb := (mem_enumerate _ _ i j).mp h
    refine ⟨(⟨i, hb.1⟩, ⟨j, hb.2.1⟩), ?_, rfl⟩
    exact (mem_enumerate_iff_primalEdges C _ _).mp h
  · rintro ⟨⟨i, j⟩, he, heq⟩
    cases heq
    exact (mem_enumerate_iff_primalEdges C i j).mpr he

/-- Exact list order, not merely equality of the underlying edge sets. This is
also the order used by the semantic compiler's negative residual rows. -/
theorem enumerate_eq_sorted_primalEdges (C : RuntimeSystem) :
    enumerate C.domains.length C.scopes =
      (C.toExplicitSystem.primalEdges.sort (Prod.Lex (· < ·) (· ≤ ·))).map
        (eraseEdge C.domains.length) := by
  rw [Finset.map_sort (eraseEdge C.domains.length) _
    (Prod.Lex (· < ·) (· ≤ ·)) (Prod.Lex (· < ·) (· ≤ ·))]
  · rw [← enumerate_toFinset]
    symm
    apply (List.toFinset_sort (Prod.Lex (· < ·) (· ≤ ·))
      (enumerate_nodup _ _)).mpr
    apply (enumerate_pairwise _ _).imp
    intro a b h
    rcases Prod.lex_iff.mp h with hlt | ⟨heq, hlt⟩
    · exact Prod.lex_iff.mpr (Or.inl hlt)
    · exact Prod.lex_iff.mpr (Or.inr ⟨heq, hlt.le⟩)
  · intro a _ b _
    simp only [Prod.lex_iff, Fin.lt_def, Fin.le_def, Fin.ext_iff]
    rfl

/-- The exact compiler target, on the scopes retained by domain relabelling. -/
def ofRuntimeSystem (C : RuntimeSystem) : List (ℕ × ℕ) :=
  enumerate C.domains.length C.scopes

theorem enumerate_relabelledSections (C : RuntimeSystem) :
    enumerate (AllDifferentCSPMachine.CountedRelabelledSections.ofRuntimeSystem C).2
      (AllDifferentCSPMachine.CountedRelabelledSections.ofRuntimeSystem C).1.2 =
      ofRuntimeSystem C := rfl

example : enumerate 4 [[2, 0, 2], [], [0, 2], [3], [1, 3, 2], [99, 0]] =
    [(0, 2), (1, 2), (1, 3), (2, 3)] := by decide
example : enumerate 0 [[0, 1]] = [] := by decide
example : enumerate 3 [[1, 1], [], [2]] = [] := by decide

#print axioms mem_enumerate_iff_primalEdges
#print axioms enumerate_eq_sorted_primalEdges
#print axioms enumerate_nodup
#print axioms enumerate_length_le
#print axioms enumerate_relabelledSections

end PrimalEdgeEnumeration

end PhdThesisLean.AllDifferentCSPEncoding
