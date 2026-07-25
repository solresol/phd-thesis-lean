import PhdThesisLean.AllDifferent

namespace PhdThesisLean.AllDifferentCSP

/-!
# Explicit finite-domain all-different systems

This module begins the statement-faithful formalisation of thesis Corollary
`cor:all-different-csp`.  It gives an executable, strongly typed input syntax
for explicitly listed finite domains and all-different scopes.  Variable
indices are already range checked by `Fin n`; domains and scopes are `Finset`s,
so duplicate values and duplicate variables inside one scope are eliminated by
the syntax itself.

The primal graph is constructed as a `Finset` of canonically oriented pairs.
Consequently, edges shared by several scopes (or repeated scopes) occur only
once.  The main semantic theorem `satisfies_iff_isProper` proves that satisfying
the original all-different scopes is exactly proper list-colouring of this
deduplicated graph.  The remaining compiler work is to relabel `domainValues`,
choose a prime, emit the p-adic dataset, and prove its encoded polynomial
runtime.
-/

/-- An explicitly represented finite-domain all-different constraint system.

Values are natural-number symbols.  Using the same natural number in different
domains preserves equality across those domains. -/
structure ExplicitSystem (n : ℕ) where
  domains : Fin n → Finset ℕ
  scopes : List (Finset (Fin n))

namespace ExplicitSystem

/-- The only remaining well-formedness condition after using typed variable
indices and finite-set domains/scopes: every variable has an allowed value. -/
def WellFormed {n : ℕ} (C : ExplicitSystem n) : Prop :=
  ∀ i, (C.domains i).Nonempty

/-- An assignment respects every explicitly listed variable domain. -/
def InDomain {n : ℕ} (C : ExplicitSystem n) (x : Fin n → ℕ) : Prop :=
  ∀ i, x i ∈ C.domains i

/-- All variables in one scope receive pairwise distinct values. -/
def AllDifferentOn {n : ℕ} (x : Fin n → ℕ)
    (scope : Finset (Fin n)) : Prop :=
  ∀ i ∈ scope, ∀ j ∈ scope, i ≠ j → x i ≠ x j

/-- Satisfaction of the explicitly listed domains and all-different scopes. -/
def Satisfies {n : ℕ} (C : ExplicitSystem n) (x : Fin n → ℕ) : Prop :=
  C.InDomain x ∧
    ∀ scope ∈ C.scopes, AllDifferentOn x scope

/-- The union of all explicitly listed domain symbols. -/
def domainValues {n : ℕ} (C : ExplicitSystem n) : Finset ℕ :=
  Finset.univ.biUnion C.domains

@[simp]
theorem mem_domainValues_iff {n : ℕ} (C : ExplicitSystem n) (a : ℕ) :
    a ∈ C.domainValues ↔ ∃ i, a ∈ C.domains i := by
  simp [domainValues]

/-- A well-formed system has at least one domain-respecting assignment.

This also handles the zero-variable system: its unique empty assignment
vacuously respects every domain. -/
theorem exists_inDomain {n : ℕ} (C : ExplicitSystem n)
    (hC : C.WellFormed) :
    ∃ x, C.InDomain x := by
  classical
  let x : Fin n → ℕ := fun i => (hC i).choose
  exact ⟨x, fun i => (hC i).choose_spec⟩

/-- The deduplicated primal graph, with every undirected edge represented once
in increasing endpoint order. -/
def primalEdges {n : ℕ} (C : ExplicitSystem n) :
    Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter fun e =>
    e.1 < e.2 ∧
      ∃ scope ∈ C.scopes, e.1 ∈ scope ∧ e.2 ∈ scope

@[simp]
theorem mem_primalEdges_iff {n : ℕ} (C : ExplicitSystem n)
    (i j : Fin n) :
    (i, j) ∈ C.primalEdges ↔
      i < j ∧ ∃ scope ∈ C.scopes, i ∈ scope ∧ j ∈ scope := by
  simp [primalEdges]

/-- The finite type of edges emitted by the primal-graph construction. -/
abbrev PrimalEdge {n : ℕ} (C : ExplicitSystem n) :=
  {e : Fin n × Fin n // e ∈ C.primalEdges}

def edgeLeft {n : ℕ} {C : ExplicitSystem n} (e : C.PrimalEdge) : Fin n :=
  e.1.1

def edgeRight {n : ℕ} {C : ExplicitSystem n} (e : C.PrimalEdge) : Fin n :=
  e.1.2

theorem edgeLeft_lt_edgeRight {n : ℕ} {C : ExplicitSystem n}
    (e : C.PrimalEdge) :
    edgeLeft e < edgeRight e :=
  (C.mem_primalEdges_iff (edgeLeft e) (edgeRight e)).mp e.2 |>.1

theorem edgeLeft_ne_edgeRight {n : ℕ} {C : ExplicitSystem n}
    (e : C.PrimalEdge) :
    edgeLeft e ≠ edgeRight e :=
  ne_of_lt (edgeLeft_lt_edgeRight e)

/-- Proper list-colouring of the deduplicated primal graph. -/
def IsProper {n : ℕ} (C : ExplicitSystem n) (x : Fin n → ℕ) : Prop :=
  C.InDomain x ∧
    ∀ e : C.PrimalEdge, x (edgeLeft e) ≠ x (edgeRight e)

/-- Scope satisfaction is exactly proper colouring of the deduplicated primal
graph.  In particular, repeated scopes and edges shared by several scopes do
not change the semantics. -/
theorem satisfies_iff_isProper {n : ℕ} (C : ExplicitSystem n)
    (x : Fin n → ℕ) :
    C.Satisfies x ↔ C.IsProper x := by
  constructor
  · rintro ⟨hxD, hxScopes⟩
    refine ⟨hxD, ?_⟩
    intro e
    obtain ⟨hlt, scope, hscope, hleft, hright⟩ :=
      (C.mem_primalEdges_iff (edgeLeft e) (edgeRight e)).mp e.2
    exact hxScopes scope hscope (edgeLeft e) hleft (edgeRight e) hright
      (ne_of_lt hlt)
  · rintro ⟨hxD, hxEdges⟩
    refine ⟨hxD, ?_⟩
    intro scope hscope i hi j hj hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have he : (i, j) ∈ C.primalEdges :=
        (C.mem_primalEdges_iff i j).2
          ⟨hijlt, scope, hscope, hi, hj⟩
      simpa [edgeLeft, edgeRight] using
        hxEdges (⟨(i, j), he⟩ : C.PrimalEdge)
    · have he : (j, i) ∈ C.primalEdges :=
        (C.mem_primalEdges_iff j i).2
          ⟨hjilt, scope, hscope, hj, hi⟩
      exact Ne.symm (by
        simpa [edgeLeft, edgeRight] using
          hxEdges (⟨(j, i), he⟩ : C.PrimalEdge))

/-- The deduplicated set of monochromatic primal-graph edges. -/
def conflictEdges {n : ℕ} (C : ExplicitSystem n)
    (x : Fin n → ℕ) : Finset (Fin n × Fin n) :=
  C.primalEdges.filter fun e => x e.1 = x e.2

/-- The number of violated deduplicated primal-graph edges. -/
def conflictCount {n : ℕ} (C : ExplicitSystem n)
    (x : Fin n → ℕ) : ℕ :=
  (C.conflictEdges x).card

theorem conflictCount_eq_zero_iff {n : ℕ} (C : ExplicitSystem n)
    (x : Fin n → ℕ) :
    C.conflictCount x = 0 ↔
      ∀ e : C.PrimalEdge, x (edgeLeft e) ≠ x (edgeRight e) := by
  rw [conflictCount, Finset.card_eq_zero]
  constructor
  · intro hempty e heq
    have heq' : x e.1.1 = x e.1.2 := by
      simpa [edgeLeft, edgeRight] using heq
    have he : e.1 ∈ C.conflictEdges x := by
      exact Finset.mem_filter.mpr ⟨e.2, heq'⟩
    rw [hempty] at he
    simp at he
  · intro hproper
    by_contra hne
    obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨heEdge, heq⟩ := Finset.mem_filter.mp he
    exact hproper (⟨e, heEdge⟩ : C.PrimalEdge) heq

theorem satisfies_iff_inDomain_and_conflictCount_eq_zero
    {n : ℕ} (C : ExplicitSystem n) (x : Fin n → ℕ) :
    C.Satisfies x ↔ C.InDomain x ∧ C.conflictCount x = 0 := by
  rw [C.satisfies_iff_isProper]
  exact and_congr_right fun _ => (C.conflictCount_eq_zero_iff x).symm

/-- A domain-respecting assignment of least deduplicated edge-conflict count. -/
def MinimizesConflicts {n : ℕ} (C : ExplicitSystem n)
    (x : Fin n → ℕ) : Prop :=
  C.InDomain x ∧
    ∀ y, C.InDomain y → C.conflictCount x ≤ C.conflictCount y

/-- If the explicit all-different system is satisfiable, its minimum-conflict
assignments are exactly its satisfying assignments. -/
theorem minimizesConflicts_iff_satisfies_of_satisfiable
    {n : ℕ} (C : ExplicitSystem n)
    (hsat : ∃ y, C.Satisfies y) (x : Fin n → ℕ) :
    C.MinimizesConflicts x ↔ C.Satisfies x := by
  obtain ⟨y, hy⟩ := hsat
  have hy' := (C.satisfies_iff_inDomain_and_conflictCount_eq_zero y).mp hy
  constructor
  · rintro ⟨hxD, hxMin⟩
    have hxle : C.conflictCount x ≤ 0 := by
      simpa [hy'.2] using hxMin y hy'.1
    have hxzero : C.conflictCount x = 0 := Nat.eq_zero_of_le_zero hxle
    exact (C.satisfies_iff_inDomain_and_conflictCount_eq_zero x).2
      ⟨hxD, hxzero⟩
  · intro hx
    have hx' :=
      (C.satisfies_iff_inDomain_and_conflictCount_eq_zero x).mp hx
    refine ⟨hx'.1, ?_⟩
    intro z _
    rw [hx'.2]
    exact Nat.zero_le _

end ExplicitSystem

#print axioms ExplicitSystem.satisfies_iff_isProper
#print axioms ExplicitSystem.minimizesConflicts_iff_satisfies_of_satisfiable

end PhdThesisLean.AllDifferentCSP
