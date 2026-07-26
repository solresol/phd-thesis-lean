import PhdThesisLean.AllDifferent
import Mathlib.Order.Interval.Finset.Nat

namespace PhdThesisLean.AllDifferentCSP

open scoped BigOperators

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
deduplicated graph.  The executable rank relabelling maps the union of domain
symbols onto `{1, ..., q}` and preserves equality, satisfaction, and minimum
conflict. The remaining compiler work is to choose a prime, emit the p-adic
dataset, and prove its encoded polynomial runtime.
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

/-- The number of distinct symbols occurring anywhere in the input domains. -/
def symbolCount {n : ℕ} (C : ExplicitSystem n) : ℕ :=
  C.domainValues.card

/-- The number of distinct symbols is at most the number of explicitly listed
domain entries. Shared symbols are counted only once on the left. -/
theorem symbolCount_le_sum_domain_card {n : ℕ} (C : ExplicitSystem n) :
    C.symbolCount ≤ ∑ i, (C.domains i).card := by
  exact Finset.card_biUnion_le

/-- The canonical one-based rank of a domain symbol in the ordered union of
all explicitly listed values. The definition is executable and independent of
the variable domain in which the symbol occurs. -/
def relabelValue {n : ℕ} (C : ExplicitSystem n) (a : ℕ) : ℕ :=
  (C.domainValues.filter fun b => b < a).card + 1

theorem relabelValue_pos {n : ℕ} (C : ExplicitSystem n) (a : ℕ) :
    0 < C.relabelValue a := by
  simp [relabelValue]

theorem relabelValue_le_symbolCount {n : ℕ} (C : ExplicitSystem n)
    {a : ℕ} (ha : a ∈ C.domainValues) :
    C.relabelValue a ≤ C.symbolCount := by
  have hsubset :
      C.domainValues.filter (fun b => b < a) ⊆
        C.domainValues :=
    Finset.filter_subset _ _
  have hstrict :
      C.domainValues.filter (fun b => b < a) ⊂ C.domainValues := by
    rw [Finset.ssubset_iff_of_subset hsubset]
    exact ⟨a, ha, by simp⟩
  simpa [relabelValue, symbolCount] using Finset.card_lt_card hstrict

theorem relabelValue_lt {n : ℕ} (C : ExplicitSystem n)
    {a b : ℕ} (ha : a ∈ C.domainValues) (hab : a < b) :
    C.relabelValue a < C.relabelValue b := by
  have hsubset :
      C.domainValues.filter (fun c => c < a) ⊆
        C.domainValues.filter (fun c => c < b) := by
    intro c hc
    obtain ⟨hcD, hca⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨hcD, hca.trans hab⟩
  have hstrict :
      C.domainValues.filter (fun c => c < a) ⊂
        C.domainValues.filter (fun c => c < b) := by
    rw [Finset.ssubset_iff_of_subset hsubset]
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, hab⟩, by simp⟩
  have hcard := Finset.card_lt_card hstrict
  simp only [relabelValue]
  omega

/-- Canonical ranks are injective on the union of domain symbols. -/
theorem relabelValue_injective {n : ℕ} (C : ExplicitSystem n)
    {a b : ℕ} (ha : a ∈ C.domainValues) (hb : b ∈ C.domainValues)
    (h : C.relabelValue a = C.relabelValue b) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact False.elim ((ne_of_lt (C.relabelValue_lt ha hab)) h)
  · exact hab
  · exact False.elim ((ne_of_lt (C.relabelValue_lt hb hba)) h.symm)

theorem relabelValue_eq_iff {n : ℕ} (C : ExplicitSystem n)
    {a b : ℕ} (ha : a ∈ C.domainValues) (hb : b ∈ C.domainValues) :
    C.relabelValue a = C.relabelValue b ↔ a = b := by
  exact ⟨C.relabelValue_injective ha hb, congrArg C.relabelValue⟩

/-- The image of all input symbols under canonical rank relabelling. -/
def relabeledValues {n : ℕ} (C : ExplicitSystem n) : Finset ℕ :=
  C.domainValues.image C.relabelValue

theorem card_relabeledValues {n : ℕ} (C : ExplicitSystem n) :
    C.relabeledValues.card = C.symbolCount := by
  rw [relabeledValues, symbolCount, Finset.card_image_iff]
  intro a ha b hb h
  exact C.relabelValue_injective ha hb h

/-- Canonical relabelling maps the distinct input symbols onto exactly
`{1, ..., q}`, where `q` is `symbolCount`. This theorem includes the empty
union case (`q = 0`). -/
theorem relabeledValues_eq_Icc {n : ℕ} (C : ExplicitSystem n) :
    C.relabeledValues = Finset.Icc 1 C.symbolCount := by
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_Icc.mpr
      ⟨C.relabelValue_pos a, C.relabelValue_le_symbolCount ha⟩
  · rw [Nat.card_Icc, C.card_relabeledValues]
    omega

/-- Explicit zero-symbol edge case for canonical relabelling. -/
theorem relabeledValues_eq_empty_of_symbolCount_eq_zero
    {n : ℕ} (C : ExplicitSystem n) (h : C.symbolCount = 0) :
    C.relabeledValues = ∅ := by
  rw [C.relabeledValues_eq_Icc, h]
  simp

/-- Explicit one-symbol edge case for canonical relabelling. -/
theorem relabeledValues_eq_singleton_of_symbolCount_eq_one
    {n : ℕ} (C : ExplicitSystem n) (h : C.symbolCount = 1) :
    C.relabeledValues = {1} := by
  rw [C.relabeledValues_eq_Icc, h]
  norm_num

/-- A variable domain after canonical one-based rank relabelling. -/
def relabeledDomain {n : ℕ} (C : ExplicitSystem n)
    (i : Fin n) : Finset ℕ :=
  (C.domains i).image C.relabelValue

/-- The whole constraint system after canonical value relabelling. Scopes, and
hence the deduplicated primal graph, are unchanged. -/
def relabeled {n : ℕ} (C : ExplicitSystem n) : ExplicitSystem n where
  domains := C.relabeledDomain
  scopes := C.scopes

@[simp]
theorem relabeled_domains {n : ℕ} (C : ExplicitSystem n) (i : Fin n) :
    C.relabeled.domains i = C.relabeledDomain i :=
  rfl

@[simp]
theorem relabeled_scopes {n : ℕ} (C : ExplicitSystem n) :
    C.relabeled.scopes = C.scopes :=
  rfl

theorem domainValues_relabeled {n : ℕ} (C : ExplicitSystem n) :
    C.relabeled.domainValues = C.relabeledValues := by
  ext r
  simp only [mem_domainValues_iff, relabeled_domains, relabeledDomain,
    Finset.mem_image, relabeledValues]
  constructor
  · rintro ⟨i, a, ha, rfl⟩
    exact ⟨a, ⟨i, ha⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, hai⟩ := ha
    exact ⟨i, a, hai, rfl⟩

theorem domainValues_relabeled_eq_Icc {n : ℕ} (C : ExplicitSystem n) :
    C.relabeled.domainValues = Finset.Icc 1 C.symbolCount := by
  rw [C.domainValues_relabeled, C.relabeledValues_eq_Icc]

theorem relabeled_wellFormed {n : ℕ} (C : ExplicitSystem n)
    (hC : C.WellFormed) :
    C.relabeled.WellFormed := by
  intro i
  obtain ⟨a, ha⟩ := hC i
  exact ⟨C.relabelValue a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩

/-- Pointwise application of canonical rank relabelling to an assignment. -/
def relabelAssignment {n : ℕ} (C : ExplicitSystem n)
    (x : Fin n → ℕ) : Fin n → ℕ :=
  fun i => C.relabelValue (x i)

theorem relabelAssignment_inDomain {n : ℕ} (C : ExplicitSystem n)
    {x : Fin n → ℕ} (hx : C.InDomain x) :
    C.relabeled.InDomain (C.relabelAssignment x) := by
  intro i
  exact Finset.mem_image.mpr ⟨x i, hx i, rfl⟩

/-- Every assignment in the relabelled product domain has an original
domain-respecting preimage. This supplies the inverse direction needed for
minimum-conflict and satisfiability equivalences without making the compiler's
forward relabelling noncomputable. -/
theorem exists_inDomain_relabelAssignment_eq {n : ℕ}
    (C : ExplicitSystem n) {y : Fin n → ℕ}
    (hy : C.relabeled.InDomain y) :
    ∃ x, C.InDomain x ∧ C.relabelAssignment x = y := by
  classical
  have hchoice :
      ∀ i, ∃ a, a ∈ C.domains i ∧ C.relabelValue a = y i := by
    intro i
    simpa [relabeled, relabeledDomain] using hy i
  choose x hx using hchoice
  exact ⟨x, fun i => (hx i).1, funext fun i => (hx i).2⟩

theorem relabelAssignment_eq_iff_of_inDomain {n : ℕ}
    (C : ExplicitSystem n) {x : Fin n → ℕ}
    (hx : C.InDomain x) (i j : Fin n) :
    C.relabelAssignment x i = C.relabelAssignment x j ↔ x i = x j := by
  apply C.relabelValue_eq_iff
  · exact (C.mem_domainValues_iff (x i)).2 ⟨i, hx i⟩
  · exact (C.mem_domainValues_iff (x j)).2 ⟨j, hx j⟩

theorem allDifferentOn_relabelAssignment_iff {n : ℕ}
    (C : ExplicitSystem n) {x : Fin n → ℕ}
    (hx : C.InDomain x) (scope : Finset (Fin n)) :
    AllDifferentOn (C.relabelAssignment x) scope ↔
      AllDifferentOn x scope := by
  constructor
  · intro h i hi j hj hij hEq
    exact h i hi j hj hij (congrArg C.relabelValue hEq)
  · intro h i hi j hj hij hEq
    exact h i hi j hj hij
      ((C.relabelAssignment_eq_iff_of_inDomain hx i j).mp hEq)

/-- Satisfaction is preserved and reflected by canonical relabelling on every
domain-respecting original assignment. -/
theorem relabeled_satisfies_relabelAssignment_iff {n : ℕ}
    (C : ExplicitSystem n) {x : Fin n → ℕ}
    (hx : C.InDomain x) :
    C.relabeled.Satisfies (C.relabelAssignment x) ↔ C.Satisfies x := by
  constructor
  · rintro ⟨_, hscopes⟩
    refine ⟨hx, ?_⟩
    intro scope hscope
    exact (C.allDifferentOn_relabelAssignment_iff hx scope).mp
      (hscopes scope hscope)
  · rintro ⟨_, hscopes⟩
    refine ⟨C.relabelAssignment_inDomain hx, ?_⟩
    intro scope hscope
    exact (C.allDifferentOn_relabelAssignment_iff hx scope).mpr
      (hscopes scope hscope)

theorem relabeled_satisfiable_iff {n : ℕ} (C : ExplicitSystem n) :
    (∃ y, C.relabeled.Satisfies y) ↔ ∃ x, C.Satisfies x := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ :=
      C.exists_inDomain_relabelAssignment_eq hy.1
    exact ⟨x, (C.relabeled_satisfies_relabelAssignment_iff hx).mp hy⟩
  · rintro ⟨x, hx⟩
    exact ⟨C.relabelAssignment x,
      (C.relabeled_satisfies_relabelAssignment_iff hx.1).mpr hx⟩

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

@[simp]
theorem primalEdges_relabeled {n : ℕ} (C : ExplicitSystem n) :
    C.relabeled.primalEdges = C.primalEdges :=
  rfl

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

theorem conflictEdges_relabelAssignment {n : ℕ}
    (C : ExplicitSystem n) {x : Fin n → ℕ} (hx : C.InDomain x) :
    C.relabeled.conflictEdges (C.relabelAssignment x) =
      C.conflictEdges x := by
  ext e
  simp only [conflictEdges, Finset.mem_filter, C.primalEdges_relabeled]
  exact and_congr_right fun _ =>
    C.relabelAssignment_eq_iff_of_inDomain hx e.1 e.2

theorem conflictCount_relabelAssignment {n : ℕ}
    (C : ExplicitSystem n) {x : Fin n → ℕ} (hx : C.InDomain x) :
    C.relabeled.conflictCount (C.relabelAssignment x) =
      C.conflictCount x := by
  rw [conflictCount, conflictCount, C.conflictEdges_relabelAssignment hx]

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

/-- Minimum deduplicated conflict count is preserved and reflected by
canonical relabelling. -/
theorem relabeled_minimizesConflicts_relabelAssignment_iff {n : ℕ}
    (C : ExplicitSystem n) {x : Fin n → ℕ} (hx : C.InDomain x) :
    C.relabeled.MinimizesConflicts (C.relabelAssignment x) ↔
      C.MinimizesConflicts x := by
  constructor
  · rintro ⟨_, hmin⟩
    refine ⟨hx, ?_⟩
    intro y hy
    have hle := hmin (C.relabelAssignment y)
      (C.relabelAssignment_inDomain hy)
    simpa only [C.conflictCount_relabelAssignment hx,
      C.conflictCount_relabelAssignment hy] using hle
  · rintro ⟨_, hmin⟩
    refine ⟨C.relabelAssignment_inDomain hx, ?_⟩
    intro y hy
    obtain ⟨z, hz, rfl⟩ := C.exists_inDomain_relabelAssignment_eq hy
    simpa only [C.conflictCount_relabelAssignment hx,
      C.conflictCount_relabelAssignment hz] using hmin z hz

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
#print axioms ExplicitSystem.relabeledValues_eq_Icc
#print axioms ExplicitSystem.relabeled_minimizesConflicts_relabelAssignment_iff

end PhdThesisLean.AllDifferentCSP
