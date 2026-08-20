import PhdThesisLean.AllDifferent
import Mathlib.NumberTheory.Bertrand
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
conflict. After the supplied-prime semantic stage, the remaining compiler work
uses an executable bounded scan to select a prime, then composes that choice
with the p-adic correctness theorem. The compiler now emits a finite sparse
row list and proves that interpreting it is exactly the checked objective.
`compileObjectiveAt` exposes the same prime-independent rows under any supplied
prime header, so a runtime front end may select a prime above a checked input-
length-bounded overestimate of the distinct-symbol count.
The separate `AllDifferentCSPEncoding` module supplies standard binary
`FinEncoding`s and a complete polynomial output-size bound.
`AllDifferentCSPMachine` starts the finite-machine layer with checked linear
passes from raw binary naturals to the self-delimiting field encoding and from
a stack-oriented raw-natural stream to the exact framed list encoding. It also
checks the reverse traversal from the standard nested-list encoding to an
explicit delimited raw-field stream, and supplies linear-time successor and
less-than-or-equal machines on canonical binary naturals, plus a linear-time
ripple-carry adder on their aligned-pair encoding. Its unary-bound Bertrand
enumerator emits exactly `[q + 1, ..., 2q]` in quadratic time, making explicit
the eventual full-input invariant `q ≤ input length`. Its companion unary
producer emits that same candidate list in a checked delimiter encoding in at
most `6(q+1)^2` steps and bounds the stream by `2q^2+2q+1` cells, matching the
native input of the candidate-primality pass. Its checked unary-padded
divisibility machine handles every natural pair in time linear in the padded
pair length. Its executable trial-division specification tests exactly the
divisors in `[2, n)`, filters the enumerated Bertrand candidates, and proves
that the first survivor is `selectPrimeAbove`. A checked quadratic-time finite
machine emits the complete stack-oriented list of padded pairs
`(n,2), ..., (n,n-1)`, including the empty small-`n` cases. The checked
`pairDivisionResultsComputableInPolyTime` driver consumes that representation,
runs the divisibility program on every field, and emits the exact result stream
in at most `17s + 1` steps for encoded stream length `s`; the concrete trial
stream is quadratically bounded. A checked linear-time Boolean fold accepts
exactly when none of those results is true, and its trial-result bridge is
equivalent to primality for `n ≥ 2`. The fused
`allFalseDivisibilityResultsComputableInPolyTime` machine consumes the padded
pair stream directly, invokes divisibility for every field, keeps the fold in
finite control, and emits the exact no-divisor bit in at most `18s + 1` steps;
on `trialDivisionPairs n` that bit accepts exactly the primes for `n ≥ 2`.
The composed `unaryCandidatePrimeComputableInPolyTime` machine now generates
that pair stream and runs the fused pass, computing the candidate-only bit in
at most `64(n+1)^2` steps on unary `n`; for `n ≥ 2`, the bit is true exactly
when `n` is prime. The generated-stream invariant proves every Bertrand
candidate is at least two and that filtering with this machine predicate gives
exactly the guarded semantic prime-candidate list. The checked
`primeSelectorComputableInPolyTime` driver consumes that unary-delimited list,
runs the candidate-primality component once per value field, and emits the
first source-order survivor in polynomial time in the complete stream length;
on the Bertrand stream it is exactly `selectPrimeAbove`, including the empty
`q = 0` convention. `selectedPrimeComputableInPolyTime` composes the producer
and selector into one unary-`q` machine for `selectPrimeAbove`, bounded by
`1000(q+1)^6` steps. The runtime encoding now selects its prime above the
explicit domain-entry count, proves this bounds the distinct-symbol count, and
retains the complete quartic output-size and exact semantic theorems. A
compiler-facing Boolean encoding now carries that occurrence count in a
decoder-checked unary header; a linear finite machine extracts it, and checked
generic composition computes the same runtime prime used by the semantic
compiler. Encoded objective emission and final whole-compiler composition
remain.
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

/-- The finite interval scanned for a prime strictly above `q`.

For positive `q`, Bertrand's postulate guarantees that this set is nonempty.
Keeping the scan as an executable `Finset` separates the prime-selection
algorithm from its later bit-level running-time proof. -/
def primeCandidates (q : ℕ) : Finset ℕ :=
  (Finset.Icc (q + 1) (2 * q)).filter Nat.Prime

@[simp]
theorem mem_primeCandidates_iff (q p : ℕ) :
    p ∈ primeCandidates q ↔ p.Prime ∧ q < p ∧ p ≤ 2 * q := by
  simp [primeCandidates, Nat.lt_iff_add_one_le, and_comm]

theorem primeCandidates_nonempty {q : ℕ} (hq : q ≠ 0) :
    (primeCandidates q).Nonempty := by
  obtain ⟨p, hp, hqp, hpq⟩ :=
    Nat.exists_prime_lt_and_le_two_mul q hq
  exact ⟨p, (mem_primeCandidates_iff q p).2 ⟨hp, hqp, hpq⟩⟩

/-- The prime selected by the explicit compiler.

At `q = 0` the selector returns `2`. At positive `q` it scans the Bertrand
interval and returns its least prime. The separate machine module proves a
polynomial-time unary-bound implementation; producing that unary bound from
the explicit CSP remains a compiler obligation. -/
def selectPrimeAbove (q : ℕ) : ℕ :=
  if hq : q = 0 then
    2
  else
    (primeCandidates q).min' (primeCandidates_nonempty hq)

@[simp]
theorem selectPrimeAbove_zero : selectPrimeAbove 0 = 2 := by
  simp [selectPrimeAbove]

theorem selectPrimeAbove_mem_primeCandidates {q : ℕ} (hq : q ≠ 0) :
    selectPrimeAbove q ∈ primeCandidates q := by
  rw [selectPrimeAbove, dif_neg hq]
  exact Finset.min'_mem _ _

theorem selectPrimeAbove_prime (q : ℕ) :
    (selectPrimeAbove q).Prime := by
  by_cases hq : q = 0
  · subst q
    norm_num
  · exact ((mem_primeCandidates_iff q (selectPrimeAbove q)).1
      (selectPrimeAbove_mem_primeCandidates hq)).1

theorem lt_selectPrimeAbove (q : ℕ) :
    q < selectPrimeAbove q := by
  by_cases hq : q = 0
  · subst q
    norm_num
  · exact ((mem_primeCandidates_iff q (selectPrimeAbove q)).1
      (selectPrimeAbove_mem_primeCandidates hq)).2.1

theorem selectPrimeAbove_le_two_mul {q : ℕ} (hq : q ≠ 0) :
    selectPrimeAbove q ≤ 2 * q :=
  ((mem_primeCandidates_iff q (selectPrimeAbove q)).1
    (selectPrimeAbove_mem_primeCandidates hq)).2.2

/-- For the nontrivial `q > 1` branch, the selected prime is strictly below
`2q`; equality would make it the product of two non-units. -/
theorem selectPrimeAbove_lt_two_mul {q : ℕ} (hq : 1 < q) :
    selectPrimeAbove q < 2 * q := by
  have hle := selectPrimeAbove_le_two_mul (by omega : q ≠ 0)
  have hne : selectPrimeAbove q ≠ 2 * q := by
    intro heq
    have hp := selectPrimeAbove_prime q
    rw [heq] at hp
    exact Nat.not_prime_mul (by omega) (by omega) hp
  omega

@[simp]
theorem selectPrimeAbove_one : selectPrimeAbove 1 = 2 := by
  have hgt := lt_selectPrimeAbove 1
  have hle := selectPrimeAbove_le_two_mul (by norm_num : (1 : ℕ) ≠ 0)
  omega

/-- The compiler-selected prime for an explicit system. -/
def compilerPrime {n : ℕ} (C : ExplicitSystem n) : ℕ :=
  selectPrimeAbove C.symbolCount

theorem compilerPrime_prime {n : ℕ} (C : ExplicitSystem n) :
    C.compilerPrime.Prime :=
  selectPrimeAbove_prime C.symbolCount

theorem symbolCount_lt_compilerPrime {n : ℕ} (C : ExplicitSystem n) :
    C.symbolCount < C.compilerPrime :=
  lt_selectPrimeAbove C.symbolCount

theorem compilerPrime_lt_two_mul_symbolCount {n : ℕ}
    (C : ExplicitSystem n) (hq : 1 < C.symbolCount) :
    C.compilerPrime < 2 * C.symbolCount :=
  selectPrimeAbove_lt_two_mul hq

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

theorem card_relabeledDomain {n : ℕ} (C : ExplicitSystem n)
    (i : Fin n) :
    (C.relabeledDomain i).card = (C.domains i).card := by
  rw [relabeledDomain, Finset.card_image_iff]
  intro a ha b hb h
  exact C.relabelValue_injective
    ((C.mem_domainValues_iff a).2 ⟨i, ha⟩)
    ((C.mem_domainValues_iff b).2 ⟨i, hb⟩) h

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

/-- The canonically relabelled domain embedded in the supplied p-adic field.

This is an intermediate compiler stage: `p` is supplied together with its
primality proof, rather than selected by the compiler. -/
noncomputable def padicDomain
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    (i : Fin n) : Finset ℚ_[p] := by
  classical
  exact (C.relabeledDomain i).image fun a : ℕ => (a : ℚ_[p])

theorem unaryCost_padicDomain
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    (i : Fin n) (z : ℚ_[p]) :
    PhdThesisLean.FiniteDomainCompiler.unaryCost
        (C.padicDomain (p := p) i) z =
      ∑ a ∈ C.relabeledDomain i, ‖z - (a : ℚ_[p])‖ := by
  classical
  rw [PhdThesisLean.FiniteDomainCompiler.unaryCost, padicDomain,
    Finset.sum_image]
  intro a _ b _ hab
  exact Nat.cast_injective (R := ℚ_[p]) hab

/-- An original assignment, canonically relabelled and embedded in `ℚ_[p]`. -/
def padicAssignment
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    (x : Fin n → ℕ) :
    PhdThesisLean.FiniteDomainCompiler.Parameter p n :=
  fun i => (C.relabelAssignment x i : ℚ_[p])

/-- One plus the number of deduplicated primal edges. This simple uniform
pinning weight dominates every vertex's unit incident-edge weight. -/
def pinningWeight {n : ℕ} (C : ExplicitSystem n) : ℕ :=
  C.primalEdges.card + 1

/-- Finite sparse row syntax emitted by the all-different compiler.

`pin i a w` represents the positive weighted residual `w * ‖xᵢ - a‖`.
`unequal i j` represents the negative unit-weight residual
`-‖xᵢ - xⱼ‖`. The compiler emits only canonically oriented unequal rows,
although the syntax remains total for arbitrary endpoints. -/
inductive ResidualRow (n : ℕ) where
  | pin (index : Fin n) (target weight : ℕ)
  | unequal (left right : Fin n)
  deriving DecidableEq, Repr

namespace ResidualRow

/-- Interpret a finite compiler row as a signed weighted affine observation. -/
noncomputable def observation
    {n p : ℕ} [Fact p.Prime] :
    ResidualRow n →
      PhdThesisLean.FiniteDomainCompiler.AffineObservation p n
  | .pin i a w => {
      sign := 1
      weight := w
      coeff := fun j => if j = i then 1 else 0
      target := a
    }
  | .unequal i j =>
      PhdThesisLean.AllDifferent.edgeObservation
        (fun _ : Unit => i) (fun _ : Unit => j) (fun _ : Unit => 1) ()

/-- The signed p-adic contribution of one interpreted compiler row. -/
noncomputable def loss
    {n p : ℕ} [Fact p.Prime] (row : ResidualRow n)
    (z : PhdThesisLean.FiniteDomainCompiler.Parameter p n) : ℝ :=
  let t := row.observation (p := p)
  t.sign * t.weight *
    ‖PhdThesisLean.FiniteDomainCompiler.affineResidual t z‖

@[simp]
theorem affineResidual_pin
    {n p : ℕ} [Fact p.Prime] (i : Fin n) (a w : ℕ)
    (z : PhdThesisLean.FiniteDomainCompiler.Parameter p n) :
    PhdThesisLean.FiniteDomainCompiler.affineResidual
        ((ResidualRow.pin i a w).observation (p := p)) z =
      z i - (a : ℚ_[p]) := by
  classical
  simp [observation, PhdThesisLean.FiniteDomainCompiler.affineResidual]

@[simp]
theorem loss_pin
    {n p : ℕ} [Fact p.Prime] (i : Fin n) (a w : ℕ)
    (z : PhdThesisLean.FiniteDomainCompiler.Parameter p n) :
    (ResidualRow.pin i a w).loss (p := p) z =
      (w : ℝ) * ‖z i - (a : ℚ_[p])‖ := by
  rw [loss, affineResidual_pin]
  simp [observation]

theorem affineResidual_unequal
    {n p : ℕ} [Fact p.Prime] (i j : Fin n) (hij : i ≠ j)
    (z : PhdThesisLean.FiniteDomainCompiler.Parameter p n) :
    PhdThesisLean.FiniteDomainCompiler.affineResidual
        ((ResidualRow.unequal i j).observation (p := p)) z =
      z i - z j := by
  exact PhdThesisLean.AllDifferent.edgeResidual
    (fun _ : Unit => i) (fun _ : Unit => j) (fun _ : Unit => 1)
    (fun _ => hij) () z

theorem loss_unequal
    {n p : ℕ} [Fact p.Prime] (i j : Fin n) (hij : i ≠ j)
    (z : PhdThesisLean.FiniteDomainCompiler.Parameter p n) :
    (ResidualRow.unequal i j).loss (p := p) z =
      -‖z i - z j‖ := by
  rw [loss, affineResidual_unequal i j hij]
  simp [observation, PhdThesisLean.AllDifferent.edgeObservation]

end ResidualRow

/-- Finite selected-prime output of the all-different compiler. -/
structure CompiledObjective (n : ℕ) where
  prime : ℕ
  rows : List (ResidualRow n)
  deriving DecidableEq, Repr

/-- Positive pinning rows, one for every relabelled domain entry. -/
def pinningRows {n : ℕ} (C : ExplicitSystem n) :
    List (ResidualRow n) :=
  (Finset.univ : Finset (Fin n)).sort (· ≤ ·) |>.flatMap fun i =>
    (C.relabeledDomain i).sort (· ≤ ·) |>.map fun a =>
      .pin i a C.pinningWeight

/-- Negative unit rows, one for every deduplicated primal edge. -/
def unequalRows {n : ℕ} (C : ExplicitSystem n) :
    List (ResidualRow n) :=
  C.primalEdges.sort (Prod.Lex (· < ·) (· ≤ ·)) |>.map fun e =>
    .unequal e.1 e.2

/-- The executable selected-prime residual-objective compiler. -/
def compileObjective {n : ℕ} (C : ExplicitSystem n) :
    CompiledObjective n where
  prime := C.compilerPrime
  rows := C.pinningRows ++ C.unequalRows

@[simp]
theorem compileObjective_prime {n : ℕ} (C : ExplicitSystem n) :
    C.compileObjective.prime = C.compilerPrime :=
  rfl

/-- The same finite residual-row compiler at an explicitly supplied prime.

The rows do not depend on the prime.  Separating the header choice from row
construction lets a runtime front end select a prime above any checked upper
bound for `symbolCount`, rather than first deduplicating all domain symbols. -/
def compileObjectiveAt {n : ℕ} (C : ExplicitSystem n) (p : ℕ) :
    CompiledObjective n where
  prime := p
  rows := C.compileObjective.rows

@[simp]
theorem compileObjectiveAt_prime {n : ℕ} (C : ExplicitSystem n) (p : ℕ) :
    (C.compileObjectiveAt p).prime = p :=
  rfl

@[simp]
theorem compileObjectiveAt_rows {n : ℕ} (C : ExplicitSystem n) (p : ℕ) :
    (C.compileObjectiveAt p).rows = C.compileObjective.rows :=
  rfl

private theorem sum_map_finset_sort
    {α M : Type*} [AddCommMonoid M] (s : Finset α)
    (r : α → α → Prop) [DecidableRel r] [IsTrans α r]
    [IsAntisymm α r] [IsTotal α r] (f : α → M) :
    ((s.sort r).map f).sum = ∑ a ∈ s, f a := by
  change (↑((s.sort r).map f) : Multiset M).sum =
    (s.1.map f).sum
  rw [← Multiset.map_coe, Finset.sort_eq]

private theorem sum_map_flatMap_rows
    {α β M : Type*} [AddMonoid M]
    (as : List α) (f : α → List β) (g : β → M) :
    ((as.flatMap f).map g).sum =
      (as.map fun a => ((f a).map g).sum).sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp [ih]

private theorem sum_map_map_rows
    {α β M : Type*} [AddMonoid M]
    (as : List α) (f : α → β) (g : β → M) :
    (((as.map f).map g).sum) =
      (as.map fun a => g (f a)).sum := by
  simp only [List.map_map]
  rfl

theorem pinningRows_length {n : ℕ} (C : ExplicitSystem n) :
    C.pinningRows.length = ∑ i, (C.domains i).card := by
  simp only [pinningRows, List.length_flatMap, List.length_map,
    Finset.length_sort, C.card_relabeledDomain]
  change
    (↑((Finset.univ : Finset (Fin n)).sort (· ≤ ·) |>.map
      fun i => (C.domains i).card) : Multiset ℕ).sum =
      ∑ i, (C.domains i).card
  rw [← Multiset.map_coe, Finset.sort_eq]
  rfl

theorem unequalRows_length {n : ℕ} (C : ExplicitSystem n) :
    C.unequalRows.length = C.primalEdges.card := by
  simp [unequalRows]

theorem primalEdges_card_le_square {n : ℕ} (C : ExplicitSystem n) :
    C.primalEdges.card ≤ n ^ 2 := by
  have hcard :
      C.primalEdges.card ≤
        ((Finset.univ : Finset (Fin n)).product Finset.univ).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  simpa [primalEdges, pow_two] using hcard

/-- Exact emitted-row count: one positive row per listed domain value and one
negative row per deduplicated primal edge. -/
theorem compileObjective_rows_length {n : ℕ} (C : ExplicitSystem n) :
    C.compileObjective.rows.length =
      (∑ i, (C.domains i).card) + C.primalEdges.card := by
  simp [compileObjective, C.pinningRows_length, C.unequalRows_length]

/-- Row-count bound for the sparse output. This is not yet a binary encoded
bit-size or machine-running-time theorem. -/
theorem compileObjective_rows_length_le {n : ℕ} (C : ExplicitSystem n) :
    C.compileObjective.rows.length ≤
      (∑ i, (C.domains i).card) + n ^ 2 := by
  rw [C.compileObjective_rows_length]
  exact Nat.add_le_add_left C.primalEdges_card_le_square _

/-- Interpret a finite list of residual rows over a supplied p-adic field. -/
noncomputable def rowsLoss
    {n p : ℕ} [Fact p.Prime] (rows : List (ResidualRow n))
    (z : PhdThesisLean.FiniteDomainCompiler.Parameter p n) : ℝ :=
  (rows.map fun row => row.loss (p := p) z).sum

@[simp]
theorem rowsLoss_append
    {n p : ℕ} [Fact p.Prime] (first second : List (ResidualRow n))
    (z : PhdThesisLean.FiniteDomainCompiler.Parameter p n) :
    rowsLoss (p := p) (first ++ second) z =
      rowsLoss (p := p) first z + rowsLoss (p := p) second z := by
  simp [rowsLoss]

theorem rowsLoss_pinningRows
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    (z : PhdThesisLean.FiniteDomainCompiler.Parameter p n) :
    rowsLoss (p := p) C.pinningRows z =
      PhdThesisLean.FiniteDomainCompiler.pinningLoss
        (C.padicDomain (p := p))
        (fun _ => (C.pinningWeight : ℝ)) z := by
  classical
  rw [rowsLoss, pinningRows, sum_map_flatMap_rows,
    PhdThesisLean.FiniteDomainCompiler.pinningLoss]
  simp_rw [C.unaryCost_padicDomain]
  have hinner : ∀ i : Fin n,
      (((C.relabeledDomain i).sort (· ≤ ·)).map fun a =>
        (ResidualRow.pin i a C.pinningWeight).loss (p := p) z).sum =
        (C.pinningWeight : ℝ) *
          ∑ a ∈ C.relabeledDomain i, ‖z i - (a : ℚ_[p])‖ := by
    intro i
    rw [sum_map_finset_sort]
    simp [Finset.mul_sum]
  have hmap : ∀ i : Fin n,
      ((((C.relabeledDomain i).sort (· ≤ ·)).map fun a =>
        ResidualRow.pin i a C.pinningWeight).map
          (fun row => row.loss (p := p) z)).sum =
        (((C.relabeledDomain i).sort (· ≤ ·)).map fun a =>
          (ResidualRow.pin i a C.pinningWeight).loss (p := p) z).sum := by
    intro i
    simp only [List.map_map]
    rfl
  simp_rw [hmap, hinner]
  rw [sum_map_finset_sort]

theorem rowsLoss_unequalRows
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    (z : PhdThesisLean.FiniteDomainCompiler.Parameter p n) :
    rowsLoss (p := p) C.unequalRows z =
      PhdThesisLean.FiniteDomainCompiler.interactionLoss
        (PhdThesisLean.AllDifferent.edgeObservation
          edgeLeft edgeRight (fun _ : C.PrimalEdge => 1)) z := by
  classical
  have hinteraction :
      PhdThesisLean.FiniteDomainCompiler.interactionLoss
          (PhdThesisLean.AllDifferent.edgeObservation
            edgeLeft edgeRight (fun _ : C.PrimalEdge => 1)) z =
        ∑ e ∈ C.primalEdges, -‖z e.1 - z e.2‖ := by
    rw [PhdThesisLean.FiniteDomainCompiler.interactionLoss]
    calc
      (∑ e : C.PrimalEdge,
          (PhdThesisLean.AllDifferent.edgeObservation
            edgeLeft edgeRight (fun _ : C.PrimalEdge => 1) e).sign *
          (PhdThesisLean.AllDifferent.edgeObservation
            edgeLeft edgeRight (fun _ : C.PrimalEdge => 1) e).weight *
          ‖PhdThesisLean.FiniteDomainCompiler.affineResidual
            (PhdThesisLean.AllDifferent.edgeObservation
              edgeLeft edgeRight (fun _ : C.PrimalEdge => 1) e) z‖) =
          ∑ e : C.PrimalEdge,
            -‖z (edgeLeft e) - z (edgeRight e)‖ := by
        apply Finset.sum_congr rfl
        intro e _
        rw [PhdThesisLean.AllDifferent.edgeResidual
          edgeLeft edgeRight (fun _ : C.PrimalEdge => 1)
          edgeLeft_ne_edgeRight e z]
        simp [PhdThesisLean.AllDifferent.edgeObservation]
      _ = ∑ e ∈ C.primalEdges, -‖z e.1 - z e.2‖ := by
        rw [Finset.univ_eq_attach C.primalEdges]
        simp only [edgeLeft, edgeRight]
        rw [Finset.sum_attach C.primalEdges
          (fun e => -‖z e.1 - z e.2‖)]
  calc
    rowsLoss (p := p) C.unequalRows z =
        ∑ e ∈ C.primalEdges,
          (ResidualRow.unequal e.1 e.2).loss (p := p) z := by
      rw [rowsLoss, unequalRows, sum_map_map_rows, sum_map_finset_sort]
    _ = ∑ e ∈ C.primalEdges, -‖z e.1 - z e.2‖ := by
      apply Finset.sum_congr rfl
      intro e he
      have hne : e.1 ≠ e.2 :=
        ne_of_lt ((C.mem_primalEdges_iff e.1 e.2).mp he).1
      rw [ResidualRow.loss_unequal e.1 e.2 hne z]
    _ = PhdThesisLean.FiniteDomainCompiler.interactionLoss
          (PhdThesisLean.AllDifferent.edgeObservation
            edgeLeft edgeRight (fun _ : C.PrimalEdge => 1)) z :=
      hinteraction.symm

/-- The supplied-prime signed weighted synthetic p-adic residual objective.

Each primal edge has one negative unit-weight residual, and every allowed
coordinate value has one positive residual with uniform weight
`pinningWeight`. -/
noncomputable def suppliedPrimeLoss
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    (z : PhdThesisLean.FiniteDomainCompiler.Parameter p n) : ℝ :=
  PhdThesisLean.AllDifferent.allDifferentLoss
    (C.padicDomain (p := p)) (C.pinningWeight : ℝ)
    edgeLeft edgeRight (fun _ : C.PrimalEdge => 1) z

/-- Interpreting the emitted row list gives exactly the previously checked
supplied-prime all-different objective. -/
@[simp]
theorem rowsLoss_compileObjective
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    (z : PhdThesisLean.FiniteDomainCompiler.Parameter p n) :
    rowsLoss (p := p) C.compileObjective.rows z =
      C.suppliedPrimeLoss (p := p) z := by
  rw [compileObjective, rowsLoss_append, C.rowsLoss_pinningRows,
    C.rowsLoss_unequalRows, suppliedPrimeLoss,
    PhdThesisLean.AllDifferent.allDifferentLoss,
    PhdThesisLean.FiniteDomainCompiler.compilerLoss]

theorem padicDomain_nonempty
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    (hC : C.WellFormed) (i : Fin n) :
    (C.padicDomain (p := p) i).Nonempty := by
  classical
  obtain ⟨a, ha⟩ := C.relabeled_wellFormed hC i
  exact ⟨(a : ℚ_[p]), Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩

/-- Ranks in `{1, ..., q}` are globally unit-separated whenever the supplied
prime is larger than `q`. -/
theorem padicDomain_globallyUnitSeparated
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    (hp : C.symbolCount < p) :
    PhdThesisLean.AllDifferent.GloballyUnitSeparated
      (C.padicDomain (p := p)) := by
  classical
  intro i a ha j b hb hab
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hb
  have hrValues : r ∈ C.relabeled.domainValues := by
    exact (C.relabeled.mem_domainValues_iff r).2 ⟨i, hr⟩
  have hsValues : s ∈ C.relabeled.domainValues := by
    exact (C.relabeled.mem_domainValues_iff s).2 ⟨j, hs⟩
  rw [C.domainValues_relabeled_eq_Icc] at hrValues hsValues
  have hrBounds := Finset.mem_Icc.mp hrValues
  have hsBounds := Finset.mem_Icc.mp hsValues
  have hrs : r ≠ s := by
    intro h
    apply hab
    rw [h]
  rcases lt_or_gt_of_ne hrs with hrs | hsr
  · have hdiff_ne : s - r ≠ 0 := by omega
    have hdiff_lt : s - r < p :=
      (Nat.sub_le s r).trans_lt (hsBounds.2.trans_lt hp)
    have hcoprime : p.Coprime (s - r) :=
      Nat.coprime_of_lt_prime hdiff_ne hdiff_lt Fact.out
    rw [← norm_neg, neg_sub, ← Nat.cast_sub hrs.le,
      Padic.norm_natCast_eq_one_iff]
    exact hcoprime
  · have hdiff_ne : r - s ≠ 0 := by omega
    have hdiff_lt : r - s < p :=
      (Nat.sub_le r s).trans_lt (hrBounds.2.trans_lt hp)
    have hcoprime : p.Coprime (r - s) :=
      Nat.coprime_of_lt_prime hdiff_ne hdiff_lt Fact.out
    rw [← Nat.cast_sub hsr.le, Padic.norm_natCast_eq_one_iff]
    exact hcoprime

theorem padicAssignment_inDomain
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    {x : Fin n → ℕ} (hx : C.InDomain x) :
    PhdThesisLean.FiniteDomainCompiler.InDomain
      (C.padicDomain (p := p)) (C.padicAssignment (p := p) x) := by
  classical
  intro i
  exact Finset.mem_image.mpr
    ⟨C.relabelValue (x i),
      Finset.mem_image.mpr ⟨x i, hx i, rfl⟩, rfl⟩

/-- Every point in the embedded product domain is the embedded canonical
relabeling of an original domain-respecting assignment. -/
theorem exists_inDomain_padicAssignment_eq
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    {z : PhdThesisLean.FiniteDomainCompiler.Parameter p n}
    (hz : PhdThesisLean.FiniteDomainCompiler.InDomain
      (C.padicDomain (p := p)) z) :
    ∃ x, C.InDomain x ∧ C.padicAssignment (p := p) x = z := by
  classical
  have hchoice :
      ∀ i, ∃ a, a ∈ C.relabeledDomain i ∧ (a : ℚ_[p]) = z i := by
    intro i
    simpa only [padicDomain, Finset.mem_image] using hz i
  choose y hy using hchoice
  have hyDomain : C.relabeled.InDomain y := by
    intro i
    exact (hy i).1
  obtain ⟨x, hx, hxy⟩ :=
    C.exists_inDomain_relabelAssignment_eq hyDomain
  refine ⟨x, hx, ?_⟩
  funext i
  change (C.relabelAssignment x i : ℚ_[p]) = z i
  rw [hxy]
  exact (hy i).2

theorem conflictWeight_padicAssignment
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    {x : Fin n → ℕ} (hx : C.InDomain x) :
    PhdThesisLean.AllDifferent.conflictWeight
        (p := p) edgeLeft edgeRight (fun _ : C.PrimalEdge => 1)
        (C.padicAssignment (p := p) x) =
      (C.conflictCount x : ℝ) := by
  classical
  rw [PhdThesisLean.AllDifferent.conflictWeight]
  simp only [padicAssignment, edgeLeft, edgeRight, Nat.cast_inj]
  rw [Finset.univ_eq_attach C.primalEdges]
  rw [Finset.sum_attach C.primalEdges
    (fun e => if C.relabelAssignment x e.1 =
      C.relabelAssignment x e.2 then (1 : ℝ) else 0)]
  rw [Finset.sum_boole]
  rw [show C.primalEdges.filter
      (fun e => C.relabelAssignment x e.1 =
        C.relabelAssignment x e.2) =
      C.relabeled.conflictEdges (C.relabelAssignment x) by
        rfl]
  change (C.relabeled.conflictCount (C.relabelAssignment x) : ℝ) =
    (C.conflictCount x : ℝ)
  exact_mod_cast C.conflictCount_relabelAssignment hx

theorem incidentEdgeWeight_lt_pinningWeight
    {n : ℕ} (C : ExplicitSystem n) (i : Fin n) :
    PhdThesisLean.AllDifferent.incidentEdgeWeight
        edgeLeft edgeRight (fun _ : C.PrimalEdge => 1) i <
      (C.pinningWeight : ℝ) := by
  classical
  have hle :
      PhdThesisLean.AllDifferent.incidentEdgeWeight
          edgeLeft edgeRight (fun _ : C.PrimalEdge => 1) i ≤
        (C.primalEdges.card : ℝ) := by
    rw [PhdThesisLean.AllDifferent.incidentEdgeWeight]
    calc
      (∑ e : C.PrimalEdge,
          if i = edgeLeft e ∨ i = edgeRight e then (1 : ℝ) else 0) ≤
          ∑ _e : C.PrimalEdge, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro e _
            split <;> norm_num
      _ = (Fintype.card C.PrimalEdge : ℝ) := by simp
      _ = (C.primalEdges.card : ℝ) := by
        rw [Fintype.card_coe]
  exact hle.trans_lt (by
    exact_mod_cast Nat.lt_succ_self C.primalEdges.card)

/-- Exact semantics of the supplied-prime compiler stage.

Every global minimizer of the emitted p-adic objective is the canonical
embedding of an original domain-respecting minimum-conflict assignment, and
every such embedded assignment is a global minimizer. The theorem deliberately
does not claim that the compiler has selected `p` or established bit-level
polynomial runtime. -/
theorem suppliedPrime_allDifferent_correctness
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    (hC : C.WellFormed) (hp : C.symbolCount < p) :
    (∃ z, PhdThesisLean.AllDifferent.IsGlobalMin
      (C.suppliedPrimeLoss (p := p)) z) ∧
    ∀ z, PhdThesisLean.AllDifferent.IsGlobalMin
        (C.suppliedPrimeLoss (p := p)) z ↔
      ∃ x, C.MinimizesConflicts x ∧
        C.padicAssignment (p := p) x = z := by
  have hcorrect :=
    PhdThesisLean.AllDifferent.all_different_correctness
      (C.padicDomain (p := p)) (C.pinningWeight : ℝ)
      edgeLeft edgeRight (fun _ : C.PrimalEdge => 1)
      (C.padicDomain_nonempty hC) edgeLeft_ne_edgeRight
      (C.padicDomain_globallyUnitSeparated hp)
      (fun _ => by norm_num) C.incidentEdgeWeight_lt_pinningWeight
  refine ⟨by simpa only [suppliedPrimeLoss] using hcorrect.1, ?_⟩
  intro z
  rw [show PhdThesisLean.AllDifferent.IsGlobalMin
      (C.suppliedPrimeLoss (p := p)) z ↔
      PhdThesisLean.AllDifferent.MinimizesConflicts
        (C.padicDomain (p := p)) edgeLeft edgeRight
        (fun _ : C.PrimalEdge => 1) z by
      simpa only [suppliedPrimeLoss] using hcorrect.2 z]
  constructor
  · rintro ⟨hzDomain, hzMin⟩
    obtain ⟨x, hxDomain, rfl⟩ :=
      C.exists_inDomain_padicAssignment_eq hzDomain
    refine ⟨x, ⟨hxDomain, ?_⟩, rfl⟩
    intro y hyDomain
    have hxy := hzMin (C.padicAssignment (p := p) y)
      (C.padicAssignment_inDomain hyDomain)
    rw [C.conflictWeight_padicAssignment hxDomain,
      C.conflictWeight_padicAssignment hyDomain] at hxy
    exact_mod_cast hxy
  · rintro ⟨x, ⟨hxDomain, hxMin⟩, rfl⟩
    refine ⟨C.padicAssignment_inDomain hxDomain, ?_⟩
    intro z hzDomain
    obtain ⟨y, hyDomain, rfl⟩ :=
      C.exists_inDomain_padicAssignment_eq hzDomain
    have hxy := hxMin y hyDomain
    rw [C.conflictWeight_padicAssignment hxDomain,
      C.conflictWeight_padicAssignment hyDomain]
    exact_mod_cast hxy

/-- Exact minimum-conflict semantics for the finite row list with an arbitrary
checked prime in its header.  This is the semantic interface used by runtime
front ends that compute a convenient upper bound for the distinct-symbol
count. -/
theorem compileObjectiveAt_allDifferent_correctness
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    (hC : C.WellFormed) (hp : C.symbolCount < p) :
    (∃ z, PhdThesisLean.AllDifferent.IsGlobalMin
      (rowsLoss (p := p)
        (C.compileObjectiveAt p).rows) z) ∧
    ∀ z, PhdThesisLean.AllDifferent.IsGlobalMin
        (rowsLoss (p := p)
          (C.compileObjectiveAt p).rows) z ↔
      ∃ x, C.MinimizesConflicts x ∧
        C.padicAssignment (p := p) x = z := by
  have hloss :
      rowsLoss (p := p) (C.compileObjectiveAt p).rows =
        C.suppliedPrimeLoss (p := p) :=
    funext C.rowsLoss_compileObjective
  simpa only [compileObjectiveAt_prime, hloss] using
    C.suppliedPrime_allDifferent_correctness hC hp

/-- Exact minimum-conflict semantics after composing the executable
compiler-selected prime with the supplied-prime p-adic stage.

This closes prime selection for the semantic compiler. The encoding and
machine modules separately check finite output size and unary-bound prime
selection; structural CSP compilation, unary-bound production, encoded
objective emission, and final runtime composition remain before
`cor:all-different-csp` is complete. -/
theorem compilerPrime_allDifferent_correctness
    {n : ℕ} (C : ExplicitSystem n) (hC : C.WellFormed) :
    letI : Fact C.compilerPrime.Prime := ⟨C.compilerPrime_prime⟩
    (∃ z, PhdThesisLean.AllDifferent.IsGlobalMin
      (C.suppliedPrimeLoss (p := C.compilerPrime)) z) ∧
    ∀ z, PhdThesisLean.AllDifferent.IsGlobalMin
        (C.suppliedPrimeLoss (p := C.compilerPrime)) z ↔
      ∃ x, C.MinimizesConflicts x ∧
        C.padicAssignment (p := C.compilerPrime) x = z := by
  letI : Fact C.compilerPrime.Prime := ⟨C.compilerPrime_prime⟩
  exact C.suppliedPrime_allDifferent_correctness hC
    C.symbolCount_lt_compilerPrime

/-- Exact minimum-conflict semantics stated directly for the finite emitted
row list at its selected prime. -/
theorem compileObjective_allDifferent_correctness
    {n : ℕ} (C : ExplicitSystem n) (hC : C.WellFormed) :
    letI : Fact C.compileObjective.prime.Prime :=
      ⟨by simpa using C.compilerPrime_prime⟩
    (∃ z, PhdThesisLean.AllDifferent.IsGlobalMin
      (rowsLoss (p := C.compileObjective.prime)
        C.compileObjective.rows) z) ∧
    ∀ z, PhdThesisLean.AllDifferent.IsGlobalMin
        (rowsLoss (p := C.compileObjective.prime)
          C.compileObjective.rows) z ↔
      ∃ x, C.MinimizesConflicts x ∧
        C.padicAssignment (p := C.compileObjective.prime) x = z := by
  letI : Fact C.compileObjective.prime.Prime :=
    ⟨by simpa using C.compilerPrime_prime⟩
  have hloss :
      rowsLoss (p := C.compileObjective.prime) C.compileObjective.rows =
        C.suppliedPrimeLoss (p := C.compileObjective.prime) :=
    funext C.rowsLoss_compileObjective
  rw [hloss]
  simpa only [compileObjective_prime] using
    C.compilerPrime_allDifferent_correctness hC

/-- In the satisfiable case, the supplied-prime objective's global minimizers
are exactly the embedded satisfying assignments. -/
theorem suppliedPrime_globalMin_iff_satisfies_of_satisfiable
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    (hC : C.WellFormed) (hp : C.symbolCount < p)
    (hsat : ∃ x, C.Satisfies x)
    (z : PhdThesisLean.FiniteDomainCompiler.Parameter p n) :
    PhdThesisLean.AllDifferent.IsGlobalMin
        (C.suppliedPrimeLoss (p := p)) z ↔
      ∃ x, C.Satisfies x ∧ C.padicAssignment (p := p) x = z := by
  rw [(C.suppliedPrime_allDifferent_correctness hC hp).2 z]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (C.minimizesConflicts_iff_satisfies_of_satisfiable
      hsat x).mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (C.minimizesConflicts_iff_satisfies_of_satisfiable
      hsat x).mpr hx, rfl⟩

/-- Satisfiable-case specialization for a finite row list whose supplied
prime is larger than the distinct-symbol count. -/
theorem compileObjectiveAt_globalMin_iff_satisfies_of_satisfiable
    {n p : ℕ} [Fact p.Prime] (C : ExplicitSystem n)
    (hC : C.WellFormed) (hp : C.symbolCount < p)
    (hsat : ∃ x, C.Satisfies x)
    (z : PhdThesisLean.FiniteDomainCompiler.Parameter p n) :
    PhdThesisLean.AllDifferent.IsGlobalMin
        (rowsLoss (p := p)
          (C.compileObjectiveAt p).rows) z ↔
      ∃ x, C.Satisfies x ∧
        C.padicAssignment (p := p) x = z := by
  have hloss :
      rowsLoss (p := p) (C.compileObjectiveAt p).rows =
        C.suppliedPrimeLoss (p := p) :=
    funext C.rowsLoss_compileObjective
  simpa only [compileObjectiveAt_prime, hloss] using
    C.suppliedPrime_globalMin_iff_satisfies_of_satisfiable hC hp hsat z

/-- Satisfiable-case specialization for the executable compiler-selected
prime. -/
theorem compilerPrime_globalMin_iff_satisfies_of_satisfiable
    {n : ℕ} (C : ExplicitSystem n) (hC : C.WellFormed)
    (hsat : ∃ x, C.Satisfies x) :
    letI : Fact C.compilerPrime.Prime := ⟨C.compilerPrime_prime⟩
    ∀ z : PhdThesisLean.FiniteDomainCompiler.Parameter C.compilerPrime n,
      PhdThesisLean.AllDifferent.IsGlobalMin
          (C.suppliedPrimeLoss (p := C.compilerPrime)) z ↔
        ∃ x, C.Satisfies x ∧
          C.padicAssignment (p := C.compilerPrime) x = z := by
  letI : Fact C.compilerPrime.Prime := ⟨C.compilerPrime_prime⟩
  exact C.suppliedPrime_globalMin_iff_satisfies_of_satisfiable hC
    C.symbolCount_lt_compilerPrime hsat

/-- Satisfiable-case characterization stated directly for the finite emitted
row list at its selected prime. -/
theorem compileObjective_globalMin_iff_satisfies_of_satisfiable
    {n : ℕ} (C : ExplicitSystem n) (hC : C.WellFormed)
    (hsat : ∃ x, C.Satisfies x) :
    letI : Fact C.compileObjective.prime.Prime :=
      ⟨by simpa using C.compilerPrime_prime⟩
    ∀ z : PhdThesisLean.FiniteDomainCompiler.Parameter
        C.compileObjective.prime n,
      PhdThesisLean.AllDifferent.IsGlobalMin
          (rowsLoss (p := C.compileObjective.prime)
            C.compileObjective.rows) z ↔
        ∃ x, C.Satisfies x ∧
          C.padicAssignment (p := C.compileObjective.prime) x = z := by
  letI : Fact C.compileObjective.prime.Prime :=
    ⟨by simpa using C.compilerPrime_prime⟩
  have hloss :
      rowsLoss (p := C.compileObjective.prime) C.compileObjective.rows =
        C.suppliedPrimeLoss (p := C.compileObjective.prime) :=
    funext C.rowsLoss_compileObjective
  rw [hloss]
  simpa only [compileObjective_prime] using
    C.compilerPrime_globalMin_iff_satisfies_of_satisfiable hC hsat

end ExplicitSystem

#print axioms ExplicitSystem.satisfies_iff_isProper
#print axioms ExplicitSystem.minimizesConflicts_iff_satisfies_of_satisfiable
#print axioms ExplicitSystem.relabeledValues_eq_Icc
#print axioms ExplicitSystem.relabeled_minimizesConflicts_relabelAssignment_iff
#print axioms ExplicitSystem.selectPrimeAbove_prime
#print axioms ExplicitSystem.selectPrimeAbove_lt_two_mul
#print axioms ExplicitSystem.rowsLoss_compileObjective
#print axioms ExplicitSystem.suppliedPrime_allDifferent_correctness
#print axioms ExplicitSystem.compileObjectiveAt_allDifferent_correctness
#print axioms ExplicitSystem.compilerPrime_allDifferent_correctness
#print axioms ExplicitSystem.compileObjective_allDifferent_correctness
#print axioms ExplicitSystem.suppliedPrime_globalMin_iff_satisfies_of_satisfiable
#print axioms ExplicitSystem.compileObjectiveAt_globalMin_iff_satisfies_of_satisfiable
#print axioms ExplicitSystem.compilerPrime_globalMin_iff_satisfies_of_satisfiable
#print axioms ExplicitSystem.compileObjective_globalMin_iff_satisfies_of_satisfiable

end PhdThesisLean.AllDifferentCSP
