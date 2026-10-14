import PhdThesisLean.FixedPrimeHardness

namespace PhdThesisLean.CNFNormalisation

open scoped BigOperators
open PhdThesisLean.FiniteDomainCompiler
open PhdThesisLean.ClauseCompiler
open PhdThesisLean.FixedPrimeHardness

/-!
# Normalising arbitrary 3-CNF syntax to the distinct-variable convention

Thesis Theorem `thm:3sat-clausewise`
(`appendices/complexity-3sat-clausewise.tex`) is stated for 3-CNF formulas in
the "standard restricted form": every clause has exactly three literals on
pairwise distinct variables.  `ClauseCompiler.three_sat_clausewise` and
`ClauseCompiler.satisfiable_iff_minimum_value` formalise the theorem under
that convention, which `Clause.variables_injective` makes explicit.  This
module removes the qualification: it formalises general 3-CNF syntax
(`GeneralCNF`: clauses are lists of at most three literals, allowing repeated
literals, complementary literals, and empty clauses), the standard deletion of
repeated literals and tautological clauses, and padding with three fresh
variables, and proves that the result is a satisfiability-equivalent
`ThreeCNF` of linear size.  Composing with the existing theorems transfers
`thm:3sat-clausewise` and the fixed-prime reduction of `cor:signed-nphard`
to arbitrary 3-CNF input.

## Padding scheme

After deleting repeated literals a non-tautological clause has `k ∈ {0,1,2,3}`
literals on distinct variables.  With fresh variables `u, v, w`:

* `k = 3`, literals `a, b, c`: the single clause `(a ∨ b ∨ c)`;
* `k = 2`, literals `a, b`: `(a ∨ b ∨ u)` and `(a ∨ b ∨ ¬u)`;
* `k = 1`, literal `a`: the four clauses `(a ∨ ±u ∨ ±v)`;
* `k = 0` (empty clause): the eight clauses `(±u ∨ ±v ∨ ±w)`, which are
  jointly unsatisfiable;
* tautological clauses (containing `z` and `¬z`) emit nothing.

Hence `(normalise F).numVars = F.numVars + 3`,
`(normalise F).numClauses ≤ 8 * F.numClauses`, and in the unit-cell model
`(normalise F).cellSize ≤ 8 * F.cellSize`.

## Correspondence notes

* `GeneralCNF` is strictly more general than the thesis syntax: the thesis
  Sudoku chapter speaks of "the standard deletion of repeated literals and
  tautological clauses", and the clause-wise appendix assumes distinct
  variables.  Both conventions are now machine-checked rather than assumed.
* `general_satisfiable_iff_minimum_value` and `general_three_sat_clausewise`
  are `thm:3sat-clausewise` for arbitrary 3-CNF input, via `normalise`.
* `general_compileFixedPrime_correct` and
  `fixed_prime_signed_decision_is_general_three_sat_hard_in_cell_model`
  extend the fixed-prime reduction of `FixedPrimeHardness` to general input,
  with the explicit polynomial bound `392 * cellSize ^ 2` in the unit-cell
  model.  As in `FixedPrimeHardness`, the external theorem "3-SAT is NP-hard"
  is not formalised; the semantic reduction and its size bounds are.
* `threeCNFToGeneral` embeds the restricted syntax into the general syntax,
  so the general syntax subsumes the old one.
-/

deriving instance DecidableEq for Literal

/-! ## General 3-CNF syntax -/

/-- A general three-CNF clause: a list of literals (the width bound
`length ≤ 3` is recorded on the formula). Repeated literals, complementary
literals and the empty clause are all allowed. -/
abbrev GeneralClause (n : ℕ) := List (Literal n)

/-- A general clause is satisfied when some literal in it is true, i.e. has
failure bit `false`. -/
def GeneralClause.satisfied {n : ℕ} (C : GeneralClause n) (x : Fin n → Bool) : Prop :=
  ∃ l ∈ C, literalFailureBit l x = false

/-- A 3-CNF formula in general syntax: every clause has at most three
literals, with no further restriction. -/
structure GeneralCNF where
  numVars : ℕ
  numClauses : ℕ
  clause : Fin numClauses → GeneralClause numVars
  width : ∀ r, (clause r).length ≤ 3

def GeneralCNF.Satisfiable (F : GeneralCNF) : Prop :=
  ∃ x : Fin F.numVars → Bool, ∀ r, GeneralClause.satisfied (F.clause r) x

/-- Unit-cell size of the general syntax, in the same fixed-width model as
`ThreeCNF.cellSize`: one slot per variable, a three-literal slot (two cells
per literal) per clause, and two header cells. -/
def GeneralCNF.cellSize (F : GeneralCNF) : ℕ :=
  F.numVars + 6 * F.numClauses + 2

/-! ## Deleting repeated literals and tautological clauses -/

/-- The variables of the literals are pairwise distinct. -/
abbrev DistinctVars {n : ℕ} (R : List (Literal n)) : Prop :=
  R.Pairwise fun a b => a.var ≠ b.var

/-- A clause with pairwise distinct variables. -/
abbrev ReducedClause (n : ℕ) := {R : List (Literal n) // DistinctVars R}

/-- Insert a literal into a reduced clause: a repeated literal is dropped, a
complementary literal makes the clause tautological (`none`), otherwise the
literal is added. -/
def insertLiteral {n : ℕ} (l : Literal n) :
    Option (ReducedClause n) → Option (ReducedClause n)
  | none => none
  | some ⟨R, hR⟩ =>
    if l ∈ R then some ⟨R, hR⟩
    else if h : ∃ l' ∈ R, l'.var = l.var then none
    else some ⟨l :: R,
      List.pairwise_cons.mpr ⟨fun l' hl' heq => h ⟨l', hl', heq.symm⟩, hR⟩⟩

/-- Standard deletion: remove repeated literals; return `none` for a
tautological clause. -/
def reduce {n : ℕ} (C : GeneralClause n) : Option (ReducedClause n) :=
  C.foldr insertLiteral (some ⟨[], List.Pairwise.nil⟩)

theorem reduce_nil {n : ℕ} :
    reduce ([] : GeneralClause n) = some ⟨[], List.Pairwise.nil⟩ := rfl

theorem reduce_cons {n : ℕ} (l : Literal n) (C : GeneralClause n) :
    reduce (l :: C) = insertLiteral l (reduce C) := rfl

theorem insertLiteral_none {n : ℕ} (l : Literal n) :
    insertLiteral l none = none := rfl

theorem mem_reduce {n : ℕ} (C : GeneralClause n) (R : ReducedClause n)
    (h : reduce C = some R) (l : Literal n) : l ∈ C ↔ l ∈ R.1 := by
  induction C generalizing R with
  | nil =>
    rw [reduce_nil] at h
    cases h
    simp
  | cons l₀ C ih =>
    rw [reduce_cons] at h
    cases hC : reduce C with
    | none =>
      rw [hC, insertLiteral_none] at h
      cases h
    | some R₀ =>
      rw [hC] at h
      obtain ⟨R₀, hR₀⟩ := R₀
      have ih' := ih ⟨R₀, hR₀⟩ hC
      simp only [insertLiteral] at h
      split_ifs at h with h₁ h₂
      · cases h
        simp only [List.mem_cons, ih']
        constructor
        · rintro (rfl | hl)
          · exact h₁
          · exact hl
        · intro hl
          exact Or.inr hl
      · cases h
        simp only [List.mem_cons, ih']

theorem reduce_eq_none {n : ℕ} (C : GeneralClause n) (h : reduce C = none) :
    ∃ a ∈ C, ∃ b ∈ C, a.var = b.var ∧ a.negated ≠ b.negated := by
  induction C with
  | nil =>
    rw [reduce_nil] at h
    cases h
  | cons l₀ C ih =>
    rw [reduce_cons] at h
    cases hC : reduce C with
    | none =>
      obtain ⟨a, ha, b, hb, hab, hne⟩ := ih hC
      exact ⟨a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, hab, hne⟩
    | some R₀ =>
      rw [hC] at h
      obtain ⟨R₀, hR₀⟩ := R₀
      simp only [insertLiteral] at h
      split_ifs at h with h₁ h₂
      obtain ⟨l', hl', hvar⟩ := h₂
      have hl'C : l' ∈ C := (mem_reduce C ⟨R₀, hR₀⟩ hC l').mpr hl'
      refine ⟨l₀, by simp, l', List.mem_cons_of_mem _ hl'C, hvar.symm, ?_⟩
      intro hneg
      apply h₁
      have heq : l' = l₀ := by
        cases l'
        cases l₀
        simp_all
      rw [← heq]
      exact hl'

theorem reduce_length_le {n : ℕ} (C : GeneralClause n) (R : ReducedClause n)
    (h : reduce C = some R) : R.1.length ≤ C.length := by
  induction C generalizing R with
  | nil =>
    rw [reduce_nil] at h
    cases h
    simp
  | cons l₀ C ih =>
    rw [reduce_cons] at h
    cases hC : reduce C with
    | none =>
      rw [hC, insertLiteral_none] at h
      cases h
    | some R₀ =>
      rw [hC] at h
      obtain ⟨R₀, hR₀⟩ := R₀
      have ih' := ih ⟨R₀, hR₀⟩ hC
      simp only [insertLiteral] at h
      split_ifs at h with h₁ h₂
      · cases h
        simp only [List.length_cons] at ih' ⊢
        omega
      · cases h
        simp only [List.length_cons] at ih' ⊢
        omega

/-- A clause containing a literal and its complement is satisfied by every
assignment. -/
theorem satisfied_of_complementary {n : ℕ} (C : GeneralClause n)
    (a b : Literal n) (ha : a ∈ C) (hb : b ∈ C)
    (hvar : a.var = b.var) (hneg : a.negated ≠ b.negated)
    (x : Fin n → Bool) : GeneralClause.satisfied C x := by
  by_cases hfa : literalFailureBit a x = false
  · exact ⟨a, ha, hfa⟩
  · refine ⟨b, hb, ?_⟩
    obtain ⟨va, na⟩ := a
    obtain ⟨vb, nb⟩ := b
    simp only at hvar hneg
    subst hvar
    cases na <;> cases nb <;> simp_all [literalFailureBit]

/-! ## Lifting to `n + 3` variables -/

/-- Lift a literal on the original variables. -/
def liftLit {n : ℕ} (l : Literal n) : Literal (n + 3) :=
  ⟨Fin.castAdd 3 l.var, l.negated⟩

/-- The three fresh variables `u, v, w`. -/
def freshVar (n : ℕ) (j : Fin 3) : Fin (n + 3) := Fin.natAdd n j

/-- A (possibly negated) fresh literal. -/
def freshLit (n : ℕ) (j : Fin 3) (s : Bool) : Literal (n + 3) := ⟨freshVar n j, s⟩

theorem liftLit_var_ne {n : ℕ} {a b : Literal n} (h : a.var ≠ b.var) :
    (liftLit a).var ≠ (liftLit b).var := by
  intro heq
  apply h
  have := congrArg Fin.val heq
  simp only [liftLit, Fin.val_castAdd] at this
  exact Fin.ext this

theorem liftLit_var_ne_freshLit {n : ℕ} (l : Literal n) (j : Fin 3) (s : Bool) :
    (liftLit l).var ≠ (freshLit n j s).var := by
  intro heq
  have := congrArg Fin.val heq
  simp only [liftLit, freshLit, freshVar, Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem freshLit_var_ne {n : ℕ} {j j' : Fin 3} (s s' : Bool) (h : j ≠ j') :
    (freshLit n j s).var ≠ (freshLit n j' s').var := by
  intro heq
  apply h
  have := congrArg Fin.val heq
  simp only [freshLit, freshVar, Fin.val_natAdd] at this
  exact Fin.ext (by omega)

/-- Restrict an assignment on `n + 3` variables to the original variables. -/
def restrict {n : ℕ} (x : Fin (n + 3) → Bool) : Fin n → Bool :=
  fun i => x (Fin.castAdd 3 i)

theorem literalFailureBit_liftLit {n : ℕ} (l : Literal n) (x : Fin (n + 3) → Bool) :
    literalFailureBit (liftLit l) x = literalFailureBit l (restrict x) := rfl

theorem literalFailureBit_liftLit_append {n : ℕ} (l : Literal n)
    (x : Fin n → Bool) (y : Fin 3 → Bool) :
    literalFailureBit (liftLit l) (Fin.append x y) = literalFailureBit l x := by
  simp [literalFailureBit, liftLit, Fin.append_left]

theorem literalFailureBit_not {m : ℕ} (i : Fin m) (x : Fin m → Bool) :
    literalFailureBit ⟨i, !(x i)⟩ x = true := by
  cases h : x i <;> simp [literalFailureBit, h]

/-! ## Three-literal clauses on distinct variables -/

/-- Build a `Clause` from three literals on pairwise distinct variables. -/
def mkClause {m : ℕ} (a b c : Literal m)
    (hab : a.var ≠ b.var) (hac : a.var ≠ c.var) (hbc : b.var ≠ c.var) : Clause m where
  literal := ![a, b, c]
  variables_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem clauseSatisfied_mkClause {m : ℕ} (a b c : Literal m)
    (hab : a.var ≠ b.var) (hac : a.var ≠ c.var) (hbc : b.var ≠ c.var)
    (x : Fin m → Bool) :
    clauseSatisfied (mkClause a b c hab hac hbc) x ↔
      literalFailureBit a x = false ∨ literalFailureBit b x = false ∨
        literalFailureBit c x = false := by
  simp only [clauseSatisfied, mkClause, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  cases literalFailureBit a x <;> cases literalFailureBit b x <;>
    cases literalFailureBit c x <;> simp

/-! ## Padding -/

def allSigns3 : List (Bool × Bool × Bool) :=
  [(false, false, false), (false, false, true), (false, true, false), (false, true, true),
    (true, false, false), (true, false, true), (true, true, false), (true, true, true)]

def allSigns2 : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

def allSigns1 : List Bool := [false, true]

theorem mem_allSigns3 : ∀ s : Bool × Bool × Bool, s ∈ allSigns3 := by decide

theorem mem_allSigns2 : ∀ s : Bool × Bool, s ∈ allSigns2 := by decide

theorem mem_allSigns1 : ∀ s : Bool, s ∈ allSigns1 := by decide

/-- The eight clauses `(±u ∨ ±v ∨ ±w)`: jointly unsatisfiable. -/
def emptyClauses (n : ℕ) : List (Clause (n + 3)) :=
  allSigns3.map fun s =>
    mkClause (freshLit n 0 s.1) (freshLit n 1 s.2.1) (freshLit n 2 s.2.2)
      (freshLit_var_ne _ _ (by decide)) (freshLit_var_ne _ _ (by decide))
      (freshLit_var_ne _ _ (by decide))

/-- The four clauses `(a ∨ ±u ∨ ±v)`. -/
def oneClauses {n : ℕ} (a : Literal n) : List (Clause (n + 3)) :=
  allSigns2.map fun s =>
    mkClause (liftLit a) (freshLit n 0 s.1) (freshLit n 1 s.2)
      (liftLit_var_ne_freshLit _ _ _) (liftLit_var_ne_freshLit _ _ _)
      (freshLit_var_ne _ _ (by decide))

/-- The two clauses `(a ∨ b ∨ ±u)`. -/
def twoClauses {n : ℕ} (a b : Literal n) (hab : a.var ≠ b.var) :
    List (Clause (n + 3)) :=
  allSigns1.map fun s =>
    mkClause (liftLit a) (liftLit b) (freshLit n 0 s)
      (liftLit_var_ne hab) (liftLit_var_ne_freshLit _ _ _)
      (liftLit_var_ne_freshLit _ _ _)

/-- The single clause `(a ∨ b ∨ c)`. -/
def threeClauses {n : ℕ} (a b c : Literal n)
    (hab : a.var ≠ b.var) (hac : a.var ≠ c.var) (hbc : b.var ≠ c.var) :
    List (Clause (n + 3)) :=
  [mkClause (liftLit a) (liftLit b) (liftLit c)
    (liftLit_var_ne hab) (liftLit_var_ne hac) (liftLit_var_ne hbc)]

theorem distinct_two {n : ℕ} {a b : Literal n} (h : DistinctVars [a, b]) :
    a.var ≠ b.var :=
  (List.pairwise_cons.mp h).1 b (by simp)

theorem distinct_three_ab {n : ℕ} {a b c : Literal n} (h : DistinctVars [a, b, c]) :
    a.var ≠ b.var :=
  (List.pairwise_cons.mp h).1 b (by simp)

theorem distinct_three_ac {n : ℕ} {a b c : Literal n} (h : DistinctVars [a, b, c]) :
    a.var ≠ c.var :=
  (List.pairwise_cons.mp h).1 c (by simp)

theorem distinct_three_bc {n : ℕ} {a b c : Literal n} (h : DistinctVars [a, b, c]) :
    b.var ≠ c.var :=
  (List.pairwise_cons.mp (List.pairwise_cons.mp h).2).1 c (by simp)

/-- Pad a reduced clause to a list of three-literal distinct-variable
clauses over `n + 3` variables.  (The last case is unreachable for width
`≤ 3`.) -/
def pad {n : ℕ} : ReducedClause n → List (Clause (n + 3))
  | ⟨[], _⟩ => emptyClauses n
  | ⟨[a], _⟩ => oneClauses a
  | ⟨[a, b], h⟩ => twoClauses a b (distinct_two h)
  | ⟨[a, b, c], h⟩ =>
    threeClauses a b c (distinct_three_ab h) (distinct_three_ac h) (distinct_three_bc h)
  | ⟨_ :: _ :: _ :: _ :: _, _⟩ => []

/-- Every padded clause is satisfied whenever one of the retained literals is
true. -/
theorem pad_satisfied {n : ℕ} (R : ReducedClause n) (x : Fin (n + 3) → Bool)
    (l : Literal n) (hl : l ∈ R.1)
    (hfail : literalFailureBit (liftLit l) x = false) :
    ∀ D ∈ pad R, clauseSatisfied D x := by
  obtain ⟨R, hR⟩ := R
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, R⟩⟩⟩⟩
  · simp at hl
  · simp only [List.mem_singleton] at hl
    subst hl
    intro D hD
    simp only [pad, oneClauses, List.mem_map] at hD
    obtain ⟨s, _, rfl⟩ := hD
    rw [clauseSatisfied_mkClause]
    exact Or.inl hfail
  · intro D hD
    simp only [pad, twoClauses, List.mem_map] at hD
    obtain ⟨s, _, rfl⟩ := hD
    rw [clauseSatisfied_mkClause]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact Or.inl hfail
    · exact Or.inr (Or.inl hfail)
  · intro D hD
    simp only [pad, threeClauses, List.mem_singleton] at hD
    subst hD
    rw [clauseSatisfied_mkClause]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact Or.inl hfail
    · exact Or.inr (Or.inl hfail)
    · exact Or.inr (Or.inr hfail)
  · intro D hD
    simp [pad] at hD

/-- If all padded clauses hold then one of the retained literals is true. -/
theorem pad_forces {n : ℕ} (R : ReducedClause n) (hlen : R.1.length ≤ 3)
    (x : Fin (n + 3) → Bool) (hall : ∀ D ∈ pad R, clauseSatisfied D x) :
    ∃ l ∈ R.1, literalFailureBit (liftLit l) x = false := by
  obtain ⟨R, hR⟩ := R
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, R⟩⟩⟩⟩
  · exfalso
    have hD := hall
      (mkClause (freshLit n 0 (!(x (freshVar n 0)))) (freshLit n 1 (!(x (freshVar n 1))))
        (freshLit n 2 (!(x (freshVar n 2))))
        (freshLit_var_ne _ _ (by decide)) (freshLit_var_ne _ _ (by decide))
        (freshLit_var_ne _ _ (by decide)))
      (by
        simp only [pad, emptyClauses, List.mem_map]
        exact ⟨(!(x (freshVar n 0)), !(x (freshVar n 1)), !(x (freshVar n 2))),
          mem_allSigns3 _, rfl⟩)
    rw [clauseSatisfied_mkClause] at hD
    simp [freshLit, literalFailureBit_not] at hD
  · refine ⟨a, by simp, ?_⟩
    have hD := hall
      (mkClause (liftLit a) (freshLit n 0 (!(x (freshVar n 0))))
        (freshLit n 1 (!(x (freshVar n 1))))
        (liftLit_var_ne_freshLit _ _ _) (liftLit_var_ne_freshLit _ _ _)
        (freshLit_var_ne _ _ (by decide)))
      (by
        simp only [pad, oneClauses, List.mem_map]
        exact ⟨(!(x (freshVar n 0)), !(x (freshVar n 1))), mem_allSigns2 _, rfl⟩)
    rw [clauseSatisfied_mkClause] at hD
    simpa [freshLit, literalFailureBit_not] using hD
  · have hD := hall
      (mkClause (liftLit a) (liftLit b) (freshLit n 0 (!(x (freshVar n 0))))
        (liftLit_var_ne (distinct_two hR)) (liftLit_var_ne_freshLit _ _ _)
        (liftLit_var_ne_freshLit _ _ _))
      (by
        simp only [pad, twoClauses, List.mem_map]
        exact ⟨!(x (freshVar n 0)), mem_allSigns1 _, rfl⟩)
    rw [clauseSatisfied_mkClause] at hD
    simp only [freshLit, literalFailureBit_not, Bool.true_eq_false, or_false] at hD
    rcases hD with h | h
    · exact ⟨a, by simp, h⟩
    · exact ⟨b, by simp, h⟩
  · have hD := hall
      (mkClause (liftLit a) (liftLit b) (liftLit c)
        (liftLit_var_ne (distinct_three_ab hR)) (liftLit_var_ne (distinct_three_ac hR))
        (liftLit_var_ne (distinct_three_bc hR)))
      (by simp [pad, threeClauses])
    rw [clauseSatisfied_mkClause] at hD
    rcases hD with h | h | h
    · exact ⟨a, by simp, h⟩
    · exact ⟨b, by simp, h⟩
    · exact ⟨c, by simp, h⟩
  · simp at hlen

theorem length_pad_le {n : ℕ} (R : ReducedClause n) : (pad R).length ≤ 8 := by
  obtain ⟨R, hR⟩ := R
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, R⟩⟩⟩⟩ <;>
    simp [pad, emptyClauses, oneClauses, twoClauses, threeClauses,
      allSigns3, allSigns2, allSigns1]

/-! ## Emitting the clauses of one general clause -/

/-- The clauses emitted for one general clause: nothing for a tautology,
otherwise the padding of the reduced clause. -/
def emit {n : ℕ} (C : GeneralClause n) : List (Clause (n + 3)) :=
  match reduce C with
  | none => []
  | some R => pad R

theorem emit_eq_none {n : ℕ} (C : GeneralClause n) (h : reduce C = none) :
    emit C = [] := by
  simp [emit, h]

theorem emit_eq_some {n : ℕ} (C : GeneralClause n) (R : ReducedClause n)
    (h : reduce C = some R) : emit C = pad R := by
  simp [emit, h]

theorem length_emit_le {n : ℕ} (C : GeneralClause n) : (emit C).length ≤ 8 := by
  cases h : reduce C with
  | none => simp [emit_eq_none C h]
  | some R =>
    rw [emit_eq_some C R h]
    exact length_pad_le R

theorem emit_satisfied_of_satisfied {n : ℕ} (C : GeneralClause n)
    (x : Fin n → Bool) (y : Fin 3 → Bool) (hC : GeneralClause.satisfied C x) :
    ∀ D ∈ emit C, clauseSatisfied D (Fin.append x y) := by
  obtain ⟨l, hl, hfail⟩ := hC
  cases hR : reduce C with
  | none => simp [emit_eq_none C hR]
  | some R =>
    rw [emit_eq_some C R hR]
    apply pad_satisfied R _ l ((mem_reduce C R hR l).mp hl)
    rw [literalFailureBit_liftLit_append]
    exact hfail

theorem satisfied_of_emit {n : ℕ} (C : GeneralClause n) (hw : C.length ≤ 3)
    (x : Fin (n + 3) → Bool) (hall : ∀ D ∈ emit C, clauseSatisfied D x) :
    GeneralClause.satisfied C (restrict x) := by
  cases hR : reduce C with
  | none =>
    obtain ⟨a, ha, b, hb, hab, hne⟩ := reduce_eq_none C hR
    exact satisfied_of_complementary C a b ha hb hab hne _
  | some R =>
    rw [emit_eq_some C R hR] at hall
    obtain ⟨l, hl, hfail⟩ :=
      pad_forces R ((reduce_length_le C R hR).trans hw) x hall
    exact ⟨l, (mem_reduce C R hR l).mpr hl, by
      rw [← literalFailureBit_liftLit]
      exact hfail⟩

/-! ## The normalisation map -/

/-- All emitted clauses, in clause order. -/
def clauseList (F : GeneralCNF) : List (Clause (F.numVars + 3)) :=
  (List.finRange F.numClauses).flatMap fun r => emit (F.clause r)

/-- Normalise a general 3-CNF formula to the distinct-variable three-literal
convention of `ThreeCNF`, over three additional variables. -/
def normalise (F : GeneralCNF) : ThreeCNF where
  numVars := F.numVars + 3
  numClauses := (clauseList F).length
  clause := fun i => (clauseList F).get i

theorem normalise_numVars (F : GeneralCNF) :
    (normalise F).numVars = F.numVars + 3 := rfl

theorem mem_clauseList {F : GeneralCNF} {D : Clause (F.numVars + 3)} :
    D ∈ clauseList F ↔ ∃ r, D ∈ emit (F.clause r) := by
  simp [clauseList, List.mem_flatMap, List.mem_finRange]

/-- Correctness of normalisation: satisfiability is preserved and reflected. -/
theorem normalise_satisfiable_iff (F : GeneralCNF) :
    F.Satisfiable ↔ (normalise F).Satisfiable := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨Fin.append x (fun _ => false), ?_⟩
    intro i
    show clauseSatisfied ((clauseList F).get i) _
    have hmem : (clauseList F).get i ∈ clauseList F := List.get_mem _ _
    obtain ⟨r, hr⟩ := mem_clauseList.mp hmem
    exact emit_satisfied_of_satisfied (F.clause r) x _ (hx r) _ hr
  · rintro ⟨x, hx⟩
    refine ⟨restrict x, ?_⟩
    intro r
    apply satisfied_of_emit (F.clause r) (F.width r) x
    intro D hD
    have hmem : D ∈ clauseList F := mem_clauseList.mpr ⟨r, hD⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
    have hi' := hx i
    rw [← hi]
    exact hi'

/-! ## Size bounds -/

theorem length_flatMap_le_eight {α β : Type*} (l : List α) (f : α → List β)
    (h : ∀ a ∈ l, (f a).length ≤ 8) :
    (l.flatMap f).length ≤ 8 * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h₁ := h a (by simp)
    have h₂ := ih (fun a' ha' => h a' (by simp [ha']))
    omega

theorem normalise_numClauses_le (F : GeneralCNF) :
    (normalise F).numClauses ≤ 8 * F.numClauses := by
  have h := length_flatMap_le_eight (List.finRange F.numClauses)
    (fun r => emit (F.clause r)) (fun r _ => length_emit_le _)
  rw [List.length_finRange] at h
  exact h

theorem normalise_cellSize_le (F : GeneralCNF) :
    (normalise F).cellSize ≤ 8 * F.cellSize := by
  have h := normalise_numClauses_le F
  simp only [ThreeCNF.cellSize, GeneralCNF.cellSize, normalise_numVars]
  omega

/-! ## Transfer of the clause-wise theorem to arbitrary 3-CNF syntax -/

/-- Thesis `thm:3sat-clausewise` for arbitrary 3-CNF syntax: `F` is
satisfiable iff the clause-wise objective of `normalise F` attains the value
`α n' - m'`. -/
theorem general_satisfiable_iff_minimum_value
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (F : GeneralCNF) (pinWeight : ℝ)
    (hdomination : ∀ i, variableDegree (normalise F).clause i < pinWeight) :
    F.Satisfiable ↔
      ∃ x : Parameter p (normalise F).numVars,
        (∀ y : Parameter p (normalise F).numVars,
          clausewiseLoss (normalise F).clause pinWeight x ≤
            clausewiseLoss (normalise F).clause pinWeight y) ∧
        clausewiseLoss (normalise F).clause pinWeight x =
          pinWeight * (normalise F).numVars - (normalise F).numClauses := by
  rw [normalise_satisfiable_iff]
  show (∃ b, FormulaSatisfied (normalise F).clause b) ↔ _
  rw [satisfiable_iff_minimum_value hp (normalise F).clause pinWeight hdomination,
    Fintype.card_fin]

/-- The same with the canonical pin weight `Δ + 1` of `FixedPrimeHardness`. -/
theorem general_satisfiable_iff_minimum_value_pinWeight
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (F : GeneralCNF) :
    F.Satisfiable ↔
      ∃ x : Parameter p (normalise F).numVars,
        (∀ y : Parameter p (normalise F).numVars,
          clausewiseLoss (normalise F).clause ((normalise F).pinWeight : ℝ) x ≤
            clausewiseLoss (normalise F).clause ((normalise F).pinWeight : ℝ) y) ∧
        clausewiseLoss (normalise F).clause ((normalise F).pinWeight : ℝ) x =
          ((normalise F).pinWeight : ℝ) * (normalise F).numVars -
            (normalise F).numClauses :=
  general_satisfiable_iff_minimum_value hp F _ (normalise F).variableDegree_lt_pinWeight

/-- Thesis `thm:3sat-clausewise` for arbitrary 3-CNF syntax, all four
clauses: global minimisers exist, are Boolean, the objective equals
`α n' - sat`, and satisfiability of the *original* formula is the
minimum-value criterion for the normalised one. -/
theorem general_three_sat_clausewise
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (F : GeneralCNF) (pinWeight : ℝ)
    (hdomination : ∀ i, variableDegree (normalise F).clause i < pinWeight) :
    (∃ x : Parameter p (normalise F).numVars,
      ∀ y : Parameter p (normalise F).numVars,
        clausewiseLoss (normalise F).clause pinWeight x ≤
          clausewiseLoss (normalise F).clause pinWeight y) ∧
    (∀ x : Parameter p (normalise F).numVars,
      (∀ y : Parameter p (normalise F).numVars,
        clausewiseLoss (normalise F).clause pinWeight x ≤
          clausewiseLoss (normalise F).clause pinWeight y) →
      InDomain (booleanDomain (p := p)) x) ∧
    (∀ x, clausewiseLoss (normalise F).clause pinWeight (embeddedBoolean (p := p) x) =
      pinWeight * (normalise F).numVars - satisfiedCount (normalise F).clause x) ∧
    (F.Satisfiable ↔
      ∃ x : Parameter p (normalise F).numVars,
        (∀ y : Parameter p (normalise F).numVars,
          clausewiseLoss (normalise F).clause pinWeight x ≤
            clausewiseLoss (normalise F).clause pinWeight y) ∧
        clausewiseLoss (normalise F).clause pinWeight x =
          pinWeight * (normalise F).numVars - (normalise F).numClauses) := by
  obtain ⟨h₁, h₂, h₃, _⟩ :=
    three_sat_clausewise hp (normalise F).clause pinWeight hdomination
  exact ⟨h₁, h₂, h₃, general_satisfiable_iff_minimum_value hp F pinWeight hdomination⟩

/-! ## Transfer of the fixed-prime reduction -/

/-- The fixed-prime signed reduction accepts arbitrary 3-CNF syntax. -/
theorem general_compileFixedPrime_correct (F : GeneralCNF) :
    F.Satisfiable ↔ (compileFixedPrime (normalise F)).Accepts :=
  (normalise_satisfiable_iff F).trans (compileFixedPrime_correct (normalise F))

/-- Cell writes of normalisation followed by the dense fixed-prime compiler. -/
def generalCellWrites (F : GeneralCNF) : ℕ :=
  (normalise F).cellSize + compileFixedPrimeCellWrites (normalise F)

theorem general_denseCellSize_le (F : GeneralCNF) :
    (compileFixedPrime (normalise F)).denseCellSize ≤ 392 * F.cellSize ^ 2 := by
  have h₁ := compileFixedPrime_size_polynomial (normalise F)
  have h₂ : (normalise F).cellSize ^ 2 ≤ (8 * F.cellSize) ^ 2 :=
    Nat.pow_le_pow_left (normalise_cellSize_le F) 2
  calc (compileFixedPrime (normalise F)).denseCellSize
      ≤ 6 * (normalise F).cellSize ^ 2 := h₁
    _ ≤ 6 * (8 * F.cellSize) ^ 2 := Nat.mul_le_mul_left 6 h₂
    _ = 384 * F.cellSize ^ 2 := by ring
    _ ≤ 392 * F.cellSize ^ 2 := Nat.mul_le_mul_right _ (by norm_num)

theorem general_cellWrites_le (F : GeneralCNF) :
    generalCellWrites F ≤ 392 * F.cellSize ^ 2 := by
  have h₁ := compileFixedPrime_cellWrites_polynomial (normalise F)
  have h₂ : (normalise F).cellSize ^ 2 ≤ (8 * F.cellSize) ^ 2 :=
    Nat.pow_le_pow_left (normalise_cellSize_le F) 2
  have h₃ := normalise_cellSize_le F
  have h₄ : F.cellSize ≤ F.cellSize ^ 2 := by
    rcases Nat.eq_zero_or_pos F.cellSize with h | h
    · simp [h]
    · exact Nat.le_self_pow (by norm_num) _
  calc generalCellWrites F
      = (normalise F).cellSize + compileFixedPrimeCellWrites (normalise F) := rfl
    _ ≤ 8 * F.cellSize + 6 * (normalise F).cellSize ^ 2 := Nat.add_le_add h₃ h₁
    _ ≤ 8 * F.cellSize ^ 2 + 6 * (8 * F.cellSize) ^ 2 :=
        Nat.add_le_add (Nat.mul_le_mul_left 8 h₄) (Nat.mul_le_mul_left 6 h₂)
    _ = 392 * F.cellSize ^ 2 := by ring

/-- The polynomial unit-cell reduction from general 3-CNF satisfiability to
the fixed-prime signed decision problem. -/
def generalPolynomialCellReduction :
    PolynomialCellReduction GeneralCNF.Satisfiable
      FixedPrimeSignedInstance.Accepts GeneralCNF.cellSize
      FixedPrimeSignedInstance.denseCellSize where
  map F := compileFixedPrime (normalise F)
  correct := general_compileFixedPrime_correct
  cellWrites := generalCellWrites
  sizeCoefficient := 392
  sizeExponent := 2
  outputSize_le := general_denseCellSize_le
  cellWrites_le := general_cellWrites_le

def FixedPrimeSignedDecisionIsGeneralThreeSATHardInCellModel : Prop :=
  Nonempty
    (PolynomialCellReduction GeneralCNF.Satisfiable
      FixedPrimeSignedInstance.Accepts GeneralCNF.cellSize
      FixedPrimeSignedInstance.denseCellSize)

theorem fixed_prime_signed_decision_is_general_three_sat_hard_in_cell_model :
    FixedPrimeSignedDecisionIsGeneralThreeSATHardInCellModel :=
  ⟨generalPolynomialCellReduction⟩

/-! ## The restricted syntax embeds into the general syntax -/

/-- View a distinct-variable three-literal formula as a general formula. -/
def threeCNFToGeneral (F : ThreeCNF) : GeneralCNF where
  numVars := F.numVars
  numClauses := F.numClauses
  clause r := [(F.clause r).literal 0, (F.clause r).literal 1, (F.clause r).literal 2]
  width _ := by simp

theorem clauseSatisfied_iff_general {n : ℕ} (C : Clause n) (x : Fin n → Bool) :
    clauseSatisfied C x ↔
      GeneralClause.satisfied [C.literal 0, C.literal 1, C.literal 2] x := by
  simp only [clauseSatisfied, GeneralClause.satisfied, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  cases literalFailureBit (C.literal 0) x <;> cases literalFailureBit (C.literal 1) x <;>
    cases literalFailureBit (C.literal 2) x <;> simp

theorem threeCNFToGeneral_satisfiable_iff (F : ThreeCNF) :
    (threeCNFToGeneral F).Satisfiable ↔ F.Satisfiable := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun r => (clauseSatisfied_iff_general _ x).mpr (hx r)⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, fun r => (clauseSatisfied_iff_general _ x).mp (hx r)⟩

/-! ## A worked example of the padding counts

Six general clauses over three variables: a unit clause (4 padded clauses),
a tautology `z₀ ∨ ¬z₀` (dropped), a two-literal clause (2), a two-literal
clause with a repeated literal (2), the empty clause (8), and a full clause
(1): `4 + 0 + 2 + 2 + 8 + 1 = 17` clauses over `3 + 3 = 6` variables. -/
def exampleFormula : GeneralCNF where
  numVars := 3
  numClauses := 6
  clause := ![[⟨0, false⟩], [⟨0, false⟩, ⟨0, true⟩], [⟨0, false⟩, ⟨1, false⟩],
    [⟨0, false⟩, ⟨0, false⟩, ⟨1, false⟩], [], [⟨0, false⟩, ⟨1, false⟩, ⟨2, false⟩]]
  width := by decide

example : (normalise exampleFormula).numClauses = 17 := by decide

example : (normalise exampleFormula).numVars = 6 := rfl

#print axioms normalise_satisfiable_iff
#print axioms normalise_numClauses_le
#print axioms normalise_cellSize_le
#print axioms general_satisfiable_iff_minimum_value
#print axioms general_three_sat_clausewise
#print axioms general_compileFixedPrime_correct
#print axioms fixed_prime_signed_decision_is_general_three_sat_hard_in_cell_model
#print axioms threeCNFToGeneral_satisfiable_iff

end PhdThesisLean.CNFNormalisation
