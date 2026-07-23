import PhdThesisLean.ClauseCompiler

namespace PhdThesisLean.FixedPrimeHardness

open scoped BigOperators
open PhdThesisLean.FiniteDomainCompiler
open PhdThesisLean.ClauseCompiler

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-!
# Fixed-prime hardness reduction

This module formalises the reduction premise of thesis Corollary
`cor:signed-nphard` from
`thesis-statements/finite-domain-compilers.tex`.

`ThreeCNF` is an explicitly finite three-CNF syntax and
`FixedPrimeSignedInstance` is the Boolean-pinned, unit-negative-row subclass of
signed affine residual decision instances at the fixed prime `p = 5`.
`compileFixedPrime_correct` proves the many-one semantic equivalence:
a formula is satisfiable exactly when its compiled objective attains a value
at most `α n - m`, with `α = 1 + Δ`. The theorem
`global_optimizer_decides_three_sat` records the optimisation consequence:
any exact global optimiser decides the source formula.

The file also makes the encoding model explicit. In the documented unit-cell
model, the dense expansion has `2n + m` observations and the exact cell-write
count is quadratic in the source syntax size. The resulting
`PolynomialCellReduction` is a closed, machine-checked 3-SAT-hardness result
for that model.

Mathlib at the pinned revision has computable many-one reductions but no
formal P, NP, Cook-Levin, or polynomial-time Turing-machine framework.
Consequently this module does not disguise the standard external theorem
"3-SAT is NP-hard" as a proved Lean premise. It proves the full concrete
reduction and its syntactic polynomial bound; connecting that result to a
future bit-level P/NP library remains a separate foundational step.
-/

structure ThreeCNF where
  numVars : ℕ
  numClauses : ℕ
  clause : Fin numClauses → Clause numVars

def ThreeCNF.Satisfiable (F : ThreeCNF) : Prop :=
  ∃ x : Fin F.numVars → Bool, FormulaSatisfied F.clause x

def ThreeCNF.occurrenceCount (F : ThreeCNF) (i : Fin F.numVars) : ℕ :=
  (Finset.univ.filter fun r =>
    ∃ k, ((F.clause r).literal k).var = i).card

def ThreeCNF.maxOccurrence (F : ThreeCNF) : ℕ :=
  Finset.univ.sup F.occurrenceCount

def ThreeCNF.pinWeight (F : ThreeCNF) : ℕ :=
  F.maxOccurrence + 1

theorem ThreeCNF.occurrenceCount_le_maxOccurrence
    (F : ThreeCNF) (i : Fin F.numVars) :
    F.occurrenceCount i ≤ F.maxOccurrence := by
  exact Finset.le_sup (f := F.occurrenceCount) (Finset.mem_univ i)

theorem ThreeCNF.variableDegree_eq_occurrenceCount
    (F : ThreeCNF) (i : Fin F.numVars) :
    variableDegree F.clause i = F.occurrenceCount i := by
  classical
  rw [variableDegree, ThreeCNF.occurrenceCount]
  simp

theorem ThreeCNF.variableDegree_lt_pinWeight
    (F : ThreeCNF) (i : Fin F.numVars) :
    variableDegree F.clause i < F.pinWeight := by
  rw [F.variableDegree_eq_occurrenceCount]
  exact_mod_cast Nat.lt_succ_of_le (F.occurrenceCount_le_maxOccurrence i)

structure IntegerAffineRow (n : ℕ) where
  coeff : Fin n → ℤ
  target : ℤ

structure FixedPrimeSignedInstance where
  numVars : ℕ
  numRows : ℕ
  row : Fin numRows → IntegerAffineRow numVars
  pinWeight : ℕ
  threshold : ℤ

noncomputable def FixedPrimeSignedInstance.loss
    (I : FixedPrimeSignedInstance)
    (x : Parameter 5 I.numVars) : ℝ :=
  (I.pinWeight : ℝ) *
      ∑ i, (‖x i‖ + ‖x i - 1‖) -
    ∑ r, ‖(∑ i, ((I.row r).coeff i : ℚ_[5]) * x i) -
      ((I.row r).target : ℚ_[5])‖

def FixedPrimeSignedInstance.Accepts (I : FixedPrimeSignedInstance) : Prop :=
  ∃ x : Parameter 5 I.numVars, I.loss x ≤ (I.threshold : ℝ)

def compileFixedPrime (F : ThreeCNF) : FixedPrimeSignedInstance where
  numVars := F.numVars
  numRows := F.numClauses
  row r := {
    coeff := clauseCoeff (F.clause r)
    target := clauseTarget (F.clause r)
  }
  pinWeight := F.pinWeight
  threshold :=
    (F.pinWeight * F.numVars : ℕ) - (F.numClauses : ℤ)

theorem compileFixedPrime_loss
    (F : ThreeCNF) (x : Parameter 5 F.numVars) :
    (compileFixedPrime F).loss x =
      clausewiseLoss F.clause (F.pinWeight : ℝ) x := by
  rw [FixedPrimeSignedInstance.loss, clausewiseLoss, compilerLoss,
    pinningLoss, interactionLoss]
  simp [compileFixedPrime, unaryCost, booleanDomain, clauseObservation,
    affineResidual]
  rw [Finset.mul_sum]
  ring

theorem compileFixedPrime_threshold
    (F : ThreeCNF) :
    ((compileFixedPrime F).threshold : ℝ) =
      (F.pinWeight : ℝ) * F.numVars - F.numClauses := by
  simp [compileFixedPrime]

theorem compileFixedPrime_correct
    (F : ThreeCNF) :
    F.Satisfiable ↔ (compileFixedPrime F).Accepts := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨embeddedBoolean (p := 5) b, ?_⟩
    rw [compileFixedPrime_loss, compileFixedPrime_threshold,
      clausewiseLoss_on_boolean (by norm_num) F.clause
        (F.pinWeight : ℝ) b,
      (satisfiedCount_eq_card_iff F.clause b).mpr hb]
    simp
  · rintro ⟨x, hx⟩
    have hdomination : ∀ i,
        variableDegree F.clause i < (F.pinWeight : ℝ) :=
      F.variableDegree_lt_pinWeight
    obtain ⟨g, hgmin⟩ :=
      exists_clausewise_globalMin (p := 5) F.clause
        (F.pinWeight : ℝ) hdomination
    have hgD :=
      clausewise_globalMin_inBooleanDomain (p := 5) F.clause
        (F.pinWeight : ℝ) hdomination g hgmin
    obtain ⟨b, rfl⟩ := inBooleanDomain_exists_embedded (p := 5) g hgD
    refine ⟨b, (satisfiedCount_eq_card_iff F.clause b).mp ?_⟩
    have hbound := (hgmin x).trans
      (by simpa [compileFixedPrime_loss, compileFixedPrime_threshold] using hx)
    rw [clausewiseLoss_on_boolean (by norm_num) F.clause
      (F.pinWeight : ℝ) b] at hbound
    have hle :
        satisfiedCount F.clause b ≤ F.numClauses := by
      rw [satisfiedCount]
      have hsubset :
          (Finset.univ.filter fun r : Fin F.numClauses =>
            clauseSatisfied (F.clause r) b) ⊆ Finset.univ :=
        Finset.filter_subset _ _
      simpa using Finset.card_le_card hsubset
    have hge : F.numClauses ≤ satisfiedCount F.clause b := by
      exact_mod_cast (by linarith :
        (F.numClauses : ℝ) ≤ satisfiedCount F.clause b)
    simpa using Nat.le_antisymm hle hge

theorem ThreeCNF.occurrenceCount_le_numClauses
    (F : ThreeCNF) (i : Fin F.numVars) :
    F.occurrenceCount i ≤ F.numClauses := by
  rw [ThreeCNF.occurrenceCount]
  simpa using Finset.card_le_card
    (Finset.filter_subset
      (fun r : Fin F.numClauses =>
        ∃ k, ((F.clause r).literal k).var = i) Finset.univ)

theorem ThreeCNF.maxOccurrence_le_numClauses (F : ThreeCNF) :
    F.maxOccurrence ≤ F.numClauses := by
  rw [ThreeCNF.maxOccurrence]
  apply Finset.sup_le
  intro i _
  exact F.occurrenceCount_le_numClauses i

theorem ThreeCNF.pinWeight_le_numClauses_add_one (F : ThreeCNF) :
    F.pinWeight ≤ F.numClauses + 1 := by
  exact Nat.add_le_add_right F.maxOccurrence_le_numClauses 1

/-- Unit-cell size of the explicit 3-CNF syntax: one variable slot per
variable, two scalar cells per literal, three literals per clause, and two
header cells. This is deliberately a unit-cost syntactic model, not a binary
Turing-machine encoding. -/
def ThreeCNF.cellSize (F : ThreeCNF) : ℕ :=
  F.numVars + 6 * F.numClauses + 2

/-- Number of signed observations after expanding the two Boolean pinning
rows for each variable and one reward row for each clause. -/
def FixedPrimeSignedInstance.observationCount
    (I : FixedPrimeSignedInstance) : ℕ :=
  2 * I.numVars + I.numRows

/-- Dense unit-cell encoding size: each observation stores `n` coefficients,
a sign, a weight, and a target; two header/threshold cells are also stored. -/
def FixedPrimeSignedInstance.denseCellSize
    (I : FixedPrimeSignedInstance) : ℕ :=
  I.observationCount * (I.numVars + 3) + 2

/-- Exact cell-write count of the straightforward dense compiler. -/
def compileFixedPrimeCellWrites (F : ThreeCNF) : ℕ :=
  (2 * F.numVars + F.numClauses) * (F.numVars + 3) + 2

theorem compileFixedPrime_observationCount (F : ThreeCNF) :
    (compileFixedPrime F).observationCount =
      2 * F.numVars + F.numClauses := by
  rfl

theorem compileFixedPrime_denseCellSize (F : ThreeCNF) :
    (compileFixedPrime F).denseCellSize =
      compileFixedPrimeCellWrites F := by
  rfl

theorem compileFixedPrime_size_polynomial (F : ThreeCNF) :
    (compileFixedPrime F).denseCellSize ≤ 6 * F.cellSize ^ 2 := by
  rw [compileFixedPrime_denseCellSize]
  simp only [compileFixedPrimeCellWrites, ThreeCNF.cellSize]
  nlinarith [Nat.zero_le F.numVars, Nat.zero_le F.numClauses]

theorem compileFixedPrime_cellWrites_polynomial (F : ThreeCNF) :
    compileFixedPrimeCellWrites F ≤ 6 * F.cellSize ^ 2 := by
  simpa [compileFixedPrime_denseCellSize] using
    compileFixedPrime_size_polynomial F

structure PolynomialCellReduction
    {α β : Type*} (source : α → Prop) (target : β → Prop)
    (sourceSize : α → ℕ) (targetSize : β → ℕ) where
  map : α → β
  correct : ∀ a, source a ↔ target (map a)
  cellWrites : α → ℕ
  sizeCoefficient : ℕ
  sizeExponent : ℕ
  outputSize_le : ∀ a,
    targetSize (map a) ≤ sizeCoefficient * (sourceSize a) ^ sizeExponent
  cellWrites_le : ∀ a,
    cellWrites a ≤ sizeCoefficient * (sourceSize a) ^ sizeExponent

def fixedPrimePolynomialCellReduction :
    PolynomialCellReduction ThreeCNF.Satisfiable
      FixedPrimeSignedInstance.Accepts ThreeCNF.cellSize
      FixedPrimeSignedInstance.denseCellSize where
  map := compileFixedPrime
  correct := compileFixedPrime_correct
  cellWrites := compileFixedPrimeCellWrites
  sizeCoefficient := 6
  sizeExponent := 2
  outputSize_le := compileFixedPrime_size_polynomial
  cellWrites_le := compileFixedPrime_cellWrites_polynomial

def FixedPrimeSignedDecisionIsThreeSATHardInCellModel : Prop :=
  Nonempty
    (PolynomialCellReduction ThreeCNF.Satisfiable
      FixedPrimeSignedInstance.Accepts ThreeCNF.cellSize
      FixedPrimeSignedInstance.denseCellSize)

theorem fixed_prime_signed_decision_is_three_sat_hard_in_cell_model :
    FixedPrimeSignedDecisionIsThreeSATHardInCellModel :=
  ⟨fixedPrimePolynomialCellReduction⟩

theorem global_optimizer_decides_three_sat
    (solve : (I : FixedPrimeSignedInstance) → Parameter 5 I.numVars)
    (optimal : ∀ (I : FixedPrimeSignedInstance)
      (y : Parameter 5 I.numVars), I.loss (solve I) ≤ I.loss y)
    (F : ThreeCNF) :
    F.Satisfiable ↔
      (compileFixedPrime F).loss (solve (compileFixedPrime F)) ≤
        ((compileFixedPrime F).threshold : ℝ) := by
  rw [compileFixedPrime_correct]
  constructor
  · rintro ⟨x, hx⟩
    exact (optimal (compileFixedPrime F) x).trans hx
  · intro h
    exact ⟨solve (compileFixedPrime F), h⟩

end PhdThesisLean.FixedPrimeHardness
