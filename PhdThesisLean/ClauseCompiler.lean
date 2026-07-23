import PhdThesisLean.FiniteDomainCompiler

namespace PhdThesisLean.ClauseCompiler

open scoped BigOperators
open PhdThesisLean.FiniteDomainCompiler

/-!
# Direct clause-wise 3-SAT compiler

This module formalises thesis Lemma `lem:3sat-row-indicator` and Theorem
`thm:3sat-clausewise` from
`thesis-statements/finite-domain-compilers.tex`.

Literals and three-literal clauses are represented explicitly; the clause
structure records the thesis assumption that the three variables are
distinct. Boolean `false` is embedded as the p-adic value zero (a true
propositional variable in the thesis convention), while Boolean `true` is
embedded as one. The compiled affine residual is proved equal to the sum of
the three literal-failure values minus three.

For `p > 3`, `clause_row_indicator` proves that the residual norm is exactly
the clause-satisfaction indicator. The headline theorem
`three_sat_clausewise` proves existence and Booleanity of global minimisers,
the exact `α n - sat` objective formula, and equivalence with maximum clause
satisfaction. `satisfiable_iff_minimum_value` proves the final minimum-value
criterion from the thesis theorem.
-/

theorem norm_two {p : ℕ} [Fact p.Prime] (hp : 3 < p) :
    ‖(2 : ℚ_[p])‖ = 1 := by
  change ‖((2 : ℕ) : ℚ_[p])‖ = 1
  rw [Padic.norm_natCast_eq_one_iff]
  apply (Nat.Prime.coprime_iff_not_dvd
    (p := p) (n := 2) Fact.out).mpr
  intro hdvd
  have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdvd
  omega

theorem norm_three {p : ℕ} [Fact p.Prime] (hp : 3 < p) :
    ‖(3 : ℚ_[p])‖ = 1 := by
  change ‖((3 : ℕ) : ℚ_[p])‖ = 1
  rw [Padic.norm_natCast_eq_one_iff]
  apply (Nat.Prime.coprime_iff_not_dvd
    (p := p) (n := 3) Fact.out).mpr
  intro hdvd
  have hle : p ≤ 3 := Nat.le_of_dvd (by omega) hdvd
  omega

def boolValue {p : ℕ} [Fact p.Prime] (b : Bool) : ℚ_[p] :=
  if b then 1 else 0

theorem threeBitIndicator
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (b₀ b₁ b₂ : Bool) :
    ‖(boolValue (p := p) b₀ - 1) +
        (boolValue (p := p) b₁ - 1) +
        (boolValue (p := p) b₂ - 1)‖ =
      if b₀ && b₁ && b₂ then 0 else 1 := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;>
    simp [boolValue] <;> ring_nf
  all_goals simp [norm_two hp, norm_three hp, norm_neg]

structure Literal (n : ℕ) where
  var : Fin n
  negated : Bool

structure Clause (n : ℕ) where
  literal : Fin 3 → Literal n
  variables_injective : Function.Injective fun k => (literal k).var

def literalFailureBit
    {n : ℕ} (l : Literal n) (x : Fin n → Bool) : Bool :=
  if l.negated then !(x l.var) else x l.var

def clauseSatisfied
    {n : ℕ} (C : Clause n) (x : Fin n → Bool) : Prop :=
  !(literalFailureBit (C.literal 0) x &&
      literalFailureBit (C.literal 1) x &&
      literalFailureBit (C.literal 2) x) = true

instance instDecidableClauseSatisfied
    {n : ℕ} (C : Clause n) (x : Fin n → Bool) :
    Decidable (clauseSatisfied C x) := by
  unfold clauseSatisfied
  infer_instance

def embeddedBoolean
    {p n : ℕ} [Fact p.Prime] (x : Fin n → Bool) : Parameter p n :=
  fun i => boolValue (x i)

def literalFailureValue
    {p n : ℕ} [Fact p.Prime] (l : Literal n)
    (x : Parameter p n) : ℚ_[p] :=
  if l.negated then 1 - x l.var else x l.var

theorem literalFailureValue_embeddedBoolean
    {p n : ℕ} [Fact p.Prime] (l : Literal n) (x : Fin n → Bool) :
    literalFailureValue l (embeddedBoolean (p := p) x) =
      boolValue (literalFailureBit l x) := by
  cases hneg : l.negated <;> cases hx : x l.var <;>
    simp [literalFailureValue, embeddedBoolean, literalFailureBit,
      boolValue, hneg, hx]

def literalSign (l : Literal n) : ℤ :=
  if l.negated then -1 else 1

def clauseCoeff (C : Clause n) (i : Fin n) : ℤ :=
  ∑ k, if (C.literal k).var = i then literalSign (C.literal k) else 0

def clauseTarget (C : Clause n) : ℤ :=
  ∑ k, if (C.literal k).negated then 0 else 1

theorem clauseCoeff_ne_zero_iff
    {n : ℕ} (C : Clause n) (i : Fin n) :
    clauseCoeff C i ≠ 0 ↔ ∃ k, (C.literal k).var = i := by
  classical
  constructor
  · intro hne
    by_contra hnone
    push_neg at hnone
    apply hne
    rw [clauseCoeff]
    apply Finset.sum_eq_zero
    intro k _
    simp [hnone k]
  · rintro ⟨k, hk⟩
    rw [clauseCoeff]
    have hsum :
        (∑ j, if (C.literal j).var = i
          then literalSign (C.literal j) else 0) =
          (if (C.literal k).var = i
            then literalSign (C.literal k) else 0) := by
      apply Finset.sum_eq_single k
      · intro j _ hjk
        have hvars : (C.literal j).var ≠ i := by
          intro hj
          apply hjk
          exact C.variables_injective (hj.trans hk.symm)
        simp [hvars]
      · simp
    rw [hsum]
    cases hneg : (C.literal k).negated <;>
      simp [hk, literalSign, hneg]

noncomputable def clauseObservation
    {p n : ℕ} [Fact p.Prime] (C : Clause n) :
    AffineObservation p n where
  sign := -1
  weight := 1
  coeff i := (clauseCoeff C i : ℚ_[p])
  target := (clauseTarget C : ℚ_[p])

theorem clauseObservation_sign
    {p n : ℕ} [Fact p.Prime] (C : Clause n) :
    |(clauseObservation (p := p) C).sign| = 1 := by
  simp [clauseObservation]

theorem clauseObservation_weight
    {p n : ℕ} [Fact p.Prime] (C : Clause n) :
    0 ≤ (clauseObservation (p := p) C).weight := by
  simp [clauseObservation]

theorem clauseObservation_coeff_norm
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (i : Fin n) :
    ‖(clauseObservation (p := p) C).coeff i‖ ≤ 1 := by
  simpa [clauseObservation] using
    Padic.norm_int_le_one (p := p) (clauseCoeff C i)

theorem clauseResidual_eq_failureSum
    {p n : ℕ} [Fact p.Prime] (C : Clause n) (x : Parameter p n) :
    affineResidual (clauseObservation (p := p) C) x =
      ∑ k, (literalFailureValue (C.literal k) x - 1) := by
  classical
  rw [affineResidual, clauseObservation]
  simp only [clauseCoeff, clauseTarget, Int.cast_sum, Int.cast_ite,
    Int.cast_zero, Int.cast_one]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hdot :
      (∑ k : Fin 3, ∑ i : Fin n,
          (if (C.literal k).var = i
            then ((literalSign (C.literal k) : ℤ) : ℚ_[p]) else 0) * x i) =
        ∑ k : Fin 3,
          ((literalSign (C.literal k) : ℤ) : ℚ_[p]) *
            x (C.literal k).var := by
    apply Finset.sum_congr rfl
    intro k _
    simp_rw [ite_mul, zero_mul]
    rw [Fintype.sum_ite_eq]
  rw [hdot, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  cases hneg : (C.literal k).negated
  · simp [literalSign, literalFailureValue, hneg]
  · simp [literalSign, literalFailureValue, hneg]

theorem clause_row_indicator
    {p n : ℕ} [Fact p.Prime] (hp : 3 < p)
    (C : Clause n) (x : Fin n → Bool) :
    ‖affineResidual (clauseObservation (p := p) C)
        (embeddedBoolean (p := p) x)‖ =
      if clauseSatisfied C x then 1 else 0 := by
  classical
  rw [clauseResidual_eq_failureSum]
  simp_rw [literalFailureValue_embeddedBoolean]
  rw [show (∑ k : Fin 3,
      (boolValue (literalFailureBit (C.literal k) x) - 1)) =
      (boolValue (literalFailureBit (C.literal 0) x) - 1) +
      (boolValue (literalFailureBit (C.literal 1) x) - 1) +
      (boolValue (literalFailureBit (C.literal 2) x) - 1) by
        simp [Fin.sum_univ_succ, add_assoc]
        ring]
  rw [threeBitIndicator hp]
  cases h₀ : literalFailureBit (C.literal 0) x <;>
    cases h₁ : literalFailureBit (C.literal 1) x <;>
    cases h₂ : literalFailureBit (C.literal 2) x <;>
    simp [clauseSatisfied, h₀, h₁, h₂]

noncomputable def booleanDomain
    {p n : ℕ} [Fact p.Prime] (_i : Fin n) : Finset ℚ_[p] := by
  classical
  exact {0, 1}

theorem booleanDomain_nonempty
    {p n : ℕ} [Fact p.Prime] (i : Fin n) :
    (booleanDomain (p := p) i).Nonempty := by
  exact ⟨0, by simp [booleanDomain]⟩

theorem booleanDomain_unitSeparated
    {p n : ℕ} [Fact p.Prime] (i : Fin n) :
    UnitSeparated (booleanDomain (p := p) i) := by
  intro a ha b hb hab
  simp only [booleanDomain, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · simp
  · simp
  · exact (hab rfl).elim

theorem embeddedBoolean_inDomain
    {p n : ℕ} [Fact p.Prime] (x : Fin n → Bool) :
    InDomain (booleanDomain (p := p)) (embeddedBoolean (p := p) x) := by
  intro i
  cases x i <;> simp [booleanDomain, embeddedBoolean, boolValue]

theorem inBooleanDomain_exists_embedded
    {p n : ℕ} [Fact p.Prime] (x : Parameter p n)
    (hx : InDomain (booleanDomain (p := p)) x) :
    ∃ b : Fin n → Bool, embeddedBoolean (p := p) b = x := by
  classical
  let b : Fin n → Bool := fun i => if x i = 0 then false else true
  refine ⟨b, ?_⟩
  funext i
  have hxi : x i = 0 ∨ x i = 1 := by
    simpa [booleanDomain] using hx i
  rcases hxi with hzero | hone
  · simp [b, embeddedBoolean, boolValue, hzero]
  · simp [b, embeddedBoolean, boolValue, hone]

noncomputable def variableDegree
    {n : ℕ} {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (i : Fin n) : ℝ := by
  classical
  exact ∑ r, if ∃ k, ((Φ r).literal k).var = i then 1 else 0

theorem incidentWeight_clauseObservation
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (i : Fin n) :
    incidentWeight (fun r => clauseObservation (p := p) (Φ r)) i =
      variableDegree Φ i := by
  classical
  rw [incidentWeight, variableDegree]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hoccurs : ∃ k, ((Φ r).literal k).var = i
  · have hne : clauseCoeff (Φ r) i ≠ 0 :=
      (clauseCoeff_ne_zero_iff (Φ r) i).mpr hoccurs
    simp [clauseObservation, hoccurs, hne]
  · have hzero : clauseCoeff (Φ r) i = 0 :=
      not_ne_iff.mp ((clauseCoeff_ne_zero_iff (Φ r) i).not.mpr hoccurs)
    simp [clauseObservation, hoccurs, hzero]

noncomputable def satisfiedCount
    {n : ℕ} {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (x : Fin n → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter fun r => clauseSatisfied (Φ r) x).card

noncomputable def clausewiseLoss
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (pinWeight : ℝ) (x : Parameter p n) : ℝ :=
  compilerLoss (booleanDomain (p := p)) (fun _ => pinWeight)
    (fun r => clauseObservation (p := p) (Φ r)) x

theorem clausewiseLoss_on_boolean
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (hp : 3 < p) (Φ : κ → Clause n) (pinWeight : ℝ)
    (x : Fin n → Bool) :
    clausewiseLoss Φ pinWeight (embeddedBoolean (p := p) x) =
      pinWeight * n - satisfiedCount Φ x := by
  classical
  have hxD := embeddedBoolean_inDomain (p := p) x
  have hpin :
      pinningLoss (booleanDomain (p := p)) (fun _ => pinWeight)
          (embeddedBoolean (p := p) x) =
        pinWeight * n := by
    rw [pinningLoss_on_domain (booleanDomain (p := p)) (fun _ => pinWeight)
      booleanDomain_unitSeparated _ hxD, domainPinningConstant]
    simp [booleanDomain]
    ring
  have hinteraction :
      interactionLoss (fun r => clauseObservation (p := p) (Φ r))
          (embeddedBoolean (p := p) x) =
        -(satisfiedCount Φ x : ℝ) := by
    rw [interactionLoss, satisfiedCount]
    simp_rw [clause_row_indicator hp]
    simp only [clauseObservation]
    have hindicator :
        (∑ r : κ, if clauseSatisfied (Φ r) x then (1 : ℝ) else 0) =
          ((Finset.univ.filter fun r => clauseSatisfied (Φ r) x).card : ℝ) := by
      simp
    simp only [neg_one_mul]
    rw [Finset.sum_neg_distrib, hindicator]
  rw [clausewiseLoss, compilerLoss, hpin, hinteraction]
  ring

def MaximizesSatisfied
    {n : ℕ} {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (x : Fin n → Bool) : Prop :=
  ∀ y, satisfiedCount Φ y ≤ satisfiedCount Φ x

theorem globalMin_clausewiseLoss_iff_maximizesSatisfied
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (hp : 3 < p) (Φ : κ → Clause n) (pinWeight : ℝ)
    (hdomination : ∀ i, variableDegree Φ i < pinWeight)
    (x : Fin n → Bool) :
    (∀ y : Parameter p n,
      clausewiseLoss Φ pinWeight (embeddedBoolean (p := p) x) ≤
      clausewiseLoss Φ pinWeight y) ↔
      MaximizesSatisfied Φ x := by
  let T : κ → AffineObservation p n :=
    fun r => clauseObservation (p := p) (Φ r)
  have hdomination' : ∀ i,
      incidentWeight T i < (fun _ => pinWeight) i := by
    intro i
    rw [incidentWeight_clauseObservation Φ i]
    exact hdomination i
  have hsign : ∀ r, |(T r).sign| = 1 :=
    fun r => clauseObservation_sign (p := p) (Φ r)
  have hweight : ∀ r, 0 ≤ (T r).weight :=
    fun r => clauseObservation_weight (p := p) (Φ r)
  have hcoeff : ∀ r i, ‖(T r).coeff i‖ ≤ 1 :=
    fun r i => clauseObservation_coeff_norm (p := p) (Φ r) i
  constructor
  · intro hmin y
    have hxy := hmin (embeddedBoolean (p := p) y)
    rw [clausewiseLoss_on_boolean hp Φ pinWeight x,
      clausewiseLoss_on_boolean hp Φ pinWeight y] at hxy
    exact_mod_cast (by linarith :
      (satisfiedCount Φ y : ℝ) ≤ satisfiedCount Φ x)
  · intro hmax y
    obtain ⟨z, hzD, hzy⟩ :=
      exists_inDomain_not_greater (booleanDomain (p := p))
        (fun _ => pinWeight) T booleanDomain_nonempty
        booleanDomain_unitSeparated hdomination' hsign hweight hcoeff y
    obtain ⟨b, rfl⟩ := inBooleanDomain_exists_embedded z hzD
    have hcount := hmax b
    have hloss :
        clausewiseLoss Φ pinWeight (embeddedBoolean (p := p) x) ≤
          clausewiseLoss Φ pinWeight (embeddedBoolean (p := p) b) := by
      rw [clausewiseLoss_on_boolean hp Φ pinWeight x,
        clausewiseLoss_on_boolean hp Φ pinWeight b]
      have hcountR :
          (satisfiedCount Φ b : ℝ) ≤ satisfiedCount Φ x := by
        exact_mod_cast hcount
      linarith
    exact hloss.trans (by simpa [clausewiseLoss, T] using hzy)

theorem clausewise_globalMin_inBooleanDomain
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (pinWeight : ℝ)
    (hdomination : ∀ i, variableDegree Φ i < pinWeight)
    (x : Parameter p n)
    (hmin : ∀ y : Parameter p n,
      clausewiseLoss Φ pinWeight x ≤ clausewiseLoss Φ pinWeight y) :
    InDomain (booleanDomain (p := p)) x := by
  let T : κ → AffineObservation p n :=
    fun r => clauseObservation (p := p) (Φ r)
  apply compiler_global_minimizer_inDomain
    (booleanDomain (p := p)) (fun _ => pinWeight) T
    booleanDomain_nonempty booleanDomain_unitSeparated
  · intro i
    rw [incidentWeight_clauseObservation Φ i]
    exact hdomination i
  · exact fun r => clauseObservation_sign (p := p) (Φ r)
  · exact fun r => clauseObservation_weight (p := p) (Φ r)
  · exact fun r i => clauseObservation_coeff_norm (p := p) (Φ r) i
  · simpa [clausewiseLoss, T] using hmin

theorem exists_clausewise_globalMin
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (pinWeight : ℝ)
    (hdomination : ∀ i, variableDegree Φ i < pinWeight) :
    ∃ x : Parameter p n, ∀ y : Parameter p n,
      clausewiseLoss Φ pinWeight x ≤ clausewiseLoss Φ pinWeight y := by
  let T : κ → AffineObservation p n :=
    fun r => clauseObservation (p := p) (Φ r)
  obtain ⟨x, _, hmin⟩ :=
    exists_compiler_global_minimizer
      (booleanDomain (p := p)) (fun _ => pinWeight) T
      booleanDomain_nonempty booleanDomain_unitSeparated
      (fun i => by
        rw [incidentWeight_clauseObservation Φ i]
        exact hdomination i)
      (fun r => clauseObservation_sign (p := p) (Φ r))
      (fun r => clauseObservation_weight (p := p) (Φ r))
      (fun r i => clauseObservation_coeff_norm (p := p) (Φ r) i)
  exact ⟨x, by simpa [clausewiseLoss, T] using hmin⟩

theorem three_sat_clausewise
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (hp : 3 < p) (Φ : κ → Clause n) (pinWeight : ℝ)
    (hdomination : ∀ i, variableDegree Φ i < pinWeight) :
    (∃ x : Parameter p n, ∀ y : Parameter p n,
      clausewiseLoss Φ pinWeight x ≤ clausewiseLoss Φ pinWeight y) ∧
    (∀ x : Parameter p n, (∀ y : Parameter p n,
      clausewiseLoss Φ pinWeight x ≤ clausewiseLoss Φ pinWeight y) →
      InDomain (booleanDomain (p := p)) x) ∧
    (∀ x, clausewiseLoss Φ pinWeight (embeddedBoolean (p := p) x) =
      pinWeight * n - satisfiedCount Φ x) ∧
    (∀ x, (∀ y : Parameter p n,
      clausewiseLoss Φ pinWeight (embeddedBoolean (p := p) x) ≤
        clausewiseLoss Φ pinWeight y) ↔ MaximizesSatisfied Φ x) := by
  exact ⟨exists_clausewise_globalMin Φ pinWeight hdomination,
    fun x => clausewise_globalMin_inBooleanDomain Φ pinWeight hdomination x,
    clausewiseLoss_on_boolean hp Φ pinWeight,
    globalMin_clausewiseLoss_iff_maximizesSatisfied hp Φ pinWeight hdomination⟩

def FormulaSatisfied
    {n : ℕ} {κ : Type*}
    (Φ : κ → Clause n) (x : Fin n → Bool) : Prop :=
  ∀ r, clauseSatisfied (Φ r) x

theorem satisfiedCount_eq_card_iff
    {n : ℕ} {κ : Type*} [Fintype κ]
    (Φ : κ → Clause n) (x : Fin n → Bool) :
    satisfiedCount Φ x = Fintype.card κ ↔ FormulaSatisfied Φ x := by
  classical
  constructor
  · intro hcount r
    have hcard :
        (Finset.univ.filter fun j => clauseSatisfied (Φ j) x).card =
          (Finset.univ : Finset κ).card := by
      simpa [satisfiedCount] using hcount
    have heq :
        Finset.univ.filter (fun j => clauseSatisfied (Φ j) x) =
          Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hcard.ge
    have hr : r ∈ Finset.univ.filter
        (fun j => clauseSatisfied (Φ j) x) := by
      rw [heq]
      exact Finset.mem_univ r
    exact (Finset.mem_filter.mp hr).2
  · intro hall
    rw [satisfiedCount]
    have heq :
        Finset.univ.filter (fun j => clauseSatisfied (Φ j) x) =
          Finset.univ := by
      ext r
      simp [hall r]
    rw [heq, Finset.card_univ]

theorem satisfiable_iff_minimum_value
    {p n : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    (hp : 3 < p) (Φ : κ → Clause n) (pinWeight : ℝ)
    (hdomination : ∀ i, variableDegree Φ i < pinWeight) :
    (∃ b : Fin n → Bool, FormulaSatisfied Φ b) ↔
      ∃ x : Parameter p n,
        (∀ y : Parameter p n,
          clausewiseLoss Φ pinWeight x ≤ clausewiseLoss Φ pinWeight y) ∧
        clausewiseLoss Φ pinWeight x =
          pinWeight * n - Fintype.card κ := by
  constructor
  · rintro ⟨b, hb⟩
    have hcount :
        satisfiedCount Φ b = Fintype.card κ :=
      (satisfiedCount_eq_card_iff Φ b).mpr hb
    refine ⟨embeddedBoolean (p := p) b, ?_, ?_⟩
    · rw [globalMin_clausewiseLoss_iff_maximizesSatisfied hp Φ pinWeight
        hdomination b]
      intro c
      rw [hcount]
      rw [satisfiedCount, ← Finset.card_univ]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    · rw [clausewiseLoss_on_boolean hp Φ pinWeight b, hcount]
  · rintro ⟨x, hmin, hvalue⟩
    have hxD :=
      clausewise_globalMin_inBooleanDomain Φ pinWeight hdomination x hmin
    obtain ⟨b, rfl⟩ := inBooleanDomain_exists_embedded x hxD
    refine ⟨b, (satisfiedCount_eq_card_iff Φ b).mp ?_⟩
    rw [clausewiseLoss_on_boolean hp Φ pinWeight b] at hvalue
    exact_mod_cast (by linarith :
      (satisfiedCount Φ b : ℝ) = Fintype.card κ)

end PhdThesisLean.ClauseCompiler
