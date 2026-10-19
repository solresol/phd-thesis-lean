import PhdThesisLean.AllDifferentCSPObjectiveAssembly

/-!
# The all-different CSP corollary, including bit-level construction

The concrete compiler consumes a checked Boolean encoding and emits a checked
Boolean encoding of signed weighted affine residual rows. Their interpretation
below agrees exactly with the dependent semantic compiler, including the prime
and variable-count headers. The final theorem joins polynomial-time execution,
complete output-bit size, prime selection, attainment and both minimizer claims.
-/

namespace PhdThesisLean.AllDifferentCSPEncoding

open PhdThesisLean.FiniteDomainCompiler
open PhdThesisLean.AllDifferent
open PhdThesisLean.AllDifferentCSP

namespace RuntimeResidualRow

/-- Direct affine interpretation of a serialized row; indices are natural numbers. -/
noncomputable def observation {n p : ℕ} [Fact p.Prime] :
    RuntimeResidualRow → AffineObservation p n
  | .pin i a w => {
      sign := 1
      weight := w
      coeff := fun j => if j.val = i then 1 else 0
      target := a }
  | .unequal i j => {
      sign := -1
      weight := 1
      coeff := fun k => if k.val = i then 1 else if k.val = j then -1 else 0
      target := 0 }

/-- Erasing finite indices for serialization preserves the entire affine row. -/
@[simp]
theorem observation_ofResidualRow {n p : ℕ} [Fact p.Prime]
    (row : ExplicitSystem.ResidualRow n) :
    (ofResidualRow row).observation (n := n) (p := p) = row.observation (p := p) := by
  cases row <;>
    simp [ofResidualRow, observation, ExplicitSystem.ResidualRow.observation,
      edgeObservation, Fin.ext_iff]

noncomputable def loss {n p : ℕ} [Fact p.Prime] (row : RuntimeResidualRow)
    (z : Parameter p n) : ℝ :=
  let t := row.observation (n := n) (p := p)
  t.sign * t.weight * ‖affineResidual t z‖

@[simp]
theorem loss_ofResidualRow {n p : ℕ} [Fact p.Prime]
    (row : ExplicitSystem.ResidualRow n) (z : Parameter p n) :
    (ofResidualRow row).loss z = row.loss z := by
  simp [loss, ExplicitSystem.ResidualRow.loss]

end RuntimeResidualRow

namespace RuntimeObjective

/-- Interpret the emitted rows at precisely the emitted prime and dimension. -/
noncomputable def loss (objective : RuntimeObjective) [Fact objective.prime.Prime]
    (z : Parameter objective.prime objective.variableCount) : ℝ :=
  (objective.rows.map fun row => row.loss z).sum

local instance {n : ℕ} (objective : ExplicitSystem.CompiledObjective n)
    [Fact objective.prime.Prime] : Fact (ofCompiled objective).prime.Prime :=
  ⟨show objective.prime.Prime from Fact.out⟩

@[simp]
theorem loss_ofCompiled {n : ℕ} (objective : ExplicitSystem.CompiledObjective n)
    [Fact objective.prime.Prime] (z : Parameter objective.prime n) :
    (ofCompiled objective).loss z = ExplicitSystem.rowsLoss objective.rows z := by
  simp [loss, ofCompiled, ExplicitSystem.rowsLoss, List.map_map, Function.comp_def]

end RuntimeObjective

local instance (C : RuntimeSystem) : Fact C.domainEntryPrime.Prime :=
  ⟨C.domainEntryPrime_prime⟩

local instance (C : RuntimeSystem) : Fact (compileUsingDomainEntryBound C).prime.Prime :=
  ⟨C.domainEntryPrime_prime⟩

/-- The actual runtime output has exactly the previously proved objective semantics. -/
theorem compileUsingDomainEntryBound_loss (C : RuntimeSystem) [Fact C.domainEntryPrime.Prime] :
    (compileUsingDomainEntryBound C).loss =
      ExplicitSystem.rowsLoss (C.toExplicitSystem.compileObjectiveAt C.domainEntryPrime).rows := by
  let : Fact (C.toExplicitSystem.compileObjectiveAt C.domainEntryPrime).prime.Prime :=
    ⟨C.domainEntryPrime_prime⟩
  funext z
  exact RuntimeObjective.loss_ofCompiled _ z

/-- Attainment and exact minimum-conflict semantics for the serialized output itself. -/
theorem compiledObjective_correct (C : RuntimeSystem) (hC : C.WellFormed) :
    (∃ z, IsGlobalMin (compileUsingDomainEntryBound C).loss z) ∧
      ∀ z, IsGlobalMin (compileUsingDomainEntryBound C).loss z ↔
        ∃ x, C.toExplicitSystem.MinimizesConflicts x ∧
          C.toExplicitSystem.padicAssignment (p := C.domainEntryPrime) x = z := by
  rw [compileUsingDomainEntryBound_loss]
  exact compileUsingDomainEntryBound_allDifferent_correctness C hC

/-- Satisfiable systems have exactly their embedded satisfying assignments as minimizers. -/
theorem compiledObjective_satisfiable (C : RuntimeSystem) (hC : C.WellFormed)
    (hsat : ∃ x, C.toExplicitSystem.Satisfies x) :
    ∀ z, IsGlobalMin (compileUsingDomainEntryBound C).loss z ↔
      ∃ x, C.toExplicitSystem.Satisfies x ∧
        C.toExplicitSystem.padicAssignment (p := C.domainEntryPrime) x = z := by
  rw [compileUsingDomainEntryBound_loss]
  exact compileUsingDomainEntryBound_globalMin_iff_satisfies_of_satisfiable C hC hsat

/-- Thesis `cor:all-different-csp`: the one concrete compiler satisfies the
bit-level polynomial-time, full bit-size, prime and exact minimizer claims.
Well-formed inputs have nonempty domains and in-range scope indices; repeated
entries/scopes use set semantics and conflicts count deduplicated primal edges. -/
theorem all_different_csp :
    Nonempty (@LeanNPHardness.TM2ComputableInPolyTime RuntimeSystem RuntimeObjective
      RuntimeCompilerInput.finEncoding RuntimeObjective.finEncoding compileUsingDomainEntryBound) ∧
    ∀ C : RuntimeSystem, C.WellFormed →
      (compileUsingDomainEntryBound C).variableCount = C.domains.length ∧
      (compileUsingDomainEntryBound C).prime.Prime ∧
      C.toExplicitSystem.symbolCount < (compileUsingDomainEntryBound C).prime ∧
      (compileUsingDomainEntryBound C).encodedSize ≤
        64 * ((RuntimeCompilerInput.encode C).length + 1) ^ 4 ∧
      (∃ z, IsGlobalMin (compileUsingDomainEntryBound C).loss z) ∧
      (∀ z, IsGlobalMin (compileUsingDomainEntryBound C).loss z ↔
        ∃ x, C.toExplicitSystem.MinimizesConflicts x ∧
          C.toExplicitSystem.padicAssignment (p := C.domainEntryPrime) x = z) ∧
      ((∃ x, C.toExplicitSystem.Satisfies x) →
        ∀ z, IsGlobalMin (compileUsingDomainEntryBound C).loss z ↔
          ∃ x, C.toExplicitSystem.Satisfies x ∧
            C.toExplicitSystem.padicAssignment (p := C.domainEntryPrime) x = z) := by
  refine ⟨⟨AllDifferentCSPMachine.runtimeCompilerComputableInPolyTime⟩, ?_⟩
  intro C hC
  refine ⟨rfl, C.domainEntryPrime_prime, C.symbolCount_lt_domainEntryPrime,
    compileUsingDomainEntryBound_encodedSize_le_compilerInput_quartic C, ?_⟩
  exact ⟨(compiledObjective_correct C hC).1, (compiledObjective_correct C hC).2,
    compiledObjective_satisfiable C hC⟩

-- Kernel-checked complete compiler examples: empty input and repeated symbols/scopes.
example : compileUsingDomainEntryBound ⟨[], []⟩ = ⟨0, 2, []⟩ := by
  rw [← AllDifferentCSPMachine.ObjectiveHeader.assemble_ofRuntimeSystem,
    ← AllDifferentCSPMachine.ObjectiveHeader.prepare_result]
  decide
example : compileUsingDomainEntryBound ⟨[[10, 10], [10, 30]], [[0, 1], [1, 0, 1]]⟩ =
    ⟨2, 5, [.pin 0 1 2, .pin 1 1 2, .pin 1 2 2, .unequal 0 1]⟩ := by
  rw [← AllDifferentCSPMachine.ObjectiveHeader.assemble_ofRuntimeSystem,
    ← AllDifferentCSPMachine.ObjectiveHeader.prepare_result]
  decide

#print axioms RuntimeResidualRow.observation_ofResidualRow
#print axioms RuntimeResidualRow.loss_ofResidualRow
#print axioms RuntimeObjective.loss_ofCompiled
#print axioms compileUsingDomainEntryBound_loss
#print axioms compiledObjective_correct
#print axioms compiledObjective_satisfiable
#print axioms all_different_csp

end PhdThesisLean.AllDifferentCSPEncoding
