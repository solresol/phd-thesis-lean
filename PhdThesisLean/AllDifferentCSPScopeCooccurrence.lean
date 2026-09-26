import PhdThesisLean.AllDifferentCSPScopeQueries

/-!
# Checked co-occurrence of two endpoints in one scope

Prepare both membership queries, execute the existing raw-field membership
machine twice through the checked pair adapters, and conjoin the two answers.
All preparation, transfers and cleanup are included in the composed polynomial.
This is the one-scope predicate; traversing counted scopes and the bounded pair
grid still requires an outer finite dispatcher.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace ScopeCooccurrence

/-- Both endpoints occur in this particular scope. -/
def evaluate (input : ScopeQueries.Input) : Bool :=
  DomainSymbolMembership.contains (input.1.1, input.2) &&
    DomainSymbolMembership.contains (input.1.2, input.2)

@[simp]
theorem evaluate_eq_true (input : ScopeQueries.Input) :
    evaluate input = true ↔ input.1.1 ∈ input.2 ∧ input.1.2 ∈ input.2 := by
  simp [evaluate, DomainSymbolMembership.contains]

/-- The outer OR must combine complete same-scope answers. -/
theorem adjacent_cons (scope : List ℕ) (scopes : List (List ℕ)) (i j : ℕ) :
    PrimalEdgeEnumeration.adjacent (scope :: scopes) i j =
      (evaluate ((i, j), scope) || PrimalEdgeEnumeration.adjacent scopes i j) := by
  simp only [PrimalEdgeEnumeration.adjacent, List.any_cons, List.contains_eq_mem,
    evaluate, DomainSymbolMembership.contains]

theorem adjacent_eq_any (scopes : List (List ℕ)) (i j : ℕ) :
    PrimalEdgeEnumeration.adjacent scopes i j =
      scopes.any (fun scope => evaluate ((i, j), scope)) := by
  simp [PrimalEdgeEnumeration.adjacent, evaluate, DomainSymbolMembership.contains]

/-- Every scope's complete raw field stream is charged to its counted section. -/
theorem scope_length_le_payload (scope : List ℕ) (scopes : List (List ℕ))
    (member : scope ∈ scopes) :
    (SourceOrderRawFields.encode scope).length ≤
      (DomainFieldSection.rowPayloadEncode scopes).length := by
  induction scopes with
  | nil => simp at member
  | cons head scopes ih =>
      have length : (DomainFieldSection.rowPayloadEncode (head :: scopes)).length =
          (encodeNat head.length).length + 1 + (SourceOrderRawFields.encode head).length +
            (DomainFieldSection.rowPayloadEncode scopes).length := by
        simp [DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
          SourceOrderRawFields.encode, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      rw [length]
      rcases List.mem_cons.mp member with equal | member
      · subst scope; omega
      · have h := ih member; omega

/-- A bounded-pair query for any retained scope uses at most twice the complete
intermediate wire length. Numerical endpoint magnitudes are charged in binary. -/
theorem query_length_le (value : BoundedRelabelledSections.Value) (i j : ℕ)
    (hi : i < value.1.2) (hj : j < value.1.2) (scope : List ℕ)
    (member : scope ∈ value.2) :
    (ScopeQueries.inputFinEncoding.encode ((i, j), scope)).length ≤
      2 * (BoundedRelabelledSections.finEncoding.encode value).length := by
  have left := (BinaryNatLists.encodeNat_length_le i).trans hi.le
  have right := (BinaryNatLists.encodeNat_length_le j).trans hj.le
  have fields := scope_length_le_payload scope value.2 member
  rw [ScopeQueries.input_length, BoundedRelabelledSections.encode_length]
  dsimp only
  omega

example : evaluate ((0, 1000000), [1000000, 0, 1000000]) = true := by decide
example : evaluate ((0, 0), []) = false := by decide
example : evaluate ((0, 0), [0]) = true := by decide
example : evaluate ((0, 1), [0, 0]) = false := by decide
example : PrimalEdgeEnumeration.adjacent [[0], [1]] 0 1 = false := by decide
example : PrimalEdgeEnumeration.adjacent [[0], [1], [1, 0, 1]] 0 1 = true := by decide

end ScopeCooccurrence

namespace ScopeConjunctionMachine

/-- Exactly the two membership-result cells, in the pair adapter's format. -/
def inputFinEncoding : FinEncoding (Bool × Bool) :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingBoolBool finEncodingBoolBool

inductive Stack
  | input | output
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => Sum Bool Bool | .output => Bool
abbrev State := Bool × Bool

/-- Fixed finite control consumes the two cells and emits their conjunction. -/
def program (_ : Unit) : TM2.Stmt Alphabet Unit State :=
  .pop .input (fun _ bit => ((bit.bind Sum.getLeft?).getD false, false)) <|
    .pop .input (fun s bit => (s.1, (bit.bind Sum.getRight?).getD false)) <|
      .push .output (fun s => s.1 && s.2) <| .load (fun _ => (false, false)) .halt

def computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Unit
  main := ()
  σ := State
  initialState := (false, false)
  Γk₀Fin := inferInstance
  m := program

def outputsInTime (input : Bool × Bool) :
    TM2OutputsInTime computer (inputFinEncoding.encode input)
      (some (finEncodingBoolBool.encode (input.1 && input.2))) 1 := by
  refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_rfl }
  change computer.step (initList computer (inputFinEncoding.encode input)) =
    some (haltList computer (finEncodingBoolBool.encode (input.1 && input.2)))
  simp [computer, FinTM2.step, initList, haltList,
    inputFinEncoding, LeanNPHardness.PairEncoding.finEncoding, finEncodingBoolBool,
    encodeBool, program, Alphabet, Function.update]
  funext k
  cases k <;> rfl

noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime (Bool × Bool) Bool inputFinEncoding finEncodingBoolBool
      (fun input => input.1 && input.2) where
  tm := computer
  inputAlphabet := Equiv.refl (Sum Bool Bool)
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_one] using outputsInTime input

end ScopeConjunctionMachine

/-- Decide co-occurrence from the complete serialized endpoint-pair/scope
input. The composed polynomial includes query duplication and both calls. -/
noncomputable def scopeCooccurrenceComputableInPolyTime :
    @TM2ComputableInPolyTime ScopeQueries.Input Bool
      ScopeQueries.inputFinEncoding finEncodingBoolBool ScopeCooccurrence.evaluate := by
  let membership := DomainSymbolMembership.finEncoding
  let first := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    membership finEncodingBoolBool membership
    DomainSymbolMembership.contains domainSymbolMembershipComputableInPolyTime
  let second := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    finEncodingBoolBool membership finEncodingBoolBool
    DomainSymbolMembership.contains domainSymbolMembershipComputableInPolyTime
  let prepared := compositionComputableInPolyTime _ _ _ _ _
    scopeQueriesComputableInPolyTime first
  let tested := compositionComputableInPolyTime _ _ _ _ _ prepared second
  let composed := compositionComputableInPolyTime _ _ _ _ _ tested
    ScopeConjunctionMachine.computableInPolyTime
  exact { composed with
    outputsFun := fun input => by
      simpa only [Function.comp_def, ScopeQueries.prepare, ScopeCooccurrence.evaluate]
        using composed.outputsFun input }

/-- The complete predicate cost is bounded by the same polynomial evaluated at
`2s` for any bounded pair and any scope retained in an `s`-cell intermediate.
Extraction of that scope from the counted section remains a separate machine. -/
theorem scopeCooccurrence_steps_le (value : BoundedRelabelledSections.Value) (i j : ℕ)
    (hi : i < value.1.2) (hj : j < value.1.2) (scope : List ℕ)
    (member : scope ∈ value.2) :
    (scopeCooccurrenceComputableInPolyTime.outputsFun ((i, j), scope)).steps ≤
      scopeCooccurrenceComputableInPolyTime.time.eval
        (2 * (BoundedRelabelledSections.finEncoding.encode value).length) := by
  exact (scopeCooccurrenceComputableInPolyTime.outputsFun ((i, j), scope)).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _
      (ScopeCooccurrence.query_length_le value i j hi hj scope member))

/-- The composed finite machine's output is precisely the singleton-scope
predicate used by the checked primal-edge enumeration. -/
theorem scopeCooccurrence_correct (scope : List ℕ) (i j : ℕ) :
    ScopeCooccurrence.evaluate ((i, j), scope) =
      PrimalEdgeEnumeration.adjacent [scope] i j := by
  rw [ScopeCooccurrence.adjacent_cons]
  simp [PrimalEdgeEnumeration.adjacent]

#print axioms ScopeCooccurrence.evaluate_eq_true
#print axioms ScopeCooccurrence.adjacent_cons
#print axioms ScopeCooccurrence.query_length_le
#print axioms ScopeConjunctionMachine.outputsInTime
#print axioms scopeCooccurrenceComputableInPolyTime
#print axioms scopeCooccurrence_steps_le
#print axioms scopeCooccurrence_correct

end PhdThesisLean.AllDifferentCSPMachine
