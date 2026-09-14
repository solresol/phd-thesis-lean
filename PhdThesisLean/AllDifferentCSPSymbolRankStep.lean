import PhdThesisLean.AllDifferentCSPSymbolMembership

/-!
# Connect symbol membership to deduplication and canonical ranks

The checked membership machine returns the branch used to skip a repeated
symbol. A smaller symbol adds one rank position only at its final occurrence.
These recurrence and encoded-size lemmas specify the next repeated driver;
they do not assert a finite-machine running time for deduplication or rank.
The full thesis corollary `cor:all-different-csp` remains partial.
-/

namespace PhdThesisLean.AllDifferentCSPEncoding.DomainSymbols

/-- A smaller symbol contributes once, at its final source-order occurrence. -/
theorem rank_cons (symbol : ℕ) (symbols : List ℕ) (value : ℕ) :
    rank (symbol :: symbols) value = rank symbols value +
      if symbol < value ∧ symbol ∉ symbols then 1 else 0 := by
  by_cases hs : symbol < value
  · by_cases hm : symbol ∈ symbols
    · have hf : symbol ∈ symbols.filter (fun s => decide (s < value)) := by simp [hs, hm]
      simp [rank, hs, hm, List.dedup_cons_of_mem hf]
    · have hf : symbol ∉ symbols.filter (fun s => decide (s < value)) := by simp [hm]
      simp [rank, hs, hm, List.dedup_cons_of_notMem hf, Nat.add_comm]
  · simp [rank, hs]

end PhdThesisLean.AllDifferentCSPEncoding.DomainSymbols

namespace PhdThesisLean.AllDifferentCSPMachine.DomainSymbolMembership

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-- The computed membership bit refers to exactly the semantic domain union. -/
theorem contains_extracted (C : RuntimeSystem) (value : ℕ) :
    contains (value, DomainSymbols.extract (RuntimeStructuralView.ofRuntimeSystem C).domainOccurrences) =
      decide (value ∈ C.toExplicitSystem.domainValues) := by
  have h := congrArg (fun values : Finset ℕ => decide (value ∈ values)) (DomainSymbols.extract_toFinset C)
  simpa [contains] using h

/-- The checked membership output is exactly the branch needed for deduplication. -/
theorem dedup_cons (symbol : ℕ) (symbols : List ℕ) :
    (symbol :: symbols).dedup =
      if contains (symbol, symbols) then symbols.dedup else symbol :: symbols.dedup := by
  simp [contains, List.dedup_cons]

/-- The checked membership bit determines whether this smaller symbol adds one
new rank position. This is the loop contract, not a running-time theorem for rank. -/
theorem rank_cons (symbol : ℕ) (symbols : List ℕ) (value : ℕ) :
    DomainSymbols.rank (symbol :: symbols) value = DomainSymbols.rank symbols value +
      if decide (symbol < value) && !contains (symbol, symbols) then 1 else 0 := by
  rw [DomainSymbols.rank_cons]
  by_cases hs : symbol < value <;> by_cases hm : symbol ∈ symbols <;> simp [contains, hs, hm]

/-- Reusing a row head as the query removes exactly its one raw-field delimiter;
no candidate bits or query bits are supplied without being charged. -/
theorem input_cons_length (symbol : ℕ) (symbols : List ℕ) :
    (finEncoding.encode (symbol, symbols)).length + 1 =
      (SourceOrderRawFields.encode (symbol :: symbols)).length := by
  simp [finEncoding, finEncodingNatBool, encodingNatBool, SourceOrderRawFields.finEncoding,
    SourceOrderRawFields.encode, Nat.add_comm, Nat.add_left_comm]

/-- Each deduplication query/tail test has the same checked machine and a bound
of six times the square of its original complete raw-field stream length. -/
def tailMembership_outputsInTime (symbol : ℕ) (symbols : List ℕ) :
    TM2OutputsInTime SymbolMembershipMachine.computer (finEncoding.encode (symbol, symbols))
      (some (finEncodingBoolBool.encode (contains (symbol, symbols))))
      (6 * (SourceOrderRawFields.encode (symbol :: symbols)).length^2) := by
  rw [← input_cons_length]
  exact domainSymbolMembership_outputsInTime (symbol, symbols)

/-- Removing duplicates retains a sublist of complete fields and cannot enlarge
this binary representation, regardless of the magnitudes of the symbols. -/
theorem dedup_fields_length_le (symbols : List ℕ) :
    (SourceOrderRawFields.encode symbols.dedup).length ≤
      (SourceOrderRawFields.encode symbols).length :=
  ((List.dedup_sublist symbols).flatMap _).length_le

example : contains (0, [100, 0, 100]) = true := by decide
example : contains (42, [100, 0, 100]) = false := by decide
example : contains (0, []) = false := by decide
example : DomainSymbols.rank [7, 100, 7, 42, 7] 42 = 2 := by decide

#print axioms contains_extracted
#print axioms dedup_cons
#print axioms rank_cons
#print axioms input_cons_length
#print axioms tailMembership_outputsInTime
#print axioms dedup_fields_length_le

end PhdThesisLean.AllDifferentCSPMachine.DomainSymbolMembership
