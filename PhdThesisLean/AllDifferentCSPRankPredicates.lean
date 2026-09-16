import PhdThesisLean.AllDifferentCSPRankQueries

/-!
# Execute both predicates of one rank iteration while retaining the tail

The checked preparation machine constructs all input copies. The upstream
pair adapters then run membership and strict comparison without losing the
next target/tail query. Their polynomial bounds include transfers and output
reassembly. Loop control and rank accumulation are not yet implemented.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace RankPredicates

abbrev Output := Bool × (Bool × DomainSymbolMembership.Input)

def outputFinEncoding : FinEncoding Output :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingBoolBool
    (LeanNPHardness.PairEncoding.finEncoding finEncodingBoolBool DomainSymbolMembership.finEncoding)

/-- Membership, strict comparison, and the exact retained next query. -/
def evaluate (input : RankQueries.Input) : Output :=
  (DomainSymbolMembership.contains (input.2.1, input.2.2),
    (DomainSymbolComparison.less (input.2.1, input.1), (input.1, input.2.2)))

/-- The machine-produced bits choose exactly the contribution to canonical rank.
A repeated symbol is counted only at its final occurrence. -/
theorem rank_step (input : RankQueries.Input) :
    DomainSymbols.rank (input.2.1 :: input.2.2) input.1 =
      DomainSymbols.rank (evaluate input).2.2.2 (evaluate input).2.2.1 +
        if (evaluate input).2.1 && !(evaluate input).1 then 1 else 0 :=
  DomainSymbolComparison.rank_cons input.2.1 input.1 input.2.2

/-- Taking a rank step removes exactly one complete field from the retained
input; the symbol's magnitude contributes its canonical binary length. -/
theorem remaining_length (input : RankQueries.Input) :
    (DomainSymbolMembership.finEncoding.encode (evaluate input).2.2).length +
      (encodeNat input.2.1).length + 1 = (RankQueries.inputEncode input).length := by
  rw [RankQueries.input_length]
  simp [evaluate, DomainSymbolMembership.finEncoding, finEncodingNatBool,
    encodingNatBool, SourceOrderRawFields.finEncoding, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc]

/-- The retained query strictly decreases even when the consumed symbol is zero. -/
theorem remaining_length_lt (input : RankQueries.Input) :
    (DomainSymbolMembership.finEncoding.encode (evaluate input).2.2).length <
      (RankQueries.inputEncode input).length := by
  have h := remaining_length input
  omega

theorem output_length (input : RankQueries.Input) :
    (outputFinEncoding.encode (evaluate input)).length =
      (DomainSymbolMembership.finEncoding.encode (evaluate input).2.2).length + 2 := by
  simp [outputFinEncoding, finEncodingBoolBool, encodeBool]

theorem output_length_le (input : RankQueries.Input) :
    (outputFinEncoding.encode (evaluate input)).length ≤
      (RankQueries.inputEncode input).length + 1 := by
  rw [output_length]
  have h := remaining_length_lt input
  omega

end RankPredicates

/-- Evaluate membership and order from the original serialized nonempty rank
query, retaining its exact target and tail. Every input copy is constructed by
the preparation machine; the generic composition accounts for all transfers. -/
noncomputable def rankPredicatesComputableInPolyTime :
    @TM2ComputableInPolyTime RankQueries.Input RankPredicates.Output
      RankQueries.inputFinEncoding RankPredicates.outputFinEncoding RankPredicates.evaluate := by
  let remaining := DomainSymbolMembership.finEncoding
  let comparisonAndRemaining := LeanNPHardness.PairEncoding.finEncoding
    DomainSymbolComparison.finEncoding remaining
  let membership := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    DomainSymbolMembership.finEncoding finEncodingBoolBool comparisonAndRemaining
    DomainSymbolMembership.contains domainSymbolMembershipComputableInPolyTime
  let comparison := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    DomainSymbolComparison.finEncoding finEncodingBoolBool remaining
    DomainSymbolComparison.less domainSymbolLessComputableInPolyTime
  let keepMembership := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    finEncodingBoolBool comparisonAndRemaining
    (LeanNPHardness.PairEncoding.finEncoding finEncodingBoolBool remaining)
    (fun pair => (DomainSymbolComparison.less pair.1, pair.2)) comparison
  let first := compositionComputableInPolyTime _ _ _ _ _ rankQueriesComputableInPolyTime membership
  let composed := compositionComputableInPolyTime _ _ _ _ _ first keepMembership
  exact { composed with
    outputsFun := fun input => by
      simpa [Function.comp_def, RankQueries.prepare, RankPredicates.evaluate,
        RankPredicates.outputFinEncoding, remaining]
        using composed.outputsFun input }

#print axioms RankPredicates.rank_step
#print axioms RankPredicates.remaining_length
#print axioms RankPredicates.remaining_length_lt
#print axioms RankPredicates.output_length_le
#print axioms rankPredicatesComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
