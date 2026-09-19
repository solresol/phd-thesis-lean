import PhdThesisLean.AllDifferentCSPRankAccumulator

/-!
# One complete rank iteration with an explicit accumulator

Compose query preparation, both predicates, and conditional accumulation using
the pinned checked machine adapters. The entire retained state does not grow,
and exactly one symbol disappears per iteration. The executable recursive
specification agrees with canonical rank, including its empty-list branch;
`AllDifferentCSPRankLoop` supplies its repeated finite-machine implementation
and total polynomial bound.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace RankIteration

abbrev Input := RankQueries.Input × ℕ
abbrev Output := RankAccumulator.Output

def inputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding RankQueries.inputFinEncoding unaryFinEncodingNat

abbrev outputFinEncoding := RankAccumulator.outputFinEncoding

/-- The next target/tail query and the updated unary accumulator. -/
def step (input : Input) : Output :=
  RankAccumulator.update (RankPredicates.evaluate input.1, input.2)

theorem rank_invariant (input : Input) :
    (step input).2 + DomainSymbols.rank (step input).1.2 (step input).1.1 =
      input.2 + DomainSymbols.rank (input.1.2.1 :: input.1.2.2) input.1.1 := by
  rw [RankPredicates.rank_step input.1]
  simp [step, RankAccumulator.update, Nat.add_assoc, Nat.add_comm]

theorem remaining_symbols_length (input : Input) :
    (step input).1.2.length + 1 = (input.1.2.1 :: input.1.2.2).length := rfl

/-- A consumed field pays for the optional new unary cell. The exact balance
charges the head's canonical binary length and its delimiter. -/
theorem output_length_balance (input : Input) :
    (outputFinEncoding.encode (step input)).length + (encodeNat input.1.2.1).length + 1 =
      (inputFinEncoding.encode input).length +
        if (RankPredicates.evaluate input.1).2.1 && !(RankPredicates.evaluate input.1).1 then 1 else 0 := by
  have h := RankPredicates.remaining_length input.1
  simp only [outputFinEncoding, step, RankAccumulator.output_length]
  simp only [inputFinEncoding, LeanNPHardness.PairEncoding.finEncoding_encode_length,
    RankQueries.inputFinEncoding, unaryFinEncodingNat]
  have hu : (unaryEncodeNat input.2).length = input.2 := unary_decode_encode_nat input.2
  rw [hu]
  omega

/-- Even though the tally can increase, the full serialized iteration state
never grows. The number of remaining fields, rather than this weak inequality,
supplies strict termination. -/
theorem output_length_le (input : Input) :
    (outputFinEncoding.encode (step input)).length ≤ (inputFinEncoding.encode input).length := by
  have h := output_length_balance input
  split at h <;> omega

/-- Executable tail recursion; the starting tally is one for canonical rank. -/
def finish (target : ℕ) : List ℕ → ℕ → ℕ
  | [], count => count
  | symbol :: symbols, count =>
      finish target symbols (step ((target, symbol, symbols), count)).2

theorem finish_add_one (target : ℕ) (symbols : List ℕ) (count : ℕ) :
    finish target symbols count + 1 = count + DomainSymbols.rank symbols target := by
  induction symbols generalizing count with
  | nil => simp [finish, DomainSymbols.rank]
  | cons symbol symbols ih =>
      rw [finish, ih]
      exact rank_invariant ((target, symbol, symbols), count)

/-- The executable loop counts each distinct smaller symbol exactly once. -/
theorem finish_one_eq_rank (target : ℕ) (symbols : List ℕ) :
    finish target symbols 1 = DomainSymbols.rank symbols target := by
  have h := finish_add_one target symbols 1
  omega

/-- Unary counting is bounded by the number of explicit symbol occurrences,
not by their numeric magnitudes. -/
theorem finish_le_count_add_length (target : ℕ) (symbols : List ℕ) (count : ℕ) :
    finish target symbols count ≤ count + symbols.length := by
  have h := finish_add_one target symbols count
  have hd := (List.dedup_sublist (symbols.filter fun symbol => decide (symbol < target))).length_le
  have hf := List.length_filter_le (fun symbol => decide (symbol < target)) symbols
  unfold DomainSymbols.rank at h
  omega

/-- In particular, this recursive specification gives the thesis compiler's
existing canonical relabelling on its actual extracted occurrence stream. -/
theorem finish_extracted_eq_relabelValue (C : RuntimeSystem) (value : ℕ) :
    finish value (DomainSymbols.extract (RuntimeStructuralView.ofRuntimeSystem C).domainOccurrences) 1 =
      C.toExplicitSystem.relabelValue value := by
  rw [finish_one_eq_rank, DomainSymbols.rank_extract_eq_relabelValue]

example : finish 42 [7, 100, 7, 42, 7] 1 = 2 := by decide
example : finish 0 [0, 0, 7] 1 = 1 := by decide
example : finish 100 [] 1 = 1 := by decide

end RankIteration

/-- A complete nonempty iteration: all queries are constructed, both predicates
are computed, and the retained unary accumulator is conditionally incremented.
The checked polynomial includes every adapter and intermediate transfer. -/
noncomputable def rankIterationComputableInPolyTime :
    @TM2ComputableInPolyTime RankIteration.Input RankIteration.Output
      RankIteration.inputFinEncoding RankIteration.outputFinEncoding RankIteration.step := by
  let predicates := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    RankQueries.inputFinEncoding RankPredicates.outputFinEncoding unaryFinEncodingNat
    RankPredicates.evaluate rankPredicatesComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _ predicates rankAccumulatorComputableInPolyTime
  exact { composed with
    outputsFun := fun input => by
      simpa [Function.comp_def, RankIteration.step, RankIteration.inputFinEncoding,
        RankAccumulator.inputFinEncoding] using composed.outputsFun input }

#print axioms RankIteration.rank_invariant
#print axioms RankIteration.output_length_balance
#print axioms RankIteration.output_length_le
#print axioms RankIteration.finish_one_eq_rank
#print axioms RankIteration.finish_le_count_add_length
#print axioms RankIteration.finish_extracted_eq_relabelValue
#print axioms rankIterationComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
