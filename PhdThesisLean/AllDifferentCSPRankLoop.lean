import PhdThesisLean.AllDifferentCSPRankLoopMachine

/-!
# Polynomial-time canonical symbol rank

The finite loop consumes one source symbol per cycle. Its complete serialized
state never grows, so every body call and transfer is charged to the original
encoded length. The unary tally is bounded by explicit occurrences rather
than numeric symbol magnitudes. Initialization then gives one-based rank.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace RankLoop

def result (input : RankControl.Input) : ℕ :=
  RankIteration.finish input.1.1 input.1.2 input.2

theorem state_length (target count : ℕ) (symbols : List ℕ) :
    (RankControl.inputFinEncoding.encode ((target, symbols), count)).length =
      (encodeNat target).length + (SourceOrderRawFields.encode symbols).length + count := by
  simp [RankAccumulator.outputFinEncoding, DomainSymbolMembership.finEncoding,
    SourceOrderRawFields.finEncoding, finEncodingNatBool, encodingNatBool,
    unaryFinEncodingNat, unaryEncodeNat_eq_replicate_true, Nat.add_assoc]

/-- Each source occurrence contributes its own delimiter, even for zero. -/
theorem symbols_length_le_state (input : RankControl.Input) :
    input.1.2.length ≤ (RankControl.inputFinEncoding.encode input).length := by
  rcases input with ⟨⟨target, symbols⟩, count⟩
  change symbols.length ≤ _
  rw [state_length]
  have fields : symbols.length ≤ (SourceOrderRawFields.encode symbols).length := by
    induction symbols with
    | nil => simp [SourceOrderRawFields.encode]
    | cons symbol symbols ih =>
        simp only [SourceOrderRawFields.encode, List.flatMap_cons, List.length_append,
          List.length_cons, List.length_map] at *
        omega
  omega

noncomputable section

/-- Uniform cost of one complete cycle at a bound on the full state length.
It also bounds the final empty-state scan and output. -/
def passTime : Polynomial ℕ := RankLoopMachine.body.time + 4 * Polynomial.X + 4

theorem passTime_eval (s : ℕ) :
    passTime.eval s = RankLoopMachine.body.time.eval s + 4 * s + 4 := by
  simp [passTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]

/-- Induction on remaining fields supplies termination; the weak wire-length
bound supplies a uniform cost, even when a counted zero leaves it unchanged. -/
def run_bounded (target : ℕ) (symbols : List ℕ) (count bound : ℕ)
    (size : (RankControl.inputFinEncoding.encode ((target, symbols), count)).length ≤ bound) :
    RankLoopMachine.Run (RankLoopMachine.ready ((target, symbols), count))
      (RankLoopMachine.done (RankIteration.finish target symbols count))
      ((symbols.length + 1) * passTime.eval bound) := by
  induction symbols generalizing count with
  | nil =>
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (RankLoopMachine.exit_run target count)
      simp only [List.length_nil, zero_add, one_mul, passTime_eval]
      omega
  | cons symbol symbols ih =>
      let input : RankIteration.Input := ((target, symbol, symbols), count)
      have input_size : (RankIteration.inputFinEncoding.encode input).length ≤ bound := size
      have output_size := (RankIteration.output_length_le input).trans input_size
      have tail_size : (RankControl.inputFinEncoding.encode
          ((target, symbols), (RankIteration.step input).2)).length ≤ bound := output_size
      have tail_run := ih (RankIteration.step input).2 tail_size
      have cycle := RankLoopMachine.iteration_cycle target symbol symbols count
      have body_cost := LeanNPHardness.MachineRuntime.polynomial_eval_mono
        RankLoopMachine.body.time input_size
      apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (RankLoopMachine.seq cycle tail_run)
      simp only [List.length_cons, passTime_eval]
      change RankLoopMachine.body.time.eval (RankIteration.inputFinEncoding.encode input).length +
        2 * (RankIteration.inputFinEncoding.encode input).length +
        2 * (RankIteration.outputFinEncoding.encode (RankIteration.step input)).length + 4 +
        (symbols.length + 1) * (RankLoopMachine.body.time.eval bound + 4 * bound + 4) ≤
        (symbols.length + 1 + 1) * (RankLoopMachine.body.time.eval bound + 4 * bound + 4)
      nlinarith

/-- A polynomial in the original complete wire length, including all cycles,
their control/transfers, and the final empty-state exit. -/
def time : Polynomial ℕ := (Polynomial.X + 1) * passTime

theorem time_eval (s : ℕ) :
    time.eval s = (s + 1) * (RankLoopMachine.body.time.eval s + 4 * s + 4) := by
  simp [time, passTime_eval, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]

def outputsInTime (input : RankControl.Input) :
    TM2OutputsInTime RankLoopMachine.computer (RankControl.inputFinEncoding.encode input)
      (some (unaryFinEncodingNat.encode (result input)))
      (time.eval (RankControl.inputFinEncoding.encode input).length) := by
  have h := run_bounded input.1.1 input.1.2 input.2
    (RankControl.inputFinEncoding.encode input).length (by rfl)
  have h' := LeanNPHardness.MachinePrimitives.evalsToInTimeMono h
    (Nat.mul_le_mul_right (passTime.eval (RankControl.inputFinEncoding.encode input).length)
      (Nat.add_le_add_right (symbols_length_le_state input) 1))
  simpa only [RankLoopMachine.ready_eq_initList, RankLoopMachine.done_eq_haltList,
    result, time, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one] using h'

end

end RankLoop

/-- Complete repeated rank computation from an arbitrary checked query/tally
state to its unary result. This is a finite-machine polynomial-time theorem. -/
noncomputable def rankLoopComputableInPolyTime :
    @TM2ComputableInPolyTime RankControl.Input ℕ RankControl.inputFinEncoding unaryFinEncodingNat
      RankLoop.result where
  tm := RankLoopMachine.computer
  inputAlphabet := Equiv.refl RankLoopMachine.Wire
  outputAlphabet := Equiv.refl Bool
  time := RankLoop.time
  outputsFun input := by simpa [Equiv.refl] using RankLoop.outputsInTime input

/-- Compute the canonical one-based rank of the target in the complete
source-order symbol list. Initialization and every transfer are included. -/
noncomputable def canonicalRankComputableInPolyTime :
    @TM2ComputableInPolyTime DomainSymbolMembership.Input ℕ
      DomainSymbolMembership.finEncoding unaryFinEncodingNat
      (fun input => DomainSymbols.rank input.2 input.1) := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    rankInitializationComputableInPolyTime rankLoopComputableInPolyTime
  exact { composed with
    outputsFun := fun input => by
      simpa [Function.comp_def, RankLoop.result, RankInitialization.finish_initialize] using
        composed.outputsFun input }

/-- The full local rank machine returns the thesis compiler's exact relabelled
value on its extracted symbols. The serialized query is the input boundary;
the occurrence-query and occurrence-rank modules perform its one-occurrence
composition while retaining compiler sections. -/
noncomputable def canonicalRank_extracted_outputsInTime (C : RuntimeSystem) (value : ℕ) :
    let query : DomainSymbolMembership.Input :=
      (value, DomainSymbols.extract (RuntimeStructuralView.ofRuntimeSystem C).domainOccurrences)
    TM2OutputsInTime canonicalRankComputableInPolyTime.tm
      ((DomainSymbolMembership.finEncoding.encode query).map canonicalRankComputableInPolyTime.inputAlphabet.symm)
      (some ((unaryFinEncodingNat.encode (C.toExplicitSystem.relabelValue value)).map
        canonicalRankComputableInPolyTime.outputAlphabet.symm))
      (canonicalRankComputableInPolyTime.time.eval (DomainSymbolMembership.finEncoding.encode query).length) := by
  simpa only [DomainSymbols.rank_extract_eq_relabelValue] using
    canonicalRankComputableInPolyTime.outputsFun
      (value, DomainSymbols.extract (RuntimeStructuralView.ofRuntimeSystem C).domainOccurrences)

#print axioms RankLoop.symbols_length_le_state
#print axioms RankLoop.run_bounded
#print axioms RankLoop.outputsInTime
#print axioms rankLoopComputableInPolyTime
#print axioms canonicalRankComputableInPolyTime
#print axioms canonicalRank_extracted_outputsInTime

end PhdThesisLean.AllDifferentCSPMachine
