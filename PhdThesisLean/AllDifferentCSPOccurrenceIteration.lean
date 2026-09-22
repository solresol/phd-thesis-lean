import PhdThesisLean.AllDifferentCSPOccurrenceAccumulator

/-!
# Relabel one occurrence with accumulated output and bound the traversal

The complete checked step ranks the next occurrence and appends its binary
record to the accumulated output. An executable traversal specifies all later
states. A decreasing size budget bounds every such state quadratically in
the initial wire length, even though output grows as the source shrinks.
The repeated finite dispatcher and its total runtime remain separate work.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace OccurrenceIteration

abbrev Input := OccurrenceQuery.Input × List (ℕ × ℕ)
abbrev State := OccurrenceAccumulator.Output

def inputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding OccurrenceQuery.inputFinEncoding
    DomainFieldRow.outputFinEncoding

abbrev stateFinEncoding := OccurrenceAccumulator.outputFinEncoding

def source (input : Input) : State := (OccurrenceQuery.source input.1, input.2)

def step (input : Input) : State :=
  OccurrenceAccumulator.appendRecord (OccurrenceEmit.step input.1, input.2)

theorem source_encode (input : Input) :
    stateFinEncoding.encode (source input) = inputFinEncoding.encode input := rfl

theorem step_eq (input : Input) :
    step input = (input.1.2, input.2 ++ [(input.1.1.1, DomainSymbols.rank input.1.2.2 input.1.1.2)]) := rfl

/-- Every cycle preserves the complete original symbol list. -/
theorem step_symbols (input : Input) : (step input).1.2 = input.1.2.2 := rfl

theorem step_occurrences_length (input : Input) :
    (step input).1.1.length + 1 = (source input).1.1.length := rfl

/-- The growing accumulator replaces only the old value's bits by rank bits. -/
theorem step_length_balance (input : Input) :
    (stateFinEncoding.encode (step input)).length + (encodeNat input.1.1.2).length =
      (inputFinEncoding.encode input).length +
        (encodeNat (DomainSymbols.rank input.1.2.2 input.1.1.2)).length := by
  have h := CountedOccurrenceStep.output_length_balance ((input.1, []), 0)
  rw [step, OccurrenceAccumulator.output_length]
  simp only [OccurrenceAccumulator.inputFinEncoding, inputFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length]
  simp only [CountedOccurrenceStep.outputFinEncoding, CountedOccurrenceStep.sectionsFinEncoding,
    CountedOccurrenceStep.step, CountedOccurrenceRank.inputFinEncoding,
    CountedOccurrenceRank.inputSectionsFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length] at h
  change _ + _ + _ = _ + _ + _ at h
  omega

/-- Reserve enough space for every remaining rank. This budget also includes
all retained symbols and every already emitted record. -/
def budget (state : State) : ℕ :=
  (stateFinEncoding.encode state).length + state.1.1.length * (state.1.2.length + 1)

theorem step_budget_le (input : Input) : budget (step input) ≤ budget (source input) := by
  have hb := step_length_balance input
  have hr := OccurrenceQuery.rank_le_length_add_one input.1.2.2 input.1.1.2
  have hn := BinaryNatLists.encodeNat_length_le (DomainSymbols.rank input.1.2.2 input.1.1.2)
  change (stateFinEncoding.encode (step input)).length +
      input.1.2.1.length * (input.1.2.2.length + 1) ≤
    (inputFinEncoding.encode input).length +
      (input.1.2.1.length + 1) * (input.1.2.2.length + 1)
  nlinarith

/-- One executable traversal step; exhausted states are fixed points. -/
def advance (state : State) : State :=
  match state.1.1 with
  | [] => state
  | occurrence :: occurrences => step ((occurrence, occurrences, state.1.2), state.2)

theorem advance_budget_le (state : State) : budget (advance state) ≤ budget state := by
  rcases state with ⟨⟨occurrences, symbols⟩, accum⟩
  cases occurrences with
  | nil => exact le_rfl
  | cons occurrence occurrences => exact step_budget_le ((occurrence, occurrences, symbols), accum)

theorem iterate_budget_le (n : ℕ) (state : State) : budget (advance^[n] state) ≤ budget state := by
  induction n generalizing state with
  | zero => exact le_rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact (ih (advance state)).trans (advance_budget_le state)

/-- Each occurrence contributes six format cells, even when both fields are zero. -/
theorem occurrences_length_le_wire (occurrences : List (ℕ × ℕ)) :
    occurrences.length ≤ (DomainFieldRow.outputEncode occurrences).length := by
  induction occurrences with
  | nil => simp [DomainFieldRow.outputEncode]
  | cons occurrence occurrences ih =>
      simp only [DomainFieldRow.outputEncode, List.flatMap_cons, List.length_append,
        List.length_cons] at *
      have h : 1 ≤ (DomainOccurrenceFieldBlock.outputEncode occurrence).length := by
        simp [DomainOccurrenceFieldBlock.outputEncode_eq_prefix, DomainOccurrenceFieldBlock.headerPrefix]
      omega

theorem state_length (state : State) :
    (stateFinEncoding.encode state).length =
      (DomainFieldRow.outputEncode state.1.1).length +
        (SourceOrderRawFields.encode state.1.2).length +
        (DomainFieldRow.outputEncode state.2).length := by
  simp [OccurrenceAccumulator.outputFinEncoding, DomainSymbolExtraction.finEncoding,
    DomainFieldRow.outputFinEncoding, SourceOrderRawFields.finEncoding, Nat.add_assoc]

/-- A uniform quadratic bound holds for arbitrary initial accumulators, not
just the compiler's empty one. Numeric symbol magnitudes enter only as bits. -/
theorem budget_le_quadratic (state : State) :
    budget state ≤ 2 * ((stateFinEncoding.encode state).length + 1) ^ 2 := by
  have ho := occurrences_length_le_wire state.1.1
  have hs := OccurrenceQuery.symbols_length_le_wire state.1.2
  have hw := state_length state
  have hocc : state.1.1.length ≤ (stateFinEncoding.encode state).length := by omega
  have hsym : state.1.2.length ≤ (stateFinEncoding.encode state).length := by omega
  have hm := Nat.mul_le_mul hocc (Nat.add_le_add_right hsym 1)
  unfold budget
  nlinarith

/-- Every executable traversal state, including its accumulated output, is
bounded by the same polynomial in the original complete wire length. -/
theorem iterate_length_le_quadratic (n : ℕ) (state : State) :
    (stateFinEncoding.encode (advance^[n] state)).length ≤
      2 * ((stateFinEncoding.encode state).length + 1) ^ 2 := by
  have h := (iterate_budget_le n state).trans (budget_le_quadratic state)
  unfold budget at h
  omega

/-- Ordered executable tail recursion using exactly the checked step function. -/
def finish (symbols : List ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
  | [], accum => accum
  | occurrence :: occurrences, accum =>
      finish symbols occurrences (step ((occurrence, occurrences, symbols), accum)).2

theorem finish_eq_append_map (symbols : List ℕ) (occurrences accum : List (ℕ × ℕ)) :
    finish symbols occurrences accum =
      accum ++ occurrences.map (fun occurrence => (occurrence.1, DomainSymbols.rank symbols occurrence.2)) := by
  induction occurrences generalizing accum with
  | nil => simp [finish]
  | cons occurrence occurrences ih =>
      simp [finish, ih, step_eq, List.append_assoc]

/-- Exactly one cycle per original occurrence exhausts the source, retains the
full symbols, and emits the ordered rank map with no lost or repeated record. -/
theorem iterate_eq_finish (occurrences : List (ℕ × ℕ)) (symbols : List ℕ)
    (accum : List (ℕ × ℕ)) :
    advance^[occurrences.length] ((occurrences, symbols), accum) =
      (([], symbols), finish symbols occurrences accum) := by
  induction occurrences generalizing accum with
  | nil => rfl
  | cons occurrence occurrences ih =>
      simp only [List.length_cons, Function.iterate_succ_apply, advance]
      exact ih _

/-- Starting from no emitted records adds no wire cells. -/
theorem seed_length (input : DomainSymbolExtraction.Value) :
    (stateFinEncoding.encode (input, [])).length =
      (DomainSymbolExtraction.finEncoding.encode input).length := by
  simp [OccurrenceAccumulator.outputFinEncoding, DomainFieldRow.outputFinEncoding,
    DomainFieldRow.outputEncode]

/-- Complete emitted output has a quadratic bound in the original serialized
occurrences and symbols, including every record tag and numeric field. -/
theorem finish_encoded_length_le_quadratic (input : DomainSymbolExtraction.Value) :
    (DomainFieldRow.outputEncode (finish input.2 input.1 [])).length ≤
      2 * ((DomainSymbolExtraction.finEncoding.encode input).length + 1) ^ 2 := by
  have h := iterate_length_le_quadratic input.1.length (input, [])
  rw [iterate_eq_finish, seed_length, state_length] at h
  have hz : (DomainFieldRow.outputEncode []).length = 0 := rfl
  rw [hz] at h
  dsimp only at h
  omega

/-- All compiler occurrences acquire precisely the thesis relabelled values;
variable indices, source order, and duplicate occurrences are preserved. -/
theorem finish_extracted_eq_relabelValue (C : RuntimeSystem) :
    finish C.domains.flatten (RuntimeStructuralView.indexedDomainOccurrences C.domains) [] =
      (RuntimeStructuralView.indexedDomainOccurrences C.domains).map
        (fun occurrence => (occurrence.1, C.toExplicitSystem.relabelValue occurrence.2)) := by
  simp [finish_eq_append_map, DomainSymbols.rank_flatten_eq_relabelValue]

/-- Every completed compiler record carries a positive rank strictly below
the already checked domain-entry prime. -/
theorem finish_rank_bounds (C : RuntimeSystem) (record : ℕ × ℕ)
    (h : record ∈ finish C.domains.flatten
      (RuntimeStructuralView.indexedDomainOccurrences C.domains) []) :
    0 < record.2 ∧ record.2 < C.domainEntryPrime := by
  rw [finish_eq_append_map] at h
  simp only [List.nil_append, List.mem_map] at h
  obtain ⟨occurrence, hmem, rfl⟩ := h
  have hvalue : occurrence.2 ∈ C.domains.flatten := by
    rw [← RuntimeStructuralView.indexedDomainOccurrences_values C.domains]
    exact List.mem_map.mpr ⟨occurrence, hmem, rfl⟩
  exact ⟨by unfold DomainSymbols.rank; omega,
    DomainSymbols.rank_lt_domainEntryPrime C hvalue⟩

example : finish [100, 7, 100, 42, 7] [(0, 100), (0, 7), (1, 100), (2, 42), (2, 7)] [] =
    [(0, 3), (0, 1), (1, 3), (2, 2), (2, 1)] := by decide
example : finish [0, 0] [(0, 0), (0, 0)] [] = [(0, 1), (0, 1)] := by decide
example : advance^[4] (([], []), [(7, 2)]) = (([], []), [(7, 2)]) := by decide

end OccurrenceIteration

/-- Complete rank, binary emission, and ordered append, retaining all prior
records through the checked pair adapter. Its time includes every transfer. -/
noncomputable def occurrenceIterationComputableInPolyTime :
    @TM2ComputableInPolyTime OccurrenceIteration.Input OccurrenceIteration.State
      OccurrenceIteration.inputFinEncoding OccurrenceIteration.stateFinEncoding
      OccurrenceIteration.step := by
  let retained := LeanNPHardness.MachineAdapters.pairReductionComputableInPolyTime
    OccurrenceQuery.inputFinEncoding OccurrenceEmit.outputFinEncoding
    DomainFieldRow.outputFinEncoding OccurrenceEmit.step occurrenceStepComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _
    retained occurrenceAccumulatorComputableInPolyTime
  exact { composed with
    outputsFun := fun input => by
      simpa only [Function.comp_def, OccurrenceIteration.step] using composed.outputsFun input }

#print axioms OccurrenceIteration.step_length_balance
#print axioms OccurrenceIteration.step_budget_le
#print axioms OccurrenceIteration.iterate_length_le_quadratic
#print axioms OccurrenceIteration.finish_eq_append_map
#print axioms OccurrenceIteration.iterate_eq_finish
#print axioms OccurrenceIteration.finish_encoded_length_le_quadratic
#print axioms OccurrenceIteration.finish_rank_bounds
#print axioms OccurrenceIteration.finish_extracted_eq_relabelValue
#print axioms occurrenceIterationComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
