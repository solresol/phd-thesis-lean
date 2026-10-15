import PhdThesisLean.AllDifferentCSPPositiveCandidateFilter

/-!
# Rectangular positive-candidate traversal and reached-state bounds

Visit `(index, rank)` with `index < variableCount` and `rank ≤ occurrenceCount`.
The latter count is a unary header, not the magnitude of an original symbol.
The checked test-and-emit call supplies each row. An ordinal proves progress,
freshness and capacity for every reached state, including canonical exhaustion.
These executable iterations are a semantic specification; a repeated finite
machine and its total running-time bound remain separate obligations.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open PhdThesisLean.AllDifferentCSPEncoding

namespace PositiveAdvance

abbrev State := PositiveCandidateQueries.Input

def ordinal (q : ℕ) (candidate : ℕ × ℕ) : ℕ := candidate.1 * (q + 1) + candidate.2

def position (state : State) : ℕ := ordinal state.2.1.1.1.1.2 state.1

def gridSize (sections : CountedPositiveSections.Value) : ℕ :=
  sections.1.1.2 * (sections.1.1.1.2 + 1)

def nextPair (q : ℕ) (candidate : ℕ × ℕ) : ℕ × ℕ :=
  if candidate.2 < q then (candidate.1, candidate.2 + 1) else (candidate.1 + 1, 0)

/-- Filtering retains the complete sections; counter advance changes only the candidate. -/
def step (state : State) : State :=
  (nextPair state.2.1.1.1.1.2 state.1, (PositiveCandidateFilter.filter state).2)

def advance (state : State) : State :=
  if state.1.1 < state.2.1.1.1.2 then step state else state

def seed (sections : CountedPositiveSections.Value) : State := ((0, 0), sections, [])

/-- The closed inner bound gives one column even when the occurrence count is zero. -/
def Counters (state : State) : Prop :=
  (state.1.1 < state.2.1.1.1.2 ∧ state.1.2 ≤ state.2.1.1.1.1.2) ∨
    (state.1.1 = state.2.1.1.1.2 ∧ state.1.2 = 0)

structure Invariant (state : State) : Prop where
  counters : Counters state
  count_le : state.2.2.length ≤ position state
  earlier : ∀ row ∈ state.2.2, ordinal state.2.1.1.1.1.2 row.1 < position state
  bounded : ∀ row ∈ state.2.2, row.1.1 < state.2.1.1.1.2 ∧
    row.1.2 ≤ state.2.1.1.1.1.2 ∧ row.2 = state.2.1.2.2
  sound : ∀ row ∈ state.2.2, row.1 ∈ state.2.1.1.1.1.1
  ordered : state.2.2.Pairwise (Prod.Lex (Prod.Lex (· < ·) (· < ·)) (· < ·))

@[simp] theorem step_retained (state : State) : (step state).2.1 = state.2.1 := rfl

@[simp] theorem advance_retained (state : State) : (advance state).2.1 = state.2.1 := by
  unfold advance
  split <;> rfl

theorem next_position (q : ℕ) (candidate : ℕ × ℕ) (hr : candidate.2 ≤ q) :
    ordinal q (nextPair q candidate) = ordinal q candidate + 1 := by
  unfold nextPair ordinal
  split <;> dsimp only
  · omega
  · have h : candidate.2 = q := by omega
    nlinarith

theorem next_counters (n q : ℕ) (candidate : ℕ × ℕ)
    (hi : candidate.1 < n) (hr : candidate.2 ≤ q) :
    ((nextPair q candidate).1 < n ∧ (nextPair q candidate).2 ≤ q) ∨
      ((nextPair q candidate).1 = n ∧ (nextPair q candidate).2 = 0) := by
  unfold nextPair
  split <;> dsimp only <;> omega

theorem position_le_gridSize (state : State) (h : Counters state) :
    position state ≤ gridSize state.2.1 := by
  rcases h with ⟨hi, hr⟩ | ⟨hi, hr⟩
  · unfold position ordinal gridSize
    nlinarith
  · simp [position, ordinal, gridSize, hi, hr]

theorem ordinal_lt_iff_lex (q : ℕ) (a b : ℕ × ℕ) (ha : a.2 ≤ q) (hb : b.2 ≤ q) :
    ordinal q a < ordinal q b ↔ Prod.Lex (· < ·) (· < ·) a b := by
  rw [Prod.lex_iff]
  unfold ordinal
  constructor
  · intro h
    by_cases hab : a.1 < b.1
    · exact Or.inl hab
    · right
      have he : a.1 = b.1 := by nlinarith
      exact ⟨he, by nlinarith⟩
  · rintro (h | ⟨h, h'⟩) <;> nlinarith

theorem seed_invariant (sections : CountedPositiveSections.Value) : Invariant (seed sections) := by
  constructor
  · simp [Counters, seed]; omega
  · simp [seed, position, ordinal]
  · simp [seed]
  · simp [seed]
  · simp [seed]
  · simp [seed]

theorem step_position (state : State) (hr : state.1.2 ≤ state.2.1.1.1.1.2) :
    position (step state) = position state + 1 := next_position _ _ hr

/-- Every active step appends at most one fresh, bounded, correctly weighted row. -/
theorem step_invariant (state : State) (h : Invariant state)
    (hi : state.1.1 < state.2.1.1.1.2) : Invariant (step state) := by
  have hr : state.1.2 ≤ state.2.1.1.1.1.2 := by
    rcases h.counters with hc | hc <;> omega
  have hp := step_position state hr
  have rows : (step state).2.2 =
      if state.1 ∈ state.2.1.1.1.1.1 then
        state.2.2 ++ [PositiveCandidateEmit.row state] else state.2.2 :=
    PositiveCandidateFilter.rows_eq state
  constructor
  · exact next_counters _ _ _ hi hr
  · rw [hp]
    exact (PositiveCandidateFilter.rows_length_le state).trans (Nat.add_le_add_right h.count_le 1)
  · intro row he
    rw [hp]
    change ordinal state.2.1.1.1.1.2 row.1 < position state + 1
    rw [rows] at he
    split at he
    · rcases List.mem_append.mp he with old | new
      · exact (h.earlier row old).trans (Nat.lt_succ_self _)
      · have eq := List.mem_singleton.mp new
        subst row
        exact Nat.lt_succ_self _
    · exact (h.earlier row he).trans (Nat.lt_succ_self _)
  · exact PositiveCandidateFilter.rows_bounded state.2.1 state.1 state.2.2 hi hr h.bounded
  · intro row he
    change row.1 ∈ state.2.1.1.1.1.1
    rw [rows] at he
    split at he
    next hit =>
      rcases List.mem_append.mp he with old | new
      · exact h.sound row old
      · have eq := List.mem_singleton.mp new
        subst row
        exact hit
    next => exact h.sound row he
  · rw [rows]
    split
    · rw [List.pairwise_append]
      refine ⟨h.ordered, by simp, ?_⟩
      intro row he last hl
      have eq := List.mem_singleton.mp hl
      subst last
      apply Prod.Lex.left
      exact (ordinal_lt_iff_lex _ _ _ (h.bounded row he).2.1 hr).mp (h.earlier row he)
    · exact h.ordered

theorem advance_invariant (state : State) (h : Invariant state) : Invariant (advance state) := by
  unfold advance
  split
  · exact step_invariant state h ‹_›
  · exact h

/-- The next candidate has never already been emitted, without an external freshness assumption. -/
theorem fresh (state : State) (h : Invariant state) :
    PositiveCandidateEmit.row state ∉ state.2.2 := by
  intro he
  exact (Nat.lt_irrefl (position state)) (h.earlier _ he)

theorem active_capacity (state : State) (h : Invariant state)
    (hi : state.1.1 < state.2.1.1.1.2) : state.2.2.length < gridSize state.2.1 := by
  have hr : state.1.2 ≤ state.2.1.1.1.1.2 := by
    rcases h.counters with hc | hc <;> omega
  apply h.count_le.trans_lt
  unfold position ordinal gridSize
  nlinarith

def budget (state : State) : ℕ := gridSize state.2.1 - position state

theorem advance_budget (state : State) (h : Invariant state)
    (hi : state.1.1 < state.2.1.1.1.2) : budget (advance state) + 1 = budget state := by
  have hr : state.1.2 ≤ state.2.1.1.1.1.2 := by
    rcases h.counters with hc | hc <;> omega
  have hp := step_position state hr
  have hn := position_le_gridSize _ (step_invariant state h hi).counters
  simp only [step_retained] at hn
  simp only [advance, ite_eq_left hi, budget, step_retained]
  omega

def run (sections : CountedPositiveSections.Value) (k : ℕ) : State := advance^[k] (seed sections)

@[simp] theorem run_retained (sections : CountedPositiveSections.Value) (k : ℕ) :
    (run sections k).2.1 = sections := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [run, Function.iterate_succ_apply', advance_retained]
    exact ih

theorem run_succ (sections : CountedPositiveSections.Value) (k : ℕ) :
    run sections (k + 1) = advance (run sections k) := Function.iterate_succ_apply' _ _ _

theorem run_invariant (sections : CountedPositiveSections.Value) (k : ℕ) :
    Invariant (run sections k) := by
  induction k with
  | zero => exact seed_invariant sections
  | succ k ih => rw [run_succ]; exact advance_invariant _ ih

/-- Each grid cell is visited once; after `n(q+1)` steps the state is fixed. -/
theorem run_position (value : CountedPositiveSections.Value) (k : ℕ) :
    position (run value k) = min k (gridSize value) := by
  induction k with
  | zero => simp [run, seed, position, ordinal]
  | succ k ih =>
      rw [run_succ]
      have h := run_invariant value k
      have retained := run_retained value k
      by_cases hi : (run value k).1.1 < (run value k).2.1.1.1.2
      · have hj : (run value k).1.2 ≤ (run value k).2.1.1.1.1.2 := by
          rcases h.counters with hc | hc <;> omega
        have hp := step_position (run value k) hj
        have hn := position_le_gridSize _ (step_invariant _ h hi).counters
        simp only [step_retained, retained] at hn
        simp only [advance, ite_eq_left hi]
        omega
      · have hc : (run value k).1.1 = value.1.1.2 ∧ (run value k).1.2 = 0 := by
          rcases h.counters with hc | hc
          · omega
          · simpa only [retained] using hc
        have hp : position (run value k) = gridSize value := by
          simp [position, ordinal, gridSize, hc.1, hc.2]
        simp only [advance, ite_eq_right hi]
        omega

theorem run_active_iff (value : CountedPositiveSections.Value) (k : ℕ) :
    (run value k).1.1 < value.1.1.2 ↔ k < gridSize value := by
  have h := (run_invariant value k).counters
  have hp := run_position value k
  simp only [Counters, run_retained] at h
  have hp' : (run value k).1.1 * (value.1.1.1.2 + 1) + (run value k).1.2 = min k (gridSize value) := by
    simpa only [position, ordinal, run_retained] using hp
  rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hlt : (run value k).1.1 * (value.1.1.1.2 + 1) + (run value k).1.2 < gridSize value := by
      unfold gridSize
      nlinarith
    constructor
    · intro _; omega
    · intro _; exact hi
  · have hpterm : (run value k).1.1 * (value.1.1.1.2 + 1) + (run value k).1.2 = gridSize value := by
      simp [hi, hj, gridSize]
    constructor <;> intro hk <;> omega

theorem run_exhausted (value : CountedPositiveSections.Value) :
    (run value (gridSize value)).1 = (value.1.1.2, 0) := by
  have hn := run_active_iff value (gridSize value)
  have hc := (run_invariant value (gridSize value)).counters
  simp only [Counters, run_retained] at hc
  rcases hc with hc | hc
  · omega
  · exact Prod.ext hc.1 hc.2

theorem run_budget (value : CountedPositiveSections.Value) (k : ℕ) :
    budget (run value k) = gridSize value - k := by
  simp only [budget, run_retained, run_position]
  omega

/-- No additional predicate call is needed after the last candidate. -/
theorem run_stable (value : CountedPositiveSections.Value) (k : ℕ)
    (hk : gridSize value ≤ k) : advance (run value k) = run value k := by
  have hn : ¬ (run value k).1.1 < value.1.1.2 := by rw [run_active_iff]; omega
  simp only [advance, run_retained, ite_eq_right hn]

/-- A bounded row-major ordinal determines both endpoints uniquely. -/
theorem ordinal_injective (n : ℕ) (a b : ℕ × ℕ) (ha : a.2 ≤ n) (hb : b.2 ≤ n)
    (h : ordinal n a = ordinal n b) : a = b := by
  unfold ordinal at h
  have hi : a.1 = b.1 := by nlinarith
  exact Prod.ext hi (by nlinarith)

theorem run_pair_at (value : CountedPositiveSections.Value) (edge : ℕ × ℕ)
    (hi : edge.1 < value.1.1.2) (hj : edge.2 ≤ value.1.1.1.2) :
    (run value (ordinal value.1.1.1.2 edge)).1 = edge := by
  have hk : ordinal value.1.1.1.2 edge < gridSize value := by unfold ordinal gridSize; nlinarith
  have ha := (run_active_iff value _).mpr hk
  have hc := (run_invariant value (ordinal value.1.1.1.2 edge)).counters
  simp only [Counters, run_retained] at hc
  have hr : (run value (ordinal value.1.1.1.2 edge)).1.2 ≤ value.1.1.1.2 := by
    rcases hc with hc | hc <;> omega
  apply ordinal_injective _ _ _ hr hj
  have hp := run_position value (ordinal value.1.1.1.2 edge)
  rw [Nat.min_eq_left hk.le] at hp
  simpa only [position, run_retained] using hp

/-- One original-section cubic bit bound covers all reached states, even after exhaustion. -/
theorem run_length_le_cubic (sections : CountedPositiveSections.Value) (k : ℕ) :
    (PositiveCandidateQueries.inputFinEncoding.encode (run sections k)).length ≤
      16 * ((CountedPositiveSections.finEncoding.encode sections).length + 1) ^ 3 := by
  have h := run_invariant sections k
  have ends : (run sections k).1.1 ≤ sections.1.1.2 ∧
      (run sections k).1.2 ≤ sections.1.1.1.2 := by
    have hc := h.counters
    simp only [Counters, run_retained] at hc
    rcases hc with hc | hc <;> omega
  have hc := h.count_le.trans (position_le_gridSize _ h.counters)
  have hb := h.bounded
  simp only [run_retained] at hc hb
  have bound := PositiveCandidateTest.state_length_le_cubic sections (run sections k).1
    (run sections k).2.2 ends.1 ends.2 hc hb
  have shape : ((run sections k).1, sections, (run sections k).2.2) = run sections k :=
    Prod.ext rfl (Prod.ext (run_retained sections k).symm rfl)
  rwa [shape] at bound

/-- This bounds actual finite test-and-emit calls, not the unimplemented loop controller. -/
theorem run_filter_steps_le (sections : CountedPositiveSections.Value) (k : ℕ) :
    (positiveCandidateFilterComputableInPolyTime.outputsFun (run sections k)).steps ≤
      positiveCandidateFilterComputableInPolyTime.time.eval
        (16 * ((CountedPositiveSections.finEncoding.encode sections).length + 1) ^ 3) :=
  (positiveCandidateFilterComputableInPolyTime.outputsFun _).steps_le_m.trans
    (LeanNPHardness.MachineRuntime.polynomial_eval_mono _ (run_length_le_cubic sections k))

theorem mem_advance_of_mem (state : State) (row : PositiveBlock.Value) (h : row ∈ state.2.2) :
    row ∈ (advance state).2.2 := by
  unfold advance
  split
  · change row ∈ (PositiveCandidateFilter.filter state).2.2
    rw [PositiveCandidateFilter.rows_eq]
    split
    · exact List.mem_append_left _ h
    · exact h
  · exact h

theorem mem_iterate_of_mem (k : ℕ) (state : State) (row : PositiveBlock.Value)
    (h : row ∈ state.2.2) : row ∈ (advance^[k] state).2.2 := by
  induction k generalizing state with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih _ (mem_advance_of_mem state row h)

theorem run_mem_mono (sections : CountedPositiveSections.Value) (k l : ℕ) (hkl : k ≤ l)
    (row : PositiveBlock.Value) (h : row ∈ (run sections k).2.2) :
    row ∈ (run sections l).2.2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  have hrun : run sections (k + d) = advance^[d] (run sections k) := by
    simp only [run, Nat.add_comm k d, Function.iterate_add_apply]
  rw [hrun]
  exact mem_iterate_of_mem d _ row h

/-- Every accepted candidate appears exactly once, in the compiler's precise
row order. The count-consistency premise is proved by the existing initializer. -/
theorem run_rows_eq (sections : CountedPositiveSections.Value)
    (counted : sections.1.1.1.2 = sections.1.1.1.1.length) :
    (run sections (gridSize sections)).2.2 =
      (PositiveEnumeration.enumerate sections.1.1.2 sections.1.1.1.1).map
        (fun candidate => (candidate, sections.2.2)) := by
  apply (run_invariant sections _).ordered.eq_of_mem_iff
  · rw [List.pairwise_map]
    exact (PositiveEnumeration.enumerate_pairwise _ _).imp fun h => Prod.Lex.left _ _ h
  · intro row
    constructor
    · intro he
      have hb := (run_invariant sections _).bounded row he
      have hs := (run_invariant sections _).sound row he
      simp only [run_retained] at hb hs
      apply List.mem_map.mpr
      refine ⟨row.1, ?_, Prod.ext rfl hb.2.2.symm⟩
      exact (PositiveEnumeration.mem_enumerate _ _ _ _).mpr
        ⟨hb.1, by simpa only [← counted] using hb.2.1, hs⟩
    · intro he
      obtain ⟨candidate, hc, rfl⟩ := List.mem_map.mp he
      have hb := (PositiveEnumeration.mem_enumerate _ _ _ _).mp hc
      have hr : candidate.2 ≤ sections.1.1.1.2 := by simpa only [counted] using hb.2.1
      let k := ordinal sections.1.1.1.2 candidate
      have hk : k < gridSize sections := by dsimp [k, ordinal, gridSize]; nlinarith [hb.1]
      have pair : (run sections k).1 = candidate := run_pair_at sections candidate hb.1 hr
      have hi : (run sections k).1.1 < (run sections k).2.1.1.1.2 := by
        simpa only [run_retained, pair] using hb.1
      apply run_mem_mono sections (k + 1) _ hk
      rw [run_succ, advance, ite_eq_left hi]
      change (candidate, sections.2.2) ∈ (PositiveCandidateFilter.filter (run sections k)).2.2
      rw [PositiveCandidateFilter.rows_eq]
      simp [run_retained, pair, hb.2.2, PositiveCandidateEmit.row]

/-- No duplicate positive rows are introduced even by repeated source occurrences. -/
theorem run_nodup (sections : CountedPositiveSections.Value) (k : ℕ) :
    (run sections k).2.2.Nodup := (run_invariant sections k).ordered.nodup

/-- Specialize the exact traversal to the thesis compiler's actual pinning rows. -/
theorem run_ofRuntimeSystem (C : RuntimeSystem) :
    ((run (CountedPositiveSections.ofRuntimeSystem C)
      (gridSize (CountedPositiveSections.ofRuntimeSystem C))).2.2.map PositiveRows.row) =
      C.toExplicitSystem.pinningRows.map RuntimeResidualRow.ofResidualRow := by
  rw [run_rows_eq _ rfl, List.map_map]
  exact PositiveEnumeration.rows_eq_pinningRows C

/-- The terminal stream is literally the compiler's counted raw positive-row payload. -/
theorem run_outputEncode_ofRuntimeSystem (C : RuntimeSystem) :
    PositiveRows.outputEncode ((run (CountedPositiveSections.ofRuntimeSystem C)
      (gridSize (CountedPositiveSections.ofRuntimeSystem C))).2.2) =
      DomainFieldSection.rowPayloadEncode
        ((C.toExplicitSystem.pinningRows.map RuntimeResidualRow.ofResidualRow).map
          RuntimeResidualRow.toNatList) := by
  rw [PositiveRows.outputEncode_eq_rows, run_ofRuntimeSystem]

/-- Both bounds were emitted in unary, so the number of visits is quadratic in wire length. -/
theorem iterations_le_wire_quadratic (sections : CountedPositiveSections.Value) :
    gridSize sections ≤ (CountedPositiveSections.finEncoding.encode sections).length *
      ((CountedPositiveSections.finEncoding.encode sections).length + 1) :=
  CountedPositiveSections.gridSize_le_wire_quadratic sections

example : (run (((([(0, 2), (0, 2), (2, 1)], 3), 4), [[]]), ([(0, 2)], 7)) 16).2.2 =
    [((0, 2), 7), ((2, 1), 7)] := by decide
example : (run (((([], 0), 3), []), ([], 1)) 3).1 = (3, 0) := by decide
example : (run (((([], 0), 0), []), ([], 1)) 12).2.2 = [] := by decide
example : nextPair 2 (0, 1) = (0, 2) := by decide
example : nextPair 2 (0, 2) = (1, 0) := by decide

#print axioms run_position
#print axioms run_exhausted
#print axioms run_stable
#print axioms run_pair_at
#print axioms run_rows_eq
#print axioms run_nodup
#print axioms run_ofRuntimeSystem
#print axioms run_outputEncode_ofRuntimeSystem
#print axioms iterations_le_wire_quadratic
#print axioms next_position
#print axioms step_invariant
#print axioms fresh
#print axioms active_capacity
#print axioms advance_budget
#print axioms run_invariant
#print axioms run_length_le_cubic
#print axioms run_filter_steps_le

end PositiveAdvance

end PhdThesisLean.AllDifferentCSPMachine
