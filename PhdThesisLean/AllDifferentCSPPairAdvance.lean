import PhdThesisLean.AllDifferentCSPPairInitialization

/-!
# Bounded candidate-pair advancement and its loop invariant

The executable step consumes the checked candidate test, conditionally appends
one edge, and advances the lexicographic grid. The invariant bounds every
state in the original retained wire length and tracks a decreasing grid
budget; the completed scan equals the exact ordered primal-edge list. This is an executable specification with checked semantic/size lemmas;
the two finite counter actions are supplied by `AllDifferentCSPPairCounters`.
Branch selection and repeated dispatch remain open. The conditional emission
machine is supplied separately by `AllDifferentCSPPairEmit`.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding

namespace PairAdvance

abbrev State := PairQueries.Input

def ordinal (n : ℕ) (pair : ℕ × ℕ) : ℕ := pair.1 * n + pair.2

def position (state : State) : ℕ := ordinal state.2.1.1.2 state.1

def nextPair (n : ℕ) (pair : ℕ × ℕ) : ℕ × ℕ :=
  if pair.2 + 1 < n then (pair.1, pair.2 + 1) else (pair.1 + 1, 0)

/-- Consume exactly the Boolean returned by the checked retained-state test. -/
def afterTest (tested : PairTest.Output) : State :=
  (nextPair tested.2.2.1.1.2 tested.2.1, tested.2.2.1,
    if tested.1 then tested.2.2.2 ++ [tested.2.1] else tested.2.2.2)

def advance (state : State) : State :=
  if state.1.1 < state.2.1.1.2 then afterTest (PairTest.evaluate state) else state

/-- Canonical exhaustion is `(n,0)`; zero variables start exhausted. -/
def Counters (state : State) : Prop :=
  (state.1.1 < state.2.1.1.2 ∧ state.1.2 < state.2.1.1.2) ∨
    (state.1.1 = state.2.1.1.2 ∧ state.1.2 = 0)

structure Invariant (state : State) : Prop where
  counters : Counters state
  count_le : state.2.2.length ≤ position state
  earlier : ∀ edge ∈ state.2.2, ordinal state.2.1.1.2 edge < position state
  sound : ∀ edge ∈ state.2.2, edge ∈ BoundedRelabelledSections.edges state.2.1
  ordered : state.2.2.Pairwise (Prod.Lex (· < ·) (· < ·))

@[simp] theorem afterTest_retained (tested : PairTest.Output) :
    (afterTest tested).2.1 = tested.2.2.1 := rfl

@[simp] theorem advance_retained (state : State) : (advance state).2.1 = state.2.1 := by
  unfold advance
  split <;> rfl

theorem next_position (n : ℕ) (pair : ℕ × ℕ) (hj : pair.2 < n) :
    ordinal n (nextPair n pair) = ordinal n pair + 1 := by
  unfold nextPair ordinal
  split <;> dsimp only
  · omega
  · have h : pair.2 + 1 = n := by omega
    nlinarith

theorem next_counters (n : ℕ) (pair : ℕ × ℕ) (hi : pair.1 < n) (hj : pair.2 < n) :
    ((nextPair n pair).1 < n ∧ (nextPair n pair).2 < n) ∨
      ((nextPair n pair).1 = n ∧ (nextPair n pair).2 = 0) := by
  unfold nextPair
  split <;> dsimp only <;> omega

theorem position_le_square (state : State) (h : Counters state) :
    position state ≤ state.2.1.1.2 ^ 2 := by
  rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · unfold position ordinal
    nlinarith
  · simp [position, ordinal, hi, hj, pow_two]

theorem ordinal_lt_iff_lex (n : ℕ) (a b : ℕ × ℕ) (ha : a.2 < n) (hb : b.2 < n) :
    ordinal n a < ordinal n b ↔ Prod.Lex (· < ·) (· < ·) a b := by
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

theorem seed_invariant (value : BoundedRelabelledSections.Value) :
    Invariant (PairInitialization.seed value) := by
  constructor
  · simp [Counters, PairInitialization.seed]; omega
  · simp [PairInitialization.seed, position, ordinal]
  · simp [PairInitialization.seed]
  · simp [PairInitialization.seed]
  · simp [PairInitialization.seed]

/-- One active transition reserves at most one row and advances exactly one cell. -/
theorem afterTest_position (state : State) (hj : state.1.2 < state.2.1.1.2) :
    position (afterTest (PairTest.evaluate state)) = position state + 1 :=
  next_position _ _ hj

theorem afterTest_invariant (state : State) (h : Invariant state)
    (hi : state.1.1 < state.2.1.1.2) : Invariant (afterTest (PairTest.evaluate state)) := by
  have hj : state.1.2 < state.2.1.1.2 := by
    rcases h.counters with hc | hc <;> omega
  have hp := afterTest_position state hj
  have hc := next_counters state.2.1.1.2 state.1 hi hj
  have hb : ∀ edge ∈ state.2.2, edge.2 < state.2.1.1.2 := by
    intro edge he
    exact (PrimalEdgeEnumeration.mem_enumerate _ _ _ _ |>.mp (h.sound edge he)).2.1
  constructor
  · exact hc
  · change (if PairTest.accept state then state.2.2 ++ [state.1] else state.2.2).length ≤ _
    rw [hp]
    have hcount := h.count_le
    split
    · simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right hcount 1
    · omega
  · intro edge he
    rw [hp]
    change ordinal state.2.1.1.2 edge < position state + 1
    change edge ∈ (if PairTest.accept state then state.2.2 ++ [state.1] else state.2.2) at he
    split at he
    · rcases List.mem_append.mp he with he | he
      · exact (h.earlier edge he).trans (Nat.lt_succ_self _)
      · have heq := List.mem_singleton.mp he
        subst edge
        exact Nat.lt_succ_self _
    · exact (h.earlier edge he).trans (Nat.lt_succ_self _)
  · intro edge he
    change edge ∈ BoundedRelabelledSections.edges state.2.1
    change edge ∈ (if PairTest.accept state then state.2.2 ++ [state.1] else state.2.2) at he
    split at he
    next ht =>
      rcases List.mem_append.mp he with he | he
      · exact h.sound edge he
      · have heq := List.mem_singleton.mp he
        subst edge
        exact (PairTest.accept_iff_mem_enumerate state hi hj).mp ht
    next => exact h.sound edge he
  · change (if PairTest.accept state then state.2.2 ++ [state.1] else state.2.2).Pairwise _
    split
    · rw [List.pairwise_append]
      refine ⟨h.ordered, by simp, ?_⟩
      intro edge he last hl
      have heq := List.mem_singleton.mp hl
      subst last
      exact (ordinal_lt_iff_lex _ _ _ (hb edge he) hj).mp (h.earlier edge he)
    · exact h.ordered

theorem advance_invariant (state : State) (h : Invariant state) : Invariant (advance state) := by
  unfold advance
  split
  · exact afterTest_invariant state h ‹_›
  · exact h

/-- The ordinal, rather than binary word length, measures the finite grid. -/
def budget (state : State) : ℕ := state.2.1.1.2 ^ 2 - position state

theorem advance_budget (state : State) (h : Invariant state)
    (hi : state.1.1 < state.2.1.1.2) : budget (advance state) + 1 = budget state := by
  have hj : state.1.2 < state.2.1.1.2 := by
    rcases h.counters with hc | hc <;> omega
  have hp := afterTest_position state hj
  have hn := position_le_square _ (afterTest_invariant state h hi).counters
  simp only [afterTest_retained, PairTest.retained_eq] at hn
  simp only [advance, if_pos hi, budget, afterTest_retained, PairTest.retained_eq]
  omega

/-- The same invariant holds at every executable iteration, including exhaustion. -/
theorem iterate_invariant (k : ℕ) (state : State) (h : Invariant state) :
    Invariant (advance^[k] state) := by
  induction k generalizing state with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih _ (advance_invariant state h)

@[simp] theorem iterate_retained (k : ℕ) (state : State) :
    (advance^[k] state).2.1 = state.2.1 := by
  induction k generalizing state with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, advance_retained]

/-- The cubic bound holds for every iterate from the constructed seed, including
terminal and zero-variable states, with no external accumulator hypotheses. -/
theorem iterate_length_le_cubic (value : BoundedRelabelledSections.Value) (k : ℕ) :
    (PairQueries.inputFinEncoding.encode (advance^[k] (PairInitialization.seed value))).length ≤
      12 * ((BoundedRelabelledSections.finEncoding.encode value).length + 1) ^ 3 := by
  let state := advance^[k] (PairInitialization.seed value)
  have h : Invariant state := iterate_invariant k _ (seed_invariant value)
  have retained : state.2.1 = value := iterate_retained k _
  have ends : state.1.1 ≤ state.2.1.1.2 ∧ state.1.2 ≤ state.2.1.1.2 := by
    rcases h.counters with hc | hc <;> omega
  have bound := PairTest.state_length_le_cubic_of_le state ends.1 ends.2
    (h.count_le.trans (position_le_square state h.counters)) (by
      intro edge he
      have hs := (PrimalEdgeEnumeration.mem_enumerate _ _ _ _).mp (h.sound edge he)
      exact ⟨hs.1, hs.2.1⟩)
  simpa only [retained] using bound

/-- Complete calls to the already checked test have one common polynomial
bound in the original retained-section length throughout the executable scan. -/
theorem iterate_test_steps_le (value : BoundedRelabelledSections.Value) (k : ℕ) :
    (pairTestComputableInPolyTime.outputsFun (advance^[k] (PairInitialization.seed value))).steps ≤
      pairTestComputableInPolyTime.time.eval
        (12 * ((BoundedRelabelledSections.finEncoding.encode value).length + 1) ^ 3) :=
  pairTest_steps_le _ _ (iterate_length_le_cubic value k)

/-- Executable scan states; this definition carries no machine runtime claim. -/
def run (value : BoundedRelabelledSections.Value) (k : ℕ) : State :=
  advance^[k] (PairInitialization.seed value)

@[simp] theorem run_retained (value : BoundedRelabelledSections.Value) (k : ℕ) :
    (run value k).2.1 = value := iterate_retained k _

theorem run_invariant (value : BoundedRelabelledSections.Value) (k : ℕ) :
    Invariant (run value k) := iterate_invariant k _ (seed_invariant value)

theorem run_succ (value : BoundedRelabelledSections.Value) (k : ℕ) :
    run value (k + 1) = advance (run value k) := Function.iterate_succ_apply' _ _ _

/-- Each grid cell is visited once; after `n²` steps the state is fixed. -/
theorem run_position (value : BoundedRelabelledSections.Value) (k : ℕ) :
    position (run value k) = min k (value.1.2 ^ 2) := by
  induction k with
  | zero => simp [run, PairInitialization.seed, position, ordinal]
  | succ k ih =>
      rw [run_succ]
      have h := run_invariant value k
      have retained := run_retained value k
      by_cases hi : (run value k).1.1 < (run value k).2.1.1.2
      · have hj : (run value k).1.2 < (run value k).2.1.1.2 := by
          rcases h.counters with hc | hc <;> omega
        have hp := afterTest_position (run value k) hj
        have hn := position_le_square _ (afterTest_invariant _ h hi).counters
        simp only [afterTest_retained, PairTest.retained_eq, retained] at hn
        simp only [advance, if_pos hi]
        omega
      · have hc : (run value k).1.1 = value.1.2 ∧ (run value k).1.2 = 0 := by
          rcases h.counters with hc | hc
          · omega
          · simpa only [retained] using hc
        have hp : position (run value k) = value.1.2 ^ 2 := by
          simp [position, ordinal, hc.1, hc.2, pow_two]
        simp only [advance, if_neg hi]
        omega

theorem run_active_iff (value : BoundedRelabelledSections.Value) (k : ℕ) :
    (run value k).1.1 < value.1.2 ↔ k < value.1.2 ^ 2 := by
  have h := (run_invariant value k).counters
  have hp := run_position value k
  simp only [Counters, run_retained] at h
  have hp' : (run value k).1.1 * value.1.2 + (run value k).1.2 = min k (value.1.2 ^ 2) := by
    simpa only [position, ordinal, run_retained] using hp
  rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hlt : (run value k).1.1 * value.1.2 + (run value k).1.2 < value.1.2 ^ 2 := by
      nlinarith
    constructor
    · intro _; omega
    · intro _; exact hi
  · constructor <;> intro hk <;> nlinarith [Nat.min_le_left k (value.1.2 ^ 2)]

theorem run_exhausted (value : BoundedRelabelledSections.Value) :
    (run value (value.1.2 ^ 2)).1 = (value.1.2, 0) := by
  have hn := run_active_iff value (value.1.2 ^ 2)
  have hc := (run_invariant value (value.1.2 ^ 2)).counters
  simp only [Counters, run_retained] at hc
  rcases hc with hc | hc
  · omega
  · exact Prod.ext hc.1 hc.2

theorem run_budget (value : BoundedRelabelledSections.Value) (k : ℕ) :
    budget (run value k) = value.1.2 ^ 2 - k := by
  simp only [budget, run_retained, run_position]
  omega

/-- No additional predicate call is needed after the last candidate. -/
theorem run_stable (value : BoundedRelabelledSections.Value) (k : ℕ)
    (hk : value.1.2 ^ 2 ≤ k) : advance (run value k) = run value k := by
  have hn : ¬ (run value k).1.1 < value.1.2 := by rw [run_active_iff]; omega
  simp only [advance, run_retained, if_neg hn]

/-- The unary bound makes the number of candidates polynomial in actual wire
length. This is a cycle count; finite dispatch costs still require a machine. -/
theorem iterations_le_wire_square (value : BoundedRelabelledSections.Value) :
    value.1.2 ^ 2 ≤ (BoundedRelabelledSections.finEncoding.encode value).length ^ 2 :=
  Nat.pow_le_pow_left (BoundedRelabelledSections.variableCount_le_encode_length value) 2

/-- A bounded row-major ordinal determines both endpoints uniquely. -/
theorem ordinal_injective (n : ℕ) (a b : ℕ × ℕ) (ha : a.2 < n) (hb : b.2 < n)
    (h : ordinal n a = ordinal n b) : a = b := by
  unfold ordinal at h
  have hi : a.1 = b.1 := by nlinarith
  exact Prod.ext hi (by nlinarith)

theorem run_pair_at (value : BoundedRelabelledSections.Value) (edge : ℕ × ℕ)
    (hi : edge.1 < value.1.2) (hj : edge.2 < value.1.2) :
    (run value (ordinal value.1.2 edge)).1 = edge := by
  have hk : ordinal value.1.2 edge < value.1.2 ^ 2 := by unfold ordinal; nlinarith
  have ha := (run_active_iff value _).mpr hk
  have hc := (run_invariant value (ordinal value.1.2 edge)).counters
  simp only [Counters, run_retained] at hc
  have hr : (run value (ordinal value.1.2 edge)).1.2 < value.1.2 := by
    rcases hc with hc | hc <;> omega
  apply ordinal_injective _ _ _ hr hj
  have hp := run_position value (ordinal value.1.2 edge)
  rw [Nat.min_eq_left hk.le] at hp
  simpa only [position, run_retained] using hp

theorem mem_advance_of_mem (state : State) (edge : ℕ × ℕ) (h : edge ∈ state.2.2) :
    edge ∈ (advance state).2.2 := by
  unfold advance
  split
  · simp only [afterTest, PairTest.evaluate]
    split
    · exact List.mem_append_left _ h
    · exact h
  · exact h

theorem mem_iterate_of_mem (k : ℕ) (state : State) (edge : ℕ × ℕ) (h : edge ∈ state.2.2) :
    edge ∈ (advance^[k] state).2.2 := by
  induction k generalizing state with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih _ (mem_advance_of_mem state edge h)

theorem run_mem_mono (value : BoundedRelabelledSections.Value) (k l : ℕ) (hkl : k ≤ l)
    (edge : ℕ × ℕ) (h : edge ∈ (run value k).2.2) : edge ∈ (run value l).2.2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  have hrun : run value (k + d) = advance^[d] (run value k) := by
    simp only [run, Nat.add_comm k d, Function.iterate_add_apply]
  rw [hrun]
  exact mem_iterate_of_mem d _ edge h

/-- The terminal ordered list is exactly the established deduplicated primal
edge enumeration, including empty grids and overlapping or repeated scopes. -/
theorem run_edges_eq (value : BoundedRelabelledSections.Value) :
    (run value (value.1.2 ^ 2)).2.2 = BoundedRelabelledSections.edges value := by
  apply (run_invariant value _).ordered.eq_of_mem_iff
    (PrimalEdgeEnumeration.enumerate_pairwise _ _)
  intro edge
  constructor
  · intro he
    simpa only [run_retained] using (run_invariant value _).sound edge he
  · intro he
    have hb := (PrimalEdgeEnumeration.mem_enumerate _ _ _ _).mp he
    let k := ordinal value.1.2 edge
    have hk : k < value.1.2 ^ 2 := by dsimp [k, ordinal]; nlinarith [hb.1, hb.2.1]
    have pair : (run value k).1 = edge := run_pair_at value edge hb.1 hb.2.1
    have hi : (run value k).1.1 < (run value k).2.1.1.2 := by
      simpa only [run_retained, pair] using hb.1
    have hj : (run value k).1.2 < (run value k).2.1.1.2 := by
      simpa only [run_retained, pair] using hb.2.1
    have ht : PairTest.accept (run value k) = true :=
      (PairTest.accept_iff_mem_enumerate _ hi hj).mpr (by simpa only [run_retained, pair] using he)
    apply run_mem_mono value (k + 1) _ hk edge
    rw [run_succ]
    simp [advance, afterTest, PairTest.evaluate, ht, pair, hb.1]

theorem run_ofRuntimeSystem (C : RuntimeSystem) :
    (run (BoundedRelabelledSections.ofRuntimeSystem C) (C.domains.length ^ 2)).2.2 =
      PrimalEdgeEnumeration.ofRuntimeSystem C := run_edges_eq _

example : (run (([], 4), [[2, 0, 2], [], [0, 2], [3], [1, 3, 2], [99, 0]]) 16).2.2 =
    [(0, 2), (1, 2), (1, 3), (2, 3)] := by decide
example : (run (([], 0), [[0, 1]]) 0).2.2 = [] := rfl

example : advance ((0, 0), (([], 0), [[0, 1]]), []) =
    ((0, 0), (([], 0), [[0, 1]]), []) := rfl
example : advance ((0, 0), (([], 1), [[0, 0]]), []) =
    ((1, 0), (([], 1), [[0, 0]]), []) := by decide
example : advance ((0, 1), (([], 2), [[0, 1], [1, 0, 1]]), []) =
    ((1, 0), (([], 2), [[0, 1], [1, 0, 1]]), [(0, 1)]) := by decide

#print axioms run_budget
#print axioms run_stable
#print axioms iterations_le_wire_square
#print axioms run_position
#print axioms run_exhausted
#print axioms run_edges_eq
#print axioms run_ofRuntimeSystem
#print axioms seed_invariant
#print axioms afterTest_invariant
#print axioms advance_budget
#print axioms iterate_invariant
#print axioms iterate_length_le_cubic
#print axioms iterate_test_steps_le

end PairAdvance

end PhdThesisLean.AllDifferentCSPMachine
