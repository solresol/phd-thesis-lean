import PhdThesisLean.SmithSweepBounds
import PhdThesisLean.SmithForwardBounds
import PhdThesisLean.SmithDiagonalization

/-!
# The complete diagonalizer trace and its width-dependent addition count

Reify all sweep pairs and diagonal stages of the existing algorithm. Replay
is unconditional and covers the entire five-matrix state. The addition-count
bound is conditional on a common intermediate width; proving that width is
polynomial in the original input remains open. Counting additions does not
charge quotient computation, traversal, trace construction or machine steps.
-/

namespace PhdThesisLean.SmithTraceCount

open SmithTrace SmithReduction SmithSweep SmithIsolation SmithIsolationCount
  SmithSweepBounds SmithDiagonalization SmithEncoding SmithDecomposition

variable {m n : ℕ}

/-- Bound the transformed entries at every actual addition prefix. The
parameter is a proposed width, not an established global input-bit bound. -/
def PrefixWidth (Q : State m n) (ops : List (Op m n)) (b : ℕ) : Prop :=
  ∀ t i j, ((run Q (ops.take t)).S i j).natAbs < 2 ^ b

theorem PrefixWidth.initial {Q : State m n} {ops : List (Op m n)} {b : ℕ}
    (h : PrefixWidth Q ops b) : ∀ i j, (Q.S i j).natAbs < 2 ^ b := by
  simpa only [List.take_zero, run] using h 0

theorem PrefixWidth.left {Q : State m n} {xs ys : List (Op m n)} {b : ℕ}
    (h : PrefixWidth Q (xs ++ ys) b) : PrefixWidth Q xs b := by
  intro t i j
  by_cases ht : t ≤ xs.length
  · simpa only [List.take_append, Nat.sub_eq_zero_of_le ht, List.take_zero,
      List.append_nil] using h t i j
  · have hle : xs.length ≤ t := by omega
    simpa only [List.take_append, List.take_length, Nat.sub_self, List.take_zero,
      List.append_nil, List.take_of_length_le hle] using h xs.length i j

theorem PrefixWidth.right {Q : State m n} {xs ys : List (Op m n)} {b : ℕ}
    (h : PrefixWidth Q (xs ++ ys) b) : PrefixWidth (run Q xs) ys b := by
  intro t i j
  have ht := h (xs.length + t) i j
  simpa only [List.take_append,
    List.take_of_length_le (Nat.le_add_right xs.length t), Nat.add_sub_cancel_left,
    SmithSweepBounds.run_append] using ht

/-- A pair pays at most eight additions per selected-entry bit per target.
Both the incoming column and the actual row-sweep midpoint are charged. -/
theorem crossTrace_length_le_of_width (Q : State m n) (k b : ℕ) (hb : 0 < b)
    (h : PrefixWidth Q (crossTrace Q k) b) :
    (crossTrace Q k).length ≤ 8 * (m + n) * b := by
  have hstart := h.initial
  have hmid : ∀ i j, ((clearActiveColumn Q k).S i j).natAbs < 2 ^ b := by
    intro i j
    have ht := h (columnTrace Q k).length i j
    simpa only [crossTrace, List.take_append, List.take_length, Nat.sub_self,
      List.take_zero, List.append_nil, columnTrace_run] using ht
  have hcol := columnTrace_length_le Q k b hb hstart
  have hrow := columnTrace_length_le (transposeState (clearActiveColumn Q k))
    k b hb (fun i j => hmid j i)
  simpa only [crossTrace, List.length_append, List.length_map] using
    (show (columnTrace Q k).length +
      (columnTrace (transposeState (clearActiveColumn Q k)) k).length ≤
        8 * (m + n) * b by nlinarith)

/-- The computed trace of a specified number of consecutive sweep pairs. -/
def crossesTrace (Q : State m n) (k : ℕ) : ℕ → List (Op m n)
  | 0 => []
  | count + 1 => crossTrace Q k ++ crossesTrace (cross Q k) k count

theorem crossesTrace_run (Q : State m n) (k count : ℕ) :
    run Q (crossesTrace Q k count) = crosses Q k count := by
  induction count generalizing Q with
  | zero => rfl
  | succ count ih =>
      simp only [crossesTrace, crosses, SmithSweepBounds.run_append, crossTrace_run, ih]

theorem crossesTrace_length_le_of_width (Q : State m n) (k count b : ℕ)
    (hb : 0 < b) (h : PrefixWidth Q (crossesTrace Q k count) b) :
    (crossesTrace Q k count).length ≤ count * (8 * (m + n) * b) := by
  induction count generalizing Q with
  | zero => simp [crossesTrace]
  | succ count ih =>
      change PrefixWidth Q (crossTrace Q k ++ crossesTrace (cross Q k) k count) b at h
      have hfirst := crossTrace_length_le_of_width Q k b hb h.left
      have htail : PrefixWidth (cross Q k) (crossesTrace (cross Q k) k count) b := by
        simpa only [crossTrace_run] using h.right
      have hrest := ih (cross Q k) htail
      simp only [crossesTrace, List.length_append]
      nlinarith

/-- No supplied pass count: use the existing executable counter, which
replays exactly the terminating isolator, including its zero-pivot seeding. -/
def isolateTrace (Q : State m n) (k : ℕ) : List (Op m n) :=
  crossesTrace Q k (isolationPasses Q k)

theorem isolateTrace_run (Q : State m n) (k : ℕ) :
    run Q (isolateTrace Q k) = isolate Q k := by
  rw [isolateTrace, crossesTrace_run, isolationPasses_replay]

theorem isolateTrace_of_missing (Q : State m n) (k : ℕ)
    (h : m ≤ k ∨ n ≤ k) : isolateTrace Q k = [] := by
  rw [isolateTrace, isolationPasses_of_missing Q k h, crossesTrace]

theorem isolationPasses_le_of_width (Q : State m n) (k b : ℕ)
    (h : ∀ i j, (Q.S i j).natAbs < 2 ^ b) :
    isolationPasses Q k ≤ b + 1 := by
  by_cases hr : k < m
  · by_cases hc : k < n
    · have hp : 0 < (2 : ℕ) ^ b := by positivity
      have hs := cross_pivot_le Q k hr hc (2 ^ b - 1) (fun i j => by
        have := h i j
        omega)
      have hs' : ((cross Q k).S ⟨k, hr⟩ ⟨k, hc⟩).natAbs < 2 ^ b := by omega
      have hsize := Nat.size_le.mpr hs'
      have hcount := isolationPasses_le_seed_size Q k hr hc
      omega
    · rw [isolationPasses_of_missing Q k (Or.inr (by omega))]
      omega
  · rw [isolationPasses_of_missing Q k (Or.inl (by omega))]
    omega

theorem isolateTrace_length_le_of_width (Q : State m n) (k b : ℕ) (hb : 0 < b)
    (h : PrefixWidth Q (isolateTrace Q k) b) :
    (isolateTrace Q k).length ≤ (b + 1) * (8 * (m + n) * b) := by
  exact (crossesTrace_length_le_of_width Q k _ b hb h).trans
    (Nat.mul_le_mul_right _ (isolationPasses_le_of_width Q k b h.initial))

/-- Reify all remaining stages of the existing rectangular diagonalizer.
The dimension recursion is the same as `finish`; no new algorithm is selected. -/
def finishTrace (Q : State m n) (k : ℕ) : List (Op m n) :=
  if _h : k < min m n then
    isolateTrace Q k ++ finishTrace (isolate Q k) (k + 1)
  else []
termination_by min m n - k
decreasing_by omega

theorem finishTrace_of_done (Q : State m n) (k : ℕ) (h : min m n ≤ k) :
    finishTrace Q k = [] := by
  rw [finishTrace]
  split_ifs with hactive
  · omega
  · rfl

theorem finishTrace_run (Q : State m n) (k : ℕ) :
    run Q (finishTrace Q k) = finish Q k := by
  rw [finishTrace, finish]
  split_ifs with h
  · rw [SmithSweepBounds.run_append, isolateTrace_run, finishTrace_run]
  · rfl
termination_by min m n - k
decreasing_by omega

theorem finishTrace_length_le_of_width (Q : State m n) (k b : ℕ) (hb : 0 < b)
    (h : PrefixWidth Q (finishTrace Q k) b) :
    (finishTrace Q k).length ≤
      (min m n - k) * ((b + 1) * (8 * (m + n) * b)) := by
  rw [finishTrace] at h ⊢
  split_ifs at h ⊢ with hk
  · have hfirst := isolateTrace_length_le_of_width Q k b hb h.left
    have htail : PrefixWidth (isolate Q k) (finishTrace (isolate Q k) (k + 1)) b := by
      simpa only [isolateTrace_run] using h.right
    have hrest := finishTrace_length_le_of_width (isolate Q k) (k + 1) b hb htail
    have hd : min m n - k = (min m n - (k + 1)) + 1 := by omega
    rw [List.length_append, hd]
    nlinarith
  · simp
termination_by min m n - k
decreasing_by omega

/-- Full trace selected from the original dense input alone. -/
def decomposeTrace (A : Dense) : List (Op A.rows A.cols) :=
  finishTrace (initial A.toMatrix) 0

theorem decomposeTrace_result (A : Dense) :
    (run (initial A.toMatrix) (decomposeTrace A)).result = decompose A := by
  rw [decomposeTrace, finishTrace_run]
  rfl

theorem decomposeTrace_valid (A : Dense) :
    Valid A.toMatrix (run (initial A.toMatrix) (decomposeTrace A)).result := by
  rw [decomposeTrace_result]
  exact decompose_valid A

theorem decomposeTrace_of_empty (A : Dense) (h : A.rows = 0 ∨ A.cols = 0) :
    decomposeTrace A = [] := by
  apply finishTrace_of_done
  rcases h with h | h <;> simp [h]

/-- Dimensions are charged to the existing unary headers, including empty
rectangles. This is polynomial in input bits AND the proposed global width. -/
theorem decomposeTrace_length_le_of_width (A : Dense) (b : ℕ) (hb : 0 < b)
    (h : PrefixWidth (initial A.toMatrix) (decomposeTrace A) b) :
    (decomposeTrace A).length ≤
      8 * (SmithEncoding.encode A).length * (SmithEncoding.encode A).length * b * (b + 1) := by
  have ht := finishTrace_length_le_of_width (initial A.toMatrix) 0 b hb h
  have hd := dimensions_le_length A
  have hm : min A.rows A.cols ≤ (SmithEncoding.encode A).length := by omega
  have hsum : A.rows + A.cols ≤ (SmithEncoding.encode A).length := by omega
  simp only [Nat.sub_zero] at ht
  exact ht.trans (by
    calc
      min A.rows A.cols * ((b + 1) * (8 * (A.rows + A.cols) * b)) ≤
          (SmithEncoding.encode A).length *
            ((b + 1) * (8 * (SmithEncoding.encode A).length * b)) := by gcongr
      _ = _ := by ring)

/-- Combine the semantic count with the preceding forward-map reduction.
The two uniform forward bounds are STILL HYPOTHESES: this proves neither
their polynomial growth nor any binary arithmetic or machine runtime. -/
theorem decomposeTrace_length_le_of_forward (A : Dense) (d : ℕ)
    (hU : ∀ t i j, ((run (initial A.toMatrix) ((decomposeTrace A).take t)).U i j).natAbs ≤ 2 ^ d)
    (hV : ∀ t i j, ((run (initial A.toMatrix) ((decomposeTrace A).take t)).V i j).natAbs ≤ 2 ^ d) :
    let s := (SmithEncoding.encode A).length
    let B := SmithForwardBounds.stateWidth s d
    (decomposeTrace A).length ≤ 8 * s * s * (B + 1) * (B + 2) := by
  apply decomposeTrace_length_le_of_width A (SmithForwardBounds.stateWidth _ d + 1) (by omega)
  intro t i j
  have hs := (SmithForwardBounds.trace_prefix_bound A (decomposeTrace A) t d (hU t) (hV t)).S i j
  have hp : 0 < (2 : ℕ) ^ SmithForwardBounds.stateWidth (SmithEncoding.encode A).length d := by positivity
  rw [pow_succ]
  omega

-- Kernel theorem specializations retain the rectangular/empty guards.
private abbrev exactInput : Dense := ⟨2, 2, [2, 4, 0, 6], rfl⟩
example : Valid (⟨3, 2, [0, -6, 0, 12, 0, 0], rfl⟩ : Dense).toMatrix
    (run (initial (⟨3, 2, [0, -6, 0, 12, 0, 0], rfl⟩ : Dense).toMatrix)
      (decomposeTrace ⟨3, 2, [0, -6, 0, 12, 0, 0], rfl⟩)).result :=
  decomposeTrace_valid _
example : decomposeTrace (⟨0, 3, [], rfl⟩ : Dense) = [] :=
  decomposeTrace_of_empty _ (Or.inl rfl)
example : decomposeTrace (⟨3, 0, [], rfl⟩ : Dense) = [] :=
  decomposeTrace_of_empty _ (Or.inr rfl)
example : decomposeTrace (⟨0, 0, [], rfl⟩ : Dense) = [] :=
  decomposeTrace_of_empty _ (Or.inl rfl)
example : isolateTrace (initial exactInput.toMatrix) 42 = [] :=
  isolateTrace_of_missing _ _ (Or.inl (by decide))

-- Evaluator regression evidence is separate from universal kernel proofs.
/-- info: (4, [2, 0, 0, 6], true) -/
#guard_msgs in
#eval ((decomposeTrace exactInput).length,
  (pack (run (initial exactInput.toMatrix) (decomposeTrace exactInput)).S).val.entries,
  check exactInput.toMatrix (run (initial exactInput.toMatrix) (decomposeTrace exactInput)).result)

end PhdThesisLean.SmithTraceCount
