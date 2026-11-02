import PhdThesisLean.SmithPivot
import PhdThesisLean.SmithIsolationCount

/-!
# Local binary bounds for a computed Euclidean pivot

These bounds concern one pair pivot and every prefix of its actual addition
trace. All five state matrices, including the integral inverses, are covered.
They do not assert polynomial global growth through a complete decomposition
or give costs for arithmetic or structural operations on a finite machine.
-/

namespace PhdThesisLean.SmithPivotBounds

open SmithTrace SmithPivot SmithRowOperations SmithEncoding SmithDecomposition

variable {m n : ℕ}

/-- Two nonterminal Euclidean divisions at least halve the second magnitude. -/
theorem remainder_pair_halves (a b : ℕ) (hb : 0 < b) (hr : 0 < a % b) :
    2 * (b % (a % b)) ≤ b := by
  have hrb := Nat.mod_lt a hb
  have ht := Nat.mod_lt b hr
  by_cases h : 2 * (a % b) ≤ b
  · omega
  · have hdiv : b / (a % b) = 1 := by
      apply Nat.div_eq_of_lt_le <;> omega
    have hrem := Nat.div_add_mod b (a % b)
    rw [hdiv] at hrem
    omega

/-- The existing trace uses four additions per division and at most two
nonterminal divisions per second-entry bit. This is a semantic list length. -/
theorem gcdTrace_length_le (r s : Fin m) (h : r ≠ s) (a b : ℤ) :
    (gcdTrace (n := n) r s h a b).length ≤ 8 * b.natAbs.size := by
  rw [gcdTrace]
  split_ifs with hb
  · simp
  · let c := -(a.tmod b)
    have hcabs : c.natAbs = a.natAbs % b.natAbs := by simp [c]
    change (pairStep (n := n) r s h (a.tdiv b) ++ gcdTrace r s h b c).length ≤ _
    rw [List.length_append]
    by_cases hc : c = 0
    · rw [hc, gcdTrace]
      simp only [↓reduceDIte, pairStep, List.length_cons, List.length_nil]
      have hp := Nat.size_pos.mpr (Int.natAbs_pos.mpr hb)
      omega
    · rw [gcdTrace]
      simp only [hc, ↓reduceDIte]
      have hi := gcdTrace_length_le r s h c (-(b.tmod c))
      have hhalves : 2 * (-(b.tmod c)).natAbs ≤ b.natAbs := by
        simpa only [Int.natAbs_neg, Int.natAbs_tmod, hcabs] using
          remainder_pair_halves a.natAbs b.natAbs (Int.natAbs_pos.mpr hb) (by
            rw [← hcabs]; exact Int.natAbs_pos.mpr hc)
      have hsize : (-(b.tmod c)).natAbs.size < b.natAbs.size := by
        by_cases hz : (-(b.tmod c)).natAbs = 0
        · simp only [hz, Nat.size_zero]
          exact Nat.size_pos.mpr (Int.natAbs_pos.mpr hb)
        · exact SmithIsolationCount.size_lt_of_halves (Nat.pos_of_ne_zero hz) hhalves
      change (pairStep (n := n) r s h (a.tdiv b)).length +
        (pairStep r s h (b.tdiv c) ++ gcdTrace r s h c (-(b.tmod c))).length ≤ _
      simp only [List.length_append, pairStep, List.length_cons, List.length_nil] at *
      omega
termination_by b.natAbs
decreasing_by
  have hcabs : (-(a.tmod b)).natAbs < b.natAbs := remainder_descent a b hb
  exact lt_trans (remainder_descent b c hc) hcabs

/-- Common magnitude bound for every entry of all five matrices. -/
structure Bounded (Q : State m n) (H : ℕ) : Prop where
  U : ∀ i j, (Q.U i j).natAbs ≤ H
  Uinv : ∀ i j, (Q.Uinv i j).natAbs ≤ H
  V : ∀ i j, (Q.V i j).natAbs ≤ H
  Vinv : ∀ i j, (Q.Vinv i j).natAbs ≤ H
  S : ∀ i j, (Q.S i j).natAbs ≤ H

theorem Bounded.mono {Q : State m n} {H K : ℕ} (hQ : Bounded Q H) (h : H ≤ K) :
    Bounded Q K :=
  ⟨fun i j => (hQ.U i j).trans h, fun i j => (hQ.Uinv i j).trans h,
    fun i j => (hQ.V i j).trans h, fun i j => (hQ.Vinv i j).trans h,
    fun i j => (hQ.S i j).trans h⟩

/-- Read the integer multiplier already stored in an addition instruction. -/
def coefficient : Op m n → ℤ
  | .row _ _ _ c => c
  | .col _ _ _ c => c

theorem colAdd_pow_bound (A : Matrix (Fin m) (Fin n) ℤ) (r s : Fin n)
    (c : ℤ) (a b : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ a)
    (hc : c.natAbs ≤ 2 ^ b) :
    ∀ i j, (colAdd A r s c i j).natAbs ≤ 2 ^ (a + b + 1) := by
  intro i j
  exact rowAdd_pow_bound A.transpose r s c a b (fun j i => hA i j) hc j i

/-- Both inverse updates pay the same multiplier bits as their forward maps. -/
theorem step_pow_bound (Q : State m n) (op : Op m n) (a b : ℕ)
    (hQ : Bounded Q (2 ^ a)) (hc : (coefficient op).natAbs ≤ 2 ^ b) :
    Bounded (step Q op) (2 ^ (a + b + 1)) := by
  have hle : 2 ^ a ≤ (2 : ℕ) ^ (a + b + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hwide := hQ.mono hle
  cases op with
  | row r s h c =>
      exact ⟨rowAdd_pow_bound Q.U r s c a b hQ.U hc,
        colAdd_pow_bound Q.Uinv s r (-c) a b hQ.Uinv (by simpa [coefficient] using hc),
        hwide.V, hwide.Vinv, rowAdd_pow_bound Q.S r s c a b hQ.S hc⟩
  | col r s h c =>
      exact ⟨hwide.U, hwide.Uinv, colAdd_pow_bound Q.V r s c a b hQ.V hc,
        rowAdd_pow_bound Q.Vinv s r (-c) a b hQ.Vinv (by simpa [coefficient] using hc),
        colAdd_pow_bound Q.S r s c a b hQ.S hc⟩

/-- Accumulate bit widths along a finite trace, with its actual list length. -/
theorem run_pow_bound (Q : State m n) (ops : List (Op m n)) (a b : ℕ)
    (hQ : Bounded Q (2 ^ a))
    (hc : ∀ op ∈ ops, (coefficient op).natAbs ≤ 2 ^ b) :
    Bounded (run Q ops) (2 ^ (a + ops.length * (b + 1))) := by
  induction ops generalizing Q a with
  | nil => simpa [run] using hQ
  | cons op ops ih =>
      have hi := ih (step Q op) (a + b + 1)
        (step_pow_bound Q op a b hQ (hc op (by simp)))
        (fun op hop => hc op (by simp [hop]))
      have heq : a + b + 1 + ops.length * (b + 1) =
          a + (ops.length + 1) * (b + 1) := by ring
      simpa only [run, List.length_cons, heq] using hi

/-- Every quotient in the actual Euclidean trace is bounded by the incoming
pair's common height; signed swaps use only unit multipliers. -/
theorem gcdTrace_coefficient_le (r s : Fin m) (h : r ≠ s) (a b : ℤ)
    (H : ℕ) (hH : 1 ≤ H) (ha : a.natAbs ≤ H) (hb : b.natAbs ≤ H) :
    ∀ op ∈ gcdTrace (n := n) r s h a b, (coefficient op).natAbs ≤ H := by
  rw [gcdTrace]
  split_ifs with hz
  · simp
  · intro op hop
    rcases List.mem_append.mp hop with hop | hop
    · simp only [pairStep, List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl | rfl
      · simpa [coefficient] using (Int.natAbs_tdiv_le_natAbs a b).trans ha
      all_goals simpa [coefficient] using hH
    · apply gcdTrace_coefficient_le r s h b (-(a.tmod b)) H hH hb _ op hop
      simpa only [Int.natAbs_neg, Int.natAbs_tmod] using (Nat.mod_le a.natAbs b.natAbs).trans ha
termination_by b.natAbs
decreasing_by exact remainder_descent a b hz

/-- Each prefix includes the temporary additions used to implement a signed
swap, rather than only the completed Euclidean division states. -/
theorem gcdTrace_prefix_pow_bound (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (a b : ℤ) (d c t : ℕ) (hQ : Bounded Q (2 ^ d))
    (ha : a.natAbs < 2 ^ c) (hb : b.natAbs < 2 ^ c) :
    Bounded (run Q ((gcdTrace r s h a b).take t))
      (2 ^ (d + 8 * c * (c + 1))) := by
  have hc := gcdTrace_coefficient_le (n := n) r s h a b (2 ^ c)
    (Nat.one_le_pow c 2 (by decide)) ha.le hb.le
  have hrun := run_pow_bound Q ((gcdTrace r s h a b).take t) d c hQ
    (fun op hop => hc op (List.mem_of_mem_take hop))
  have hlen : ((gcdTrace (n := n) r s h a b).take t).length ≤ 8 * c :=
    (List.length_take_le' t _).trans
      ((gcdTrace_length_le r s h a b).trans
        (Nat.mul_le_mul_left 8 (Nat.size_le.mpr hb)))
  exact hrun.mono (Nat.pow_le_pow_right (by decide)
    (Nat.add_le_add_left (Nat.mul_le_mul_right (c + 1) hlen) d))

theorem initial_pow_bound (A : Matrix (Fin m) (Fin n) ℤ) (d : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ d) : Bounded (initial A) (2 ^ d) := by
  have hi {k : ℕ} (i j : Fin k) :
      ((1 : Matrix (Fin k) (Fin k) ℤ) i j).natAbs ≤ 2 ^ d := by
    by_cases h : i = j
    · simpa [Matrix.one_apply, h] using Nat.one_le_pow d 2 (by decide)
    · simp [h]
  exact ⟨hi, hi, hi, hi, hA⟩

/-- A quadratic exponent in the complete dense matrix's source bit length. -/
def pivotWidth (s : ℕ) : ℕ := s + 8 * s * (s + 1)

/-- Every stored entry of every prefix state of one computed pair pivot is
bounded in the original matrix encoding, including signs and dimension costs. -/
theorem pivot_prefix_bound (A : Dense) (r s : Fin A.rows) (h : r ≠ s)
    (j : Fin A.cols) (t : ℕ) :
    Bounded (run (initial A.toMatrix)
      ((gcdTrace r s h (A.toMatrix r j) (A.toMatrix s j)).take t))
      (2 ^ pivotWidth (SmithEncoding.encode A).length) := by
  have hA : ∀ i j, (A.toMatrix i j).natAbs < 2 ^ (SmithEncoding.encode A).length :=
    fun i j => Nat.size_le.mp (SmithIsolationCount.entry_size_le_input_length A i j)
  exact gcdTrace_prefix_pow_bound _ r s h _ _ _ _ t
    (initial_pow_bound A.toMatrix _ (fun i j => (hA i j).le)) (hA r j) (hA s j)

theorem pivot_bound (A : Dense) (r s : Fin A.rows) (h : r ≠ s) (j : Fin A.cols) :
    Bounded (pivot (initial A.toMatrix) r s h j)
      (2 ^ pivotWidth (SmithEncoding.encode A).length) := by
  simpa only [List.take_length, pivot, initial] using
    pivot_prefix_bound A r s h j (gcdTrace (n := A.cols) r s h
      (A.toMatrix r j) (A.toMatrix s j)).length

private theorem pack_entry_le (A : Matrix (Fin m) (Fin n) ℤ) (H : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ H) (z : ℤ) (hz : z ∈ (pack A).val.entries) :
    z.natAbs ≤ H := by
  obtain ⟨k, hk⟩ := List.mem_ofFn.mp hz
  rw [← hk]
  exact hA _ _

/-- Transfer the five-matrix bound to every actual serialized integer field. -/
theorem Bounded.result_entry_bits {Q : State m n} {d : ℕ}
    (hQ : Bounded Q (2 ^ d)) :
    ∀ B ∈ [Q.result.U.val, Q.result.Uinv.val, Q.result.V.val,
      Q.result.Vinv.val, Q.result.S.val],
      ∀ z ∈ B.entries, (Computability.encodeNat z.natAbs).length ≤ d + 1 := by
  intro B hB z hz
  rw [LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size]
  have hbits (hz : z.natAbs ≤ 2 ^ d) : z.natAbs.size ≤ d + 1 := by
    simpa only [Nat.size_pow] using Nat.size_le_size hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl
  · exact hbits (pack_entry_le Q.U _ hQ.U z hz)
  · exact hbits (pack_entry_le Q.Uinv _ hQ.Uinv z hz)
  · exact hbits (pack_entry_le Q.V _ hQ.V z hz)
  · exact hbits (pack_entry_le Q.Vinv _ hQ.Vinv z hz)
  · exact hbits (pack_entry_le Q.S _ hQ.S z hz)

/-- The complete five-matrix output of this single pivot has polynomial length
in the actual dense input bits. This is serialization size, not its runtime. -/
theorem pivotDense_output_length_le (A : Dense) (r s : Fin A.rows) (h : r ≠ s)
    (j : Fin A.cols) :
    (SmithDecomposition.encode (pivotDense A r s h j)).length ≤
      2 * (5 * (SmithEncoding.encode A).length + 10 +
        2 * (SmithEncoding.encode A).length * (SmithEncoding.encode A).length *
          (2 * (pivotWidth (SmithEncoding.encode A).length + 1) + 2)) + 5 := by
  exact encode_length_le_of_input_bits A _ _ (pivot_bound A r s h j).result_entry_bits

/-- Transposition exchanges the forward maps and their inverse maps without
changing a common height bound. -/
theorem Bounded.transposeState {Q : State m n} {H : ℕ} (hQ : Bounded Q H) :
    Bounded (SmithReduction.transposeState Q) H :=
  ⟨fun i j => hQ.V j i, fun i j => hQ.Vinv j i,
    fun i j => hQ.U j i, fun i j => hQ.Uinv j i, fun i j => hQ.S j i⟩

/-- The controller's divisible-entry shortcut also respects the local bound. -/
theorem reduceRows_pow_bound (Q : State m n) (r s : Fin m) (h : r ≠ s)
    (j : Fin n) (d c : ℕ) (hc : 0 < c) (hQ : Bounded Q (2 ^ d))
    (ha : (Q.S r j).natAbs < 2 ^ c) (hb : (Q.S s j).natAbs < 2 ^ c) :
    Bounded (SmithReduction.reduceRows Q r s h j) (2 ^ (d + 8 * c * (c + 1))) := by
  unfold SmithReduction.reduceRows
  split_ifs
  · have hstep := step_pow_bound Q (.row s r h.symm (-(Q.S s j).tdiv (Q.S r j)))
      d c hQ (by
        simpa [coefficient] using (Int.natAbs_tdiv_le_natAbs (Q.S s j) (Q.S r j)).trans hb.le)
    apply hstep.mono
    apply Nat.pow_le_pow_right (by decide)
    have hmul : c + 1 ≤ 8 * c * (c + 1) := by nlinarith
    omega
  · simpa only [List.take_length, pivot] using
      gcdTrace_prefix_pow_bound Q r s h _ _ d c
        (gcdTrace (n := n) r s h (Q.S r j) (Q.S s j)).length hQ ha hb

/-- One total entry reduction, including all missing-index no-op branches. -/
theorem reduceAtColumn_pow_bound (Q : State m n) (k target d c : ℕ)
    (hc : 0 < c) (hQ : Bounded Q (2 ^ d))
    (hS : ∀ i j, (Q.S i j).natAbs < 2 ^ c) :
    Bounded (SmithReduction.reduceAtColumn Q k target) (2 ^ (d + 8 * c * (c + 1))) := by
  unfold SmithReduction.reduceAtColumn
  split_ifs
  · exact reduceRows_pow_bound Q _ _ _ _ d c hc hQ (hS _ _) (hS _ _)
  all_goals exact hQ.mono (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))

theorem reduceAtRow_pow_bound (Q : State m n) (k target d c : ℕ)
    (hc : 0 < c) (hQ : Bounded Q (2 ^ d))
    (hS : ∀ i j, (Q.S i j).natAbs < 2 ^ c) :
    Bounded (SmithReduction.reduceAtRow Q k target) (2 ^ (d + 8 * c * (c + 1))) :=
  (reduceAtColumn_pow_bound (SmithReduction.transposeState Q) k target d c hc
    hQ.transposeState (fun i j => hS j i)).transposeState

/-- An unconditional polynomial size bound for the existing stored single-entry
reducer in either orientation. Rectangular, singular, empty and missing-index
inputs are included; this does not iterate over a sweep or a decomposition. -/
theorem reduceDense_output_length_le (A : Dense) (acrossRow : Bool) (k target : ℕ) :
    (SmithDecomposition.encode (SmithReduction.reduceDense A acrossRow k target)).length ≤
      2 * (5 * (SmithEncoding.encode A).length + 10 +
        2 * (SmithEncoding.encode A).length * (SmithEncoding.encode A).length *
          (2 * (pivotWidth (SmithEncoding.encode A).length + 1) + 2)) + 5 := by
  have hS : ∀ i j, (A.toMatrix i j).natAbs < 2 ^ (SmithEncoding.encode A).length :=
    fun i j => Nat.size_le.mp (SmithIsolationCount.entry_size_le_input_length A i j)
  have hp : 0 < (SmithEncoding.encode A).length := by
    simp only [SmithEncoding.encode, List.length_append, List.length_replicate,
      List.length_cons]
    omega
  have hQ := initial_pow_bound A.toMatrix _ (fun i j => (hS i j).le)
  have hb : Bounded (if acrossRow then
      SmithReduction.reduceAtRow (initial A.toMatrix) k target
    else SmithReduction.reduceAtColumn (initial A.toMatrix) k target)
      (2 ^ pivotWidth (SmithEncoding.encode A).length) := by
    split
    · exact reduceAtRow_pow_bound _ k target _ _ hp hQ hS
    · exact reduceAtColumn_pow_bound _ k target _ _ hp hQ hS
  exact encode_length_le_of_input_bits A _ _ hb.result_entry_bits

#print axioms remainder_pair_halves
#print axioms gcdTrace_length_le
#print axioms Bounded
#print axioms Bounded.mono
#print axioms coefficient
#print axioms colAdd_pow_bound
#print axioms step_pow_bound
#print axioms run_pow_bound
#print axioms gcdTrace_coefficient_le
#print axioms gcdTrace_prefix_pow_bound
#print axioms initial_pow_bound
#print axioms pivotWidth
#print axioms pivot_prefix_bound
#print axioms pivot_bound
#print axioms Bounded.result_entry_bits
#print axioms pivotDense_output_length_le
#print axioms Bounded.transposeState
#print axioms reduceRows_pow_bound
#print axioms reduceAtColumn_pow_bound
#print axioms reduceAtRow_pow_bound
#print axioms reduceDense_output_length_le

end PhdThesisLean.SmithPivotBounds
