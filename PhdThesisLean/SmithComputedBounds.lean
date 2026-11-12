import PhdThesisLean.SmithTraceCount

/-!
# Growth reduction for the computed diagonalizer

For this controller, a common width of the transformed matrix bounds every
selected quotient. Together with the existing conditional addition count this
bounds all five matrices at every addition prefix, and the complete output.
The common transformed width is still a hypothesis, not a global polynomial
growth theorem or an encoded-machine runtime bound. Arbitrary valid traces do
not satisfy the quotient-selection premise used here.
-/

namespace PhdThesisLean.SmithComputedBounds

open SmithTrace SmithPivotBounds SmithSweepBounds SmithTraceCount
  SmithReduction SmithSweep SmithIsolation SmithDiagonalization
  SmithEncoding SmithDecomposition

variable {m n : ℕ}

/-- The selected-column invariant controls all quotients in one full sweep. -/
theorem columnTrace_coefficient_le (Q : State m n) (k b : ℕ) (hb : 0 < b)
    (h : ∀ i j, (Q.S i j).natAbs < 2 ^ b) :
    ∀ op ∈ columnTrace Q k, (coefficient op).natAbs ≤ 2 ^ b := by
  unfold columnTrace
  split_ifs
  · exact (sweepRowsTrace_bounds _ _ _ _ b hb (fun i => h i _)).2
  all_goals simp

/-- Charge the second sweep to its actual midpoint, including zero pivots. -/
theorem crossTrace_coefficient_le (Q : State m n) (k b : ℕ) (hb : 0 < b)
    (h : PrefixWidth Q (crossTrace Q k) b) :
    ∀ op ∈ crossTrace Q k, (coefficient op).natAbs ≤ 2 ^ b := by
  change PrefixWidth Q (columnTrace Q k ++
    (columnTrace (transposeState (clearActiveColumn Q k)) k).map transposeOp) b at h
  have hstart := columnTrace_coefficient_le Q k b hb h.left.initial
  have hmid : ∀ i j, ((clearActiveColumn Q k).S i j).natAbs < 2 ^ b := by
    simpa only [columnTrace_run] using h.right.initial
  have hnext := columnTrace_coefficient_le (transposeState (clearActiveColumn Q k))
    k b hb (fun i j => hmid j i)
  intro op hop
  rcases List.mem_append.mp hop with hop | hop
  · exact hstart op hop
  · obtain ⟨op', hop', rfl⟩ := List.mem_map.mp hop
    have hc := hnext op' hop'
    cases op' <;> exact hc

theorem crossesTrace_coefficient_le (Q : State m n) (k count b : ℕ) (hb : 0 < b)
    (h : PrefixWidth Q (crossesTrace Q k count) b) :
    ∀ op ∈ crossesTrace Q k count, (coefficient op).natAbs ≤ 2 ^ b := by
  induction count generalizing Q with
  | zero => simp [crossesTrace]
  | succ count ih =>
      change PrefixWidth Q (crossTrace Q k ++ crossesTrace (cross Q k) k count) b at h
      have hfirst := crossTrace_coefficient_le Q k b hb h.left
      have htail : PrefixWidth (cross Q k) (crossesTrace (cross Q k) k count) b := by
        simpa only [crossTrace_run] using h.right
      intro op hop
      exact (List.mem_append.mp hop).elim (hfirst op) (ih (cross Q k) htail op)

theorem isolateTrace_coefficient_le (Q : State m n) (k b : ℕ) (hb : 0 < b)
    (h : PrefixWidth Q (isolateTrace Q k) b) :
    ∀ op ∈ isolateTrace Q k, (coefficient op).natAbs ≤ 2 ^ b :=
  crossesTrace_coefficient_le Q k _ b hb h

theorem finishTrace_coefficient_le (Q : State m n) (k b : ℕ) (hb : 0 < b)
    (h : PrefixWidth Q (finishTrace Q k) b) :
    ∀ op ∈ finishTrace Q k, (coefficient op).natAbs ≤ 2 ^ b := by
  rw [finishTrace] at h ⊢
  split_ifs at h ⊢ with hk
  · have hfirst := isolateTrace_coefficient_le Q k b hb h.left
    have htail : PrefixWidth (isolate Q k) (finishTrace (isolate Q k) (k + 1)) b := by
      simpa only [isolateTrace_run] using h.right
    have hrest := finishTrace_coefficient_le (isolate Q k) (k + 1) b hb htail
    intro op hop
    exact (List.mem_append.mp hop).elim (hfirst op) (hrest op)
  · simp
termination_by min m n - k
decreasing_by omega

/-- Applies to this computed trace, not to an arbitrary equivalent trace. -/
theorem decomposeTrace_coefficient_le (A : Dense) (b : ℕ) (hb : 0 < b)
    (h : PrefixWidth (initial A.toMatrix) (decomposeTrace A) b) :
    ∀ op ∈ decomposeTrace A, (coefficient op).natAbs ≤ 2 ^ b :=
  finishTrace_coefficient_le _ 0 b hb h

/-- Polynomial in source length AND the still-unproved transformed width. -/
def computedWidth (s b : ℕ) : ℕ := s + 8 * s * s * b * (b + 1) * (b + 1)

/-- The existing semantic count and actual quotient bounds control both
forward maps and both inverses, including every unfinished signed swap. -/
theorem decomposeTrace_prefix_bound (A : Dense) (b : ℕ) (hb : 0 < b)
    (h : PrefixWidth (initial A.toMatrix) (decomposeTrace A) b) (t : ℕ) :
    Bounded (run (initial A.toMatrix) ((decomposeTrace A).take t))
      (2 ^ computedWidth (SmithEncoding.encode A).length b) := by
  have hA := initial_pow_bound A.toMatrix (SmithEncoding.encode A).length
    (fun i j => (Nat.size_le.mp
      (SmithIsolationCount.entry_size_le_input_length A i j)).le)
  have hc := decomposeTrace_coefficient_le A b hb h
  have hr := run_pow_bound _ ((decomposeTrace A).take t) _ b hA
    (fun op hop => hc op (List.mem_of_mem_take hop))
  have hlen := (List.length_take_le' t (decomposeTrace A)).trans
    (decomposeTrace_length_le_of_width A b hb h)
  exact hr.mono (Nat.pow_le_pow_right (by decide)
    (Nat.add_le_add_left (Nat.mul_le_mul_right (b + 1) hlen) _))

/-- Full five-matrix output size in the original codec, conditional only on
the transformed prefix width; includes inverse matrices and empty dimensions. -/
theorem decompose_output_length_le (A : Dense) (b : ℕ) (hb : 0 < b)
    (h : PrefixWidth (initial A.toMatrix) (decomposeTrace A) b) :
    let s := (SmithEncoding.encode A).length
    (SmithDecomposition.encode (decompose A)).length ≤
      2 * (5 * s + 10 + 2 * s * s * (2 * (computedWidth s b + 1) + 2)) + 5 := by
  have hout := decomposeTrace_prefix_bound A b hb h (decomposeTrace A).length
  rw [List.take_length] at hout
  have hbits := hout.result_entry_bits
  rw [decomposeTrace_result] at hbits
  exact encode_length_le_of_input_bits A _ _ hbits

/-- Two equivalent, still-open growth obligations for the actual controller.
The extra bit in the transformed formulation ensures a positive width. Neither
side asserts machine time, and this equivalence supplies neither witness. -/
theorem polynomial_growth_iff :
    (∃ P : Polynomial ℕ, ∀ A : Dense,
      PrefixWidth (initial A.toMatrix) (decomposeTrace A)
        (P.eval (SmithEncoding.encode A).length + 1)) ↔
    (∃ P : Polynomial ℕ, ∀ (A : Dense) (t : ℕ),
      let Q := run (initial A.toMatrix) ((decomposeTrace A).take t)
      (∀ i j, (Q.U i j).natAbs ≤ 2 ^ P.eval (SmithEncoding.encode A).length) ∧
      (∀ i j, (Q.V i j).natAbs ≤ 2 ^ P.eval (SmithEncoding.encode A).length)) := by
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨Polynomial.X + 8 * Polynomial.X * Polynomial.X * (P + 1) *
      (P + 2) * (P + 2), ?_⟩
    intro A t
    have hw := decomposeTrace_prefix_bound A _ (by omega) (hP A) t
    have he : (Polynomial.X + 8 * Polynomial.X * Polynomial.X * (P + 1) *
        (P + 2) * (P + 2)).eval (SmithEncoding.encode A).length =
        computedWidth (SmithEncoding.encode A).length
          (P.eval (SmithEncoding.encode A).length + 1) := by
      simp [Polynomial.eval_add, Polynomial.eval_mul, computedWidth,
        Nat.add_assoc]
    simp only [he]
    exact ⟨hw.U, hw.V⟩
  · rintro ⟨P, hP⟩
    refine ⟨(Polynomial.X + 2) * (P + Polynomial.X + 1), ?_⟩
    intro A t i j
    obtain ⟨hU, hV⟩ := hP A t
    have hw := SmithForwardBounds.trace_prefix_bound A (decomposeTrace A) t _ hU hV
    have he : ((Polynomial.X + 2) * (P + Polynomial.X + 1)).eval
        (SmithEncoding.encode A).length =
        SmithForwardBounds.stateWidth (SmithEncoding.encode A).length
          (P.eval (SmithEncoding.encode A).length) := by
      simp [Polynomial.eval_add, Polynomial.eval_mul, SmithForwardBounds.stateWidth]
    change _ < 2 ^ (((Polynomial.X + 2) * (P + Polynomial.X + 1)).eval
      (SmithEncoding.encode A).length + 1)
    rw [he, pow_succ]
    have hp : 0 < (2 : ℕ) ^ SmithForwardBounds.stateWidth
        (SmithEncoding.encode A).length (P.eval (SmithEncoding.encode A).length) := by
      positivity
    have hs := hw.S i j
    omega

-- Universal specializations exercise both empty orientations: the transformed
-- bound is vacuous, but the forward maps and inverses still contain identities.
example (t : ℕ) :
    Bounded (run (initial (⟨0, 3, [], rfl⟩ : Dense).toMatrix)
      ((decomposeTrace (⟨0, 3, [], rfl⟩ : Dense)).take t))
      (2 ^ computedWidth (SmithEncoding.encode (⟨0, 3, [], rfl⟩ : Dense)).length 1) :=
  decomposeTrace_prefix_bound _ 1 (by decide) (by intro t i; exact Fin.elim0 i) t

example (t : ℕ) :
    Bounded (run (initial (⟨3, 0, [], rfl⟩ : Dense).toMatrix)
      ((decomposeTrace (⟨3, 0, [], rfl⟩ : Dense)).take t))
      (2 ^ computedWidth (SmithEncoding.encode (⟨3, 0, [], rfl⟩ : Dense)).length 1) :=
  decomposeTrace_prefix_bound _ 1 (by decide) (by intro t i j; exact Fin.elim0 j) t

#print axioms columnTrace_coefficient_le
#print axioms crossTrace_coefficient_le
#print axioms crossesTrace_coefficient_le
#print axioms isolateTrace_coefficient_le
#print axioms finishTrace_coefficient_le
#print axioms decomposeTrace_coefficient_le
#print axioms computedWidth
#print axioms decomposeTrace_prefix_bound
#print axioms decompose_output_length_le
#print axioms polynomial_growth_iff

end PhdThesisLean.SmithComputedBounds
