import PhdThesisLean.AllDifferent

namespace PhdThesisLean.SudokuSpecialCase

open scoped BigOperators
open PhdThesisLean.FiniteDomainCompiler PhdThesisLean.AllDifferent

/-!
# Sudoku completion as a special case of the all-different theorem

This module formalises thesis Corollary `cor:sudoku-special-case` and the
auxiliary Corollary `cor:sudoku-differences` from
`sudoku-via-padic-regression/body.tex` (the "Positive pinning", "Negative
signed residual terms" and "Minimal and expanded residual objectives"
subsections), by instantiating `PhdThesisLean.AllDifferent` on the Sudoku
peer graph.

## Construction

* Cells are `Fin 81`, numbered `9 * row + col`; `row`, `col` and `box` are the
  usual coordinates.  `Peer i j` holds when `i ≠ j` share a row, a column or a
  `3 × 3` box (the thesis's set `𝒫`, read as a symmetric relation).
* `PeerEdge` is the *deduplicated* peer graph: pairs `(i, j)` with `i < j` and
  `Peer i j`, so each unordered peer pair is one edge.  Every edge has weight
  `1` (`edgeWeight`), matching the thesis's normalisation of the pairwise
  coefficient.
* `digitSet p = {1, …, 9} ⊆ ℚ_[p]`; the domain `sudokuDomain p C g i` is the
  singleton `{g i}` on clue cells `i ∈ C` and `digitSet p` otherwise (the
  thesis's `D_i`).  The clue digits are required to lie in `{1, …, 9}`
  (`ClueDigits C g`), as the thesis assumes `g_i ∈ D`.
* `sudokuLoss p C g α` is `allDifferentLoss` for these data;
  `sudokuLoss_eq` shows it is literally the displayed minimal objective
  `eq:objective-minimal` (pinning weight `α` on both the digit wells and the
  clue pins, minus the sum of the peer-difference norms).

## Results

* `digit_difference_norm` is `cor:sudoku-differences`: for `p > 9` and
  digits `a, b ∈ {1, …, 9}`, `‖a - b‖ = 0` if `a = b` and `1` otherwise.
* `card_peers` / `degree_eq_twenty`: every cell has exactly `20` peers, so the
  incident edge weight at every cell is `20`.  The peer count is established
  by kernel evaluation (`decide +kernel`) of the `81 × 81` decidable peer
  relation; the identification of the peer count with the number of incident
  deduplicated edges is an explicit bijection (`card_incidentEdges`).
* `sudoku_special_case` is `cor:sudoku-special-case`: for `p > 9` and
  `α > 20`, the objective has a global minimiser; the global minimisers are
  exactly the clue-respecting digit assignments minimising the peer-conflict
  count (`MinimizesConflicts`, spelled out in `inDomain_iff` and
  `minimizesConflicts_iff`); and when the puzzle is satisfiable the global
  minimisers are exactly the valid completions (`ValidCompletion`, which
  `validCompletion_iff_isProper` identifies with `IsProper`).
* `unit_complete` and its instances `row_complete`, `col_complete`,
  `box_complete` record the proof's pigeonhole remark: in a valid completion
  every row, column and box contains every digit exactly once.

## Correspondence notes

* The thesis works in `ℤ_p^{81}`; here the parameter ranges over all of
  `ℚ_[p]^{81}`, which is stronger (the theorem excludes every non-digit point,
  including those outside `ℤ_p`).
* The thesis states the result for the minimal objective with a single weight
  `α > 20`; this is exactly `sudokuLoss`.  The expanded objective
  `eq:objective` is not formalised here.
* The thesis's count of `810` negative observations is also checked
  (`card_peerEdge`).
-/

/-! ### The 81-cell grid and its peer relation -/

/-- Row of a cell; cells are numbered `9 * row + col`. -/
def row (i : Fin 81) : ℕ := i.val / 9

/-- Column of a cell. -/
def col (i : Fin 81) : ℕ := i.val % 9

/-- The `3 × 3` box of a cell, numbered `3 * (row / 3) + col / 3`. -/
def box (i : Fin 81) : ℕ := 3 * (row i / 3) + col i / 3

/-- Two distinct cells are peers when they share a row, a column or a box. -/
def Peer (i j : Fin 81) : Prop :=
  i ≠ j ∧ (row i = row j ∨ col i = col j ∨ box i = box j)

instance instDecidablePeer (i j : Fin 81) : Decidable (Peer i j) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Peer.ne {i j : Fin 81} (h : Peer i j) : i ≠ j := h.1

theorem Peer.symm {i j : Fin 81} (h : Peer i j) : Peer j i := by
  obtain ⟨hne, hunit⟩ := h
  refine ⟨hne.symm, ?_⟩
  rcases hunit with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr h.symm)

theorem not_peer_self (i : Fin 81) : ¬ Peer i i := fun h => h.1 rfl

/-- The set of peers of a cell. -/
def peers (i : Fin 81) : Finset (Fin 81) := Finset.univ.filter (Peer i)

theorem mem_peers {i j : Fin 81} : j ∈ peers i ↔ Peer i j := by
  simp [peers]

/-- Every cell has exactly `20` peers: `8` in its row, `8` in its column and
`4` further cells in its box.  Checked by kernel evaluation of the decidable
peer relation over all `81 × 81` cell pairs. -/
theorem card_peers : ∀ i : Fin 81, (peers i).card = 20 := by
  decide +kernel

/-! ### The deduplicated peer graph -/

/-- An edge of the deduplicated Sudoku peer graph: a pair `(i, j)` of peers
with `i < j`.  Each unordered peer pair appears exactly once. -/
def PeerEdge : Type := {e : Fin 81 × Fin 81 // e.1 < e.2 ∧ Peer e.1 e.2}

/-- The finite enumeration of peer edges, as a subtype of `Fin 81 × Fin 81`.

It is wrapped in an irreducible definition on purpose: otherwise the
elaborator's `whnf` (triggered, e.g., by hypotheses of type
`e ∈ Finset.univ.filter _`) tries to evaluate the `81 × 81` candidate list and
exceeds the recursion limit.  The kernel ignores reducibility, so
`decide +kernel` still computes with this instance (see `card_peerEdge`). -/
@[irreducible] def peerEdgeFintype : Fintype PeerEdge :=
  inferInstanceAs (Fintype {e : Fin 81 × Fin 81 // e.1 < e.2 ∧ Peer e.1 e.2})

instance : Fintype PeerEdge := peerEdgeFintype

instance : DecidableEq PeerEdge :=
  inferInstanceAs (DecidableEq {e : Fin 81 × Fin 81 // e.1 < e.2 ∧ Peer e.1 e.2})

/-- Smaller endpoint of an edge. -/
def left (e : PeerEdge) : Fin 81 := e.1.1

/-- Larger endpoint of an edge. -/
def right (e : PeerEdge) : Fin 81 := e.1.2

/-- All peer edges carry weight `1`. -/
def edgeWeight (_ : PeerEdge) : ℝ := 1

theorem left_lt_right (e : PeerEdge) : left e < right e := e.2.1

theorem left_ne_right (e : PeerEdge) : left e ≠ right e := ne_of_lt e.2.1

theorem peer_left_right (e : PeerEdge) : Peer (left e) (right e) := e.2.2

theorem edgeWeight_pos (e : PeerEdge) : 0 < edgeWeight e := one_pos

theorem edgeWeight_nonneg (e : PeerEdge) : 0 ≤ edgeWeight e := zero_le_one

/-- The thesis's `810` distinct peer pairs. -/
theorem card_peerEdge : Fintype.card PeerEdge = 810 := by
  decide +kernel

/-- The endpoint of an edge incident to `i` other than `i`. -/
def other (i : Fin 81) (e : PeerEdge) : Fin 81 :=
  if i = left e then right e else left e

/-- The edge joining a cell to one of its peers. -/
def edgeOf (i j : Fin 81) (h : Peer i j) : PeerEdge :=
  if hij : i < j then ⟨(i, j), hij, h⟩
  else ⟨(j, i), lt_of_le_of_ne (not_lt.mp hij) h.ne.symm, h.symm⟩

theorem edgeOf_endpoints (i j : Fin 81) (h : Peer i j) :
    (left (edgeOf i j h) = i ∧ right (edgeOf i j h) = j) ∨
      (left (edgeOf i j h) = j ∧ right (edgeOf i j h) = i) := by
  unfold edgeOf
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem incident_edgeOf (i j : Fin 81) (h : Peer i j) :
    i = left (edgeOf i j h) ∨ i = right (edgeOf i j h) := by
  rcases edgeOf_endpoints i j h with ⟨hl, _⟩ | ⟨_, hr⟩
  · exact Or.inl hl.symm
  · exact Or.inr hr.symm

theorem other_edgeOf (i j : Fin 81) (h : Peer i j) :
    other i (edgeOf i j h) = j := by
  have hne : i ≠ j := h.ne
  rcases edgeOf_endpoints i j h with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rw [other, if_pos hl.symm, hr]
  · rw [other, if_neg (by rw [hl]; exact hne), hl]

theorem peer_other {i : Fin 81} {e : PeerEdge} (h : i = left e ∨ i = right e) :
    Peer i (other i e) := by
  unfold other
  split
  · rename_i hil
    rw [hil]
    exact peer_left_right e
  · rename_i hil
    rw [h.resolve_left hil]
    exact (peer_left_right e).symm

/-- The deduplicated edges incident to a cell. -/
def incidentEdges (i : Fin 81) : Finset PeerEdge :=
  Finset.univ.filter (fun e => i = left e ∨ i = right e)

theorem mem_incidentEdges {i : Fin 81} {e : PeerEdge} :
    e ∈ incidentEdges i ↔ i = left e ∨ i = right e := by
  simp [incidentEdges]

/-- Incident deduplicated edges correspond bijectively to peers, via the
other endpoint. -/
theorem card_incidentEdges (i : Fin 81) :
    (incidentEdges i).card = (peers i).card := by
  apply Finset.card_bij (fun e _ => other i e)
  · intro e he
    rw [mem_incidentEdges] at he
    exact mem_peers.mpr (peer_other he)
  · intro e₁ he₁ e₂ he₂ heq
    rw [mem_incidentEdges] at he₁ he₂
    have hne₁ : i = right e₁ → i ≠ left e₁ :=
      fun h₁ h₂ => left_ne_right e₁ (h₂.symm.trans h₁)
    have hne₂ : i = right e₂ → i ≠ left e₂ :=
      fun h₁ h₂ => left_ne_right e₂ (h₂.symm.trans h₁)
    rcases he₁ with h₁ | h₁ <;> rcases he₂ with h₂ | h₂
    · -- both have `i` on the left
      rw [other, if_pos h₁, other, if_pos h₂] at heq
      exact Subtype.ext (Prod.ext (h₁.symm.trans h₂) heq)
    · -- `i = left e₁`, `i = right e₂`: impossible by ordering
      rw [other, if_pos h₁, other, if_neg (hne₂ h₂)] at heq
      exfalso
      have h3 : left e₁ < right e₁ := left_lt_right e₁
      have h4 : left e₂ < right e₂ := left_lt_right e₂
      rw [← h₁, heq] at h3
      rw [← h₂] at h4
      exact lt_asymm h3 h4
    · -- `i = right e₁`, `i = left e₂`: impossible by ordering
      rw [other, if_neg (hne₁ h₁), other, if_pos h₂] at heq
      exfalso
      have h3 : left e₁ < right e₁ := left_lt_right e₁
      have h4 : left e₂ < right e₂ := left_lt_right e₂
      rw [heq, ← h₁] at h3
      rw [← h₂] at h4
      exact lt_asymm h3 h4
    · -- both have `i` on the right
      rw [other, if_neg (hne₁ h₁), other, if_neg (hne₂ h₂)] at heq
      exact Subtype.ext (Prod.ext heq (h₁.symm.trans h₂))
  · intro j hj
    have hpeer : Peer i j := mem_peers.mp hj
    have hmem : edgeOf i j hpeer ∈ incidentEdges i :=
      mem_incidentEdges.mpr (incident_edgeOf i j hpeer)
    refine ⟨edgeOf i j hpeer, hmem, ?_⟩
    exact other_edgeOf i j hpeer

theorem incidentEdgeWeight_eq_card (i : Fin 81) :
    incidentEdgeWeight left right edgeWeight i = ((incidentEdges i).card : ℝ) := by
  classical
  rw [incidentEdgeWeight, incidentEdges, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : i = left e ∨ i = right e <;> simp [h, edgeWeight]

/-- In the deduplicated peer graph every cell has degree `20`. -/
theorem degree_eq_twenty (i : Fin 81) :
    incidentEdgeWeight left right edgeWeight i = 20 := by
  rw [incidentEdgeWeight_eq_card, card_incidentEdges, card_peers]
  norm_num

/-! ### Digits, clues and domains -/

/-- The digit set `{1, …, 9}` inside `ℚ_[p]`. -/
def digitSet (p : ℕ) [Fact p.Prime] : Finset ℚ_[p] :=
  (Finset.Icc (1 : ℕ) 9).map Nat.castEmbedding

theorem mem_digitSet {p : ℕ} [Fact p.Prime] {a : ℚ_[p]} :
    a ∈ digitSet p ↔ ∃ k ∈ Finset.Icc (1 : ℕ) 9, (k : ℚ_[p]) = a := by
  rw [digitSet, Finset.mem_map]
  simp only [Nat.castEmbedding_apply]

theorem natCast_mem_digitSet {p : ℕ} [Fact p.Prime] {k : ℕ}
    (hk : k ∈ Finset.Icc (1 : ℕ) 9) : (k : ℚ_[p]) ∈ digitSet p :=
  mem_digitSet.mpr ⟨k, hk, rfl⟩

theorem digitSet_nonempty (p : ℕ) [Fact p.Prime] : (digitSet p).Nonempty :=
  ⟨((1 : ℕ) : ℚ_[p]), natCast_mem_digitSet (by simp)⟩

theorem card_digitSet (p : ℕ) [Fact p.Prime] : (digitSet p).card = 9 := by
  rw [digitSet, Finset.card_map]
  simp

theorem unaryCost_digitSet {p : ℕ} [Fact p.Prime] (t : ℚ_[p]) :
    unaryCost (digitSet p) t = ∑ k ∈ Finset.Icc (1 : ℕ) 9, ‖t - (k : ℚ_[p])‖ := by
  rw [unaryCost, digitSet, Finset.sum_map]
  simp only [Nat.castEmbedding_apply]

/-- The clue digits lie in `{1, …, 9}`. -/
def ClueDigits (C : Finset (Fin 81)) (g : Fin 81 → ℕ) : Prop :=
  ∀ i ∈ C, g i ∈ Finset.Icc (1 : ℕ) 9

/-- The thesis's domains `D_i`: the clue digit on clue cells, `{1, …, 9}`
elsewhere. -/
def sudokuDomain (p : ℕ) [Fact p.Prime] (C : Finset (Fin 81)) (g : Fin 81 → ℕ)
    (i : Fin 81) : Finset ℚ_[p] :=
  if i ∈ C then {(g i : ℚ_[p])} else digitSet p

theorem sudokuDomain_of_mem {p : ℕ} [Fact p.Prime] {C : Finset (Fin 81)}
    {g : Fin 81 → ℕ} {i : Fin 81} (hi : i ∈ C) :
    sudokuDomain p C g i = {(g i : ℚ_[p])} := by
  rw [sudokuDomain, if_pos hi]

theorem sudokuDomain_of_not_mem {p : ℕ} [Fact p.Prime] {C : Finset (Fin 81)}
    {g : Fin 81 → ℕ} {i : Fin 81} (hi : i ∉ C) :
    sudokuDomain p C g i = digitSet p := by
  rw [sudokuDomain, if_neg hi]

theorem sudokuDomain_nonempty (p : ℕ) [Fact p.Prime] (C : Finset (Fin 81))
    (g : Fin 81 → ℕ) (i : Fin 81) : (sudokuDomain p C g i).Nonempty := by
  rw [sudokuDomain]
  split
  · exact Finset.singleton_nonempty _
  · exact digitSet_nonempty p

theorem sudokuDomain_subset_digitSet {p : ℕ} [Fact p.Prime] {C : Finset (Fin 81)}
    {g : Fin 81 → ℕ} (hg : ClueDigits C g) (i : Fin 81) :
    sudokuDomain p C g i ⊆ digitSet p := by
  rw [sudokuDomain]
  split
  · rename_i hi
    intro a ha
    rw [Finset.mem_singleton] at ha
    rw [ha]
    exact natCast_mem_digitSet (hg i hi)
  · exact subset_rfl

/-! ### Corollary `cor:sudoku-differences` -/

theorem norm_natCast_eq_one_of_pos_of_lt {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
    (h0 : 0 < n) (hn : n < p) : ‖(n : ℚ_[p])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  have := Nat.eq_zero_of_dvd_of_lt hdvd hn
  omega

/-- Thesis Corollary `cor:sudoku-differences`: for `p > 9` and digits
`a, b ∈ {1, …, 9}`, `‖a - b‖_p` is `0` if `a = b` and `1` otherwise. -/
theorem digit_difference_norm {p : ℕ} [Fact p.Prime] (hp : 9 < p) {a b : ℕ}
    (ha : a ∈ Finset.Icc (1 : ℕ) 9) (hb : b ∈ Finset.Icc (1 : ℕ) 9) :
    ‖(a : ℚ_[p]) - (b : ℚ_[p])‖ = if a = b then 0 else 1 := by
  rw [Finset.mem_Icc] at ha hb
  split
  · rename_i hab
    rw [hab, sub_self, norm_zero]
  · rename_i hab
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · rw [norm_sub_rev, ← Nat.cast_sub hlt.le]
      exact norm_natCast_eq_one_of_pos_of_lt (by omega) (by omega)
    · rw [← Nat.cast_sub hgt.le]
      exact norm_natCast_eq_one_of_pos_of_lt (by omega) (by omega)

theorem digitSet_unitSeparated {p : ℕ} [Fact p.Prime] (hp : 9 < p) :
    UnitSeparated (digitSet p) := by
  intro a ha b hb hab
  obtain ⟨k, hk, rfl⟩ := mem_digitSet.mp ha
  obtain ⟨l, hl, rfl⟩ := mem_digitSet.mp hb
  rw [digit_difference_norm hp hk hl, if_neg]
  rintro rfl
  exact hab rfl

theorem sudokuDomain_globallyUnitSeparated {p : ℕ} [Fact p.Prime] (hp : 9 < p)
    {C : Finset (Fin 81)} {g : Fin 81 → ℕ} (hg : ClueDigits C g) :
    GloballyUnitSeparated (sudokuDomain p C g) := by
  intro i a ha j b hb hab
  exact digitSet_unitSeparated hp a (sudokuDomain_subset_digitSet hg i ha)
    b (sudokuDomain_subset_digitSet hg j hb) hab

/-! ### The minimal Sudoku objective `eq:objective-minimal` -/

/-- The minimal Sudoku objective: `allDifferentLoss` for the Sudoku domains,
pinning weight `α`, and the unit-weight deduplicated peer graph. -/
noncomputable def sudokuLoss (p : ℕ) [Fact p.Prime] (C : Finset (Fin 81))
    (g : Fin 81 → ℕ) (α : ℝ) (x : Parameter p 81) : ℝ :=
  allDifferentLoss (sudokuDomain p C g) α left right edgeWeight x

/-- `sudokuLoss` is literally the thesis's displayed objective
`eq:objective-minimal`. -/
theorem sudokuLoss_eq {p : ℕ} [Fact p.Prime] (C : Finset (Fin 81))
    (g : Fin 81 → ℕ) (α : ℝ) (x : Parameter p 81) :
    sudokuLoss p C g α x =
      α * ∑ i ∈ Cᶜ, ∑ k ∈ Finset.Icc (1 : ℕ) 9, ‖x i - (k : ℚ_[p])‖ +
        α * ∑ i ∈ C, ‖x i - (g i : ℚ_[p])‖ -
        ∑ e, ‖x (left e) - x (right e)‖ := by
  have hC : ∀ i ∈ C,
      α * unaryCost (sudokuDomain p C g i) (x i) = α * ‖x i - (g i : ℚ_[p])‖ := by
    intro i hi
    rw [sudokuDomain_of_mem hi, unaryCost, Finset.sum_singleton]
  have hCc : ∀ i ∈ Cᶜ,
      α * unaryCost (sudokuDomain p C g i) (x i) =
        α * ∑ k ∈ Finset.Icc (1 : ℕ) 9, ‖x i - (k : ℚ_[p])‖ := by
    intro i hi
    rw [Finset.mem_compl] at hi
    rw [sudokuDomain_of_not_mem hi, unaryCost_digitSet]
  have hpin : pinningLoss (sudokuDomain p C g) (fun _ => α) x =
      α * ∑ i ∈ C, ‖x i - (g i : ℚ_[p])‖ +
        α * ∑ i ∈ Cᶜ, ∑ k ∈ Finset.Icc (1 : ℕ) 9, ‖x i - (k : ℚ_[p])‖ := by
    rw [pinningLoss, ← Finset.sum_add_sum_compl C, Finset.sum_congr rfl hC,
      Finset.sum_congr rfl hCc, ← Finset.mul_sum, ← Finset.mul_sum]
  have hint : interactionLoss (edgeObservation left right edgeWeight) x =
      -∑ e, ‖x (left e) - x (right e)‖ := by
    rw [interactionLoss, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [edgeResidual left right edgeWeight left_ne_right e x]
    simp [edgeObservation, edgeWeight]
  rw [sudokuLoss, allDifferentLoss, compilerLoss, hpin, hint]
  ring

/-! ### Clue-respecting assignments, conflicts and valid completions -/

/-- `InDomain` spelled out: clue cells carry their clue digit and every other
cell carries a digit in `{1, …, 9}`. -/
theorem inDomain_iff {p : ℕ} [Fact p.Prime] (C : Finset (Fin 81))
    (g : Fin 81 → ℕ) (x : Parameter p 81) :
    InDomain (sudokuDomain p C g) x ↔
      (∀ i ∈ C, x i = (g i : ℚ_[p])) ∧
        (∀ i ∉ C, ∃ k ∈ Finset.Icc (1 : ℕ) 9, x i = (k : ℚ_[p])) := by
  constructor
  · intro hx
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := hx i
      rw [sudokuDomain_of_mem hi, Finset.mem_singleton] at this
      exact this
    · have := hx i
      rw [sudokuDomain_of_not_mem hi, mem_digitSet] at this
      obtain ⟨k, hk, hk'⟩ := this
      exact ⟨k, hk, hk'.symm⟩
  · rintro ⟨hC, hCc⟩ i
    by_cases hi : i ∈ C
    · rw [sudokuDomain_of_mem hi, Finset.mem_singleton]
      exact hC i hi
    · rw [sudokuDomain_of_not_mem hi]
      obtain ⟨k, hk, hk'⟩ := hCc i hi
      rw [hk']
      exact natCast_mem_digitSet hk

open Classical in
/-- With unit weights, `conflictWeight` is the number of conflicting
(deduplicated) peer pairs. -/
theorem conflictWeight_eq_card {p : ℕ} [Fact p.Prime] (x : Parameter p 81) :
    conflictWeight left right edgeWeight x =
      ((Finset.univ.filter (fun e : PeerEdge => x (left e) = x (right e))).card : ℝ) := by
  rw [conflictWeight, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : x (left e) = x (right e) <;> simp [h, edgeWeight]

open Classical in
/-- `MinimizesConflicts` spelled out: a clue-respecting digit assignment whose
number of conflicting peer pairs is minimal among clue-respecting digit
assignments. -/
theorem minimizesConflicts_iff {p : ℕ} [Fact p.Prime] (C : Finset (Fin 81))
    (g : Fin 81 → ℕ) (x : Parameter p 81) :
    MinimizesConflicts (sudokuDomain p C g) left right edgeWeight x ↔
      InDomain (sudokuDomain p C g) x ∧
        ∀ y, InDomain (sudokuDomain p C g) y →
          (Finset.univ.filter (fun e : PeerEdge => x (left e) = x (right e))).card ≤
            (Finset.univ.filter (fun e : PeerEdge => y (left e) = y (right e))).card := by
  unfold MinimizesConflicts
  simp only [conflictWeight_eq_card, Nat.cast_le]

/-- A valid completion: a clue-respecting digit assignment with no two peers
carrying the same digit. -/
def ValidCompletion (p : ℕ) [Fact p.Prime] (C : Finset (Fin 81)) (g : Fin 81 → ℕ)
    (x : Parameter p 81) : Prop :=
  InDomain (sudokuDomain p C g) x ∧ ∀ i j, Peer i j → x i ≠ x j

theorem validCompletion_iff_isProper {p : ℕ} [Fact p.Prime] (C : Finset (Fin 81))
    (g : Fin 81 → ℕ) (x : Parameter p 81) :
    ValidCompletion p C g x ↔ IsProper (sudokuDomain p C g) left right x := by
  unfold ValidCompletion IsProper
  constructor
  · rintro ⟨hx, hpeer⟩
    exact ⟨hx, fun e => hpeer _ _ (peer_left_right e)⟩
  · rintro ⟨hx, hedge⟩
    refine ⟨hx, fun i j hij => ?_⟩
    have h := hedge (edgeOf i j hij)
    rcases edgeOf_endpoints i j hij with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · rw [hl, hr] at h
      exact h
    · rw [hl, hr] at h
      exact fun hij' => h hij'.symm

/-! ### Corollary `cor:sudoku-special-case` -/

/-- Thesis Corollary `cor:sudoku-special-case`.  For `p > 9`, clue digits in
`{1, …, 9}` and `α > 20`:
(i) the minimal objective has a global minimiser;
(ii) its global minimisers are exactly the clue-respecting digit assignments
     minimising the peer-conflict count;
(iii) if the puzzle is satisfiable, its global minimisers are exactly the
      valid completions. -/
theorem sudoku_special_case {p : ℕ} [Fact p.Prime] (hp : 9 < p)
    (C : Finset (Fin 81)) (g : Fin 81 → ℕ) (hg : ClueDigits C g)
    {α : ℝ} (hα : 20 < α) :
    (∃ x, IsGlobalMin (sudokuLoss p C g α) x) ∧
    (∀ x, IsGlobalMin (sudokuLoss p C g α) x ↔
      MinimizesConflicts (sudokuDomain p C g) left right edgeWeight x) ∧
    ((∃ y, ValidCompletion p C g y) →
      ∀ x, IsGlobalMin (sudokuLoss p C g α) x ↔ ValidCompletion p C g x) := by
  have hneD := sudokuDomain_nonempty p C g
  have hsep := sudokuDomain_globallyUnitSeparated hp hg
  have hdom : ∀ i, incidentEdgeWeight left right edgeWeight i < α := by
    intro i
    rw [degree_eq_twenty]
    exact hα
  refine ⟨?_, ?_, ?_⟩
  · exact exists_allDifferentLoss_globalMin _ α left right edgeWeight hneD
      left_ne_right hsep edgeWeight_nonneg hdom
  · intro x
    exact globalMin_allDifferentLoss_iff _ α left right edgeWeight hneD
      left_ne_right hsep edgeWeight_nonneg hdom x
  · rintro ⟨y, hy⟩ x
    rw [validCompletion_iff_isProper]
    exact globalMin_allDifferentLoss_iff_proper_of_satisfiable _ α left right
      edgeWeight hneD left_ne_right hsep edgeWeight_pos hdom
      ⟨y, (validCompletion_iff_isProper C g y).mp hy⟩ x

/-! ### Units contain every digit exactly once -/

/-- In a valid completion, any unit of `9` pairwise-peer cells contains every
digit exactly once (pigeonhole: `9` distinct digits among `9` cells). -/
theorem unit_complete {p : ℕ} [Fact p.Prime] {C : Finset (Fin 81)} {g : Fin 81 → ℕ}
    (hg : ClueDigits C g) {x : Parameter p 81} (hx : ValidCompletion p C g x)
    (U : Finset (Fin 81)) (hU : U.card = 9)
    (hpeer : ∀ i ∈ U, ∀ j ∈ U, i ≠ j → Peer i j)
    {k : ℕ} (hk : k ∈ Finset.Icc (1 : ℕ) 9) :
    ∃! i, i ∈ U ∧ x i = (k : ℚ_[p]) := by
  classical
  have hinj : Set.InjOn x U := by
    intro i hi j hj hij
    by_contra hne
    exact hx.2 i j (hpeer i hi j hj hne) hij
  have himage : U.image x = digitSet p := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨i, _, rfl⟩ := ha
      exact sudokuDomain_subset_digitSet hg i (hx.1 i)
    · rw [Finset.card_image_of_injOn hinj, hU, card_digitSet]
  have hmem : (k : ℚ_[p]) ∈ U.image x := by
    rw [himage]
    exact natCast_mem_digitSet hk
  rw [Finset.mem_image] at hmem
  obtain ⟨i, hi, hik⟩ := hmem
  refine ⟨i, ⟨hi, hik⟩, ?_⟩
  rintro j ⟨hj, hjk⟩
  exact hinj hj hi (hjk.trans hik.symm)

/-- The cells of row `r`. -/
def rowCells (r : Fin 9) : Finset (Fin 81) := Finset.univ.filter (fun i => row i = r)

/-- The cells of column `c`. -/
def colCells (c : Fin 9) : Finset (Fin 81) := Finset.univ.filter (fun i => col i = c)

/-- The cells of box `b`. -/
def boxCells (b : Fin 9) : Finset (Fin 81) := Finset.univ.filter (fun i => box i = b)

theorem card_rowCells : ∀ r : Fin 9, (rowCells r).card = 9 := by
  decide +kernel

theorem card_colCells : ∀ c : Fin 9, (colCells c).card = 9 := by
  decide +kernel

theorem card_boxCells : ∀ b : Fin 9, (boxCells b).card = 9 := by
  decide +kernel

theorem row_complete {p : ℕ} [Fact p.Prime] {C : Finset (Fin 81)} {g : Fin 81 → ℕ}
    (hg : ClueDigits C g) {x : Parameter p 81} (hx : ValidCompletion p C g x)
    (r : Fin 9) {k : ℕ} (hk : k ∈ Finset.Icc (1 : ℕ) 9) :
    ∃! i, i ∈ rowCells r ∧ x i = (k : ℚ_[p]) := by
  refine unit_complete hg hx (rowCells r) (card_rowCells r) ?_ hk
  intro i hi j hj hij
  simp only [rowCells, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact ⟨hij, Or.inl (hi.trans hj.symm)⟩

theorem col_complete {p : ℕ} [Fact p.Prime] {C : Finset (Fin 81)} {g : Fin 81 → ℕ}
    (hg : ClueDigits C g) {x : Parameter p 81} (hx : ValidCompletion p C g x)
    (c : Fin 9) {k : ℕ} (hk : k ∈ Finset.Icc (1 : ℕ) 9) :
    ∃! i, i ∈ colCells c ∧ x i = (k : ℚ_[p]) := by
  refine unit_complete hg hx (colCells c) (card_colCells c) ?_ hk
  intro i hi j hj hij
  simp only [colCells, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact ⟨hij, Or.inr (Or.inl (hi.trans hj.symm))⟩

theorem box_complete {p : ℕ} [Fact p.Prime] {C : Finset (Fin 81)} {g : Fin 81 → ℕ}
    (hg : ClueDigits C g) {x : Parameter p 81} (hx : ValidCompletion p C g x)
    (b : Fin 9) {k : ℕ} (hk : k ∈ Finset.Icc (1 : ℕ) 9) :
    ∃! i, i ∈ boxCells b ∧ x i = (k : ℚ_[p]) := by
  refine unit_complete hg hx (boxCells b) (card_boxCells b) ?_ hk
  intro i hi j hj hij
  simp only [boxCells, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact ⟨hij, Or.inr (Or.inr (hi.trans hj.symm))⟩

end PhdThesisLean.SudokuSpecialCase

#print axioms PhdThesisLean.SudokuSpecialCase.digit_difference_norm
#print axioms PhdThesisLean.SudokuSpecialCase.card_peers
#print axioms PhdThesisLean.SudokuSpecialCase.degree_eq_twenty
#print axioms PhdThesisLean.SudokuSpecialCase.sudokuLoss_eq
#print axioms PhdThesisLean.SudokuSpecialCase.sudoku_special_case
#print axioms PhdThesisLean.SudokuSpecialCase.unit_complete
#print axioms PhdThesisLean.SudokuSpecialCase.card_peerEdge
#print axioms PhdThesisLean.SudokuSpecialCase.inDomain_iff
#print axioms PhdThesisLean.SudokuSpecialCase.conflictWeight_eq_card
#print axioms PhdThesisLean.SudokuSpecialCase.minimizesConflicts_iff
#print axioms PhdThesisLean.SudokuSpecialCase.validCompletion_iff_isProper
#print axioms PhdThesisLean.SudokuSpecialCase.row_complete
