import PhdThesisLean.PadicRegressionLanguage

/-!
# The fixed-prime Max-Cut reduction as a map of encoded instances

This module gives the semantic half of the NP-hardness transfer for thesis Theorem
`thm:fixed-prime-hardness` (`padic-regression-complexity/body.tex`): an explicit map
`reduce` from the library's Max-Cut instances (`LeanNPHardness.MaxCut.MaxCutLang`, an
edge list on natural-number vertices and a threshold `K`) to regression instances of
`PadicRegressionLanguage`, with `maxCut_iff_regression` proving that it preserves
membership for every prime `p`. The machine computing `reduce` is in
`FixedPrimeMaxCutMachine.lean`.

## The construction

Vertex `x` is the coefficient with literal index `x + 2` (that is, `β (x + 1)`); index
`0` is the target and index `1` is a fresh vertex `z`. Every edge `(a, b)` contributes
the five rows `edgeRows a b`:
`(e_a, 0)`, `(e_a, 1)`, `(e_b, 0)`, `(e_b, 1)`, `(e_a + e_b, 1)`,
so each endpoint receives one Boolean forcing pair per incident edge. This is the
thesis's construction with forcing weight `M_j = d_j` instead of `d_j + 1`: weak
domination suffices for the decision problem, and it lets the rows be emitted edge by
edge.

`reduce (G, K)` lists the rows of every edge of `G`, then the rows of one extra pendant
edge between `z` and the vertex `K`, then `K + 2` constant rows `(0, 1)`, with bound
`3|E| + 4`. The pendant edge and the constant rows let a streaming machine handle the
threshold clause of the input like an edge clause: `z` occurs nowhere else, so the
pendant edge raises the maximum cut by exactly one, and each constant row costs exactly
one.

## Correctness

* `snap` maps every rational to `0` or `1` and satisfies the local snapping inequality
  `U (snap t) + |t - snap t|_p ≤ U t` (`snap_le`, thesis `lem:local-boolean-snapping`
  over `ℚ`), so snapping all coordinates does not increase the loss of any edge gadget
  (`edgeLoss_snap_le`), including self-loops.
* At Boolean points an edge gadget costs `3` minus its cut indicator (`edgeLoss_bool`).
* Hence the instance is accepted iff some cut of `G` has at least `K` edges
  (`maxCut_iff_regression`), for every prime `p`.
-/

namespace PhdThesisLean.FixedPrimeMaxCutReduction

open LeanNPHardness LeanNPHardness.CNF LeanNPHardness.MaxCut
open PhdThesisLean.PadicRegressionLanguage

/-! ### The construction -/

/-- The five rows of an edge between literal indices `a` and `b`. -/
def edgeRows (a b : ℕ) : List Row :=
  [[.positive a], [.positive a, .positive 0], [.positive b], [.positive b, .positive 0],
    [.positive a, .positive b, .positive 0]]

/-- The constant row `(0, 1)`, whose residual is `-1`. -/
def constRow : Row := [.positive 0]

/-- The rows of the instance produced from `(G, K)`. -/
def reduceRows (G : List Edge) (K : ℕ) : List Row :=
  G.flatMap (fun e => edgeRows (e.1 + 2) (e.2 + 2)) ++ edgeRows 1 (K + 2) ++
    List.replicate (K + 2) constRow

/-- The reduction from Max-Cut to summed `p`-adic regression. -/
def reduce (x : List Edge × ℕ) : List Row × ℕ :=
  (reduceRows x.1 x.2, 3 * x.1.length + 4)

/-! ### Losses of the gadgets -/

variable {p : ℕ}

/-- Boolean forcing cost `U(t) = |t|_p + |t - 1|_p`. -/
def U (p : ℕ) (t : ℚ) : ℚ := padicNorm p t + padicNorm p (t - 1)

/-- The loss of the five rows of one edge, in terms of its endpoint values. -/
def edgeLoss (p : ℕ) (s t : ℚ) : ℚ := U p s + U p t + padicNorm p (s + t - 1)

theorem loss_edgeRows (β : ℕ → ℚ) (a b : ℕ) :
    loss p β (edgeRows (a + 1) (b + 1)) = edgeLoss p (β a) (β b) := by
  simp only [edgeRows, loss, residual, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, term, edgeLoss, U]
  ring_nf

theorem loss_constRows (β : ℕ → ℚ) (n : ℕ) :
    loss p β (List.replicate n constRow) = n := by
  rw [loss_replicate]
  simp [constRow, residual, term]

/-! ### Snapping over `ℚ` -/

/-- Snap a rational to `1` if it is `p`-adically close to `1`, and to `0` otherwise. -/
noncomputable def snap (p : ℕ) (t : ℚ) : ℚ := if padicNorm p (t - 1) < 1 then 1 else 0

theorem snap_bool (t : ℚ) : snap p t = 0 ∨ snap p t = 1 := by
  unfold snap; split_ifs <;> simp

theorem U_zero : U p 0 = 1 := by simp [U]

theorem U_one : U p 1 = 1 := by simp [U]

/-- Thesis `lem:local-boolean-snapping` over `ℚ`, with the snapping rule `snap`. -/
theorem snap_le [Fact p.Prime] (t : ℚ) : U p (snap p t) + padicNorm p (t - snap p t) ≤ U p t := by
  unfold snap
  split_ifs with h
  · rw [U_one, U]
    have h1 : (1 : ℚ) ≤ padicNorm p t := by
      have := padicNorm.nonarchimedean (p := p) (q := t) (r := -(t - 1))
      rw [show t + -(t - 1) = 1 by ring, padicNorm.one, padicNorm.neg] at this
      rcases le_max_iff.mp this with h' | h'
      · exact h'
      · linarith
    linarith
  · rw [U_zero, U, sub_zero]
    push_neg at h
    linarith

theorem padicNorm_sub3_le [Fact p.Prime] (a b c : ℚ) :
    padicNorm p (a - b - c) ≤ padicNorm p a + padicNorm p b + padicNorm p c := by
  have h1 := padicNorm.triangle_ineq (p := p) (a + -b) (-c)
  have h2 := padicNorm.triangle_ineq (p := p) a (-b)
  rw [padicNorm.neg] at h1 h2
  rw [show a - b - c = a + -b + -c by ring]
  linarith

/-- Snapping both endpoints does not increase the loss of an edge gadget. -/
theorem edgeLoss_snap_le [Fact p.Prime] (s t : ℚ) :
    edgeLoss p (snap p s) (snap p t) ≤ edgeLoss p s t := by
  have hs := snap_le (p := p) s
  have ht := snap_le (p := p) t
  have he : padicNorm p (snap p s + snap p t - 1) ≤
      padicNorm p (s + t - 1) + padicNorm p (s - snap p s) + padicNorm p (t - snap p t) := by
    have := padicNorm_sub3_le (p := p) (s + t - 1) (s - snap p s) (t - snap p t)
    rwa [show s + t - 1 - (s - snap p s) - (t - snap p t) = snap p s + snap p t - 1 by ring]
      at this
  unfold edgeLoss
  linarith

/-- The value of a Boolean colour. -/
def bval (c : Bool) : ℚ := if c then 1 else 0

/-- At Boolean points an edge gadget costs `3` minus its cut indicator. -/
theorem edgeLoss_bool (c d : Bool) :
    edgeLoss p (bval c) (bval d) = 3 - (if c != d then 1 else 0) := by
  cases c <;> cases d <;>
    simp [edgeLoss, bval, U_zero, U_one] <;> norm_num

theorem cut_cast (s : ℕ → Bool) (G : List Edge) :
    (cut s G : ℚ) = (G.map fun e => if s e.1 != s e.2 then (1 : ℚ) else 0).sum := by
  induction G with
  | nil => simp [cut_nil]
  | cons e G ih =>
      rw [cut_cons, List.map_cons, List.sum_cons, ← ih]
      split <;> simp

/-- The loss of the instance, written per edge. -/
theorem loss_reduceRows (β : ℕ → ℚ) (G : List Edge) (K : ℕ) :
    loss p β (reduceRows G K) =
      (G.map fun e => edgeLoss p (β (e.1 + 1)) (β (e.2 + 1))).sum +
        edgeLoss p (β 0) (β (K + 1)) + (K + 2) := by
  rw [reduceRows, loss_append, loss_append, loss_flatMap, loss_constRows]
  have h1 : ∀ e : Edge, loss p β (edgeRows (e.1 + 2) (e.2 + 2)) =
      edgeLoss p (β (e.1 + 1)) (β (e.2 + 1)) := fun e => loss_edgeRows β (e.1 + 1) (e.2 + 1)
  have h2 : loss p β (edgeRows 1 (K + 2)) = edgeLoss p (β 0) (β (K + 1)) :=
    loss_edgeRows β 0 (K + 1)
  simp only [h1, h2]
  push_cast
  ring

/-- The loss of the snapped point is at most the loss of the original point. -/
theorem loss_snap_le [Fact p.Prime] (β : ℕ → ℚ) (G : List Edge) (K : ℕ) :
    loss p (fun i => snap p (β i)) (reduceRows G K) ≤ loss p β (reduceRows G K) := by
  rw [loss_reduceRows, loss_reduceRows]
  have hG : ∀ L : List Edge,
      (L.map fun e => edgeLoss p (snap p (β (e.1 + 1))) (snap p (β (e.2 + 1)))).sum ≤
        (L.map fun e => edgeLoss p (β (e.1 + 1)) (β (e.2 + 1))).sum := by
    intro L
    induction L with
    | nil => simp
    | cons e L ih =>
        simp only [List.map_cons, List.sum_cons]
        exact add_le_add (edgeLoss_snap_le _ _) ih
  have hz := edgeLoss_snap_le (p := p) (β 0) (β (K + 1))
  linarith [hG G]

theorem bval_of_bool {t : ℚ} (h : t = 0 ∨ t = 1) : t = bval (decide (t = 1)) := by
  rcases h with rfl | rfl <;> simp [bval]

theorem sum_edgeLoss_bool (c : ℕ → Bool) (G : List Edge) :
    (G.map fun e => edgeLoss p (bval (c (e.1 + 1))) (bval (c (e.2 + 1)))).sum =
      3 * G.length - cut (fun x => c (x + 1)) G := by
  rw [cut_cast]
  induction G with
  | nil => simp
  | cons e G ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, edgeLoss_bool,
        List.length_cons]
      push_cast
      ring

/-- The loss at a Boolean point. -/
theorem loss_bool (c : ℕ → Bool) (G : List Edge) (K : ℕ) :
    loss p (fun i => bval (c i)) (reduceRows G K) =
      3 * G.length - cut (fun x => c (x + 1)) G + (3 - (if c 0 != c (K + 1) then 1 else 0)) +
        (K + 2) := by
  simp only [loss_reduceRows]
  rw [sum_edgeLoss_bool, edgeLoss_bool]

/-- **The fixed-prime Max-Cut reduction preserves membership**: a cut of `G` with at
least `K` edges exists iff the regression instance `reduce (G, K)` has a parameter
vector of summed `p`-adic loss at most `3|E| + 4`. -/
theorem maxCut_iff_regression [Fact p.Prime] (x : List Edge × ℕ) :
    MaxCutLang x ↔ RegressionLang p (reduce x) := by
  obtain ⟨G, K⟩ := x
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨fun i => bval (if i = 0 then !s K else s (i - 1)), ?_⟩
    have := loss_bool (p := p) (fun i => if i = 0 then !s K else s (i - 1)) G K
    simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false, if_true] at this
    show loss p _ (reduceRows G K) ≤ ((3 * G.length + 4 : ℕ) : ℚ)
    rw [this]
    have hc : (if (!s K) != s K then (1 : ℚ) else 0) = 1 := by cases s K <;> rfl
    rw [hc]
    have : (K : ℚ) ≤ cut s G := by exact_mod_cast hs
    push_cast
    linarith
  · rintro ⟨β, hβ⟩
    change loss p β (reduceRows G K) ≤ ((3 * G.length + 4 : ℕ) : ℚ) at hβ
    have hsnap := loss_snap_le (p := p) β G K
    set c : ℕ → Bool := fun i => decide (snap p (β i) = 1) with hc
    have hfun : (fun i => snap p (β i)) = fun i => bval (c i) := by
      funext i
      exact bval_of_bool (snap_bool (β i))
    rw [hfun, loss_bool] at hsnap
    refine ⟨fun x => c (x + 1), ?_⟩
    have hz : (if c 0 != c (K + 1) then (1 : ℚ) else 0) ≤ 1 := by split <;> norm_num
    have : (K : ℚ) ≤ cut (fun x => c (x + 1)) G := by
      push_cast at hβ
      linarith
    exact_mod_cast this

end PhdThesisLean.FixedPrimeMaxCutReduction

#print axioms PhdThesisLean.FixedPrimeMaxCutReduction.maxCut_iff_regression
