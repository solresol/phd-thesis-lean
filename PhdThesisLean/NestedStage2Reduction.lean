import PhdThesisLean.FixedPrimeMaxCutReduction
import PhdThesisLean.NestedEasyHardEasy

/-!
# Stage 2 of the nested family as a map of encoded instances

Thesis Theorem `thm:nested-easy-hard-easy` (`complexity-regimes/body.tex`), Stage 2:
"the map `G ↦ A'_G` is a polynomial-time reduction from an NP-hard problem, so ordinary
summed `5`-adic linear regression over the family `{A'_G}_G` is NP-hard". This module
gives the semantic half; the machine is in `NestedStage2Machine.lean`.

## The map

For a Max-Cut instance `(G, K)` with unary input length `L`, `nestedReduce` produces the
rows of `A'_{G''}` for the graph `G''` obtained from `G` by adding a pendant edge from a
fresh vertex `z` to the vertex `K` and padding the vertex set to `L` vertices. Vertex `x`
is the coefficient `β (x + 1)` and `z` is `β 0`. The rows are listed edge by edge (the
five rows `(e_u, 0)`, `(e_u, 1)`, `(e_v, 0)`, `(e_v, 1)`, `(e_u + e_v, 1)` of each edge)
and then vertex by vertex (one pair `(e_j, 0)`, `(e_j, 1)` per vertex), so every vertex
receives exactly `M_j = d_j + 1` forcing pairs, as in `A'_G`. The bound is
`3|E| + 2 + L - K`: the optimal value of `A'_{G''}` is
`∑ M_j + |E''| - maxcut(G'') = (2|E''| + L) + |E''| - (maxcut(G) + 1)`.

## Results

* `maxCut_iff_stage2`: for every prime `p` and every Max-Cut instance, some cut has at
  least `K` edges iff the produced instance is accepted.
* `stage2_rows_eq_A'_G`: for a loopless graph the produced rows, read as dense rows over
  `Fin L`, form exactly the multiset `NestedEasyHardEasy.A'_G` of the graph `G''`.
-/

namespace PhdThesisLean.NestedStage2Reduction

open LeanNPHardness LeanNPHardness.CNF LeanNPHardness.MaxCut
open PhdThesisLean.PadicRegressionLanguage
open PhdThesisLean.FixedPrimeMaxCutReduction (edgeRows edgeLoss U snap snap_le snap_bool bval
  U_zero U_one edgeLoss_bool edgeLoss_snap_le loss_edgeRows bval_of_bool cut_cast)

/-! ### The map -/

/-- The forcing pair of a vertex with literal index `i`. -/
def vertexRows (i : ℕ) : List Row := [[.positive i], [.positive i, .positive 0]]

/-- The rows of `A'_{G''}`: edge rows of `G`, of the pendant edge, and one forcing pair
per vertex. -/
def stage2Rows (G : List Edge) (K L : ℕ) : List Row :=
  G.flatMap (fun e => edgeRows (e.1 + 2) (e.2 + 2)) ++ edgeRows 1 (K + 2) ++
    (List.range L).flatMap fun i => vertexRows (i + 1)

/-- The bound `3|E| + 2 + L - K` (truncated). -/
def stage2Bound (G : List Edge) (K L : ℕ) : ℕ := 3 * G.length + 4 + L - (K + 2)

/-- The Stage 2 reduction, with `L` the length of the unary encoding of the input. -/
def nestedReduce (x : List Edge × ℕ) : List Row × ℕ :=
  (stage2Rows x.1 x.2 (MaxCut.unaryEncoding.encode x).length,
    stage2Bound x.1 x.2 (MaxCut.unaryEncoding.encode x).length)

/-! ### Correctness -/

variable {p : ℕ}

theorem loss_vertexRows (β : ℕ → ℚ) (i : ℕ) : loss p β (vertexRows (i + 1)) = U p (β i) := by
  simp only [vertexRows, loss, PadicRegressionLanguage.residual, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, term, U]
  ring_nf

theorem loss_stage2Rows (β : ℕ → ℚ) (G : List Edge) (K L : ℕ) :
    loss p β (stage2Rows G K L) =
      (G.map fun e => edgeLoss p (β (e.1 + 1)) (β (e.2 + 1))).sum +
        edgeLoss p (β 0) (β (K + 1)) + ((List.range L).map fun i => U p (β i)).sum := by
  rw [stage2Rows, loss_append, loss_append, loss_flatMap, loss_flatMap]
  have h1 : ∀ e : Edge, loss p β (edgeRows (e.1 + 2) (e.2 + 2)) =
      edgeLoss p (β (e.1 + 1)) (β (e.2 + 1)) := fun e => loss_edgeRows β (e.1 + 1) (e.2 + 1)
  have h2 : loss p β (edgeRows 1 (K + 2)) = edgeLoss p (β 0) (β (K + 1)) :=
    loss_edgeRows β 0 (K + 1)
  simp only [h1, h2, loss_vertexRows]

theorem sum_U_le_snap [Fact p.Prime] (β : ℕ → ℚ) (L : List ℕ) :
    (L.map fun i => U p (snap p (β i))).sum ≤ (L.map fun i => U p (β i)).sum := by
  apply List.sum_le_sum
  intro i _
  have := snap_le (p := p) (β i)
  have := padicNorm.nonneg (p := p) (β i - snap p (β i))
  linarith

theorem loss_snap_le [Fact p.Prime] (β : ℕ → ℚ) (G : List Edge) (K L : ℕ) :
    loss p (fun i => snap p (β i)) (stage2Rows G K L) ≤ loss p β (stage2Rows G K L) := by
  rw [loss_stage2Rows, loss_stage2Rows]
  have hG : (G.map fun e => edgeLoss p (snap p (β (e.1 + 1))) (snap p (β (e.2 + 1)))).sum ≤
      (G.map fun e => edgeLoss p (β (e.1 + 1)) (β (e.2 + 1))).sum := by
    apply List.sum_le_sum
    intro e _
    exact edgeLoss_snap_le _ _
  have hz := edgeLoss_snap_le (p := p) (β 0) (β (K + 1))
  have hv := sum_U_le_snap (p := p) β (List.range L)
  linarith

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

theorem loss_bool (c : ℕ → Bool) (G : List Edge) (K L : ℕ) :
    loss p (fun i => bval (c i)) (stage2Rows G K L) =
      3 * G.length - cut (fun x => c (x + 1)) G + (3 - (if c 0 != c (K + 1) then 1 else 0)) +
        L := by
  simp only [loss_stage2Rows]
  rw [sum_edgeLoss_bool, edgeLoss_bool]
  have : ∀ i ∈ List.range L, U p (bval (c i)) = 1 := by
    intro i _
    cases c i <;> simp [bval, U_zero, U_one]
  rw [List.map_congr_left this]
  simp

/-- **Stage 2 preserves membership.** For every prime `p` and every Max-Cut instance, a
cut with at least `K` edges exists iff some `β` has loss at most `3|E| + 2 + L - K` on the
rows of `A'_{G''}`. -/
theorem maxCut_iff_stage2 [Fact p.Prime] (G : List Edge) (K L : ℕ) :
    MaxCutLang (G, K) ↔ RegressionLang p (stage2Rows G K L, stage2Bound G K L) := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨fun i => bval (if i = 0 then !s K else s (i - 1)), ?_⟩
    have := loss_bool (p := p) (fun i => if i = 0 then !s K else s (i - 1)) G K L
    simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false, if_true] at this
    show loss p _ (stage2Rows G K L) ≤ ((stage2Bound G K L : ℕ) : ℚ)
    rw [this]
    have hc : (if (!s K) != s K then (1 : ℚ) else 0) = 1 := by cases s K <;> rfl
    rw [hc]
    have hK : K ≤ cut s G := hs
    have hcut := cut_le s G
    have hT : ((stage2Bound G K L : ℕ) : ℚ) = 3 * G.length + 2 + L - K := by
      rw [stage2Bound, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hT]
    have : (K : ℚ) ≤ cut s G := by exact_mod_cast hK
    linarith
  · rintro ⟨β, hβ⟩
    change loss p β (stage2Rows G K L) ≤ ((stage2Bound G K L : ℕ) : ℚ) at hβ
    have hsnap := loss_snap_le (p := p) β G K L
    set c : ℕ → Bool := fun i => decide (snap p (β i) = 1) with hc
    have hfun : (fun i => snap p (β i)) = fun i => bval (c i) := by
      funext i
      exact bval_of_bool (snap_bool (β i))
    rw [hfun, loss_bool] at hsnap
    refine ⟨fun x => c (x + 1), ?_⟩
    have hz : (if c 0 != c (K + 1) then (1 : ℚ) else 0) ≤ 1 := by split <;> norm_num
    have hcut : (cut (fun x => c (x + 1)) G : ℚ) ≤ G.length := by exact_mod_cast cut_le _ _
    by_cases hle : K + 2 ≤ 3 * G.length + 4 + L
    · have hT : ((stage2Bound G K L : ℕ) : ℚ) = 3 * G.length + 2 + L - K := by
        rw [stage2Bound, Nat.cast_sub hle]
        push_cast
        ring
      rw [hT] at hβ
      have : (K : ℚ) ≤ cut (fun x => c (x + 1)) G := by linarith
      exact_mod_cast this
    · have hT : stage2Bound G K L = 0 := by rw [stage2Bound]; omega
      rw [hT] at hβ
      push_cast at hβ
      have hL : (0 : ℚ) ≤ L := by positivity
      linarith

/-! ### The produced rows are `A'_{G''}` -/

open PhdThesisLean.NestedEasyHardEasy (basis deg M A_G A'_G)

/-- A sparse row with nonnegative unit terms, read as a dense row over `Fin n`. -/
noncomputable def toDense (n : ℕ) (r : Row) : NestedEasyHardEasy.Row n :=
  (fun j => ((r.count (.positive (j.1 + 1)) : ℤ) - r.count (.negative (j.1 + 1)) : ℚ_[5]),
    ((r.count (.positive 0) : ℤ) - r.count (.negative 0) : ℚ_[5]))

/-- The edges of `G''` over `Fin L`: the edges of `G` shifted by one, then the pendant
edge `(z, K)`. -/
def edgesOf (G : List Edge) (K : ℕ) : List (ℕ × ℕ) :=
  G.map (fun e => (e.1 + 1, e.2 + 1)) ++ [(0, K + 1)]

theorem toDense_vertex0 (n : ℕ) (j : Fin n) :
    toDense n [.positive (j.1 + 1)] = (basis j, 0) := by
  refine Prod.ext ?_ ?_
  · funext k
    by_cases h : k = j
    · subst h; simp [toDense, basis]
    · have : k.1 ≠ j.1 := fun e => h (Fin.ext e)
      simp [toDense, basis, h, List.count_cons, Ne.symm this]
  · simp [toDense]

theorem toDense_vertex1 (n : ℕ) (j : Fin n) :
    toDense n [.positive (j.1 + 1), .positive 0] = (basis j, 1) := by
  refine Prod.ext ?_ ?_
  · funext k
    by_cases h : k = j
    · subst h; simp [toDense, basis, List.count_cons]
    · have : k.1 ≠ j.1 := fun e => h (Fin.ext e)
      simp [toDense, basis, h, List.count_cons, Ne.symm this]
  · simp [toDense, List.count_cons]

theorem toDense_edge (n : ℕ) (u v : Fin n) (huv : u ≠ v) :
    toDense n [.positive (u.1 + 1), .positive (v.1 + 1), .positive 0] = (basis u + basis v, 1) := by
  have huv' : u.1 ≠ v.1 := fun e => huv (Fin.ext e)
  refine Prod.ext ?_ ?_
  · funext k
    by_cases hu : k = u
    · subst hu
      simp [toDense, basis, huv, Ne.symm huv', List.count_cons]
    · by_cases hv : k = v
      · subst hv
        have : k.1 ≠ u.1 := fun e => hu (Fin.ext e)
        simp [toDense, basis, hu, Ne.symm this, List.count_cons]
      · have h1 : k.1 ≠ u.1 := fun e => hu (Fin.ext e)
        have h2 : k.1 ≠ v.1 := fun e => hv (Fin.ext e)
        simp [toDense, basis, hu, hv, Ne.symm h1, Ne.symm h2, List.count_cons]
  · simp [toDense, List.count_cons]

theorem sum_singleton_fiber {n : ℕ} {ε : Type*} [Fintype ε] {α : Type*} (g : ε → Fin n)
    (F : Fin n → α) :
    (∑ e, ({F (g e)} : Multiset α)) =
      ∑ j, Multiset.replicate (Finset.univ.filter (fun e => g e = j)).card (F j) := by
  rw [← Finset.sum_fiberwise' Finset.univ g (fun j => ({F j} : Multiset α))]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_const, Multiset.nsmul_singleton]

/-- Double counting for multisets: summing one singleton per edge endpoint gives each
vertex with multiplicity its degree, for a loopless edge family. -/
theorem sum_endpoints {n : ℕ} {ε : Type*} [Fintype ε] [DecidableEq ε]
    (left right : ε → Fin n) (hne : ∀ e, left e ≠ right e) {α : Type*}
    (f : Fin n → α) :
    (∑ e, (({f (left e)} : Multiset α) + {f (right e)})) =
      ∑ j, Multiset.replicate (deg left right j) (f j) := by
  rw [Finset.sum_add_distrib, sum_singleton_fiber, sum_singleton_fiber, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Multiset.replicate_add]
  congr 1
  unfold deg
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  intro e _ h1 h2
  exact hne e (h1.trans h2.symm)

theorem coe_flatMap {β γ : Type*} (L : List β) (g : β → List γ) :
    ((L.flatMap g : List γ) : Multiset γ) = (L.map fun b => ((g b : List γ) : Multiset γ)).sum := by
  induction L with
  | nil => rfl
  | cons b L ih => rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, List.sum_cons]

theorem edgesOf_loopless (G : List Edge) (K : ℕ) (hloop : ∀ e ∈ G, e.1 ≠ e.2) :
    ∀ e ∈ edgesOf G K, e.1 ≠ e.2 := by
  intro e he
  simp only [edgesOf, List.mem_append, List.mem_map, List.mem_singleton] at he
  rcases he with ⟨e', he', rfl⟩ | rfl
  · simpa using hloop e' he'
  · simp

/-- The vertex maps of the edges of `G''` into `Fin L`. -/
def leftOf (Es : List (ℕ × ℕ)) (L : ℕ) (hb : ∀ e ∈ Es, e.1 < L ∧ e.2 < L) :
    Fin Es.length → Fin L := fun e => ⟨Es[e].1, (hb _ (List.getElem_mem _)).1⟩

def rightOf (Es : List (ℕ × ℕ)) (L : ℕ) (hb : ∀ e ∈ Es, e.1 < L ∧ e.2 < L) :
    Fin Es.length → Fin L := fun e => ⟨Es[e].2, (hb _ (List.getElem_mem _)).2⟩

/-- **The produced rows are `A'_{G''}`.** For a loopless graph, the rows of
`stage2Rows G K L`, read as dense rows over `Fin L`, form exactly the multiset
`NestedEasyHardEasy.A'_G` of the graph `G''` with edges `edgesOf G K`. -/
theorem stage2_rows_eq_A'_G (G : List Edge) (K L : ℕ) (hloop : ∀ e ∈ G, e.1 ≠ e.2)
    (hb : ∀ e ∈ edgesOf G K, e.1 < L ∧ e.2 < L) :
    (((stage2Rows G K L).map (toDense L) : List _) : Multiset (NestedEasyHardEasy.Row L)) =
      A'_G (leftOf (edgesOf G K) L hb) (rightOf (edgesOf G K) L hb) := by
  set Es := edgesOf G K with hEs
  have hloopE := edgesOf_loopless G K hloop
  set l := leftOf Es L hb
  set r := rightOf Es L hb
  have hne : ∀ e, l e ≠ r e := by
    intro e h
    exact hloopE _ (List.getElem_mem e.2) (congrArg Fin.val h)
  have hrows : stage2Rows G K L = Es.flatMap (fun e => edgeRows (e.1 + 1) (e.2 + 1)) ++
      (List.finRange L).flatMap (fun j => vertexRows (j.1 + 1)) := by
    rw [stage2Rows, hEs, edgesOf, List.flatMap_append, List.flatMap_map,
      ← List.map_coe_finRange_eq_range, List.flatMap_map]
    simp
  -- the dense edge rows
  have hedge : ∀ e : Fin Es.length,
      (((edgeRows (Es[e.1].1 + 1) (Es[e.1].2 + 1)).map (toDense L) : List _) :
        Multiset (NestedEasyHardEasy.Row L)) =
        ({(basis (l e), 0)} + {(basis (r e), 0)}) + ({(basis (l e), 1)} + {(basis (r e), 1)}) +
          {(basis (l e) + basis (r e), 1)} := by
    intro e
    have h1 := toDense_vertex0 L (l e)
    have h2 := toDense_vertex1 L (l e)
    have h3 := toDense_vertex0 L (r e)
    have h4 := toDense_vertex1 L (r e)
    have h5 := toDense_edge L (l e) (r e) (hne e)
    have e1 : (l e).1 = Es[e.1].1 := rfl
    have e2 : (r e).1 = Es[e.1].2 := rfl
    rw [e1] at h1 h2 h5
    rw [e2] at h3 h4 h5
    simp only [edgeRows, List.map_cons, List.map_nil, h1, h2, h3, h4, h5]
    simp only [← Multiset.cons_coe, Multiset.coe_nil, ← Multiset.singleton_add, add_zero]
    abel
  have hvertex : ∀ j : Fin L, (((vertexRows (j.1 + 1)).map (toDense L) : List _) :
      Multiset (NestedEasyHardEasy.Row L)) = {(basis j, 0)} + {(basis j, 1)} := by
    intro j
    simp only [vertexRows, List.map_cons, List.map_nil, toDense_vertex0, toDense_vertex1]
    simp only [← Multiset.cons_coe, Multiset.coe_nil, ← Multiset.singleton_add, add_zero]
  rw [hrows, List.map_append, ← Multiset.coe_add, List.map_flatMap, List.map_flatMap,
    coe_flatMap, coe_flatMap]
  rw [← Fin.sum_univ_fun_getElem Es (fun e => (((edgeRows (e.1 + 1) (e.2 + 1)).map
    (toDense L) : List _) : Multiset (NestedEasyHardEasy.Row L)))]
  simp only [hedge]
  rw [← Fin.sum_univ_def]
  simp only [hvertex]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_endpoints l r hne (fun j => (basis j, (0 : ℚ_[5]))),
    sum_endpoints l r hne (fun j => (basis j, (1 : ℚ_[5]))), Finset.sum_add_distrib]
  unfold A'_G A_G
  simp only [NestedEasyHardEasy.M_sub_one]
  simp only [NestedEasyHardEasy.M, Multiset.replicate_succ, ← Multiset.singleton_add,
    Finset.sum_add_distrib]
  abel

end PhdThesisLean.NestedStage2Reduction

#print axioms PhdThesisLean.NestedStage2Reduction.maxCut_iff_stage2
#print axioms PhdThesisLean.NestedStage2Reduction.stage2_rows_eq_A'_G
