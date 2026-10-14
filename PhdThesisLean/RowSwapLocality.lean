import PhdThesisLean.SudokuSpecialCase

namespace PhdThesisLean.RowSwapLocality

open scoped BigOperators
open PhdThesisLean.SudokuSpecialCase

/-!
# Locality of row swaps for the duplicated unit-scope objective `H_cb`

This module formalises thesis Lemma `lem:row-swap-locality` ("Locality of row
swaps") from `sudoku-via-padic-regression/body.tex` (Section "Heuristic
details", subsection "Row-swap local search"), together with the definition
of the duplicated unit-scope column/box conflict count `H_cb` from the
"Illustrative computations" section of the same file:

  `conf(U; x) := ∑_{d=1}^{9} C(#{u ∈ U : x_u = d}, 2)`,
  `H_cb(x)    := ∑_{c=1}^{9} conf(C_c; x) + ∑_{b=1}^{9} conf(B_b; x)`.

## Construction

* Cell geometry is reused from `PhdThesisLean.SudokuSpecialCase`: cells are
  `Fin 81` with `row`, `col`, `box : Fin 81 → ℕ`, and the units
  `rowCells r`, `colCells c`, `boxCells b : Finset (Fin 81)` are indexed by
  `Fin 9`.  `colIdx i`, `boxIdx i : Fin 9` are the column and box of a cell
  as unit indices.
* States are `x : Fin 81 → ℕ` (the thesis's digit-valued states; values
  outside `1..9` are allowed by the type but never contribute to a conflict
  count, so on digit-valued states `conf` is literally the thesis's formula).
* `conf U x` is `conf(U; x)`, `Hcb x` is `H_cb(x)`, and `H x` adds the nine
  row terms, so that the thesis's remark "the row contribution is identically
  zero on the row-permutation state space and is omitted" can be stated
  (`H_eq_Hcb_of_rowsArePerms`).
* `swap x i j = x ∘ Equiv.swap i j` exchanges the values at cells `i` and `j`
  (the thesis's `x ⊕ ξ` for the swap `ξ`).
* `RowIsPerm x r` says the digits of the nine cells of row `r` are exactly
  `{1, …, 9}`; `RowsArePerms x` says this for every row (the thesis's "each
  row is a permutation of `1, …, 9`").

## Results

* `conf_swap_of_not_mem`, `conf_swap_of_both_mem`: a unit containing neither
  or both swapped cells has the same conflict count before and after the swap
  (it sees the same multiset of digits).
* `conf_rowCells_swap`: a within-row swap preserves every row term;
  `rowsArePerms_swap`: it preserves the row-permutation property;
  `conf_eq_zero_of_rowIsPerm`: a permutation row contributes `0`.
* `conf_colCells_swap_of_not_mem`, `conf_boxCells_swap_of_not_mem`: columns
  and boxes containing neither swapped cell are unchanged;
  `conf_boxCells_swap_of_box_eq`: if the two cells share a box, every box
  term is unchanged.
* `Hcb_swap_locality` (the thesis's `ΔH_cb` statement): for cells `i, j` in
  distinct columns, `H_cb(swap) − H_cb(x)` is the change in the two column
  terms plus the change in the terms of the (one or two) boxes containing
  `i` and `j`; no other term changes.
* `row_swap_locality` (headline): for cells in the same row and distinct
  columns, the same identity for the full objective `H`, row terms included.
* `H_eq_Hcb_of_rowsArePerms`, `H_swap_eq_Hcb_swap`: on the row-permutation
  state space `H = H_cb`, before and after the swap.

## Correspondence notes

* The thesis lemma assumes `x` digit-valued and clue-consistent with every
  row a permutation, and swaps two *non-clue* cells of one row at columns
  `c₁ ≠ c₂`.  The `H_cb` identity `Hcb_swap_locality` needs none of this: it
  holds for any state and any two cells in distinct columns (same row or
  not).  The row hypothesis is used only to control the row terms
  (`conf_rowCells_swap`, `H_swap_sub_eq_Hcb_swap_sub`) and the permutation
  hypothesis only to make them vanish (`H_eq_Hcb_of_rowsArePerms`).  The
  formal results are therefore strictly stronger than the thesis statement.
* The non-clue condition is about the search space (the swap must stay
  clue-consistent), not about the identity; `swap_clueConsistent` records
  that swapping two non-clue cells preserves clue-consistency.  Clue cells do
  not otherwise enter `H_cb`.
* When `box i = box j` the single shared box is in fact *unchanged*
  (`conf_boxCells_swap_of_box_eq`), so the change is carried by the two
  column terms alone (`Hcb_swap_locality_of_box_eq`); the thesis's "one or
  two boxes" is an upper bound on the affected units.
* The numerical example (seed-`0` initialisation with `47` deduplicated
  conflicts but `H_cb = 56`) is data and is not formalised.
-/

/-! ### Unit indices and membership -/

/-- The column of a cell as a unit index in `Fin 9`. -/
def colIdx (i : Fin 81) : Fin 9 := ⟨col i, by unfold col; omega⟩

/-- The box of a cell as a unit index in `Fin 9`. -/
def boxIdx (i : Fin 81) : Fin 9 :=
  ⟨box i, by have := i.isLt; unfold box row col; omega⟩

@[simp] theorem colIdx_val (i : Fin 81) : (colIdx i : ℕ) = col i := rfl

@[simp] theorem boxIdx_val (i : Fin 81) : (boxIdx i : ℕ) = box i := rfl

theorem mem_rowCells {u : Fin 81} {r : Fin 9} : u ∈ rowCells r ↔ row u = r := by
  simp [rowCells]

theorem mem_colCells {u : Fin 81} {c : Fin 9} : u ∈ colCells c ↔ col u = c := by
  simp [colCells]

theorem mem_boxCells {u : Fin 81} {b : Fin 9} : u ∈ boxCells b ↔ box u = b := by
  simp [boxCells]

theorem colIdx_eq_of_mem {u : Fin 81} {c : Fin 9} (h : u ∈ colCells c) : colIdx u = c :=
  Fin.ext (mem_colCells.mp h)

theorem boxIdx_eq_of_mem {u : Fin 81} {b : Fin 9} (h : u ∈ boxCells b) : boxIdx u = b :=
  Fin.ext (mem_boxCells.mp h)

theorem mem_colCells_colIdx (u : Fin 81) : u ∈ colCells (colIdx u) := mem_colCells.mpr rfl

theorem mem_boxCells_boxIdx (u : Fin 81) : u ∈ boxCells (boxIdx u) := mem_boxCells.mpr rfl

/-! ### States, conflict counts and the objectives -/

/-- The thesis's unit conflict count `conf(U; x) = ∑_{d=1}^{9} C(#{u ∈ U : x_u = d}, 2)`:
the number of (unordered) pairs of cells of `U` carrying the same digit. -/
def conf (U : Finset (Fin 81)) (x : Fin 81 → ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 9, Nat.choose (U.filter (fun u => x u = d)).card 2

/-- The duplicated unit-scope column/box conflict count
`H_cb(x) = ∑_c conf(C_c; x) + ∑_b conf(B_b; x)`. -/
def Hcb (x : Fin 81 → ℕ) : ℕ :=
  ∑ c : Fin 9, conf (colCells c) x + ∑ b : Fin 9, conf (boxCells b) x

/-- The full digit-restricted unit-scope objective: `H_cb` plus the nine row terms
that the thesis omits on the row-permutation state space. -/
def H (x : Fin 81 → ℕ) : ℕ :=
  ∑ r : Fin 9, conf (rowCells r) x + Hcb x

/-- The state obtained from `x` by exchanging the values at cells `i` and `j`. -/
def swap (x : Fin 81 → ℕ) (i j : Fin 81) : Fin 81 → ℕ := x ∘ Equiv.swap i j

theorem swap_apply (x : Fin 81 → ℕ) (i j u : Fin 81) :
    swap x i j u = x (Equiv.swap i j u) := rfl

@[simp] theorem swap_apply_left (x : Fin 81 → ℕ) (i j : Fin 81) : swap x i j i = x j := by
  simp [swap]

@[simp] theorem swap_apply_right (x : Fin 81 → ℕ) (i j : Fin 81) : swap x i j j = x i := by
  simp [swap]

theorem swap_apply_of_ne (x : Fin 81 → ℕ) {i j u : Fin 81} (hi : u ≠ i) (hj : u ≠ j) :
    swap x i j u = x u := by
  rw [swap_apply, Equiv.swap_apply_of_ne_of_ne hi hj]

/-- Row `r` of `x` is a permutation of `1, …, 9`: the digits of its nine cells are
exactly `{1, …, 9}`. -/
def RowIsPerm (x : Fin 81 → ℕ) (r : Fin 9) : Prop :=
  (rowCells r).image x = Finset.Icc 1 9

/-- Every row of `x` is a permutation of `1, …, 9` (the thesis's row-permutation
state space). -/
def RowsArePerms (x : Fin 81 → ℕ) : Prop := ∀ r : Fin 9, RowIsPerm x r

/-- Swapping two non-clue cells preserves clue-consistency: this is the role of
the thesis's non-clue hypothesis (it keeps the move inside the search space). -/
theorem swap_clueConsistent {C : Finset (Fin 81)} {g x : Fin 81 → ℕ}
    (hx : ∀ u ∈ C, x u = g u) {i j : Fin 81} (hi : i ∉ C) (hj : j ∉ C) :
    ∀ u ∈ C, swap x i j u = g u := by
  intro u hu
  rw [swap_apply_of_ne x (fun h : u = i => hi (h ▸ hu)) (fun h : u = j => hj (h ▸ hu))]
  exact hx u hu

/-! ### Swap invariance of a unit's conflict count -/

/-- If both `i` and `j` lie in `U`, the transposition `(i j)` maps `U` to itself. -/
theorem swap_mem_iff {U : Finset (Fin 81)} {i j : Fin 81} (hi : i ∈ U) (hj : j ∈ U)
    (u : Fin 81) : Equiv.swap i j u ∈ U ↔ u ∈ U := by
  by_cases hui : u = i
  · rw [hui, Equiv.swap_apply_left]
    exact ⟨fun _ => hi, fun _ => hj⟩
  · by_cases huj : u = j
    · rw [huj, Equiv.swap_apply_right]
      exact ⟨fun _ => hj, fun _ => hi⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hui huj]

theorem filter_swap_of_not_mem (U : Finset (Fin 81)) (x : Fin 81 → ℕ) {i j : Fin 81}
    (hi : i ∉ U) (hj : j ∉ U) (d : ℕ) :
    U.filter (fun u => swap x i j u = d) = U.filter (fun u => x u = d) := by
  refine Finset.filter_congr fun u hu => ?_
  rw [swap_apply_of_ne x (fun h : u = i => hi (h ▸ hu)) (fun h : u = j => hj (h ▸ hu))]

/-- A unit containing neither swapped cell is unchanged by the swap. -/
theorem conf_swap_of_not_mem (U : Finset (Fin 81)) (x : Fin 81 → ℕ) {i j : Fin 81}
    (hi : i ∉ U) (hj : j ∉ U) : conf U (swap x i j) = conf U x := by
  unfold conf
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [filter_swap_of_not_mem U x hi hj d]

theorem card_filter_swap_of_both_mem (U : Finset (Fin 81)) (x : Fin 81 → ℕ) {i j : Fin 81}
    (hi : i ∈ U) (hj : j ∈ U) (d : ℕ) :
    (U.filter (fun u => swap x i j u = d)).card = (U.filter (fun u => x u = d)).card := by
  refine Finset.card_nbij' (Equiv.swap i j) (Equiv.swap i j) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_coe, Finset.mem_filter] at hu ⊢
    exact ⟨(swap_mem_iff hi hj u).mpr hu.1, hu.2⟩
  · intro u hu
    simp only [Finset.mem_coe, Finset.mem_filter] at hu ⊢
    refine ⟨(swap_mem_iff hi hj u).mpr hu.1, ?_⟩
    rw [swap_apply, Equiv.swap_apply_self]
    exact hu.2
  · intro u _
    exact Equiv.swap_apply_self i j u
  · intro u _
    exact Equiv.swap_apply_self i j u

/-- A unit containing both swapped cells sees the same multiset of digits, so it
is unchanged by the swap. -/
theorem conf_swap_of_both_mem (U : Finset (Fin 81)) (x : Fin 81 → ℕ) {i j : Fin 81}
    (hi : i ∈ U) (hj : j ∈ U) : conf U (swap x i j) = conf U x := by
  unfold conf
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [card_filter_swap_of_both_mem U x hi hj d]

/-- A unit containing both swapped cells or neither of them is unchanged. -/
theorem conf_swap_of_mem_iff (U : Finset (Fin 81)) (x : Fin 81 → ℕ) {i j : Fin 81}
    (h : i ∈ U ↔ j ∈ U) : conf U (swap x i j) = conf U x := by
  by_cases hi : i ∈ U
  · exact conf_swap_of_both_mem U x hi (h.mp hi)
  · exact conf_swap_of_not_mem U x hi (fun hj => hi (h.mpr hj))

/-! ### Row terms -/

/-- A within-row swap preserves every row term. -/
theorem conf_rowCells_swap (x : Fin 81 → ℕ) {i j : Fin 81} (hrow : row i = row j)
    (r : Fin 9) : conf (rowCells r) (swap x i j) = conf (rowCells r) x := by
  apply conf_swap_of_mem_iff
  rw [mem_rowCells, mem_rowCells, hrow]

theorem image_swap_of_both_mem (U : Finset (Fin 81)) (x : Fin 81 → ℕ) {i j : Fin 81}
    (hi : i ∈ U) (hj : j ∈ U) : U.image (swap x i j) = U.image x := by
  ext v
  simp only [Finset.mem_image, swap_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨Equiv.swap i j u, (swap_mem_iff hi hj u).mpr hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨Equiv.swap i j u, (swap_mem_iff hi hj u).mpr hu, by rw [Equiv.swap_apply_self]⟩

theorem image_swap_of_not_mem (U : Finset (Fin 81)) (x : Fin 81 → ℕ) {i j : Fin 81}
    (hi : i ∉ U) (hj : j ∉ U) : U.image (swap x i j) = U.image x := by
  refine Finset.image_congr fun u hu => ?_
  have hu' : u ∈ U := hu
  exact swap_apply_of_ne x (fun h => hi (h ▸ hu')) (fun h => hj (h ▸ hu'))

/-- A within-row swap preserves the property "row `r` is a permutation of `1, …, 9`". -/
theorem rowIsPerm_swap {x : Fin 81 → ℕ} {i j : Fin 81} (hrow : row i = row j) {r : Fin 9}
    (h : RowIsPerm x r) : RowIsPerm (swap x i j) r := by
  unfold RowIsPerm at h ⊢
  rw [← h]
  by_cases hr : row i = r
  · exact image_swap_of_both_mem _ x (mem_rowCells.mpr hr)
      (mem_rowCells.mpr (hrow.symm.trans hr))
  · exact image_swap_of_not_mem _ x (fun hm => hr (mem_rowCells.mp hm))
      (fun hm => hr (hrow.trans (mem_rowCells.mp hm)))

/-- A within-row swap keeps the state on the row-permutation state space. -/
theorem rowsArePerms_swap {x : Fin 81 → ℕ} {i j : Fin 81} (hrow : row i = row j)
    (h : RowsArePerms x) : RowsArePerms (swap x i j) :=
  fun r => rowIsPerm_swap hrow (h r)

theorem injOn_of_rowIsPerm {x : Fin 81 → ℕ} {r : Fin 9} (h : RowIsPerm x r) :
    Set.InjOn x (rowCells r) := by
  rw [← Finset.card_image_iff, h, card_rowCells]
  simp

/-- A unit whose cells carry pairwise distinct digits has no conflicts. -/
theorem conf_eq_zero_of_injOn (U : Finset (Fin 81)) {x : Fin 81 → ℕ}
    (h : Set.InjOn x U) : conf U x = 0 := by
  unfold conf
  refine Finset.sum_eq_zero fun d _ => ?_
  apply Nat.choose_eq_zero_of_lt
  have hle : (U.filter (fun u => x u = d)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact h ha.1 hb.1 (ha.2.trans hb.2.symm)
  omega

/-- The row contribution of a permutation row is identically zero. -/
theorem conf_eq_zero_of_rowIsPerm {x : Fin 81 → ℕ} {r : Fin 9} (h : RowIsPerm x r) :
    conf (rowCells r) x = 0 :=
  conf_eq_zero_of_injOn _ (injOn_of_rowIsPerm h)

/-- On the row-permutation state space the full objective is exactly `H_cb`. -/
theorem H_eq_Hcb_of_rowsArePerms {x : Fin 81 → ℕ} (h : RowsArePerms x) : H x = Hcb x := by
  unfold H
  rw [Finset.sum_eq_zero fun r _ => conf_eq_zero_of_rowIsPerm (h r), zero_add]

/-- On the row-permutation state space, `H = H_cb` both before and after a
within-row swap. -/
theorem H_swap_eq_Hcb_swap {x : Fin 81 → ℕ} {i j : Fin 81} (hrow : row i = row j)
    (h : RowsArePerms x) : H (swap x i j) = Hcb (swap x i j) ∧ H x = Hcb x :=
  ⟨H_eq_Hcb_of_rowsArePerms (rowsArePerms_swap hrow h), H_eq_Hcb_of_rowsArePerms h⟩

/-- For a within-row swap the change in `H` equals the change in `H_cb`, on any
state (the row terms are individually unchanged). -/
theorem H_swap_sub_eq_Hcb_swap_sub (x : Fin 81 → ℕ) {i j : Fin 81} (hrow : row i = row j) :
    (H (swap x i j) : ℤ) - H x = (Hcb (swap x i j) : ℤ) - Hcb x := by
  unfold H
  simp only [conf_rowCells_swap x hrow]
  omega

/-! ### Column and box locality -/

/-- A column containing neither swapped cell is unchanged. -/
theorem conf_colCells_swap_of_not_mem (x : Fin 81 → ℕ) {i j : Fin 81} {c : Fin 9}
    (hc : c ∉ ({colIdx i, colIdx j} : Finset (Fin 9))) :
    conf (colCells c) (swap x i j) = conf (colCells c) x := by
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact conf_swap_of_not_mem _ x (fun h => hc.1 (colIdx_eq_of_mem h).symm)
    (fun h => hc.2 (colIdx_eq_of_mem h).symm)

/-- A box containing neither swapped cell is unchanged. -/
theorem conf_boxCells_swap_of_not_mem (x : Fin 81 → ℕ) {i j : Fin 81} {b : Fin 9}
    (hb : b ∉ ({boxIdx i, boxIdx j} : Finset (Fin 9))) :
    conf (boxCells b) (swap x i j) = conf (boxCells b) x := by
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  exact conf_swap_of_not_mem _ x (fun h => hb.1 (boxIdx_eq_of_mem h).symm)
    (fun h => hb.2 (boxIdx_eq_of_mem h).symm)

/-- If the swapped cells share a box, every box term is unchanged (the shared box
contains both cells, every other box contains neither). -/
theorem conf_boxCells_swap_of_box_eq (x : Fin 81 → ℕ) {i j : Fin 81} (hbox : box i = box j)
    (b : Fin 9) : conf (boxCells b) (swap x i j) = conf (boxCells b) x := by
  apply conf_swap_of_mem_iff
  rw [mem_boxCells, mem_boxCells, hbox]

/-! ### The locality lemma -/

theorem sum_eq_compl_add_pair {f : Fin 9 → ℕ} (a b : Fin 9) :
    ∑ k, f k =
      ∑ k ∈ ({a, b} : Finset (Fin 9))ᶜ, f k + ∑ k ∈ ({a, b} : Finset (Fin 9)), f k := by
  rw [add_comm, Finset.sum_add_sum_compl]

/-- `H_cb` split into the terms of the units not containing `i` or `j` and the
terms of the (at most two) columns and (at most two) boxes that do. -/
theorem Hcb_eq (x : Fin 81 → ℕ) (i j : Fin 81) :
    Hcb x =
      (∑ c ∈ ({colIdx i, colIdx j} : Finset (Fin 9))ᶜ, conf (colCells c) x
        + ∑ b ∈ ({boxIdx i, boxIdx j} : Finset (Fin 9))ᶜ, conf (boxCells b) x)
      + (∑ c ∈ ({colIdx i, colIdx j} : Finset (Fin 9)), conf (colCells c) x
        + ∑ b ∈ ({boxIdx i, boxIdx j} : Finset (Fin 9)), conf (boxCells b) x) := by
  unfold Hcb
  rw [sum_eq_compl_add_pair (f := fun c => conf (colCells c) x) (colIdx i) (colIdx j),
    sum_eq_compl_add_pair (f := fun b => conf (boxCells b) x) (boxIdx i) (boxIdx j)]
  ring

/-- **Locality of swaps for `H_cb`** (thesis `lem:row-swap-locality`, `ΔH_cb`
statement).  For two cells `i, j` in distinct columns, the change
`H_cb(swap x i j) − H_cb(x)` is determined entirely by the conflict counts of
the columns of `i` and `j` and of the one or two boxes containing `i` and `j`;
no other column or box term changes.  No row or permutation hypothesis is
needed. -/
theorem Hcb_swap_locality (x : Fin 81 → ℕ) {i j : Fin 81} (hcol : col i ≠ col j) :
    (Hcb (swap x i j) : ℤ) - Hcb x =
      ((conf (colCells (colIdx i)) (swap x i j) + conf (colCells (colIdx j)) (swap x i j)
          + ∑ b ∈ ({boxIdx i, boxIdx j} : Finset (Fin 9)), conf (boxCells b) (swap x i j) : ℕ)
        : ℤ)
      - ((conf (colCells (colIdx i)) x + conf (colCells (colIdx j)) x
          + ∑ b ∈ ({boxIdx i, boxIdx j} : Finset (Fin 9)), conf (boxCells b) x : ℕ)
        : ℤ) := by
  have hci : colIdx i ≠ colIdx j := fun h => hcol (congrArg Fin.val h)
  have hcols : ∑ c ∈ ({colIdx i, colIdx j} : Finset (Fin 9))ᶜ, conf (colCells c) (swap x i j)
      = ∑ c ∈ ({colIdx i, colIdx j} : Finset (Fin 9))ᶜ, conf (colCells c) x :=
    Finset.sum_congr rfl fun c hc => conf_colCells_swap_of_not_mem x (Finset.mem_compl.mp hc)
  have hboxes : ∑ b ∈ ({boxIdx i, boxIdx j} : Finset (Fin 9))ᶜ, conf (boxCells b) (swap x i j)
      = ∑ b ∈ ({boxIdx i, boxIdx j} : Finset (Fin 9))ᶜ, conf (boxCells b) x :=
    Finset.sum_congr rfl fun b hb => conf_boxCells_swap_of_not_mem x (Finset.mem_compl.mp hb)
  have h1 := Hcb_eq (swap x i j) i j
  have h2 := Hcb_eq x i j
  rw [hcols, hboxes, Finset.sum_pair hci] at h1
  rw [Finset.sum_pair hci] at h2
  omega

/-- **Locality of row swaps** (thesis `lem:row-swap-locality`).  For two cells of
the same row in distinct columns, the change of the full digit-restricted
objective `H` (row, column and box terms) is determined entirely by the
conflict counts of the two columns and the one or two boxes containing the
swapped cells.  The row hypothesis is what controls the row terms; the `H_cb`
part is `Hcb_swap_locality`. -/
theorem row_swap_locality (x : Fin 81 → ℕ) {i j : Fin 81} (hrow : row i = row j)
    (hcol : col i ≠ col j) :
    (H (swap x i j) : ℤ) - H x =
      ((conf (colCells (colIdx i)) (swap x i j) + conf (colCells (colIdx j)) (swap x i j)
          + ∑ b ∈ ({boxIdx i, boxIdx j} : Finset (Fin 9)), conf (boxCells b) (swap x i j) : ℕ)
        : ℤ)
      - ((conf (colCells (colIdx i)) x + conf (colCells (colIdx j)) x
          + ∑ b ∈ ({boxIdx i, boxIdx j} : Finset (Fin 9)), conf (boxCells b) x : ℕ)
        : ℤ) := by
  rw [H_swap_sub_eq_Hcb_swap_sub x hrow]
  exact Hcb_swap_locality x hcol

/-- When the two swapped cells share a box, the change in `H_cb` is carried by the
two column terms alone. -/
theorem Hcb_swap_locality_of_box_eq (x : Fin 81 → ℕ) {i j : Fin 81} (hcol : col i ≠ col j)
    (hbox : box i = box j) :
    (Hcb (swap x i j) : ℤ) - Hcb x =
      ((conf (colCells (colIdx i)) (swap x i j) + conf (colCells (colIdx j)) (swap x i j) : ℕ)
        : ℤ)
      - ((conf (colCells (colIdx i)) x + conf (colCells (colIdx j)) x : ℕ) : ℤ) := by
  have h := Hcb_swap_locality x hcol
  have hb : ∑ b ∈ ({boxIdx i, boxIdx j} : Finset (Fin 9)), conf (boxCells b) (swap x i j)
      = ∑ b ∈ ({boxIdx i, boxIdx j} : Finset (Fin 9)), conf (boxCells b) x :=
    Finset.sum_congr rfl fun b _ => conf_boxCells_swap_of_box_eq x hbox b
  rw [hb] at h
  omega

end PhdThesisLean.RowSwapLocality

#print axioms PhdThesisLean.RowSwapLocality.conf_swap_of_not_mem
#print axioms PhdThesisLean.RowSwapLocality.conf_swap_of_both_mem
#print axioms PhdThesisLean.RowSwapLocality.conf_rowCells_swap
#print axioms PhdThesisLean.RowSwapLocality.conf_eq_zero_of_rowIsPerm
#print axioms PhdThesisLean.RowSwapLocality.rowsArePerms_swap
#print axioms PhdThesisLean.RowSwapLocality.H_eq_Hcb_of_rowsArePerms
#print axioms PhdThesisLean.RowSwapLocality.H_swap_eq_Hcb_swap
#print axioms PhdThesisLean.RowSwapLocality.conf_boxCells_swap_of_box_eq
#print axioms PhdThesisLean.RowSwapLocality.Hcb_swap_locality
#print axioms PhdThesisLean.RowSwapLocality.row_swap_locality
#print axioms PhdThesisLean.RowSwapLocality.Hcb_swap_locality_of_box_eq
