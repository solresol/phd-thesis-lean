/-
  Formalisation of Lemma `lem:pow2-landscape` ("Plateaus, near-misses, and
  all-or-nothing progress") from the powers-of-two appendix of Greg Baker's
  PhD thesis, together with the `p = 7` inversion example that follows it.

  Thesis source: sudoku-via-padic-regression/body.tex
  Thesis labels: app:powers-two, lem:pow2-landscape
-/

import Mathlib

namespace PhdThesisLean.PowersOfTwoLandscape

/-!
# Plateaus, near-misses, and all-or-nothing progress

Formalises Lemma `lem:pow2-landscape` of the thesis section `app:powers-two`
(`/Users/gregb/Documents/devel/phd-thesis/sudoku-via-padic-regression/body.tex`,
around lines 1930–2000) and the `p = 7` inversion paragraph that follows it.

## Setting

The powers-of-two encoding assigns digit `k ∈ {1, …, 9}` the value `2^(k-1)`;
a unit (row, column, box) is correct iff its entries sum to
`1 + 2 + ⋯ + 256 = 2^9 - 1 = 511` (`target`, `target_eq_sum`), and the unit
residual is the integer `r_g(β) = 511 - Σ β` (`residual`).  A local move that
changes one entry of the unit from `2^b` to `2^a` changes the residual to
`r - ε` with `ε = 2^a - 2^b` (`eps`, `residual_move`).

The thesis writes `|·|_p` for the `p`-adic absolute value on the integers.
Here that is `padicNorm p (↑z : ℚ)`, the rational `p`-adic norm of the integer
cast; the exponent `v_p` is `padicValInt p`.

## Correspondence with the thesis

* (i) `padicNorm_eps` : `|ε|_p = |2^{|a-b|} - 1|_p`, with `|a - b|` realised as
  `gap a b = max a b - min a b` (`gap_eq_natAbs`).  The thesis assumes `a ≠ b`;
  the identity is proved for all `a b` (both sides are `|0|_p` when `a = b`),
  which is strictly stronger.  `padicNorm_eps_eq_one_iff_not_dvd` and
  `padicNorm_eps_eq_one_iff` give the criterion
  `|ε|_p = 1 ↔ ¬ p ∣ 2^{|a-b|} - 1 ↔ ¬ ord_p(2) ∣ |a - b|`.
  The orders `ord_p(2) = 10, 12, 11, 23, 9, 48` for
  `p = 11, 13, 23, 47, 73, 97` are verified by `decide`
  (`orderOf_two_zmod_*`), and `padicNorm_eps_eq_one_of_mem` /
  `padicNorm_eps_eq_one_of_gt` give the unit-step conclusion for those six
  primes and for every prime `p > 255` (the latter needs no oddness
  hypothesis).  The single-cell-error remark is `residual_single_error` and
  `padicNorm_residual_single_error`: a unit that agrees with a valid
  completion except in one cell has residual `-ε`, hence unit term `1`.
* (ii) `strict_decrease_iff` : for `r ≠ 0`,
  `|r - ε|_p < |r|_p ↔ p^(v_p(r)+1) ∣ r - ε`, including the degenerate case
  `r - ε = 0` (both sides hold).  `strict_decrease_iff_modEq` restates the
  right-hand side as `ε ≡ r [ZMOD p^(v_p(r)+1)]`, the form used in the thesis.
* (iii) `padicNorm_sub_eq_of_lt` (for rationals, hence stronger) and
  `padicNorm_residual_sub_eq` (for integer residuals):
  `|r|_p < |ε|_p → |r - ε|_p = |ε|_p`.  `padicNorm_sub_eq_one_of_dvd` is the
  highlighted special case: `ε` a unit and `p ∣ r` (which covers `r = 0` and
  `v_p(r) ≥ 1`, see `dvd_of_one_le_padicValInt`) gives `|r - ε|_p = 1`.
* `pow2_landscape` bundles (i)–(iii) for an odd prime `p`.
* The `p = 7` paragraph: `target_factor` (`511 = 7 · 73`),
  `orderOf_two_zmod_seven` (`ord_7(2) = 3`), `padicNorm_seven_target`
  (`|511|_7 = 1/7`), `padicNorm_seven_residual_le` (a unit sum divisible by
  `7` has term `≤ 1/7`), `padicNorm_seven_eps_three_zero` (`|2^3 - 2^0|_7 =
  1/7`, a gap-`3` step discounted because `ord_7(2) = 3`), and
  `seven_inversion`: the near-miss unit (eight correct entries, `1` in place of
  `256`) has residual `255` and term `1`, while the scrambled multiset
  `(8,4,2,2,1,1,1,1,1)` sums to `21`, has residual `490 = 2·5·7²` and term
  `1/49`, so the near-miss is scored `49` times worse.

Only the integer arithmetic of a single unit is modelled, exactly as in the
lemma; the Sudoku grid structure (which cells lie in which units) is not
needed for the statement and is not formalised here.
-/

open scoped BigOperators

/-- The target unit sum `1 + 2 + ⋯ + 256 = 2^9 - 1 = 511`. -/
def target : ℤ := 511

/-- The target is the sum of the nine encoded digit values `2^0, …, 2^8`. -/
theorem target_eq_sum : target = ∑ k ∈ Finset.range 9, (2 : ℤ) ^ k := by
  decide

/-- The residual of a unit whose entries sum to `S`: `r_g(β) = 511 - Σ β`. -/
def residual (S : ℤ) : ℤ := target - S

/-- The residual change `ε = 2^a - 2^b` of a move replacing the entry `2^b` by `2^a`. -/
def eps (a b : ℕ) : ℤ := (2 : ℤ) ^ a - 2 ^ b

/-- The digit gap `|a - b|`, as a natural number. -/
def gap (a b : ℕ) : ℕ := max a b - min a b

theorem gap_eq_natAbs (a b : ℕ) : gap a b = ((a : ℤ) - b).natAbs := by
  unfold gap; omega

theorem gap_comm (a b : ℕ) : gap a b = gap b a := by
  unfold gap; omega

/-- A move replacing one entry `2^b` of the unit by `2^a` sends the residual `r` to `r - ε`. -/
theorem residual_move (S : ℤ) (a b : ℕ) :
    residual (S - 2 ^ b + 2 ^ a) = residual S - eps a b := by
  unfold residual eps; ring

/-- A unit agreeing with a valid completion (sum `511`) except in one cell, where
`2^b` has been replaced by `2^a`, has residual `-ε`. -/
theorem residual_single_error (a b : ℕ) :
    residual (target - 2 ^ b + 2 ^ a) = -eps a b := by
  unfold residual eps; ring

/-- `ε ≠ 0` when the two digits differ. -/
theorem eps_ne_zero {a b : ℕ} (hab : a ≠ b) : eps a b ≠ 0 := by
  unfold eps
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact sub_ne_zero.mpr (ne_of_lt (pow_lt_pow_right₀ (by norm_num) h))
  · exact sub_ne_zero.mpr (ne_of_gt (pow_lt_pow_right₀ (by norm_num) h))

/-- `|ε| ≤ 255` for digit exponents `a, b ≤ 8`. -/
theorem abs_eps_le {a b : ℕ} (ha : a ≤ 8) (hb : b ≤ 8) : |eps a b| ≤ 255 := by
  unfold eps
  have h1 : (2 : ℤ) ^ a ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) ha
  have h2 : (2 : ℤ) ^ b ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) hb
  have h3 : (1 : ℤ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
  have h4 : (1 : ℤ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  norm_num at h1 h2
  rw [abs_le]
  constructor <;> linarith

section OddPrime

variable {p : ℕ} [hp : Fact p.Prime]

/-- An odd prime does not divide `2`. -/
theorem not_dvd_two (hodd : p ≠ 2) : ¬ (p : ℤ) ∣ 2 := by
  intro h
  have h2 : p ∣ 2 := by exact_mod_cast h
  exact hodd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2)

/-- For an odd prime `p`, every power of two is a `p`-adic unit: `|2^n|_p = 1`. -/
theorem padicNorm_two_pow (hodd : p ≠ 2) (n : ℕ) :
    padicNorm p (((2 : ℤ) ^ n : ℤ) : ℚ) = 1 := by
  rw [padicNorm.int_eq_one_iff]
  intro h
  exact not_dvd_two hodd ((Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow h)

/-- **(i), identity.** `|2^a - 2^b|_p = |2^{|a-b|} - 1|_p` for an odd prime `p`
(for all `a b`, not only `a ≠ b`). -/
theorem padicNorm_eps (hodd : p ≠ 2) (a b : ℕ) :
    padicNorm p (eps a b : ℚ) = padicNorm p (((2 : ℤ) ^ gap a b - 1 : ℤ) : ℚ) := by
  rcases le_total a b with h | h
  · have hg : gap a b = b - a := by unfold gap; omega
    have hpow : (2 : ℤ) ^ b = 2 ^ a * 2 ^ (b - a) := by
      rw [← pow_add, Nat.add_sub_of_le h]
    have he : eps a b = -((2 : ℤ) ^ a * (2 ^ (b - a) - 1)) := by
      unfold eps; rw [hpow]; ring
    rw [hg, he, Int.cast_neg, padicNorm.neg, Int.cast_mul, padicNorm.mul,
      padicNorm_two_pow hodd, one_mul]
  · have hg : gap a b = a - b := by unfold gap; omega
    have hpow : (2 : ℤ) ^ a = 2 ^ b * 2 ^ (a - b) := by
      rw [← pow_add, Nat.add_sub_of_le h]
    have he : eps a b = (2 : ℤ) ^ b * (2 ^ (a - b) - 1) := by
      unfold eps; rw [hpow]; ring
    rw [hg, he, Int.cast_mul, padicNorm.mul, padicNorm_two_pow hodd, one_mul]

/-- `p ∣ 2^d - 1` iff the multiplicative order of `2` modulo `p` divides `d`. -/
theorem int_dvd_two_pow_sub_one_iff (d : ℕ) :
    (p : ℤ) ∣ (2 : ℤ) ^ d - 1 ↔ orderOf (2 : ZMod p) ∣ d := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, orderOf_dvd_iff_pow_eq_one]
  push_cast
  exact sub_eq_zero

/-- **(i), criterion (divisibility form).** `|ε|_p = 1 ↔ ¬ p ∣ 2^{|a-b|} - 1`. -/
theorem padicNorm_eps_eq_one_iff_not_dvd (hodd : p ≠ 2) (a b : ℕ) :
    padicNorm p (eps a b : ℚ) = 1 ↔ ¬ (p : ℤ) ∣ (2 : ℤ) ^ gap a b - 1 := by
  rw [padicNorm_eps hodd, padicNorm.int_eq_one_iff]

/-- **(i), criterion (order form).** `|ε|_p = 1 ↔ ¬ ord_p(2) ∣ |a - b|`. -/
theorem padicNorm_eps_eq_one_iff (hodd : p ≠ 2) (a b : ℕ) :
    padicNorm p (eps a b : ℚ) = 1 ↔ ¬ orderOf (2 : ZMod p) ∣ gap a b := by
  rw [padicNorm_eps_eq_one_iff_not_dvd hodd, int_dvd_two_pow_sub_one_iff]

/-- If `ord_p(2) > 8` then every move between distinct digit exponents `≤ 8` is a
`p`-adic unit step. -/
theorem padicNorm_eps_eq_one_of_orderOf_gt (hodd : p ≠ 2)
    (hord : 8 < orderOf (2 : ZMod p)) {a b : ℕ} (ha : a ≤ 8) (hb : b ≤ 8) (hab : a ≠ b) :
    padicNorm p (eps a b : ℚ) = 1 := by
  rw [padicNorm_eps_eq_one_iff hodd]
  intro hdvd
  have hpos : 0 < gap a b := by unfold gap; omega
  have hle : gap a b ≤ 8 := by unfold gap; omega
  have := Nat.le_of_dvd hpos hdvd
  omega

/-- For a prime `p > 255 ≥ |ε|`, every move between distinct digit exponents `≤ 8`
is a `p`-adic unit step (no oddness hypothesis is needed). -/
theorem padicNorm_eps_eq_one_of_gt (hgt : 255 < p) {a b : ℕ} (ha : a ≤ 8) (hb : b ≤ 8)
    (hab : a ≠ b) : padicNorm p (eps a b : ℚ) = 1 := by
  rw [padicNorm.int_eq_one_iff]
  intro hdvd
  apply eps_ne_zero hab
  apply Int.eq_zero_of_abs_lt_dvd hdvd
  have h1 := abs_eps_le ha hb
  have h2 : (255 : ℤ) < p := by exact_mod_cast hgt
  linarith

omit hp in
/-- The unit term is insensitive to the sign of the residual. -/
theorem padicNorm_neg_eps (a b : ℕ) :
    padicNorm p ((-eps a b : ℤ) : ℚ) = padicNorm p (eps a b : ℚ) := by
  rw [Int.cast_neg, padicNorm.neg]

omit hp in
/-- **(i), single-cell error.** If the move `2^b ↦ 2^a` is a unit step, a unit that
agrees with a valid completion except in that one cell has unit term exactly `1`. -/
theorem padicNorm_residual_single_error {a b : ℕ} (hunit : padicNorm p (eps a b : ℚ) = 1) :
    padicNorm p (residual (target - 2 ^ b + 2 ^ a) : ℚ) = 1 := by
  rw [residual_single_error, Int.cast_neg, padicNorm.neg, hunit]

/-- A unit term equals `1` exactly when the unit sum is coprime to `p`: the scoring
cannot distinguish a one-cell error from an arbitrary sum coprime to `p`. -/
theorem padicNorm_residual_eq_one_iff (S : ℤ) :
    padicNorm p (residual S : ℚ) = 1 ↔ ¬ (p : ℤ) ∣ residual S :=
  padicNorm.int_eq_one_iff _

/-- A nonzero integer has positive `p`-adic norm. -/
theorem padicNorm_pos_of_ne_zero {r : ℤ} (hr : r ≠ 0) : 0 < padicNorm p (r : ℚ) :=
  lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero (by exact_mod_cast hr)).symm

/-- **(ii).** For `r ≠ 0`, the move strictly decreases the unit term iff
`p^(v_p(r)+1) ∣ r - ε`, i.e. iff the move reproduces the leading `p`-adic digit of
the residual.  (When `r - ε = 0` both sides hold.) -/
theorem strict_decrease_iff (r ε : ℤ) (hr : r ≠ 0) :
    padicNorm p ((r - ε : ℤ) : ℚ) < padicNorm p (r : ℚ) ↔
      (p : ℤ) ^ (padicValInt p r + 1) ∣ r - ε := by
  by_cases hs : r - ε = 0
  · rw [hs]
    simp only [Int.cast_zero, padicNorm.zero, dvd_zero, iff_true]
    exact padicNorm_pos_of_ne_zero hr
  · have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
    rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hs),
      padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hr),
      zpow_lt_zpow_iff_right₀ hp1, neg_lt_neg_iff, padicValRat.of_int, padicValRat.of_int,
      padicValInt_dvd_iff]
    simp only [hs, false_or]
    constructor <;> intro h <;> omega

/-- **(ii), congruence form.** `|r - ε|_p < |r|_p ↔ ε ≡ r (mod p^(v_p(r)+1))`. -/
theorem strict_decrease_iff_modEq (r ε : ℤ) (hr : r ≠ 0) :
    padicNorm p ((r - ε : ℤ) : ℚ) < padicNorm p (r : ℚ) ↔
      ε ≡ r [ZMOD (p : ℤ) ^ (padicValInt p r + 1)] := by
  rw [strict_decrease_iff r ε hr, Int.modEq_iff_dvd]

/-- **(iii), rational form.** If `|q|_p < |s|_p` then `|q - s|_p = |s|_p`. -/
theorem padicNorm_sub_eq_of_lt {q s : ℚ} (h : padicNorm p q < padicNorm p s) :
    padicNorm p (q - s) = padicNorm p s := by
  rw [sub_eq_add_neg, padicNorm.add_eq_max_of_ne, padicNorm.neg, max_eq_right h.le]
  rw [padicNorm.neg]
  exact h.ne

/-- **(iii).** If `|r|_p < |ε|_p` then `|r - ε|_p = |ε|_p`: one move erases all the
valuation accumulated on the unit. -/
theorem padicNorm_residual_sub_eq {r ε : ℤ} (h : padicNorm p (r : ℚ) < padicNorm p (ε : ℚ)) :
    padicNorm p ((r - ε : ℤ) : ℚ) = padicNorm p (ε : ℚ) := by
  rw [Int.cast_sub]
  exact padicNorm_sub_eq_of_lt h

/-- `v_p(r) ≥ 1` implies `p ∣ r`. -/
theorem dvd_of_one_le_padicValInt {r : ℤ} (h : 1 ≤ padicValInt p r) : (p : ℤ) ∣ r := by
  have := (padicValInt_dvd_iff 1 r).mpr (Or.inr h)
  simpa using this

/-- **(iii), highlighted case.** If `ε` is a `p`-adic unit and the unit sum is exactly
(`r = 0`) or approximately (`p ∣ r`, i.e. `v_p(r) ≥ 1`) satisfied, then the move
produces a unit term of `1`. -/
theorem padicNorm_sub_eq_one_of_dvd {r ε : ℤ} (hr : (p : ℤ) ∣ r)
    (hε : padicNorm p (ε : ℚ) = 1) : padicNorm p ((r - ε : ℤ) : ℚ) = 1 := by
  rw [padicNorm_residual_sub_eq, hε]
  rw [hε]
  exact (padicNorm.int_lt_one_iff r).mpr hr

end OddPrime

/-! ### The multiplicative orders of `2` modulo the sweep primes -/

theorem orderOf_two_zmod_seven : orderOf (2 : ZMod 7) = 3 :=
  (orderOf_eq_iff (by norm_num)).mpr (by decide)

theorem orderOf_two_zmod_eleven : orderOf (2 : ZMod 11) = 10 :=
  (orderOf_eq_iff (by norm_num)).mpr (by decide)

theorem orderOf_two_zmod_thirteen : orderOf (2 : ZMod 13) = 12 :=
  (orderOf_eq_iff (by norm_num)).mpr (by decide)

theorem orderOf_two_zmod_twentyThree : orderOf (2 : ZMod 23) = 11 :=
  (orderOf_eq_iff (by norm_num)).mpr (by decide)

theorem orderOf_two_zmod_fortySeven : orderOf (2 : ZMod 47) = 23 :=
  (orderOf_eq_iff (by norm_num)).mpr (by decide)

theorem orderOf_two_zmod_seventyThree : orderOf (2 : ZMod 73) = 9 :=
  (orderOf_eq_iff (by norm_num)).mpr (by decide)

theorem orderOf_two_zmod_ninetySeven : orderOf (2 : ZMod 97) = 48 :=
  (orderOf_eq_iff (by norm_num)).mpr (by decide)

section SweepPrimes

variable {p : ℕ} [hp : Fact p.Prime]

/-- **(i), the six sweep primes.** For `p ∈ {11, 13, 23, 47, 73, 97}` (orders
`10, 12, 11, 23, 9, 48`, all `> 8`), every move between distinct digit exponents
`≤ 8` is a `p`-adic unit step. -/
theorem padicNorm_eps_eq_one_of_mem (hmem : p ∈ ({11, 13, 23, 47, 73, 97} : Finset ℕ))
    {a b : ℕ} (ha : a ≤ 8) (hb : b ≤ 8) (hab : a ≠ b) : padicNorm p (eps a b : ℚ) = 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact padicNorm_eps_eq_one_of_orderOf_gt (by norm_num)
      (by rw [orderOf_two_zmod_eleven]; norm_num) ha hb hab
  · exact padicNorm_eps_eq_one_of_orderOf_gt (by norm_num)
      (by rw [orderOf_two_zmod_thirteen]; norm_num) ha hb hab
  · exact padicNorm_eps_eq_one_of_orderOf_gt (by norm_num)
      (by rw [orderOf_two_zmod_twentyThree]; norm_num) ha hb hab
  · exact padicNorm_eps_eq_one_of_orderOf_gt (by norm_num)
      (by rw [orderOf_two_zmod_fortySeven]; norm_num) ha hb hab
  · exact padicNorm_eps_eq_one_of_orderOf_gt (by norm_num)
      (by rw [orderOf_two_zmod_seventyThree]; norm_num) ha hb hab
  · exact padicNorm_eps_eq_one_of_orderOf_gt (by norm_num)
      (by rw [orderOf_two_zmod_ninetySeven]; norm_num) ha hb hab

/-- **Lemma `lem:pow2-landscape`** (plateaus, near-misses, all-or-nothing progress),
for an odd prime `p`.

1. `|ε|_p = |2^{|a-b|} - 1|_p`, and `|ε|_p = 1 ↔ ¬ ord_p(2) ∣ |a - b|`;
2. for `p ∈ {11, 13, 23, 47, 73, 97}` or `p > 255`, every move between distinct
   digit exponents `≤ 8` is a unit step;
3. for `r ≠ 0`, `|r - ε|_p < |r|_p ↔ p^(v_p(r)+1) ∣ r - ε`;
4. `|r|_p < |ε|_p → |r - ε|_p = |ε|_p`. -/
theorem pow2_landscape (hodd : p ≠ 2) :
    (∀ a b : ℕ,
        padicNorm p (eps a b : ℚ) = padicNorm p (((2 : ℤ) ^ gap a b - 1 : ℤ) : ℚ) ∧
        (padicNorm p (eps a b : ℚ) = 1 ↔ ¬ orderOf (2 : ZMod p) ∣ gap a b)) ∧
    (p ∈ ({11, 13, 23, 47, 73, 97} : Finset ℕ) ∨ 255 < p →
        ∀ a b : ℕ, a ≤ 8 → b ≤ 8 → a ≠ b → padicNorm p (eps a b : ℚ) = 1) ∧
    (∀ r ε : ℤ, r ≠ 0 →
        (padicNorm p ((r - ε : ℤ) : ℚ) < padicNorm p (r : ℚ) ↔
          (p : ℤ) ^ (padicValInt p r + 1) ∣ r - ε)) ∧
    (∀ r ε : ℤ, padicNorm p (r : ℚ) < padicNorm p (ε : ℚ) →
        padicNorm p ((r - ε : ℤ) : ℚ) = padicNorm p (ε : ℚ)) := by
  refine ⟨fun a b => ⟨padicNorm_eps hodd a b, padicNorm_eps_eq_one_iff hodd a b⟩, ?_,
    fun r ε hr => strict_decrease_iff r ε hr, fun r ε h => padicNorm_residual_sub_eq h⟩
  rintro (hmem | hgt) a b ha hb hab
  · exact padicNorm_eps_eq_one_of_mem hmem ha hb hab
  · exact padicNorm_eps_eq_one_of_gt hgt ha hb hab

end SweepPrimes

/-! ### The `p = 7` inversion example -/

section Seven

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- `511 = 7 · 73`: the target itself is `7`-adically small. -/
theorem target_factor : target = 7 * 73 := by decide

/-- `|511|_7 = 1/7`. -/
theorem padicNorm_seven_target : padicNorm 7 (target : ℚ) = (7 : ℚ)⁻¹ := by
  rw [target_factor, Int.cast_mul, padicNorm.mul,
    (padicNorm.int_eq_one_iff (p := 7) 73).mpr (by decide), mul_one]
  exact_mod_cast padicNorm.padicNorm_p (p := 7) (by norm_num)

/-- Any unit whose sum is divisible by `7` has unit term `≤ 1/7`. -/
theorem padicNorm_seven_residual_le {S : ℤ} (hS : (7 : ℤ) ∣ S) :
    padicNorm 7 (residual S : ℚ) ≤ (7 : ℚ)⁻¹ := by
  have hd : ((7 ^ 1 : ℕ) : ℤ) ∣ residual S := by
    unfold residual
    exact dvd_sub (by decide : ((7 ^ 1 : ℕ) : ℤ) ∣ target) (by simpa using hS)
  have := (padicNorm.dvd_iff_norm_le (p := 7)).mp hd
  simpa using this

/-- The gap-`3` step `2^3 - 2^0 = 7` is discounted at `p = 7` because `ord_7(2) = 3 ∣ 3`. -/
theorem padicNorm_seven_eps_three_zero : padicNorm 7 (eps 3 0 : ℚ) = (7 : ℚ)⁻¹ := by
  rw [show eps 3 0 = 7 by decide]
  exact_mod_cast padicNorm.padicNorm_p (p := 7) (by norm_num)

/-- Consistency check with the general criterion: `|eps 3 0|_7 ≠ 1` since `ord_7(2) ∣ 3`. -/
theorem padicNorm_seven_eps_three_zero_ne_one : padicNorm 7 (eps 3 0 : ℚ) ≠ 1 := by
  intro h
  rw [padicNorm_eps_eq_one_iff (p := 7) (by norm_num), orderOf_two_zmod_seven] at h
  exact h (by decide)

/-- The near-miss unit: eight correct entries and `2^0 = 1` in place of `2^8 = 256`
has residual `255 = 3 · 5 · 17`. -/
theorem nearMiss_residual : residual (target - 2 ^ 8 + 2 ^ 0) = 255 := by decide

/-- The scrambled multiset `(8, 4, 2, 2, 1, 1, 1, 1, 1)` sums to `21` and has residual
`490 = 2 · 5 · 7²`. -/
theorem scrambled_residual : residual (8 + 4 + 2 + 2 + 1 + 1 + 1 + 1 + 1) = 490 := by decide

/-- `|255|_7 = 1`. -/
theorem padicNorm_seven_nearMiss : padicNorm 7 ((255 : ℤ) : ℚ) = 1 :=
  (padicNorm.int_eq_one_iff (p := 7) 255).mpr (by decide)

/-- `|490|_7 = 1/49`. -/
theorem padicNorm_seven_scrambled : padicNorm 7 ((490 : ℤ) : ℚ) = 1 / 49 := by
  have h7 : padicNorm 7 ((7 : ℤ) : ℚ) = (7 : ℚ)⁻¹ := by
    exact_mod_cast padicNorm.padicNorm_p (p := 7) (by norm_num)
  have h10 : padicNorm 7 ((10 : ℤ) : ℚ) = 1 :=
    (padicNorm.int_eq_one_iff (p := 7) 10).mpr (by decide)
  rw [show ((490 : ℤ) : ℚ) = ((7 : ℤ) : ℚ) * (((7 : ℤ) : ℚ) * ((10 : ℤ) : ℚ)) by norm_num,
    padicNorm.mul, padicNorm.mul, h7, h10]
  norm_num

/-- **The `p = 7` inversion.** The near-miss unit (residual `255`, eight of nine cells
correct) receives term `1`, while the scrambled unit (residual `490`) receives term
`1/49`: the near-miss is ranked forty-nine times worse than noise. -/
theorem seven_inversion :
    padicNorm 7 (residual (target - 2 ^ 8 + 2 ^ 0) : ℚ) =
      49 * padicNorm 7 (residual (8 + 4 + 2 + 2 + 1 + 1 + 1 + 1 + 1) : ℚ) := by
  rw [nearMiss_residual, scrambled_residual, padicNorm_seven_nearMiss, padicNorm_seven_scrambled]
  norm_num

end Seven

#print axioms pow2_landscape
#print axioms padicNorm_eps
#print axioms padicNorm_eps_eq_one_iff
#print axioms padicNorm_eps_eq_one_of_mem
#print axioms padicNorm_eps_eq_one_of_gt
#print axioms padicNorm_residual_single_error
#print axioms strict_decrease_iff
#print axioms strict_decrease_iff_modEq
#print axioms padicNorm_residual_sub_eq
#print axioms padicNorm_sub_eq_one_of_dvd
#print axioms seven_inversion
#print axioms padicNorm_seven_target
#print axioms orderOf_two_zmod_seven

end PhdThesisLean.PowersOfTwoLandscape
