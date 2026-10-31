import PhdThesisLean.RationalWitnessEncoding
import PhdThesisLean.PadicValuationMachine

/-!
# Exact fraction evaluation with polynomial intermediate widths

An unreduced signed numerator and positive denominator suffice for every
verifier operation. No gcd or fraction normalization is required. We prove
the exact residual/loss semantics and bounds for every accumulation prefix,
norm power and comparison cross-product in the combined input/certificate
length. These are arithmetic correctness and bit-size results, not a complete
finite-machine runtime theorem or NP-membership theorem.
-/

namespace PhdThesisLean.RationalVerifierBounds

open scoped BigOperators Matrix
open RationalWitnessBounds RationalWitnessEncoding

set_option backward.isDefEq.respectTransparency false

structure Fraction where
  num : ℤ
  den : ℕ
  positive : 0 < den

namespace Fraction

def value (x : Fraction) : ℚ := x.num / x.den
def ofRat (q : ℚ) : Fraction := ⟨q.num, q.den, q.den_pos⟩
def zero : Fraction := ⟨0, 1, by decide⟩
def add (x y : Fraction) : Fraction :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den, Nat.mul_pos x.positive y.positive⟩
def neg (x : Fraction) : Fraction := ⟨-x.num, x.den, x.positive⟩
def sub (x y : Fraction) : Fraction := x.add y.neg
def mul (x y : Fraction) : Fraction :=
  ⟨x.num * y.num, x.den * y.den, Nat.mul_pos x.positive y.positive⟩
def le (x y : Fraction) : Bool := decide (x.num * y.den ≤ y.num * x.den)

@[simp] theorem value_ofRat (q : ℚ) : (ofRat q).value = q := Rat.num_div_den q
@[simp] theorem value_zero : zero.value = 0 := by simp [value, zero]
@[simp] theorem value_add (x y : Fraction) : (x.add y).value = x.value + y.value := by
  have hx : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.positive.ne'
  have hy : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.positive.ne'
  simp only [value, add, Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  field_simp
@[simp] theorem value_neg (x : Fraction) : x.neg.value = -x.value := by
  simp [value, neg, neg_div]
@[simp] theorem value_sub (x y : Fraction) : (x.sub y).value = x.value - y.value := by
  simp [sub, sub_eq_add_neg]
@[simp] theorem value_mul (x y : Fraction) : (x.mul y).value = x.value * y.value := by
  simp [value, mul, div_mul_div_comm]

theorem le_correct (x y : Fraction) : x.le y = true ↔ x.value ≤ y.value := by
  have hx : (0 : ℚ) < x.den := by exact_mod_cast x.positive
  have hy : (0 : ℚ) < y.den := by exact_mod_cast y.positive
  simp only [le, decide_eq_true_eq, value, div_le_div_iff₀ hx hy]
  exact_mod_cast (Iff.rfl : x.num * (y.den : ℤ) ≤ y.num * x.den ↔
    x.num * (y.den : ℤ) ≤ y.num * x.den)

/-- Both stored fields, without reducing their common factors. -/
def Bounded (x : Fraction) (h : ℕ) : Prop := x.num.natAbs.size ≤ h ∧ x.den.size ≤ h

theorem Bounded.mono {x : Fraction} {a b : ℕ} (hx : x.Bounded a) (h : a ≤ b) :
    x.Bounded b := ⟨hx.1.trans h, hx.2.trans h⟩

theorem bounded_zero : zero.Bounded 1 := by norm_num [Bounded, zero]

theorem bounded_ofRat (q : ℚ) : (ofRat q).Bounded (ratBits q) := by
  simp only [Bounded, ofRat, ratBits]
  omega

theorem size_mul (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  nlinarith

theorem size_add (a b : ℕ) : (a + b).size ≤ max a.size b.size + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ max a.size b.size :=
    Nat.size_le.mp (Nat.le_max_left _ _)
  have hb : b < 2 ^ max a.size b.size :=
    Nat.size_le.mp (Nat.le_max_right _ _)
  rw [pow_succ]
  omega

theorem bounded_mul {x y : Fraction} {a b : ℕ} (hx : x.Bounded a) (hy : y.Bounded b) :
    (x.mul y).Bounded (a + b) := by
  have hn := size_mul x.num.natAbs y.num.natAbs
  have hd := size_mul x.den y.den
  simp only [Bounded, mul, Int.natAbs_mul]
  exact ⟨hn.trans (Nat.add_le_add hx.1 hy.1), hd.trans (Nat.add_le_add hx.2 hy.2)⟩

theorem bounded_neg {x : Fraction} {a : ℕ} (hx : x.Bounded a) : x.neg.Bounded a := by
  simpa [Bounded, neg] using hx

theorem bounded_add {x y : Fraction} {a b : ℕ} (hx : x.Bounded a) (hy : y.Bounded b) :
    (x.add y).Bounded (a + b + 1) := by
  have h₁ : (x.num * (y.den : ℤ)).natAbs.size ≤ a + b := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
      (size_mul x.num.natAbs y.den).trans (Nat.add_le_add hx.1 hy.2)
  have h₂ : (y.num * (x.den : ℤ)).natAbs.size ≤ a + b := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast, Nat.add_comm] using
      (size_mul y.num.natAbs x.den).trans (Nat.add_le_add hy.1 hx.2)
  have hn := (Nat.size_le_size (Int.natAbs_add_le (x.num * y.den) (y.num * x.den))).trans
    (size_add (x.num * (y.den : ℤ)).natAbs (y.num * (x.den : ℤ)).natAbs)
  have hd := (size_mul x.den y.den).trans (Nat.add_le_add hx.2 hy.2)
  exact ⟨hn.trans (by omega), hd.trans (by omega)⟩

theorem bounded_sub {x y : Fraction} {a b : ℕ} (hx : x.Bounded a) (hy : y.Bounded b) :
    (x.sub y).Bounded (a + b + 1) := bounded_add hx (bounded_neg hy)

/-- The actual signed integers compared, not just the Boolean result. -/
theorem cross_products_bounded {x y : Fraction} {a b : ℕ}
    (hx : x.Bounded a) (hy : y.Bounded b) :
    (x.num * (y.den : ℤ)).natAbs.size ≤ a + b ∧
      (y.num * (x.den : ℤ)).natAbs.size ≤ a + b := by
  simp only [Int.natAbs_mul, Int.natAbs_natCast]
  exact ⟨(size_mul _ _).trans (Nat.add_le_add hx.1 hy.2),
    (size_mul _ _).trans (by have := hy.1; have := hx.2; omega)⟩

/-- Concrete raw storage: signed framed numerator and framed denominator. -/
def encode (x : Fraction) : List Bool :=
  SmithEncoding.encodeInt x.num ++ LeanNPHardness.BinaryNatLists.encodeNat x.den

theorem encode_length (x : Fraction) :
    x.encode.length = 2 * x.num.natAbs.size + 2 * x.den.size + 3 := by
  simp [encode, SmithEncoding.encodeInt_length, LeanNPHardness.BinaryNatLists.natWireSize,
    LeanNPHardness.BinaryNatLists.encodeNat_length_eq_size]
  omega

theorem encode_length_le {x : Fraction} {h : ℕ} (hx : x.Bounded h) :
    x.encode.length ≤ 4 * h + 3 := by
  rw [encode_length]
  have := hx.1
  have := hx.2
  omega

variable (p : ℕ) [Fact p.Prime]

/-- Two nonnegative valuations avoid signed exponent arithmetic. -/
def norm (x : Fraction) : Fraction :=
  if x.num = 0 then zero else
    ⟨(p ^ padicValNat p x.den : ℕ), p ^ padicValNat p x.num.natAbs,
      pow_pos (Fact.out : p.Prime).pos _⟩

theorem value_norm (x : Fraction) : (x.norm p).value = padicNorm p x.value := by
  by_cases hn : x.num = 0
  · simp [norm, hn, value, zero]
  · have hnq : (x.num : ℚ) ≠ 0 := by exact_mod_cast hn
    have hdq : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.positive.ne'
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    simp only [norm, hn, ↓reduceIte, value, Nat.cast_pow]
    rw [padicNorm.eq_zpow_of_nonzero (div_ne_zero hnq hdq),
      padicValRat.div hnq hdq, padicValRat.of_int, padicValRat.of_nat, padicValInt]
    rw [neg_sub, zpow_sub₀ hpq]
    simp

theorem size_pow_le (n k : ℕ) : (n ^ k).size ≤ n.size * k + 1 := by
  have h : n ^ k ≤ 2 ^ (n.size * k) := by
    calc
      n ^ k ≤ (2 ^ n.size) ^ k := Nat.pow_le_pow_left (Nat.lt_size_self n).le k
      _ = _ := by rw [pow_mul]
  simpa only [Nat.size_pow] using Nat.size_le_size h

theorem bounded_norm {x : Fraction} {h : ℕ} (hx : x.Bounded h) :
    (x.norm p).Bounded (p.size * h + 1) := by
  have hn := PadicValuationMachine.valuation_le_size p x.num.natAbs
  have hd := PadicValuationMachine.valuation_le_size p x.den
  by_cases hz : x.num = 0
  · simpa [norm, hz] using bounded_zero.mono (show 1 ≤ p.size * h + 1 by omega)
  · simp only [norm, hz, ↓reduceIte, Bounded, Int.natAbs_natCast]
    exact ⟨(size_pow_le p _).trans (by nlinarith [hx.2]),
      (size_pow_le p _).trans (by nlinarith [hx.1])⟩

end Fraction

open Fraction

/-- Left accumulation makes the bounds apply to each execution prefix. -/
def sum (xs : List Fraction) : Fraction := xs.foldl Fraction.add Fraction.zero

theorem value_fold_add (xs : List Fraction) (z : Fraction) :
    (xs.foldl Fraction.add z).value = z.value + (xs.map Fraction.value).sum := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc]

theorem bounded_fold_add (xs : List Fraction) {z : Fraction} {a h : ℕ}
    (hz : z.Bounded a) (hx : ∀ x ∈ xs, x.Bounded h) :
    (xs.foldl Fraction.add z).Bounded (a + xs.length * (h + 1)) := by
  induction xs generalizing z a with
  | nil => simpa using hz
  | cons x xs ih =>
      have hh := ih (bounded_add hz (hx x (by simp))) (fun y hy => hx y (by simp [hy]))
      simpa only [List.foldl_cons, List.length_cons] using
        (show (xs.foldl Fraction.add (z.add x)).Bounded (a + (xs.length + 1) * (h + 1)) from
          hh.mono (by nlinarith))

theorem bounded_fold_sub (xs : List Fraction) {z : Fraction} {a h : ℕ}
    (hz : z.Bounded a) (hx : ∀ x ∈ xs, x.Bounded h) :
    (xs.foldl Fraction.sub z).Bounded (a + xs.length * (h + 1)) := by
  induction xs generalizing z a with
  | nil => simpa using hz
  | cons x xs ih =>
      have hh := ih (bounded_sub hz (hx x (by simp))) (fun y hy => hx y (by simp [hy]))
      simpa only [List.foldl_cons, List.length_cons] using
        (show (xs.foldl Fraction.sub (z.sub x)).Bounded (a + (xs.length + 1) * (h + 1)) from
          hh.mono (by nlinarith))

theorem value_fold_sub (xs : List Fraction) (z : Fraction) :
    (xs.foldl Fraction.sub z).value = z.value - (xs.map Fraction.value).sum := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih => simp [ih]; ring

def products {d : ℕ} (row β : Fin d → ℚ) : List Fraction :=
  List.ofFn fun j => (ofRat (row j)).mul (ofRat (β j))

def residual {d : ℕ} (row β : Fin d → ℚ) (y : ℚ) : Fraction :=
  (products row β).foldl Fraction.sub (ofRat y)

theorem value_residual {d : ℕ} (row β : Fin d → ℚ) (y : ℚ) :
    (residual row β y).value = y - ∑ j, row j * β j := by
  simp [residual, products, value_fold_sub, List.map_ofFn, List.sum_ofFn]

def losses (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (β : Fin d → ℚ) : List Fraction :=
  List.ofFn fun i => (residual (A i) β (y i)).norm p

def check (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) : Bool :=
  (sum (losses p A y β)).le (ofRat B)

theorem value_loss (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (β : Fin d → ℚ) :
    (sum (losses p A y β)).value = RationalWitnesses.loss p A y β := by
  rw [RationalWitnesses.loss_eq_thesis]
  simp [sum, losses, value_fold_add, value_norm, value_residual,
    List.map_ofFn, List.sum_ofFn, Matrix.mulVec, dotProduct]

theorem check_correct (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) :
    check p A y B β = true ↔ RationalWitnesses.loss p A y β ≤ B := by
  simp [check, le_correct, value_loss]

/-- All input and certificate bits, including signs, dimensions and framing. -/
def totalBits {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) : ℕ :=
  (encodeInput A y B).length + (encodeRats (List.ofFn β)).length

/-- Bounds charged to the concrete encodings, not to a unit-cost field model. -/
theorem source_bounds {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    let S := totalBits A y B β
    r ≤ S ∧ d ≤ S ∧ (ofRat B).Bounded S ∧
      (∀ i, (ofRat (y i)).Bounded S) ∧
      (∀ i j, (ofRat (A i j)).Bounded S) ∧
      (∀ j, (ofRat (β j)).Bounded S) := by
  dsimp only
  let S := totalBits A y B β
  have hi : (encodeInput A y B).length ≤ S := Nat.le_add_right _ _
  have hc : (encodeRats (List.ofFn β)).length ≤ S := Nat.le_add_left _ _
  have hd := (input_size_bounds A y B hr).1.trans hi
  have hdata := (input_size_bounds A y B hr).2.trans hi
  have hb : ratBits B ≤ S := by
    have hlen := encodeRat_length B
    dsimp [S, totalBits, encodeInput] at hi ⊢
    simp only [List.length_append] at hi ⊢
    omega
  have hcount := count_le_encodeRats (inputEntries A y)
  rw [inputEntries_length] at hcount
  have her : (encodeRats (inputEntries A y)).length ≤ S := by
    dsimp [S, totalBits, encodeInput]
    simp only [List.length_append]
    omega
  refine ⟨by nlinarith, hd, (bounded_ofRat B).mono hb, ?_, ?_, ?_⟩
  · intro i
    exact (bounded_ofRat _).mono ((ratBits_le_dataBits (inputData A y) (i, none)).trans hdata)
  · intro i j
    exact (bounded_ofRat _).mono ((ratBits_le_dataBits (inputData A y) (i, some j)).trans hdata)
  · intro j
    have hsum := payload_le_encodeRats (List.ofFn β)
    rw [List.map_ofFn, List.sum_ofFn] at hsum
    have hj : ratBits (β j) ≤ ∑ k, ratBits (β k) :=
      Finset.single_le_sum (fun k _ => Nat.zero_le (ratBits (β k))) (Finset.mem_univ j)
    exact (bounded_ofRat _).mono (hj.trans (hsum.trans hc))

/-- Quadratic residual width, cubic summed-loss width at each fixed prime. -/
def residualWidth (S : ℕ) : ℕ := (S + 1) * (2 * S + 1)
def normWidth (p S : ℕ) : ℕ := p.size * residualWidth S + 1
def lossWidth (p S : ℕ) : ℕ := 1 + S * (normWidth p S + 1)
def compareWidth (p S : ℕ) : ℕ := lossWidth p S + S

theorem product_bounds {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) (i : Fin r)
    (x : Fraction) (hx : x ∈ products (A i) β) :
    x.Bounded (2 * totalBits A y B β) := by
  have hs := source_bounds A y B β hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  simpa [two_mul] using bounded_mul (hs.2.2.2.2.1 i j) (hs.2.2.2.2.2 j)

/-- Every left-to-right residual accumulator, including empty/full prefixes. -/
theorem residual_prefix_bounds {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) (i : Fin r) (k : ℕ) :
    (((products (A i) β).take k).foldl Fraction.sub (ofRat (y i))).Bounded
      (residualWidth (totalBits A y B β)) := by
  have hs := source_bounds A y B β hr
  have hlen : ((products (A i) β).take k).length ≤ d := by
    simp [products]
  have hh := bounded_fold_sub ((products (A i) β).take k) (hs.2.2.2.1 i)
    (fun x hx => product_bounds A y B β hr i x (List.mem_of_mem_take hx))
  apply hh.mono
  dsimp [residualWidth]
  have hd := hs.2.1
  nlinarith

theorem residual_bounds {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) (i : Fin r) :
    (residual (A i) β (y i)).Bounded (residualWidth (totalBits A y B β)) := by
  simpa only [List.take_length, residual] using
    residual_prefix_bounds A y B β hr i (products (A i) β).length

theorem norm_bounds (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ)
    (hr : 0 < r) (x : Fraction) (hx : x ∈ losses p A y β) :
    x.Bounded (normWidth p (totalBits A y B β)) := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact bounded_norm p (residual_bounds A y B β hr i)

/-- Powers needed for norms stay small throughout repeated multiplication. -/
theorem norm_power_bounds (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ)
    (hr : 0 < r) (i : Fin r) (k : ℕ)
    (hk : k ≤ padicValNat p (residual (A i) β (y i)).num.natAbs ∨
      k ≤ padicValNat p (residual (A i) β (y i)).den) :
    (p ^ k).size ≤ normWidth p (totalBits A y B β) := by
  have hs := residual_bounds A y B β hr i
  have hn := PadicValuationMachine.valuation_le_size p (residual (A i) β (y i)).num.natAbs
  have hd := PadicValuationMachine.valuation_le_size p (residual (A i) β (y i)).den
  have hk' : k ≤ residualWidth (totalBits A y B β) := by
    rcases hk with hk | hk
    · exact hk.trans (hn.trans hs.1)
    · exact hk.trans (hd.trans hs.2)
  exact (size_pow_le p k).trans (Nat.add_le_add_right (Nat.mul_le_mul_left p.size hk') 1)

/-- Every accumulated loss prefix, with repeated observations retained. -/
theorem loss_prefix_bounds (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ)
    (hr : 0 < r) (k : ℕ) :
    (sum ((losses p A y β).take k)).Bounded (lossWidth p (totalBits A y B β)) := by
  have hs := source_bounds A y B β hr
  have hlen : ((losses p A y β).take k).length ≤ r := by
    simp [losses]
  have hh := bounded_fold_add ((losses p A y β).take k) bounded_zero
    (fun x hx => norm_bounds p A y B β hr x (List.mem_of_mem_take hx))
  exact hh.mono (by dsimp [lossWidth]; nlinarith [hs.1])

theorem loss_bounds (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ)
    (hr : 0 < r) :
    (sum (losses p A y β)).Bounded (lossWidth p (totalBits A y B β)) := by
  simpa only [List.take_length] using loss_prefix_bounds p A y B β hr (losses p A y β).length

theorem comparison_bounds (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ)
    (hr : 0 < r) :
    let z := sum (losses p A y β)
    (z.num * (B.den : ℤ)).natAbs.size ≤ compareWidth p (totalBits A y B β) ∧
      (B.num * (z.den : ℤ)).natAbs.size ≤ compareWidth p (totalBits A y B β) :=
  cross_products_bounded (loss_bounds p A y B β hr) (source_bounds A y B β hr).2.2.1

/-- Explicit cubic polynomial, with the prime contributing only a constant. -/
theorem compareWidth_polynomial (p S : ℕ) :
    compareWidth p S = 2 * p.size * S ^ 3 + 3 * p.size * S ^ 2 + (p.size + 3) * S + 1 := by
  simp only [compareWidth, lossWidth, normWidth, residualWidth]
  ring

theorem compareWidth_mono (p : ℕ) {S T : ℕ} (h : S ≤ T) :
    compareWidth p S ≤ compareWidth p T := by
  unfold compareWidth lossWidth normWidth residualWidth
  gcongr

/-- Specialize to the already proved cubic certificate bound in input length.
The resulting degree-nine bound is a size bound only, with no runtime claim. -/
theorem short_comparison_bounds (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ)
    (hr : 0 < r)
    (hβ : (encodeRats (List.ofFn β)).length ≤
      12 * (encodeInput A y B).length ^ 3 + 9 * (encodeInput A y B).length + 1) :
    let z := sum (losses p A y β)
    let bound := compareWidth p
      (12 * (encodeInput A y B).length ^ 3 + 10 * (encodeInput A y B).length + 1)
    (z.num * (B.den : ℤ)).natAbs.size ≤ bound ∧
      (B.num * (z.den : ℤ)).natAbs.size ≤ bound := by
  have h := comparison_bounds p A y B β hr
  have hS : totalBits A y B β ≤
      12 * (encodeInput A y B).length ^ 3 + 10 * (encodeInput A y B).length + 1 := by
    unfold totalBits
    omega
  exact ⟨h.1.trans (compareWidth_mono p hS), h.2.trans (compareWidth_mono p hS)⟩

/-- Semantic checking and certificate size meet, still without a machine-time
or binary-parser theorem. This statement does not assert membership in NP. -/
theorem threshold_iff_short_check (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (hr : 0 < r) :
    (∃ β, RationalWitnesses.loss p A y β ≤ B) ↔
      ∃ β, check p A y B β = true ∧ (encodeRats (List.ofFn β)).length ≤
        12 * (encodeInput A y B).length ^ 3 + 9 * (encodeInput A y B).length + 1 := by
  simp only [check_correct]
  exact threshold_iff_short_certificate p A y B hr

#print axioms Fraction.value_norm
#print axioms Fraction.bounded_add
#print axioms Fraction.bounded_norm
#print axioms Fraction.encode_length_le
#print axioms source_bounds
#print axioms check_correct
#print axioms residual_prefix_bounds
#print axioms norm_power_bounds
#print axioms loss_prefix_bounds
#print axioms comparison_bounds
#print axioms compareWidth_polynomial
#print axioms short_comparison_bounds
#print axioms threshold_iff_short_check

end PhdThesisLean.RationalVerifierBounds
