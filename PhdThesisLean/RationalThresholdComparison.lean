import PhdThesisLean.SignedIntegerComparison
import PhdThesisLean.RationalVerifierBounds

/-!
# Machine comparison of the verifier's final cross-products

The signed comparison machine consumes the two already computed, encoded
cross-products. Its actual runtime is bounded in the original regression input
and certificate length using the earlier intermediate-width theorem. Computing
and serializing these products from fractions is still a separate obligation.
-/

namespace PhdThesisLean.RationalThresholdComparison

open Computability Turing StateTransition
open RationalVerifierBounds
open SignedIntegerComparison

set_option backward.isDefEq.respectTransparency false

def crossProducts (x y : Fraction) : ℤ × ℤ :=
  (x.num * y.den, y.num * x.den)

theorem crossProducts_correct (x y : Fraction) :
    decide ((crossProducts x y).1 ≤ (crossProducts x y).2) = x.le y := rfl

/-- Actual comparison execution, conditional on its serialized cross-products
being supplied as the input; this does not charge their construction. -/
def fractionOutputsInTime (x y : Fraction) :
    TM2OutputsInTime computer (encode (crossProducts x y)) (some [x.le y])
      (2 * (encode (crossProducts x y)).length + 1) :=
  outputsInTime (crossProducts x y)

theorem fraction_answer_correct (x y : Fraction) :
    decide ((crossProducts x y).1 ≤ (crossProducts x y).2) = true ↔ x.value ≤ y.value :=
  Fraction.le_correct x y

/-- A bit-width bound gives a bound on actual comparison steps, including
signs, both frames and cleanup. It does not estimate multiplication costs. -/
def boundedOutputsInTime (a b : ℤ) (w : ℕ)
    (ha : a.natAbs.size ≤ w) (hb : b.natAbs.size ≤ w) :
    TM2OutputsInTime computer (encode (a, b)) (some [decide (a ≤ b)]) (8 * w + 9) := by
  apply LeanNPHardness.MachinePrimitives.evalsToInTimeMono (outputsInTime (a, b))
  rw [encode_length]
  dsimp only
  omega

/-- Polynomial machine time for the final comparison phase in total original
input/certificate bits. The input here is explicitly the pair of products. -/
def lossComparisonOutputsInTime (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ)
    (hr : 0 < r) :
    TM2OutputsInTime computer
      (encode (crossProducts (sum (losses p A y β)) (Fraction.ofRat B)))
      (some [check p A y B β])
      (16 * p.size * (totalBits A y B β) ^ 3 +
        24 * p.size * (totalBits A y B β) ^ 2 +
        8 * (p.size + 3) * totalBits A y B β + 17) := by
  have hs := comparison_bounds p A y B β hr
  have h := boundedOutputsInTime _ _ (compareWidth p (totalBits A y B β)) hs.1 hs.2
  have ht : 8 * compareWidth p (totalBits A y B β) + 9 =
      16 * p.size * (totalBits A y B β) ^ 3 +
        24 * p.size * (totalBits A y B β) ^ 2 +
        8 * (p.size + 3) * totalBits A y B β + 17 := by
    rw [compareWidth_polynomial]
    ring
  rw [ht] at h
  exact h

theorem loss_answer_correct (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) :
    decide ((crossProducts (sum (losses p A y β)) (Fraction.ofRat B)).1 ≤
      (crossProducts (sum (losses p A y β)) (Fraction.ofRat B)).2) = true ↔
        RationalWitnesses.loss p A y β ≤ B :=
  check_correct p A y B β

#print axioms fractionOutputsInTime
#print axioms boundedOutputsInTime
#print axioms lossComparisonOutputsInTime
#print axioms loss_answer_correct

end PhdThesisLean.RationalThresholdComparison
