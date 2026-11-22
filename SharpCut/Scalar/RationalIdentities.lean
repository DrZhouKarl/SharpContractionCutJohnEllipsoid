import Lean
import Init.Grind.Ordered.Field

/-!
# Rational identities in the scalar certificate

Exact algebraic parts of (8.28), (8.29), (8.30), (8.33), (8.35), and (8.37).
The nonzero hypotheses below are the denominators of these identities.
Their domains and analytic integrations are separately tracked obligations.
-/

namespace SharpCut.Scalar
open Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast
variable {R : Type u} [Field R] [LE R] [LT R]
  [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

theorem prefactor_difference (b1 b2 : R)
    (h1 : b1^2 + b1 + 2 ≠ 0) (h2 : b2^2 + b2 + 2 ≠ 0) :
    4 * (2+b2) * (3+b2) / (b2^2+b2+2) -
      4 * (2+b1) * (3+b1) / (b1^2+b1+2) =
      16 * (b2-b1) * (1-b1-b2-b1*b2) /
        ((b1^2+b1+2) * (b2^2+b2+2)) := by
  simp only [Field.div_eq_mul_inv, Semiring.pow_succ, Semiring.pow_zero,
    Semiring.one_mul, Field.inv_mul]
  grind

theorem integrand_factor_difference (b1 b2 w : R)
    (h1 : 2+b1*(1-w) ≠ 0) (h2 : 2+b2*(1-w) ≠ 0) :
    (2*w+b2*(1-w)) / (2+b2*(1-w)) -
      (2*w+b1*(1-w)) / (2+b1*(1-w)) =
      2*(b2-b1)*(1-w)^2 / ((2+b1*(1-w))*(2+b2*(1-w))) := by
  simp only [Field.div_eq_mul_inv, Semiring.pow_succ, Semiring.pow_zero,
    Semiring.one_mul, Field.inv_mul]
  grind

theorem interval_endpoint_difference (b1 b2 : R)
    (h1 : 4+b1 ≠ 0) (h2 : 4+b2 ≠ 0) :
    (2+b2)/(4+b2) - (2+b1)/(4+b1) =
      2*(b2-b1)/((4+b1)*(4+b2)) := by
  simp only [Field.div_eq_mul_inv, Semiring.pow_succ, Semiring.pow_zero,
    Semiring.one_mul, Field.inv_mul]
  grind

theorem largest_interval_endpoint : (2+1/4 : R)/(4+1/4) = 9/17 := by
  simp only [Field.div_eq_mul_inv, Semiring.pow_succ, Semiring.pow_zero,
    Semiring.one_mul, Field.inv_mul]
  grind

theorem endpoint_partial_fractions (w : R)
    (hp : 1+w ≠ 0) (hm : 1-w ≠ 0) (h9 : 9-w ≠ 0) :
    (1+7*w)^2 / ((1-w^2)*(9-w)^2) =
      9/(50*(1+w)) + 1/(2*(1-w)) -
        8/(25*(9-w)) - 256/(5*(9-w)^2) := by
  have hf : 1-w^2 = (1-w)*(1+w) := by grind
  rw [hf]
  simp only [Field.div_eq_mul_inv, Semiring.pow_succ, Semiring.pow_zero,
    Semiring.one_mul, Field.inv_mul]
  grind

theorem gain_polynomial_identity (b : R) :
    6*(1+b)*(b^2+b+2) - (2-b)*(1-b)*(2+b)*(3+b) =
      b*(26+19*b+4*b^2-b^3) := by
  simp only [Field.div_eq_mul_inv, Semiring.pow_succ, Semiring.pow_zero,
    Semiring.one_mul, Field.inv_mul]
  grind

theorem loss_factor_difference (a z s : R)
    (hz : 1-z ≠ 0) (hs : 1-z*s ≠ 0) :
    (1-a)/(1-z) - (1-a*s)/(1-z*s) =
      (z-a)*(1-s)/((1-z)*(1-z*s)) := by
  simp only [Field.div_eq_mul_inv, Semiring.pow_succ, Semiring.pow_zero,
    Semiring.one_mul, Field.inv_mul]
  grind

theorem interpolated_slope_identity (a t b : R)
    (ha : 1-a*b ≠ 0) (ht : 1-t*b ≠ 0) :
    -(t-a)/((1-a*b)*(1-t*b)) = a/(1-a*b) - t/(1-t*b) := by
  simp only [Field.div_eq_mul_inv, Semiring.pow_succ, Semiring.pow_zero,
    Semiring.one_mul, Field.inv_mul]
  grind

/-- Rational Hermite remainder; integrating it is a separate analytic step. -/
theorem rational_hermite_remainder (z b s : R)
    (hz : 1+z ≠ 0) (hb : 1-b*z ≠ 0) (hs : 1-z*s ≠ 0)
    (hbp : 1+b ≠ 0) :
    s/(1-z*s) -
      (b/(1-z*b) + (s-b)/(1-z*b)^2 +
        ((-1)/(1+z) - b/(1-z*b) + (1+b)/(1-z*b)^2) /
          (1+b)^2 * (s-b)^2) =
      z^2*(1+s)*(s-b)^2/((1+z)*(1-b*z)^2*(1-z*s)) := by
  simp only [Field.div_eq_mul_inv, Semiring.pow_succ, Semiring.pow_zero,
    Semiring.one_mul, Field.inv_mul]
  grind

end SharpCut.Scalar
