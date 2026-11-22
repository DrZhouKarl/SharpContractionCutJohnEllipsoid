import Lean
import Init.Grind.Ordered.Field

/-!
# Exact endpoint arithmetic

Supporting algebra for SUP-17, Lemma 8.4 and equation (8.66). The statements
hold in every linearly ordered field with the standard Lean `grind` interfaces.
They do not assert the analytic logarithm bounds or the determinant theorem.
The rational logarithm bounds come from
`revised_v3/verification/endpoint_log_bounds.md`.
-/

namespace SharpCut.Scalar
open Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast
variable {R : Type u} [Field R] [LE R] [LT R]
  [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

theorem log_two_upper_arithmetic :
    2 * (1 / 3 + 1 / 81 + 1 / 1215 : R) + 1 / 6804 = 23581 / 34020 := by
  grind

theorem log_sixteen_thirteen_lower_arithmetic :
    2 * (3 / 29 + (3 / 29 : R)^3 / 3) = 5064 / 24389 := by
  grind

theorem endpoint_substitution_arithmetic :
    ((7956 : R) * (23581 / 34020) - 2106 * (5064 / 24389) - 4160) / 925 =
      21144601309 / 21319034625 := by
  grind

theorem endpoint_strict_comparison :
    (21144601309 : R) / 21319034625 < 9919 / 10000 := by
  grind

theorem endpoint_margin_comparison : (9919 : R) / 10000 < 124 / 125 := by
  grind

/-- A conditional substitution lemma, not a proof of either logarithm bound. -/
theorem endpoint_bound_of_log_bounds (l2 l1613 : R)
    (h2 : l2 ≤ 23581 / 34020) (h1613 : 5064 / 24389 ≤ l1613) :
    (7956 * l2 - 2106 * l1613 - 4160) / 925 < 124 / 125 := by
  grind

theorem logarithm_recombination (l2 l13 l1613 : R)
    (h : l13 = 4 * l2 - l1613) :
    (2106 * l13 - 468 * l2 - 4160) / 925 =
      (7956 * l2 - 2106 * l1613 - 4160) / 925 := by
  grind

theorem endpoint_integral_recombination (l2 l13 : R) :
    468 / 37 * (9 / 50 * l13 - 1 / 25 * l2 - 16 / 45) =
      (2106 * l13 - 468 * l2 - 4160) / 925 := by
  grind

theorem high_dimension_margin : (1 : R) / 12 * (1 - 124 / 125) = 1 / 1500 := by
  grind

theorem dimension_two_log_margin :
    (11 / 60 : R) / (1 + 2 * (11 / 60)) ≥ 1 / 1500 := by
  grind

theorem dimension_three_log_margin :
    (36 / 385 : R) / (1 + 2 * (36 / 385)) ≥ 1 / 1500 := by
  grind

theorem dimension_three_sigma_conversion (chi sigma : R)
    (h : sigma = 18 * chi / 35) : 2 * sigma / 11 = 36 * chi / 385 := by
  grind

end SharpCut.Scalar
