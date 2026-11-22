import SharpCut.Determinant.DimensionThree
import SharpCut.Determinant.HigherDimensions

/-! # The quantitative lower bound in every dimension n ≥ 2 -/

noncomputable section
open scoped RealInnerProductSpace
namespace SharpCut.Determinant
open Certificate

/-- All three genuine matrix branches of the lower half of Theorem 8.1. -/
theorem all_dimensions_logdet_lower {n N : ℕ} (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    (1/1500 : ℝ)*frameDefect F v ≤ Real.log (normalizedCertificate F v).det := by
  by_cases h2 : n = 2
  · subst n; exact dimension_two_uniform_logdet F v hv
  by_cases h3 : n = 3
  · subst n; exact dimension_three_uniform_logdet F v hv
  exact higher_dimensional_uniform_logdet F (by omega) v hv

end SharpCut.Determinant
