import Lean
import Init.Grind.Ordered.Field

/-!
# Dimension-three polynomial certificate

The scalar polynomial portion of Proposition 8.7, equations (8.63)--(8.65).
No matrix hypothesis or determinant conclusion is included in this module.
-/

namespace SharpCut.Determinant
open Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast
variable {R : Type u} [Field R] [LE R] [LT R]
  [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

def dimensionThreePolynomial (sigma z : R) : R :=
  72*sigma*(1+sigma) + (171/4-53/4*sigma+75*sigma^2)*z +
    (-333/4+75*sigma)*z^2

theorem dimension_three_endpoint_identity (sigma : R) :
    dimensionThreePolynomial sigma (sigma*(1+sigma)) =
      sigma*(1+sigma)/4 * (300*sigma^3+267*sigma^2-386*sigma+459) := by
  unfold dimensionThreePolynomial
  grind

theorem dimension_three_cubic_decomposition (sigma : R) :
    300*sigma^3+267*sigma^2-386*sigma+459-288 =
      300*sigma^3+267*(sigma-3/4)^2+29/2*sigma+333/16 := by
  grind

theorem dimension_three_cubic_nonneg (sigma : R) (h : 0 ≤ sigma) :
    0 ≤ 300*sigma^3+267*sigma^2-386*sigma+459-288 := by
  rw [dimension_three_cubic_decomposition]
  have hs := OrderedRing.sq_nonneg (a := sigma-3/4)
  have h2 := OrderedRing.mul_nonneg h h
  have h3 := OrderedRing.mul_nonneg h2 h
  grind

theorem dimension_three_quadratic_coefficient (sigma : R) (h : sigma ≤ 3/4) :
    -333/4+75*sigma < 0 := by
  grind

theorem dimension_three_endpoint_lower (sigma : R) (h : 0 ≤ sigma) :
    72*sigma*(1+sigma) ≤ dimensionThreePolynomial sigma (sigma*(1+sigma)) := by
  rw [dimension_three_endpoint_identity]
  have hc := dimension_three_cubic_nonneg sigma h
  have hp := OrderedRing.mul_nonneg h (show 0 ≤ 1+sigma by grind)
  have hm := OrderedRing.mul_nonneg hp hc
  grind

/-- The complete interval certificate, including its zero endpoint. -/
theorem dimension_three_polynomial_lower (sigma z : R)
    (hs : 0 ≤ sigma) (hsh : sigma ≤ 3/4)
    (hz : 0 ≤ z) (hzh : z ≤ sigma*(1+sigma)) :
    72*sigma*(1+sigma) ≤ dimensionThreePolynomial sigma z := by
  by_cases h0 : sigma = 0
  · subst sigma
    have hzero : z = 0 := by
      simp only [Semiring.zero_mul] at hzh
      exact Std.le_antisymm hzh hz
    subst z
    unfold dimensionThreePolynomial
    grind
  · have hpos : 0 < sigma*(1+sigma) :=
      OrderedRing.mul_pos (show 0 < sigma by grind) (show 0 < 1+sigma by grind)
    have hep := dimension_three_endpoint_lower sigma hs
    have he : 0 ≤ sigma*(1+sigma) *
        ((171/4-53/4*sigma+75*sigma^2)+(-333/4+75*sigma)*(sigma*(1+sigma))) := by
      unfold dimensionThreePolynomial at hep
      grind
    have hbr : 0 ≤ (171/4-53/4*sigma+75*sigma^2)+
        (-333/4+75*sigma)*(sigma*(1+sigma)) := by
      have hi := (OrderedRing.mul_nonneg_iff.mp he)
      grind
    have hc := dimension_three_quadratic_coefficient sigma hsh
    have hm := OrderedRing.mul_le_mul_of_nonpos_left hzh (Preorder.le_of_lt hc)
    have hbrz : 0 ≤ (171/4-53/4*sigma+75*sigma^2)+(-333/4+75*sigma)*z := by
      grind
    have hr := OrderedRing.mul_nonneg hz hbrz
    unfold dimensionThreePolynomial
    grind

/-- Scalar elimination of the Gram and direct-coupling inequalities.

The matrix-to-scalar hypotheses of Proposition 8.7 still have to be proved
from a John frame. This helper does not assume any determinant lower bound.
-/
theorem dimension_three_scalar_elimination (sigma z r omega value : R)
    (hs : 0 ≤ sigma) (hsh : sigma ≤ 3/4)
    (hz : 0 ≤ z) (hzh : z ≤ sigma*(1+sigma))
    (hgram : (2/3-sigma)*r+omega ≤
      5*sigma/12 * ((2/3)^2-2/3*sigma+(z-sigma)/4))
    (hvar : ((1+sigma)*(1+4*sigma)-z)*r-4*(1+sigma)*omega ≤
      (5/8-5*sigma/6)/2*z*(1+sigma+z))
    (hvalue : value = (1-5*sigma/12)*(1+sigma+(z-sigma)/4)-((1+sigma)*r-omega)) :
    1+2*sigma/11 ≤ value := by
  have hdelta : 0 < 11/3*(1+sigma)-z := by
    have hm := OrderedRing.mul_le_mul_of_nonneg_right hsh
      (show 0 ≤ 1+sigma by grind)
    grind
  have hg := OrderedRing.mul_le_mul_of_nonneg_left hgram
    (show 0 ≤ 3*(1+sigma)+z by grind)
  have hv := OrderedRing.mul_le_mul_of_nonneg_left hvar (show (0 : R) ≤ 5/3 by grind)
  have hsum := OrderedAdd.add_le_add hg hv
  have hc : (3*(1+sigma)+z)*((2/3-sigma)*r+omega) +
      5/3*(((1+sigma)*(1+4*sigma)-z)*r-4*(1+sigma)*omega) =
      (11/3*(1+sigma)-z)*((1+sigma)*r-omega) := by grind
  rw [hc] at hsum
  have hdiff := OrderedAdd.sub_nonneg_iff.mpr hsum
  have hscaled := OrderedRing.mul_nonneg (show (0 : R) ≤ 108 by grind) hdiff
  have hid : 108 *
      ((3*(1+sigma)+z)*(5*sigma/12*((2/3)^2-2/3*sigma+(z-sigma)/4)) +
        5/3*((5/8-5*sigma/6)/2*z*(1+sigma+z)) -
        (11/3*(1+sigma)-z)*((1+sigma)*r-omega)) =
      108*(11/3*(1+sigma)-z)*(value-1)-dimensionThreePolynomial sigma z := by
    rw [hvalue]
    unfold dimensionThreePolynomial
    grind
  rw [hid] at hscaled
  have hpol := OrderedAdd.sub_nonneg_iff.mp hscaled
  have hp := dimension_three_polynomial_lower sigma z hs hsh hz hzh
  have hbase := OrderedRing.mul_nonneg hs (show 0 ≤ 1+sigma by grind)
  have hv0 : 0 ≤ value-1 := by
    have hmul : 0 ≤ (11/3*(1+sigma)-z)*(value-1) := by grind
    have hi := OrderedRing.mul_nonneg_iff.mp hmul
    grind
  have hdhi : 11/3*(1+sigma)-z ≤ 11/3*(1+sigma) := by grind
  have hm := OrderedRing.mul_le_mul_of_nonneg_right hdhi hv0
  have hfinal : 0 ≤ (1+sigma)*(396*(value-1)-72*sigma) := by grind
  have hi := OrderedRing.mul_nonneg_iff.mp hfinal
  grind

end SharpCut.Determinant
