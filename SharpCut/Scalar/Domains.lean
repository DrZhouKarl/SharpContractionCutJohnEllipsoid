import SharpCut.Scalar.RationalIdentities

/-!
# Positive domains of the scalar construction

These are universal ordered-field lemmas. The later finite-frame module must
derive the height hypotheses from a unit vector and a unit cut normal.
-/

namespace SharpCut.Scalar
open Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast
variable {R : Type u} [Field R] [LE R] [LT R]
  [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

theorem lorentz_parameter_bounds (b : R) (hb : 0 < b) (hbh : b ≤ 1/2) :
    0 < b/(2-b) ∧ b/(2-b) ≤ 1/3 := by
  have hd : 0 < 2-b := by grind
  have hp := Field.IsOrdered.inv_pos_iff.mpr hd
  have hpos := OrderedRing.mul_pos hb hp
  have hc := OrderedRing.mul_le_mul_of_nonneg_right
    (show 3*b ≤ 2-b by grind) (Preorder.le_of_lt hp)
  grind

theorem lorentz_denominator_lower (b s : R) (hb : 0 < b) (hbh : b ≤ 1/2)
    (hs : s ≤ 1) : 2/3 ≤ 1-b/(2-b)*s := by
  have ha := lorentz_parameter_bounds b hb hbh
  have hmul := OrderedRing.mul_le_mul_of_nonneg_left hs (Preorder.le_of_lt ha.1)
  grind

theorem balanced_weight_lower (b s weight : R) (hb : 0 ≤ b) (hbh : b ≤ 1/2)
    (hs : s ≤ 1) (hw : 0 < weight) :
    weight/4 ≤ weight*(1-(1+b)/2*s) ∧ 0 < weight*(1-(1+b)/2*s) := by
  have ht : 0 ≤ (1+b)/2 := by grind
  have hmul := OrderedRing.mul_le_mul_of_nonneg_left hs ht
  have hl : 1/4 ≤ 1-(1+b)/2*s := by grind
  have hwc := OrderedRing.mul_le_mul_of_nonneg_left hl (Preorder.le_of_lt hw)
  grind

theorem endpoint_denominators_positive (w : R) (hw : 0 ≤ w) (hwh : w ≤ 9/17) :
    0 < 1+w ∧ 0 < 1-w ∧ 0 < 9-w ∧ 0 < 1-w^2 := by
  have hp : 0 < 1+w := by grind
  have hm : 0 < 1-w := by grind
  have hprod := OrderedRing.mul_pos hp hm
  grind

theorem rational_prefactor_denominator_positive (b : R) (hb : 0 ≤ b) :
    0 < b^2+b+2 := by
  have hs := OrderedRing.sq_nonneg (a := b)
  grind

theorem monotonicity_numerator_lower (b1 b2 : R)
    (h1 : 0 ≤ b1) (h1h : b1 ≤ 1/4) (h2 : 0 ≤ b2) (h2h : b2 ≤ 1/4) :
    7/16 ≤ 1-b1-b2-b1*b2 := by
  have hm := OrderedRing.mul_le_mul_of_nonneg_right h1h h2
  grind

theorem gain_polynomial_nonneg (b : R) (hb : 0 ≤ b) (hbh : b ≤ 1/4) :
    0 ≤ b*(26+19*b+4*b^2-b^3) := by
  have hs := OrderedRing.sq_nonneg (a := b)
  have hc := OrderedRing.mul_le_mul_of_nonneg_right hbh hs
  have hi : 0 ≤ 26+19*b+4*b^2-b^3 := by grind
  exact OrderedRing.mul_nonneg hb hi

theorem gain_coefficient_lower (b : R) (hb : 0 < b) (hbh : b ≤ 1/4) :
    1/12 ≤ (1+b)*(b^2+b+2)/(2*(2-b)*(1-b)*(2+b)*(3+b)) := by
  have hbp : 0 ≤ b := Preorder.le_of_lt hb
  have hpoly := gain_polynomial_nonneg b hbp hbh
  have hid := gain_polynomial_identity b
  have hd := OrderedRing.mul_pos (show 0 < 2*(2-b) by grind)
    (show 0 < 1-b by grind)
  have hd2 := OrderedRing.mul_pos hd (show 0 < 2+b by grind)
  have hd3 := OrderedRing.mul_pos hd2 (show 0 < 3+b by grind)
  have hi := Field.IsOrdered.inv_pos_iff.mpr hd3
  have hm := OrderedRing.mul_le_mul_of_nonneg_right
    (show 2*(2-b)*(1-b)*(2+b)*(3+b) ≤ 12*((1+b)*(b^2+b+2)) by grind)
    (Preorder.le_of_lt hi)
  grind

end SharpCut.Scalar
