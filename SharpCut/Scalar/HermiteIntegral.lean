import SharpCut.Scalar.LossIntegral
import SharpCut.Determinant.LogGain

/-!
# Analytic data for logarithmic Hermite interpolation

Recovering logarithmic values and slope data from compact rational integrals
uses explicit primitives and positive denominators. No differentiation under
the integral is needed. The full remainder and weighted loss are subsequent
proof obligations.
-/

open Set MeasureTheory
namespace SharpCut.Scalar
noncomputable section
variable {b s : ℝ}
def rationalHeight (s z : ℝ) : ℝ := s/(1-z*s)
def logHeightPrimitive (s z : ℝ) : ℝ := Real.log (1-z*s)
theorem scalar_interval_bounds (hb : 0 < b) (hbq : b ≤ 1/4) :
  0 < scalarA b ∧ scalarA b ≤ scalarT b ∧ scalarT b < 1 := by
 have ha := lorentz_parameter_bounds b hb (by linarith : b ≤ 1/2)
 refine ⟨ha.1, ?_, ?_⟩ <;> dsimp [scalarA, scalarT] <;> linarith [ha.2]
theorem scalar_height_denominator (hb : 0 < b) (hbq : b ≤ 1/4)
 (hs : s ≤ 1) {z : ℝ} (hz : z ∈ Icc (scalarA b) (scalarT b)) : 0 < 1-z*s := by
 have ha := scalar_interval_bounds hb hbq
 have hz0 : 0 ≤ z := ha.1.le.trans hz.1
 have hzs := mul_le_mul_of_nonneg_left hs hz0
 linarith [ha.2.2, hz.2]
theorem rationalHeight_continuousOn (hb : 0 < b) (hbq : b ≤ 1/4) (hs : s ≤ 1) :
 ContinuousOn (rationalHeight s) (Icc (scalarA b) (scalarT b)) := by
 unfold rationalHeight
 apply ContinuousOn.div
 · fun_prop
 · fun_prop
 · intro z hz
   exact (scalar_height_denominator hb hbq hs hz).ne'
theorem logHeightPrimitive_hasDerivAt {z : ℝ} (hz : 1-z*s ≠ 0) :
 HasDerivAt (logHeightPrimitive s) (-rationalHeight s z) z := by
 have h := (((hasDerivAt_id z).mul_const s).const_sub 1).log hz
 change HasDerivAt (fun y => Real.log (1-y*s)) (-(s/(1-z*s))) z
 simpa only [logHeightPrimitive, rationalHeight, one_mul, neg_div, id_eq] using h
theorem log_height_integral (hb : 0 < b) (hbq : b ≤ 1/4) (hs : s ≤ 1) :
 -(∫ z in scalarA b..scalarT b, rationalHeight s z) =
 Real.log (SharpCut.Determinant.heightFactor b s) := by
 have ha := scalar_interval_bounds hb hbq
 have hder : ∀ z ∈ uIcc (scalarA b) (scalarT b),
   HasDerivAt (logHeightPrimitive s) (-rationalHeight s z) z := by
  intro z hz
  rw [uIcc_of_le ha.2.1] at hz
  exact logHeightPrimitive_hasDerivAt (scalar_height_denominator hb hbq hs hz).ne'
 have hc : ContinuousOn (fun z => -rationalHeight s z) (uIcc (scalarA b) (scalarT b)) := by
  rw [uIcc_of_le ha.2.1]
  exact (rationalHeight_continuousOn hb hbq hs).neg
 have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hc.intervalIntegrable
 rw [intervalIntegral.integral_neg] at h
 change -(∫ z in scalarA b..scalarT b, rationalHeight s z) = Real.log ((1-scalarT b*s)/(1-scalarA b*s))
 rw [Real.log_div
   (scalar_height_denominator hb hbq hs ⟨ha.2.1,le_rfl⟩).ne'
   (scalar_height_denominator hb hbq hs ⟨le_rfl,ha.2.1⟩).ne']
 exact h

def slopePrimitive (b z : ℝ) : ℝ := z/(1-z*b)
def slopeIntegrand (b z : ℝ) : ℝ := 1/(1-z*b)^2
def logarithmicSlope (b : ℝ) : ℝ :=
  scalarA b/(1-scalarA b*b)-scalarT b/(1-scalarT b*b)

theorem slopePrimitive_hasDerivAt {z : ℝ} (hz : 1-z*b ≠ 0) :
    HasDerivAt (slopePrimitive b) (slopeIntegrand b z) z := by
  have h := (hasDerivAt_id z).div (((hasDerivAt_id z).mul_const b).const_sub 1) hz
  convert h using 1
  · rfl
  · simp only [slopeIntegrand, id_eq, one_mul]
    field_simp [hz]
    ring

theorem slopeIntegrand_continuousOn (hb : 0 < b) (hbq : b ≤ 1/4) :
    ContinuousOn (slopeIntegrand b) (Icc (scalarA b) (scalarT b)) := by
  unfold slopeIntegrand
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro z hz
    exact pow_ne_zero 2 (scalar_height_denominator hb hbq (by linarith : b ≤ 1) hz).ne'

theorem logarithmic_slope_integral (hb : 0 < b) (hbq : b ≤ 1/4) :
    -(∫ z in scalarA b..scalarT b, slopeIntegrand b z) = logarithmicSlope b := by
  have ha := scalar_interval_bounds hb hbq
  have hder : ∀ z ∈ uIcc (scalarA b) (scalarT b),
      HasDerivAt (slopePrimitive b) (slopeIntegrand b z) z := by
    intro z hz
    rw [uIcc_of_le ha.2.1] at hz
    exact slopePrimitive_hasDerivAt
      (scalar_height_denominator hb hbq (by linarith : b ≤ 1) hz).ne'
  have hc : ContinuousOn (slopeIntegrand b) (uIcc (scalarA b) (scalarT b)) := by
    rw [uIcc_of_le ha.2.1]
    exact slopeIntegrand_continuousOn hb hbq
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hc.intervalIntegrable
  simp only [slopePrimitive] at h
  simp only [logarithmicSlope]
  linarith only [h]

theorem logarithmic_slope_value (hb : 0 < b) (hbq : b ≤ 1/4) :
    logarithmicSlope b = -(scalarT b-scalarA b)/
      ((1-scalarA b*b)*(1-scalarT b*b)) := by
  have ha := scalar_interval_bounds hb hbq
  exact (interpolated_slope_identity (scalarA b) (scalarT b) b
    (scalar_height_denominator hb hbq (by linarith : b ≤ 1) ⟨le_rfl,ha.2.1⟩).ne'
    (scalar_height_denominator hb hbq (by linarith : b ≤ 1) ⟨ha.2.1,le_rfl⟩).ne').symm

end
end SharpCut.Scalar
