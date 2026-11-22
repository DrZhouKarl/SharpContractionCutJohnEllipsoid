import SharpCut.Scalar.HermiteIntegral

/-! # Integrating the exact rational Hermite remainder -/

noncomputable section
open Set MeasureTheory
namespace SharpCut.Scalar
variable {b s : ℝ}

def hermiteQuadratic (b pole latitude slope s : ℝ) : ℝ :=
  latitude+slope*(s-b)+
    ((pole-latitude+(1+b)*slope)/(1+b)^2)*(s-b)^2

def rationalHermite (b s z : ℝ) : ℝ :=
  hermiteQuadratic b (rationalHeight (-1) z) (rationalHeight b z) (slopeIntegrand b z) s

def logarithmicHermite (b s : ℝ) : ℝ :=
  hermiteQuadratic b (Real.log (Determinant.heightFactor b (-1)))
    (Real.log (Determinant.heightFactor b b)) (logarithmicSlope b) s

def hermiteRemainderIntegrand (b s z : ℝ) : ℝ :=
  z^2/((1+z)*(1-b*z)^2*(1-z*s))

theorem hermite_linear (b pole latitude slope s : ℝ) :
    hermiteQuadratic b pole latitude slope s =
      (1-(s-b)^2/(1+b)^2)*latitude+((s-b)^2/(1+b)^2)*pole+
        ((s-b)+(1+b)*((s-b)^2/(1+b)^2))*slope := by
  unfold hermiteQuadratic
  ring

theorem rationalHeight_intervalIntegrable (hb : 0 < b) (hbq : b ≤ 1/4) (hs : s ≤ 1) :
    IntervalIntegrable (rationalHeight s) volume (scalarA b) (scalarT b) := by
  have hc : ContinuousOn (rationalHeight s) (uIcc (scalarA b) (scalarT b)) := by
    rw [uIcc_of_le (scalar_interval_bounds hb hbq).2.1]
    exact rationalHeight_continuousOn hb hbq hs
  exact hc.intervalIntegrable

theorem slope_intervalIntegrable (hb : 0 < b) (hbq : b ≤ 1/4) :
    IntervalIntegrable (slopeIntegrand b) volume (scalarA b) (scalarT b) := by
  have hc : ContinuousOn (slopeIntegrand b) (uIcc (scalarA b) (scalarT b)) := by
    rw [uIcc_of_le (scalar_interval_bounds hb hbq).2.1]
    exact slopeIntegrand_continuousOn hb hbq
  exact hc.intervalIntegrable

theorem rationalHermite_intervalIntegrable (hb : 0 < b) (hbq : b ≤ 1/4) :
    IntervalIntegrable (rationalHermite b s) volume (scalarA b) (scalarT b) := by
  unfold rationalHermite
  simp only [hermite_linear]
  exact (((rationalHeight_intervalIntegrable hb hbq (by linarith : b ≤ 1)).const_mul _).add
    ((rationalHeight_intervalIntegrable hb hbq (by norm_num : (-1 : ℝ) ≤ 1)).const_mul _)).add
      ((slope_intervalIntegrable hb hbq).const_mul _)

theorem hermite_interpolant_integral (hb : 0 < b) (hbq : b ≤ 1/4) :
    -(∫ z in scalarA b..scalarT b, rationalHermite b s z) = logarithmicHermite b s := by
  let q := (s-b)^2/(1+b)^2
  let c := (s-b)+(1+b)*q
  have hib := rationalHeight_intervalIntegrable hb hbq (by linarith : b ≤ 1)
  have hip := rationalHeight_intervalIntegrable hb hbq (by norm_num : (-1 : ℝ) ≤ 1)
  have his := slope_intervalIntegrable hb hbq
  simp only [rationalHermite, hermite_linear, logarithmicHermite]
  change -(∫ z in scalarA b..scalarT b,
      ((1-q)*rationalHeight b z+q*rationalHeight (-1) z)+c*slopeIntegrand b z) =
    (1-q)*Real.log (Determinant.heightFactor b b)+q*Real.log (Determinant.heightFactor b (-1))+
      c*logarithmicSlope b
  rw [intervalIntegral.integral_add ((hib.const_mul (1-q)).add (hip.const_mul q)) (his.const_mul c),
    intervalIntegral.integral_add (hib.const_mul (1-q)) (hip.const_mul q),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have h1 := log_height_integral hb hbq (by linarith : b ≤ 1)
  have h2 := log_height_integral hb hbq (by norm_num : (-1 : ℝ) ≤ 1)
  have h3 := logarithmic_slope_integral hb hbq
  rw [neg_eq_iff_eq_neg] at h1 h2 h3
  rw [h1, h2, h3]
  ring

theorem rational_hermite_exact (hb : 0 < b) (hbq : b ≤ 1/4) (hs : s ≤ 1)
    {z : ℝ} (hz : z ∈ Icc (scalarA b) (scalarT b)) :
    rationalHeight s z-rationalHermite b s z =
      (1+s)*(s-b)^2*hermiteRemainderIntegrand b s z := by
  have ha := scalar_interval_bounds hb hbq
  have hz0 : 0 ≤ z := ha.1.le.trans hz.1
  have hp : 1+z ≠ 0 := by linarith
  have hden := scalar_height_denominator hb hbq hs hz
  have hdb := scalar_height_denominator hb hbq (by linarith : b ≤ 1) hz
  have h := rational_hermite_remainder z b s hp
    (by simpa only [mul_comm] using hdb.ne') hden.ne' (by linarith : 1+b ≠ 0)
  convert h using 1 <;>
    simp only [rationalHeight, rationalHermite, hermiteQuadratic, slopeIntegrand,
      hermiteRemainderIntegrand, mul_neg_one, sub_neg_eq_add, mul_comm b z] <;> ring

/-- Exact pointwise remainder (8.27), with a genuine compact interval integral. -/
theorem logarithmic_hermite_remainder (hb : 0 < b) (hbq : b ≤ 1/4) (hs : s ≤ 1) :
    Real.log (Determinant.heightFactor b s)-logarithmicHermite b s =
      -(1+s)*(s-b)^2*∫ z in scalarA b..scalarT b, hermiteRemainderIntegrand b s z := by
  have hsub := intervalIntegral.integral_sub (rationalHeight_intervalIntegrable hb hbq hs)
    (rationalHermite_intervalIntegrable (s := s) hb hbq)
  have hpoint : (∫ z in scalarA b..scalarT b, rationalHeight s z-rationalHermite b s z) =
      (1+s)*(s-b)^2*∫ z in scalarA b..scalarT b, hermiteRemainderIntegrand b s z := by
    calc
      _ = ∫ z in scalarA b..scalarT b, (1+s)*(s-b)^2*hermiteRemainderIntegrand b s z := by
        apply intervalIntegral.integral_congr
        intro z hz
        rw [uIcc_of_le (scalar_interval_bounds hb hbq).2.1] at hz
        exact rational_hermite_exact hb hbq hs hz
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [hsub] at hpoint
  have h1 := log_height_integral hb hbq hs
  have h2 := hermite_interpolant_integral (s := s) hb hbq
  linarith only [hpoint, h1, h2]

end SharpCut.Scalar
