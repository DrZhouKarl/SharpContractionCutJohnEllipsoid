import SharpCut.Scalar.HermiteRemainder

/-! # Pointwise logarithmic interpolation loss in units of the contact defect -/

noncomputable section
open Set MeasureTheory
namespace SharpCut.Scalar
variable {b s : ℝ}

theorem hermiteRemainderIntegrand_continuousOn (hb : 0 < b) (hbq : b ≤ 1/4) (hs : s ≤ 1) :
    ContinuousOn (hermiteRemainderIntegrand b s) (Icc (scalarA b) (scalarT b)) := by
  unfold hermiteRemainderIntegrand
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro z hz
    have ha := scalar_interval_bounds hb hbq
    have hp : 1+z ≠ 0 := by linarith [ha.1, hz.1]
    have hdb := scalar_height_denominator hb hbq (by linarith : b ≤ 1) hz
    have hds := scalar_height_denominator hb hbq hs hz
    exact mul_ne_zero (mul_ne_zero hp (pow_ne_zero 2 (by simpa only [mul_comm] using hdb.ne'))) hds.ne'

theorem originalIntegrand_continuousOn_interval (hb : 0 < b) (hbq : b ≤ 1/4) :
    ContinuousOn (originalIntegrand b) (Icc (scalarA b) (scalarT b)) := by
  unfold originalIntegrand
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro z hz
    have ha := scalar_interval_bounds hb hbq
    have hz0 : 0 ≤ z := ha.1.le.trans hz.1
    have hm : 0 < 1-z := by linarith [ha.2.2, hz.2]
    have hp : 0 < 1+z := by linarith
    have hs : 0 < 1-z^2 := by nlinarith [mul_pos hm hp]
    have hbz := scalar_height_denominator hb hbq (by linarith : b ≤ 1) hz
    exact mul_ne_zero hs.ne' (pow_ne_zero 2 (by simpa only [mul_comm] using hbz.ne'))

theorem hermite_integrand_comparison (hb : 0 < b) (hbq : b ≤ 1/4) (hs : s ≤ 1)
    {z : ℝ} (hz : z ∈ Icc (scalarA b) (scalarT b)) :
    (1-scalarA b*s)*hermiteRemainderIntegrand b s z ≤
      (1-scalarA b)*originalIntegrand b z := by
  have ha := scalar_interval_bounds hb hbq
  have hz0 : 0 ≤ z := ha.1.le.trans hz.1
  have hm : 0 < 1-z := by linarith [ha.2.2, hz.2]
  have hp : 0 < 1+z := by linarith
  have hbs : 0 < 1-b*z := by
    simpa only [mul_comm] using scalar_height_denominator hb hbq (by linarith : b ≤ 1) hz
  have hzs := scalar_height_denominator hb hbq hs hz
  have hdiff : 0 ≤ (1-scalarA b)/(1-z)-(1-scalarA b*s)/(1-z*s) := by
    rw [loss_factor_difference (scalarA b) z s hm.ne' hzs.ne']
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hz.1) (sub_nonneg.mpr hs)) (mul_pos hm hzs).le
  have hbase : 0 ≤ z^2/((1+z)*(1-b*z)^2) := by positivity
  have h := mul_le_mul_of_nonneg_left (sub_nonneg.mp hdiff) hbase
  have hsq : 1-z^2 = (1-z)*(1+z) := by ring
  convert h using 1 <;>
    simp only [hermiteRemainderIntegrand, originalIntegrand, hsq] <;>
    field_simp [hp.ne', hm.ne', hbs.ne', hzs.ne'] <;> ring

theorem hermite_integral_comparison (hb : 0 < b) (hbq : b ≤ 1/4) (hs : s ≤ 1) :
    (1-scalarA b*s)*(∫ z in scalarA b..scalarT b, hermiteRemainderIntegrand b s z) ≤
      (1-scalarA b)*(∫ z in scalarA b..scalarT b, originalIntegrand b z) := by
  have ha := scalar_interval_bounds hb hbq
  have hr : IntervalIntegrable (hermiteRemainderIntegrand b s) volume (scalarA b) (scalarT b) := by
    have hc := hermiteRemainderIntegrand_continuousOn hb hbq hs
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le ha.2.1] using hc
  have hi : IntervalIntegrable (originalIntegrand b) volume (scalarA b) (scalarT b) := by
    have hc := originalIntegrand_continuousOn_interval hb hbq
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le ha.2.1] using hc
  have h := intervalIntegral.integral_mono_on ha.2.1
    (hr.const_mul (1-scalarA b*s)) (hi.const_mul (1-scalarA b))
    (fun z hz => hermite_integrand_comparison hb hbq hs hz)
  simpa only [intervalIntegral.integral_const_mul] using h

theorem logarithmic_hermite_loss (hb : 0 < b) (hbq : b ≤ 1/4)
    (hsm : -1 ≤ s) (hs : s ≤ 1) :
    -(1-scalarA b)*(∫ z in scalarA b..scalarT b, originalIntegrand b z)*
      ((1+s)*(s-b)^2)/(1-scalarA b*s) ≤
        Real.log (Determinant.heightFactor b s)-logarithmicHermite b s := by
  have ha := scalar_interval_bounds hb hbq
  have hd := scalar_height_denominator hb hbq hs ⟨le_rfl,ha.2.1⟩
  have hc : 0 ≤ (1+s)*(s-b)^2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h := hermite_integral_comparison hb hbq hs
  have hi : (∫ z in scalarA b..scalarT b, hermiteRemainderIntegrand b s z) ≤
      ((1-scalarA b)*(∫ z in scalarA b..scalarT b, originalIntegrand b z))/(1-scalarA b*s) := by
    apply (le_div_iff₀ hd).mpr
    simpa only [mul_comm] using h
  have hm := neg_le_neg (mul_le_mul_of_nonneg_left hi hc)
  rw [logarithmic_hermite_remainder hb hbq hs]
  convert hm using 1 <;> ring

end SharpCut.Scalar
