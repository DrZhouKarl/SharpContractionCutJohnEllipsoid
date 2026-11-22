import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import SharpCut.Scalar.EndpointLogs
import SharpCut.Scalar.Domains

/-! # Compact-interval scalar certificate preparation

All arguments are real, with 0 ≤ b ≤ 1/4. This module defines the transformed
integral of (8.32) and proves the positive domains and parameter monotonicity.
The relation to the original integral is a separate change-of-variables step.
-/

noncomputable section
open Set MeasureTheory
namespace SharpCut.Scalar

def ratioPrefactor (b : ℝ) : ℝ := 4*(2+b)*(3+b)/(b^2+b+2)
def ratioEndpoint (b : ℝ) : ℝ := (2+b)/(4+b)
def ratioFactor (b w : ℝ) : ℝ := (2*w+b*(1-w))/(2+b*(1-w))
def ratioIntegrand (b w : ℝ) : ℝ := (ratioFactor b w)^2/(1-w^2)
def transformedRatio (b : ℝ) : ℝ :=
  ratioPrefactor b * ∫ w in 0..ratioEndpoint b, ratioIntegrand b w

theorem ratioFactor_denominator_pos {b w : ℝ} (hb : 0 ≤ b) (hw : w ≤ 9/17) :
    0 < 2+b*(1-w) := by
  have h := mul_nonneg hb (show 0 ≤ 1-w by linarith)
  linarith

theorem ratioFactor_nonneg {b w : ℝ} (hb : 0 ≤ b) (hw : 0 ≤ w) (hwh : w ≤ 9/17) :
    0 ≤ ratioFactor b w := by
  apply div_nonneg
  · exact add_nonneg (mul_nonneg (by norm_num) hw) (mul_nonneg hb (by linarith))
  · exact (ratioFactor_denominator_pos hb hwh).le

theorem ratioIntegrand_nonneg {b w : ℝ} (hw : 0 ≤ w) (hwh : w ≤ 9/17) :
    0 ≤ ratioIntegrand b w :=
  div_nonneg (sq_nonneg _) (endpoint_denominators_positive w hw hwh).2.2.2.le

theorem ratioPrefactor_nonneg {b : ℝ} (hb : 0 ≤ b) : 0 ≤ ratioPrefactor b := by
  have hd := rational_prefactor_denominator_positive b hb
  unfold ratioPrefactor
  positivity

theorem ratioEndpoint_mono {b1 b2 : ℝ} (h1 : 0 ≤ b1) (h12 : b1 ≤ b2) :
    ratioEndpoint b1 ≤ ratioEndpoint b2 := by
  have hd1 : 0 < 4+b1 := by linarith
  have hd2 : 0 < 4+b2 := by linarith
  have he := interval_endpoint_difference b1 b2 hd1.ne' hd2.ne'
  have hn : 0 ≤ 2*(b2-b1)/((4+b1)*(4+b2)) :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr h12)) (mul_pos hd1 hd2).le
  unfold ratioEndpoint
  linarith

theorem ratioEndpoint_bounds {b : ℝ} (hb : 0 ≤ b) (hbq : b ≤ 1/4) :
    0 ≤ ratioEndpoint b ∧ ratioEndpoint b ≤ 9/17 := by
  constructor
  · unfold ratioEndpoint; positivity
  · have h := ratioEndpoint_mono hb hbq
    norm_num [ratioEndpoint] at h
    exact h

theorem ratioPrefactor_mono {b1 b2 : ℝ} (h1 : 0 ≤ b1) (h12 : b1 ≤ b2)
    (h2q : b2 ≤ 1/4) : ratioPrefactor b1 ≤ ratioPrefactor b2 := by
  have h2 : 0 ≤ b2 := by linarith
  have hd1 := rational_prefactor_denominator_positive b1 h1
  have hd2 := rational_prefactor_denominator_positive b2 h2
  have hc := monotonicity_numerator_lower b1 b2 h1 (by linarith) h2 h2q
  have he := prefactor_difference b1 b2 hd1.ne' hd2.ne'
  have hn : 0 ≤ 16*(b2-b1)*(1-b1-b2-b1*b2)/((b1^2+b1+2)*(b2^2+b2+2)) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr h12))
      (by linarith)) (mul_pos hd1 hd2).le
  unfold ratioPrefactor
  linarith

theorem ratioFactor_mono {b1 b2 w : ℝ} (h1 : 0 ≤ b1) (h12 : b1 ≤ b2)
    (hwh : w ≤ 9/17) : ratioFactor b1 w ≤ ratioFactor b2 w := by
  have hd1 := ratioFactor_denominator_pos h1 hwh
  have hd2 := ratioFactor_denominator_pos (show 0 ≤ b2 by linarith) hwh
  have he := integrand_factor_difference b1 b2 w hd1.ne' hd2.ne'
  have hn : 0 ≤ 2*(b2-b1)*(1-w)^2/((2+b1*(1-w))*(2+b2*(1-w))) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr h12))
      (sq_nonneg _)) (mul_pos hd1 hd2).le
  unfold ratioFactor
  linarith

theorem ratioFactor_continuousOn {b : ℝ} (hb : 0 ≤ b) :
    ContinuousOn (ratioFactor b) (Icc 0 (9/17)) := by
  unfold ratioFactor
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro w hw
    exact (ratioFactor_denominator_pos hb hw.2).ne'

theorem ratioIntegrand_continuousOn {b : ℝ} (hb : 0 ≤ b) :
    ContinuousOn (ratioIntegrand b) (Icc 0 (9/17)) := by
  unfold ratioIntegrand
  apply ContinuousOn.div
  · exact (ratioFactor_continuousOn hb).pow 2
  · fun_prop
  · intro w hw
    exact (endpoint_denominators_positive w hw.1 hw.2).2.2.2.ne'

theorem ratioIntegrand_mono {b1 b2 w : ℝ} (h1 : 0 ≤ b1) (h12 : b1 ≤ b2)
    (hw : 0 ≤ w) (hwh : w ≤ 9/17) : ratioIntegrand b1 w ≤ ratioIntegrand b2 w := by
  have hf := ratioFactor_mono h1 h12 hwh
  have hf1 := ratioFactor_nonneg h1 hw hwh
  have hf2 := ratioFactor_nonneg (show 0 ≤ b2 by linarith) hw hwh
  apply div_le_div_of_nonneg_right _ (endpoint_denominators_positive w hw hwh).2.2.2.le
  have hm := mul_nonneg (sub_nonneg.mpr hf) (show 0 ≤ ratioFactor b2 w+ratioFactor b1 w by linarith)
  nlinarith

theorem ratioIntegrand_intervalIntegrable {b c : ℝ} (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hch : c ≤ 9/17) : IntervalIntegrable (ratioIntegrand b) volume 0 c := by
  apply ContinuousOn.intervalIntegrable
  apply (ratioIntegrand_continuousOn hb).mono
  rw [uIcc_of_le hc]
  exact Icc_subset_Icc le_rfl hch

theorem ratio_integral_nonneg {b : ℝ} (hb : 0 ≤ b) (hbq : b ≤ 1/4) :
    0 ≤ ∫ w in 0..ratioEndpoint b, ratioIntegrand b w := by
  have he := ratioEndpoint_bounds hb hbq
  exact intervalIntegral.integral_nonneg he.1
    (fun w hw => ratioIntegrand_nonneg hw.1 (hw.2.trans he.2))

theorem ratio_integral_mono {b1 b2 : ℝ} (h1 : 0 ≤ b1) (h12 : b1 ≤ b2)
    (h2q : b2 ≤ 1/4) :
    (∫ w in 0..ratioEndpoint b1, ratioIntegrand b1 w) ≤
      ∫ w in 0..ratioEndpoint b2, ratioIntegrand b2 w := by
  have h2 : 0 ≤ b2 := by linarith
  have he1 := ratioEndpoint_bounds h1 (show b1 ≤ 1/4 by linarith)
  have he2 := ratioEndpoint_bounds h2 h2q
  have hfirst := intervalIntegral.integral_mono_on he1.1
    (ratioIntegrand_intervalIntegrable h1 he1.1 he1.2)
    (ratioIntegrand_intervalIntegrable h2 he1.1 he1.2)
    (fun w hw => ratioIntegrand_mono h1 h12 hw.1 (hw.2.trans he1.2))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc 0 (ratioEndpoint b2))] ratioIntegrand b2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
    exact ratioIntegrand_nonneg hw.1.le (hw.2.trans he2.2)
  have hsecond := intervalIntegral.integral_mono_interval
    (a := 0) (b := ratioEndpoint b1) (c := 0) (d := ratioEndpoint b2)
    le_rfl he1.1 (ratioEndpoint_mono h1 h12) hnonneg
    (ratioIntegrand_intervalIntegrable h2 he2.1 he2.2)
  exact hfirst.trans hsecond

theorem transformedRatio_mono {b1 b2 : ℝ} (h1 : 0 ≤ b1) (h12 : b1 ≤ b2)
    (h2q : b2 ≤ 1/4) : transformedRatio b1 ≤ transformedRatio b2 := by
  unfold transformedRatio
  exact mul_le_mul (ratioPrefactor_mono h1 h12 h2q) (ratio_integral_mono h1 h12 h2q)
    (ratio_integral_nonneg h1 (by linarith)) (ratioPrefactor_nonneg (by linarith))

end SharpCut.Scalar
