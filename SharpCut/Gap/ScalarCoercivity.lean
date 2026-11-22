import SharpCut.Gap.MatrixDivergence
import SharpCut.Scalar.EndpointLogs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Exact scalar divergence bounds underlying matrix matching -/

noncomputable section
open MeasureTheory Set
namespace SharpCut.Gap

def divergenceSlope (t : ℝ) : ℝ := 1-1/t

theorem scalarDivergence_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt scalarDivergence (divergenceSlope t) t := by
  have h := ((hasDerivAt_id t).sub_const 1).sub (((hasDerivAt_id t).log ht.ne'))
  convert h using 1 <;> (try simp [divergenceSlope, id_eq, one_div])
  all_goals funext x; rfl

theorem divergenceSlope_continuousOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn divergenceSlope (uIcc a b) := by
  unfold divergenceSlope
  apply ContinuousOn.sub continuousOn_const
  apply ContinuousOn.div continuousOn_const continuousOn_id
  intro x hx
  exact ((lt_min ha hb).trans_le hx.1).ne'

theorem divergence_integral {t : ℝ} (ht : 0 < t) :
    (∫ x in (1 : ℝ)..t, divergenceSlope x) = scalarDivergence t := by
  have hd : ∀ x ∈ uIcc (1 : ℝ) t, HasDerivAt scalarDivergence (divergenceSlope x) x := by
    intro x hx
    exact scalarDivergence_hasDerivAt ((lt_min (by norm_num : (0 : ℝ) < 1) ht).trans_le hx.1)
  have hc := divergenceSlope_continuousOn (by norm_num : (0 : ℝ) < 1) ht
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  norm_num [scalarDivergence] at h ⊢
  exact h

theorem linear_integral_upper (t : ℝ) : (∫ x in (1 : ℝ)..t, x-1) = (t-1)^2/2 := by
  have hi : IntervalIntegrable (fun x : ℝ => x) volume 1 t := continuous_id.intervalIntegrable (μ := volume) 1 t
  have hc : IntervalIntegrable (fun x : ℝ => (1 : ℝ)) volume 1 t := continuous_const.intervalIntegrable (μ := volume) 1 t
  rw [intervalIntegral.integral_sub hi hc, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  ring

theorem linear_integral_lower (t : ℝ) : (∫ x in t..(1 : ℝ), 1-x) = (t-1)^2/2 := by
  have hi : IntervalIntegrable (fun x : ℝ => x) volume t 1 := continuous_id.intervalIntegrable (μ := volume) t 1
  have hc : IntervalIntegrable (fun x : ℝ => (1 : ℝ)) volume t 1 := continuous_const.intervalIntegrable (μ := volume) t 1
  rw [intervalIntegral.integral_sub hc hi, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  ring

theorem scalarDivergence_upper_side {t : ℝ} (ht : 0 < t) (h1t : 1 ≤ t) :
    (t-1)^2/(2*t) ≤ scalarDivergence t := by
  have hc : Continuous (fun x : ℝ => (x-1)/t) := by fun_prop
  have hi := divergenceSlope_continuousOn (by norm_num : (0 : ℝ) < 1) ht
  have hp : ∀ x ∈ Icc (1 : ℝ) t, (x-1)/t ≤ divergenceSlope x := by
    intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    have h := div_le_div_of_nonneg_left (sub_nonneg.mpr hx.1) hxpos hx.2
    have he : (x-1)/x = divergenceSlope x := by unfold divergenceSlope; field_simp [hxpos.ne'] <;> ring
    rwa [he] at h
  have h := intervalIntegral.integral_mono_on (μ := volume) h1t (hc.intervalIntegrable (μ := volume) 1 t)
    (hi.intervalIntegrable (μ := volume)) hp
  rw [intervalIntegral.integral_div, linear_integral_upper, divergence_integral ht, div_div] at h
  exact h

theorem scalarDivergence_lower_side {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (t-1)^2/2 ≤ scalarDivergence t := by
  have hc : Continuous (fun x : ℝ => 1-x) := by fun_prop
  have hi := (divergenceSlope_continuousOn ht (by norm_num : (0 : ℝ) < 1)).neg
  have hp : ∀ x ∈ Icc t (1 : ℝ), 1-x ≤ -divergenceSlope x := by
    intro x hx
    have hxpos := ht.trans_le hx.1
    have he : -divergenceSlope x = (1-x)/x := by unfold divergenceSlope; field_simp [hxpos.ne']; ring
    rw [he]
    apply (le_div_iff₀ hxpos).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx.2 (sub_nonneg.mpr hx.2)
  have h := intervalIntegral.integral_mono_on (μ := volume) ht1 (hc.intervalIntegrable (μ := volume) t 1)
    (hi.intervalIntegrable (μ := volume)) hp
  rw [linear_integral_lower] at h
  change (t-1)^2/2 ≤ ∫ x in t..(1 : ℝ), -divergenceSlope x at h
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_symm, divergence_integral ht, neg_neg] at h
  exact h

/-- The exact max-denominator inequality displayed in (4.7). -/
theorem scalarDivergence_coercive {t : ℝ} (ht : 0 < t) :
    (t-1)^2/(2*max 1 t) ≤ scalarDivergence t := by
  by_cases h1t : 1 ≤ t
  · rw [max_eq_right h1t]
    exact scalarDivergence_upper_side ht h1t
  · have ht1 : t ≤ 1 := le_of_not_ge h1t
    rw [max_eq_left ht1, mul_one]
    exact scalarDivergence_lower_side ht ht1

theorem scalarDivergence_two : (1/4 : ℝ) < scalarDivergence 2 := by
  have h := Scalar.log_two_le_rational
  unfold scalarDivergence
  linarith

theorem scalarDivergence_gt_quarter {t : ℝ} (ht : 2 ≤ t) : (1/4 : ℝ) < scalarDivergence t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · exact scalarDivergence_two
  · have htpos : 0 < t := by linarith
    have hl := scalarDivergence_upper_side htpos (by linarith : 1 ≤ t)
    have hp : (1/4 : ℝ) < (t-1)^2/(2*t) := by
      apply (lt_div_iff₀ (by linarith : 0 < 2*t)).mpr
      have hprod := mul_pos (show 0 < t-2 by linarith) (show 0 < t-1/2 by linarith)
      nlinarith only [hprod]
    exact hp.trans_le hl

theorem scalarDivergence_quadratic {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) :
    (t-1)^2 ≤ 4*scalarDivergence t := by
  have h := scalarDivergence_coercive ht
  have hm : 0 < max (1 : ℝ) t := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hm2 : max (1 : ℝ) t ≤ 2 := max_le (by norm_num) ht2
  have hh := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hm)).mp h
  have hnon := scalarDivergence_nonneg ht
  nlinarith only [hh, hm2, hnon]

end SharpCut.Gap
