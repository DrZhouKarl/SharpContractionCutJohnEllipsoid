import SharpCut.Stability.LocalSpectrum
import SharpCut.Gap.ScalarCoercivity

/-! # Kernel-checked local quadratic lower bound for the real logarithm -/

noncomputable section
open MeasureTheory Set
namespace SharpCut.Stability
open Gap

theorem scalarDivergence_upper_positive {t : ℝ} (ht : 0 < t) (h1t : 1 ≤ t) :
    scalarDivergence t ≤ (t-1)^2/2 := by
  have hc : Continuous (fun x : ℝ => x-1) := by fun_prop
  have hi := divergenceSlope_continuousOn (by norm_num : (0 : ℝ) < 1) ht
  have hp : ∀ x ∈ Icc (1 : ℝ) t, divergenceSlope x ≤ x-1 := by
    intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    have he : divergenceSlope x = (x-1)/x := by unfold divergenceSlope; field_simp [hxpos.ne'] <;> ring
    rw [he]
    apply (div_le_iff₀ hxpos).mpr
    nlinarith [sq_nonneg (x-1)]
  have h := intervalIntegral.integral_mono_on (μ := volume) h1t (hi.intervalIntegrable (μ := volume))
    (hc.intervalIntegrable (μ := volume) 1 t) hp
  rw [divergence_integral ht, linear_integral_upper] at h
  exact h

theorem scalarDivergence_upper_negative {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    scalarDivergence t ≤ (t-1)^2/(2*t) := by
  have hc : Continuous (fun x : ℝ => (1-x)/t) := by fun_prop
  have hi := (divergenceSlope_continuousOn ht (by norm_num : (0 : ℝ) < 1)).neg
  have hp : ∀ x ∈ Icc t (1 : ℝ), -divergenceSlope x ≤ (1-x)/t := by
    intro x hx
    have hxpos := ht.trans_le hx.1
    have he : -divergenceSlope x = (1-x)/x := by unfold divergenceSlope; field_simp [hxpos.ne'] <;> ring
    rw [he]
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hx.2) ht hx.1
  have h := intervalIntegral.integral_mono_on (μ := volume) ht1 (hi.intervalIntegrable (μ := volume))
    (hc.intervalIntegrable (μ := volume) t 1) hp
  change (∫ x in t..(1 : ℝ), -divergenceSlope x) ≤ ∫ x in t..(1 : ℝ), (1-x)/t at h
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_symm, divergence_integral ht,
    neg_neg, intervalIntegral.integral_div, linear_integral_lower, div_div] at h
  exact h

/-- The paper's 15/29 coefficient, valid throughout the prescribed interval. -/
theorem logarithm_quadratic_lower (z : ℝ) (hz : -(1/30 : ℝ) ≤ z) :
    z-(15/29 : ℝ)*z^2 ≤ Real.log (1+z) := by
  have ht : 0 < 1+z := by linarith
  have hupper : scalarDivergence (1+z) ≤ (15/29 : ℝ)*z^2 := by
    by_cases hpos : 0 ≤ z
    · have h := scalarDivergence_upper_positive ht (by linarith : 1 ≤ 1+z)
      have hn := sq_nonneg z
      nlinarith only [h, hn]
    · have h := scalarDivergence_upper_negative ht (by linarith : 1+z ≤ 1)
      have hp : (1+z-1)^2/(2*(1+z)) ≤ (15/29 : ℝ)*z^2 := by
        apply (div_le_iff₀ (mul_pos (by norm_num) ht)).mpr
        have hm := mul_le_mul_of_nonneg_right hz (sq_nonneg z)
        nlinarith only [hm]
      exact h.trans hp
  unfold scalarDivergence at hupper
  linarith only [hupper]

end SharpCut.Stability
