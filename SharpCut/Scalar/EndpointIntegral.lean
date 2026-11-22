import SharpCut.Scalar.IntegralCertificate

/-! # Exact evaluation of the compact endpoint integral in (8.34)--(8.36) -/

noncomputable section
open Set MeasureTheory
namespace SharpCut.Scalar

def endpointIntegrand (w : ℝ) : ℝ := (1+7*w)^2/((1-w^2)*(9-w)^2)

def endpointPrimitive (w : ℝ) : ℝ :=
  9/50*Real.log (1+w)-1/2*Real.log (1-w)+8/25*Real.log (9-w)-256/5*(9-w)⁻¹

theorem endpointPrimitive_hasDerivAt {w : ℝ}
    (hp : 1+w ≠ 0) (hm : 1-w ≠ 0) (h9 : 9-w ≠ 0) :
    HasDerivAt endpointPrimitive (endpointIntegrand w) w := by
  have h1 := ((hasDerivAt_id w).const_add 1).log hp
  have h2 := ((hasDerivAt_id w).const_sub 1).log hm
  have hn := ((hasDerivAt_id w).const_sub 9).log h9
  have hi := ((hasDerivAt_id w).const_sub 9).inv h9
  have h := (((h1.const_mul (9/50)).sub (h2.const_mul (1/2))).add
    (hn.const_mul (8/25))).sub (hi.const_mul (256/5))
  convert h using 1
  · rfl
  · rw [endpointIntegrand, endpoint_partial_fractions w hp hm h9]
    simp only [id_eq]
    field_simp [hp, hm, h9]
    ring

theorem endpointIntegrand_continuousOn : ContinuousOn endpointIntegrand (Icc 0 (9/17)) := by
  unfold endpointIntegrand
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro w hw
    have h := endpoint_denominators_positive w hw.1 hw.2
    exact mul_ne_zero h.2.2.2.ne' (pow_ne_zero 2 h.2.2.1.ne')

theorem endpointPrimitive_difference :
    endpointPrimitive (9/17)-endpointPrimitive 0 =
      9/50*Real.log 13-1/25*Real.log 2-16/45 := by
  have h26 : Real.log (26 : ℝ) = Real.log 2+Real.log 13 := by
    rw [show (26 : ℝ) = 2*13 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h8 : Real.log (8 : ℝ) = 3*Real.log 2 := by
    rw [show (8 : ℝ) = 2^3 by norm_num, Real.log_pow]
    norm_num
  have h144 : Real.log (144 : ℝ) = 4*Real.log 2+Real.log 9 := by
    rw [show (144 : ℝ) = 2^4*9 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num [endpointPrimitive]
  rw [Real.log_div (x := (26 : ℝ)) (y := 17) (by norm_num) (by norm_num),
    Real.log_div (x := (8 : ℝ)) (y := 17) (by norm_num) (by norm_num),
    Real.log_div (x := (144 : ℝ)) (y := 17) (by norm_num) (by norm_num), h26, h8, h144]
  ring

theorem endpointIntegral_eq :
    (∫ w in (0 : ℝ)..9/17, endpointIntegrand w) =
      9/50*Real.log 13-1/25*Real.log 2-16/45 := by
  have hle : (0 : ℝ) ≤ 9/17 := by norm_num
  have hd : ∀ w ∈ uIcc (0 : ℝ) (9/17), HasDerivAt endpointPrimitive (endpointIntegrand w) w := by
    intro w hw
    rw [uIcc_of_le hle] at hw
    have h := endpoint_denominators_positive w hw.1 hw.2
    exact endpointPrimitive_hasDerivAt h.1.ne' h.2.1.ne' h.2.2.1.ne'
  have hc : ContinuousOn endpointIntegrand (uIcc (0 : ℝ) (9/17)) := by
    simpa only [uIcc_of_le hle] using endpointIntegrand_continuousOn
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable).trans
    endpointPrimitive_difference

theorem quarter_integrand_eq {w : ℝ} (hw : 0 ≤ w) (hwh : w ≤ 9/17) :
    ratioIntegrand (1/4) w = endpointIntegrand w := by
  have h := endpoint_denominators_positive w hw hwh
  have hf : ratioFactor (1/4) w = (1+7*w)/(9-w) := by
    unfold ratioFactor
    rw [show 2*w+(1/4 : ℝ)*(1-w) = (1+7*w)/4 by ring,
      show (2 : ℝ)+1/4*(1-w) = (9-w)/4 by ring]
    exact div_div_div_cancel_right₀ (by norm_num : (4 : ℝ) ≠ 0) _ _
  unfold ratioIntegrand endpointIntegrand
  rw [hf, div_pow, div_div]
  congr 1
  ring

theorem transformedRatio_quarter :
    transformedRatio (1/4) = (2106*Real.log 13-468*Real.log 2-4160)/925 := by
  have hle : (0 : ℝ) ≤ 9/17 := by norm_num
  have he : (∫ w in (0 : ℝ)..9/17, ratioIntegrand (1/4) w) =
      ∫ w in (0 : ℝ)..9/17, endpointIntegrand w := by
    apply intervalIntegral.integral_congr
    intro w hw
    rw [uIcc_of_le hle] at hw
    exact quarter_integrand_eq hw.1 hw.2
  unfold transformedRatio
  norm_num [ratioPrefactor, ratioEndpoint]
  rw [he, endpointIntegral_eq]
  exact endpoint_integral_recombination (Real.log 2) (Real.log 13)

theorem transformedRatio_lt {b : ℝ} (hb : 0 ≤ b) (hbq : b ≤ 1/4) :
    transformedRatio b < 124/125 := by
  have h := transformedRatio_mono hb hbq (show (1/4 : ℝ) ≤ 1/4 by rfl)
  rw [transformedRatio_quarter] at h
  exact h.trans_lt endpoint_logarithm_certificate

end SharpCut.Scalar
