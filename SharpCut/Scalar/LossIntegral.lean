import SharpCut.Scalar.EndpointIntegral

/-! # Domains and Möbius substitution for the original scalar loss integral -/

noncomputable section
open Set MeasureTheory
namespace SharpCut.Scalar

def scalarA (b : ℝ) : ℝ := b/(2-b)
def scalarT (b : ℝ) : ℝ := (1+b)/2
def originalIntegrand (b z : ℝ) : ℝ := z^2/((1-z^2)*(1-b*z)^2)
def lossRatio (b : ℝ) : ℝ :=
  (4*(1-b)^2*(2+b)*(3+b)/(b^2+b+2)) *
    ∫ z in scalarA b..scalarT b, originalIntegrand b z

def mobius (b w : ℝ) : ℝ := (b+(2-b)*w)/(2-b+b*w)
def mobiusDerivative (b w : ℝ) : ℝ := 4*(1-b)/(2-b+b*w)^2

theorem mobius_denominator_pos {b w : ℝ} (hb : 0 < b) (hbq : b ≤ 1/4)
    (hw : 0 ≤ w) : 0 < 2-b+b*w := by
  have h := mul_nonneg hb.le hw
  linarith

theorem mobius_one_sub_sq {b w : ℝ} (hd : 2-b+b*w ≠ 0) :
    1-(mobius b w)^2 = 4*(1-b)*(1-w^2)/(2-b+b*w)^2 := by
  unfold mobius
  field_simp [hd]
  ring

theorem mobius_one_sub_mul {b w : ℝ} (hd : 2-b+b*w ≠ 0) :
    1-b*mobius b w = (1-b)*(2+b*(1-w))/(2-b+b*w) := by
  unfold mobius
  field_simp [hd]
  ring

theorem mobius_original_denominators_pos {b w : ℝ} (hb : 0 < b) (hbq : b ≤ 1/4)
    (hw : 0 ≤ w) (hwh : w ≤ 9/17) :
    0 < 1-(mobius b w)^2 ∧ 0 < 1-b*mobius b w := by
  have hd := mobius_denominator_pos hb hbq hw
  have hb1 : 0 < 1-b := by linarith
  have hw1 := (endpoint_denominators_positive w hw hwh).2.2.2
  have hp := ratioFactor_denominator_pos hb.le hwh
  constructor
  · rw [mobius_one_sub_sq hd.ne']
    positivity
  · rw [mobius_one_sub_mul hd.ne']
    exact div_pos (mul_pos hb1 hp) hd

theorem mobius_hasDerivAt {b w : ℝ} (hd : 2-b+b*w ≠ 0) :
    HasDerivAt (mobius b) (mobiusDerivative b w) w := by
  have hn := ((hasDerivAt_id w).const_mul (2-b)).const_add b
  have hdv := ((hasDerivAt_id w).const_mul b).const_add (2-b)
  have h := hn.div hdv hd
  convert h using 1
  · rfl
  · simp only [mobiusDerivative, id_eq]
    ring

theorem mobiusDerivative_continuousOn {b : ℝ} (hb : 0 < b) (hbq : b ≤ 1/4) :
    ContinuousOn (mobiusDerivative b) (Icc 0 (9/17)) := by
  unfold mobiusDerivative
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro w hw
    exact pow_ne_zero 2 (mobius_denominator_pos hb hbq hw.1).ne'

@[simp] theorem mobius_zero (b : ℝ) : mobius b 0 = scalarA b := by
  simp [mobius, scalarA]

theorem mobius_endpoint {b : ℝ} (hb : 0 < b) (hbq : b ≤ 1/4) :
    mobius b (ratioEndpoint b) = scalarT b := by
  have hd0 : 2-b ≠ 0 := by linarith
  have hd4 : 4+b ≠ 0 := by linarith
  have hd := mobius_denominator_pos hb hbq (ratioEndpoint_bounds hb.le hbq).1
  unfold mobius ratioEndpoint scalarT
  field_simp [hd0, hd4, hd.ne']
  ring

theorem originalIntegrand_substitution {b w : ℝ} (hb : 0 < b) (hbq : b ≤ 1/4)
    (hw : 0 ≤ w) (hwh : w ≤ 9/17) :
    originalIntegrand b (mobius b w)*mobiusDerivative b w =
      ratioIntegrand b w/(1-b)^2 := by
  have hd := mobius_denominator_pos hb hbq hw
  have hb1 : 1-b ≠ 0 := by linarith
  have hw1 := (endpoint_denominators_positive w hw hwh).2.2.2.ne'
  have hp := (ratioFactor_denominator_pos hb.le hwh).ne'
  unfold originalIntegrand mobiusDerivative
  rw [mobius_one_sub_sq hd.ne', mobius_one_sub_mul hd.ne']
  unfold mobius ratioIntegrand ratioFactor
  field_simp [hd.ne', hb1, hw1, hp] <;> ring

theorem originalIntegrand_continuousOn_image {b : ℝ} (hb : 0 < b) (hbq : b ≤ 1/4) :
    ContinuousOn (originalIntegrand b) (mobius b '' uIcc 0 (ratioEndpoint b)) := by
  have he := ratioEndpoint_bounds hb.le hbq
  unfold originalIntegrand
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · rintro z ⟨w, hw, rfl⟩
    rw [uIcc_of_le he.1] at hw
    have h := mobius_original_denominators_pos hb hbq hw.1 (hw.2.trans he.2)
    exact mul_ne_zero h.1.ne' (pow_ne_zero 2 h.2.ne')

theorem lossRatio_eq_transformedRatio {b : ℝ} (hb : 0 < b) (hbq : b ≤ 1/4) :
    lossRatio b = transformedRatio b := by
  have he := ratioEndpoint_bounds hb.le hbq
  have hder : ∀ w ∈ uIcc 0 (ratioEndpoint b),
      HasDerivAt (mobius b) (mobiusDerivative b w) w := by
    intro w hw
    rw [uIcc_of_le he.1] at hw
    exact mobius_hasDerivAt (mobius_denominator_pos hb hbq hw.1).ne'
  have hcont : ContinuousOn (mobiusDerivative b) (uIcc 0 (ratioEndpoint b)) := by
    apply (mobiusDerivative_continuousOn hb hbq).mono
    rw [uIcc_of_le he.1]
    exact Icc_subset_Icc le_rfl he.2
  have hs := intervalIntegral.integral_comp_mul_deriv' hder hcont
    (originalIntegrand_continuousOn_image hb hbq)
  simp only [Function.comp_apply, mobius_zero, mobius_endpoint hb hbq] at hs
  have hpoint : (∫ w in 0..ratioEndpoint b,
      originalIntegrand b (mobius b w)*mobiusDerivative b w) =
      ∫ w in 0..ratioEndpoint b, ratioIntegrand b w/(1-b)^2 := by
    apply intervalIntegral.integral_congr
    intro w hw
    rw [uIcc_of_le he.1] at hw
    exact originalIntegrand_substitution hb hbq hw.1 (hw.2.trans he.2)
  rw [hpoint, intervalIntegral.integral_div] at hs
  unfold lossRatio transformedRatio ratioPrefactor
  rw [← hs]
  have hb1 : 1-b ≠ 0 := by linarith
  have hden := (rational_prefactor_denominator_positive b hb.le).ne'
  field_simp [hb1, hden]

/-- Lemma 8.4 on the complete real interval, using the original integral. -/
theorem uniform_certificate {b : ℝ} (hb : 0 < b) (hbq : b ≤ 1/4) :
    1/125 < 1-lossRatio b ∧
      1/12 ≤ (1+b)*(b^2+b+2)/(2*(2-b)*(1-b)*(2+b)*(3+b)) := by
  refine ⟨?_, gain_coefficient_lower b hb hbq⟩
  rw [lossRatio_eq_transformedRatio hb hbq]
  have h := transformedRatio_lt hb.le hbq
  linarith

end SharpCut.Scalar
