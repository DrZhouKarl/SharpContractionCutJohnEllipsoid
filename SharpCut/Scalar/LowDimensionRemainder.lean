import SharpCut.Scalar.EndpointSupplement

/-! # Exact polynomial integral lower certificates for the scalar remainder in n=2 and n=3 -/

noncomputable section
open Set MeasureTheory
namespace SharpCut.Scalar

def polynomialLowerIntegrand (b z : ℝ) : ℝ := z^2*(1+z^2+z^4)*(1+2*b*z+3*b^2*z^2)
def polynomialLowerPrimitive (b z : ℝ) : ℝ :=
  (1/3 : ℝ)*z^3+(b/2)*z^4+((1+3*b^2)/5)*z^5+(b/3)*z^6+
    ((1+3*b^2)/7)*z^7+(b/4)*z^8+(b^2/3)*z^9

/-- The antiderivative is proved symbolically for every real parameter and endpoint. -/
theorem polynomialLowerPrimitive_hasDerivAt (b z : ℝ) :
    HasDerivAt (polynomialLowerPrimitive b) (polynomialLowerIntegrand b z) z := by
  have h1 := ((hasDerivAt_id z).pow 3).const_mul (1/3 : ℝ)
  have h2 := ((hasDerivAt_id z).pow 4).const_mul (b/2)
  have h3 := ((hasDerivAt_id z).pow 5).const_mul ((1+3*b^2)/5)
  have h4 := ((hasDerivAt_id z).pow 6).const_mul (b/3)
  have h5 := ((hasDerivAt_id z).pow 7).const_mul ((1+3*b^2)/7)
  have h6 := ((hasDerivAt_id z).pow 8).const_mul (b/4)
  have h7 := ((hasDerivAt_id z).pow 9).const_mul (b^2/3)
  have h := (((((h1.add h2).add h3).add h4).add h5).add h6).add h7
  convert h using 1
  · rfl
  · simp only [polynomialLowerIntegrand, id_eq]
    ring

theorem polynomial_lower_integral (b a t : ℝ) :
    (∫ z in a..t, polynomialLowerIntegrand b z) = polynomialLowerPrimitive b t-polynomialLowerPrimitive b a := by
  have hc : Continuous (polynomialLowerIntegrand b) := by unfold polynomialLowerIntegrand; fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z hz => polynomialLowerPrimitive_hasDerivAt b z)
    (hc.intervalIntegrable a t)

/-- The two reciprocal lower bounds in (8.38), on their full positive denominator domains. -/
theorem reciprocal_polynomial_lower (z s : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) (hs : 0 ≤ s) (hs1 : s < 1) :
    1+z^2+z^4 ≤ 1/(1-z^2) ∧ 1+2*s+3*s^2 ≤ 1/(1-s)^2 := by
  have hd1 : 0 < 1-z^2 := by nlinarith only [hz, hz1]
  have hd2 : 0 < (1-s)^2 := sq_pos_of_pos (by linarith only [hs1])
  have hpoly1 : (1+z^2+z^4)*(1-z^2) = 1-z^6 := by ring
  have hpoly2 : (1+2*s+3*s^2)*(1-s)^2 = 1-s^3*(4-3*s) := by ring
  constructor
  · apply (le_div_iff₀ hd1).mpr
    rw [hpoly1]
    exact sub_le_self _ (pow_nonneg hz 6)
  · apply (le_div_iff₀ hd2).mpr
    rw [hpoly2]
    exact sub_le_self _ (mul_nonneg (pow_nonneg hs 3) (by linarith only [hs1]))

/-- Every denominator is positive throughout the original integration interval up to b=1/2. -/
theorem low_dimension_integration_domain (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 1/2) :
    scalarA b ≤ scalarT b ∧ ∀ z ∈ Icc (scalarA b) (scalarT b), 0 ≤ z ∧ z < 1 ∧ 0 ≤ b*z ∧ b*z < 1 := by
  have hd : 0 < 2-b := by linarith only [hb2]
  have ha : 0 < scalarA b := div_pos hb hd
  have ht : scalarT b ≤ 3/4 := by unfold scalarT; linarith only [hb2]
  have hat : scalarA b ≤ scalarT b := by
    unfold scalarA scalarT
    apply (div_le_iff₀ hd).mpr
    nlinarith only [hb, hb2, sq_nonneg (b-1/2)]
  refine ⟨hat, ?_⟩
  intro z hz
  have hz0 : 0 ≤ z := (ha.trans_le hz.1).le
  have hz3 : z ≤ 3/4 := hz.2.trans ht
  have hprod := mul_le_mul_of_nonneg_right hb2 hz0
  have hbz : b*z < 1 := by nlinarith only [hprod, hz3]
  exact ⟨hz0, by linarith only [hz3], mul_nonneg hb.le hz0, hbz⟩

theorem polynomial_integrand_lower (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 1/2)
    (z : ℝ) (hz : z ∈ Icc (scalarA b) (scalarT b)) : polynomialLowerIntegrand b z ≤ originalIntegrand b z := by
  have hd := (low_dimension_integration_domain b hb hb2).2 z hz
  have hlo := reciprocal_polynomial_lower z (b*z) hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
  have hf : 0 ≤ 1+z^2+z^4 := by positivity
  have hbz0 : 0 ≤ b*z := hd.2.2.1
  have hg : 0 ≤ 1+2*(b*z)+3*(b*z)^2 := by positivity
  have hdiv : 0 ≤ 1/(1-z^2) := by
    have hp : 0 < 1-z^2 := by nlinarith only [hd.1, hd.2.1]
    exact div_nonneg (by norm_num) hp.le
  have hm := mul_le_mul hlo.1 hlo.2 hg hdiv
  have ht := mul_le_mul_of_nonneg_left hm (sq_nonneg z)
  unfold polynomialLowerIntegrand originalIntegrand
  simp only [div_eq_mul_inv, _root_.mul_inv_rev] at ht ⊢
  convert ht using 1 <;> ring

/-- The actual scalar loss is bounded below by the exact polynomial integral in (8.39). -/
theorem lossRatio_polynomial_lower (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 1/2) :
    (4*(1-b)^2*(2+b)*(3+b)/(b^2+b+2)) *
      (polynomialLowerPrimitive b (scalarT b)-polynomialLowerPrimitive b (scalarA b)) ≤ lossRatio b := by
  have hdom := low_dimension_integration_domain b hb hb2
  have hpoly : Continuous (polynomialLowerIntegrand b) := by unfold polynomialLowerIntegrand; fun_prop
  have horig : ContinuousOn (originalIntegrand b) (Icc (scalarA b) (scalarT b)) := by
    unfold originalIntegrand
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro z hz
      have hd := hdom.2 z hz
      exact mul_ne_zero (by nlinarith only [hd.1, hd.2.1] : 1-z^2 ≠ 0) (pow_ne_zero 2 (by linarith only [hd.2.2.2] : 1-b*z ≠ 0))
  have hcont : ContinuousOn (originalIntegrand b) (uIcc (scalarA b) (scalarT b)) := by
    simpa only [uIcc_of_le hdom.1] using horig
  have hintegrable : IntervalIntegrable (originalIntegrand b) volume (scalarA b) (scalarT b) := hcont.intervalIntegrable
  have hi := intervalIntegral.integral_mono_on hdom.1 (hpoly.intervalIntegrable _ _) hintegrable
    (fun z hz => polynomial_integrand_lower b hb hb2 z hz)
  rw [polynomial_lower_integral] at hi
  have hp : 0 ≤ 4*(1-b)^2*(2+b)*(3+b)/(b^2+b+2) := by positivity
  exact mul_le_mul_of_nonneg_left hi hp

/-- Both numerical thresholds are exact rational polynomial evaluations checked by Lean's kernel. -/
theorem low_dimension_scalar_remainder : (16/15 : ℝ) < lossRatio (1/3) ∧ (7/6 : ℝ) < lossRatio (1/2) := by
  have h3 := lossRatio_polynomial_lower (1/3) (by norm_num) (by norm_num)
  have h2 := lossRatio_polynomial_lower (1/2) (by norm_num) (by norm_num)
  norm_num [polynomialLowerPrimitive, scalarA, scalarT] at h3 h2
  constructor <;> linarith only [h3, h2]

end SharpCut.Scalar
