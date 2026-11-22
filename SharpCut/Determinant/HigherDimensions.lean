import SharpCut.Determinant.InterpolationLoss

/-! # The complete n ≥ 4 quantitative determinant branch -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace SharpCut.Determinant
open Certificate
variable {n N : ℕ}

def higherCoefficient (n : ℕ) : ℝ :=
  liftedGainCoefficient (inverseDimension n)*(1-Scalar.lossRatio (inverseDimension n))

theorem higherCoefficient_lower (hn : 4 ≤ n) : 1/1500 ≤ higherCoefficient n := by
  have hb := inverseDimension_bounds (show 2 ≤ n by omega)
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hbq : inverseDimension n ≤ 1/4 := one_div_le_one_div_of_le (by norm_num) hnreal
  obtain ⟨hr, hg⟩ := Scalar.uniform_certificate hb.1 hbq
  change 1/12 ≤ liftedGainCoefficient (inverseDimension n) at hg
  have hh := mul_le_mul hg hr.le (by norm_num : (0 : ℝ) ≤ 1/125) (by linarith :
    0 ≤ liftedGainCoefficient (inverseDimension n))
  norm_num at hh
  exact hh

theorem higher_loss_identity (b : ℝ) (hb : 0 < b) (hbq : b ≤ 1/4) :
    (1+b)*(1-Scalar.scalarA b)*
      (∫ z in Scalar.scalarA b..Scalar.scalarT b, Scalar.originalIntegrand b z) =
        liftedGainCoefficient b*Scalar.lossRatio b := by
  have hd : 2-b ≠ 0 := by linarith
  have h1 : 1-b ≠ 0 := by linarith
  have h2 : 2+b ≠ 0 := by linarith
  have h3 : 3+b ≠ 0 := by linarith
  have hpoly : b^2+b+2 ≠ 0 := by nlinarith [sq_nonneg b]
  have ha : 1-Scalar.scalarA b = 2*(1-b)/(2-b) := by
    unfold Scalar.scalarA
    field_simp [hd]
    ring
  rw [ha]
  unfold liftedGainCoefficient Scalar.lossRatio
  field_simp [hd, h1, h2, h3, hpoly] <;> ring

theorem higher_dimensional_logdet (F : JohnFrame n N) (hn : 4 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    higherCoefficient n*frameDefect F v ≤ Real.log (normalizedCertificate F v).det := by
  have hb := inverseDimension_bounds (show 2 ≤ n by omega)
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hbq : inverseDimension n ≤ 1/4 := one_div_le_one_div_of_le (by norm_num) hnreal
  have hl := interpolation_loss F hn v hv
  have hg := lifted_determinant_bound F hn v hv
  have hh := mul_le_mul_of_nonneg_left hl (by linarith [hb.1] : 0 ≤ 1+inverseDimension n)
  have he := higher_loss_identity (inverseDimension n) hb.1 hbq
  change (1+inverseDimension n)*(1-boostParameter n)*
    (∫ z in boostParameter n..cutWeight n, Scalar.originalIntegrand (inverseDimension n) z) = _ at he
  have hclear : higherCoefficient n*frameDefect F v =
      liftedGainCoefficient (inverseDimension n)*frameDefect F v+
        (1+inverseDimension n)*(-(1-boostParameter n)*
          (∫ z in boostParameter n..cutWeight n, Scalar.originalIntegrand (inverseDimension n) z)*
            frameDefect F v) := by
    dsimp [higherCoefficient]
    calc
      _ = liftedGainCoefficient (inverseDimension n)*frameDefect F v-
        ((1+inverseDimension n)*(1-boostParameter n)*
          (∫ z in boostParameter n..cutWeight n, Scalar.originalIntegrand (inverseDimension n) z))*
            frameDefect F v := by rw [he]; ring
      _ = _ := by ring
  rw [hclear]
  linarith only [hh, hg]

theorem higher_dimensional_uniform_logdet (F : JohnFrame n N) (hn : 4 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    (1/1500 : ℝ)*frameDefect F v ≤ Real.log (normalizedCertificate F v).det :=
  (mul_le_mul_of_nonneg_right (higherCoefficient_lower hn)
    (frameDefect_nonneg F (by omega) v hv)).trans (higher_dimensional_logdet F hn v hv)

end SharpCut.Determinant
