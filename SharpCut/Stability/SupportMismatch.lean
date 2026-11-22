import SharpCut.Stability.ContactStability

/-! # Exact model support mismatch and its weighted defect control -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Stability
open Certificate
variable {n N : ℕ}

def modelMismatch (v u : V n) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u‖-1-⟪u,v⟫/2

theorem modelShape_unit_lower (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    (1/2 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u‖ := by
  have hb := inverseDimension_bounds hn
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hs := transverse_norm_sq v u hv hu
  have hnrm := sq_nonneg ‖transverse v u‖
  have hlow : (1-⟪u,v⟫^2)/4 ≤ (1-⟪u,v⟫^2)/(1-inverseDimension n) := by
    apply (le_div_iff₀ h1).mpr
    have hp := mul_nonneg hb.1.le (show 0 ≤ 1-⟪u,v⟫^2 by linarith only [hs, hnrm])
    nlinarith only [hp, hs, hnrm]
  have hsq := Sharpness.modelShape_norm_sq hn v u hv hu
  have hp := norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u)
  nlinarith only [hlow, hsq, hp]

/-- Equations (9.19) and (9.20) retain the actual positive shape action. -/
theorem model_support_mismatch_identity (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u‖^2-(1+⟪u,v⟫/2)^2 =
      (1+⟪u,v⟫)*(inverseDimension n-⟪u,v⟫)/(1-inverseDimension n) ∧
    modelMismatch v u = (1+⟪u,v⟫)*(inverseDimension n-⟪u,v⟫)/
      ((1-inverseDimension n)*(‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u‖+1+⟪u,v⟫/2)) := by
  have hb := inverseDimension_bounds hn
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hsq := Sharpness.modelShape_norm_sq hn v u hv hu
  have hnorm := modelShape_unit_lower hn v u hv hu
  have hs := abs_le.mp (by simpa only [hu, hv, mul_one] using abs_real_inner_le_norm u v)
  have hden : 0 < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u‖+1+⟪u,v⟫/2 := by
    linarith only [hnorm, hs.1]
  have hdiff : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u‖^2-(1+⟪u,v⟫/2)^2 =
      (1+⟪u,v⟫)*(inverseDimension n-⟪u,v⟫)/(1-inverseDimension n) := by
    rw [hsq]
    field_simp [h1.ne'] <;> ring
  refine ⟨hdiff, ?_⟩
  unfold modelMismatch
  apply (eq_div_iff (mul_pos h1 hden).ne').mpr
  have h := (eq_div_iff h1.ne').mp hdiff
  nlinarith only [h]

theorem latitude_denominator_product (a s : ℝ) (ha : 0 ≤ a) (hah : a ≤ 1/3) (hs : -1 ≤ s) (hsh : s ≤ 1) :
    (1+s)*(1-a*s) ≤ 2 := by
  have hsp : 0 ≤ 1+s := by linarith
  by_cases h0 : 0 ≤ s
  · have hden : 1-a*s ≤ 1 := by nlinarith only [mul_nonneg ha h0]
    have h := mul_le_mul_of_nonneg_left hden hsp
    nlinarith only [h, hsh]
  · have hs0 : s ≤ 0 := le_of_not_ge h0
    have hden : 1-a*s ≤ 4/3 := by nlinarith only [mul_le_mul_of_nonneg_left hs ha, hah]
    have h := mul_le_mul_of_nonneg_left hden hsp
    nlinarith only [h, hs0]

/-- The pointwise factor-eight support estimate (9.21). -/
theorem model_support_mismatch_bound (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    (modelMismatch v u)^2 ≤ 8*((1+⟪u,v⟫)*(⟪u,v⟫-inverseDimension n)^2/(1-boostParameter n*⟪u,v⟫)) := by
  have hb := inverseDimension_bounds hn
  have ha : 0 < boostParameter n ∧ boostParameter n ≤ 1/3 := Scalar.lorentz_parameter_bounds _ hb.1 hb.2
  have hs := abs_le.mp (by simpa only [hu, hv, mul_one] using abs_real_inner_le_norm u v)
  have hden : 0 < 1-boostParameter n*⟪u,v⟫ := by
    have h := certificate_denominator_lower hn hs.2
    change 2/3 ≤ 1-boostParameter n*⟪u,v⟫ at h
    linarith
  have hpos : 0 ≤ 1+⟪u,v⟫ := by linarith only [hs.1]
  have hnorm := modelShape_unit_lower hn v u hv hu
  have hsum : 1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u‖+1+⟪u,v⟫/2 := by
    linarith only [hnorm, hs.1]
  have hcoeff : 1/4 ≤ (1-inverseDimension n)^2 := by nlinarith only [hb.2, sq_nonneg (inverseDimension n-1/2)]
  have hplus : 1 ≤ (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u‖+1+⟪u,v⟫/2)^2 := by
    nlinarith only [hsum, sq_nonneg (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u‖+1+⟪u,v⟫/2-1)]
  have hcoeffprod : 1/4 ≤ (1-inverseDimension n)^2*
      (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u‖+1+⟪u,v⟫/2)^2 := by
    have h := mul_le_mul_of_nonneg_left hplus (sq_nonneg (1-inverseDimension n))
    nlinarith only [h, hcoeff]
  have hid := (model_support_mismatch_identity hn v u hv hu).2
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hD : 0 < (1-inverseDimension n)*(‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u‖+1+⟪u,v⟫/2) := mul_pos h1 (by linarith only [hsum])
  have hid' := congrArg (fun x : ℝ => x^2) ((eq_div_iff hD.ne').mp hid)
  simp only [mul_pow] at hid'
  have hlow := mul_le_mul_of_nonneg_right hcoeffprod (sq_nonneg (modelMismatch v u))
  have hprod := latitude_denominator_product (boostParameter n) ⟪u,v⟫ ha.1.le ha.2 hs.1 hs.2
  have hhigh := mul_le_mul_of_nonneg_right hprod (mul_nonneg hpos (sq_nonneg (⟪u,v⟫-inverseDimension n)))
  have hlow' := mul_le_mul_of_nonneg_right hlow hden.le
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hden).mpr
  have heq : (inverseDimension n-⟪u,v⟫)^2 = (⟪u,v⟫-inverseDimension n)^2 := by ring
  rw [heq] at hid'
  have hidmul := congrArg (fun r : ℝ => r*(1-boostParameter n*⟪u,v⟫)) hid'
  nlinarith only [hidmul, hlow', hhigh]

/-- Weighted support mismatch control, required for recovering the center. -/
theorem weighted_model_mismatch_bound (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (∑ i, F.weight i*(modelMismatch v (F.contact i))^2) ≤ 8*frameDefect F v := by
  unfold frameDefect defectTerm height
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left (model_support_mismatch_bound hn v (F.contact i) hv (F.contact_unit i)) (F.weight_pos i).le
  convert h using 1 <;> ring

end SharpCut.Stability
