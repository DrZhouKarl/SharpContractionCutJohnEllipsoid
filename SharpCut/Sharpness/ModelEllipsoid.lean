import SharpCut.Sharpness.ContactConstruction

/-! # The actual extremal ellipsoid: positive shape, inverse and exact determinant -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Sharpness
open Certificate
variable {n : ℕ}

def modelCenter (v : V n) : V n := (-1/2 : ℝ) • v
def modelShape (v : V n) : MatR n :=
  (1/2 : ℝ) • outer v+(Real.sqrt (1-inverseDimension n))⁻¹ • projector v

theorem inverseModel_posDef (hn : 2 ≤ n) (v : V n) : (inverseModel v).PosDef := by
  have hb := inverseDimension_bounds hn
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hs : 0 < Real.sqrt (1-inverseDimension n) := Real.sqrt_pos.mpr h1
  have hsq := Real.sq_sqrt h1.le
  have hcoef : 0 ≤ 2-Real.sqrt (1-inverseDimension n) := by nlinarith [hb.1]
  have he : inverseModel v = Real.sqrt (1-inverseDimension n) • (1 : MatR n)+
      (2-Real.sqrt (1-inverseDimension n)) • outer v := by
    unfold inverseModel projector
    simp only [smul_sub, sub_smul]
    abel
  rw [he]
  exact (Matrix.PosDef.one.smul hs).add_posSemidef ((Khachiyan.outer_posSemidef v).smul hcoef)

theorem modelShape_mul_inverseModel (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    modelShape v*inverseModel v = 1 := by
  have hb := inverseDimension_bounds hn
  have hs : Real.sqrt (1-inverseDimension n) ≠ 0 := (Real.sqrt_pos.mpr (by linarith [hb.2])).ne'
  unfold modelShape inverseModel
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    outer_idempotent v hv, projector_idempotent v hv, outer_mul_projector v hv,
    projector_mul_outer v hv, smul_zero, zero_add, add_zero, inv_mul_cancel₀ hs, mul_inv_cancel₀ hs]
  norm_num
  unfold projector
  abel

theorem modelShape_eq_inverse (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) : modelShape v = (inverseModel v)⁻¹ :=
  (Matrix.inv_eq_left_inv (modelShape_mul_inverseModel hn v hv)).symm

theorem modelShape_posDef (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) : (modelShape v).PosDef := by
  rw [modelShape_eq_inverse hn v hv]
  exact (inverseModel_posDef hn v).inv

theorem modelShape_det (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) : (modelShape v).det = sharpRatio n := by
  have he := congrArg Matrix.det (modelShape_mul_inverseModel hn v hv)
  simp only [Matrix.det_mul, Matrix.det_one] at he
  have hs := sharpRatio_inverseModel hn v hv
  exact mul_right_cancel₀ (inverseModel_posDef hn v).det_pos.ne' (he.trans hs.symm)

theorem modelShape_action (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (modelShape v) u =
      ((1/2 : ℝ)*⟪v, u⟫) • v+(Real.sqrt (1-inverseDimension n))⁻¹ • transverse v u := by
  rw [modelShape, matrix_action_add, matrix_action_smul, matrix_action_smul,
    Khachiyan.outer_action, projector_action, smul_smul]

theorem modelShape_axis (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (modelShape v) v = (1/2 : ℝ) • v := by
  rw [modelShape_action hn v v hv, real_inner_self_eq_norm_sq, hv, one_pow, mul_one,
    transverse_axis_zero v hv, smul_zero, add_zero]

end SharpCut.Sharpness
