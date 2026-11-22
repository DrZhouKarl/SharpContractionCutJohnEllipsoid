import SharpCut.Certificate.TransverseBlocks
import SharpCut.Geometry.AxialCoordinates

/-! # Bilinear blocks of the actual positive normalized certificate -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

theorem matrix_action_mul (A B : MatR n) (x : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (A*B) x =
      Matrix.toEuclideanCLM (𝕜 := ℝ) A (Matrix.toEuclideanCLM (𝕜 := ℝ) B x) := by
  rw [map_mul, ContinuousLinearMap.mul_apply]

theorem matrix_action_add (A B : MatR n) (x : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (A+B) x =
      Matrix.toEuclideanCLM (𝕜 := ℝ) A x+Matrix.toEuclideanCLM (𝕜 := ℝ) B x := by
  rw [map_add, ContinuousLinearMap.add_apply]

theorem matrix_action_sub (A B : MatR n) (x : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (A-B) x =
      Matrix.toEuclideanCLM (𝕜 := ℝ) A x-Matrix.toEuclideanCLM (𝕜 := ℝ) B x := by
  rw [map_sub, ContinuousLinearMap.sub_apply]

theorem matrix_action_smul (r : ℝ) (A : MatR n) (x : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (r • A) x = r • Matrix.toEuclideanCLM (𝕜 := ℝ) A x := by
  rw [map_smul, ContinuousLinearMap.smul_apply]

theorem certificateF_bilinear (F : JohnFrame n N) (v x y : V n) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (certificateF F v) y⟫ =
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedShape F (contactScalarFactor F v)) y⟫+
        (cutWeight n/(1-boostParameter n))*⟪x, v⟫*⟪v, y⟫ := by
  rw [certificateF, matrix_action_add, matrix_action_smul, inner_add_right,
    real_inner_smul_right, Khachiyan.outer_action, real_inner_smul_right]
  ring

theorem normalizedCertificate_bilinear (F : JohnFrame n N) (hn : 2 ≤ n)
    (v x y : V n) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizedCertificate F v) y⟫ =
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (modelNormalizer v) x,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (certificateF F v)
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (modelNormalizer v) y)⟫ := by
  rw [normalizedCertificate, matrix_action_mul, matrix_action_mul,
    Khachiyan.inner_matrix_action_symm (modelNormalizer_posDef hn v).isHermitian.isSymm]

theorem projector_transverse_identity (v x : V n) (hx : ⟪x, v⟫ = 0) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (projector v) x = x := by
  rw [projector_action]
  simp only [transverse, hx, zero_smul, sub_zero]

theorem projector_sandwich_bilinear (A : MatR n) (v x y : V n)
    (hx : ⟪x, v⟫ = 0) (hy : ⟪y, v⟫ = 0) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (projector v*A*projector v) y⟫ =
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A y⟫ := by
  have hP : (projector v).IsSymm :=
    (Matrix.isHermitian_one.sub (Khachiyan.outer_posSemidef v).isHermitian).isSymm
  rw [matrix_action_mul, matrix_action_mul, Khachiyan.inner_matrix_action_symm hP,
    projector_transverse_identity v x hx, projector_transverse_identity v y hy]

theorem transversePerturbation_bilinear (F : JohnFrame n N) (hn : 2 ≤ n)
    (v x y : V n) (hv : ‖v‖ = 1) (hx : ⟪x, v⟫ = 0) (hy : ⟪y, v⟫ = 0) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v) y⟫ =
      (modelTransverseScale n)^2*
        ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedShape F (contactScalarFactor F v)) y⟫-⟪x, y⟫ := by
  rw [transversePerturbation_shape F hn v hv, matrix_action_sub, matrix_action_smul,
    inner_sub_right, real_inner_smul_right, projector_sandwich_bilinear _ v x y hx hy,
    projector_transverse_identity v y hy]

theorem normalized_transverse_bilinear (F : JohnFrame n N) (hn : 2 ≤ n)
    (v x y : V n) (hv : ‖v‖ = 1) (hx : ⟪x, v⟫ = 0) (hy : ⟪y, v⟫ = 0) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizedCertificate F v) y⟫ =
      ⟪x, y⟫+⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v) y⟫ := by
  have hx' : ⟪v, x⟫ = 0 := by rwa [real_inner_comm]
  have hy' : ⟪v, y⟫ = 0 := by rwa [real_inner_comm]
  rw [normalizedCertificate_bilinear F hn,
    modelNormalizer_transverse hn v x hv hx', modelNormalizer_transverse hn v y hv hy',
    real_inner_smul_left, map_smul, real_inner_smul_right, certificateF_bilinear]
  rw [hx, mul_zero, zero_mul, add_zero, transversePerturbation_bilinear F hn v x y hv hx hy]
  ring

theorem transverseCoupling_orthogonal (F : JohnFrame n N) (v : V n) (hv : ‖v‖ = 1) :
    ⟪v, transverseCoupling F v⟫ = 0 := by
  rw [transverseCoupling, real_inner_smul_right, projector_action,
    axis_transverse_inner v _ hv, mul_zero]

theorem normalized_mixed_bilinear (F : JohnFrame n N) (hn : 2 ≤ n)
    (v x : V n) (hv : ‖v‖ = 1) (hx : ⟪x, v⟫ = 0) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizedCertificate F v) v⟫ =
      ⟪x, transverseCoupling F v⟫ := by
  have hx' : ⟪v, x⟫ = 0 := by rwa [real_inner_comm]
  rw [normalizedCertificate_bilinear F hn,
    modelNormalizer_transverse hn v x hv hx', modelNormalizer_axis hn v hv,
    real_inner_smul_left, map_smul, real_inner_smul_right, certificateF_bilinear]
  rw [hx, mul_zero, zero_mul, add_zero]
  rw [transverseCoupling, real_inner_smul_right, projector_action]
  simp only [transverse, inner_sub_right, real_inner_smul_right, hx, mul_zero, sub_zero]
  ring

theorem normalized_axial_scalar_identity (b chi : ℝ) (hb : 0 < b) (hb2 : b ≤ 1/2) :
    (2*(1-b)/(2-b)^2)*(Determinant.modelAxial b-Determinant.axialDrop b*chi+
      Determinant.axialKappa b) = 1-chi/(2*(2+b)) := by
  have hd : 2-b ≠ 0 := by linarith
  have h1 : 1-b ≠ 0 := by linarith
  have h2 : 2+b ≠ 0 := by linarith
  have hs := Determinant.model_axial_plus_kappa b hb2
  have hre : Determinant.modelAxial b-Determinant.axialDrop b*chi+Determinant.axialKappa b =
      (Determinant.modelAxial b+Determinant.axialKappa b)-Determinant.axialDrop b*chi := by ring
  rw [hre, hs]
  unfold Determinant.axialDrop
  field_simp [hd, h1, h2] <;> ring

theorem normalized_axial_bilinear (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizedCertificate F v) v⟫ = 1-axialDeficit F v := by
  have hb := inverseDimension_bounds hn
  rw [normalizedCertificate_bilinear F hn, modelNormalizer_axis hn v hv,
    real_inner_smul_left, map_smul, real_inner_smul_right, certificateF_bilinear,
    real_inner_self_eq_norm_sq, hv, one_pow, mul_one, mul_one,
    contactShape_axial, axial_defect_identity F hn v hv]
  rw [← mul_assoc, ← pow_two, modelAxialScale_sq hn]
  exact normalized_axial_scalar_identity (inverseDimension n) (frameDefect F v) hb.1 hb.2

theorem transversePerturbation_axis (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v) v = 0 := by
  rw [transversePerturbation_shape F hn v hv]
  simp only [matrix_action_sub, matrix_action_smul, matrix_action_mul,
    projector_action v v, transverse_axis_zero v hv, map_zero, smul_zero, sub_zero]

end SharpCut.Certificate
