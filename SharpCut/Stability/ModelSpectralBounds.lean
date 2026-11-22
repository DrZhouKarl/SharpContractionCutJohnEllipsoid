import SharpCut.Stability.SpectralTransfers

/-! # Exact model singular and quadratic bounds in every dimension n >= 2 -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Stability
open Certificate
variable {n : ℕ}

theorem sqrt_half_eq_inv_sqrt_two : Real.sqrt (1/2 : ℝ) = (Real.sqrt 2)⁻¹ := by
  rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.sqrt_inv]

theorem axial_scaling_quadratic (v : V n) (u : V n) (a k : ℝ) :
    ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (a • outer v+k • projector v) u⟫ =
      a*⟪u,v⟫^2+k*(‖u‖^2-⟪u,v⟫^2) := by
  rw [matrix_action_add, matrix_action_smul, matrix_action_smul, inner_add_right,
    real_inner_smul_right, real_inner_smul_right, Khachiyan.outer_action,
    real_inner_smul_right, projector_quadratic, real_inner_comm u v]
  ring

theorem axial_scaling_quadratic_lower (v : V n) (hv : ‖v‖ = 1) (a k ell : ℝ)
    (ha : ell ≤ a) (hk : ell ≤ k) (u : V n) :
    ell*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (a • outer v+k • projector v) u⟫ := by
  rw [axial_scaling_quadratic]
  have hy := transverse_norm_sq_general v u hv
  have hs := mul_le_mul_of_nonneg_right ha (sq_nonneg ⟪u,v⟫)
  have ht := mul_le_mul_of_nonneg_right hk (sq_nonneg ‖transverse v u‖)
  calc
    _ = ell*⟪u,v⟫^2+ell*‖transverse v u‖^2 := by rw [hy]; ring
    _ ≤ a*⟪u,v⟫^2+k*‖transverse v u‖^2 := add_le_add hs ht
    _ = _ := by rw [hy]

theorem axial_scaling_upper (v : V n) (hv : ‖v‖ = 1) (a k ell : ℝ)
    (ha : a^2 ≤ ell) (hk : k^2 ≤ ell) (u : V n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (a • outer v+k • projector v) u‖^2 ≤ ell*‖u‖^2 := by
  rw [matrix_action_add, matrix_action_smul, matrix_action_smul, Khachiyan.outer_action,
    projector_action, smul_smul, real_inner_comm u v,
    orthogonal_combination_norm_sq v (transverse v u) hv (axis_transverse_inner v u hv)]
  have hs := mul_le_mul_of_nonneg_right ha (sq_nonneg ⟪u,v⟫)
  have ht := mul_le_mul_of_nonneg_right hk (sq_nonneg ‖transverse v u‖)
  have hy := transverse_norm_sq_general v u hv
  calc
    _ = a^2*⟪u,v⟫^2+k^2*‖transverse v u‖^2 := by ring
    _ ≤ ell*⟪u,v⟫^2+ell*‖transverse v u‖^2 := add_le_add hs ht
    _ = _ := by rw [hy]; ring

theorem model_half_root_bounds :
    7/10 < Real.sqrt (1/2 : ℝ) ∧ Real.sqrt (1/2 : ℝ) < 1 ∧
      7/10 < Real.sqrt (1/2 : ℝ)-1/250 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/2)
  have hp := Real.sqrt_nonneg (1/2 : ℝ)
  constructor
  · nlinarith only [hs, hp]
  · constructor <;> nlinarith only [hs, hp]

/-- The actual M0 is uniformly positive, rather than only a diagonal special case. -/
theorem model_quadratic_lower (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (u : V n) :
    Real.sqrt (1/2 : ℝ)*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (inverseModel v) u⟫ := by
  apply axial_scaling_quadratic_lower v hv
  · linarith only [model_half_root_bounds.2.1]
  · exact Real.sqrt_le_sqrt (by linarith [(inverseDimension_bounds hn).2])

/-- Both exact singular bounds used in (9.14), with the reciprocal-root identity above. -/
theorem model_action_bounds (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (u : V n) :
    Real.sqrt (1/2 : ℝ)*‖u‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (inverseModel v) u‖ ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (inverseModel v) u‖ ≤ 2*‖u‖ := by
  refine ⟨quadratic_action_lower _ _ (model_quadratic_lower hn v hv) u, ?_⟩
  have hb := inverseDimension_bounds hn
  have hs := Real.sq_sqrt (by linarith [hb.2] : 0 ≤ 1-inverseDimension n)
  have h := axial_scaling_upper v hv 2 (Real.sqrt (1-inverseDimension n)) 4 (by norm_num)
    (by rw [hs]; linarith only [hb.1]) u
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (inverseModel v) u‖^2 ≤ 4*‖u‖^2 at h
  nlinarith only [h, norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) (inverseModel v) u), norm_nonneg u]

theorem model_operator_upper (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) : operatorNorm (inverseModel v) ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  exact (model_action_bounds hn v hv u).2

theorem model_quadratic_seven_tenths (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (u : V n) :
    (7/10 : ℝ)*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (inverseModel v) u⟫ :=
  (mul_le_mul_of_nonneg_right model_half_root_bounds.1.le (sq_nonneg ‖u‖)).trans (model_quadratic_lower hn v hv u)

/-- The strict lower bound on every actual M0 eigenvalue in (9.15). -/
theorem model_eigenvalue_lower (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (i : Fin n) :
    (7/10 : ℝ) < (Sharpness.inverseModel_posDef hn v).isHermitian.eigenvalues i := by
  have hM := Sharpness.inverseModel_posDef hn v
  let u := hM.isHermitian.eigenvectorBasis i
  have hu : ‖u‖ = 1 := hM.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i
  have h := model_quadratic_lower hn v hv u
  rw [Gap.eigenvector_action _ hM.isHermitian i, real_inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one, mul_one] at h
  linarith only [h, model_half_root_bounds.1]

end SharpCut.Stability
