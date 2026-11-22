import SharpCut.Stability.ModelSpectralBounds

/-! # Actual left polar factor bounds under a small certificate perturbation -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Stability
open Certificate
variable {n : ℕ}

/-- The left polar factor acts with exactly the singular norm of Q transpose. -/
theorem polar_action_norm (Q : MatR n) (hQ : 0 < Q.det) (u : V n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (polarMatrix Q) u‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Qᵀ u‖ := by
  have hM := polarMatrix_posDef hQ
  have hsq : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Qᵀ u‖^2 =
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (Q*Qᵀ) u⟫ := by
    rw [← real_inner_self_eq_norm_sq, Khachiyan.inner_eq_dotProduct,
      Khachiyan.matrix_action_ofLp, Khachiyan.inner_matrix_action]
    rw [← Matrix.dotProduct_transpose_mulVec Qᵀ u.ofLp (Qᵀ*ᵥu.ofLp), Matrix.transpose_transpose,
      Matrix.mulVec_mulVec]
  rw [← polarMatrix_square hQ, ← symmetric_square_action _ hM.isHermitian.isSymm] at hsq
  nlinarith only [hsq, norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) (polarMatrix Q) u),
    norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) Qᵀ u)]

/-- The two vector inequalities in (9.14), before the deficit threshold is applied. -/
theorem perturbed_model_action_bounds (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (Q : MatR n) (u : V n) :
    (Real.sqrt (1/2 : ℝ)-operatorNorm (Q-inverseModel v))*‖u‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Qᵀ u‖ ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Qᵀ u‖ ≤ (2+operatorNorm (Q-inverseModel v))*‖u‖ := by
  have hmodel := model_action_bounds hn v hv u
  have hsym := (Sharpness.inverseModel_posDef hn v).isHermitian.isSymm
  have hQt : Qᵀ = (Q-inverseModel v)ᵀ+inverseModel v := by rw [Matrix.transpose_sub, hsym.eq]; abel
  have haction : Matrix.toEuclideanCLM (𝕜 := ℝ) Qᵀ u =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (Q-inverseModel v)ᵀ u+Matrix.toEuclideanCLM (𝕜 := ℝ) (inverseModel v) u := by
    rw [hQt, matrix_action_add]
  have herr := ContinuousLinearMap.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℝ) (Q-inverseModel v)ᵀ) u
  change _ ≤ operatorNorm (Q-inverseModel v)ᵀ*‖u‖ at herr
  rw [operatorNorm_transpose] at herr
  have hupper := norm_add_le (Matrix.toEuclideanCLM (𝕜 := ℝ) (Q-inverseModel v)ᵀ u)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (inverseModel v) u)
  rw [← haction] at hupper
  have hlower : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (inverseModel v) u‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Qᵀ u‖+‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Q-inverseModel v)ᵀ u‖ := by
    calc
      _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Qᵀ u-Matrix.toEuclideanCLM (𝕜 := ℝ) (Q-inverseModel v)ᵀ u‖ := by rw [haction]; congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  constructor <;> nlinarith only [hmodel.1, hmodel.2, herr, hupper, hlower]

/-- Actual polar eigenvalues at the exact sufficient perturbation size. -/
theorem polar_eigenvalue_bounds (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (Q : MatR n) (hQ : 0 < Q.det)
    (hsmall : operatorNorm (Q-inverseModel v) ≤ 1/250) (i : Fin n) :
    (7/10 : ℝ) < (polarMatrix_posDef hQ).isHermitian.eigenvalues i ∧
      (polarMatrix_posDef hQ).isHermitian.eigenvalues i < 201/100 := by
  have hM := polarMatrix_posDef hQ
  let u := hM.isHermitian.eigenvectorBasis i
  have hu : ‖u‖ = 1 := hM.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i
  have ha := perturbed_model_action_bounds hn v hv Q u
  rw [← polar_action_norm Q hQ u, Gap.eigenvector_action _ hM.isHermitian i, norm_smul,
    Real.norm_eq_abs, abs_of_pos (hM.eigenvalues_pos i), hu, mul_one] at ha
  constructor
  · linarith only [ha.1, hsmall, model_half_root_bounds.2.2]
  · linarith only [ha.2, hsmall]

theorem polar_quadratic_lower (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (Q : MatR n) (hQ : 0 < Q.det)
    (hsmall : operatorNorm (Q-inverseModel v) ≤ 1/250) (u : V n) :
    (7/10 : ℝ)*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (polarMatrix Q) u⟫ :=
  hermitian_quadratic_lower _ (polarMatrix_posDef hQ).isHermitian _
    (fun i => (polar_eigenvalue_bounds hn v hv Q hQ hsmall i).1.le) u

theorem perturbed_model_operator_upper (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (Q : MatR n) :
    operatorNorm Q ≤ 2+operatorNorm (Q-inverseModel v) := by
  rw [← operatorNorm_transpose Q]
  apply ContinuousLinearMap.opNorm_le_bound _ (by have h := norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) (Q-inverseModel v)); change 0 ≤ operatorNorm (Q-inverseModel v) at h; linarith only [h])
  intro u
  exact (perturbed_model_action_bounds hn v hv Q u).2

/-- The exact squared norm/quadratic identity in (9.14). -/
theorem polar_gram_quadratic (Q : MatR n) (hQ : 0 < Q.det) (u : V n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Qᵀ u‖^2 = ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) ((polarMatrix Q)^2) u⟫ := by
  rw [← polar_action_norm Q hQ u, symmetric_square_action _ (polarMatrix_posDef hQ).isHermitian.isSymm, pow_two]

end SharpCut.Stability
