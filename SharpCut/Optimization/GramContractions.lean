import SharpCut.Coupled.InverseTrace.RecordedIdentities

/-! # Actual Euclidean contraction Gram bounds and the skew Gram determinant identity -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Optimization
open Certificate
variable {n : ℕ}

theorem real_conjTranspose (A : MatR n) : Aᴴ = Aᵀ := by ext i j; simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]

theorem transpose_gram_posSemidef (A : MatR n) : (Aᵀ*A).PosSemidef := by
  rw [← real_conjTranspose A]
  exact Matrix.posSemidef_conjTranspose_mul_self A

theorem transpose_gram_quadratic (A : MatR n) (u : V n) :
    ⟪u,Matrix.toEuclideanCLM (𝕜 := ℝ) (Aᵀ*A) u⟫ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A u‖^2 := by
  rw [← real_inner_self_eq_norm_sq, Khachiyan.inner_eq_dotProduct, Khachiyan.inner_matrix_action,
    Khachiyan.matrix_action_ofLp]
  simp only [Khachiyan.matrix_action_ofLp]
  rw [← Matrix.dotProduct_transpose_mulVec A u.ofLp (A*ᵥu.ofLp), Matrix.mulVec_mulVec]

/-- The lower Gram determinant bound in (10.4), for every real matrix T. -/
theorem one_add_gram_det_ge_one (T : MatR n) : 1 ≤ (1+Tᵀ*T).det := by
  have hG := (Matrix.PosDef.one : (1 : MatR n).PosDef).add_posSemidef (transpose_gram_posSemidef T)
  have he (i : Fin n) : 1 ≤ hG.isHermitian.eigenvalues i := by
    let u := hG.isHermitian.eigenvectorBasis i
    have hu : ‖u‖ = 1 := hG.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i
    have hq : ⟪u,Matrix.toEuclideanCLM (𝕜 := ℝ) (1+Tᵀ*T) u⟫ = 1+‖Matrix.toEuclideanCLM (𝕜 := ℝ) T u‖^2 := by
      rw [matrix_action_add, inner_add_right, map_one, ContinuousLinearMap.one_apply,
        real_inner_self_eq_norm_sq, hu, one_pow, transpose_gram_quadratic]
    rw [Gap.eigenvector_action _ hG.isHermitian i, real_inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one] at hq
    nlinarith only [hq, sq_nonneg ‖Matrix.toEuclideanCLM (𝕜 := ℝ) T u‖]
  rw [hG.isHermitian.det_eq_prod_eigenvalues]
  exact Finset.one_le_prod₀ (fun i _ => he i)

/-- The exact skew Gram identity (10.4), preserving transpose and multiplication order. -/
theorem skew_gram_identity (T : MatR n) (hT : Tᵀ = -T) :
    (1+T)ᵀ*(1+T) = 1+Tᵀ*T ∧ (1 ≤ ((1+T).det)^2) := by
  have hgram : (1+T)ᵀ*(1+T) = 1+Tᵀ*T := by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one]
    simp only [Matrix.one_mul, Matrix.mul_one]
    rw [hT]
    abel
  have hdet : ((1+T).det)^2 = (1+Tᵀ*T).det := by
    rw [← hgram, Matrix.det_mul, Matrix.det_transpose, pow_two]
  exact ⟨hgram, hdet.symm ▸ one_add_gram_det_ge_one T⟩

/-- A contraction gives the actual Loewner inequalities and determinant bound in (10.5). -/
theorem contraction_gram_bounds (R : MatR n) (hR : operatorNorm R ≤ 1) :
    (Rᵀ*R).PosSemidef ∧ (1-Rᵀ*R).PosSemidef ∧ 0 ≤ Rᵀ*R ∧ Rᵀ*R ≤ 1 ∧
    (Rᵀ*R).det ≤ 1 ∧ |R.det| ≤ 1 := by
  have hG := transpose_gram_posSemidef R
  have hn (u : V n) : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) R u‖ ≤ ‖u‖ := by
    have h := ContinuousLinearMap.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℝ) R) u
    have hmul := mul_le_mul_of_nonneg_right hR (norm_nonneg u)
    change _ ≤ operatorNorm R*‖u‖ at h
    nlinarith only [h, hmul]
  have hD : (1-Rᵀ*R).PosSemidef := by
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨Matrix.isHermitian_one.sub hG.isHermitian, ?_⟩
    intro x
    let u : V n := WithLp.toLp 2 x
    have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hn u)
    have hq : 0 ≤ ⟪u,Matrix.toEuclideanCLM (𝕜 := ℝ) (1-Rᵀ*R) u⟫ := by
      rw [matrix_action_sub, inner_sub_right, map_one, ContinuousLinearMap.one_apply,
        real_inner_self_eq_norm_sq, transpose_gram_quadratic]
      linarith only [hs]
    simpa only [Khachiyan.inner_matrix_action, u, WithLp.ofLp_toLp, star_trivial] using hq
  have he (i : Fin n) : hG.isHermitian.eigenvalues i ≤ 1 := by
    let u := hG.isHermitian.eigenvectorBasis i
    have hu : ‖u‖ = 1 := hG.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i
    have hq := transpose_gram_quadratic R u
    rw [Gap.eigenvector_action _ hG.isHermitian i, real_inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one] at hq
    have hs := hn u
    rw [hu] at hs
    nlinarith only [hq, hs, norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) R u)]
  have hdet : (Rᵀ*R).det ≤ 1 := by
    rw [hG.isHermitian.det_eq_prod_eigenvalues]
    exact Finset.prod_le_one₀ (fun i _ => hG.eigenvalues_nonneg i) (fun i _ => he i)
  have habs : |R.det| ≤ 1 := by
    rw [Matrix.det_mul, Matrix.det_transpose] at hdet
    nlinarith only [hdet, sq_abs R.det, abs_nonneg R.det]
  exact ⟨hG, hD, hG.nonneg, sub_nonneg.mp hD.nonneg, hdet, habs⟩

end SharpCut.Optimization
