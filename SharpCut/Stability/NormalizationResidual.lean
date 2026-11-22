import SharpCut.Stability.ResidualAlgebra
import SharpCut.Certificate.NormalizedBlocks

/-! # Ordered, dimension-independent transfer to the positive normalized matrix -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Stability
open Certificate
variable {n N : ℕ}

theorem transverse_norm_sq_general (v u : V n) (hv : ‖v‖ = 1) :
    ‖transverse v u‖^2 = ‖u‖^2-⟪u,v⟫^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [transverse, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hv, one_pow, mul_one]
  rw [real_inner_comm v u]
  ring

/-- A squared lower singular-value bound, expressed through every Euclidean vector. -/
theorem axial_scaling_lower (v : V n) (hv : ‖v‖ = 1) (a k ell : ℝ)
    (ha : ell ≤ a^2) (hk : ell ≤ k^2) (u : V n) :
    ell*‖u‖^2 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (a • outer v+k • projector v) u‖^2 := by
  rw [matrix_action_add, matrix_action_smul, matrix_action_smul,
    Khachiyan.outer_action, projector_action, smul_smul, real_inner_comm u v,
    orthogonal_combination_norm_sq v (transverse v u) hv (axis_transverse_inner v u hv)]
  have hs := mul_le_mul_of_nonneg_right ha (sq_nonneg ⟪u,v⟫)
  have ht := mul_le_mul_of_nonneg_right hk (sq_nonneg ‖transverse v u‖)
  have hy := transverse_norm_sq_general v u hv
  calc
    _ = ell*⟪u,v⟫^2+ell*‖transverse v u‖^2 := by rw [hy]; ring
    _ ≤ a^2*⟪u,v⟫^2+k^2*‖transverse v u‖^2 := add_le_add hs ht
    _ = _ := by ring

theorem frobenius_left_lower (L X : MatR n) (ell : ℝ)
    (hL : ∀ u : V n, ell*‖u‖^2 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) L u‖^2) :
    ell*(frobeniusNorm X)^2 ≤ (frobeniusNorm (L*X))^2 := by
  rw [frobeniusNorm_sq_columns, frobeniusNorm_sq_columns, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [matrixColumn_mul]
  exact hL (matrixColumn X j)

theorem frobenius_right_lower (R X : MatR n) (ell : ℝ) (hR : R.IsSymm)
    (hL : ∀ u : V n, ell*‖u‖^2 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) R u‖^2) :
    ell*(frobeniusNorm X)^2 ≤ (frobeniusNorm (X*R))^2 := by
  have h := frobenius_left_lower R Xᵀ ell hL
  rw [← hR.eq, ← Matrix.transpose_mul, frobeniusNorm_transpose, frobeniusNorm_transpose] at h
  exact h

theorem modelRoot_lower (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (u : V n) :
    ((2-inverseDimension n)/2)*‖u‖^2 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (modelRoot v) u‖^2 := by
  rw [modelRoot_explicit hn v hv]
  apply axial_scaling_lower v hv
  · rw [Real.sq_sqrt (modelEigenvalues_pos hn).1.le]
    have hb := inverseDimension_bounds hn
    have hpos : 0 < 2*(1-inverseDimension n) := by linarith [hb.2]
    unfold modelAxialEigenvalue
    apply (le_div_iff₀ hpos).mpr
    nlinarith [hb.1, hb.2]
  · rw [Real.sq_sqrt (modelEigenvalues_pos hn).2.le]
    rfl

theorem modelRoot_D_lower (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (u : V n) :
    (2*(1-inverseDimension n)/(2-inverseDimension n))*‖u‖^2 ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (modelRoot v*certificateD v) u‖^2 := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have he := modelEigenvalues_pos hn
  have hk := boostScale_bounds hn
  have hksq : (boostScale n)^2 = 4*(1-inverseDimension n)/(2-inverseDimension n)^2 :=
    hk.2.2.trans (lorentz_parameter_square _ hd.ne')
  have hprod : modelRoot v*certificateD v =
      (Real.sqrt (modelAxialEigenvalue n)*(boostScale n)^2) • outer v+
        (Real.sqrt (modelTransverseEigenvalue n)*boostScale n) • projector v := by
    rw [modelRoot_explicit hn v hv]
    unfold explicitModelRoot certificateD
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      outer_idempotent v hv, projector_idempotent v hv, outer_mul_projector v hv,
      projector_mul_outer v hv, smul_zero, zero_add, add_zero, mul_comm]
    rw [add_comm]
  rw [hprod]
  apply axial_scaling_lower v hv
  · rw [mul_pow, Real.sq_sqrt he.1.le, hksq]
    unfold modelAxialEigenvalue
    have hscalar : (2-inverseDimension n)^2/(2*(1-inverseDimension n))*
        (4*(1-inverseDimension n)/(2-inverseDimension n)^2)^2 =
        8*(1-inverseDimension n)/(2-inverseDimension n)^2 := by field_simp [hd.ne', h1.ne'] <;> ring
    rw [hscalar]
    apply (div_le_div_iff₀ hd (pow_pos hd 2)).mpr
    nlinarith [hb.1, hb.2]
  · rw [mul_pow, Real.sq_sqrt he.2.le, hksq]
    unfold modelTransverseEigenvalue
    apply le_of_eq
    field_simp [hd.ne'] <;> ring

theorem normalized_residual_factorization (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    unrotatedQ F v-inverseModel v =
      modelRoot v*(normalizedCertificate F v-1)*(modelRoot v*certificateD v) := by
  have hu : IsUnit (modelRoot v).det := isUnit_iff_ne_zero.mpr (modelRoot_posDef hn v).det_pos.ne'
  have hi : modelRoot v*modelNormalizer v = 1 := Matrix.mul_nonsing_inv _ hu
  have hi' : modelNormalizer v*modelRoot v = 1 := Matrix.nonsing_inv_mul _ hu
  have hs : modelRoot v*modelRoot v = modelF0 v :=
    CFC.sqrt_mul_sqrt_self _ (modelF0_posDef hn v).posSemidef.nonneg
  rw [ordered_factorization F hn v hv, ← modelF0_mul_D hn v hv]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, normalizedCertificate]
  have hF : modelRoot v*(modelNormalizer v*certificateF F v*modelNormalizer v)*(modelRoot v*certificateD v) =
      certificateF F v*certificateD v := by
    calc
      _ = (modelRoot v*modelNormalizer v)*certificateF F v*(modelNormalizer v*modelRoot v)*certificateD v := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hi, hi', Matrix.one_mul, Matrix.mul_one]
  rw [hF, ← Matrix.mul_assoc, hs]

/-- The second bound of (9.3), without any commutativity assumption on the frame. -/
theorem normalized_residual_bound (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (frobeniusNorm (normalizedCertificate F v-1))^2 ≤ frameDefect F v/(2-inverseDimension n) := by
  have hb := inverseDimension_bounds hn
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have hR : (modelRoot v*certificateD v).IsSymm := by
    have he : modelRoot v*certificateD v =
        (Real.sqrt (modelAxialEigenvalue n)*(boostScale n)^2) • outer v+
          (Real.sqrt (modelTransverseEigenvalue n)*boostScale n) • projector v := by
      rw [modelRoot_explicit hn v hv]
      unfold explicitModelRoot certificateD
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        outer_idempotent v hv, projector_idempotent v hv, outer_mul_projector v hv,
        projector_mul_outer v hv, smul_zero, zero_add, add_zero, mul_comm]
      rw [add_comm]
    rw [he]
    apply Matrix.IsSymm.ext
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply,
      (Khachiyan.outer_posSemidef v).isHermitian.isSymm.apply i j,
      (projector_posSemidef v hv).isHermitian.isSymm.apply i j]
  have hl := frobenius_left_lower (modelRoot v) (normalizedCertificate F v-1) ((2-inverseDimension n)/2)
    (modelRoot_lower hn v hv)
  have hr := frobenius_right_lower (modelRoot v*certificateD v) (modelRoot v*(normalizedCertificate F v-1))
    (2*(1-inverseDimension n)/(2-inverseDimension n)) hR (modelRoot_D_lower hn v hv)
  have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2*(1-inverseDimension n)/(2-inverseDimension n))
  rw [← normalized_residual_factorization F hn v hv] at hr
  have hc := certificate_residual_bound F hn v hv
  have hs : (2*(1-inverseDimension n)/(2-inverseDimension n))*((2-inverseDimension n)/2) =
      1-inverseDimension n := by field_simp [hd.ne']
  rw [← mul_assoc, hs] at hm
  have ht : (1-inverseDimension n)*(frobeniusNorm (normalizedCertificate F v-1))^2 ≤
      (1-inverseDimension n)/(2-inverseDimension n)*frameDefect F v := hm.trans (hr.trans hc)
  apply le_of_mul_le_mul_left (a := 1-inverseDimension n) _ h1
  convert ht using 1 <;> ring

end SharpCut.Stability
