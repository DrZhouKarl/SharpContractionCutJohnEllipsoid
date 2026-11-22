import SharpCut.Certificate.DirectCoupling

/-! # Exact two-by-two matrix identities for the three-dimensional branch -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
open Certificate

theorem det_one_add_scale_two (E : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    (1+t • E).det = 1+t*E.trace+t^2*E.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.trace,
    Matrix.diag_apply, Fin.sum_univ_two, smul_eq_mul]
  norm_num
  ring

theorem adjugate_two (E : Matrix (Fin 2) (Fin 2) ℝ) :
    E.adjugate = E.trace • (1 : Matrix (Fin 2) (Fin 2) ℝ)-E := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem adjugate_one_add_scale_two (E : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    (1+t • E).adjugate = (1+t*E.trace) • (1 : Matrix (Fin 2) (Fin 2) ℝ)-t • E := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem det_le_trace_sq_two (E : Matrix (Fin 2) (Fin 2) ℝ) (hE : E.IsHermitian) :
    E.det ≤ E.trace^2/4 := by
  have hs := hE.isSymm.apply 1 0
  rw [Matrix.det_fin_two]
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  rw [← hs]
  nlinarith [sq_nonneg (E 0 0-E 1 1), sq_nonneg (E 0 1)]

theorem inverse_trace_identity_two (E : Matrix (Fin 2) (Fin 2) ℝ)
    (hD : 1+2*E.trace+4*E.det ≠ 0) :
    E.trace-2*(E^2*(1+(2 : ℝ) • E)⁻¹).trace =
      (E.trace+4*E.det)/(1+2*E.trace+4*E.det) := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, det_one_add_scale_two E 2]
  norm_num only at *
  rw [Matrix.adjugate_fin_two, pow_two]
  simp only [Matrix.mul_smul, Matrix.trace_smul]
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.det_fin_two, smul_eq_mul] at hD ⊢
  simp at hD ⊢
  ring_nf at hD ⊢
  have hcancel := mul_inv_cancel₀ hD
  linear_combination -(E 0 0+E 1 1)*hcancel

theorem square_identity_two (E : Matrix (Fin 2) (Fin 2) ℝ) :
    E^2 = E.trace • E-E.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem det_scalar_sub_two (E : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    (t • (1 : Matrix (Fin 2) (Fin 2) ℝ)-E).det = t^2-t*E.trace+E.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.trace,
    Matrix.diag_apply, Fin.sum_univ_two, smul_eq_mul]
  norm_num
  ring

theorem adjugate_scalar_sub_two (E : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    (t • (1 : Matrix (Fin 2) (Fin 2) ℝ)-E).adjugate =
      (t-E.trace) • (1 : Matrix (Fin 2) (Fin 2) ℝ)+E := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem action_norm_square_two (E : Matrix (Fin 2) (Fin 2) ℝ) (hE : E.IsHermitian) (j : V 2) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) E j‖^2 =
      E.trace*⟪j, Matrix.toEuclideanCLM (𝕜 := ℝ) E j⟫-E.det*‖j‖^2 := by
  have h : ⟪j, Matrix.toEuclideanCLM (𝕜 := ℝ) (E^2) j⟫ =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) E j‖^2 := by
    rw [pow_two, matrix_action_mul, Khachiyan.inner_matrix_action_symm hE.isSymm,
      real_inner_self_eq_norm_sq]
  rw [square_identity_two, matrix_action_sub, matrix_action_smul, matrix_action_smul,
    inner_sub_right, real_inner_smul_right, real_inner_smul_right, map_one,
    ContinuousLinearMap.one_apply, real_inner_self_eq_norm_sq] at h
  exact h.symm

theorem adjugate_norm_square_two (E : Matrix (Fin 2) (Fin 2) ℝ) (hE : E.IsHermitian) (j : V 2) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) ((1+(2 : ℝ) • E).adjugate) j‖^2 =
      ((1+2*E.trace)^2-4*E.det)*‖j‖^2-
        4*(1+E.trace)*⟪j, Matrix.toEuclideanCLM (𝕜 := ℝ) E j⟫ := by
  rw [adjugate_one_add_scale_two E 2, matrix_action_sub, matrix_action_smul, matrix_action_smul,
    map_one, ContinuousLinearMap.one_apply, norm_sub_sq_real, real_inner_smul_left,
    real_inner_smul_right, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs, action_norm_square_two E hE j]
  ring

theorem inverse_norm_det {n : ℕ} (K : MatR n) (hK : K.PosDef) (j : V n) :
    K.det^2*‖Matrix.toEuclideanCLM (𝕜 := ℝ) K⁻¹ j‖^2 =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) K.adjugate j‖^2 := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, matrix_action_smul, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  have he : K.det^2*(K.det⁻¹)^2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hK.det_pos.ne', one_pow]
  rw [← mul_assoc, he, one_mul]

theorem adjugate_pairing_scalar_sub_two (E : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (j : V 2) :
    ⟪j, Matrix.toEuclideanCLM (𝕜 := ℝ) ((t • (1 : Matrix (Fin 2) (Fin 2) ℝ)-E).adjugate) j⟫ =
      (t-E.trace)*‖j‖^2+⟪j, Matrix.toEuclideanCLM (𝕜 := ℝ) E j⟫ := by
  rw [adjugate_scalar_sub_two, matrix_action_add, matrix_action_smul, inner_add_right,
    real_inner_smul_right, map_one, ContinuousLinearMap.one_apply, real_inner_self_eq_norm_sq]

theorem gram_adjugate_bound_two (N : MatR 2) (hN : N.PosDef) (j : V 2) (x : ℝ)
    (hx : 0 ≤ x) (hg : ∀ w : V 2, ⟪j, w⟫^2 ≤ x*⟪w, Matrix.toEuclideanCLM (𝕜 := ℝ) N w⟫) :
    ⟪j, Matrix.toEuclideanCLM (𝕜 := ℝ) N.adjugate j⟫ ≤ x*N.det := by
  let w := Matrix.toEuclideanCLM (𝕜 := ℝ) N⁻¹ j
  let s := ⟪j, w⟫
  have hs : 0 ≤ s := by
    simpa only [s, w, Khachiyan.inner_matrix_action, star_trivial] using
      hN.inv.posSemidef.dotProduct_mulVec_nonneg j.ofLp
  have hw : Matrix.toEuclideanCLM (𝕜 := ℝ) N w = j := posDef_action_inverse N hN j
  have hc : ⟪w, j⟫ = s := real_inner_comm _ _
  have hb := hg w
  rw [hw, hc] at hb
  change s^2 ≤ x*s at hb
  have hsx : s ≤ x := by
    by_cases h0 : s = 0
    · simpa only [h0] using hx
    · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm h0)
      nlinarith only [hb, hsp]
  have he : s = N.det⁻¹*⟪j, Matrix.toEuclideanCLM (𝕜 := ℝ) N.adjugate j⟫ := by
    dsimp [s, w]
    rw [Matrix.inv_def, Ring.inverse_eq_inv, matrix_action_smul, real_inner_smul_right]
  have hm := mul_le_mul_of_nonneg_left hsx hN.det_pos.le
  rw [he, ← mul_assoc, mul_inv_cancel₀ hN.det_pos.ne', one_mul] at hm
  simpa only [mul_comm] using hm

end SharpCut.Determinant
