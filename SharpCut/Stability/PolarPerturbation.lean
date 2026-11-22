import SharpCut.Stability.PolarSpectralBounds

/-! # Ordered perturbation of the positive left polar factor -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Stability
open Certificate
variable {n N : ℕ}

/-- The exact Sylvester equation in (9.16). -/
theorem polar_sylvester_identity (Q : MatR n) (hQ : 0 < Q.det) (M₀ : MatR n) :
    polarMatrix Q*(polarMatrix Q-M₀)+(polarMatrix Q-M₀)*M₀ = Q*Qᵀ-M₀*M₀ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, ← polarMatrix_square hQ]
  abel

/-- The ordered Gram-product difference used in (9.17). -/
theorem gram_difference_identity (Q M₀ : MatR n) :
    Q*Qᵀ-M₀*M₀ = (Q-M₀)*Qᵀ+M₀*(Qᵀ-M₀) := by
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

theorem gram_difference_frobenius (Q M₀ : MatR n) (hM₀ : M₀.IsSymm) :
    frobeniusNorm (Q*Qᵀ-M₀*M₀) ≤ (operatorNorm Q+operatorNorm M₀)*frobeniusNorm (Q-M₀) := by
  rw [gram_difference_identity]
  have h := (frobeniusNorm_add_le ((Q-M₀)*Qᵀ) (M₀*(Qᵀ-M₀))).trans
    (add_le_add (frobeniusNorm_mul_operator_right (Q-M₀) Qᵀ) (frobeniusNorm_mul_operator_left M₀ (Qᵀ-M₀)))
  have ht : Qᵀ-M₀ = (Q-M₀)ᵀ := by rw [Matrix.transpose_sub, hM₀.eq]
  rw [ht, frobeniusNorm_transpose, operatorNorm_transpose] at h
  have heq : frobeniusNorm (Q-M₀)*operatorNorm Q+operatorNorm M₀*frobeniusNorm (Q-M₀) =
      (operatorNorm Q+operatorNorm M₀)*frobeniusNorm (Q-M₀) := by ring
  rw [ht]
  rwa [heq] at h

/-- A Sylvester coercivity factor of 7/5, without a commutation assumption. -/
theorem polar_model_frobenius_bound (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (Q : MatR n) (hQ : 0 < Q.det)
    (hsmall : operatorNorm (Q-inverseModel v) ≤ 1/250) :
    frobeniusNorm (polarMatrix Q-inverseModel v) ≤
      ((operatorNorm Q+operatorNorm (inverseModel v))*frobeniusNorm (Q-inverseModel v))/(7/5 : ℝ) := by
  have hM₀ := (Sharpness.inverseModel_posDef hn v).isHermitian.isSymm
  have hs := sylvester_frobenius_bound (polarMatrix Q) (inverseModel v) (polarMatrix Q-inverseModel v)
    (7/10) (7/10) (by norm_num) hM₀ (polar_quadratic_lower hn v hv Q hQ hsmall) (model_quadratic_seven_tenths hn v hv)
  rw [polar_sylvester_identity Q hQ (inverseModel v)] at hs
  norm_num at hs
  have hg := gram_difference_frobenius Q (inverseModel v) hM₀
  have hdiv := div_le_div_of_nonneg_right hg (by norm_num : (0 : ℝ) ≤ 7/5)
  exact hs.trans hdiv

/-- The numerical square-root threshold is checked in the kernel, including epsilon=0. -/
theorem small_deficit_sqrt (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ 1/1000000) : Real.sqrt ε ≤ 1/1000 := by
  have hs := Real.sq_sqrt hε
  have hn := Real.sqrt_nonneg ε
  nlinarith only [hs, hn, hsmall]

/-- The actual polar perturbation and spectral bounds required for the shape estimate. -/
theorem near_extremal_polar_bounds (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (F : JohnFrame n N) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A)
    (hε : 0 ≤ Gap.volumeDeficit n A) (hsmall : Gap.volumeDeficit n A ≤ 1/1000000) :
    operatorNorm (unrotatedQ F v-inverseModel v) ≤ 1/250 ∧
    (∀ i, (7/10 : ℝ) < (polarMatrix_posDef (unrotatedQ_det_pos F hn v hv)).isHermitian.eigenvalues i ∧
      (polarMatrix_posDef (unrotatedQ_det_pos F hn v hv)).isHermitian.eigenvalues i < 201/100) ∧
    operatorNorm (unrotatedQ F v) < 201/100 ∧
    frobeniusNorm (polarMatrix (unrotatedQ F v)-inverseModel v) ≤ 12*Real.sqrt (Gap.volumeDeficit n A) := by
  have hcontact := near_extremal_contact_stability hn hK hJ F hs v hv hA hε hsmall
  have hroot := small_deficit_sqrt (Gap.volumeDeficit n A) hε hsmall
  have hop := operator_frobenius_bound (unrotatedQ F v-inverseModel v)
  have hδ : operatorNorm (unrotatedQ F v-inverseModel v) ≤ 1/250 := by
    nlinarith only [hop, hcontact.2.1, hroot]
  have hQ := unrotatedQ_det_pos F hn v hv
  have hqupper := perturbed_model_operator_upper hn v hv (unrotatedQ F v)
  have hqstrict : operatorNorm (unrotatedQ F v) < 201/100 := by linarith only [hqupper, hδ]
  have hM₀op := model_operator_upper hn v hv
  have hpert := polar_model_frobenius_bound hn v hv (unrotatedQ F v) hQ hδ
  have hsum : operatorNorm (unrotatedQ F v)+operatorNorm (inverseModel v) ≤ 401/100 := by linarith only [hqstrict, hM₀op]
  have hnum := mul_le_mul_of_nonneg_right hsum (show 0 ≤ frobeniusNorm (unrotatedQ F v-inverseModel v) from Real.sqrt_nonneg _)
  have hnum' := mul_le_mul_of_nonneg_left hcontact.2.1 (by norm_num : (0 : ℝ) ≤ 401/100)
  have hfinal : frobeniusNorm (polarMatrix (unrotatedQ F v)-inverseModel v) ≤ 12*Real.sqrt (Gap.volumeDeficit n A) := by
    have hr := Real.sqrt_nonneg (Gap.volumeDeficit n A)
    have hp := (le_div_iff₀ (by norm_num : (0 : ℝ) < 7/5)).mp hpert
    nlinarith only [hp, hnum, hnum', hr]
  exact ⟨hδ, polar_eigenvalue_bounds hn v hv (unrotatedQ F v) hQ hδ, hqstrict, hfinal⟩

/-- The Frobenius trace identity explicitly displayed in (9.16). -/
theorem polar_sylvester_trace_identity (Q : MatR n) (hQ : 0 < Q.det) (M₀ : MatR n) :
    let X := polarMatrix Q-M₀
    (Xᵀ*polarMatrix Q*X).trace+(Xᵀ*X*M₀).trace = frobeniusPair X (Q*Qᵀ-M₀*M₀) := by
  dsimp only
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← frobeniusPair_trace, ← frobeniusPair_trace,
    ← frobeniusPair_add_right, polar_sylvester_identity Q hQ M₀]

/-- The unrounded 401/35 coefficient in (9.17). -/
theorem near_extremal_polar_coefficient (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (F : JohnFrame n N) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A)
    (hε : 0 ≤ Gap.volumeDeficit n A) (hsmall : Gap.volumeDeficit n A ≤ 1/1000000) :
    frobeniusNorm (polarMatrix (unrotatedQ F v)-inverseModel v) ≤ (401/35 : ℝ)*Real.sqrt (Gap.volumeDeficit n A) := by
  have hcontact := near_extremal_contact_stability hn hK hJ F hs v hv hA hε hsmall
  have hpolar := near_extremal_polar_bounds hn hK hJ F hs v hv hA hε hsmall
  have hQ := unrotatedQ_det_pos F hn v hv
  have hpert := polar_model_frobenius_bound hn v hv (unrotatedQ F v) hQ hpolar.1
  have hsum : operatorNorm (unrotatedQ F v)+operatorNorm (inverseModel v) ≤ 401/100 := by
    linarith only [hpolar.2.2.1, model_operator_upper hn v hv]
  have hnum := mul_le_mul_of_nonneg_right hsum (show 0 ≤ frobeniusNorm (unrotatedQ F v-inverseModel v) from Real.sqrt_nonneg _)
  have hnum' := mul_le_mul_of_nonneg_left hcontact.2.1 (by norm_num : (0 : ℝ) ≤ 401/100)
  have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 7/5)).mp hpert
  nlinarith only [h, hnum, hnum']

end SharpCut.Stability
