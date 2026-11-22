import SharpCut.Certificate.CouplingInverse

/-! # The complete direct coupling bound, Lemma 8.6 -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

theorem deformation_lower (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    0 ≤ transverseDeformation F v := by
  have hE := transversePerturbation_isHermitian F v
  have hp := (couplingK_posDef F hn v hv).inv.posSemidef.mul_mul_conjTranspose_same
    (transversePerturbation F v)
  rw [hE.eq] at hp
  change (couplingZ F v*transversePerturbation F v).PosSemidef at hp
  rw [couplingZ_mul_perturbation F hn v hv] at hp
  unfold transverseDeformation
  exact Finset.sum_nonneg (fun i hi => hp.diag_nonneg)

theorem deformation_upper (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    transverseDeformation F v ≤ transverseSigma F v/2 := by
  have h := coupling_test_variational F hn v hv (couplingZ F v) (couplingZ_isHermitian F hn v hv) 0
  simp only [couplingLinearTest, couplingQuadraticTest, inner_zero_left, norm_zero,
    zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at h
  rw [(couplingZ_trace_identities F hn v hv).1, (couplingZ_trace_identities F hn v hv).2] at h
  linarith only [h]

theorem selected_test_bound (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (q : V n) :
    transverseDeformation F v+
      2*⟪q, Matrix.toEuclideanCLM (𝕜 := ℝ) (couplingK F v)⁻¹ (transverseCoupling F v)⟫-
        couplingL F v*‖q‖^2 ≤ transverseSigma F v/2 := by
  have h := coupling_test_variational F hn v hv (couplingZ F v) (couplingZ_isHermitian F hn v hv) q
  simp only [couplingLinearTest, couplingQuadraticTest] at h
  rw [(couplingZ_trace_identities F hn v hv).1, (couplingZ_trace_identities F hn v hv).2] at h
  have he := congrArg (fun A : MatR n => ⟪q, Matrix.toEuclideanCLM (𝕜 := ℝ) A (transverseCoupling F v)⟫)
    (couplingZ_twice F hn v hv)
  simp only [matrix_action_smul, real_inner_smul_right, matrix_action_sub,
    inner_sub_right, map_one, ContinuousLinearMap.one_apply] at he
  linarith only [h, he]

theorem coupling_quadratic_full (F : JohnFrame n N) (v : V n) (Z : MatR n)
    (hZ : Z.IsHermitian) (hZv : Matrix.toEuclideanCLM (𝕜 := ℝ) Z v = 0) (q : V n) :
    couplingQuadraticTest F v Z q = (Z^2*couplingK F v).trace+
      4*⟪q, Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverseCoupling F v)⟫+couplingL F v*‖q‖^2 := by
  have he : projector v+(2 : ℝ) • transversePerturbation F v = couplingK F v-outer v := by
    unfold projector couplingK; abel
  unfold couplingQuadraticTest
  rw [he, Matrix.mul_sub, Matrix.trace_sub, trace_action_square_outer Z hZ,
    hZv, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]

theorem coupling_test_variational_full (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (Z : MatR n) (hZ : Z.IsHermitian) (hZv : Matrix.toEuclideanCLM (𝕜 := ℝ) Z v = 0) (q : V n) :
    2*((Z*transversePerturbation F v).trace+⟪q, transverseCoupling F v⟫)-
      ((Z^2*couplingK F v).trace+4*⟪q, Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverseCoupling F v)⟫+
        couplingL F v*‖q‖^2) ≤ transverseSigma F v/2 := by
  have h := coupling_test_variational F hn v hv Z hZ q
  rwa [couplingLinearTest, coupling_quadratic_full F v Z hZ hZv q] at h

theorem coupling_zero_of_L_zero (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hL : couplingL F v = 0) : transverseCoupling F v = 0 := by
  have h := coupling_test_cauchy F hn v hv 0 Matrix.isHermitian_zero (transverseCoupling F v)
  simp only [couplingLinearTest, couplingQuadraticTest, Matrix.zero_mul, Matrix.trace_zero,
    zero_add, real_inner_self_eq_norm_sq, zero_pow (by decide : 2 ≠ 0), map_zero,
    ContinuousLinearMap.zero_apply, inner_zero_right, mul_zero, add_zero, hL, zero_mul] at h
  have he : (‖transverseCoupling F v‖^2)^2 = 0 := le_antisymm h (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (sq_eq_zero_iff.mp he))

/-- Lemma 8.6, including L=0 and sigma=0 without additional endpoint hypotheses. -/
theorem direct_coupling_bound (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    transverseDeformation F v ≤ transverseSigma F v/2 ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (couplingK F v)⁻¹ (transverseCoupling F v)‖^2 ≤
        couplingL F v*(transverseSigma F v/2-transverseDeformation F v) := by
  refine ⟨deformation_upper F hn v hv, ?_⟩
  have hL := couplingL_nonneg F hn v hv
  by_cases h0 : couplingL F v = 0
  · rw [coupling_zero_of_L_zero F hn v hv h0, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), h0, zero_mul]
  · have hLp : 0 < couplingL F v := lt_of_le_of_ne hL (Ne.symm h0)
    let w := Matrix.toEuclideanCLM (𝕜 := ℝ) (couplingK F v)⁻¹ (transverseCoupling F v)
    have h := selected_test_bound F hn v hv ((1/couplingL F v) • w)
    change transverseDeformation F v+2*⟪(1/couplingL F v) • w, w⟫-
      couplingL F v*‖(1/couplingL F v) • w‖^2 ≤ transverseSigma F v/2 at h
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs] at h
    have he : 2*((1/couplingL F v)*‖w‖^2)-couplingL F v*(1/couplingL F v)^2*‖w‖^2 =
      ‖w‖^2/couplingL F v := by field_simp [h0]; ring
    have hb : transverseDeformation F v+‖w‖^2/couplingL F v ≤ transverseSigma F v/2 := by
      linarith only [h, he]
    have hm := (div_le_iff₀ hLp).mp (show ‖w‖^2/couplingL F v ≤
      transverseSigma F v/2-transverseDeformation F v by linarith only [hb])
    simpa only [mul_comm] using hm

end SharpCut.Certificate
