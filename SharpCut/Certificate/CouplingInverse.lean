import SharpCut.Certificate.CouplingCauchy

/-! # Ordered inverse identities for the optimal direct-coupling test -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

def couplingZ (F : JohnFrame n N) (v : V n) : MatR n :=
  transversePerturbation F v*(couplingK F v)⁻¹

def transverseDeformation (F : JohnFrame n N) (v : V n) : ℝ :=
  ((transversePerturbation F v)^2*(couplingK F v)⁻¹).trace

theorem perturbation_commute_K (F : JohnFrame n N) (v : V n) :
    transversePerturbation F v*couplingK F v = couplingK F v*transversePerturbation F v := by
  simp only [couplingK, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem perturbation_commute_K_inv (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    transversePerturbation F v*(couplingK F v)⁻¹ =
      (couplingK F v)⁻¹*transversePerturbation F v := by
  have hu : IsUnit (couplingK F v).det := isUnit_iff_ne_zero.mpr (couplingK_posDef F hn v hv).det_pos.ne'
  calc
    _ = (couplingK F v)⁻¹*(couplingK F v*(transversePerturbation F v*(couplingK F v)⁻¹)) := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = (couplingK F v)⁻¹*((couplingK F v*transversePerturbation F v)*(couplingK F v)⁻¹) := by
      simp only [Matrix.mul_assoc]
    _ = (couplingK F v)⁻¹*((transversePerturbation F v*couplingK F v)*(couplingK F v)⁻¹) := by
      rw [perturbation_commute_K]
    _ = _ := by rw [Matrix.mul_assoc (transversePerturbation F v), Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem couplingZ_isHermitian (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (couplingZ F v).IsHermitian := by
  apply ((transversePerturbation_isHermitian F v).commute_iff (couplingK_posDef F hn v hv).inv.isHermitian).mp
  exact perturbation_commute_K_inv F hn v hv

theorem couplingZ_axis (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (couplingZ F v) v = 0 := by
  rw [couplingZ, matrix_action_mul, couplingK_inv_axis F hn v hv, transversePerturbation_axis F hn v hv]

theorem couplingZ_twice (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (2 : ℝ) • couplingZ F v = 1-(couplingK F v)⁻¹ := by
  have hu : IsUnit (couplingK F v).det := isUnit_iff_ne_zero.mpr (couplingK_posDef F hn v hv).det_pos.ne'
  have h := Matrix.mul_nonsing_inv (couplingK F v) hu
  rw [couplingK, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at h
  change (couplingK F v)⁻¹+(2 : ℝ) • couplingZ F v = 1 at h
  calc
    _ = ((couplingK F v)⁻¹+(2 : ℝ) • couplingZ F v)-(couplingK F v)⁻¹ := by abel
    _ = _ := by rw [h]

theorem couplingZ_mul_perturbation (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    couplingZ F v*transversePerturbation F v =
      (transversePerturbation F v)^2*(couplingK F v)⁻¹ := by
  rw [couplingZ, Matrix.mul_assoc, ← perturbation_commute_K_inv F hn v hv, ← Matrix.mul_assoc, pow_two]

theorem couplingZ_square_K (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (couplingZ F v)^2*couplingK F v = (transversePerturbation F v)^2*(couplingK F v)⁻¹ := by
  have hu : IsUnit (couplingK F v).det := isUnit_iff_ne_zero.mpr (couplingK_posDef F hn v hv).det_pos.ne'
  calc
    _ = couplingZ F v*transversePerturbation F v := by
      rw [pow_two, Matrix.mul_assoc]
      change couplingZ F v*(transversePerturbation F v*(couplingK F v)⁻¹*couplingK F v) = _
      rw [Matrix.nonsing_inv_mul_cancel_right _ _ hu]
    _ = _ := couplingZ_mul_perturbation F hn v hv

theorem couplingZ_outer_axis (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    couplingZ F v*outer v = 0 := by
  change couplingZ F v*cross v v = 0
  rw [mul_cross, couplingZ_axis F hn v hv]
  ext i j
  simp only [cross, Matrix.vecMulVec_apply, WithLp.ofLp_zero, Pi.zero_apply, zero_mul, Matrix.zero_apply]

theorem couplingZ_square_transverse (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (couplingZ F v)^2*(projector v+(2 : ℝ) • transversePerturbation F v) =
      (transversePerturbation F v)^2*(couplingK F v)⁻¹ := by
  have he : projector v+(2 : ℝ) • transversePerturbation F v = couplingK F v-outer v := by
    unfold projector couplingK; abel
  have h0 : (couplingZ F v)^2*outer v = 0 := by
    rw [pow_two, Matrix.mul_assoc, couplingZ_outer_axis F hn v hv, Matrix.mul_zero]
  rw [he, Matrix.mul_sub, couplingZ_square_K F hn v hv, h0, sub_zero]

theorem couplingZ_trace_identities (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (couplingZ F v*transversePerturbation F v).trace = transverseDeformation F v ∧
      ((couplingZ F v)^2*(projector v+(2 : ℝ) • transversePerturbation F v)).trace =
        transverseDeformation F v := by
  constructor
  · rw [couplingZ_mul_perturbation F hn v hv]; rfl
  · rw [couplingZ_square_transverse F hn v hv]; rfl

end SharpCut.Certificate
