import SharpCut.Paper.EquationBasic
import SharpCut.Stability.Theorem
import SharpCut.Applications.Initialization

/-! # Literal intermediate chains in Sections 4–7

These exports retain displayed intermediates that otherwise appear only as
local steps inside the equivalent proofs of the named paper results.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Paper
open Optimization Certificate Gap Equality
variable {n N : ℕ}

/-- The first expanded equality in (4.2), before balance and normalization. -/
theorem cone_gap_expanded {g q : Fin N → V n} {beta alpha : Fin N → ℝ}
    {c : V n} {A : MatR n} (hA : A.IsHermitian) :
    coneGap g beta alpha q c A =
      (∑ r, alpha r*beta r)-⟪c, ∑ r, alpha r • g r⟫-(A*aggregate g q).trace := by
  have ht : (A*aggregate g q).trace =
      ∑ r, ⟪q r, Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ := by
    simp only [aggregate, Matrix.mul_sum, Matrix.trace_sum,
      trace_mul_symmetricOuter hA.isSymm]
  simp only [coneGap, conePairing, coneHeight, mul_sub, Finset.sum_sub_distrib,
    inner_sum, real_inner_smul_right, ht]
  congr 2
  apply Finset.sum_congr rfl
  intro r hr
  rw [real_inner_comm]

/-- The complete cancellation displayed in (4.4), on the proper positive domain. -/
theorem deficit_cancellation (hn : 1 ≤ n) (A M : MatR n)
    (hA : A.PosDef) (hM : M.PosDef) :
    Real.log (sharpRatio n*M.det)-Real.log M.det-Real.log A.det =
      Real.log (sharpRatio n/A.det) := by
  rw [Real.log_mul (sharpRatio_pos hn).ne' hM.det_pos.ne',
    Real.log_div (sharpRatio_pos hn).ne' hA.det_pos.ne']
  ring

/-- The spectral identity and both inequalities in (4.8). -/
theorem matching_square_chain {g q : Fin N → V n} {beta alpha : Fin N → ℝ}
    {c : V n} {A : MatR n} (hp : PrimalFeasible g beta c A)
    (hd : DualFeasible g beta alpha q)
    (hsmall : dualityGap A (aggregate g q) ≤ 1/4) :
    let Y := matchingMatrix A (aggregate g q)
    let hY := matchingMatrix_posDef A (aggregate g q) hp.1 hd.positive
    (frobeniusNorm (Y-1))^2 = ∑ j, (hY.isHermitian.eigenvalues j-1)^2 ∧
    (frobeniusNorm (Y-1))^2 ≤ 4*(∑ j, scalarDivergence (hY.isHermitian.eigenvalues j)) ∧
    (∑ j, scalarDivergence (hY.isHermitian.eigenvalues j)) = matrixDivergence Y ∧
    matrixDivergence Y ≤ dualityGap A (aggregate g q) := by
  dsimp only
  have hY := matchingMatrix_posDef A (aggregate g q) hp.1 hd.positive
  have he := normalized_pair_gap hp hd
  have hc := coneGap_nonneg hp hd
  have hD : matrixDivergence (matchingMatrix A (aggregate g q)) ≤
      dualityGap A (aggregate g q) := by
    change pairDivergence A (aggregate g q) ≤ _
    linarith only [he, hc]
  have hs := matrixDivergence_spectral _ hY
  refine ⟨frobenius_shift_spectral _ hY.isHermitian, ?_, hs.symm, hD⟩
  rw [← hs]
  exact frobenius_divergence_square _ hY (hD.trans hsmall)

/-- All certificate and shape conclusions in (5.3), including the common rotation. -/
theorem zero_deficit_certificate (hn : 2 ≤ n) {K : Set (V n)}
    (hK : IsConvexBody K) (hJ : IsJohnNormalized K) (F : JohnFrame n N)
    (hs : F.Supports K) (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n}
    (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) (hz : volumeDeficit n A = 0) :
    geometricGap F v = 0 ∧ frameConeGap F v c A = 0 ∧
    pairDivergence A (frameMatrix F v) = 0 ∧ frameDefect F v = 0 ∧
    unrotatedQ F v = inverseModel v ∧ frameMatrix F v = inverseModel v ∧
    polarRotation (unrotatedQ F v) = 1 ∧ A = Sharpness.modelShape v := by
  have hzero := (volumeDeficit_zero_iff hn hK hJ F hs v hv hA).mp hz
  have hp := zero_deficit_parameters hn hK hJ F hs v hv hA hz
  have hQ := sharp_frame_model_matrix F hn v hv hp.1
  have hM := frameMatrix_model F hn v hv hp.1
  have hU : polarRotation (unrotatedQ F v) = 1 := by
    unfold polarRotation
    change (frameMatrix F v)⁻¹*unrotatedQ F v = 1
    rw [hM, hQ]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (Sharpness.inverseModel_posDef hn v).det_pos.ne')
  exact ⟨hzero.1, hzero.2.1, hzero.2.2,
    (geometricGap_zero_iff F hn v hv).mp hzero.1, hQ, hM, hU, hp.2.1⟩

/-- The active model support and isotropic center identities in (5.4)–(5.5). -/
theorem zero_deficit_support_center (hn : 2 ≤ n) {K : Set (V n)}
    (hK : IsConvexBody K) (hJ : IsJohnNormalized K) (F : JohnFrame n N)
    (hs : F.Supports K) (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n}
    (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) (hz : volumeDeficit n A = 0) :
    (∀ i, originalWeight F v i*
      (1-⟪F.contact i,c⟫-‖Matrix.toEuclideanCLM (𝕜 := ℝ)
        (Sharpness.modelShape v) (F.contact i)‖) = 0) ∧
    (∀ i, ⟪F.contact i,c-Sharpness.modelCenter v⟫ = 0) ∧
    ‖c-Sharpness.modelCenter v‖^2 =
      ∑ i, F.weight i*⟪F.contact i,c-Sharpness.modelCenter v⟫^2 ∧
    (∑ i, F.weight i*⟪F.contact i,c-Sharpness.modelCenter v⟫^2) = 0 := by
  have hp := zero_deficit_parameters hn hK hJ F hs v hv hA hz
  refine ⟨?_, ?_, (F.scalar_second_moment _).symm, ?_⟩
  · intro i
    rw [hp.2.2]
    have hm := Sharpness.model_support_height hn v (F.contact i) hv
      (F.contact_unit i) (hp.1 i)
    have hslack : 1-⟪F.contact i,Sharpness.modelCenter v⟫-
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) (F.contact i)‖ = 0 := by
      linarith only [hm]
    rw [hslack, mul_zero]
  · intro i; rw [hp.2.2, sub_self, inner_zero_right]
  · simp only [hp.2.2, sub_self, inner_zero_right, zero_pow (by decide : 2 ≠ 0),
      mul_zero, Finset.sum_const_zero]

/-- Both strict numeric bounds in (7.8), with the actual Euclidean norm. -/
theorem initialization_strict_bounds (v x : V n) (hv : ‖v‖ = 1)
    (hx : x ∈ Metric.closedBall ((-1/4 : ℝ) • v) (1/8 : ℝ)) :
    ‖x‖ ≤ 3/8 ∧ (3/8 : ℝ) < 1 ∧ ⟪v,x⟫ ≤ -1/8 ∧ (-1/8 : ℝ) < 0 := by
  have hr : ‖x+(1/4 : ℝ) • v‖ ≤ 1/8 := by
    have h := Metric.mem_closedBall.mp hx
    rw [dist_eq_norm] at h
    simpa only [neg_div, neg_smul, sub_neg_eq_add] using h
  have hnorm := norm_sub_le (x+(1/4 : ℝ) • v) ((1/4 : ℝ) • v)
  rw [add_sub_cancel_right, norm_smul, hv, mul_one] at hnorm
  norm_num at hnorm
  have hi := real_inner_le_norm v (x+(1/4 : ℝ) • v)
  rw [hv, one_mul, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hv, one_pow, mul_one] at hi
  exact ⟨by linarith only [hnorm, hr], by norm_num,
    by linarith only [hi, hr], by norm_num⟩

end SharpCut.Paper
