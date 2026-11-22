import SharpCut.Matrix.NuclearInequalities
import SharpCut.Gap.Exact

/-! # The four nonnegative nuclear deficits and the exact polar correction

This is (10.6)-(10.8). The correction is retained in both identities where it
occurs, and is proved to vanish under the sufficient commuting condition.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix Set
namespace SharpCut.Nuclear
open Certificate Optimization Gap
variable {n N : ℕ}

def frameSupportSlack (F : JohnFrame n N) (v c : V n) (A : MatR n) : ℝ :=
  (∑ i, originalWeight F v i*(1-⟪F.contact i,c⟫-‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖))+
    cutWeight n*(-⟪v,c⟫-‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖)

def frameNuclearTotal (F : JohnFrame n N) (v : V n) (A : MatR n) : ℝ :=
  (∑ i, originalWeight F v i*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖)+
    cutWeight n*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖

def frameTriangleGap (F : JohnFrame n N) (v : V n) (A : MatR n) : ℝ :=
  frameNuclearTotal F v A-nuclearNorm (A*unrotatedQ F v)

def frameLogGap (F : JohnFrame n N) (v : V n) (A : MatR n) : ℝ :=
  nuclearNorm (A*unrotatedQ F v)-(n : ℝ)-Real.log (A*unrotatedQ F v).det

def framePolarCorrection (F : JohnFrame n N) (v : V n) (A : MatR n) : ℝ :=
  nuclearNorm (A*unrotatedQ F v)-(A*frameMatrix F v).trace

theorem frameSupportSlack_finite (F : JohnFrame n N) (v c : V n) (A : MatR n) :
    frameSupportSlack F v c A = ∑ r, cutAlpha F v r*(cutOffsets N r-⟪cutNormals F v r,c⟫-
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (cutNormals F v r)‖) := by
  simp only [Fin.sum_univ_succ, cutAlpha, cutNormals, cutOffsets, Fin.cases_zero, Fin.cases_succ,
    zero_sub, frameSupportSlack, add_comm]

theorem frameNuclearTotal_finite (F : JohnFrame n N) (v : V n) (A : MatR n) :
    frameNuclearTotal F v A = ∑ r, cutAlpha F v r*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (cutNormals F v r)‖ := by
  simp only [Fin.sum_univ_succ, cutAlpha, cutNormals, Fin.cases_zero, Fin.cases_succ,
    frameNuclearTotal, add_comm]

theorem frameSupportSlack_mass (F : JohnFrame n N) (hn : 2 ≤ n) (v c : V n) (hv : ‖v‖ = 1) (A : MatR n) :
    frameSupportSlack F v c A = (n : ℝ)-frameNuclearTotal F v A := by
  have hd := explicit_dual_feasible F hn v hv
  have hbal : ∑ r, cutAlpha F v r*⟪cutNormals F v r,c⟫ = 0 := by
    have h := congrArg (fun u : V n => ⟪u,c⟫) hd.balance
    simpa only [sum_inner, real_inner_smul_left, inner_zero_left] using h
  rw [frameSupportSlack_finite, frameNuclearTotal_finite]
  simp only [mul_sub, Finset.sum_sub_distrib, hd.normalization, hbal, sub_zero]

theorem frameSupportSlack_nonneg (F : JohnFrame n N) (hn : 2 ≤ n) (v c : V n) (hv : ‖v‖ = 1) (A : MatR n)
    (hp : PrimalFeasible (cutNormals F v) (cutOffsets N) c A) : 0 ≤ frameSupportSlack F v c A := by
  rw [frameSupportSlack_finite]
  apply Finset.sum_nonneg
  intro r _
  exact mul_nonneg (dual_alpha_nonneg (explicit_dual_feasible F hn v hv) r) (by linarith only [hp.2 r])

theorem frameNuclearTotal_bound (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (A : MatR n) :
    nuclearNorm (A*unrotatedQ F v) ≤ frameNuclearTotal F v A := by
  have ht : 0 ≤ cutWeight n := by unfold cutWeight; linarith [(inverseDimension_bounds hn).1]
  have heach (i : Fin N) :
      nuclearNorm (originalWeight F v i • cross (Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i))
        (lorentzDirection v (F.contact i))) = originalWeight F v i*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖ := by
    rw [nuclearNorm_smul_nonneg _ (originalWeight_lower F v hn hv i).2.le, nuclearNorm_cross,
      lorentzDirection_unit hn v (F.contact i) hv (F.contact_unit i), mul_one]
  have hcut : nuclearNorm (cutWeight n • cross (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) v) =
      cutWeight n*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖ := by
    rw [nuclearNorm_smul_nonneg _ ht, nuclearNorm_cross, hv, mul_one]
  have he : A*unrotatedQ F v =
      (∑ i, originalWeight F v i • cross (Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)) (lorentzDirection v (F.contact i)))+
        cutWeight n • cross (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) v := by
    simp only [unrotatedQ, Matrix.mul_add, Matrix.mul_sum, Matrix.mul_smul, ← cross_self v, mul_cross]
  rw [he]
  calc
    _ ≤ nuclearNorm (∑ i, originalWeight F v i • cross (Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)) (lorentzDirection v (F.contact i)))+
          nuclearNorm (cutWeight n • cross (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) v) := nuclearNorm_triangle _ _
    _ ≤ (∑ i, nuclearNorm (originalWeight F v i • cross (Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)) (lorentzDirection v (F.contact i))))+
          nuclearNorm (cutWeight n • cross (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) v) :=
      add_le_add (nuclearNorm_sum Finset.univ _) le_rfl
    _ = frameNuclearTotal F v A := by simp only [heach, hcut, frameNuclearTotal]

theorem right_polar_identity (Q : MatR n) (hQ : 0 < Q.det) : Q*(polarRotation Q)ᵀ = polarMatrix Q := by
  have h := congrArg Matrix.transpose (polarRotation_aggregate hQ)
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, (polarMatrix_posDef hQ).isHermitian.isSymm.eq] using h

theorem framePolarCorrection_nonneg (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (A : MatR n) :
    0 ≤ framePolarCorrection F v A := by
  have hQ := unrotatedQ_det_pos F hn v hv
  have h := trace_le_nuclear (A*unrotatedQ F v) (polarRotation (unrotatedQ F v)) (common_polar_attainment _ hQ).1
  rw [Matrix.mul_assoc, right_polar_identity _ hQ] at h
  exact sub_nonneg.mpr h

theorem frameLogGap_spectral (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (A : MatR n) (hA : A.PosDef) :
    frameLogGap F v A = ∑ i, (singularValue (A*unrotatedQ F v) i-1-Real.log (singularValue (A*unrotatedQ F v) i)) ∧
      0 ≤ frameLogGap F v A := by
  have hX : 0 < (A*unrotatedQ F v).det := by rw [Matrix.det_mul]; exact mul_pos hA.det_pos (unrotatedQ_det_pos F hn v hv)
  exact nuclear_logdet_spectral _ hX

theorem frame_cone_nuclear_identity (F : JohnFrame n N) (hn : 2 ≤ n) (v c : V n) (hv : ‖v‖ = 1) (A : MatR n)
    (hp : PrimalFeasible (cutNormals F v) (cutOffsets N) c A) :
    frameConeGap F v c A = frameSupportSlack F v c A+frameTriangleGap F v A+framePolarCorrection F v A := by
  have h := coneGap_trace hp (explicit_dual_feasible F hn v hv)
  rw [rotated_aggregate_eq_polar F hn v hv] at h
  change frameConeGap F v c A = (n : ℝ)-(A*frameMatrix F v).trace at h
  rw [h, frameSupportSlack_mass F hn v c hv A]
  unfold frameTriangleGap framePolarCorrection
  ring

theorem frame_matrix_nuclear_identity (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (A : MatR n) :
    pairDivergence A (frameMatrix F v) = frameLogGap F v A-framePolarCorrection F v A := by
  have hQ := unrotatedQ_det_pos F hn v hv
  have hM : (frameMatrix F v).PosDef := polarMatrix_posDef hQ
  unfold pairDivergence matrixDivergence frameLogGap framePolarCorrection
  rw [matchingMatrix_trace A _ hM, matchingMatrix_det A _ hM, Matrix.det_mul,
    show (frameMatrix F v).det = (unrotatedQ F v).det from polarMatrix_det hQ]
  ring

/-- A sufficient commuting condition makes the right polar correction exactly zero. -/
theorem commuting_polar_correction (Q A : MatR n) (hQ : 0 < Q.det) (hA : A.PosDef)
    (hcomm : Commute A (polarMatrix Q)) : nuclearNorm (A*Q)-(A*polarMatrix Q).trace = 0 := by
  let M := polarMatrix Q
  let U := polarRotation Q
  have hM : M.PosDef := polarMatrix_posDef hQ
  have hAM : (A*M).PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    ((hA.isStrictlyPositive.commute_iff hM.isStrictlyPositive).mp hcomm)
  have hQU : M*U = Q := by
    dsimp only [M, U, polarRotation]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM.det_pos.ne'), Matrix.one_mul]
  have hAQ : A*Q = (A*M)*U := by rw [← hQU, Matrix.mul_assoc]
  have hgram : rowGram (A*Q) = (A*M)^2 := by
    rw [hAQ, rowGram, Matrix.transpose_mul, hAM.isHermitian.isSymm.eq]
    calc
      _ = (A*M)*(U*Uᵀ)*(A*M) := by simp only [Matrix.mul_assoc]
      _ = (A*M)^2 := by rw [polarRotation_left_orthogonal hQ, Matrix.mul_one, pow_two]
  rw [nuclearNorm, hgram, CFC.sqrt_sq (A*M) hAM.posSemidef.nonneg]
  exact sub_self _

/-- All four terms and all three exact (10.8) identities for an actual feasible central-cut ellipsoid. -/
theorem nuclear_frame_deficit (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K) (hJ : IsJohnNormalized K)
    (F : JohnFrame n N) (hs : F.Supports K) (v : V n) (hv : ‖v‖ = 1)
    {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) :
    0 ≤ frameSupportSlack F v c A ∧ 0 ≤ frameTriangleGap F v A ∧
    0 ≤ frameLogGap F v A ∧ 0 ≤ framePolarCorrection F v A ∧
    frameConeGap F v c A = frameSupportSlack F v c A+frameTriangleGap F v A+framePolarCorrection F v A ∧
    pairDivergence A (frameMatrix F v) = frameLogGap F v A-framePolarCorrection F v A ∧
    volumeDeficit n A = geometricGap F v+frameSupportSlack F v c A+frameTriangleGap F v A+frameLogGap F v A ∧
    (Commute A (frameMatrix F v) → framePolarCorrection F v A = 0) := by
  have hp := frame_primal F hs v hA
  have hc := frame_cone_nuclear_identity F hn v c hv A hp
  have hd := frame_matrix_nuclear_identity F hn v hv A
  have he := (exact_volume_deficit hn hK hJ F hs v hv hA).1
  refine ⟨frameSupportSlack_nonneg F hn v c hv A hp, sub_nonneg.mpr (frameNuclearTotal_bound F hn v hv A),
    (frameLogGap_spectral F hn v hv A hA.1).2, framePolarCorrection_nonneg F hn v hv A, hc, hd, ?_, ?_⟩
  · rw [hc, hd] at he
    linarith only [he]
  · intro hcomm
    exact commuting_polar_correction (unrotatedQ F v) A (unrotatedQ_det_pos F hn v hv) hA.1 hcomm

end SharpCut.Nuclear
