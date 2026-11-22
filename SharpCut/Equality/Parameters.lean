import SharpCut.Gap.VolumeInterpretation
import SharpCut.Sharpness.ModelSupport

/-! # Zero volume deficit determines the actual extremal shape and center -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Equality
open Certificate Optimization Gap
variable {n N : ℕ}

theorem polarMatrix_of_posDef (Q : MatR n) (hQ : Q.PosDef) : polarMatrix Q = Q := by
  unfold polarMatrix
  rw [hQ.isHermitian.isSymm.eq]
  exact CFC.sqrt_unique rfl hQ.posSemidef.nonneg

theorem frameMatrix_model (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hh : ∀ i, height F v i = -1 ∨ height F v i = inverseDimension n) : frameMatrix F v = inverseModel v := by
  rw [frameMatrix, sharp_frame_model_matrix F hn v hv hh,
    polarMatrix_of_posDef _ (Sharpness.inverseModel_posDef hn v)]

theorem conePairing_zero_support {g q : Fin N → V n} {beta alpha : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g beta c A) (hd : DualFeasible g beta alpha q) (r : Fin N)
    (ha : 0 < alpha r) (hzero : conePairing g beta alpha q c A r = 0) :
    beta r-⟪g r, c⟫ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ := by
  have hs : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ ≤ beta r-⟪g r, c⟫ := by linarith [hp.2 r]
  have hi : ⟪q r, Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ ≤
      alpha r*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hd.cone r) (norm_nonneg _))
  unfold conePairing coneHeight at hzero
  have hle : beta r-⟪g r, c⟫ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ := by nlinarith only [hi, hzero, ha]
  exact le_antisymm hle hs

theorem zero_deficit_parameters (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (F : JohnFrame n N) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n}
    (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) (hzero : volumeDeficit n A = 0) :
    (∀ i, height F v i = -1 ∨ height F v i = inverseDimension n) ∧
      A = Sharpness.modelShape v ∧ c = Sharpness.modelCenter v := by
  have hz := (volumeDeficit_zero_iff hn hK hJ F hs v hv hA).mp hzero
  have hh := (geometricGap_contacts_iff F hn v hv).mp hz.1
  have hM : (frameMatrix F v).PosDef := polarMatrix_posDef (unrotatedQ_det_pos F hn v hv)
  have hshape := (pairDivergence_zero_iff A (frameMatrix F v) hA.1 hM).mp hz.2.2
  rw [frameMatrix_model F hn v hv hh, ← Sharpness.modelShape_eq_inverse hn v hv] at hshape
  have hcomp := (frameConeGap_zero_iff F hn hs v hv hA).mp hz.2.1
  have hp := frame_primal F hs v hA
  have hd := explicit_dual_feasible F hn v hv
  have hpair (i : Fin N) : ⟪F.contact i, c-Sharpness.modelCenter v⟫ = 0 := by
    have ha : 0 < cutAlpha F v i.succ := (originalWeight_lower F v hn hv i).2
    have hsupport := conePairing_zero_support hp hd i.succ ha (hcomp i.succ)
    simp only [cutOffsets, cutNormals, Fin.cases_succ] at hsupport
    rw [hshape] at hsupport
    have hmodel := Sharpness.model_support_height hn v (F.contact i) hv (F.contact_unit i) (hh i)
    rw [inner_sub_right]
    linarith only [hsupport, hmodel]
  have hsum := F.scalar_second_moment (c-Sharpness.modelCenter v)
  simp only [hpair, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero] at hsum
  have hc : c = Sharpness.modelCenter v := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsum.symm))
  exact ⟨hh, hshape, hc⟩

end SharpCut.Equality
