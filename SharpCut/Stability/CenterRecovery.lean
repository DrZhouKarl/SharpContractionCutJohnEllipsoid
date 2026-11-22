import SharpCut.Stability.FrameActionNorms

/-! # Center recovery from actual support slacks and weighted John projections -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Stability
open Certificate Gap Optimization
variable {n N : ℕ}

def contactSlack (F : JohnFrame n N) (c : V n) (A : MatR n) (i : Fin N) : ℝ :=
  1-⟪F.contact i,c⟫-‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖

theorem conePairing_support_slack {g q : Fin N → V n} {β α : Fin N → ℝ} {c : V n} {A : MatR n}
    (hd : DualFeasible g β α q) (r : Fin N) :
    α r*(β r-⟪g r,c⟫-‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖) ≤ conePairing g β α q c A r := by
  have h := (real_inner_le_norm (q r) (Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r))).trans
    (mul_le_mul_of_nonneg_right (hd.cone r) (norm_nonneg _))
  unfold conePairing coneHeight
  nlinarith only [h]

theorem contactSlack_nonneg {K : Set (V n)} (F : JohnFrame n N) (hs : F.Supports K) (v : V n)
    {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) (i : Fin N) :
    0 ≤ contactSlack F c A i := by
  have hp := (frame_primal F hs v hA).2 i.succ
  simp only [cutNormals, cutOffsets, Fin.cases_succ] at hp
  unfold contactSlack
  linarith only [hp]

/-- Positive original multipliers convert the cone gap into weighted support slack. -/
theorem weighted_contact_slack_bound {K : Set (V n)} (F : JohnFrame n N) (hn : 2 ≤ n) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) :
    (∑ i, F.weight i*contactSlack F c A i) ≤ 4*frameConeGap F v c A := by
  have hp := frame_primal F hs v hA
  have hd := explicit_dual_feasible F hn v hv
  have hpoint (i : Fin N) : F.weight i*contactSlack F c A i ≤
      4*conePairing (cutNormals F v) (cutOffsets N) (cutAlpha F v)
        (rotatedVectors F v (polarRotation (unrotatedQ F v))) c A i.succ := by
    have hslack := conePairing_support_slack (c := c) (A := A) hd i.succ
    simp only [cutAlpha, cutNormals, cutOffsets, Fin.cases_succ] at hslack
    change originalWeight F v i*contactSlack F c A i ≤ _ at hslack
    have hweight := mul_le_mul_of_nonneg_right (originalWeight_lower F v hn hv i).1 (contactSlack_nonneg F hs v hA i)
    nlinarith only [hslack, hweight]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hcut := conePairing_nonneg hp hd 0
  unfold frameConeGap coneGap
  rw [Fin.sum_univ_succ]
  rw [← Finset.mul_sum] at hsum
  linarith only [hsum, hcut]

/-- The model-center projection is expressed by slack, model mismatch and shape error. -/
theorem center_projection_identity (F : JohnFrame n N) (v c : V n) (A : MatR n) (i : Fin N) :
    ⟪F.contact i,c-Sharpness.modelCenter v⟫ = -contactSlack F c A i-modelMismatch v (F.contact i)+
      (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) (F.contact i)‖-
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖) := by
  simp only [Sharpness.modelCenter, inner_sub_right, real_inner_smul_right, contactSlack, modelMismatch]
  ring

/-- The vector identity in (6.7), directly from the four John moments. -/
theorem center_vector_identity (F : JohnFrame n N) (v c : V n) (A : MatR n) :
    c-Sharpness.modelCenter v = -(∑ i, (F.weight i*contactSlack F c A i) • F.contact i)-
      (∑ i, (F.weight i*modelMismatch v (F.contact i)) • F.contact i)+
      ∑ i, (F.weight i*(‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) (F.contact i)‖-
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖)) • F.contact i := by
  rw [← F.reconstruction (c-Sharpness.modelCenter v)]
  simp only [center_projection_identity F v c A, mul_add, mul_sub, mul_neg, add_smul, sub_smul, neg_smul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]

/-- Both multiplier/slack steps in (6.6), before the total deficit is inserted. -/
theorem weighted_multiplier_slack_chain {K : Set (V n)} (F : JohnFrame n N) (hn : 2 ≤ n) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) :
    (∑ i, F.weight i*contactSlack F c A i) ≤ 4*(∑ i, originalWeight F v i*contactSlack F c A i) ∧
      (∑ i, originalWeight F v i*contactSlack F c A i) ≤ frameConeGap F v c A := by
  have hp := frame_primal F hs v hA
  have hd := explicit_dual_feasible F hn v hv
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_right (originalWeight_lower F v hn hv i).1 (contactSlack_nonneg F hs v hA i)
    nlinarith only [h]
  · have hpoint (i : Fin N) : originalWeight F v i*contactSlack F c A i ≤
        conePairing (cutNormals F v) (cutOffsets N) (cutAlpha F v)
          (rotatedVectors F v (polarRotation (unrotatedQ F v))) c A i.succ := by
      have h := conePairing_support_slack (c := c) (A := A) hd i.succ
      simpa only [contactSlack, cutNormals, cutOffsets, cutAlpha, Fin.cases_succ] using h
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
    have hcut := conePairing_nonneg hp hd 0
    unfold frameConeGap coneGap
    rw [Fin.sum_univ_succ]
    linarith only [hsum, hcut]

theorem weighted_model_mismatch_norm (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    ‖∑ i, (F.weight i*modelMismatch v (F.contact i)) • F.contact i‖ ≤ Real.sqrt (8*frameDefect F v) := by
  have hb := F.weighted_bessel (fun i => modelMismatch v (F.contact i))
  have hs := weighted_model_mismatch_bound F hn v hv
  have hp : 0 ≤ 8*frameDefect F v := mul_nonneg (by norm_num) (frameDefect_nonneg F hn v hv)
  have hroot := Real.sq_sqrt hp
  nlinarith only [hb, hs, hroot, norm_nonneg (∑ i, (F.weight i*modelMismatch v (F.contact i)) • F.contact i),
    Real.sqrt_nonneg (8*frameDefect F v)]

/-- The ordered support reconstruction bound in (9.23), before the shape constant is inserted. -/
theorem center_recovery_bound {K : Set (V n)} (F : JohnFrame n N) (hn : 2 ≤ n) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) :
    ‖c-Sharpness.modelCenter v‖ ≤ 4*frameConeGap F v c A+
      Real.sqrt (8*frameDefect F v)+frobeniusNorm (A-Sharpness.modelShape v) := by
  let Sr : V n := ∑ i, (F.weight i*contactSlack F c A i) • F.contact i
  let Sg : V n := ∑ i, (F.weight i*modelMismatch v (F.contact i)) • F.contact i
  let Sd : V n := ∑ i, (F.weight i*(‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) (F.contact i)‖-
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖)) • F.contact i
  have hvec : c-Sharpness.modelCenter v = -Sr-Sg+Sd := by
    rw [← F.reconstruction (c-Sharpness.modelCenter v)]
    simp only [center_projection_identity F v c A, mul_add, mul_sub, mul_neg, add_smul, sub_smul, neg_smul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    simp only [Sr, Sg, Sd, mul_sub, sub_smul, Finset.sum_sub_distrib]
  have hsr : ‖Sr‖ ≤ 4*frameConeGap F v c A := by
    have ht : ‖Sr‖ ≤ ∑ i, F.weight i*contactSlack F c A i := by
      calc
        _ ≤ ∑ i, ‖(F.weight i*contactSlack F c A i) • F.contact i‖ := norm_sum_le _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (F.weight_pos i).le (contactSlack_nonneg F hs v hA i)),
            F.contact_unit i, mul_one]
    exact ht.trans (weighted_contact_slack_bound F hn hs v hv hA)
  have hsg : ‖Sg‖ ≤ Real.sqrt (8*frameDefect F v) := weighted_model_mismatch_norm F hn v hv
  have hsd : ‖Sd‖ ≤ frobeniusNorm (A-Sharpness.modelShape v) := by
    have h := frame_support_difference_bound F (Sharpness.modelShape v) A
    have ht : Sharpness.modelShape v-A = -(A-Sharpness.modelShape v) := by abel
    rwa [ht, frobeniusNorm_neg] at h
  rw [hvec]
  have hnorm := (norm_add_le (-Sr-Sg) Sd).trans (add_le_add (norm_sub_le (-Sr) Sg) (le_refl ‖Sd‖))
  rw [norm_neg] at hnorm
  linarith only [hnorm, hsr, hsg, hsd]

end SharpCut.Stability
