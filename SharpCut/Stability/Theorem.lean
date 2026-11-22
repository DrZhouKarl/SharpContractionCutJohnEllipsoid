import SharpCut.Stability.ShapeTransfer

/-! # Complete dimension-independent stability theorem with the paper's constants -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Stability
open Certificate Gap
variable {n N : ℕ}

/-- The center bound includes every feasible ellipsoid and the zero-deficit case. -/
theorem near_extremal_center_bound (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (F : JohnFrame n N) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A)
    (hε : 0 ≤ volumeDeficit n A) (hsmall : volumeDeficit n A ≤ 1/1000000) :
    ‖c-Sharpness.modelCenter v‖ ≤ 50*Real.sqrt (volumeDeficit n A) := by
  have hshape := near_extremal_shape_bound hn hK hJ F hs v hv hA hε hsmall
  have hcontact := near_extremal_contact_stability hn hK hJ F hs v hv hA hε hsmall
  have hcenter := center_recovery_bound F hn hs v hv hA
  have hgap := exact_volume_deficit hn hK hJ F hs v hv hA
  have hC : frameConeGap F v c A ≤ volumeDeficit n A := by nlinarith only [hgap.1, hgap.2.1, hgap.2.2.2.1]
  have hχpos := frameDefect_nonneg F hn v hv
  have hroot : Real.sqrt (8*frameDefect F v) ≤ 16*Real.sqrt (volumeDeficit n A) := by
    have hsq1 := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hχpos)
    have hsq2 := Real.sq_sqrt hε
    have hp1 := Real.sqrt_nonneg (8*frameDefect F v)
    have hp2 := Real.sqrt_nonneg (volumeDeficit n A)
    nlinarith only [hcontact.1, hsq1, hsq2, hp1, hp2]
  have hsmallroot := small_deficit_sqrt (volumeDeficit n A) hε hsmall
  have hεsqrt : 4*volumeDeficit n A ≤ (1/250 : ℝ)*Real.sqrt (volumeDeficit n A) := by
    have hprod := mul_le_mul_of_nonneg_right hsmallroot (Real.sqrt_nonneg (volumeDeficit n A))
    have hsq := Real.sq_sqrt hε
    nlinarith only [hprod, hsq]
  have hp := Real.sqrt_nonneg (volumeDeficit n A)
  nlinarith only [hcenter, hshape, hC, hroot, hεsqrt, hp]

/-- Theorem 6.2, complete with all five exact estimates and dimension-independent constants. -/
theorem dimension_independent_stability (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (F : JohnFrame n N) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A)
    (hε : 0 ≤ volumeDeficit n A) (hsmall : volumeDeficit n A ≤ 1/1000000) :
    frameDefect F v ≤ 32*volumeDeficit n A ∧
    frobeniusNorm (unrotatedQ F v-inverseModel v) ≤ 4*Real.sqrt (volumeDeficit n A) ∧
    frobeniusNorm (A-Sharpness.modelShape v) ≤ 30*Real.sqrt (volumeDeficit n A) ∧
    ‖c-Sharpness.modelCenter v‖ ≤ 50*Real.sqrt (volumeDeficit n A) ∧
    (∑ i, F.weight i*(Metric.infDist (F.contact i) (Equality.modelContactSet v))^2) ≤
      (1024/3 : ℝ)*volumeDeficit n A := by
  have hc := near_extremal_contact_stability hn hK hJ F hs v hv hA hε hsmall
  exact ⟨hc.1, hc.2.1, near_extremal_shape_bound hn hK hJ F hs v hv hA hε hsmall,
    near_extremal_center_bound hn hK hJ F hs v hv hA hε hsmall, hc.2.2⟩

end SharpCut.Stability
