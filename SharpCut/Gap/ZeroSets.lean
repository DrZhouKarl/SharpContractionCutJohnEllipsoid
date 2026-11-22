import SharpCut.Gap.Exact
import SharpCut.Gap.MatrixDivergence

/-! # Every exact zero set in the volume deficit decomposition -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Gap
open Certificate Optimization
variable {n N : ℕ}

theorem geometricGap_upper (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    geometricGap F v ≤ frameDefect F v/(2*(2-inverseDimension n)) := by
  unfold geometricGap frameMatrix
  rw [polarMatrix_det (unrotatedQ_det_pos F hn v hv)]
  exact (john_frame_certificate_bound F hn v hv).2.2.2.1

theorem geometricGap_zero_iff (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    geometricGap F v = 0 ↔ frameDefect F v = 0 := by
  constructor
  · intro h
    have hl := geometricGap_lower F hn v hv
    rw [h] at hl
    have hc := frameDefect_nonneg F hn v hv
    nlinarith only [hl, hc]
  · intro h
    have hl := geometricGap_upper F hn v hv
    rw [h, zero_div] at hl
    exact le_antisymm hl (geometricGap_nonneg F hn v hv)

theorem geometricGap_contacts_iff (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    geometricGap F v = 0 ↔ ∀ i, height F v i = -1 ∨ height F v i = inverseDimension n :=
  (geometricGap_zero_iff F hn v hv).trans (frameDefect_zero_iff F hn v hv)

theorem frameConeGap_zero_iff {K : Set (V n)} (F : JohnFrame n N) (hn : 2 ≤ n) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) :
    frameConeGap F v c A = 0 ↔ ∀ r,
      conePairing (cutNormals F v) (cutOffsets N) (cutAlpha F v)
        (rotatedVectors F v (polarRotation (unrotatedQ F v))) c A r = 0 :=
  coneGap_zero_iff (frame_primal F hs v hA) (explicit_dual_feasible F hn v hv)

theorem volumeDeficit_zero_iff (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (F : JohnFrame n N) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) :
    volumeDeficit n A = 0 ↔ geometricGap F v = 0 ∧ frameConeGap F v c A = 0 ∧
      pairDivergence A (frameMatrix F v) = 0 := by
  have h := exact_volume_deficit hn hK hJ F hs v hv hA
  constructor
  · intro h0
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith only [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h0]
  · rintro ⟨hg, hc, hd⟩
    rw [h.1, hg, hc, hd]
    norm_num

end SharpCut.Gap
