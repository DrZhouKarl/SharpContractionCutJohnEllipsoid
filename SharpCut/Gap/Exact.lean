import SharpCut.Optimization.Gaps
import SharpCut.Geometry.SharpTheorem

/-! # Exact geometric, cone and matrix volume deficits -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix Set MeasureTheory
namespace SharpCut.Gap
open Certificate Optimization
variable {n N : ℕ}

def frameMatrix (F : JohnFrame n N) (v : V n) : MatR n := polarMatrix (unrotatedQ F v)
def geometricGap (F : JohnFrame n N) (v : V n) : ℝ := Real.log (sharpRatio n*(frameMatrix F v).det)
def volumeDeficit (n : ℕ) (A : MatR n) : ℝ := Real.log (sharpRatio n/A.det)
def frameConeGap (F : JohnFrame n N) (v c : V n) (A : MatR n) : ℝ :=
  coneGap (cutNormals F v) (cutOffsets N) (cutAlpha F v)
    (rotatedVectors F v (polarRotation (unrotatedQ F v))) c A

theorem frame_primal {K : Set (V n)} (F : JohnFrame n N) (hs : F.Supports K) (v : V n)
    {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) :
    PrimalFeasible (cutNormals F v) (cutOffsets N) c A := by
  apply (primalFeasible_iff_containment _ _ _ _).mpr
  rw [cut_polytope]
  exact ⟨hA.1, fun x hx => ⟨F.supporting_subset hs (hA.2 hx).1, (hA.2 hx).2⟩⟩

theorem geometricGap_lower (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (1/1500 : ℝ)*frameDefect F v ≤ geometricGap F v := by
  unfold geometricGap frameMatrix
  rw [polarMatrix_det (unrotatedQ_det_pos F hn v hv)]
  exact (john_frame_certificate_bound F hn v hv).2.2.1

theorem geometricGap_nonneg (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    0 ≤ geometricGap F v :=
  (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/1500) (frameDefect_nonneg F hn v hv)).trans
    (geometricGap_lower F hn v hv)

theorem frame_pair_gap {K : Set (V n)} (F : JohnFrame n N) (hn : 2 ≤ n) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) :
    dualityGap A (frameMatrix F v) = frameConeGap F v c A+pairDivergence A (frameMatrix F v) := by
  have h := normalized_pair_gap (frame_primal F hs v hA) (explicit_dual_feasible F hn v hv)
  rw [rotated_aggregate_eq_polar F hn v hv] at h
  exact h

theorem frameConeGap_nonneg {K : Set (V n)} (F : JohnFrame n N) (hn : 2 ≤ n) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) :
    0 ≤ frameConeGap F v c A :=
  coneGap_nonneg (frame_primal F hs v hA) (explicit_dual_feasible F hn v hv)

/-- Proposition 4.1 in John coordinates, for every supporting frame and feasible cut ellipsoid. -/
theorem exact_volume_deficit (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (F : JohnFrame n N) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) :
    volumeDeficit n A = geometricGap F v+frameConeGap F v c A+pairDivergence A (frameMatrix F v) ∧
    0 ≤ geometricGap F v ∧ 0 ≤ frameConeGap F v c A ∧ 0 ≤ pairDivergence A (frameMatrix F v) ∧
    frameDefect F v ≤ 1500*geometricGap F v ∧ frameDefect F v ≤ 1500*volumeDeficit n A := by
  have hM : (frameMatrix F v).PosDef := polarMatrix_posDef (unrotatedQ_det_pos F hn v hv)
  have he := frame_pair_gap F hn hs v hv hA
  have hsum : volumeDeficit n A = geometricGap F v+frameConeGap F v c A+pairDivergence A (frameMatrix F v) := by
    have hl : volumeDeficit n A = geometricGap F v+dualityGap A (frameMatrix F v) := by
      unfold volumeDeficit geometricGap dualityGap
      rw [Real.log_div (sharpRatio_pos (show 1 ≤ n by omega)).ne' hA.1.det_pos.ne',
        Real.log_mul (sharpRatio_pos (show 1 ≤ n by omega)).ne' hM.det_pos.ne']
      ring
    rw [hl, he]
    ring
  have hg := geometricGap_nonneg F hn v hv
  have hc := frameConeGap_nonneg F hn hs v hv hA
  have hd := pairDivergence_nonneg A (frameMatrix F v) hA.1 hM
  have hchi := geometricGap_lower F hn v hv
  refine ⟨hsum, hg, hc, hd, ?_, ?_⟩ <;> nlinarith only [hsum, hg, hc, hd, hchi]

theorem volume_deficit_nonneg (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (F : JohnFrame n N) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) :
    0 ≤ volumeDeficit n A := by
  have h := exact_volume_deficit hn hK hJ F hs v hv hA
  rw [h.1]
  exact add_nonneg (add_nonneg h.2.1 h.2.2.1) h.2.2.2.1

end SharpCut.Gap
