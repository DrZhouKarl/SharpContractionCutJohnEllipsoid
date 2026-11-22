import SharpCut.Geometry
import SharpCut.Scalar.Constants
import Khachiyan.OneDimensional

/-! # The exact one-dimensional branch and actual-volume well-definedness

Reuse the preceding paper's interval theorem with the new cut-sign adapter.
This does not assert the sharp upper bound in dimensions n ≥ 2.
-/

noncomputable section
open scoped ENNReal RealInnerProductSpace
namespace SharpCut

theorem john_center_cut_isConvexBody {n : ℕ} [NeZero n]
    {K : Set (V n)} (hK : IsConvexBody K) {v : V n} (hv : v ≠ 0) :
    IsConvexBody (K ∩ centralHalfspace (Khachiyan.johnCenter K) v) := by
  rw [centralHalfspace_eq_legacy]
  exact Khachiyan.john_center_cut_isConvexBody hK (neg_ne_zero.mpr hv)

theorem center_cut_volume_eq_one {K : Set (V 1)} (hK : IsConvexBody K)
    {v : V 1} (hv : v ≠ 0) :
    maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v) =
      ENNReal.ofReal (sharpRatio 1) * maxEllipsoidVolume K := by
  rw [centralHalfspace_eq_legacy, sharpRatio_one]
  exact Khachiyan.OneDimensional.center_cut_volume_eq_half hK (neg_ne_zero.mpr hv)

theorem center_cut_volume_ratio_eq_one {K : Set (V 1)} (hK : IsConvexBody K)
    {v : V 1} (hv : v ≠ 0) :
    (maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v)).toReal /
      (maxEllipsoidVolume K).toReal = sharpRatio 1 := by
  rw [centralHalfspace_eq_legacy, sharpRatio_one]
  exact Khachiyan.OneDimensional.center_cut_volume_ratio_eq_half hK (neg_ne_zero.mpr hv)

theorem fixed_dimension_attainment_one :
    ∃ (K : Set (V 1)) (v : V 1), IsConvexBody K ∧ v ≠ 0 ∧
      maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v) =
        ENNReal.ofReal (sharpRatio 1) * maxEllipsoidVolume K := by
  have hK : IsConvexBody (unitBall 1) := by
    refine ⟨isCompact_closedBall _ _, convex_closedBall _ _, 0, ?_⟩
    change (0 : V 1) ∈ interior (Metric.closedBall 0 1)
    rw [interior_closedBall (0 : V 1) one_ne_zero]
    simp
  have hv : Khachiyan.OneDimensional.point 1 ≠ 0 := by
    intro h
    have h0 := congrArg (fun x : V 1 => x 0) h
    norm_num [Khachiyan.OneDimensional.point] at h0
  exact ⟨unitBall 1, Khachiyan.OneDimensional.point 1, hK, hv,
    center_cut_volume_eq_one hK hv⟩

end SharpCut
