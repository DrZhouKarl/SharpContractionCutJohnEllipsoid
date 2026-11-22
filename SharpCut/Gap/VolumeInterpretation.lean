import SharpCut.Gap.ZeroSets

/-! # Actual Lebesgue-volume meaning of the deficit before and after affine normalization -/

noncomputable section
open scoped RealInnerProductSpace
open Matrix Set MeasureTheory
namespace SharpCut.Gap
variable {n : ℕ} [NeZero n]

/-- Actual new maximal-volume ellipsoids have the stated original-coordinate deficit. -/
theorem affine_optimal_volume_deficit (hn : 2 ≤ n) {K : Set (V n)}
    {c v a : V n} {S A : MatR n} (hmax : IsMaxDet K c S)
    (hcut : IsMaxDet (K ∩ centralHalfspace c v) a A) :
    volumeDeficit n (Khachiyan.affineShape (S⁻¹*A)) =
      Real.log (sharpRatio n*(maxEllipsoidVolume K).toReal/
        (maxEllipsoidVolume (K ∩ centralHalfspace c v)).toReal) := by
  have hv : maxEllipsoidVolume (K ∩ centralHalfspace c v) = volume (ellipsoid a A) := hcut.maxEllipsoidVolume_eq
  have hr := Khachiyan.volume_ellipsoid_real_ratio (a := a) hmax hcut.posDef
  rw [← hv] at hr
  unfold volumeDeficit
  rw [Khachiyan.normalized_shape_det hmax.posDef hcut.posDef, ← hr, div_div_eq_mul_div]

theorem normalized_optimal_volume_deficit (hn : 2 ≤ n) {K : Set (V n)} (hJ : IsJohnNormalized K)
    {v a : V n} {A : MatR n} (hcut : IsMaxDet (K ∩ centralHalfspace 0 v) a A) :
    volumeDeficit n A = Real.log (sharpRatio n*(maxEllipsoidVolume K).toReal/
      (maxEllipsoidVolume (K ∩ centralHalfspace 0 v)).toReal) := by
  have hv : maxEllipsoidVolume (K ∩ centralHalfspace 0 v) = volume (ellipsoid a A) := hcut.maxEllipsoidVolume_eq
  have hr := Khachiyan.volume_ellipsoid_real_ratio (a := a) hJ hcut.posDef
  rw [← hv, Matrix.det_one, div_one] at hr
  unfold volumeDeficit
  rw [← hr, div_div_eq_mul_div]

end SharpCut.Gap
