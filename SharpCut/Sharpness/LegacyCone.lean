import SharpCut.Geometry.SharpTheorem
import Khachiyan.ConeLimit

/-! # Rebuilt legacy cone witnesses matched to the exact new fixed-dimensional constant -/

noncomputable section
open scoped RealInnerProductSpace ENNReal BigOperators
open Matrix Set MeasureTheory Filter Topology
namespace SharpCut.Sharpness
variable {m : ℕ}

/-- The legacy feasible determinant is exactly the new fixed-dimensional sharp constant. -/
theorem legacy_cone_constant (hm : 1 ≤ m) : Khachiyan.Cone.lowerBound m = sharpRatio (m+1) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hx : 0 < ((m : ℝ)+1)/(m : ℝ) := div_pos (by positivity) (by exact_mod_cast (by omega : 0 < m))
  have hbase : 1+1/(m : ℝ) = ((m : ℝ)+1)/(m : ℝ) := by field_simp [hm0] <;> ring
  rw [Khachiyan.Cone.lowerBound, sharpRatio, ite_eq_right (by omega : m+1 ≠ 0), ite_eq_right (by omega : m+1 ≠ 1)]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  rw [hbase, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1
  congr 1
  ring

/-- The cone cut is the actual paper-oriented central cut through its John center. -/
theorem legacy_cone_cut (hm : 1 ≤ m) :
    Khachiyan.Cone.cut m = Khachiyan.Cone.body m ∩ centralHalfspace (Khachiyan.johnCenter (Khachiyan.Cone.body m)) (-Khachiyan.Cone.cutNormal m) := by
  rw [centralHalfspace_eq_legacy, neg_neg]
  exact Khachiyan.Cone.cut_eq_canonical_cut hm

/-- The newly proved upper bound closes exact fixed-dimensional attainment for the old feasible cone witness. -/
theorem legacy_cone_attainment (hm : 1 ≤ m) :
    IsConvexBody (Khachiyan.Cone.body m) ∧ IsJohnNormalized (Khachiyan.Cone.body m) ∧
    IsConvexBody (Khachiyan.Cone.cut m) ∧
    IsFeasible (Khachiyan.Cone.cut m) (Khachiyan.Cone.candidateCenter m) (Khachiyan.Cone.candidateShape m) ∧
    (Khachiyan.Cone.candidateShape m).det = sharpRatio (m+1) ∧
    Khachiyan.Cone.volumeRatio m = sharpRatio (m+1) := by
  have hbody := Khachiyan.Cone.isConvexBody_body hm
  have hupper := Geometry.sharp_center_cut_ratio_upper (show 1 ≤ m+1 by omega) hbody
    (neg_ne_zero.mpr (Khachiyan.Cone.cutNormal_ne_zero m))
  rw [← legacy_cone_cut hm] at hupper
  have hlower := Khachiyan.Cone.lowerBound_le_volumeRatio hm
  rw [legacy_cone_constant hm] at hlower
  have hratio : Khachiyan.Cone.volumeRatio m = sharpRatio (m+1) := le_antisymm hupper hlower
  exact ⟨hbody, Khachiyan.Cone.isJohnNormalized_body hm, Khachiyan.Cone.isConvexBody_cut hm,
    Khachiyan.Cone.candidate_feasible hm, (Khachiyan.Cone.candidateShape_det_eq_lowerBound hm).trans (legacy_cone_constant hm), hratio⟩

/-- The legacy limit is current imported kernel evidence, not merely a historical log. -/
theorem sharpRatio_shifted_limit : Tendsto (fun m : ℕ => sharpRatio (m+1)) atTop (𝓝 Khachiyan.rStar) := by
  have h := Khachiyan.Cone.tendsto_lowerBound
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with m hm
  exact legacy_cone_constant hm

end SharpCut.Sharpness

namespace SharpCut.Sharpness
variable {m : ℕ}

/-- The old feasible candidate is now the actual maximum-volume ellipse at each fixed dimension. -/
theorem legacy_cone_candidate_maximal (hm : 1 ≤ m) :
    IsMaxDet (Khachiyan.Cone.cut m) (Khachiyan.Cone.candidateCenter m) (Khachiyan.Cone.candidateShape m) := by
  have hp := Khachiyan.Cone.candidate_feasible hm
  have hcandidate := Khachiyan.Cone.candidate_volume_ratio hm
  rw [legacy_cone_constant hm] at hcandidate
  have hcut := (legacy_cone_attainment hm).2.2.2.2.2
  change (maxEllipsoidVolume (Khachiyan.Cone.cut m)).toReal/(maxEllipsoidVolume (Khachiyan.Cone.body m)).toReal = sharpRatio (m+1) at hcut
  have hden := (Khachiyan.Cone.isJohnNormalized_body hm).maxEllipsoidVolume_toReal_pos
  have heq := congrArg (fun t : ℝ => t*(maxEllipsoidVolume (Khachiyan.Cone.body m)).toReal) (hcandidate.trans hcut.symm)
  rw [div_mul_cancel₀ _ hden.ne', div_mul_cancel₀ _ hden.ne'] at heq
  have hfinite1 := Khachiyan.volume_ellipsoid_lt_top (Khachiyan.Cone.candidateCenter m) (Khachiyan.Cone.candidateShape m)
  have hfinite2 := (Khachiyan.Cone.isConvexBody_cut hm).maxEllipsoidVolume_lt_top
  have hvolume := congrArg ENNReal.ofReal heq
  rw [ENNReal.ofReal_toReal hfinite1.ne, ENNReal.ofReal_toReal hfinite2.ne] at hvolume
  exact (Khachiyan.isMaxDet_iff_attains_volume hp).mpr hvolume

/-- Exact actual-volume reference branch in dimension one, with the paper's halfspace orientation. -/
theorem one_dimensional_reference {K : Set (V 1)} (hK : IsConvexBody K) {v : V 1} (hv : v ≠ 0) :
    maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v) = ENNReal.ofReal (1/2 : ℝ)*maxEllipsoidVolume K ∧
    (maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v)).toReal/(maxEllipsoidVolume K).toReal = 1/2 := by
  simpa only [sharpRatio_one] using ⟨center_cut_volume_eq_one hK hv, center_cut_volume_ratio_eq_one hK hv⟩

end SharpCut.Sharpness
