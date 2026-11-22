import SharpCut.Equality.Parameters

/-! # Actual general-body equality and the convex-hull sandwich -/

noncomputable section
open scoped RealInnerProductSpace BigOperators ENNReal
open Matrix Set MeasureTheory
namespace SharpCut.Equality
open Certificate Gap
variable {n N : ℕ}

def modelEllipsoid (v : V n) : Set (V n) := ellipsoid (Sharpness.modelCenter v) (Sharpness.modelShape v)
def modelContactSet (v : V n) : Set (V n) :=
  {-v} ∪ {u | ‖u‖ = 1 ∧ ⟪u, v⟫ = inverseDimension n}

theorem modelContactSet_iff (u v : V n) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    u ∈ modelContactSet v ↔ ⟪u, v⟫ = -1 ∨ ⟪u, v⟫ = inverseDimension n := by
  simp only [modelContactSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro (h | h)
    · left; rw [h, inner_neg_left, real_inner_self_eq_norm_sq, hv, one_pow]
    · exact Or.inr h.2
  · rintro (h | h)
    · left
      have hs : ‖u+v‖^2 = 0 := by rw [norm_add_sq_real, hu, hv, h]; norm_num
      exact eq_neg_of_add_eq_zero_left (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))
    · exact Or.inr ⟨hu, h⟩

theorem modelEllipsoid_cut_subset (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    modelEllipsoid v ⊆ centralHalfspace 0 v := by
  intro x hx
  have h := Khachiyan.ellipsoid_support_le (v := v) (Sharpness.modelShape_posDef hn v hv).isHermitian.isSymm hx
  rw [Sharpness.model_cut_support hn v hv] at h
  simpa only [mem_centralHalfspace, sub_zero] using h

theorem extremal_parameters (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K) (hJ : IsJohnNormalized K)
    (F : JohnFrame n N) (hs : F.Supports K) (v : V n) (hv : ‖v‖ = 1)
    (he : maxEllipsoidVolume (K ∩ centralHalfspace 0 v) = ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K)
    {c : V n} {A : MatR n} (hcut : IsMaxDet (K ∩ centralHalfspace 0 v) c A) :
    (∀ i, F.contact i ∈ modelContactSet v) ∧ A = Sharpness.modelShape v ∧ c = Sharpness.modelCenter v := by
  letI : NeZero n := ⟨by omega⟩
  have hcenter := Khachiyan.johnCenter_eq_of_isMaxDet hK hJ
  have hvol : maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v) =
      ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K := by rwa [hcenter]
  have hr := Geometry.ratio_eq_of_attainment (show 1 ≤ n by omega) hK hvol
  rw [hcenter] at hr
  have hvc : maxEllipsoidVolume (K ∩ centralHalfspace 0 v) = volume (ellipsoid c A) := hcut.maxEllipsoidVolume_eq
  have ha : (maxEllipsoidVolume (K ∩ centralHalfspace 0 v)).toReal/(maxEllipsoidVolume K).toReal = A.det := by
    have h := Khachiyan.volume_ellipsoid_real_ratio (a := c) hJ hcut.posDef
    rw [← hvc, Matrix.det_one, div_one] at h
    exact h
  have hdet : A.det = sharpRatio n := ha.symm.trans hr
  have hz : volumeDeficit n A = 0 := by
    rw [volumeDeficit, hdet, div_self (sharpRatio_pos (show 1 ≤ n by omega)).ne', Real.log_one]
  have hp := zero_deficit_parameters hn hK hJ F hs v hv hcut.feasible hz
  exact ⟨fun i => (modelContactSet_iff _ v (F.contact_unit i) hv).mpr (hp.1 i), hp.2.1, hp.2.2⟩

theorem included_model_attains (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (v : V n) (hv : ‖v‖ = 1) (hin : modelEllipsoid v ⊆ K) :
    maxEllipsoidVolume (K ∩ centralHalfspace 0 v) = ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K := by
  letI : NeZero n := ⟨by omega⟩
  have hc : IsFeasible (K ∩ centralHalfspace 0 v) (Sharpness.modelCenter v) (Sharpness.modelShape v) :=
    ⟨Sharpness.modelShape_posDef hn v hv, fun x hx => ⟨hin hx, modelEllipsoid_cut_subset hn v hv hx⟩⟩
  have hl : volume (modelEllipsoid v) ≤ maxEllipsoidVolume (K ∩ centralHalfspace 0 v) :=
    Khachiyan.volume_le_maxEllipsoidVolume hc
  have hb : maxEllipsoidVolume K = volume (unitBall n) := Geometry.normalized_volume hJ
  have hm : volume (modelEllipsoid v) = ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K := by
    rw [modelEllipsoid, Khachiyan.volume_ellipsoid_eq_det (Sharpness.modelShape_posDef hn v hv),
      Sharpness.modelShape_det hn v hv, hb]
  rw [hm] at hl
  have hv0 : v ≠ 0 := by intro h; simpa [h] using hv
  have hu := (Geometry.sharp_center_cut_upper (show 1 ≤ n by omega) hK hv0).2
  rw [Khachiyan.johnCenter_eq_of_isMaxDet hK hJ] at hu
  exact le_antisymm hu hl

/-- The equivalence in Theorem 5.1, with the actual model ellipsoid inclusion. -/
theorem equality_sandwich_iff (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (v : V n) (hv : ‖v‖ = 1) :
    maxEllipsoidVolume (K ∩ centralHalfspace 0 v) = ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K ↔
      ∃ N : ℕ, ∃ F : JohnFrame n N, (∀ i, F.contact i ∈ modelContactSet v) ∧
        convexHull ℝ (unitBall n ∪ modelEllipsoid v) ⊆ K ∧ K ⊆ F.polytope := by
  letI : NeZero n := ⟨by omega⟩
  constructor
  · intro he
    obtain ⟨N, F, hs⟩ := John.exists_supporting_frame (show 1 ≤ n by omega) hK hJ
    have hbody := Geometry.normalized_cut_body (show 1 ≤ n by omega) hK hJ v hv
    obtain ⟨c, A, hcut⟩ := Khachiyan.exists_isMaxDet hbody
    have hp := extremal_parameters hn hK hJ F hs v hv he hcut
    have hin : modelEllipsoid v ⊆ K := by
      have hsub := hcut.subset.trans inter_subset_left
      rw [hp.2.1, hp.2.2] at hsub
      exact hsub
    exact ⟨N, F, hp.1, convexHull_min (Set.union_subset hJ.unitBall_subset hin) hK.2.1, F.supporting_subset hs⟩
  · rintro ⟨N, F, hF, hleft, hright⟩
    apply included_model_attains hn hK hJ v hv
    exact (subset_union_right).trans ((subset_convexHull ℝ _).trans hleft)

theorem every_supporting_frame_model (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (v : V n) (hv : ‖v‖ = 1)
    (he : maxEllipsoidVolume (K ∩ centralHalfspace 0 v) = ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K) :
    ∀ N : ℕ, ∀ F : JohnFrame n N, F.Supports K → ∀ i, F.contact i ∈ modelContactSet v := by
  letI : NeZero n := ⟨by omega⟩
  intro N F hs
  obtain ⟨c, A, hcut⟩ := Khachiyan.exists_isMaxDet (Geometry.normalized_cut_body (show 1 ≤ n by omega) hK hJ v hv)
  exact (extremal_parameters hn hK hJ F hs v hv he hcut).1

end SharpCut.Equality
