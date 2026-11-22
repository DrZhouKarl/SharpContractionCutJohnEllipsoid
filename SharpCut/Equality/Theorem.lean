import SharpCut.Equality.Body

/-! # The complete general-body and contact-polytope equality classification -/

noncomputable section
open scoped RealInnerProductSpace ENNReal
open Matrix Set
namespace SharpCut.Equality
variable {n N : ℕ}

theorem model_isMaxDet_of_equality (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (v : V n) (hv : ‖v‖ = 1)
    (he : maxEllipsoidVolume (K ∩ centralHalfspace 0 v) = ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K) :
    IsMaxDet (K ∩ centralHalfspace 0 v) (Sharpness.modelCenter v) (Sharpness.modelShape v) := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨N, F, hs⟩ := John.exists_supporting_frame (show 1 ≤ n by omega) hK hJ
  obtain ⟨c, A, hcut⟩ := Khachiyan.exists_isMaxDet (Geometry.normalized_cut_body (show 1 ≤ n by omega) hK hJ v hv)
  have hp := extremal_parameters hn hK hJ F hs v hv he hcut
  rw [hp.2.1, hp.2.2] at hcut
  exact hcut

theorem newJohnEllipsoid_model [NeZero n] (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (v : V n) (hv : ‖v‖ = 1)
    (he : maxEllipsoidVolume (K ∩ centralHalfspace 0 v) = ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K) :
    Khachiyan.johnEllipsoid (K ∩ centralHalfspace 0 v) = modelEllipsoid v := by
  have hcut := Geometry.normalized_cut_body (show 1 ≤ n by omega) hK hJ v hv
  have hmax := model_isMaxDet_of_equality hn hK hJ v hv he
  rw [Khachiyan.johnEllipsoid, Khachiyan.johnCenter_eq_of_isMaxDet hcut hmax,
    Khachiyan.johnShape_eq_of_isMaxDet hcut hmax]
  rfl

theorem contact_polytope_equality (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    maxEllipsoidVolume (F.polytope ∩ centralHalfspace 0 v) = ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume F.polytope ↔
      ∀ i, F.contact i ∈ modelContactSet v := by
  constructor
  · intro he
    exact every_supporting_frame_model hn F.polytope_isConvexBody F.polytope_isJohnNormalized v hv he N F
      (fun i x hx => hx i)
  · intro hc
    have hh (i : Fin N) := (modelContactSet_iff (F.contact i) v (F.contact_unit i) hv).mp (hc i)
    have hfeas := Sharpness.model_feasible_contact_cut F hn v hv hh
    apply included_model_attains hn F.polytope_isConvexBody F.polytope_isJohnNormalized v hv
    exact hfeas.2.trans inter_subset_left

/-- Theorem 5.1, including the actual new John ellipsoid and the universal supporting-frame quantifier. -/
theorem equality_classification [NeZero n] (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (v : V n) (hv : ‖v‖ = 1) :
    (maxEllipsoidVolume (K ∩ centralHalfspace 0 v) = ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K ↔
      ∃ N : ℕ, ∃ F : JohnFrame n N, (∀ i, F.contact i ∈ modelContactSet v) ∧
        convexHull ℝ (unitBall n ∪ modelEllipsoid v) ⊆ K ∧ K ⊆ F.polytope) ∧
    (maxEllipsoidVolume (K ∩ centralHalfspace 0 v) = ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K →
      Khachiyan.johnEllipsoid (K ∩ centralHalfspace 0 v) = modelEllipsoid v) ∧
    (maxEllipsoidVolume (K ∩ centralHalfspace 0 v) = ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K →
      ∀ N : ℕ, ∀ F : JohnFrame n N, F.Supports K → ∀ i, F.contact i ∈ modelContactSet v) ∧
    (∀ N : ℕ, ∀ F : JohnFrame n N,
      maxEllipsoidVolume (F.polytope ∩ centralHalfspace 0 v) = ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume F.polytope ↔
        ∀ i, F.contact i ∈ modelContactSet v) :=
  ⟨equality_sandwich_iff hn hK hJ v hv, newJohnEllipsoid_model hn hK hJ v hv,
    every_supporting_frame_model hn hK hJ v hv, fun N F => contact_polytope_equality F hn v hv⟩

end SharpCut.Equality
