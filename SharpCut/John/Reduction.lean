import SharpCut.John.Necessity
import SharpCut.FiniteReduction

/-! # Complete finite contact reduction with the actual maximal-volume functional -/

noncomputable section
open scoped ENNReal RealInnerProductSpace
open MeasureTheory
namespace SharpCut.Geometry
variable {n : ℕ}

theorem normalized_volume [NeZero n] {K : Set (V n)} (h : IsJohnNormalized K) :
    maxEllipsoidVolume K = volume (unitBall n) := by
  have he := h.maxEllipsoidVolume_eq_det
  simpa only [Matrix.det_one, ENNReal.ofReal_one, one_mul] using he

theorem normalized_cut_body (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (h : IsJohnNormalized K) (v : V n) (hv : ‖v‖ = 1) :
    IsConvexBody (K ∩ centralHalfspace 0 v) := by
  letI : NeZero n := ⟨by omega⟩
  have hv0 : v ≠ 0 := by intro hz; simp [hz] at hv
  have hc := Khachiyan.johnCenter_eq_of_isMaxDet hK h
  have hcut := Khachiyan.john_center_cut_isConvexBody hK (neg_ne_zero.mpr hv0)
  rw [hc] at hcut
  rw [centralHalfspace_eq_legacy]
  exact hcut

/-- Lemma 2.5 for each specified supporting positive-weight John frame. -/
theorem contact_reduction (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (h : IsJohnNormalized K) {N : ℕ} (F : JohnFrame n N) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) :
    IsConvexBody F.polytope ∧ K ⊆ F.polytope ∧ IsJohnNormalized F.polytope ∧
      maxEllipsoidVolume F.polytope = maxEllipsoidVolume K ∧
      maxEllipsoidVolume K = volume (unitBall n) ∧
      IsConvexBody (K ∩ centralHalfspace 0 v) ∧
      IsConvexBody (F.polytope ∩ centralHalfspace 0 v) ∧
      maxEllipsoidVolume (K ∩ centralHalfspace 0 v) ≤
        maxEllipsoidVolume (F.polytope ∩ centralHalfspace 0 v) := by
  letI : NeZero n := ⟨by omega⟩
  have hP := F.polytope_isConvexBody
  have hPJ := F.polytope_isJohnNormalized
  refine ⟨hP, F.supporting_subset hs, hPJ, ?_, normalized_volume h,
    normalized_cut_body hn hK h v hv, normalized_cut_body hn hP hPJ v hv,
    F.cut_volume_comparison hs v⟩
  rw [normalized_volume hPJ, normalized_volume h]

/-- The reduction is available for every normalized convex body, with no frame assumed. -/
theorem exists_contact_reduction (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (h : IsJohnNormalized K) (v : V n) (hv : ‖v‖ = 1) :
    ∃ N : ℕ, ∃ F : JohnFrame n N, F.Supports K ∧
      IsConvexBody F.polytope ∧ K ⊆ F.polytope ∧ IsJohnNormalized F.polytope ∧
      maxEllipsoidVolume F.polytope = maxEllipsoidVolume K ∧
      maxEllipsoidVolume K = volume (unitBall n) ∧
      IsConvexBody (K ∩ centralHalfspace 0 v) ∧
      IsConvexBody (F.polytope ∩ centralHalfspace 0 v) ∧
      maxEllipsoidVolume (K ∩ centralHalfspace 0 v) ≤
        maxEllipsoidVolume (F.polytope ∩ centralHalfspace 0 v) := by
  obtain ⟨N, F, hs⟩ := John.exists_supporting_frame hn hK h
  exact ⟨N, F, hs, contact_reduction hn hK h F hs v hv⟩

end SharpCut.Geometry
