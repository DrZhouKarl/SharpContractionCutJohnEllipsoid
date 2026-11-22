import SharpCut.Certificate.FrameBound
import SharpCut.Certificate.Feasibility
import SharpCut.John.Reduction
import SharpCut.OneDimensional

/-! # The actual sharp central-cut volume upper bound in every positive dimension -/

noncomputable section
open scoped ENNReal RealInnerProductSpace BigOperators
open Matrix Set MeasureTheory
namespace SharpCut.Geometry
variable {n : ℕ}

theorem centralHalfspace_pos_smul (c v : V n) (r : ℝ) (hr : 0 < r) :
    centralHalfspace c (r • v) = centralHalfspace c v := by
  ext x
  simp only [mem_centralHalfspace, real_inner_smul_left]
  constructor
  · intro h
    by_contra hn
    have hp : 0 < ⟪v, x-c⟫ := lt_of_not_ge hn
    have hm := mul_pos hr hp
    linarith
  · intro h
    simpa only [mul_zero] using mul_le_mul_of_nonneg_left h hr.le

def unitNormal (v : V n) : V n := ‖v‖⁻¹ • v

theorem unitNormal_norm (v : V n) (hv : v ≠ 0) : ‖unitNormal v‖ = 1 := by
  have hp := norm_pos_iff.mpr hv
  rw [unitNormal, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']

theorem unitNormal_halfspace (c v : V n) (hv : v ≠ 0) :
    centralHalfspace c (unitNormal v) = centralHalfspace c v :=
  centralHalfspace_pos_smul c v _ (inv_pos.mpr (norm_pos_iff.mpr hv))

theorem normalized_candidate_det_sharp (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (v : V n) (hv : ‖v‖ = 1)
    {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) : A.det ≤ sharpRatio n := by
  obtain ⟨N, F, hs⟩ := John.exists_supporting_frame (show 1 ≤ n by omega) hK hJ
  have hP : IsFeasible (F.polytope ∩ centralHalfspace 0 v) c A :=
    ⟨hA.1, fun x hx => ⟨F.supporting_subset hs (hA.2 hx).1, (hA.2 hx).2⟩⟩
  have hd := (Certificate.frame_volume_certificate F hn v hv hP).2
  have hp := Certificate.unrotatedQ_det_pos F hn v hv
  have hr := Determinant.normalizedCertificate_det_ge_one F hn v hv
  rw [Certificate.normalizedCertificate_det F hn v hv] at hr
  refine hd.trans ((div_le_iff₀ hp).mpr ?_)
  exact hr

theorem normalized_candidate_det_sharp_nonzero (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (v : V n) (hv : v ≠ 0)
    {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) : A.det ≤ sharpRatio n := by
  have hA' : IsFeasible (K ∩ centralHalfspace 0 (unitNormal v)) c A := by
    rwa [unitNormal_halfspace 0 v hv]
  exact normalized_candidate_det_sharp hn hK hJ _ (unitNormal_norm v hv) hA'

theorem normalized_paper_cut {S : MatR n} (hS : S.PosDef) (K : Set (V n)) (c v : V n) :
    Khachiyan.normalizedBody (K ∩ centralHalfspace c v) c S =
      Khachiyan.normalizedBody K c S ∩ centralHalfspace 0 (Matrix.toEuclideanCLM (𝕜 := ℝ) S v) := by
  rw [centralHalfspace_eq_legacy, Khachiyan.normalizedBody_cut hS, map_neg,
    ← centralHalfspace_eq_legacy]

theorem central_cut_candidate_det_sharp (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    {c v : V n} {S : MatR n} (hmax : IsMaxDet K c S) (hv : v ≠ 0)
    {a : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace c v) a A) :
    A.det ≤ sharpRatio n*S.det := by
  letI : NeZero n := ⟨by omega⟩
  have hnorm := hA.normalize c hmax.posDef
  rw [normalized_paper_cut hmax.posDef] at hnorm
  have hd := normalized_candidate_det_sharp_nonzero hn (hK.normalizedBody c hmax.posDef)
    hmax.isJohnNormalized _ (Khachiyan.normalized_normal_ne_zero hmax.posDef hv) hnorm
  rw [Khachiyan.normalized_shape_det hmax.posDef hA.1] at hd
  exact (div_le_iff₀ hmax.posDef.det_pos).mp hd

theorem central_cut_candidate_volume_sharp (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    {c v : V n} {S : MatR n} (hmax : IsMaxDet K c S) (hv : v ≠ 0)
    {a : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace c v) a A) :
    volume (ellipsoid a A) ≤ ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K := by
  letI : NeZero n := ⟨by omega⟩
  have hvolume : maxEllipsoidVolume K = ENNReal.ofReal S.det*volume (unitBall n) := hmax.maxEllipsoidVolume_eq_det
  calc
    _ = ENNReal.ofReal A.det*volume (unitBall n) := Khachiyan.volume_ellipsoid_eq_det hA.1 a
    _ ≤ ENNReal.ofReal (sharpRatio n*S.det)*volume (unitBall n) := by
      gcongr
      exact central_cut_candidate_det_sharp hn hK hmax hv hA
    _ = _ := by
      rw [ENNReal.ofReal_mul (sharpRatio_pos (show 1 ≤ n by omega)).le,
        hvolume, mul_assoc]

/-- The upper-bound half of Theorem 3.1, on actual convex bodies and maximal Lebesgue volume. -/
theorem sharp_center_cut_upper [NeZero n] (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    {v : V n} (hv : v ≠ 0) :
    IsConvexBody (K ∩ centralHalfspace (Khachiyan.johnCenter K) v) ∧
      maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v) ≤
        ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K := by
  letI : NeZero n := ⟨by omega⟩
  have hc := SharpCut.john_center_cut_isConvexBody hK hv
  refine ⟨hc, ?_⟩
  by_cases h1 : n = 1
  · subst n
    exact (center_cut_volume_eq_one hK hv).le
  · have hn2 : 2 ≤ n := by omega
    obtain ⟨a, A, hcutmax⟩ := Khachiyan.exists_isMaxDet hc
    have hvolume : maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v) =
        volume (ellipsoid a A) := hcutmax.maxEllipsoidVolume_eq
    rw [hvolume]
    exact central_cut_candidate_volume_sharp hn2 hK (Khachiyan.john_isMaxDet hK) hv hcutmax.feasible

theorem sharp_center_cut_upper_real [NeZero n] (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    {v : V n} (hv : v ≠ 0) :
    (maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v)).toReal ≤
      sharpRatio n*(maxEllipsoidVolume K).toReal := by
  have h := sharp_center_cut_upper hn hK hv
  have hl := h.1.maxEllipsoidVolume_lt_top
  have hr : ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.maxEllipsoidVolume_lt_top
  have hh := (ENNReal.toReal_le_toReal hl.ne hr.ne).mpr h.2
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sharpRatio_pos hn).le] using hh

theorem sharp_center_cut_ratio_upper [NeZero n] (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    {v : V n} (hv : v ≠ 0) :
    (maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v)).toReal/
      (maxEllipsoidVolume K).toReal ≤ sharpRatio n := by
  letI : NeZero n := ⟨by omega⟩
  apply (div_le_iff₀ (Khachiyan.john_isMaxDet hK).maxEllipsoidVolume_toReal_pos).mpr
  exact sharp_center_cut_upper_real hn hK hv

end SharpCut.Geometry
