import SharpCut.Optimization.DeterminantExtrema
import SharpCut.Geometry.SharpTheorem

/-! # Instance dual maxima and the attained infimum over all John frames

Equation (7.11) uses genuine real suprema and infima of feasible determinant
values. Their extrema are attained; all physical volume denominators are
finite and strictly positive before cancellation.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
open Matrix Set MeasureTheory
namespace SharpCut.Applications
open Optimization Certificate
variable {n N : ℕ} [NeZero n]

def instanceDeterminant (F : JohnFrame n N) (v : V n) : ℝ :=
  dualDeterminantMaximum (cutNormals F v) (cutOffsets N)

theorem cut_normals_nonzero (F : JohnFrame n N) (v : V n) (hv : ‖v‖ = 1) :
    ∀ r, cutNormals F v r ≠ 0 := by
  intro r
  refine Fin.cases ?_ (fun i => ?_) r
  · intro hz
    have : v = 0 := hz
    simp [this] at hv
  · intro hz
    have : F.contact i = 0 := hz
    have h := F.contact_unit i
    simp [this] at h

theorem instance_dual_attained (hn : 1 ≤ n) (F : JohnFrame n N) (v : V n) (hv : ‖v‖ = 1) :
    ∃ α q, DualFeasible (cutNormals F v) (cutOffsets N) α q ∧
      IsGreatest (dualDeterminants (cutNormals F v) (cutOffsets N))
        (aggregate (cutNormals F v) q).det ∧
      instanceDeterminant F v = (aggregate (cutNormals F v) q).det := by
  have hP := Geometry.normalized_cut_body hn F.polytope_isConvexBody F.polytope_isJohnNormalized v hv
  rw [← cut_polytope] at hP
  obtain ⟨c, A, α, q, _, hd, hgreat, he, _⟩ :=
    dual_determinant_maximum_attained hn _ _ (cut_normals_nonzero F v hv) hP
  exact ⟨α, q, hd, hgreat, he⟩

theorem instance_volume_identity (hn : 1 ≤ n) (F : JohnFrame n N) (v : V n) (hv : ‖v‖ = 1) :
    0 < instanceDeterminant F v ∧
      (maxEllipsoidVolume (F.polytope ∩ centralHalfspace 0 v)).toReal / (volume (unitBall n)).toReal =
        (instanceDeterminant F v)⁻¹ := by
  have hP := Geometry.normalized_cut_body hn F.polytope_isConvexBody F.polytope_isJohnNormalized v hv
  rw [← cut_polytope] at hP
  have h := dual_maximum_volume_identity hn _ _ (cut_normals_nonzero F v hv) hP
  simpa only [cut_polytope, instanceDeterminant] using h

theorem instance_lower_bound (hn : 1 ≤ n) (F : JohnFrame n N) (v : V n) (hv : ‖v‖ = 1) :
    (sharpRatio n)⁻¹ ≤ instanceDeterminant F v := by
  have hc : Khachiyan.johnCenter F.polytope = 0 :=
    Khachiyan.johnCenter_eq_of_isMaxDet F.polytope_isConvexBody F.polytope_isJohnNormalized
  have hv0 : v ≠ 0 := by intro hz; simp [hz] at hv
  have hupper := Geometry.sharp_center_cut_ratio_upper hn F.polytope_isConvexBody hv0
  rw [hc, Geometry.normalized_volume F.polytope_isJohnNormalized,
    (instance_volume_identity hn F v hv).2] at hupper
  have hp := (instance_volume_identity hn F v hv).1
  have hmul := (div_le_iff₀ hp).mp (show 1 / instanceDeterminant F v ≤ sharpRatio n by
    simpa only [one_div] using hupper)
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (sharpRatio_pos hn)).mpr
  nlinarith only [hmul]

def frameDualMaxima (n : ℕ) [NeZero n] : Set ℝ :=
  {d | ∃ N : ℕ, ∃ F : JohnFrame n N, ∃ v : V n,
    ‖v‖ = 1 ∧ d = instanceDeterminant F v}

def frameDualInfimum (n : ℕ) [NeZero n] : ℝ := sInf (frameDualMaxima n)

theorem model_attains_dual_infimum (hn : 1 ≤ n) :
    ∃ N : ℕ, ∃ F : JohnFrame n N, ∃ v : V n,
      ‖v‖ = 1 ∧ instanceDeterminant F v = (sharpRatio n)⁻¹ := by
  obtain ⟨N, F, v, hv, he⟩ := Geometry.fixed_contact_attainment hn
  let u := Geometry.unitNormal v
  have hu : ‖u‖ = 1 := Geometry.unitNormal_norm v hv
  have hc : Khachiyan.johnCenter F.polytope = 0 :=
    Khachiyan.johnCenter_eq_of_isMaxDet F.polytope_isConvexBody F.polytope_isJohnNormalized
  have hr := Geometry.ratio_eq_of_attainment hn F.polytope_isConvexBody he
  rw [← Geometry.unitNormal_halfspace (Khachiyan.johnCenter F.polytope) v hv,
    hc, Geometry.normalized_volume F.polytope_isJohnNormalized] at hr
  have hi := (instance_volume_identity hn F u hu).2
  have hEq : (instanceDeterminant F u)⁻¹ = sharpRatio n := hi.symm.trans hr
  have hInv := congrArg (fun x : ℝ => x⁻¹) hEq
  exact ⟨N, F, u, hu, by simpa only [inv_inv] using hInv⟩

theorem frameDualMaxima_isLeast (hn : 1 ≤ n) :
    IsLeast (frameDualMaxima n) (sharpRatio n)⁻¹ := by
  obtain ⟨N, F, v, hv, he⟩ := model_attains_dual_infimum hn
  refine ⟨⟨N, F, v, hv, he.symm⟩, ?_⟩
  rintro d ⟨N, F, v, hv, rfl⟩
  exact instance_lower_bound hn F v hv

theorem frameDualInfimum_eq (hn : 1 ≤ n) : frameDualInfimum n = (sharpRatio n)⁻¹ :=
  (frameDualMaxima_isLeast hn).csInf_eq

theorem instance_fixed_weight_improvement (hn : 2 ≤ n) (F : JohnFrame n N) (v : V n) (hv : ‖v‖ = 1) :
    ∃ q, DualFeasible (cutNormals F v) (cutOffsets N) (cutAlpha F v) q ∧
      IsGreatest (fixedDualDeterminants (cutNormals F v) (cutOffsets N) (cutAlpha F v))
        (aggregate (cutNormals F v) q).det ∧
      fixedDualDeterminantMaximum (cutNormals F v) (cutOffsets N) (cutAlpha F v) =
        (aggregate (cutNormals F v) q).det ∧
      (unrotatedQ F v).det ≤ (aggregate (cutNormals F v) q).det ∧
      (aggregate (cutNormals F v) q).det ≤ instanceDeterminant F v := by
  have hseed := explicit_dual_feasible F hn v hv
  obtain ⟨q, hd, hgreat, he, hlow⟩ := fixed_dual_determinant_attained hseed
  rw [rotated_aggregate_eq_polar F hn v hv,
    polarMatrix_det (unrotatedQ_det_pos F hn v hv)] at hlow
  obtain ⟨α, q', _, hfull, hD⟩ := instance_dual_attained (by omega) F v hv
  refine ⟨q, hd, hgreat, he, hlow, ?_⟩
  rw [hD]
  exact hfull.2 ⟨cutAlpha F v, q, hd, rfl⟩

/-- All three exact determinant/volume identities of (7.11), with attained extrema. -/
theorem exact_instance_dual_characterization (hn : 1 ≤ n) (F : JohnFrame n N) (v : V n) (hv : ‖v‖ = 1) :
    0 < instanceDeterminant F v ∧
      (maxEllipsoidVolume (F.polytope ∩ centralHalfspace 0 v)).toReal / (volume (unitBall n)).toReal =
        (instanceDeterminant F v)⁻¹ ∧
      Geometry.optimalConstant n = (frameDualInfimum n)⁻¹ ∧
      frameDualInfimum n = (sharpRatio n)⁻¹ ∧
      IsLeast (frameDualMaxima n) (sharpRatio n)⁻¹ ∧
      (∃ α q, DualFeasible (cutNormals F v) (cutOffsets N) α q ∧
        instanceDeterminant F v = (aggregate (cutNormals F v) q).det) := by
  have hi := instance_volume_identity hn F v hv
  obtain ⟨α, q, hd, _, hD⟩ := instance_dual_attained hn F v hv
  refine ⟨hi.1, hi.2, ?_, frameDualInfimum_eq hn, frameDualMaxima_isLeast hn, ⟨α, q, hd, hD⟩⟩
  rw [Geometry.optimalConstant_eq hn, frameDualInfimum_eq hn, inv_inv]

end SharpCut.Applications
