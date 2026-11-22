import SharpCut.Simplex.Geometry
import SharpCut.Geometry.BallHalfVolume

/-! # The original model support values and every mathematical assertion of Figure 1 -/

noncomputable section
open scoped RealInnerProductSpace BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
open Matrix Set MeasureTheory
namespace SharpCut.Simplex
open Certificate Sharpness Equality
variable {n : ℕ}

theorem normal_zero (m : ℕ) : normal m 0 = -axis m := by
  cases m <;> simp [normal,regularFrame,baseFrame,baseContact,liftFrame,frameFromTransverse,familyContact]

theorem cutNormal_axis (m : ℕ) : cutNormal m = axis m := by rw [cutNormal,normal_zero,neg_neg]

theorem model_axis_support_values (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    ⟪v,modelCenter v⟫ = -1/2 ∧ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (modelShape v) v‖ = 1/2 ∧
    ⟪-v,modelCenter v⟫ = 1/2 ∧ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (modelShape v) (-v)‖ = 1/2 := by
  have hc : ⟪v,modelCenter v⟫ = -1/2 := by
    rw [modelCenter,real_inner_smul_right,real_inner_self_eq_norm_sq,hv,one_pow,mul_one]
  have ha : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (modelShape v) v‖ = 1/2 := by
    rw [modelShape_axis hn v hv,norm_smul,hv]
    norm_num
  refine ⟨hc,ha,?_,?_⟩
  · rw [inner_neg_left,hc]
    ring
  · rw [map_neg,norm_neg,ha]

theorem model_latitude_support_values (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (hheight : ⟪u,v⟫ = inverseDimension n) :
    ⟪u,modelCenter v⟫ = -inverseDimension n/2 ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (modelShape v) u‖ = 1+inverseDimension n/2 := by
  have hc : ⟪u,modelCenter v⟫ = -inverseDimension n/2 := by
    rw [modelCenter,real_inner_smul_right,hheight]
    ring
  have hs := model_support_height hn v u hv hu (Or.inr hheight)
  exact ⟨hc,by linarith only [hc,hs]⟩

theorem model_latitude_square_root (hn : 2 ≤ n) :
    Real.sqrt ((inverseDimension n)^2/4+(1-(inverseDimension n)^2)/(1-inverseDimension n)) = 1+inverseDimension n/2 := by
  have hb := inverseDimension_bounds hn
  have he : (inverseDimension n)^2/4+(1-(inverseDimension n)^2)/(1-inverseDimension n) = (1+inverseDimension n/2)^2 := by
    field_simp [show 1-inverseDimension n ≠ 0 by linarith only [hb.2]] <;> ring
  rw [he,Real.sqrt_sq_eq_abs,abs_of_pos (by linarith only [hb.1] : 0 < 1+inverseDimension n/2)]

theorem transverseScale_two : (Real.sqrt (1-inverseDimension 2))⁻¹ = Real.sqrt 2 := by norm_num [inverseDimension]

theorem modelShape_two : modelShape (axis 1) = Matrix.diagonal ![(1/2 : ℝ),Real.sqrt 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modelShape,transverseScale_two,projector,Khachiyan.outer_apply,
      axis,EuclideanSpace.single_apply,Matrix.diagonal_apply,Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.one_apply]

theorem sharpRatio_two : sharpRatio 2 = 1/Real.sqrt 2 := by
  have h := modelShape_det (by omega : 2 ≤ 2) (axis 1) (axis_norm 1)
  rw [modelShape_two,Matrix.det_diagonal,Fin.prod_univ_two] at h
  have he : (1/2 : ℝ)*Real.sqrt 2 = 1/Real.sqrt 2 := by
    have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hp : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    field_simp [hp]
    nlinarith only [hs]
  change (1/2 : ℝ)*Real.sqrt 2 = sharpRatio 2 at h
  exact h.symm.trans he

theorem model_outside_old_ball : ∃ x ∈ modelEllipsoid (axis 1), x ∉ unitBall 2 := by
  let w : V 2 := transverseBasis 1 0
  let x := modelCenter (axis 1)+Matrix.toEuclideanCLM (𝕜 := ℝ) (modelShape (axis 1)) w
  have hw : ‖w‖ = 1 := basis_norm 1 0
  have hperp : ⟪axis 1,w⟫ = 0 := axis_basis_orthogonal 1 0
  have hperpSym : ⟪w,axis 1⟫ = 0 := by rw [real_inner_comm]; exact hperp
  have hAw : Matrix.toEuclideanCLM (𝕜 := ℝ) (modelShape (axis 1)) w = Real.sqrt 2 • w := by
    rw [modelShape_action (by omega : 2 ≤ 2) (axis 1) w (axis_norm 1),hperp,mul_zero,zero_smul,zero_add,
      transverse,hperpSym,zero_smul,sub_zero,transverseScale_two]
  have hsq : ‖x‖^2 = (9/4 : ℝ) := by
    dsimp only [x]
    rw [hAw,modelCenter,norm_add_sq_real]
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,axis_norm,hw,one_pow,mul_one,
      real_inner_smul_left,real_inner_smul_right,hperp,mul_zero,zero_mul,add_zero,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  refine ⟨x,⟨w,(Khachiyan.mem_unitBall w).mpr hw.le,rfl⟩,?_⟩
  intro hx
  have hnorm := (Khachiyan.mem_unitBall x).mp hx
  nlinarith only [hsq,hnorm,norm_nonneg x]

/-- Full Figure 1: actual regular triangle, exact model ellipse and area ratio, ordinary half-ball volume, expansion outside the old ball. -/
theorem figure_one_geometry :
    IsConvexBody (body 1) ∧ AffineIndependent ℝ (vertex 1) ∧ Khachiyan.johnEllipsoid (body 1) = unitBall 2 ∧
    IsMaxDet (body 1 ∩ centralHalfspace 0 (axis 1)) (modelCenter (axis 1)) (Matrix.diagonal ![(1/2 : ℝ),Real.sqrt 2]) ∧
    maxEllipsoidVolume (body 1 ∩ centralHalfspace 0 (axis 1)) = ENNReal.ofReal (1/Real.sqrt 2)*maxEllipsoidVolume (body 1) ∧
    (maxEllipsoidVolume (body 1 ∩ centralHalfspace 0 (axis 1))).toReal/(maxEllipsoidVolume (body 1)).toReal = 1/Real.sqrt 2 ∧
    volume (unitBall 2 ∩ centralHalfspace 0 (axis 1)) = ENNReal.ofReal (1/2 : ℝ)*volume (unitBall 2) ∧
    (∃ x ∈ Khachiyan.johnEllipsoid (body 1 ∩ centralHalfspace 0 (axis 1)), x ∈ body 1 ∩ centralHalfspace 0 (axis 1) ∧ x ∉ unitBall 2) := by
  have hg := regular_central_cut_geometry (m := 1) (by omega)
  rw [cutNormal_axis] at hg
  have hc := Khachiyan.johnCenter_eq_of_isMaxDet (body_isConvexBody 1) (body_isJohnNormalized 1)
  have he : maxEllipsoidVolume (body 1 ∩ centralHalfspace (Khachiyan.johnCenter (body 1)) (axis 1)) =
      ENNReal.ofReal (sharpRatio 2)*maxEllipsoidVolume (body 1) := by rw [hc]; exact hg.2.1
  have hr := Geometry.ratio_eq_of_attainment (by omega : 1 ≤ 2) (body_isConvexBody 1) he
  rw [hc,sharpRatio_two] at hr
  refine ⟨body_isConvexBody 1,vertices_affineIndependent 1,original_john_ball 1,?_,?_,hr,
    Geometry.unit_ball_half_volume (axis 1) (axis_norm 1),?_⟩
  · simpa only [modelShape_two] using hg.2.2.1
  · simpa only [show (1+1 : ℕ) = 2 by norm_num,sharpRatio_two] using hg.2.1
  · obtain ⟨x,hx,hout⟩ := model_outside_old_ball
    exact ⟨x,by rw [hg.2.2.2]; exact hx,hg.2.2.1.feasible.2 hx,hout⟩

end SharpCut.Simplex
