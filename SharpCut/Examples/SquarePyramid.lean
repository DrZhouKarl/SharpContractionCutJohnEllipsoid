import SharpCut.Sharpness.SignedFamily

/-! # The square-pyramid extremizer in the manuscript's x,y,z coordinates -/

noncomputable section
open scoped RealInnerProductSpace BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
open Matrix Set MeasureTheory
namespace SharpCut.Examples.SquarePyramid
open Certificate Sharpness Equality

def point (x y z : ℝ) : V 3 := WithLp.toLp 2 ![x,y,z]
def coordinateAxis (i : Fin 3) : V 3 := EuclideanSpace.single i (1 : ℝ)
def vertical : V 3 := coordinateAxis 2
def lateralBasis : Fin 4 → V 3 := ![coordinateAxis 0,-coordinateAxis 0,coordinateAxis 1,-coordinateAxis 1]

@[simp] theorem point_zero (x y z : ℝ) : point x y z 0 = x := rfl
@[simp] theorem point_one (x y z : ℝ) : point x y z 1 = y := rfl
@[simp] theorem point_two (x y z : ℝ) : point x y z 2 = z := rfl

theorem point_coordinates (p : V 3) : point (p 0) (p 1) (p 2) = p := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem axis_norm (i : Fin 3) : ‖coordinateAxis i‖ = 1 := by simp [coordinateAxis]
@[simp] theorem vertical_norm : ‖vertical‖ = 1 := axis_norm 2
@[simp] theorem axis_inner (i : Fin 3) (x : V 3) : ⟪coordinateAxis i,x⟫ = x i := by
  simp [coordinateAxis, EuclideanSpace.inner_single_left]

theorem lateral_unit (i : Fin 4) : ‖lateralBasis i‖ = 1 := by fin_cases i <;> simp [lateralBasis]
theorem lateral_perp (i : Fin 4) : ⟪vertical,lateralBasis i⟫ = 0 := by
  fin_cases i <;> simp [vertical, lateralBasis, axis_inner, coordinateAxis, EuclideanSpace.inner_single_left]

theorem lateral_balance : (∑ i : Fin 4, (1/2 : ℝ) • lateralBasis i) = 0 := by
  simp [Fin.sum_univ_succ, lateralBasis] <;> module

theorem lateral_isotropy : (∑ i : Fin 4, (1/2 : ℝ) • outer (lateralBasis i)) = projector vertical := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, lateralBasis, vertical, coordinateAxis, projector,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      Khachiyan.outer_apply, EuclideanSpace.single_apply]

def frame : JohnFrame 3 5 :=
  frameFromTransverse (by omega) vertical vertical_norm lateralBasis (fun _ => 1/2)
    lateral_unit (by intro i; norm_num) lateral_perp lateral_balance lateral_isotropy

theorem latitude_radius : familyRadius 3 = 2*Real.sqrt 2/3 := by
  have h := familyRadius_sq (by omega : 2 ≤ 3)
  norm_num [inverseDimension] at h
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hr : 0 ≤ familyRadius 3 := Real.sqrt_nonneg _
  nlinarith only [h, hs, hr, Real.sqrt_nonneg 2]

theorem contact_function : frame.contact = Fin.cases (-vertical)
    (fun i => (1/3 : ℝ) • vertical+(2*Real.sqrt 2/3) • lateralBasis i) := by
  funext i
  simp only [frame, frameFromTransverse, familyContact, latitude_radius]
  norm_num [inverseDimension]

theorem weight_function : frame.weight = Fin.cases (3/4 : ℝ) (fun _ => 9/16) := by
  funext i
  simp only [frame, frameFromTransverse, familyWeight]
  norm_num [inverseDimension]

theorem contact_array : frame.contact = ![point 0 0 (-1),point (2*Real.sqrt 2/3) 0 (1/3),
    point (-2*Real.sqrt 2/3) 0 (1/3),point 0 (2*Real.sqrt 2/3) (1/3),point 0 (-2*Real.sqrt 2/3) (1/3)] := by
  rw [contact_function]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cases_zero]
    ext k
    fin_cases k <;> norm_num [point,vertical,coordinateAxis,EuclideanSpace.single_apply]
  · rw [Fin.cases_succ]
    fin_cases j <;> ext k <;> fin_cases k <;>
      norm_num [lateralBasis,point,vertical,coordinateAxis,EuclideanSpace.single_apply,
        WithLp.ofLp_add,WithLp.ofLp_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] <;> ring

theorem inner_point (u : V 3) (x y z : ℝ) : ⟪u,point x y z⟫ = u 0*x+u 1*y+u 2*z := by
  rw [Khachiyan.inner_eq_dotProduct,dotProduct,Fin.sum_univ_three]
  rfl

theorem contact_heights (i : Fin 5) : height frame vertical i = -1 ∨ height frame vertical i = inverseDimension 3 := by
  rw [height, contact_function]
  refine Fin.cases ?_ (fun j => ?_) i
  · left
    simp [real_inner_self_eq_norm_sq]
  · right
    have hp : ⟪lateralBasis j,vertical⟫ = 0 := by simpa only [real_inner_comm] using lateral_perp j
    simp only [Fin.cases_succ, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      vertical_norm, one_pow, mul_one, hp, mul_zero, add_zero]
    norm_num [inverseDimension]

def body : Set (V 3) := {x | -1 ≤ x 2 ∧ 2*Real.sqrt 2*|x 0|+x 2 ≤ 3 ∧ 2*Real.sqrt 2*|x 1|+x 2 ≤ 3}
def cutBody : Set (V 3) := body ∩ {x | x 2 ≤ 0}

theorem two_sided_iff (a z t x : ℝ) (ha : 0 ≤ a) :
    (a*x+z ≤ t ∧ -a*x+z ≤ t) ↔ a*|x|+z ≤ t := by
  constructor
  · rintro ⟨h1,h2⟩
    have h : |a*x| ≤ t-z := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_mul, abs_of_nonneg ha] at h
    linarith only [h]
  · intro h
    have hab : |a*x| ≤ t-z := by rw [abs_mul, abs_of_nonneg ha]; linarith only [h]
    obtain ⟨h1,h2⟩ := abs_le.mp hab
    constructor <;> linarith

theorem raw_membership (x : V 3) : x ∈ frame.polytope ↔
    -x 2 ≤ 1 ∧ (1/3 : ℝ)*x 2+(2*Real.sqrt 2/3)*x 0 ≤ 1 ∧
    (1/3 : ℝ)*x 2-(2*Real.sqrt 2/3)*x 0 ≤ 1 ∧
    (1/3 : ℝ)*x 2+(2*Real.sqrt 2/3)*x 1 ≤ 1 ∧
    (1/3 : ℝ)*x 2-(2*Real.sqrt 2/3)*x 1 ≤ 1 := by
  change (∀ i, ⟪frame.contact i,x⟫ ≤ 1) ↔ _
  rw [contact_function]
  simp [Fin.forall_fin_succ, lateralBasis, vertical, axis_inner, inner_add_left,
    real_inner_smul_left, sub_eq_add_neg]

theorem polytope_eq_body : frame.polytope = body := by
  ext x
  rw [raw_membership]
  change _ ↔ -1 ≤ x 2 ∧ 2*Real.sqrt 2*|x 0|+x 2 ≤ 3 ∧ 2*Real.sqrt 2*|x 1|+x 2 ≤ 3
  have ha : 0 ≤ 2*Real.sqrt 2 := by positivity
  constructor
  · rintro ⟨hz,hxp,hxm,hyp,hym⟩
    refine ⟨by linarith, (two_sided_iff _ _ _ _ ha).mp ⟨?_,?_⟩, (two_sided_iff _ _ _ _ ha).mp ⟨?_,?_⟩⟩
    all_goals nlinarith only [hxp,hxm,hyp,hym]
  · rintro ⟨hz,hx,hy⟩
    have hxx := (two_sided_iff _ _ _ _ ha).mpr hx
    have hyy := (two_sided_iff _ _ _ _ ha).mpr hy
    refine ⟨by linarith, ?_,?_,?_,?_⟩
    all_goals nlinarith only [hxx.1,hxx.2,hyy.1,hyy.2]

theorem body_isConvexBody : IsConvexBody body := by rw [← polytope_eq_body]; exact frame.polytope_isConvexBody
theorem body_isJohnNormalized : IsJohnNormalized body := by rw [← polytope_eq_body]; exact frame.polytope_isJohnNormalized

theorem cut_eq_central : cutBody = body ∩ centralHalfspace 0 vertical := by
  ext x
  simp only [cutBody, Set.mem_inter_iff, Set.mem_setOf_eq, mem_centralHalfspace, sub_zero, vertical, axis_inner]

theorem cut_isConvexBody : IsConvexBody cutBody := by
  rw [cut_eq_central]
  exact Geometry.normalized_cut_body (by omega) body_isConvexBody body_isJohnNormalized vertical vertical_norm

theorem model_attainment :
    maxEllipsoidVolume cutBody = ENNReal.ofReal (sharpRatio 3)*maxEllipsoidVolume body ∧
    IsMaxDet cutBody (modelCenter vertical) (modelShape vertical) ∧
    Khachiyan.johnEllipsoid cutBody = Equality.modelEllipsoid vertical := by
  have hc (i : Fin 5) : frame.contact i ∈ modelContactSet vertical :=
    (modelContactSet_iff _ vertical (frame.contact_unit i) vertical_norm).mpr (contact_heights i)
  have he := (contact_polytope_equality frame (by omega) vertical vertical_norm).mpr hc
  rw [polytope_eq_body] at he
  have hm := model_isMaxDet_of_equality (by omega) body_isConvexBody body_isJohnNormalized vertical vertical_norm he
  have hj := newJohnEllipsoid_model (by omega) body_isConvexBody body_isJohnNormalized vertical vertical_norm he
  rw [← cut_eq_central] at he hm hj
  exact ⟨he,hm,hj⟩

def candidateCenter : V 3 := point 0 0 (-1/2)
def candidateShape : MatR 3 := Matrix.diagonal ![Real.sqrt (3/2),Real.sqrt (3/2),(1/2 : ℝ)]

theorem center_explicit : modelCenter vertical = candidateCenter := by
  ext i
  fin_cases i <;> norm_num [modelCenter, candidateCenter, point, vertical, coordinateAxis, EuclideanSpace.single_apply]

theorem transverse_semiaxis : (Real.sqrt (1-inverseDimension 3))⁻¹ = Real.sqrt (3/2) := by
  norm_num [inverseDimension]

theorem shape_explicit : modelShape vertical = candidateShape := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modelShape, candidateShape, transverse_semiaxis, projector, vertical, coordinateAxis,
      Matrix.diagonal_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Khachiyan.outer_apply, EuclideanSpace.single_apply]

theorem candidate_shape_det : candidateShape.det = (3/4 : ℝ) := by
  rw [candidateShape, Matrix.det_diagonal, Fin.prod_univ_three]
  change Real.sqrt (3/2 : ℝ)*Real.sqrt (3/2 : ℝ)*(1/2 : ℝ) = 3/4
  rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3/2)]
  norm_num

theorem sharpRatio_three : sharpRatio 3 = (3/4 : ℝ) := by
  have h := modelShape_det (by omega : 2 ≤ 3) vertical vertical_norm
  rw [shape_explicit, candidate_shape_det] at h
  exact h.symm

theorem original_john_ball : Khachiyan.johnEllipsoid body = unitBall 3 := by
  rw [Khachiyan.johnEllipsoid,
    Khachiyan.johnCenter_eq_of_isMaxDet body_isConvexBody body_isJohnNormalized,
    Khachiyan.johnShape_eq_of_isMaxDet body_isConvexBody body_isJohnNormalized,
    Khachiyan.ellipsoid_zero_one]

theorem new_john_parameters :
    Khachiyan.johnCenter cutBody = candidateCenter ∧ Khachiyan.johnShape cutBody = candidateShape ∧
      Khachiyan.johnEllipsoid cutBody = Khachiyan.ellipsoid candidateCenter candidateShape := by
  have hmax := model_attainment.2.1
  rw [Khachiyan.johnCenter_eq_of_isMaxDet cut_isConvexBody hmax,
    Khachiyan.johnShape_eq_of_isMaxDet cut_isConvexBody hmax, center_explicit, shape_explicit]
  have hj := model_attainment.2.2
  simpa only [Equality.modelEllipsoid, center_explicit, shape_explicit, true_and] using hj

theorem volume_ratio :
    maxEllipsoidVolume cutBody = ENNReal.ofReal (3/4 : ℝ)*maxEllipsoidVolume body ∧
    (maxEllipsoidVolume cutBody).toReal/(maxEllipsoidVolume body).toReal = (3/4 : ℝ) := by
  have hc := Khachiyan.johnCenter_eq_of_isMaxDet body_isConvexBody body_isJohnNormalized
  have he : maxEllipsoidVolume (body ∩ centralHalfspace (Khachiyan.johnCenter body) vertical) =
      ENNReal.ofReal (sharpRatio 3)*maxEllipsoidVolume body := by
    rw [hc, ← cut_eq_central]
    exact model_attainment.1
  have hr := Geometry.ratio_eq_of_attainment (by omega : 1 ≤ 3) body_isConvexBody he
  rw [hc, ← cut_eq_central, sharpRatio_three] at hr
  exact ⟨by simpa only [sharpRatio_three] using model_attainment.1,hr⟩

/-- The old ball touches all five actual defining facets at the stated unit contacts. -/
theorem original_facet_contacts (i : Fin 5) :
    frame.contact i ∈ unitBall 3 ∧ frame.contact i ∈ frontier body ∧ ⟪frame.contact i,frame.contact i⟫ = 1 := by
  have hball : unitBall 3 ⊆ body := by rw [← polytope_eq_body]; exact frame.unitBall_subset_polytope
  have hsupport : ∀ x ∈ body, ⟪frame.contact i,x⟫ ≤ 1 := by
    intro x hx
    rw [← polytope_eq_body] at hx
    exact hx i
  refine ⟨?_, John.contact_mem_frontier hball ⟨frame.contact_unit i,hsupport⟩, ?_⟩
  · rw [Khachiyan.mem_unitBall, frame.contact_unit i]
  · rw [real_inner_self_eq_norm_sq, frame.contact_unit i, one_pow]

/-- The new John ellipsoid touches every original facet and the new cut, with actual points in the retained body. -/
theorem new_facet_contacts :
    (∀ i : Fin 5, ∃ x ∈ Khachiyan.johnEllipsoid cutBody, x ∈ cutBody ∧ ⟪frame.contact i,x⟫ = 1) ∧
    (∃ x ∈ Khachiyan.johnEllipsoid cutBody, x ∈ cutBody ∧ x 2 = 0) := by
  have hA := modelShape_posDef (by omega : 2 ≤ 3) vertical vertical_norm
  have hj : Khachiyan.johnEllipsoid cutBody = Khachiyan.ellipsoid (modelCenter vertical) (modelShape vertical) :=
    model_attainment.2.2
  have hfeas := model_attainment.2.1.feasible
  constructor
  · intro i
    obtain ⟨x,hx,he⟩ := Khachiyan.ellipsoid_support_attained hA.isHermitian.isSymm (frame.contact i)
    have hs := model_support_height (by omega : 2 ≤ 3) vertical (frame.contact i) vertical_norm
      (frame.contact_unit i) (contact_heights i)
    exact ⟨x,by rw [hj]; exact hx,hfeas.2 hx,he.trans hs⟩
  · obtain ⟨x,hx,he⟩ := Khachiyan.ellipsoid_support_attained hA.isHermitian.isSymm vertical
    have hs := model_cut_support (by omega : 2 ≤ 3) vertical vertical_norm
    have hz : x 2 = 0 := by simpa only [vertical,axis_inner] using he.trans hs
    exact ⟨x,by rw [hj]; exact hx,hfeas.2 hx,hz⟩

end SharpCut.Examples.SquarePyramid
