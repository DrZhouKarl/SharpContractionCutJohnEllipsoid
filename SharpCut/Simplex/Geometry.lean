import SharpCut.Simplex.Polytope
import SharpCut.Equality.Theorem

/-! # Actual regular simplex John geometry and sharp central-cut attainment -/

noncomputable section
open scoped RealInnerProductSpace BigOperators ENNReal
open Matrix Set MeasureTheory
namespace SharpCut.Simplex
open Certificate Sharpness Equality
variable {m : ℕ}

def cutNormal (m : ℕ) : V (m+1) := -normal m 0

theorem cutNormal_unit (m : ℕ) : ‖cutNormal m‖ = 1 := by rw [cutNormal,norm_neg,normal_unit]

theorem contact_heights (m : ℕ) (i : Fin (m+2)) :
    height (regularFrame m) (cutNormal m) i = -1 ∨ height (regularFrame m) (cutNormal m) i = inverseDimension (m+1) := by
  change ⟪normal m i,-normal m 0⟫ = -1 ∨ ⟪normal m i,-normal m 0⟫ = inverseDimension (m+1)
  by_cases hi : i = 0
  · subst i
    left
    rw [inner_neg_right,real_inner_self_eq_norm_sq,normal_unit,one_pow]
  · right
    rw [inner_neg_right,normal_gram m i 0 hi,neg_neg]

theorem original_john_ball (m : ℕ) : Khachiyan.johnEllipsoid (body m) = unitBall (m+1) := by
  rw [Khachiyan.johnEllipsoid,
    Khachiyan.johnCenter_eq_of_isMaxDet (body_isConvexBody m) (body_isJohnNormalized m),
    Khachiyan.johnShape_eq_of_isMaxDet (body_isConvexBody m) (body_isJohnNormalized m),Khachiyan.ellipsoid_zero_one]

theorem normal_frontier (m : ℕ) (i : Fin (m+2)) : normal m i ∈ frontier (body m) := by
  have hball : unitBall (m+1) ⊆ body m := (regularFrame m).unitBall_subset_polytope
  exact John.contact_mem_frontier hball ⟨normal_unit m i,fun _ hx => hx i⟩

/-- The exact new maximum-volume ellipse/ellipsoid and its physical optimum are attained on the regular simplex. -/
theorem regular_central_cut_geometry (hm : 1 ≤ m) :
    IsConvexBody (body m ∩ centralHalfspace 0 (cutNormal m)) ∧
    maxEllipsoidVolume (body m ∩ centralHalfspace 0 (cutNormal m)) =
      ENNReal.ofReal (sharpRatio (m+1))*maxEllipsoidVolume (body m) ∧
    IsMaxDet (body m ∩ centralHalfspace 0 (cutNormal m)) (modelCenter (cutNormal m)) (modelShape (cutNormal m)) ∧
    Khachiyan.johnEllipsoid (body m ∩ centralHalfspace 0 (cutNormal m)) = modelEllipsoid (cutNormal m) := by
  have hn : 2 ≤ m+1 := by omega
  have hunit := cutNormal_unit m
  have hc (i : Fin (m+2)) : normal m i ∈ modelContactSet (cutNormal m) :=
    (modelContactSet_iff _ _ (normal_unit m i) hunit).mpr (contact_heights m i)
  have he := (contact_polytope_equality (regularFrame m) hn (cutNormal m) hunit).mpr hc
  have hK := body_isConvexBody m
  have hJ := body_isJohnNormalized m
  exact ⟨Geometry.normalized_cut_body (by omega) hK hJ _ hunit,he,
    model_isMaxDet_of_equality hn hK hJ _ hunit he,newJohnEllipsoid_model hn hK hJ _ hunit he⟩

theorem regular_sharp_attainment (m : ℕ) :
    maxEllipsoidVolume (body m ∩ centralHalfspace 0 (cutNormal m)) =
      ENNReal.ofReal (sharpRatio (m+1))*maxEllipsoidVolume (body m) := by
  by_cases hm : m = 0
  · subst m
    have hv : cutNormal 0 ≠ 0 := by intro h; have hu := cutNormal_unit 0; simp [h] at hu
    have h := center_cut_volume_eq_one (body_isConvexBody 0) hv
    rw [Khachiyan.johnCenter_eq_of_isMaxDet (body_isConvexBody 0) (body_isJohnNormalized 0)] at h
    exact h
  · exact (regular_central_cut_geometry (by omega)).2.1

/-- Full-dimensional, affinely independent regular vertices and standard contact identities for every n>=1. -/
theorem exists_regular_simplex (n : ℕ) (hn : 1 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    ∃ u : Fin (n+1) → V n, ∃ p : Fin (n+1) → V n, ∃ K : Set (V n),
      (∀ i, ‖u i‖ = 1) ∧ (∀ i j, i ≠ j → ⟪u i,u j⟫ = -1/(n : ℝ)) ∧
      (∑ i, u i) = 0 ∧ (∑ i, outer (u i)) = (((n : ℝ)+1)/(n : ℝ)) • (1 : MatR n) ∧
      (∀ i, p i = -(n : ℝ) • u i) ∧ AffineIndependent ℝ p ∧ K = convexHull ℝ (Set.range p) ∧
      K = {x | ∀ i, ⟪u i,x⟫ ≤ 1} ∧
      IsConvexBody K ∧ IsJohnNormalized K ∧ Khachiyan.johnEllipsoid K = unitBall n ∧
      (∀ i, u i ∈ frontier K) ∧
      maxEllipsoidVolume (K ∩ centralHalfspace 0 (-u 0)) = ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K := by
  cases n with
  | zero => omega
  | succ m =>
    refine ⟨normal m,vertex m,body m,normal_unit m,?_,normal_sum m,?_,?_,vertices_affineIndependent m,
      body_eq_vertex_hull m,rfl,body_isConvexBody m,body_isJohnNormalized m,original_john_ball m,normal_frontier m,regular_sharp_attainment m⟩
    · intro i j hij
      simpa only [inverseDimension,Nat.cast_add,Nat.cast_one,neg_div] using normal_gram m i j hij
    · simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using normal_outer_sum m
    · intro i
      simp only [vertex,Nat.cast_add,Nat.cast_one]

end SharpCut.Simplex
