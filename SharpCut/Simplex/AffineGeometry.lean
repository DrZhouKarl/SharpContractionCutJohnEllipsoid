import SharpCut.Simplex.OrthogonalTransport

/-! # The actual John ellipsoid of an arbitrary affine simplex

Every vertex may vary subject only to affine independence. The certified
regular simplex is mapped to their full convex hull by an explicit affine
map. A general left polar factor and normalized competing ellipsoids prove
actual maximality, then uniqueness identifies the canonical John parameters.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
open Matrix Set MeasureTheory
namespace SharpCut.Simplex
open Certificate
variable {m : ℕ}

def interpolationAffine (p : Fin (m+2) → V (m+1)) : V (m+1) →ᵃ[ℝ] V (m+1) :=
  { toFun := fun x => centroid p+Matrix.toEuclideanCLM (𝕜 := ℝ) (interpolationMatrix p) x
    linear := (Matrix.toEuclideanCLM (𝕜 := ℝ) (interpolationMatrix p)).toLinearMap
    map_vadd' := by
      intro x y
      change centroid p+Matrix.toEuclideanCLM (𝕜 := ℝ) (interpolationMatrix p) (y+x) =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (interpolationMatrix p) y+
          (centroid p+Matrix.toEuclideanCLM (𝕜 := ℝ) (interpolationMatrix p) x)
      rw [map_add]
      abel }

theorem interpolationAffine_vertex (p : Fin (m+2) → V (m+1)) (i : Fin (m+2)) :
    interpolationAffine p (vertex m i) = p i := by
  change centroid p+Matrix.toEuclideanCLM (𝕜 := ℝ) (interpolationMatrix p) (vertex m i) = p i
  rw [interpolation_vertex,centered]
  abel

theorem affine_image_body (p : Fin (m+2) → V (m+1)) :
    interpolationAffine p '' body m = convexHull ℝ (Set.range p) := by
  rw [body_eq_vertex_hull,AffineMap.image_convexHull]
  have he : interpolationAffine p '' Set.range (vertex m) = Set.range p := by
    ext x
    constructor
    · rintro ⟨y,⟨i,rfl⟩,hy⟩
      rw [interpolationAffine_vertex] at hy
      exact ⟨i,hy⟩
    · rintro ⟨i,rfl⟩
      exact ⟨vertex m i,⟨i,rfl⟩,interpolationAffine_vertex p i⟩
  rw [he]

theorem normalized_affine_body (p : Fin (m+2) → V (m+1)) :
    Khachiyan.normalizedBody (interpolationAffine p '' body m) (centroid p) (Khachiyan.affineShape (interpolationMatrix p)) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (shapeRotation (interpolationMatrix p)) '' body m := by
  rw [Khachiyan.normalizedBody,Set.image_image]
  congr 1
  funext x
  simp only [Khachiyan.normalizePoint,interpolationAffine,AffineMap.coe_mk,
    add_sub_cancel_left,shapeRotation,matrix_action_mul]

theorem affine_simplex_normalized (p : Fin (m+2) → V (m+1)) (hp : AffineIndependent ℝ p) :
    IsJohnNormalized (Khachiyan.normalizedBody (convexHull ℝ (Set.range p)) (centroid p)
      (Khachiyan.affineShape (interpolationMatrix p))) := by
  rw [← affine_image_body p,normalized_affine_body]
  exact orthogonal_john_normalized (regularFrame m) _ (shapeRotation_orthogonal _ (interpolation_det_isUnit p hp)).2

theorem affine_simplex_feasible (p : Fin (m+2) → V (m+1)) (hp : AffineIndependent ℝ p) :
    IsFeasible (convexHull ℝ (Set.range p)) (centroid p) (Khachiyan.affineShape (interpolationMatrix p)) := by
  refine ⟨Khachiyan.affineShape_posDef (interpolation_det_isUnit p hp),?_⟩
  rw [← affine_image_body p,← Khachiyan.affine_image_unitBall_eq_ellipsoid]
  exact Set.image_mono (regularFrame m).unitBall_subset_polytope

/-- Compare with every actual feasible ellipse, through positive symmetric normalized shapes. -/
theorem affine_simplex_isMaxDet (p : Fin (m+2) → V (m+1)) (hp : AffineIndependent ℝ p) :
    IsMaxDet (convexHull ℝ (Set.range p)) (centroid p) (Khachiyan.affineShape (interpolationMatrix p)) := by
  have hS := Khachiyan.affineShape_posDef (interpolation_det_isUnit p hp)
  have hJ := affine_simplex_normalized p hp
  refine ⟨affine_simplex_feasible p hp,?_⟩
  intro a A hA
  have hnormalized := hA.normalize (centroid p) hS
  have hdet := hJ.det_le _ _ hnormalized
  rw [Matrix.det_one,Khachiyan.normalized_shape_det hS hA.1] at hdet
  simpa only [one_mul] using (div_le_iff₀ hS.det_pos).mp hdet

theorem affine_simplex_isConvexBody (p : Fin (m+2) → V (m+1)) (hp : AffineIndependent ℝ p) :
    IsConvexBody (convexHull ℝ (Set.range p)) := by
  have hcompact : IsCompact (convexHull ℝ (Set.range p)) := by
    rw [← affine_image_body p]
    apply (body_isConvexBody m).1.image
    change Continuous (fun x : V (m+1) => centroid p+Matrix.toEuclideanCLM (𝕜 := ℝ) (interpolationMatrix p) x)
    fun_prop
  have hconvex : Convex ℝ (convexHull ℝ (Set.range p)) := convex_convexHull ℝ _
  exact ⟨hcompact,hconvex,⟨centroid p,(affine_simplex_isMaxDet p hp).center_mem_interior⟩⟩

theorem affine_simplex_shape_square (p : Fin (m+2) → V (m+1)) :
    (Khachiyan.affineShape (interpolationMatrix p))^2 =
      (1/frameScale m) • (∑ i, outer (p i-centroid p)) := by
  have he : (∑ i, outer (p i-centroid p)) = frameScale m •
      (interpolationMatrix p*(interpolationMatrix p)ᵀ) := centered_covariance p
  rw [he,smul_smul,one_div,inv_mul_cancel₀ (frameScale_pos m).ne',one_smul]
  exact affineShape_square _

/-- Canonical actual John center and shape; the squared covariance formula is the original manuscript formula. -/
theorem affine_simplex_john_parameters (p : Fin (m+2) → V (m+1)) (hp : AffineIndependent ℝ p) :
    IsConvexBody (convexHull ℝ (Set.range p)) ∧
    Khachiyan.johnCenter (convexHull ℝ (Set.range p)) = centroid p ∧
    Khachiyan.johnShape (convexHull ℝ (Set.range p)) = Khachiyan.affineShape (interpolationMatrix p) ∧
    (Khachiyan.johnShape (convexHull ℝ (Set.range p))).PosDef ∧
    (Khachiyan.johnShape (convexHull ℝ (Set.range p)))^2 =
      (1/frameScale m) • (∑ i, outer (p i-centroid p)) ∧
    IsMaxDet (convexHull ℝ (Set.range p)) (centroid p) (Khachiyan.johnShape (convexHull ℝ (Set.range p))) := by
  have hK := affine_simplex_isConvexBody p hp
  have hmax := affine_simplex_isMaxDet p hp
  have hc := Khachiyan.johnCenter_eq_of_isMaxDet hK hmax
  have hA := Khachiyan.johnShape_eq_of_isMaxDet hK hmax
  refine ⟨hK,hc,hA,?_,?_,?_⟩
  · rw [hA]
    exact hmax.posDef
  · rw [hA]
    exact affine_simplex_shape_square p
  · rwa [hA]

/-- Every vertex of every full-dimensional affine simplex may vary; all positive dimensions are covered. -/
theorem affine_simplex_shape_formula (n : ℕ) (hn : 1 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    ∀ p : Fin (n+1) → V n, AffineIndependent ℝ p →
      let K := convexHull ℝ (Set.range p)
      let c := (1/((n : ℝ)+1)) • (∑ i, p i)
      IsConvexBody K ∧ Khachiyan.johnCenter K = c ∧ (Khachiyan.johnShape K).PosDef ∧
      (Khachiyan.johnShape K)^2 = (1/((n : ℝ)*((n : ℝ)+1))) • (∑ i, outer (p i-c)) ∧
      IsMaxDet K c (Khachiyan.johnShape K) := by
  cases n with
  | zero => omega
  | succ m =>
    intro p hp
    have h := affine_simplex_john_parameters p hp
    exact ⟨h.1,by simpa only [centroid,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h.2.1,
      h.2.2.2.1,by simpa only [frameScale,centroid,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h.2.2.2.2.1,
      by simpa only [centroid,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h.2.2.2.2.2⟩

end SharpCut.Simplex
