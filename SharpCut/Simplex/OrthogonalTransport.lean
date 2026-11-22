import SharpCut.Simplex.AffineAlgebra
import SharpCut.Optimization.GramContractions

/-! # Orthogonal John-frame transport and the general left polar factor

The linear map is only required to be invertible; its determinant may be
negative and it need not be symmetric. All multiplication orders are kept.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix Set
namespace SharpCut.Simplex
open Certificate Optimization
variable {m N : ℕ}

theorem orthogonal_inner (U : MatR (m+1)) (hU : Uᵀ*U = 1) (x y : V (m+1)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) U x,Matrix.toEuclideanCLM (𝕜 := ℝ) U y⟫ = ⟪x,y⟫ := by
  have h := Khachiyan.inner_transpose_action Uᵀ x (Matrix.toEuclideanCLM (𝕜 := ℝ) U y)
  rw [Matrix.transpose_transpose,← matrix_action_mul,hU,map_one,ContinuousLinearMap.one_apply] at h
  exact h

def orthogonalFrame (F : JohnFrame (m+1) N) (U : MatR (m+1)) (hU : Uᵀ*U = 1) : JohnFrame (m+1) N :=
  { contact := fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) U (F.contact i)
    weight := F.weight
    contact_unit := fun i => (euclidean_norm_of_orthogonal U hU (F.contact i)).trans (F.contact_unit i)
    weight_pos := F.weight_pos
    first_moment := by
      have h := congrArg (fun x : V (m+1) => Matrix.toEuclideanCLM (𝕜 := ℝ) U x) F.first_moment
      simpa only [map_sum,map_smul,map_zero] using h
    second_moment := by
      have he (i : Fin N) : F.weight i • outer (Matrix.toEuclideanCLM (𝕜 := ℝ) U (F.contact i)) =
          U*(F.weight i • outer (F.contact i))*Uᵀ := by
        rw [outer_linear_image,Matrix.mul_smul,Matrix.smul_mul]
      simp only [he,← Matrix.sum_mul,← Matrix.mul_sum,F.second_moment,Matrix.mul_one]
      exact mul_eq_one_comm.mp hU }

theorem orthogonal_polytope (F : JohnFrame (m+1) N) (U : MatR (m+1)) (hU : Uᵀ*U = 1) :
    (orthogonalFrame F U hU).polytope = Matrix.toEuclideanCLM (𝕜 := ℝ) U '' F.polytope := by
  have hUL : U*Uᵀ = 1 := mul_eq_one_comm.mp hU
  ext x
  constructor
  · intro hx
    let y := Matrix.toEuclideanCLM (𝕜 := ℝ) Uᵀ x
    have hy : y ∈ F.polytope := by
      intro i
      have he := Khachiyan.inner_transpose_action Uᵀ (F.contact i) x
      rw [Matrix.transpose_transpose] at he
      change ⟪F.contact i,Matrix.toEuclideanCLM (𝕜 := ℝ) Uᵀ x⟫ ≤ 1
      rw [← he]
      exact hx i
    refine ⟨y,hy,?_⟩
    dsimp only [y]
    rw [← matrix_action_mul,hUL,map_one,ContinuousLinearMap.one_apply]
  · rintro ⟨y,hy,rfl⟩
    intro i
    change ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) U (F.contact i),Matrix.toEuclideanCLM (𝕜 := ℝ) U y⟫ ≤ 1
    rw [orthogonal_inner U hU]
    exact hy i

theorem orthogonal_john_normalized (F : JohnFrame (m+1) N) (U : MatR (m+1)) (hU : Uᵀ*U = 1) :
    IsJohnNormalized (Matrix.toEuclideanCLM (𝕜 := ℝ) U '' F.polytope) := by
  rw [← orthogonal_polytope F U hU]
  exact (orthogonalFrame F U hU).polytope_isJohnNormalized

def shapeRotation (C : MatR (m+1)) : MatR (m+1) := (Khachiyan.affineShape C)⁻¹*C

theorem affineShape_square (C : MatR (m+1)) : (Khachiyan.affineShape C)^2 = C*Cᵀ := by
  have hG : (C*Cᵀ).PosSemidef := by
    simpa only [Matrix.transpose_transpose] using transpose_gram_posSemidef Cᵀ
  exact CFC.sq_sqrt _ hG.nonneg

theorem shapeRotation_orthogonal (C : MatR (m+1)) (hC : IsUnit C.det) :
    shapeRotation C*(shapeRotation C)ᵀ = 1 ∧ (shapeRotation C)ᵀ*shapeRotation C = 1 := by
  let S := Khachiyan.affineShape C
  have hS : S.PosDef := Khachiyan.affineShape_posDef hC
  have hs : S*S = C*Cᵀ := by simpa only [pow_two] using affineShape_square C
  have hdet : IsUnit S.det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hleft : shapeRotation C*(shapeRotation C)ᵀ = 1 := by
    calc
      _ = S⁻¹*(C*Cᵀ)*S⁻¹ := by
        change (S⁻¹*C)*(S⁻¹*C)ᵀ = S⁻¹*(C*Cᵀ)*S⁻¹
        simp only [Matrix.transpose_mul,hS.inv.isHermitian.isSymm.eq,Matrix.mul_assoc]
      _ = S⁻¹*(S*S)*S⁻¹ := by rw [hs]
      _ = 1 := by rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul S hdet,Matrix.one_mul,Matrix.mul_nonsing_inv S hdet]
  exact ⟨hleft,mul_eq_one_comm.mp hleft⟩

theorem shapeRotation_factor (C : MatR (m+1)) (hC : IsUnit C.det) :
    Khachiyan.affineShape C*shapeRotation C = C := by
  have hdet : IsUnit (Khachiyan.affineShape C).det := isUnit_iff_ne_zero.mpr (Khachiyan.affineShape_posDef hC).det_pos.ne'
  rw [shapeRotation,← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hdet,Matrix.one_mul]

end SharpCut.Simplex
