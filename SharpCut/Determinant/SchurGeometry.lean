import SharpCut.Certificate.ModelDeterminant
import SharpCut.Certificate.Factorization

/-!
# Positive axial and Schur-complement identities

All vectors carry the Euclidean norm. These identities apply to arbitrary
positive-definite matrices, without an assumed determinant lower bound.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
variable {n : ℕ}

def axisMoment (B : MatR n) (v : V n) : ℝ :=
  ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) B v⟫

def inverseAxisMoment (B : MatR n) (v : V n) : ℝ := axisMoment B⁻¹ v

theorem axisMoment_smul (B : MatR n) (r : ℝ) (v : V n) :
    axisMoment B (r • v) = r^2*axisMoment B v := by
  simp only [axisMoment, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem unit_coordinate_ne_zero (v : V n) (hv : ‖v‖ = 1) : v.ofLp ≠ 0 := by
  intro h
  have hz : v = 0 := WithLp.ofLp_injective 2 h
  simpa [hz] using hv

theorem axisMoment_pos (B : MatR n) (hB : B.PosDef) (v : V n) (hv : ‖v‖ = 1) :
    0 < axisMoment B v := by
  simpa only [axisMoment, Khachiyan.inner_matrix_action, star_trivial] using
    hB.dotProduct_mulVec_pos (unit_coordinate_ne_zero v hv)

theorem inverseAxisMoment_pos (B : MatR n) (hB : B.PosDef) (v : V n) (hv : ‖v‖ = 1) :
    0 < inverseAxisMoment B v := axisMoment_pos B⁻¹ hB.inv v hv

theorem inverse_axis_cauchy (B : MatR n) (hB : B.PosDef) (v : V n) (hv : ‖v‖ = 1) :
    1 ≤ axisMoment B v*inverseAxisMoment B v := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB.det_pos.ne'
  have he : B*ᵥ (B⁻¹*ᵥ v.ofLp) = v.ofLp := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hu, Matrix.one_mulVec]
  have hvv : v.ofLp ⬝ᵥ v.ofLp = 1 := by
    rw [← Khachiyan.inner_eq_dotProduct, real_inner_self_eq_norm_sq, hv, one_pow]
  have h := hB.star_dotProduct_mulVec_mul_le v.ofLp (B⁻¹*ᵥv.ofLp)
  simp only [star_trivial, he, hvv, one_mul] at h
  rw [dotProduct_comm (B⁻¹*ᵥv.ofLp) v.ofLp] at h
  simpa only [axisMoment, inverseAxisMoment, Khachiyan.inner_matrix_action] using h

theorem det_posDef_rank_one (B : MatR n) (hB : B.PosDef) (v : V n) (r : ℝ) :
    (B+r • outer v).det = B.det*(1+r*inverseAxisMoment B v) := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB.det_pos.ne'
  let w : V n := Matrix.toEuclideanCLM (𝕜 := ℝ) B⁻¹ v
  have hw : Matrix.toEuclideanCLM (𝕜 := ℝ) B w = v := by
    apply WithLp.ofLp_injective 2
    simp only [w, Khachiyan.matrix_action_ofLp, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv B hu, Matrix.one_mulVec]
  have he : B+r • outer v = B*(1+Certificate.cross (r • w) v) := by
    rw [Matrix.mul_add, Matrix.mul_one, Certificate.cross_smul_left,
      Matrix.mul_smul, Certificate.mul_cross, hw, Certificate.cross_self]
  rw [he, Matrix.det_mul]
  change B.det*(1+Matrix.vecMulVec (r • w).ofLp v.ofLp).det = _
  rw [Certificate.det_one_add_cross, real_inner_smul_right]
  rfl

def borderedMatrix (B : MatR n) (w : V n) (c : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks B (Matrix.replicateCol Unit w.ofLp)
    (Matrix.replicateRow Unit w.ofLp) (c • (1 : Matrix Unit Unit ℝ))

theorem borderedMatrix_det (B : MatR n) (hB : B.PosDef) (w : V n) (c : ℝ) :
    (borderedMatrix B w c).det = B.det*(c-axisMoment B⁻¹ w) := by
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B
    (isUnit_iff_ne_zero.mpr hB.det_pos.ne')
  rw [borderedMatrix, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  congr 1
  rw [Matrix.det_unique]
  rw [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, Matrix.replicateRow_mul_replicateCol_apply,
    axisMoment, Khachiyan.inner_matrix_action]

theorem posDef_inverse_action (B : MatR n) (hB : B.PosDef) (v : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) B⁻¹
      (Matrix.toEuclideanCLM (𝕜 := ℝ) B v) = v := by
  apply WithLp.ofLp_injective 2
  simp only [Khachiyan.matrix_action_ofLp, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB.det_pos.ne'), Matrix.one_mulVec]

theorem posDef_action_inverse (B : MatR n) (hB : B.PosDef) (v : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) B
      (Matrix.toEuclideanCLM (𝕜 := ℝ) B⁻¹ v) = v := by
  apply WithLp.ofLp_injective 2
  simp only [Khachiyan.matrix_action_ofLp, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB.det_pos.ne'), Matrix.one_mulVec]

theorem inverse_axial_combination (B : MatR n) (hB : B.PosDef) (v : V n)
    (hv : ‖v‖ = 1) (a t : ℝ) :
    axisMoment B⁻¹ (a • Matrix.toEuclideanCLM (𝕜 := ℝ) B v-t • v) =
      a^2*axisMoment B v-2*a*t+t^2*inverseAxisMoment B v := by
  have he : Matrix.toEuclideanCLM (𝕜 := ℝ) B⁻¹
      (a • Matrix.toEuclideanCLM (𝕜 := ℝ) B v-t • v) =
      a • v-t • Matrix.toEuclideanCLM (𝕜 := ℝ) B⁻¹ v := by
    rw [map_sub, map_smul, map_smul, posDef_inverse_action B hB]
  have hc : ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) B v,
      Matrix.toEuclideanCLM (𝕜 := ℝ) B⁻¹ v⟫ = 1 := by
    rw [← Khachiyan.inner_matrix_action_symm hB.isHermitian.isSymm,
      posDef_action_inverse B hB, real_inner_self_eq_norm_sq, hv, one_pow]
  simp only [inverseAxisMoment, axisMoment]
  rw [he]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hc, real_inner_self_eq_norm_sq, hv, one_pow,
    real_inner_comm (Matrix.toEuclideanCLM (𝕜 := ℝ) B v) v]
  ring

end SharpCut.Determinant
