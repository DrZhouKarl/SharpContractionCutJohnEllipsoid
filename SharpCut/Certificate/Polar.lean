import SharpCut.Certificate.Factorization

/-! # The common left polar factor and its actual Euclidean isometry -/

noncomputable section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Certificate
variable {n : ℕ}

def polarMatrix (Q : MatR n) : MatR n := CFC.sqrt (Q*Qᵀ)
def polarRotation (Q : MatR n) : MatR n := (polarMatrix Q)⁻¹*Q

theorem gram_posDef {Q : MatR n} (hQ : 0 < Q.det) : (Q*Qᵀ).PosDef := by
  have hu : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).mpr (isUnit_iff_ne_zero.mpr hQ.ne')
  have h := Matrix.PosDef.mul_conjTranspose_self Q (Matrix.vecMul_injective_iff_isUnit.mpr hu)
  have he : Qᴴ = Qᵀ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
  rwa [he] at h

theorem polarMatrix_posDef {Q : MatR n} (hQ : 0 < Q.det) : (polarMatrix Q).PosDef := by
  unfold polarMatrix
  rw [CFC.sqrt_eq_rpow]
  exact Khachiyan.Spectral.rpow_posDef (gram_posDef hQ) _

theorem polarMatrix_square {Q : MatR n} (hQ : 0 < Q.det) :
    polarMatrix Q*polarMatrix Q = Q*Qᵀ :=
  CFC.sqrt_mul_sqrt_self _ (gram_posDef hQ).posSemidef.nonneg

theorem polarRotation_left_orthogonal {Q : MatR n} (hQ : 0 < Q.det) :
    polarRotation Q*(polarRotation Q)ᵀ = 1 := by
  have hm := polarMatrix_posDef hQ
  have hinvsym : ((polarMatrix Q)⁻¹)ᵀ = (polarMatrix Q)⁻¹ := hm.inv.isHermitian.isSymm
  have hdet : IsUnit (polarMatrix Q).det := isUnit_iff_ne_zero.mpr hm.det_pos.ne'
  calc
    _ = (polarMatrix Q)⁻¹*(Q*Qᵀ)*(polarMatrix Q)⁻¹ := by
      simp only [polarRotation, Matrix.transpose_mul, hinvsym, Matrix.mul_assoc]
    _ = (polarMatrix Q)⁻¹*(polarMatrix Q*polarMatrix Q)*(polarMatrix Q)⁻¹ := by
      rw [polarMatrix_square hQ]
    _ = 1 := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul,
        Matrix.mul_nonsing_inv _ hdet]

theorem polarRotation_right_orthogonal {Q : MatR n} (hQ : 0 < Q.det) :
    (polarRotation Q)ᵀ*polarRotation Q = 1 :=
  mul_eq_one_comm.mp (polarRotation_left_orthogonal hQ)

theorem polarRotation_aggregate {Q : MatR n} (hQ : 0 < Q.det) :
    polarRotation Q*Qᵀ = polarMatrix Q := by
  have hdet : IsUnit (polarMatrix Q).det :=
    isUnit_iff_ne_zero.mpr (polarMatrix_posDef hQ).det_pos.ne'
  calc
    _ = (polarMatrix Q)⁻¹*(Q*Qᵀ) := by rw [polarRotation, Matrix.mul_assoc]
    _ = (polarMatrix Q)⁻¹*(polarMatrix Q*polarMatrix Q) := by rw [polarMatrix_square hQ]
    _ = _ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

theorem polarMatrix_det {Q : MatR n} (hQ : 0 < Q.det) : (polarMatrix Q).det = Q.det := by
  have h := congrArg Matrix.det (polarMatrix_square hQ)
  simp only [Matrix.det_mul, Matrix.det_transpose] at h
  nlinarith [(polarMatrix_posDef hQ).det_pos]

theorem euclidean_norm_of_orthogonal (U : MatR n) (hU : Uᵀ*U = 1) (x : V n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) U x‖ = ‖x‖ := by
  have hs : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) U x‖^2 = ‖x‖^2 := by
    calc
      _ = (U*ᵥx.ofLp) ⬝ᵥ (U*ᵥx.ofLp) := by
        rw [← real_inner_self_eq_norm_sq, Khachiyan.inner_eq_dotProduct, Khachiyan.matrix_action_ofLp]
      _ = x.ofLp ⬝ᵥ (Uᵀ*ᵥ(U*ᵥx.ofLp)) := (Matrix.dotProduct_transpose_mulVec U x.ofLp (U*ᵥx.ofLp)).symm
      _ = x.ofLp ⬝ᵥ x.ofLp := by rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
      _ = ‖x‖^2 := by rw [← Khachiyan.inner_eq_dotProduct x x, real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) U x), norm_nonneg x]

theorem polarRotation_norm {Q : MatR n} (hQ : 0 < Q.det) (x : V n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (polarRotation Q) x‖ = ‖x‖ :=
  euclidean_norm_of_orthogonal _ (polarRotation_right_orthogonal hQ) x

end SharpCut.Certificate
