import SharpCut.Certificate.Factorization
import SharpCut.MatrixTools

/-! # Dimension-independent norm estimates for actual Euclidean John frames -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.JohnFrame
variable {n N : ℕ}

/-- Weighted Bessel inequality, with no contact count or dimension factor. -/
theorem weighted_bessel (F : JohnFrame n N) (a : Fin N → ℝ) :
    ‖∑ i, (F.weight i*a i) • F.contact i‖^2 ≤ ∑ i, F.weight i*(a i)^2 := by
  let x : V n := ∑ i, (F.weight i*a i) • F.contact i
  have hp : ∑ i, F.weight i*a i*⟪F.contact i, x⟫ = ‖x‖^2 := by
    have h := congrArg (fun y : V n => ⟪y, x⟫) (show (∑ i, (F.weight i*a i) • F.contact i) = x from rfl)
    simpa only [sum_inner, real_inner_smul_left, real_inner_self_eq_norm_sq] using h
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => F.weight i*a i*⟪F.contact i, x⟫)
    (f := fun i => F.weight i*(a i)^2)
    (g := fun i => F.weight i*⟪F.contact i, x⟫^2)
    (fun i _ => mul_nonneg (F.weight_pos i).le (sq_nonneg _))
    (fun i _ => mul_nonneg (F.weight_pos i).le (sq_nonneg _))
    (fun i _ => le_of_eq (by ring))
  simp only [hp, F.scalar_second_moment] at hc
  by_cases hz : ‖x‖^2 = 0
  · change ‖x‖^2 ≤ _
    rw [hz]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (F.weight_pos i).le (sq_nonneg _))
  · have hx : 0 < ‖x‖^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    change ‖x‖^2 ≤ _
    apply le_of_mul_le_mul_right (b := ‖x‖^2) _ hx
    nlinarith only [hc]

end SharpCut.JohnFrame

namespace SharpCut
variable {n : ℕ}

theorem frobeniusNorm_sq_entries (A : MatR n) :
    (frobeniusNorm A)^2 = ∑ i, ∑ j, A i j^2 := by
  unfold frobeniusNorm
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))

def matrixColumn (A : MatR n) (j : Fin n) : V n := WithLp.toLp 2 (fun i => A i j)

@[simp] theorem matrixColumn_apply (A : MatR n) (i j : Fin n) : matrixColumn A j i = A i j := rfl

theorem frobeniusNorm_sq_columns (A : MatR n) :
    (frobeniusNorm A)^2 = ∑ j, ‖matrixColumn A j‖^2 := by
  rw [frobeniusNorm_sq_entries, Finset.sum_comm]
  simp only [EuclideanSpace.real_norm_sq_eq, matrixColumn_apply]

/-- Each column is an ordinary Euclidean weighted Bessel estimate. -/
theorem JohnFrame.weighted_matrix_bessel {N : ℕ} (F : JohnFrame n N) (ξ : Fin N → V n) :
    (frobeniusNorm (∑ i, F.weight i • Certificate.cross (F.contact i) (ξ i)))^2 ≤
      ∑ i, F.weight i*‖ξ i‖^2 := by
  have hc (j : Fin n) : matrixColumn (∑ i, F.weight i • Certificate.cross (F.contact i) (ξ i)) j =
      ∑ i, (F.weight i*ξ i j) • F.contact i := by
    ext k
    simp only [matrixColumn_apply, Matrix.sum_apply, Matrix.smul_apply, Certificate.cross,
      Matrix.vecMulVec_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [frobeniusNorm_sq_columns]
  simp only [hc]
  calc
    _ ≤ ∑ j, ∑ i, F.weight i*(ξ i j)^2 := Finset.sum_le_sum (fun j _ => F.weighted_bessel (fun i => ξ i j))
    _ = ∑ i, F.weight i*‖ξ i‖^2 := by
      rw [Finset.sum_comm]
      simp only [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]

theorem matrixColumn_mul (A X : MatR n) (j : Fin n) :
    matrixColumn (A*X) j = Matrix.toEuclideanCLM (𝕜 := ℝ) A (matrixColumn X j) := by
  ext i
  rw [matrixColumn_apply, Khachiyan.matrix_action_ofLp]
  rfl

/-- The operator norm acts on each Euclidean column without a dimension factor. -/
theorem frobeniusNorm_mul_operator_left (A X : MatR n) :
    frobeniusNorm (A*X) ≤ operatorNorm A*frobeniusNorm X := by
  have hs : (frobeniusNorm (A*X))^2 ≤ (operatorNorm A*frobeniusNorm X)^2 := by
    rw [frobeniusNorm_sq_columns, mul_pow, frobeniusNorm_sq_columns, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [matrixColumn_mul]
    have h := ContinuousLinearMap.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℝ) A) (matrixColumn X j)
    change ‖_‖ ≤ operatorNorm A*‖matrixColumn X j‖ at h
    nlinarith only [h, norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) A (matrixColumn X j)),
      show 0 ≤ operatorNorm A*‖matrixColumn X j‖ from mul_nonneg (norm_nonneg _) (norm_nonneg _)]
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mp hs

end SharpCut

namespace SharpCut
variable {n : ℕ}

open scoped Matrix.Norms.L2Operator in
theorem operatorNorm_transpose (A : MatR n) : operatorNorm Aᵀ = operatorNorm A := by
  have ht : Aᴴ = Aᵀ := by ext i j; simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
  simp only [operatorNorm, Matrix.l2_opNorm_toEuclideanCLM, ← ht]
  exact Matrix.l2_opNorm_conjTranspose A

theorem frobeniusNorm_mul_operator_right (X A : MatR n) :
    frobeniusNorm (X*A) ≤ frobeniusNorm X*operatorNorm A := by
  calc
    _ = frobeniusNorm (Aᵀ*Xᵀ) := by rw [← Matrix.transpose_mul, frobeniusNorm_transpose]
    _ ≤ operatorNorm Aᵀ*frobeniusNorm Xᵀ := frobeniusNorm_mul_operator_left _ _
    _ = _ := by rw [operatorNorm_transpose, frobeniusNorm_transpose, mul_comm]

open scoped Matrix.Norms.Frobenius in
theorem frobeniusNorm_add_le (A B : MatR n) : frobeniusNorm (A+B) ≤ frobeniusNorm A+frobeniusNorm B := by
  simp only [frobeniusNorm_eq_scoped]
  exact norm_add_le A B

open scoped Matrix.Norms.Frobenius in
theorem frobeniusNorm_neg (A : MatR n) : frobeniusNorm (-A) = frobeniusNorm A := by
  simp only [frobeniusNorm_eq_scoped, norm_neg]

end SharpCut
