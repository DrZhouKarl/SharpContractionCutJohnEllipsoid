import SharpCut.Gap.MatrixDivergence
import SharpCut.MatrixTools

/-! # Exact Frobenius/spectral identities for real Hermitian matrices -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Gap
variable {n : ℕ}

theorem frobeniusNorm_sq (A : MatR n) : (frobeniusNorm A)^2 = ∑ i, ∑ j, A i j^2 := by
  unfold frobeniusNorm
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => sq_nonneg _)))

theorem frobeniusNorm_sq_trace (A : MatR n) (hA : A.IsHermitian) :
    (frobeniusNorm A)^2 = (A^2).trace := by
  rw [frobeniusNorm_sq, pow_two]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA.isSymm.apply i j, pow_two]

theorem inEigenbasis_diagonal (A : MatR n) (hA : A.IsHermitian) :
    Geometry.inBasis hA.eigenvectorBasis A = Matrix.diagonal hA.eigenvalues := by
  ext i j
  rw [Geometry.inBasis_entry, eigenvector_action A hA j, real_inner_smul_right,
    orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal i j, Matrix.diagonal_apply]
  split_ifs with hij
  · subst j; simp only [mul_one]
  · simp only [mul_zero]

theorem frobenius_shift_spectral (A : MatR n) (hA : A.IsHermitian) :
    (frobeniusNorm (A-1))^2 = ∑ i, (hA.eigenvalues i-1)^2 := by
  rw [frobeniusNorm_sq_trace _ (hA.sub Matrix.isHermitian_one), ← Geometry.inBasis_trace hA.eigenvectorBasis]
  have hp : Geometry.inBasis hA.eigenvectorBasis ((A-1)^2) =
      Matrix.diagonal (fun i => (hA.eigenvalues i-1)^2) := by
    rw [pow_two, Geometry.inBasis_mul, Geometry.inBasis_sub, inEigenbasis_diagonal,
      Geometry.inBasis_one, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [pow_two]
  rw [hp, Matrix.trace_diagonal]

end SharpCut.Gap
