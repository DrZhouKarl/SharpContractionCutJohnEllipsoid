import SharpCut.Geometry
import Mathlib.Analysis.Matrix.Normed

/-! # Explicit Frobenius and Euclidean operator norms

The two norms are separate functions. No global matrix norm instance is changed.
This supplies the norm interface for later stability statements; mixed norm
estimates and the stability theorem themselves remain separate obligations.
-/

noncomputable section
open scoped BigOperators
namespace SharpCut

def frobeniusNorm {n : ℕ} (A : MatR n) : ℝ := Real.sqrt (∑ i, ∑ j, A i j^2)
def operatorNorm {n : ℕ} (A : MatR n) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖

open scoped Matrix.Norms.Frobenius in
theorem frobeniusNorm_eq_scoped {n : ℕ} (A : MatR n) : frobeniusNorm A = ‖A‖ := by
  simp only [frobeniusNorm, Matrix.frobenius_norm_def, Real.norm_eq_abs,
    Real.rpow_two, sq_abs, Real.sqrt_eq_rpow]

open scoped Matrix.Norms.Frobenius in
theorem frobeniusNorm_transpose {n : ℕ} (A : MatR n) : frobeniusNorm A.transpose = frobeniusNorm A := by
  rw [frobeniusNorm_eq_scoped, frobeniusNorm_eq_scoped]
  exact Matrix.frobenius_norm_transpose A

open scoped Matrix.Norms.Frobenius in
theorem frobeniusNorm_mul {n : ℕ} (A B : MatR n) :
    frobeniusNorm (A*B) ≤ frobeniusNorm A*frobeniusNorm B := by
  rw [frobeniusNorm_eq_scoped, frobeniusNorm_eq_scoped, frobeniusNorm_eq_scoped]
  exact Matrix.frobenius_norm_mul A B

end SharpCut
