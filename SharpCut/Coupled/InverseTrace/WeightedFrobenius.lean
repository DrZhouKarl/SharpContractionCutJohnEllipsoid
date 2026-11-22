import SharpCut.Coupled.InverseTrace.OptimalTest
import SharpCut.Stability.FrobeniusSylvester

/-! # Exact positive-root Frobenius weighted Cauchy coefficient -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Coupled.InverseTrace
open Stability
variable {n : ℕ}

theorem frobenius_square_gram (X : MatR n) : (frobeniusNorm X)^2 = (Xᵀ*X).trace := by
  rw [frobeniusNorm_sq_entries, Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_two]

/-- The matrix quadratic form is a genuine Frobenius square, not a commuting surrogate. -/
theorem weighted_matrix_square (R Z : MatR n) (hR : R.PosDef) (hZ : Z.IsHermitian) :
    (frobeniusNorm (Z*CFC.sqrt R))^2 = (Z^2*R).trace := by
  have hS := Optimization.sqrt_posDef R hR
  have hs : CFC.sqrt R*CFC.sqrt R = R := CFC.sqrt_mul_sqrt_self _ hR.posSemidef.nonneg
  rw [frobenius_square_gram, Matrix.transpose_mul, hS.isHermitian.isSymm.eq, hZ.isSymm.eq]
  calc
    _ = (CFC.sqrt R*(Z*Z)*CFC.sqrt R).trace := by simp only [Matrix.mul_assoc]
    _ = (CFC.sqrt R*CFC.sqrt R*(Z*Z)).trace := Matrix.trace_mul_cycle _ _ _
    _ = (Z^2*(CFC.sqrt R*CFC.sqrt R)).trace := by rw [Matrix.trace_mul_comm, pow_two]
    _ = _ := by rw [hs]

theorem inverse_root_square (R : MatR n) (hR : R.PosDef) :
    (CFC.sqrt R)⁻¹*(CFC.sqrt R)⁻¹ = R⁻¹ := by
  have hS := Optimization.sqrt_posDef R hR
  have hu : IsUnit (CFC.sqrt R).det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hs : CFC.sqrt R*CFC.sqrt R = R := CFC.sqrt_mul_sqrt_self _ hR.posSemidef.nonneg
  symm
  apply Matrix.inv_eq_left_inv
  calc
    _ = ((CFC.sqrt R)⁻¹*(CFC.sqrt R)⁻¹)*(CFC.sqrt R*CFC.sqrt R) := congrArg (fun M : MatR n => ((CFC.sqrt R)⁻¹*(CFC.sqrt R)⁻¹)*M) hs.symm
    _ = (CFC.sqrt R)⁻¹*((CFC.sqrt R)⁻¹*CFC.sqrt R)*CFC.sqrt R := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]

/-- The dual matrix norm gives the exact trace coefficient in (10.22). -/
theorem weighted_dual_square (R : MatR n) (hR : R.PosDef) (β : ℝ) :
    (frobeniusNorm ((R-β • (1 : MatR n))*(CFC.sqrt R)⁻¹))^2 = ((R-β • (1 : MatR n))^2*R⁻¹).trace := by
  have hS := Optimization.sqrt_posDef R hR
  have hB : (R-β • (1 : MatR n)).IsHermitian := hR.isHermitian.sub (Matrix.isHermitian_one.smul (by rfl))
  rw [frobenius_square_gram, Matrix.transpose_mul, hS.inv.isHermitian.isSymm.eq, hB.isSymm.eq]
  calc
    _ = ((CFC.sqrt R)⁻¹*((R-β • (1 : MatR n))*(R-β • (1 : MatR n)))*(CFC.sqrt R)⁻¹).trace := by simp only [Matrix.mul_assoc]
    _ = ((CFC.sqrt R)⁻¹*(CFC.sqrt R)⁻¹*((R-β • (1 : MatR n))*(R-β • (1 : MatR n)))).trace := Matrix.trace_mul_cycle _ _ _
    _ = _ := by rw [Matrix.trace_mul_comm, inverse_root_square R hR, pow_two]

/-- Pairing cancellation uses trace cyclicity and ordered inverse cancellation only. -/
theorem weighted_matrix_pairing (R Z : MatR n) (hR : R.PosDef) (hZ : Z.IsHermitian) (β : ℝ) :
    frobeniusPair (Z*CFC.sqrt R) ((R-β • (1 : MatR n))*(CFC.sqrt R)⁻¹) = (Z*(R-β • (1 : MatR n))).trace := by
  have hS := Optimization.sqrt_posDef R hR
  have hu : IsUnit (CFC.sqrt R).det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  rw [frobeniusPair_trace, Matrix.transpose_mul, hS.isHermitian.isSymm.eq, hZ.isSymm.eq]
  calc
    _ = (CFC.sqrt R*(Z*(R-β • (1 : MatR n)))*(CFC.sqrt R)⁻¹).trace := by simp only [Matrix.mul_assoc]
    _ = ((CFC.sqrt R)⁻¹*CFC.sqrt R*(Z*(R-β • (1 : MatR n)))).trace := Matrix.trace_mul_cycle _ _ _
    _ = _ := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

theorem matrix_coefficient_cauchy (R Z : MatR n) (hR : R.PosDef) (hZ : Z.IsHermitian) (β : ℝ) :
    ((Z*(R-β • (1 : MatR n))).trace)^2 ≤ ((R-β • (1 : MatR n))^2*R⁻¹).trace*(Z^2*R).trace := by
  have h := frobeniusPair_cauchy (Z*CFC.sqrt R) ((R-β • (1 : MatR n))*(CFC.sqrt R)⁻¹)
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (show 0 ≤ frobeniusNorm (Z*CFC.sqrt R) from Real.sqrt_nonneg _)
    (show 0 ≤ frobeniusNorm ((R-β • (1 : MatR n))*(CFC.sqrt R)⁻¹) from Real.sqrt_nonneg _))).mpr h
  rw [sq_abs, mul_pow, weighted_matrix_square R Z hR hZ, weighted_dual_square R hR β,
    weighted_matrix_pairing R Z hR hZ β] at hs
  nlinarith only [hs]

end SharpCut.Coupled.InverseTrace
