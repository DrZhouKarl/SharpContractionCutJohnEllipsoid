import SharpCut.Stability.FrobeniusSylvester

/-! # Actual spectral quadratic and inverse norm transfers -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Stability
open Certificate
variable {n : ℕ}

theorem quadratic_diagonal_basis (B : OrthonormalBasis (Fin n) ℝ (V n)) (A : MatR n) (eigen : Fin n → ℝ)
    (hA : Geometry.inBasis B A = Matrix.diagonal eigen) (u : V n) :
    ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) A u⟫ = ∑ i, eigen i*(B.repr u i)^2 := by
  rw [← Geometry.basisMatrix_inner B u (Matrix.toEuclideanCLM (𝕜 := ℝ) A u),
    ← Geometry.inBasis_action B A u, hA, Khachiyan.inner_matrix_action]
  simp only [Matrix.mulVec_diagonal, dotProduct, Geometry.basisMatrix_action_repr]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hermitian_quadratic_lower (A : MatR n) (hA : A.IsHermitian) (ell : ℝ)
    (he : ∀ i, ell ≤ hA.eigenvalues i) (u : V n) :
    ell*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) A u⟫ := by
  rw [quadratic_diagonal_basis hA.eigenvectorBasis A _ (Gap.inEigenbasis_diagonal A hA),
    ← hA.eigenvectorBasis.repr.norm_map u, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (he i) (sq_nonneg _))

/-- A lower quadratic bound implies a lower action norm without commutativity. -/
theorem quadratic_action_lower (A : MatR n) (ell : ℝ)
    (hq : ∀ u : V n, ell*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) A u⟫) (u : V n) :
    ell*‖u‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A u‖ := by
  have h := (hq u).trans (real_inner_le_norm u (Matrix.toEuclideanCLM (𝕜 := ℝ) A u))
  by_cases hz : ‖u‖ = 0
  · rw [hz, mul_zero]; exact norm_nonneg _
  · have hp : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply le_of_mul_le_mul_left (a := ‖u‖) _ hp
    nlinarith only [h]

/-- A genuine positive-definite inverse is controlled by the quadratic lower bound. -/
theorem inverse_operator_bound (A : MatR n) (hA : A.PosDef) (ell : ℝ) (hell : 0 < ell)
    (hq : ∀ u : V n, ell*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) A u⟫) :
    operatorNorm A⁻¹ ≤ 1/ell := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_pos (by norm_num) hell).le
  intro u
  have h := quadratic_action_lower A ell hq (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ u)
  rw [Determinant.posDef_action_inverse A hA u] at h
  have hl : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ u‖ ≤ ‖u‖/ell :=
    (le_div_iff₀ hell).mpr (by nlinarith only [h])
  convert hl using 1 <;> ring

/-- Squared action of a symmetric square root is the original quadratic form. -/
theorem symmetric_square_action (S : MatR n) (hS : S.IsSymm) (u : V n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S u‖^2 = ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (S*S) u⟫ := by
  rw [← real_inner_self_eq_norm_sq, matrix_action_mul, Khachiyan.inner_matrix_action_symm hS u (Matrix.toEuclideanCLM (𝕜 := ℝ) S u)]

/-- Ordered square-root conjugation transfers a Frobenius error with coefficient 1/ell. -/
theorem sqrt_conjugation_lower (M X : MatR n) (hM : M.PosDef) (ell : ℝ) (hell : 0 < ell)
    (hq : ∀ u : V n, ell*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) M u⟫) :
    frobeniusNorm X ≤ frobeniusNorm (CFC.sqrt M*X*CFC.sqrt M)/ell := by
  have hS := Optimization.sqrt_posDef M hM
  have hs : CFC.sqrt M*CFC.sqrt M = M := CFC.sqrt_mul_sqrt_self _ hM.posSemidef.nonneg
  have hnorm (u : V n) : ell*‖u‖^2 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M) u‖^2 := by
    rw [symmetric_square_action _ hS.isHermitian.isSymm, hs]
    exact hq u
  have hleft := frobenius_left_lower (CFC.sqrt M) X ell hnorm
  have hright := frobenius_right_lower (CFC.sqrt M) (CFC.sqrt M*X) ell hS.isHermitian.isSymm hnorm
  have hmul := mul_le_mul_of_nonneg_left hleft hell.le
  have hsq : (ell*frobeniusNorm X)^2 ≤ (frobeniusNorm (CFC.sqrt M*X*CFC.sqrt M))^2 := by
    nlinarith only [hmul, hright]
  have hn : ell*frobeniusNorm X ≤ frobeniusNorm (CFC.sqrt M*X*CFC.sqrt M) :=
    (sq_le_sq₀ (mul_nonneg hell.le (show 0 ≤ frobeniusNorm X from Real.sqrt_nonneg _))
      (show 0 ≤ frobeniusNorm (CFC.sqrt M*X*CFC.sqrt M) from Real.sqrt_nonneg _)).mp hsq
  apply (le_div_iff₀ hell).mpr
  rw [mul_comm]
  exact hn

end SharpCut.Stability
