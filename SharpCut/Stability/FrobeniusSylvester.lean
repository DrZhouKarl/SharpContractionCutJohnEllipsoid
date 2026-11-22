import SharpCut.Stability.FrameActionNorms

/-! # Frobenius pairing and coercive Sylvester bounds with ordered products -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Stability
variable {n : ℕ}

def frobeniusPair (X Y : MatR n) : ℝ := ∑ i, ∑ j, X i j*Y i j

theorem frobeniusPair_trace (X Y : MatR n) : frobeniusPair X Y = (Xᵀ*Y).trace := by
  simp only [frobeniusPair, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem frobeniusPair_add_right (X Y Z : MatR n) :
    frobeniusPair X (Y+Z) = frobeniusPair X Y+frobeniusPair X Z := by
  simp only [frobeniusPair, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem frobeniusPair_transpose (X Y : MatR n) : frobeniusPair Xᵀ Yᵀ = frobeniusPair X Y := by
  simp only [frobeniusPair, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem frobeniusPair_columns (X Y : MatR n) :
    frobeniusPair X Y = ∑ j, ⟪matrixColumn X j,matrixColumn Y j⟫ := by
  unfold frobeniusPair
  rw [Finset.sum_comm]
  simp only [Khachiyan.inner_eq_dotProduct, dotProduct, matrixColumn, WithLp.ofLp_toLp]

theorem frobeniusPair_cauchy (X Y : MatR n) : |frobeniusPair X Y| ≤ frobeniusNorm X*frobeniusNorm Y := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p => X p.1 p.2) (fun p => Y p.1 p.2)
  simp only [Fintype.sum_prod_type] at h
  change (frobeniusPair X Y)^2 ≤ (∑ i, ∑ j, X i j^2)*(∑ i, ∑ j, Y i j^2) at h
  rw [← frobeniusNorm_sq_entries, ← frobeniusNorm_sq_entries, ← mul_pow, ← sq_abs] at h
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp h

/-- A positive quadratic lower bound acts separately on each actual Euclidean column. -/
theorem frobeniusPair_left_lower (A X : MatR n) (ell : ℝ)
    (hA : ∀ u : V n, ell*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) A u⟫) :
    ell*(frobeniusNorm X)^2 ≤ frobeniusPair X (A*X) := by
  rw [frobeniusNorm_sq_columns, frobeniusPair_columns, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [matrixColumn_mul]
  exact hA (matrixColumn X j)

theorem frobeniusPair_right_lower (B X : MatR n) (ell : ℝ) (hB : B.IsSymm)
    (hBq : ∀ u : V n, ell*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) B u⟫) :
    ell*(frobeniusNorm X)^2 ≤ frobeniusPair X (X*B) := by
  have h := frobeniusPair_left_lower B Xᵀ ell hBq
  rw [← hB.eq, ← Matrix.transpose_mul, frobeniusPair_transpose, frobeniusNorm_transpose] at h
  exact h

/-- Coercive Sylvester estimate; A and B need not commute with each other or X. -/
theorem sylvester_frobenius_bound (A B X : MatR n) (a b : ℝ) (hab : 0 < a+b) (hB : B.IsSymm)
    (hAq : ∀ u : V n, a*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) A u⟫)
    (hBq : ∀ u : V n, b*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) B u⟫) :
    frobeniusNorm X ≤ frobeniusNorm (A*X+X*B)/(a+b) := by
  have ha := frobeniusPair_left_lower A X a hAq
  have hb := frobeniusPair_right_lower B X b hB hBq
  have hc := frobeniusPair_cauchy X (A*X+X*B)
  have hl : (a+b)*(frobeniusNorm X)^2 ≤ frobeniusNorm X*frobeniusNorm (A*X+X*B) := by
    rw [frobeniusPair_add_right] at hc
    have hp := le_abs_self (frobeniusPair X (A*X)+frobeniusPair X (X*B))
    nlinarith only [ha, hb, hc, hp]
  by_cases hz : frobeniusNorm X = 0
  · rw [hz]
    exact div_nonneg (Real.sqrt_nonneg _) hab.le
  · have hx : 0 < frobeniusNorm X := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    apply (le_div_iff₀ hab).mpr
    apply le_of_mul_le_mul_left (a := frobeniusNorm X) _ hx
    nlinarith only [hl]

/-- The generic operator-to-Frobenius comparison also covers non-Hermitian Q. -/
theorem operator_frobenius_bound (A : MatR n) : operatorNorm A ≤ frobeniusNorm A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  have hrow (i : Fin n) : ((Matrix.toEuclideanCLM (𝕜 := ℝ) A u) i)^2 ≤ (∑ j, A i j^2)*‖u‖^2 := by
    rw [Khachiyan.matrix_action_ofLp]
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) (fun j => u j)
    simpa only [Matrix.mulVec, dotProduct, ← EuclideanSpace.real_norm_sq_eq] using h
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  rw [← EuclideanSpace.real_norm_sq_eq, ← Finset.sum_mul, ← frobeniusNorm_sq_entries, ← mul_pow] at h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp h

end SharpCut.Stability
