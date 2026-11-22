import SharpCut.Stability.SupportMismatch

/-! # Exact isotropic action norm and dimension-independent support-error sums -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Stability
variable {n N : ℕ}

def matrixRow (A : MatR n) (i : Fin n) : V n := matrixColumn Aᵀ i

theorem action_row_inner (A : MatR n) (u : V n) (i : Fin n) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) i = ⟪matrixRow A i,u⟫ := by
  rw [Khachiyan.matrix_action_ofLp, Khachiyan.inner_eq_dotProduct]
  rfl

/-- Isotropy gives the exact Frobenius square for every matrix, without symmetry. -/
theorem frame_action_norm_sq (F : JohnFrame n N) (A : MatR n) :
    (∑ i, F.weight i*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖^2) = (frobeniusNorm A)^2 := by
  have hrow (j : Fin n) : (∑ i, F.weight i*⟪matrixRow A j,F.contact i⟫^2) = ‖matrixRow A j‖^2 := by
    simpa only [real_inner_comm] using F.scalar_second_moment (matrixRow A j)
  simp only [EuclideanSpace.real_norm_sq_eq, ← action_row_inner]
  have hact : (∑ i, F.weight i*(∑ j, ((Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)) j)^2)) =
      ∑ j, ∑ i, F.weight i*⟪matrixRow A j,F.contact i⟫^2 := by
    simp only [Finset.mul_sum, action_row_inner]
    rw [Finset.sum_comm]
  rw [hact]
  simp only [hrow]
  change (∑ j, ‖matrixColumn Aᵀ j‖^2) = _
  rw [← frobeniusNorm_sq_columns, frobeniusNorm_transpose]

/-- The norm of the isotropic sum of support-value differences is bounded by shape error. -/
theorem frame_support_difference_bound (F : JohnFrame n N) (A B : MatR n) :
    ‖∑ i, (F.weight i*(‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖-
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B (F.contact i)‖)) • F.contact i‖ ≤ frobeniusNorm (A-B) := by
  have hb := F.weighted_bessel (fun i => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖-
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B (F.contact i)‖)
  have hs : (∑ i, F.weight i*(‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖-
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B (F.contact i)‖)^2) ≤
      ∑ i, F.weight i*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A-B) (F.contact i)‖^2 := by
    apply Finset.sum_le_sum
    intro i _
    have h := abs_norm_sub_norm_le (Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) B (F.contact i))
    rw [← Certificate.matrix_action_sub] at h
    exact mul_le_mul_of_nonneg_left (sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2) (F.weight_pos i).le
  rw [frame_action_norm_sq F (A-B)] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp (hb.trans hs)

/-- Both statements in (6.8), for arbitrary matrices, before Bessel is used. -/
theorem frame_support_difference_square (F : JohnFrame n N) (A B : MatR n) :
    (∑ i, F.weight i*|‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖-
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B (F.contact i)‖|^2) ≤ (frobeniusNorm (A-B))^2 := by
  rw [← frame_action_norm_sq F (A-B)]
  apply Finset.sum_le_sum
  intro i _
  have h := abs_norm_sub_norm_le (Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i))
    (Matrix.toEuclideanCLM (𝕜 := ℝ) B (F.contact i))
  rw [← Certificate.matrix_action_sub] at h
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h) (F.weight_pos i).le

end SharpCut.Stability
