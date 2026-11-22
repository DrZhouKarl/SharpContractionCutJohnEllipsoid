import SharpCut.Coupled.InverseTrace.WeightedFrobenius

/-! # The sharp all-test coefficient, including its zero case -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Coupled.InverseTrace
variable {n : ℕ}

theorem two_part_cauchy (r₀ r₁ s₀ s₁ t₀ t₁ : ℝ) (hs₀ : 0 ≤ s₀) (hs₁ : 0 ≤ s₁)
    (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁) (hr₀ : r₀^2 ≤ s₀*t₀) (hr₁ : r₁^2 ≤ s₁*t₁) :
    (r₀+r₁)^2 ≤ (s₀+s₁)*(t₀+t₁) := by
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ (![s₀,s₁] : Fin 2 → ℝ) i := by
    intro i hi; fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> assumption
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ (![t₀,t₁] : Fin 2 → ℝ) i := by
    intro i hi; fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> assumption
  have hr : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ((![r₀,r₁] : Fin 2 → ℝ) i)^2 ≤
      (![s₀,s₁] : Fin 2 → ℝ) i*(![t₀,t₁] : Fin 2 → ℝ) i := by
    intro i hi; fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> assumption
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ hf hg hr
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem vector_coefficient_cauchy (j q : V n) (η : ℝ) (hη : 0 < η) :
    ⟪q,j⟫^2 ≤ (‖j‖^2/η)*(η*‖q‖^2) := by
  have h := abs_real_inner_le_norm q j
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [sq_abs, mul_pow] at hs
  have heq : ‖q‖^2*‖j‖^2 = (‖j‖^2/η)*(η*‖q‖^2) := by field_simp [hη.ne'] <;> ring
  rwa [heq] at hs

theorem matrix_coefficient_nonneg (R : MatR n) (hR : R.PosDef) (β : ℝ) :
    0 ≤ ((R-β • (1 : MatR n))^2*R⁻¹).trace := by
  rw [← weighted_dual_square R hR β]
  exact sq_nonneg _

theorem matrix_quadratic_nonneg (R Z : MatR n) (hR : R.PosDef) (hZ : Z.IsHermitian) : 0 ≤ (Z^2*R).trace := by
  rw [← weighted_matrix_square R Z hR hZ]
  exact sq_nonneg _

theorem coefficient_nonneg (R : MatR n) (hR : R.PosDef) (j : V n) (β η : ℝ) (hη : 0 < η) :
    0 ≤ coefficient R j β η := add_nonneg (matrix_coefficient_nonneg R hR β) (div_nonneg (sq_nonneg _) hη.le)

theorem completedQuadratic_nonneg (R Z : MatR n) (hR : R.PosDef) (hZ : Z.IsHermitian)
    (η : ℝ) (hη : 0 < η) (q : V n) : 0 ≤ completedQuadratic R η Z q :=
  add_nonneg (matrix_quadratic_nonneg R Z hR hZ) (mul_nonneg hη.le (sq_nonneg _))

/-- Every symmetric matrix/vector test is controlled by the exact attained coefficient S. -/
theorem completed_coefficient_cauchy (R : MatR n) (hR : R.PosDef) (j : V n) (β η : ℝ) (hη : 0 < η)
    (Z : MatR n) (hZ : Z.IsHermitian) (q : V n) :
    (completedLinear R j β Z q)^2 ≤ coefficient R j β η*completedQuadratic R η Z q := by
  exact two_part_cauchy _ _ _ _ _ _ (matrix_coefficient_nonneg R hR β) (div_nonneg (sq_nonneg _) hη.le)
    (matrix_quadratic_nonneg R Z hR hZ) (mul_nonneg hη.le (sq_nonneg _))
    (matrix_coefficient_cauchy R Z hR hZ β) (vector_coefficient_cauchy j q η hη)

/-- The universal inequality is equivalent to S<=sigma; S=0 is handled explicitly. -/
theorem completed_tests_iff_coefficient (R : MatR n) (hR : R.PosDef) (j : V n) (β η σ : ℝ)
    (hη : 0 < η) (hσ : 0 ≤ σ) : AllCompletedTests R j β η σ ↔ coefficient R j β η ≤ σ := by
  constructor
  · intro h
    have ht := h (bestMatrix R β) (bestMatrix_hermitian R hR β) (bestVector j η)
    rw [(best_test_attains R hR j β η hη.ne').1, (best_test_attains R hR j β η hη.ne').2] at ht
    by_cases hz : coefficient R j β η = 0
    · rw [hz]; exact hσ
    · have hp : 0 < coefficient R j β η := lt_of_le_of_ne (coefficient_nonneg R hR j β η hη) (Ne.symm hz)
      apply le_of_mul_le_mul_right (a := coefficient R j β η) _ hp
      nlinarith only [ht]
  · intro hs Z hZ q
    exact (completed_coefficient_cauchy R hR j β η hη Z hZ q).trans
      (mul_le_mul_of_nonneg_right hs (completedQuadratic_nonneg R Z hR hZ η hη q))

end SharpCut.Coupled.InverseTrace
