import SharpCut.Coupled.InverseTrace.Positivity

/-! # The exact coefficient and a test attaining it, including zero coefficient -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Coupled.InverseTrace
variable {n : ℕ}

def coefficient (R : MatR n) (j : V n) (β η : ℝ) : ℝ := ((R-β • (1 : MatR n))^2*R⁻¹).trace+‖j‖^2/η

def bestMatrix (R : MatR n) (β : ℝ) : MatR n := 1-β • R⁻¹
def bestVector (j : V n) (η : ℝ) : V n := (1/η) • j

theorem bestMatrix_hermitian (R : MatR n) (hR : R.PosDef) (β : ℝ) : (bestMatrix R β).IsHermitian :=
  Matrix.isHermitian_one.sub (hR.inv.isHermitian.smul (by rfl))

theorem bestMatrix_identity (R : MatR n) (hR : R.PosDef) (β : ℝ) :
    bestMatrix R β = (R-β • (1 : MatR n))*R⁻¹ := by
  unfold bestMatrix
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_nonsing_inv R (isUnit_iff_ne_zero.mpr hR.det_pos.ne')]

theorem bestMatrix_mul (R : MatR n) (hR : R.PosDef) (β : ℝ) :
    bestMatrix R β*R = R-β • (1 : MatR n) := by
  unfold bestMatrix
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
    Matrix.nonsing_inv_mul R (isUnit_iff_ne_zero.mpr hR.det_pos.ne')]

theorem best_matrix_linear (R : MatR n) (hR : R.PosDef) (β : ℝ) :
    (bestMatrix R β*(R-β • (1 : MatR n))).trace = ((R-β • (1 : MatR n))^2*R⁻¹).trace := by
  rw [bestMatrix_identity R hR β, pow_two, Matrix.trace_mul_cycle]

theorem best_vector_pairing (j : V n) (η : ℝ) : ⟪bestVector j η,j⟫ = ‖j‖^2/η := by
  rw [bestVector, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

theorem best_vector_norm (j : V n) (η : ℝ) (hη : η ≠ 0) : η*‖bestVector j η‖^2 = ‖j‖^2/η := by
  rw [bestVector, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp [hη] <;> ring

/-- At the paper's selected test, both the linear and quadratic forms equal S. -/
theorem best_test_attains (R : MatR n) (hR : R.PosDef) (j : V n) (β η : ℝ) (hη : η ≠ 0) :
    completedLinear R j β (bestMatrix R β) (bestVector j η) = coefficient R j β η ∧
    completedQuadratic R η (bestMatrix R β) (bestVector j η) = coefficient R j β η := by
  unfold completedLinear completedQuadratic coefficient
  rw [best_matrix_linear R hR β, best_vector_pairing, best_vector_norm j η hη]
  have heq : (bestMatrix R β)^2*R = bestMatrix R β*(R-β • (1 : MatR n)) := by
    rw [pow_two, Matrix.mul_assoc, bestMatrix_mul R hR β]
  rw [heq, best_matrix_linear R hR β]
  exact ⟨rfl, rfl⟩

/-- Exact matrix identity underlying (10.22)/(10.24), with inverse products ordered. -/
theorem coefficient_matrix_identity (R : MatR n) (hR : R.PosDef) (β : ℝ) :
    (R-β • (1 : MatR n))^2*R⁻¹ = R-(2*β) • (1 : MatR n)+β^2 • R⁻¹ := by
  have hu : IsUnit R.det := isUnit_iff_ne_zero.mpr hR.det_pos.ne'
  rw [pow_two, Matrix.mul_assoc]
  have hright : (R-β • (1 : MatR n))*R⁻¹ = 1-β • R⁻¹ := (bestMatrix_identity R hR β).symm
  rw [hright]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, Matrix.mul_nonsing_inv R hu]
  simp only [smul_sub, smul_smul]
  module

/-- The coefficient's trace expansion, preserving the dimension and beta factors. -/
theorem coefficient_trace_identity (R : MatR n) (hR : R.PosDef) (j : V n) (β η : ℝ) :
    coefficient R j β η = R.trace-2*β*(n : ℝ)+β^2*R⁻¹.trace+‖j‖^2/η := by
  unfold coefficient
  rw [coefficient_matrix_identity R hR β]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul]


end SharpCut.Coupled.InverseTrace
