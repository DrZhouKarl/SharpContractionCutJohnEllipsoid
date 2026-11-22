import SharpCut.Coupled.Complementary

/-! # Exact completed-square forms for the inverse-trace equivalence -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Coupled.InverseTrace
open Certificate
variable {n : ℕ}

def effectiveMatrix (E : MatR n) (j : V n) (β η : ℝ) : MatR n := E+β • (1 : MatR n)-(1/η) • outer j

def originalLinear (E : MatR n) (j : V n) (Z : MatR n) (q : V n) : ℝ := (Z*E).trace+⟪q,j⟫
def originalQuadratic (E : MatR n) (j : V n) (β η : ℝ) (Z : MatR n) (q : V n) : ℝ :=
  (Z^2*(E+β • (1 : MatR n))).trace+2*⟪q,Matrix.toEuclideanCLM (𝕜 := ℝ) Z j⟫+η*‖q‖^2

def completedLinear (R : MatR n) (j : V n) (β : ℝ) (Z : MatR n) (q : V n) : ℝ :=
  (Z*(R-β • (1 : MatR n))).trace+⟪q,j⟫
def completedQuadratic (R : MatR n) (η : ℝ) (Z : MatR n) (q : V n) : ℝ := (Z^2*R).trace+η*‖q‖^2

def AllCoupledTests (E : MatR n) (j : V n) (β η σ : ℝ) : Prop :=
  ∀ Z : MatR n, Z.IsHermitian → ∀ q : V n, (originalLinear E j Z q)^2 ≤ σ*originalQuadratic E j β η Z q

def AllCompletedTests (R : MatR n) (j : V n) (β η σ : ℝ) : Prop :=
  ∀ Z : MatR n, Z.IsHermitian → ∀ q : V n, (completedLinear R j β Z q)^2 ≤ σ*completedQuadratic R η Z q

theorem effectiveMatrix_hermitian (E : MatR n) (j : V n) (β η : ℝ) (hE : E.IsHermitian) :
    (effectiveMatrix E j β η).IsHermitian :=
  (hE.add (Matrix.isHermitian_one.smul (by rfl))).sub ((Khachiyan.outer_posSemidef j).isHermitian.smul (by rfl))

/-- Equation (10.21), including the order-preserving matrix linear identity. -/
theorem linear_completion (E : MatR n) (j : V n) (β η : ℝ) (Z : MatR n) (q : V n) :
    originalLinear E j Z (q-(1/η) • Matrix.toEuclideanCLM (𝕜 := ℝ) Z j) =
      completedLinear (effectiveMatrix E j β η) j β Z q := by
  have hR : effectiveMatrix E j β η-β • (1 : MatR n) = E-(1/η) • outer j := by unfold effectiveMatrix; abel
  unfold originalLinear completedLinear
  rw [hR, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    trace_outer_linear, inner_sub_left, real_inner_smul_left, smul_eq_mul,
    real_inner_comm j (Matrix.toEuclideanCLM (𝕜 := ℝ) Z j)]
  ring

/-- The full quadratic completion in (10.21), with all inverse scalar cancellation justified. -/
theorem quadratic_completion (E : MatR n) (j : V n) (β η : ℝ) (hη : η ≠ 0)
    (Z : MatR n) (hZ : Z.IsHermitian) (q : V n) :
    originalQuadratic E j β η Z (q-(1/η) • Matrix.toEuclideanCLM (𝕜 := ℝ) Z j) =
      completedQuadratic (effectiveMatrix E j β η) η Z q := by
  unfold originalQuadratic completedQuadratic effectiveMatrix
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, trace_action_square_outer Z hZ,
    inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_sub_sq_real,
    real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [smul_eq_mul]
  field_simp [hη] <;> ring

/-- Completing the square is a bijective change of every vector test. -/
theorem all_tests_completion_iff (E : MatR n) (j : V n) (β η σ : ℝ) (hη : η ≠ 0) :
    AllCoupledTests E j β η σ ↔ AllCompletedTests (effectiveMatrix E j β η) j β η σ := by
  constructor
  · intro h Z hZ q
    have ht := h Z hZ (q-(1/η) • Matrix.toEuclideanCLM (𝕜 := ℝ) Z j)
    rw [linear_completion, quadratic_completion E j β η hη Z hZ q] at ht
    exact ht
  · intro h Z hZ q
    let q' := q+(1/η) • Matrix.toEuclideanCLM (𝕜 := ℝ) Z j
    have hq : q'-(1/η) • Matrix.toEuclideanCLM (𝕜 := ℝ) Z j = q := by dsimp [q']; abel
    have ht := h Z hZ q'
    rw [← linear_completion, ← quadratic_completion E j β η hη Z hZ q', hq] at ht
    exact ht

end SharpCut.Coupled.InverseTrace
