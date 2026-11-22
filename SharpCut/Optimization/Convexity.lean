import SharpCut.Optimization.ExtraCuts
import Mathlib.Analysis.Convex.Function

/-! # Kernel-checked convex SOC feasibility and concavity of the positive log determinant -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix Set
namespace SharpCut.Optimization
open Certificate
variable {n N : ℕ}

theorem positive_matrix_mixture (A B : MatR n) (hA : A.PosDef) (hB : B.PosDef)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b = 1) : (a • A+b • B).PosDef := by
  by_cases hz : a = 0
  · have hb1 : b = 1 := by linarith only [hab, hz]
    rw [hz, hb1, zero_smul, zero_add, one_smul]
    exact hB
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    exact (hA.smul hap).add_posSemidef (hB.posSemidef.smul hb)

theorem posDef_convex : Convex ℝ {A : MatR n | A.PosDef} := by
  intro A hA B hB a b ha hb hab
  exact positive_matrix_mixture A B hA hB a b ha hb hab

/-- The supporting trace hyperplane bound, with a genuine positive-root conjugation. -/
theorem logdet_supporting_hyperplane (A B : MatR n) (hA : A.PosDef) (hB : B.PosDef) :
    Real.log B.det ≤ Real.log A.det+(A⁻¹*(B-A)).trace := by
  have hC := matchingMatrix_posDef B A⁻¹ hB hA.inv
  have hgap := matrixDivergence_nonneg (matchingMatrix B A⁻¹) hC
  unfold matrixDivergence at hgap
  rw [matchingMatrix_trace B A⁻¹ hA.inv, matchingMatrix_det B A⁻¹ hA.inv,
    Real.log_mul hB.det_pos.ne' hA.inv.det_pos.ne', Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv] at hgap
  have htr : (A⁻¹*(B-A)).trace = (B*A⁻¹).trace-(n : ℝ) := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), Matrix.trace_one,
      Fintype.card_fin, Matrix.trace_mul_comm A⁻¹ B]
  rw [htr]
  linarith only [hgap]

/-- Logdet is concave on all genuine symmetric positive-definite matrices, without commutation. -/
theorem logdet_concaveOn : ConcaveOn ℝ {A : MatR n | A.PosDef} (fun A => Real.log A.det) := by
  refine ⟨posDef_convex, ?_⟩
  intro A hA B hB a b ha hb hab
  let C := a • A+b • B
  have hC := positive_matrix_mixture A B hA hB a b ha hb hab
  have hleft := logdet_supporting_hyperplane C A hC hA
  have hright := logdet_supporting_hyperplane C B hC hB
  have hla := mul_le_mul_of_nonneg_left hleft ha
  have hrb := mul_le_mul_of_nonneg_left hright hb
  have hgradient : a*(C⁻¹*(A-C)).trace+b*(C⁻¹*(B-C)).trace = 0 := by
    have hmix : a • (A-C)+b • (B-C) = 0 := by
      calc
        _ = (a • A+b • B)-(a+b) • C := by module
        _ = C-C := by rw [hab, one_smul]
        _ = 0 := sub_self C
    have h := congrArg (fun D : MatR n => (C⁻¹*D).trace) hmix
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
      Matrix.mul_zero, Matrix.trace_zero, smul_eq_mul] at h
    exact h
  change a*Real.log A.det+b*Real.log B.det ≤ Real.log C.det
  have hlogscale := congrArg (fun t : ℝ => t*Real.log C.det) hab
  nlinarith only [hla, hrb, hgradient, hlogscale]

/-- Actual finite SOC support feasibility is a convex set of center/positive-shape pairs. -/
theorem primal_feasible_convex (g : Fin N → V n) (β : Fin N → ℝ) :
    Convex ℝ {p : V n × MatR n | PrimalFeasible g β p.1 p.2} := by
  intro x hx y hy a b ha hb hab
  refine ⟨positive_matrix_mixture x.2 y.2 hx.1 hy.1 a b ha hb hab, ?_⟩
  intro r
  have hnorm := norm_add_le (a • Matrix.toEuclideanCLM (𝕜 := ℝ) x.2 (g r)) (b • Matrix.toEuclideanCLM (𝕜 := ℝ) y.2 (g r))
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] at hnorm
  have hleft := mul_le_mul_of_nonneg_left (hx.2 r) ha
  have hright := mul_le_mul_of_nonneg_left (hy.2 r) hb
  change ⟪g r,a • x.1+b • y.1⟫+‖Matrix.toEuclideanCLM (𝕜 := ℝ) (a • x.2+b • y.2) (g r)‖ ≤ β r
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, matrix_action_add, matrix_action_smul, matrix_action_smul]
  have hscale := congrArg (fun t : ℝ => t*β r) hab
  nlinarith only [hnorm, hleft, hright, hscale]

end SharpCut.Optimization
