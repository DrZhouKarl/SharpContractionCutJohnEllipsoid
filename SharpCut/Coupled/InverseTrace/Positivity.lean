import SharpCut.Coupled.InverseTrace.Completion

/-! # Positive effective matrix forced by universal rank-one tests -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Coupled.InverseTrace
open Certificate
variable {n : ℕ}

theorem outer_square (w : V n) : (outer w)^2 = ‖w‖^2 • outer w := by
  rw [pow_two, mul_outer_eq_cross, Khachiyan.outer_action, real_inner_self_eq_norm_sq,
    cross_smul_left, cross_self]

theorem completed_rank_one (R : MatR n) (j w : V n) (β η : ℝ) :
    completedLinear R j β (outer w) 0 = ⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) R w⟫-β*‖w‖^2 ∧
    completedQuadratic R η (outer w) 0 = ‖w‖^2*⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) R w⟫ := by
  unfold completedLinear completedQuadratic
  have htrace : (outer w*R).trace = ⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) R w⟫ := by
    rw [Matrix.trace_mul_comm]
    exact trace_outer_linear R w
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
    Khachiyan.trace_outer, inner_zero_left, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    add_zero, outer_square, Matrix.smul_mul, smul_eq_mul, htrace]
  simp

/-- Strict positivity is a consequence of the inequality itself, not a hypothesis. -/
theorem all_completed_tests_posDef (R : MatR n) (j : V n) (β η σ : ℝ) (hR : R.IsHermitian)
    (hβ : 0 < β) (hσ : 0 < σ) (h : AllCompletedTests R j β η σ) : R.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hR
  intro x hx
  let w : V n := WithLp.toLp 2 x
  have hw : w ≠ 0 := by
    intro hz
    apply hx
    have he := congrArg (fun u : V n => u.ofLp) hz
    simpa only [w, WithLp.ofLp_toLp, WithLp.ofLp_zero] using he
  have hn : 0 < ‖w‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  have ht := h (outer w) (Khachiyan.outer_posSemidef w).isHermitian 0
  rw [(completed_rank_one R j w β η).1, (completed_rank_one R j w β η).2] at ht
  have hquad : 0 < ⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) R w⟫ := by
    by_contra hc
    have hnonpos : ⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) R w⟫ ≤ 0 := le_of_not_gt hc
    have hprod := mul_nonpos_of_nonneg_of_nonpos hn.le hnonpos
    have hscaled := mul_nonpos_of_nonneg_of_nonpos hσ.le hprod
    have hz : (⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) R w⟫-β*‖w‖^2)^2 = 0 :=
      le_antisymm (ht.trans hscaled) (sq_nonneg _)
    have he := sq_eq_zero_iff.mp hz
    have hp := mul_pos hβ hn
    linarith only [he, hp, hnonpos]
  simpa only [Khachiyan.inner_matrix_action, w, WithLp.ofLp_toLp, star_trivial] using hquad

end SharpCut.Coupled.InverseTrace
