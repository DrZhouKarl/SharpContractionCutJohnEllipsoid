import SharpCut.Certificate.BlockConstraints

/-!
# Positive inverse interface for the direct coupling estimate

The ambient K = I+2E has axial eigenvalue one; its restriction to v-perp is
the manuscript's K_E. E annihilates the axis and all inverse operations use
the actual positive-definite matrix.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

def couplingK (F : JohnFrame n N) (v : V n) : MatR n := 1+(2 : ℝ) • transversePerturbation F v

def couplingL (F : JohnFrame n N) (v : V n) : ℝ :=
  (2-inverseDimension n)*(1-inverseDimension n)/(2-inverseDimension n+(inverseDimension n)^2)-
    (2-inverseDimension n)*transverseSigma F v/2

def couplingGamma (n : ℕ) : ℝ :=
  Real.sqrt (2-inverseDimension n)*Real.sqrt (1-inverseDimension n)/
    (2-inverseDimension n+(inverseDimension n)^2)

theorem couplingGamma_pos (hn : 2 ≤ n) : 0 < couplingGamma n := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hg : 0 < 2-inverseDimension n+(inverseDimension n)^2 := by nlinarith [sq_nonneg (inverseDimension n)]
  unfold couplingGamma
  positivity

theorem couplingGamma_sq (hn : 2 ≤ n) :
    (couplingGamma n)^2 = (2-inverseDimension n)*(1-inverseDimension n)/
      (2-inverseDimension n+(inverseDimension n)^2)^2 := by
  have hb := inverseDimension_bounds hn
  unfold couplingGamma
  rw [div_pow, mul_pow, Real.sq_sqrt (by linarith [hb.2] : 0 ≤ 2-inverseDimension n),
    Real.sq_sqrt (by linarith [hb.2] : 0 ≤ 1-inverseDimension n)]

theorem couplingL_nonneg (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    0 ≤ couplingL F v := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have h := mul_le_mul_of_nonneg_left (transverseSigma_range F hn v hv).2 (div_pos hd (by norm_num : (0 : ℝ) < 2)).le
  unfold couplingL
  have he : ((2-inverseDimension n)/2)*(2*(1-inverseDimension n)/
      (2-inverseDimension n+(inverseDimension n)^2)) =
      (2-inverseDimension n)*(1-inverseDimension n)/(2-inverseDimension n+(inverseDimension n)^2) := by ring
  rw [he] at h
  linarith only [h]

theorem couplingK_gram (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    couplingK F v = outer v+((2+inverseDimension n)/(2-inverseDimension n)) • transverseMinusMoment F v := by
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hp : 2+inverseDimension n ≠ 0 := by linarith [hb.1]
  rw [transverseMinusMoment_identity F hn v hv, smul_smul]
  have he : ((2+inverseDimension n)/(2-inverseDimension n))*
      ((2-inverseDimension n)/(2+inverseDimension n)) = 1 := by field_simp [hd, hp]
  rw [he, one_smul, couplingK, projector]
  abel

theorem couplingK_posDef (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (couplingK F v).PosDef := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have hp : 0 < 2+inverseDimension n := by linarith [hb.1]
  have hc : 0 < (2+inverseDimension n)/(2-inverseDimension n) := div_pos hp hd
  have hpsd : (couplingK F v).PosSemidef := by
    rw [couplingK_gram F hn v hv]
    exact (Khachiyan.outer_posSemidef v).add ((transverseMinusMoment_posSemidef F hn v hv).smul hc.le)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.isHermitian
  intro x hx
  let u : V n := WithLp.toLp 2 x
  have hu0 : u ≠ 0 := by
    intro h; apply hx
    have he := congrArg (fun y : V n => y.ofLp) h
    simpa [u] using he
  have he : ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (couplingK F v) u⟫ =
      ⟪u, v⟫^2+((2+inverseDimension n)/(2-inverseDimension n))*
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (transverseMinusMoment F v) u⟫ := by
    rw [couplingK_gram F hn v hv, matrix_action_add, matrix_action_smul,
      inner_add_right, real_inner_smul_right, Khachiyan.outer_action, real_inner_smul_right]
    rw [real_inner_comm v u]
    ring
  have hpos : 0 < ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (couplingK F v) u⟫ := by
    by_cases hu : ⟪u, v⟫ = 0
    · rw [he, hu, zero_pow (by decide : 2 ≠ 0), zero_add]
      exact mul_pos hc (transverseMinusMoment_positive F hn v u hv hu hu0)
    · have hs := sq_pos_of_ne_zero hu
      have hm : 0 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (transverseMinusMoment F v) u⟫ := by
        simpa only [Khachiyan.inner_matrix_action, star_trivial] using
          (transverseMinusMoment_posSemidef F hn v hv).dotProduct_mulVec_nonneg u.ofLp
      rw [he]
      exact add_pos_of_pos_of_nonneg hs (mul_nonneg hc.le hm)
  simpa only [Khachiyan.inner_matrix_action, WithLp.ofLp_toLp, star_trivial] using hpos

theorem couplingK_axis (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (couplingK F v) v = v := by
  simp only [couplingK, matrix_action_add, matrix_action_smul, map_one,
    ContinuousLinearMap.one_apply, transversePerturbation_axis F hn v hv, smul_zero, add_zero]

theorem couplingK_inv_axis (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (couplingK F v)⁻¹ v = v := by
  have h := Determinant.posDef_inverse_action (couplingK F v) (couplingK_posDef F hn v hv) v
  rwa [couplingK_axis F hn v hv] at h

theorem couplingK_inv_transverse (F : JohnFrame n N) (hn : 2 ≤ n)
    (v u : V n) (hv : ‖v‖ = 1) (hu : ⟪u, v⟫ = 0) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (couplingK F v)⁻¹ u, v⟫ = 0 := by
  rw [real_inner_comm, Khachiyan.inner_matrix_action_symm (couplingK_posDef F hn v hv).inv.isHermitian.isSymm,
    couplingK_inv_axis F hn v hv, real_inner_comm]
  exact hu

end SharpCut.Certificate
