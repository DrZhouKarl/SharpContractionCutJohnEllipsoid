import SharpCut.MatrixTools
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Order.Group

/-! # Positive-definite and determinant-increasing perturbations at the identity -/

noncomputable section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Matrix Set
namespace SharpCut.John
variable {n : ℕ}

theorem identity_smul_posDef (H : MatR n) (hH : H.IsSymm) {r : ℝ}
    (hr : 0 ≤ r) (hsmall : r*operatorNorm H < 1) : (1+r • H).PosDef := by
  have hh : H.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hH
  have hherm : (1+r • H).IsHermitian :=
    (Matrix.PosDef.one : (1 : MatR n).PosDef).isHermitian.add
      (IsSelfAdjoint.smul (.of_nonneg hr) hh)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hherm
  intro x hx
  let xE : V n := WithLp.toLp 2 x
  have hxE : xE ≠ 0 := by
    intro h; apply hx
    have he := congrArg (fun y : V n => y.ofLp) h
    simpa [xE] using he
  have hnorm := norm_pos_iff.mpr hxE
  have hcs : |⟪xE, Matrix.toEuclideanCLM (𝕜 := ℝ) H xE⟫| ≤ operatorNorm H*‖xE‖^2 := by
    calc
      _ ≤ ‖xE‖*‖Matrix.toEuclideanCLM (𝕜 := ℝ) H xE‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖xE‖*(‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖*‖xE‖) :=
        mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) H).le_opNorm xE) (norm_nonneg _)
      _ = _ := by unfold operatorNorm; ring
  have hlow := mul_le_mul_of_nonneg_left (abs_le.mp hcs).1 hr
  have hp := mul_pos (sub_pos.mpr hsmall) (pow_pos hnorm 2)
  have hquad : ⟪xE, Matrix.toEuclideanCLM (𝕜 := ℝ) (1+r • H) xE⟫ =
      ‖xE‖^2+r*⟪xE, Matrix.toEuclideanCLM (𝕜 := ℝ) H xE⟫ := by
    rw [Khachiyan.inner_matrix_action, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
      ← Khachiyan.inner_eq_dotProduct, real_inner_self_eq_norm_sq,
      Khachiyan.inner_matrix_action]
    simp only [smul_eq_mul]
  have hpos : 0 < ⟪xE, Matrix.toEuclideanCLM (𝕜 := ℝ) (1+r • H) xE⟫ := by
    rw [hquad]
    nlinarith
  simpa only [Khachiyan.inner_matrix_action, WithLp.ofLp_toLp, star_trivial] using hpos

theorem determinant_increases_near_identity (H : MatR n) (htrace : 0 < H.trace) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ r : ℝ, 0 < r → r < delta → 1 < (1+r • H).det := by
  let p : Polynomial ℝ :=
    (Matrix.det (1+(Polynomial.X : Polynomial ℝ) • H.map Polynomial.C)).divX.divX
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (-1 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) p.continuous.abs.continuousOn
  let M := |p.eval x|
  have hM : 0 ≤ M := abs_nonneg _
  have hden : 0 < M+1 := by linarith
  refine ⟨min 1 (H.trace/(M+1)), lt_min (by norm_num) (div_pos htrace hden), ?_⟩
  intro r hr hrd
  have hr1 : r ≤ 1 := (hrd.trans_le (min_le_left _ _)).le
  have hbudget : r*(M+1) < H.trace :=
    (lt_div_iff₀ hden).mp (hrd.trans_le (min_le_right _ _))
  have hbound : |p.eval r| ≤ M := hmax (show r ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hlow : -M ≤ p.eval r := (abs_le.mp hbound).1
  have hrem := mul_le_mul_of_nonneg_right hlow (sq_nonneg r)
  have hgain := mul_pos hr (show 0 < H.trace-r*M by linarith)
  have he : (1+r • H).det = 1+H.trace*r+p.eval r*r^2 := Matrix.det_one_add_smul r H
  rw [he]
  nlinarith

end SharpCut.John
