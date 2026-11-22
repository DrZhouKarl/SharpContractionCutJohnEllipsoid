import SharpCut.Optimization.Convexity
import SharpCut.Applications.BallVolumes
import Mathlib.Data.EReal.Basic

/-! # Exact log-determinant Lagrangian conjugate, including infinite branches -/

noncomputable section
open scoped RealInnerProductSpace BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
open Matrix Set MeasureTheory
namespace SharpCut.Optimization
variable {n N : ℕ}
attribute [local instance] Classical.propDecidable

def lagrangian (B : V n) (M : MatR n) (s : ℝ) (c : V n) (A : MatR n) : ℝ :=
  Real.log A.det-(A*M).trace-⟪B,c⟫+s

def lagrangianValues (B : V n) (M : MatR n) (s : ℝ) : Set EReal :=
  {z | ∃ c A, A.PosDef ∧ z = (lagrangian B M s c A : EReal)}

def lagrangianSupremum (B : V n) (M : MatR n) (s : ℝ) : EReal :=
  sSup (lagrangianValues B M s)

theorem logdet_conjugate_bound (M A : MatR n) (hM : M.PosDef) (hA : A.PosDef) :
    Real.log A.det-(A*M).trace ≤ -(n : ℝ)-Real.log M.det := by
  have h := logdet_supporting_hyperplane M⁻¹ A hM.inv hA
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv,
    Matrix.nonsing_inv_nonsing_inv M (isUnit_iff_ne_zero.mpr hM.det_pos.ne')] at h
  rw [Matrix.mul_sub, Matrix.trace_sub,
    Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM.det_pos.ne'),
    Matrix.trace_one, Fintype.card_fin, Matrix.trace_mul_comm M A] at h
  linarith only [h]

theorem logdet_conjugate_attained (M : MatR n) (hM : M.PosDef) :
    Real.log M⁻¹.det-(M⁻¹*M).trace = -(n : ℝ)-Real.log M.det := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv,
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM.det_pos.ne'), Matrix.trace_one, Fintype.card_fin]
  ring

theorem lagrangian_finite_value (M : MatR n) (hM : M.PosDef) (s : ℝ) :
    lagrangianSupremum 0 M s = (s-(n : ℝ)-Real.log M.det : EReal) ∧
      lagrangian 0 M s 0 M⁻¹ = s-(n : ℝ)-Real.log M.det := by
  have he : lagrangian 0 M s 0 M⁻¹ = s-(n : ℝ)-Real.log M.det := by
    simp only [lagrangian, inner_zero_left, sub_zero]
    linarith only [logdet_conjugate_attained M hM]
  refine ⟨le_antisymm ?_ ?_, he⟩
  · apply sSup_le
    rintro z ⟨c, A, hA, rfl⟩
    apply EReal.coe_le_coe_iff.mpr
    simp only [lagrangian, inner_zero_left, sub_zero]
    linarith only [logdet_conjugate_bound M A hM hA]
  · unfold lagrangianSupremum
    apply le_sSup
    exact ⟨0, M⁻¹, hM.inv, congrArg (fun r : ℝ => (r : EReal)) he.symm⟩

theorem unbalanced_lagrangian_unbounded (B : V n) (hB : B ≠ 0) (M : MatR n) (s R : ℝ) :
    ∃ c A, A.PosDef ∧ R < lagrangian B M s c A := by
  have hp : 0 < ‖B‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hB)
  let c := -((R+M.trace-s+1)/‖B‖^2) • B
  have he : lagrangian B M s c 1 = R+1 := by
    dsimp only [lagrangian, c]
    rw [Matrix.det_one, Real.log_one, Matrix.one_mul, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp [hp.ne']
    ring
  exact ⟨c, 1, Matrix.PosDef.one, by rw [he]; linarith⟩

theorem nonpositive_lagrangian_unbounded (hn : 1 ≤ n) (M : MatR n)
    (hM : M.IsHermitian) (hbad : ¬ M.PosDef) (s R : ℝ) :
    ∃ c A, A.PosDef ∧ R < lagrangian 0 M s c A := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, hM.eigenvalues i ≤ 0 := by
    by_contra h
    apply hbad
    rw [hM.posDef_iff_eigenvalues_pos]
    exact fun i => lt_of_not_ge (not_exists.mp h i)
  let v : V n := hM.eigenvectorBasis i
  have hv : ‖v‖ = 1 := hM.eigenvectorBasis.orthonormal.1 i
  have heig : Matrix.toEuclideanCLM (𝕜 := ℝ) M v = (hM.eigenvalues i) • v := by
    apply WithLp.ofLp_injective 2
    simpa only [v, Khachiyan.matrix_action_ofLp, WithLp.ofLp_smul] using hM.mulVec_eigenvectorBasis i
  let t : ℝ := Real.exp (max (R+M.trace-s+1) 0)
  have ht : 1 ≤ t := by
    have h := Real.exp_le_exp.mpr (le_max_right (R+M.trace-s+1) 0)
    simpa only [Real.exp_zero] using h
  have htp : 0 < t := Real.exp_pos _
  let A : MatR n := 1+(t-1) • outer v
  have hA : A.PosDef := Matrix.PosDef.one.add_posSemidef ((Khachiyan.outer_posSemidef v).smul (by linarith))
  have hdet : A.det = t := by
    have h := Certificate.det_axial_update hn v hv 1 (t-1) (by norm_num)
    calc
      A.det = 1+(t-1) := by simpa only [one_smul, one_pow, one_mul] using h
      _ = t := by ring
  have htrace : (A*M).trace = M.trace+(t-1)*hM.eigenvalues i := by
    have houter : (M*outer v).trace = ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) M v⟫ := by
      have ho : outer v = Matrix.vecMulVec v.ofLp v.ofLp := by ext a b; rfl
      rw [ho]
      exact trace_mul_cross M v v
    dsimp only [A]
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_mul_comm (outer v) M, houter, heig, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hv, one_pow, mul_one, smul_eq_mul]
  have hneg : (t-1)*hM.eigenvalues i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hi
  have hlog : Real.log t = max (R+M.trace-s+1) 0 := Real.log_exp _
  refine ⟨0, A, hA, ?_⟩
  simp only [lagrangian, hdet, htrace, inner_zero_left, sub_zero, hlog]
  linarith only [hneg, le_max_left (R+M.trace-s+1) 0]

theorem lagrangianSupremum_top_of_unbounded (B : V n) (M : MatR n) (s : ℝ)
    (h : ∀ R : ℝ, ∃ c A, A.PosDef ∧ R < lagrangian B M s c A) :
    lagrangianSupremum B M s = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro R
  obtain ⟨c, A, hA, hR⟩ := h R
  exact (EReal.coe_lt_coe_iff.mpr hR).trans_le
    (le_sSup (show (lagrangian B M s c A : EReal) ∈ lagrangianValues B M s from ⟨c, A, hA, rfl⟩))

/-- The finite and both infinite cases of (10.2), using the complete EReal supremum. -/
theorem lagrangian_conjugate (hn : 1 ≤ n) (B : V n) (M : MatR n) (hM : M.IsHermitian) (s : ℝ) :
    lagrangianSupremum B M s =
      if B = 0 ∧ M.PosDef then (s-(n : ℝ)-Real.log M.det : EReal) else ⊤ := by
  classical
  by_cases hB : B = 0
  · subst B
    by_cases hp : M.PosDef
    · simpa only [eq_self, true_and, ite_eq_left hp] using (lagrangian_finite_value M hp s).1
    · simp only [eq_self, true_and, ite_eq_right hp]
      exact lagrangianSupremum_top_of_unbounded 0 M s (nonpositive_lagrangian_unbounded hn M hM hp s)
  · simp only [hB, false_and, ite_false]
    exact lagrangianSupremum_top_of_unbounded B M s (unbalanced_lagrangian_unbounded B hB M s)

end SharpCut.Optimization
