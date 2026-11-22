import SharpCut.Certificate.Normalization
import SharpCut.Certificate.TransverseMoments

/-! # Explicit positive scalar factors of the actual model square root -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Certificate
variable {n : ℕ}

def modelAxialEigenvalue (n : ℕ) : ℝ := (2-inverseDimension n)^2/(2*(1-inverseDimension n))
def modelTransverseEigenvalue (n : ℕ) : ℝ := (2-inverseDimension n)/2
def modelAxialScale (n : ℕ) : ℝ := (Real.sqrt (modelAxialEigenvalue n))⁻¹
def modelTransverseScale (n : ℕ) : ℝ := (Real.sqrt (modelTransverseEigenvalue n))⁻¹

def explicitModelRoot (v : V n) : MatR n :=
  Real.sqrt (modelAxialEigenvalue n) • outer v+
    Real.sqrt (modelTransverseEigenvalue n) • projector v

def explicitModelNormalizer (v : V n) : MatR n :=
  modelAxialScale n • outer v+modelTransverseScale n • projector v

theorem modelEigenvalues_pos (hn : 2 ≤ n) :
    0 < modelAxialEigenvalue n ∧ 0 < modelTransverseEigenvalue n := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  dsimp [modelAxialEigenvalue, modelTransverseEigenvalue]
  constructor <;> positivity

theorem explicitModelRoot_square (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    explicitModelRoot v*explicitModelRoot v = modelF0 v := by
  have he := modelEigenvalues_pos hn
  have ha : Real.sqrt (modelAxialEigenvalue n)*Real.sqrt (modelAxialEigenvalue n) =
      modelAxialEigenvalue n := by rw [← pow_two, Real.sq_sqrt he.1.le]
  have ht : Real.sqrt (modelTransverseEigenvalue n)*Real.sqrt (modelTransverseEigenvalue n) =
      modelTransverseEigenvalue n := by rw [← pow_two, Real.sq_sqrt he.2.le]
  unfold explicitModelRoot
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, outer_idempotent v hv, projector_idempotent v hv,
    outer_mul_projector v hv, projector_mul_outer v hv, smul_zero, zero_add, add_zero,
    ha, ht]
  rfl

theorem modelRoot_explicit (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    modelRoot v = explicitModelRoot v := by
  have hp : (explicitModelRoot v).PosSemidef :=
    ((Khachiyan.outer_posSemidef v).smul (Real.sqrt_nonneg _)).add
      ((projector_posSemidef v hv).smul (Real.sqrt_nonneg _))
  exact CFC.sqrt_unique (explicitModelRoot_square hn v hv) hp.nonneg

theorem modelNormalizer_explicit (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    modelNormalizer v = explicitModelNormalizer v := by
  have he := modelEigenvalues_pos hn
  have ha : Real.sqrt (modelAxialEigenvalue n) ≠ 0 := (Real.sqrt_pos.mpr he.1).ne'
  have ht : Real.sqrt (modelTransverseEigenvalue n) ≠ 0 := (Real.sqrt_pos.mpr he.2).ne'
  unfold modelNormalizer
  rw [modelRoot_explicit hn v hv]
  apply Matrix.inv_eq_left_inv
  unfold explicitModelNormalizer explicitModelRoot modelAxialScale modelTransverseScale
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, outer_idempotent v hv, projector_idempotent v hv,
    outer_mul_projector v hv, projector_mul_outer v hv, smul_zero, zero_add, add_zero,
    inv_mul_cancel₀ ha, inv_mul_cancel₀ ht, mul_inv_cancel₀ ha, mul_inv_cancel₀ ht, one_smul]
  simp only [projector]
  abel

theorem modelScales_pos (hn : 2 ≤ n) : 0 < modelAxialScale n ∧ 0 < modelTransverseScale n :=
  ⟨inv_pos.mpr (Real.sqrt_pos.mpr (modelEigenvalues_pos hn).1),
    inv_pos.mpr (Real.sqrt_pos.mpr (modelEigenvalues_pos hn).2)⟩

theorem modelAxialScale_sq (hn : 2 ≤ n) :
    (modelAxialScale n)^2 = 2*(1-inverseDimension n)/(2-inverseDimension n)^2 := by
  have hb := inverseDimension_bounds hn
  unfold modelAxialScale
  rw [inv_pow, Real.sq_sqrt (modelEigenvalues_pos hn).1.le]
  simp only [modelAxialEigenvalue, inv_div]

theorem modelTransverseScale_sq (hn : 2 ≤ n) :
    (modelTransverseScale n)^2 = 2/(2-inverseDimension n) := by
  unfold modelTransverseScale
  rw [inv_pow, Real.sq_sqrt (modelEigenvalues_pos hn).2.le]
  simp only [modelTransverseEigenvalue, inv_div]

theorem modelScaleProduct_explicit (hn : 2 ≤ n) :
    modelAxialScale n*modelTransverseScale n =
      2*Real.sqrt (1-inverseDimension n)/
        ((2-inverseDimension n)*Real.sqrt (2-inverseDimension n)) := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hp := modelScales_pos hn
  have hs : (modelAxialScale n*modelTransverseScale n)^2 =
      (2*Real.sqrt (1-inverseDimension n)/
        ((2-inverseDimension n)*Real.sqrt (2-inverseDimension n)))^2 := by
    rw [mul_pow, modelAxialScale_sq hn, modelTransverseScale_sq hn, div_pow,
      mul_pow, mul_pow, Real.sq_sqrt h1.le, Real.sq_sqrt hd.le]
    field_simp [hd.ne'] <;> ring
  have hr : 0 < 2*Real.sqrt (1-inverseDimension n)/
      ((2-inverseDimension n)*Real.sqrt (2-inverseDimension n)) := by positivity
  nlinarith [mul_pos hp.1 hp.2]

theorem modelNormalizer_action (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (modelNormalizer v) u =
      (modelAxialScale n*⟪u, v⟫) • v+modelTransverseScale n • transverse v u := by
  rw [modelNormalizer_explicit hn v hv]
  apply WithLp.ofLp_injective 2
  have ho := congrArg (fun x : V n => x.ofLp) (Khachiyan.outer_action v u)
  have hp := congrArg (fun x : V n => x.ofLp) (projector_action v u)
  simp only [Khachiyan.matrix_action_ofLp, WithLp.ofLp_smul] at ho hp
  simp only [explicitModelNormalizer, Khachiyan.matrix_action_ofLp, Matrix.add_mulVec,
    Matrix.smul_mulVec, ho, hp, WithLp.ofLp_add, WithLp.ofLp_smul, smul_smul]
  rw [real_inner_comm]

theorem modelNormalizer_axis (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (modelNormalizer v) v = modelAxialScale n • v := by
  rw [modelNormalizer_action hn v v hv, transverse_axis_zero v hv,
    real_inner_self_eq_norm_sq, hv, one_pow, mul_one, smul_zero, add_zero]

theorem modelNormalizer_transverse (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1)
    (hu : ⟪v, u⟫ = 0) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (modelNormalizer v) u = modelTransverseScale n • u := by
  have hu' : ⟪u, v⟫ = 0 := by rwa [real_inner_comm]
  rw [modelNormalizer_action hn v u hv]
  simp only [transverse, hu', mul_zero, zero_smul, sub_zero, zero_add]

end SharpCut.Certificate
