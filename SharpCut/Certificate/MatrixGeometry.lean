import SharpCut.Certificate.ReweightedShape
import SharpCut.John.MatrixPerturbation

/-! # Axial projectors and positive model/certificate scaling matrices -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Certificate
variable {n : ℕ}

def projector (v : V n) : MatR n := 1-outer v
def boostScale (n : ℕ) : ℝ := Real.sqrt (1-(boostParameter n)^2)
def certificateD (v : V n) : MatR n := boostScale n • projector v+(boostScale n)^2 • outer v
def modelF0 (v : V n) : MatR n :=
  ((2-inverseDimension n)^2/(2*(1-inverseDimension n))) • outer v+
    ((2-inverseDimension n)/2) • projector v

theorem projector_action (v u : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (projector v) u = transverse v u := by
  have ho := congrArg (fun x : V n => x.ofLp) (Khachiyan.outer_action v u)
  simp only [Khachiyan.matrix_action_ofLp, WithLp.ofLp_smul] at ho
  apply WithLp.ofLp_injective 2
  simp only [Khachiyan.matrix_action_ofLp, projector, Matrix.sub_mulVec, Matrix.one_mulVec,
    transverse, WithLp.ofLp_sub, WithLp.ofLp_smul, ho]
  rw [real_inner_comm]

theorem projector_quadratic (v u : V n) :
    ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (projector v) u⟫ = ‖u‖^2-⟪v, u⟫^2 := by
  rw [projector_action, transverse, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm v u]
  ring

theorem projector_posSemidef (v : V n) (hv : ‖v‖ = 1) : (projector v).PosSemidef := by
  have hh : (projector v).IsHermitian :=
    (Matrix.PosDef.one : (1 : MatR n).PosDef).isHermitian.sub (Khachiyan.outer_posSemidef v).isHermitian
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hh, ?_⟩
  intro x
  let xE : V n := WithLp.toLp 2 x
  have hc := abs_real_inner_le_norm v xE
  rw [hv, one_mul] at hc
  have hp := mul_nonneg (sub_nonneg.mpr hc)
    (add_nonneg (norm_nonneg xE) (abs_nonneg ⟪v, xE⟫))
  have hq : 0 ≤ ⟪xE, Matrix.toEuclideanCLM (𝕜 := ℝ) (projector v) xE⟫ := by
    rw [projector_quadratic]
    nlinarith [sq_abs ⟪v, xE⟫]
  simpa only [Khachiyan.inner_matrix_action, WithLp.ofLp_toLp, star_trivial] using hq

theorem outer_idempotent (v : V n) (hv : ‖v‖ = 1) : outer v * outer v = outer v := by
  have ha := congrArg (fun x : V n => x.ofLp) (Khachiyan.outer_action v v)
  simp only [Khachiyan.matrix_action_ofLp, WithLp.ofLp_smul,
    real_inner_self_eq_norm_sq, hv, one_pow, one_smul] at ha
  change outer v * Matrix.vecMulVec v.ofLp v.ofLp = outer v
  rw [Matrix.mul_vecMulVec, ha]
  rfl

theorem outer_mul_projector (v : V n) (hv : ‖v‖ = 1) : outer v * projector v = 0 := by
  rw [projector, Matrix.mul_sub, Matrix.mul_one, outer_idempotent v hv, sub_self]

theorem projector_mul_outer (v : V n) (hv : ‖v‖ = 1) : projector v * outer v = 0 := by
  rw [projector, Matrix.sub_mul, Matrix.one_mul, outer_idempotent v hv, sub_self]

theorem boostScale_bounds (hn : 2 ≤ n) :
    0 < boostScale n ∧ boostScale n ≤ 1 ∧ (boostScale n)^2 = 1-(boostParameter n)^2 := by
  have hb := inverseDimension_bounds hn
  have ha : 0 < boostParameter n ∧ boostParameter n ≤ 1/3 :=
    Scalar.lorentz_parameter_bounds (inverseDimension n) hb.1 hb.2
  have hm := mul_nonneg ha.1.le (sub_nonneg.mpr ha.2)
  have hinside : 0 < 1-(boostParameter n)^2 := by nlinarith
  have hp : 0 < boostScale n := Real.sqrt_pos.mpr hinside
  have hs : (boostScale n)^2 = 1-(boostParameter n)^2 := Real.sq_sqrt hinside.le
  exact ⟨hp, by nlinarith [sq_nonneg (boostParameter n)], hs⟩

theorem certificateD_posDef (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) : (certificateD v).PosDef := by
  obtain ⟨hk, hk1, hsq⟩ := boostScale_bounds hn
  have hcoeff : 0 ≤ boostScale n-(boostScale n)^2 := by
    have h := mul_nonneg hk.le (sub_nonneg.mpr hk1)
    nlinarith
  have he : certificateD v = (boostScale n)^2 • (1 : MatR n)+
      (boostScale n-(boostScale n)^2) • projector v := by
    simp only [certificateD, projector, smul_sub, sub_smul]
    abel
  rw [he]
  exact ((Matrix.PosDef.one : (1 : MatR n).PosDef).smul (pow_pos hk 2)).add_posSemidef
    ((projector_posSemidef v hv).smul hcoeff)

theorem modelF0_posDef (hn : 2 ≤ n) (v : V n) : (modelF0 v).PosDef := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have hden : 0 < 1-inverseDimension n := by linarith [hb.2]
  have heq : (2-inverseDimension n)^2/(2*(1-inverseDimension n)) =
      (2-inverseDimension n)/2+(2-inverseDimension n)/(2*(1-inverseDimension n)) := by
    field_simp [hden.ne'] <;> ring
  have he : modelF0 v = ((2-inverseDimension n)/2) • (1 : MatR n)+
      ((2-inverseDimension n)/(2*(1-inverseDimension n))) • outer v := by
    rw [modelF0, heq, projector, add_smul, smul_sub]
    abel
  rw [he]
  exact ((Matrix.PosDef.one : (1 : MatR n).PosDef).smul (half_pos hd)).add_posSemidef
    ((Khachiyan.outer_posSemidef v).smul (div_pos hd (mul_pos (by norm_num) hden)).le)

end SharpCut.Certificate
