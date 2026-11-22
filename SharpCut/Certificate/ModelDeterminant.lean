import SharpCut.Certificate.MatrixGeometry
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Exact axial model determinants in arbitrary positive dimensions -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Certificate
variable {n : ℕ}

theorem det_one_add_cross (u w : V n) :
    (1+Matrix.vecMulVec u.ofLp w.ofLp).det = 1+⟪w, u⟫ := by
  have he : Matrix.vecMulVec u.ofLp w.ofLp =
      Matrix.replicateCol Unit u.ofLp*Matrix.replicateRow Unit w.ofLp := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  rw [he, Matrix.det_one_add_replicateCol_mul_replicateRow, Khachiyan.inner_eq_dotProduct]

theorem det_axial_update {n : ℕ} (hn : 1 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (r s : ℝ) (hr : r ≠ 0) :
    (r • (1 : MatR n)+s • outer v).det = r^(n-1)*(r+s) := by
  have he : r • (1 : MatR n)+s • outer v =
      r • (1+Matrix.vecMulVec ((s/r) • v).ofLp v.ofLp) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, WithLp.ofLp_smul,
      Pi.smul_apply, Khachiyan.outer_apply, smul_eq_mul]
    field_simp [hr] <;> ring
  rw [he, Matrix.det_smul, Fintype.card_fin, det_one_add_cross]
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow, mul_one]
  have hp : r^n = r^(n-1)*r := by
    conv_lhs => rw [show n = (n-1)+1 by omega, pow_succ]
  rw [hp]
  field_simp [hr] <;> ring

def inverseModel (v : V n) : MatR n :=
  (2 : ℝ) • outer v+Real.sqrt (1-inverseDimension n) • projector v

theorem projector_idempotent (v : V n) (hv : ‖v‖ = 1) : projector v*projector v = projector v := by
  rw [projector, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    outer_idempotent v hv]
  abel

theorem boostScale_explicit (hn : 2 ≤ n) :
    boostScale n = 2*Real.sqrt (1-inverseDimension n)/(2-inverseDimension n) := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have hr : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hk := boostScale_bounds hn
  have he : 1-(boostParameter n)^2 = 4*(1-inverseDimension n)/(2-inverseDimension n)^2 :=
    lorentz_parameter_square (inverseDimension n) hd.ne'
  have hs : (2*Real.sqrt (1-inverseDimension n)/(2-inverseDimension n))^2 =
      4*(1-inverseDimension n)/(2-inverseDimension n)^2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hr.le]
    norm_num
  have hp : 0 < 2*Real.sqrt (1-inverseDimension n)/(2-inverseDimension n) :=
    div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hr)) hd
  nlinarith [hk.2.2]

theorem modelF0_mul_D (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    modelF0 v*certificateD v = inverseModel v := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have hr : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hax : ((2-inverseDimension n)^2/(2*(1-inverseDimension n)))*(boostScale n)^2 = 2 := by
    have hs : (boostScale n)^2 = 4*(1-inverseDimension n)/(2-inverseDimension n)^2 :=
      (boostScale_bounds hn).2.2.trans (lorentz_parameter_square (inverseDimension n) hd.ne')
    rw [hs]
    field_simp [hd.ne', hr.ne']
    norm_num
  have htr : ((2-inverseDimension n)/2)*boostScale n = Real.sqrt (1-inverseDimension n) := by
    rw [boostScale_explicit hn]
    field_simp [hd.ne']
  have hax' : (boostScale n)^2*((2-inverseDimension n)^2/(2*(1-inverseDimension n))) = 2 := by
    simpa only [mul_comm] using hax
  have htr' : boostScale n*((2-inverseDimension n)/2) = Real.sqrt (1-inverseDimension n) := by
    simpa only [mul_comm] using htr
  unfold modelF0 certificateD inverseModel
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    outer_mul_projector v hv, projector_mul_outer v hv, outer_idempotent v hv,
    projector_idempotent v hv, smul_zero, zero_add, add_zero, hax', htr']
  rw [add_comm]

theorem inverseModel_det (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (inverseModel v).det = 2*(Real.sqrt (1-inverseDimension n))^(n-1) := by
  have hb := inverseDimension_bounds hn
  have hs : 0 < Real.sqrt (1-inverseDimension n) := Real.sqrt_pos.mpr (by linarith [hb.2])
  have he : inverseModel v = Real.sqrt (1-inverseDimension n) • (1 : MatR n)+
      (2-Real.sqrt (1-inverseDimension n)) • outer v := by
    simp only [inverseModel, projector, smul_sub, sub_smul]
    abel
  rw [he, det_axial_update (by omega) v hv _ _ hs.ne']
  ring

theorem sharpRatio_inverseModel (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    sharpRatio n*(inverseModel v).det = 1 := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hnsub : (0 : ℝ) < (n : ℝ)-1 := by linarith
  let u := 1-inverseDimension n
  have hu : 0 < u := by dsimp [u]; linarith [(inverseDimension_bounds hn).2]
  have hbase : (n : ℝ)/((n : ℝ)-1) = u⁻¹ := by
    dsimp [u, inverseDimension]
    field_simp [hnp.ne', hnsub.ne']
  have hp : (Real.sqrt u)^(n-1) = u^(((n : ℝ)-1)/2) := by
    rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hu.le]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    ring
  rw [inverseModel_det hn v hv]
  simp only [sharpRatio, if_neg hn0, if_neg hn1]
  change 1/2*((n : ℝ)/((n : ℝ)-1))^(((n : ℝ)-1)/2)*(2*(Real.sqrt u)^(n-1)) = 1
  rw [hbase, hp, Real.inv_rpow hu.le]
  have hnz : u^(((n : ℝ)-1)/2) ≠ 0 := (Real.rpow_pos_of_pos hu _).ne'
  field_simp [hnz]

theorem model_determinant_normalization (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    sharpRatio n*(modelF0 v).det*(certificateD v).det = 1 := by
  rw [mul_assoc, ← Matrix.det_mul, modelF0_mul_D hn v hv]
  exact sharpRatio_inverseModel hn v hv

end SharpCut.Certificate
