import SharpCut.Applications.Iteration
import SharpCut.Optimization.Exact.RecoveredMoments

/-! # Actual relative-volume stopping guarantee from a feasible normalized dual gap -/

noncomputable section
open scoped RealInnerProductSpace ENNReal MatrixOrder Matrix.Norms.L2Operator
open Matrix Set MeasureTheory
namespace SharpCut.Applications
open Optimization
variable {n N : ℕ} [NeZero n]

def optimumLogVolume (P : Set (V n)) : ℝ := Real.log ((maxEllipsoidVolume P).toReal/(volume (unitBall n)).toReal)

theorem optimumLogVolume_eq_shape {P : Set (V n)} (hP : IsConvexBody P) :
    optimumLogVolume P = Real.log (Khachiyan.johnShape P).det := by
  have hmax := Khachiyan.john_isMaxDet hP
  have hκpos := Khachiyan.unitBall_volume_pos (n := n)
  have hκfin : volume (unitBall n) < ∞ := (isCompact_closedBall (0 : V n) 1).measure_lt_top
  have hκreal : 0 < (volume (unitBall n)).toReal := ENNReal.toReal_pos_iff.mpr ⟨hκpos, hκfin⟩
  have hvol := congrArg ENNReal.toReal hmax.maxEllipsoidVolume_eq_det
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hmax.posDef.det_pos.le] at hvol
  unfold optimumLogVolume
  rw [(div_eq_iff hκreal.ne').mpr hvol]

/-- The actual optimum's normalized log-volume is bounded by every feasible certificate. -/
theorem normalized_gap_optimum_bound {g q : Fin N → V n} {β α : Fin N → ℝ} {c : V n} {A : MatR n}
    (hP : IsConvexBody (constraintPolytope g β)) (hp : PrimalFeasible g β c A) (hd : DualFeasible g β α q) :
    optimumLogVolume (constraintPolytope g β) ≤ -Real.log (aggregate g q).det ∧
      -Real.log (aggregate g q).det = Real.log A.det+dualityGap A (aggregate g q) := by
  have hmax := Khachiyan.john_isMaxDet hP
  have hprimal := (primalFeasible_iff_containment g β _ _).mpr hmax.feasible
  have hcert := (volume_certificate hprimal hd).2
  have hlog := Real.log_le_log hmax.posDef.det_pos hcert
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hd.positive.det_pos.ne', Real.log_one] at hlog
  refine ⟨?_, ?_⟩
  · rw [optimumLogVolume_eq_shape hP]
    linarith only [hlog]
  · unfold dualityGap
    ring

theorem candidate_volume_exp_ratio {g : Fin N → V n} {β : Fin N → ℝ} {c : V n} {A : MatR n}
    (hP : IsConvexBody (constraintPolytope g β)) (hp : PrimalFeasible g β c A) :
    (volume (Khachiyan.ellipsoid c A)).toReal/(maxEllipsoidVolume (constraintPolytope g β)).toReal =
      Real.exp (Real.log A.det-optimumLogVolume (constraintPolytope g β)) := by
  have hmax := Khachiyan.john_isMaxDet hP
  rw [Khachiyan.volume_ellipsoid_real_ratio hmax hp.1, optimumLogVolume_eq_shape hP,
    Real.exp_sub, Real.exp_log hp.1.det_pos, Real.exp_log hmax.posDef.det_pos]

/-- Exact relative volume guarantee (7.9)-(7.10), with the physical Lebesgue volume denominator. -/
theorem relative_volume_gap (hn : 1 ≤ n) {g q : Fin N → V n} {β α : Fin N → ℝ} {c : V n} {A : MatR n}
    (hP : IsConvexBody (constraintPolytope g β)) (hp : PrimalFeasible g β c A) (hd : DualFeasible g β α q) :
    0 < (maxEllipsoidVolume (constraintPolytope g β)).toReal ∧
    optimumLogVolume (constraintPolytope g β) ≤ -Real.log (aggregate g q).det ∧
    -Real.log (aggregate g q).det = Real.log A.det+dualityGap A (aggregate g q) ∧
    (volume (Khachiyan.ellipsoid c A)).toReal/(maxEllipsoidVolume (constraintPolytope g β)).toReal =
      Real.exp (Real.log A.det-optimumLogVolume (constraintPolytope g β)) ∧
    Real.exp (-dualityGap A (aggregate g q)) ≤
      (volume (Khachiyan.ellipsoid c A)).toReal/(maxEllipsoidVolume (constraintPolytope g β)).toReal ∧
    ENNReal.ofReal (Real.exp (-dualityGap A (aggregate g q)))*maxEllipsoidVolume (constraintPolytope g β) ≤
      volume (Khachiyan.ellipsoid c A) := by
  have hmax := Khachiyan.john_isMaxDet hP
  have hden := hmax.maxEllipsoidVolume_toReal_pos
  have ho := normalized_gap_optimum_bound hP hp hd
  have he := candidate_volume_exp_ratio hP hp
  have hratio : Real.exp (-dualityGap A (aggregate g q)) ≤
      (volume (Khachiyan.ellipsoid c A)).toReal/(maxEllipsoidVolume (constraintPolytope g β)).toReal := by
    rw [he]
    apply Real.exp_le_exp.mpr
    linarith only [ho.1, ho.2]
  have hreal := (le_div_iff₀ hden).mp hratio
  have hbound := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hP.maxEllipsoidVolume_lt_top.ne,
    ENNReal.ofReal_toReal (Khachiyan.volume_ellipsoid_lt_top c A).ne] at hbound
  exact ⟨hden, ho.1, ho.2, he, hratio, hbound⟩

/-- A requested relative accuracy can be certified by the scalar gap, without an unknown optimum. -/
theorem relative_accuracy_stop (hn : 1 ≤ n) {g q : Fin N → V n} {β α : Fin N → ℝ} {c : V n} {A : MatR n}
    (hP : IsConvexBody (constraintPolytope g β)) (hp : PrimalFeasible g β c A) (hd : DualFeasible g β α q)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hgap : dualityGap A (aggregate g q) ≤ -Real.log (1-δ)) :
    ENNReal.ofReal (1-δ)*maxEllipsoidVolume (constraintPolytope g β) ≤ volume (Khachiyan.ellipsoid c A) := by
  have hlow : 1-δ ≤ Real.exp (-dualityGap A (aggregate g q)) := by
    rw [← Real.exp_log (by linarith : 0 < 1-δ)]
    exact Real.exp_le_exp.mpr (by linarith only [hgap])
  have h := (relative_volume_gap hn hP hp hd).2.2.2.2.2
  exact (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hlow) zero_le).trans h

end SharpCut.Applications
