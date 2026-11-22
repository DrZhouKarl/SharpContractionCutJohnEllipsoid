import SharpCut.Applications.ConstantBounds

/-! # Genuine Euclidean balls as feasible ellipsoids and their exact Lebesgue volume -/

noncomputable section
open scoped RealInnerProductSpace ENNReal MatrixOrder Matrix.Norms.L2Operator
open Matrix Set MeasureTheory
namespace SharpCut.Applications
open Certificate
variable {n : ℕ}

theorem scalar_ball_ellipsoid (c : V n) (r : ℝ) (hr : 0 < r) :
    Khachiyan.ellipsoid c (r • (1 : MatR n)) = Metric.closedBall c r := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    dsimp only
    rw [Metric.mem_closedBall, dist_eq_norm, matrix_action_smul, map_one, ContinuousLinearMap.one_apply, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have h := (Khachiyan.mem_unitBall u).mp hu
    nlinarith only [mul_le_mul_of_nonneg_left h hr.le]
  · intro hx
    let u : V n := (1/r) • (x-c)
    have hu : u ∈ unitBall n := by
      dsimp only [u]
      rw [Khachiyan.mem_unitBall, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hr)]
      have h := Metric.mem_closedBall.mp hx
      rw [dist_eq_norm] at h
      have ht : ‖x-c‖/r ≤ 1 := (div_le_iff₀ hr).mpr (by nlinarith only [h])
      convert ht using 1 <;> ring
    refine ⟨u, hu, ?_⟩
    dsimp only [u]
    rw [matrix_action_smul, map_one, ContinuousLinearMap.one_apply, smul_smul,
      show r*(1/r) = 1 by field_simp [hr.ne'], one_smul]
    abel

theorem ball_volume_eq (c : V n) (r : ℝ) (hr : 0 < r) :
    volume (Metric.closedBall c r) = ENNReal.ofReal (r^n)*volume (unitBall n) := by
  rw [← scalar_ball_ellipsoid c r hr, Khachiyan.volume_ellipsoid_eq_det (Matrix.PosDef.one.smul hr) c,
    Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]

/-- The lower bound uses an actual positive-definite feasible ball ellipsoid. -/
theorem ball_subset_max_volume {K : Set (V n)} (c : V n) (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall c r ⊆ K) :
    ENNReal.ofReal (r^n)*volume (unitBall n) ≤ maxEllipsoidVolume K := by
  have hp : IsFeasible K c (r • (1 : MatR n)) := ⟨Matrix.PosDef.one.smul hr, by rw [scalar_ball_ellipsoid c r hr]; exact hball⟩
  have h := Khachiyan.volume_le_maxEllipsoidVolume hp
  rwa [scalar_ball_ellipsoid c r hr, ball_volume_eq c r hr] at h

/-- The upper bound compares actual maximal ellipsoid volume with actual containing-ball volume. -/
theorem max_volume_subset_ball {K : Set (V n)} (c : V n) (R : ℝ) (hR : 0 < R) (hball : K ⊆ Metric.closedBall c R) :
    maxEllipsoidVolume K ≤ ENNReal.ofReal (R^n)*volume (unitBall n) := by
  have h := (Khachiyan.maxEllipsoidVolume_le_volume K).trans (measure_mono hball)
  rwa [ball_volume_eq c R hR] at h

end SharpCut.Applications
