import SharpCut.Applications.BallVolumes
import Khachiyan.CutIterations
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! # Actual exact-center cut iteration and retained-target-ball bound -/

noncomputable section
open scoped RealInnerProductSpace ENNReal MatrixOrder Matrix.Norms.L2Operator
open Matrix Set MeasureTheory
namespace SharpCut.Applications
variable {n : ℕ} [NeZero n]

/-- Reuse the certified geometric sequence foundation, with the paper's cut orientation. -/
theorem exact_cut_sequence_bodies (hn : 1 ≤ n) {K : ℕ → Set (V n)} (hK0 : IsConvexBody (K 0))
    {p : ℕ → V n} (hp : ∀ k, p k ≠ 0)
    (hstep : ∀ k, K (k+1) = K k ∩ centralHalfspace (Khachiyan.johnCenter (K k)) (p k)) :
    ∀ k, IsConvexBody (K k) := by
  letI : NeZero n := ⟨by omega⟩
  apply Khachiyan.centralCutSequence_isConvexBody hK0 (fun k => neg_ne_zero.mpr (hp k))
  intro k
  rw [hstep k, centralHalfspace_eq_legacy]

/-- The sharp fixed-dimensional bound, on actual maximal Lebesgue ellipsoid volume. -/
theorem exact_cut_sequence_volume (hn : 1 ≤ n) {K : ℕ → Set (V n)} (hK0 : IsConvexBody (K 0))
    {p : ℕ → V n} (hp : ∀ k, p k ≠ 0)
    (hstep : ∀ k, K (k+1) = K k ∩ centralHalfspace (Khachiyan.johnCenter (K k)) (p k)) (N : ℕ) :
    maxEllipsoidVolume (K N) ≤ ENNReal.ofReal ((sharpRatio n)^N)*maxEllipsoidVolume (K 0) := by
  letI : NeZero n := ⟨by omega⟩
  have hb := exact_cut_sequence_bodies hn hK0 hp hstep
  induction N with
  | zero => simp
  | succ N ih =>
    calc
      _ = maxEllipsoidVolume (K N ∩ centralHalfspace (Khachiyan.johnCenter (K N)) (p N)) := by rw [hstep N]
      _ ≤ ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume (K N) := (Geometry.sharp_center_cut_upper hn (hb N) (hp N)).2
      _ ≤ ENNReal.ofReal (sharpRatio n)*(ENNReal.ofReal ((sharpRatio n)^N)*maxEllipsoidVolume (K 0)) := by gcongr
      _ = _ := by rw [pow_succ', ENNReal.ofReal_mul (sharpRatio_pos hn).le, mul_assoc]

theorem containing_ball_radius_pos (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (c : V n) (R : ℝ) (hball : K ⊆ Metric.closedBall c R) : 0 < R := by
  letI : NeZero n := ⟨by omega⟩
  have hnonempty : (interior (Metric.closedBall c R)).Nonempty := hK.2.2.mono (interior_mono hball)
  rw [interior_closedBall' c R] at hnonempty
  exact Metric.nonempty_ball.mp hnonempty

/-- Positive finite unit-ball volume is established before conversion and cancellation. -/
theorem unitBall_volume_finite (hn : 1 ≤ n) : volume (unitBall n) < ∞ := by
  exact (isCompact_closedBall (0 : V n) 1).measure_lt_top

theorem retained_ball_power_bound (hn : 1 ≤ n) {K : ℕ → Set (V n)} (hK0 : IsConvexBody (K 0))
    {p : ℕ → V n} (hp : ∀ k, p k ≠ 0)
    (hstep : ∀ k, K (k+1) = K k ∩ centralHalfspace (Khachiyan.johnCenter (K k)) (p k))
    (N : ℕ) (outerCenter targetCenter : V n) (R r : ℝ) (hr : 0 < r)
    (houter : K 0 ⊆ Metric.closedBall outerCenter R) (htarget : Metric.closedBall targetCenter r ⊆ K N) :
    r^n ≤ (sharpRatio n)^N*R^n := by
  letI : NeZero n := ⟨by omega⟩
  have hR := containing_ball_radius_pos hn hK0 outerCenter R houter
  have hlow := ball_subset_max_volume targetCenter r hr htarget
  have hupper := max_volume_subset_ball outerCenter R hR houter
  have hcuts := exact_cut_sequence_volume hn hK0 hp hstep N
  have hmul := mul_le_mul_of_nonneg_left hupper (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal ((sharpRatio n)^N) from zero_le)
  have hineq : ENNReal.ofReal (r^n)*volume (unitBall n) ≤
      (ENNReal.ofReal ((sharpRatio n)^N)*ENNReal.ofReal (R^n))*volume (unitBall n) := by
    simpa only [mul_assoc] using hlow.trans (hcuts.trans hmul)
  have hκpos := Khachiyan.unitBall_volume_pos (n := n)
  have hκfin := unitBall_volume_finite hn
  have hleft : ENNReal.ofReal (r^n)*volume (unitBall n) < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hκfin
  have hright : (ENNReal.ofReal ((sharpRatio n)^N)*ENNReal.ofReal (R^n))*volume (unitBall n) < ∞ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hκfin
  have hreal := (ENNReal.toReal_le_toReal hleft.ne hright.ne).mpr hineq
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_pos hr n).le,
    ENNReal.toReal_ofReal (pow_nonneg (sharpRatio_pos hn).le N), ENNReal.toReal_ofReal (pow_pos hR n).le] at hreal
  have hκreal : 0 < (volume (unitBall n)).toReal := ENNReal.toReal_pos_iff.mpr ⟨hκpos, hκfin⟩
  exact le_of_mul_le_mul_right hreal hκreal

/-- The target-ball iteration bound in (7.2), with every logarithm/division domain proved. -/
theorem retained_ball_iteration_bound (hn : 1 ≤ n) {K : ℕ → Set (V n)} (hK0 : IsConvexBody (K 0))
    {p : ℕ → V n} (hp : ∀ k, p k ≠ 0)
    (hstep : ∀ k, K (k+1) = K k ∩ centralHalfspace (Khachiyan.johnCenter (K k)) (p k))
    (N : ℕ) (outerCenter targetCenter : V n) (R r : ℝ) (hr : 0 < r)
    (houter : K 0 ⊆ Metric.closedBall outerCenter R) (htarget : Metric.closedBall targetCenter r ⊆ K N) :
    (N : ℝ) ≤ (n : ℝ)*Real.log (R/r)/(-Real.log (sharpRatio n)) := by
  have hR := containing_ball_radius_pos hn hK0 outerCenter R houter
  have hpow := retained_ball_power_bound hn hK0 hp hstep N outerCenter targetCenter R r hr houter htarget
  have hlog := Real.log_le_log (pow_pos hr n) hpow
  rw [Real.log_mul (pow_pos (sharpRatio_pos hn) N).ne' (pow_pos hR n).ne', Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  apply (le_div_iff₀ (sharpRatio_log_decrease_pos hn)).mpr
  rw [Real.log_div hR.ne' hr.ne']
  nlinarith only [hlog]

/-- Full Corollary 7.1 for any actual exact-central-cut sequence in all positive dimensions. -/
theorem successive_exact_central_cuts (hn : 1 ≤ n) {K : ℕ → Set (V n)} (hK0 : IsConvexBody (K 0))
    {p : ℕ → V n} (hp : ∀ k, p k ≠ 0)
    (hstep : ∀ k, K (k+1) = K k ∩ centralHalfspace (Khachiyan.johnCenter (K k)) (p k)) (N : ℕ) :
    IsConvexBody (K N) ∧ 0 < maxEllipsoidVolume (K N) ∧ maxEllipsoidVolume (K N) < ∞ ∧
    maxEllipsoidVolume (K N) ≤ ENNReal.ofReal ((sharpRatio n)^N)*maxEllipsoidVolume (K 0) ∧
    (∀ outerCenter targetCenter : V n, ∀ R r : ℝ, 0 < r → K 0 ⊆ Metric.closedBall outerCenter R →
      Metric.closedBall targetCenter r ⊆ K N → (N : ℝ) ≤ (n : ℝ)*Real.log (R/r)/(-Real.log (sharpRatio n))) := by
  letI : NeZero n := ⟨by omega⟩
  have hbody := exact_cut_sequence_bodies hn hK0 hp hstep N
  exact ⟨hbody, hbody.maxEllipsoidVolume_pos, hbody.maxEllipsoidVolume_lt_top,
    exact_cut_sequence_volume hn hK0 hp hstep N, retained_ball_iteration_bound hn hK0 hp hstep N⟩


/-- The three actual-volume comparisons displayed in (7.3). -/
theorem retained_ball_volume_chain (hn : 1 ≤ n) {K : ℕ → Set (V n)} (hK0 : IsConvexBody (K 0))
    {p : ℕ → V n} (hp : ∀ k, p k ≠ 0)
    (hstep : ∀ k, K (k+1) = K k ∩ centralHalfspace (Khachiyan.johnCenter (K k)) (p k))
    (N : ℕ) (outerCenter targetCenter : V n) (R r : ℝ) (hr : 0 < r)
    (houter : K 0 ⊆ Metric.closedBall outerCenter R) (htarget : Metric.closedBall targetCenter r ⊆ K N) :
    ENNReal.ofReal (r^n)*volume (unitBall n) ≤ maxEllipsoidVolume (K N) ∧
    maxEllipsoidVolume (K N) ≤ ENNReal.ofReal ((sharpRatio n)^N)*maxEllipsoidVolume (K 0) ∧
    ENNReal.ofReal ((sharpRatio n)^N)*maxEllipsoidVolume (K 0) ≤
      ENNReal.ofReal ((sharpRatio n)^N)*(ENNReal.ofReal (R^n)*volume (unitBall n)) := by
  have hR := containing_ball_radius_pos hn hK0 outerCenter R houter
  exact ⟨ball_subset_max_volume targetCenter r hr htarget, exact_cut_sequence_volume hn hK0 hp hstep N,
    mul_le_mul_of_nonneg_left (max_volume_subset_ball outerCenter R hR houter) zero_le⟩

/-- The exact logarithmic cancellation chain (7.4), after positive finite volume comparisons. -/
theorem retained_ball_log_chain (hn : 1 ≤ n) {K : ℕ → Set (V n)} (hK0 : IsConvexBody (K 0))
    {p : ℕ → V n} (hp : ∀ k, p k ≠ 0)
    (hstep : ∀ k, K (k+1) = K k ∩ centralHalfspace (Khachiyan.johnCenter (K k)) (p k))
    (N : ℕ) (outerCenter targetCenter : V n) (R r : ℝ) (hr : 0 < r)
    (houter : K 0 ⊆ Metric.closedBall outerCenter R) (htarget : Metric.closedBall targetCenter r ⊆ K N) :
    (n : ℝ)*Real.log r ≤ (N : ℝ)*Real.log (sharpRatio n)+(n : ℝ)*Real.log R ∧
      (N : ℝ)*(-Real.log (sharpRatio n)) ≤ (n : ℝ)*Real.log (R/r) := by
  have hR := containing_ball_radius_pos hn hK0 outerCenter R houter
  have hpow := retained_ball_power_bound hn hK0 hp hstep N outerCenter targetCenter R r hr houter htarget
  have hlog := Real.log_le_log (pow_pos hr n) hpow
  rw [Real.log_mul (pow_pos (sharpRatio_pos hn) N).ne' (pow_pos hR n).ne', Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  refine ⟨hlog, ?_⟩
  rw [Real.log_div hR.ne' hr.ne']
  nlinarith only [hlog]

end SharpCut.Applications
