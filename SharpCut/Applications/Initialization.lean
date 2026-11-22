import SharpCut.Applications.Stopping
import Mathlib.Analysis.Asymptotics.Defs

/-! # The explicit inner-ball and O(n) radius-ratio initialization after a central cut -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix Set
namespace SharpCut.Applications
variable {n : ℕ} [NeZero n]

def postCutCoordinates (v x : V n) : V n := (8 : ℝ) • (x+(1/4 : ℝ) • v)
def initializationRatio (n : ℕ) : ℝ := 8*(n : ℝ)+2

/-- John contact necessity derives the ordinary n-radius rounding bound. -/
theorem normalized_body_norm_bound (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K) (hJ : IsJohnNormalized K)
    {x : V n} (hx : x ∈ K) : ‖x‖ ≤ (n : ℝ) := by
  obtain ⟨N, F, hs⟩ := John.exists_supporting_frame hn hK hJ
  exact F.norm_le_dimension_of_mem_polytope (F.supporting_subset hs hx)

/-- The literal inner-ball inclusion in (7.7), with the paper's center and radius. -/
theorem post_cut_inner_ball (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K) (hJ : IsJohnNormalized K)
    (v : V n) (hv : ‖v‖ = 1) :
    Metric.closedBall ((-1/4 : ℝ) • v) (1/8 : ℝ) ⊆ K ∩ centralHalfspace 0 v := by
  have hball : unitBall n ⊆ K := by simpa only [Khachiyan.ellipsoid_zero_one] using hJ.subset
  intro x hx
  have hnorm : ‖x+(1/4 : ℝ) • v‖ ≤ 1/8 := by
    have h := Metric.mem_closedBall.mp hx
    rw [dist_eq_norm] at h
    simpa only [neg_div, neg_smul, sub_neg_eq_add] using h
  have hxnorm : ‖x‖ ≤ 3/8 := by
    have h := norm_sub_le (x+(1/4 : ℝ) • v) ((1/4 : ℝ) • v)
    rw [add_sub_cancel_right, norm_smul, hv, mul_one] at h
    norm_num at h
    linarith only [h, hnorm]
  have hinner := real_inner_le_norm v (x+(1/4 : ℝ) • v)
  rw [hv, one_mul, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow, mul_one] at hinner
  refine ⟨hball ((Khachiyan.mem_unitBall x).mpr (by linarith only [hxnorm])), ?_⟩
  simp only [mem_centralHalfspace, sub_zero]
  linarith only [hinner, hnorm]

/-- The unit ball is contained in the explicit translated/scaled next-subproblem coordinates. -/
theorem post_cut_unitBall_subset (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K) (hJ : IsJohnNormalized K)
    (v : V n) (hv : ‖v‖ = 1) : unitBall n ⊆ postCutCoordinates v '' (K ∩ centralHalfspace 0 v) := by
  intro u hu
  let x : V n := (1/8 : ℝ) • u-(1/4 : ℝ) • v
  have hxball : x ∈ Metric.closedBall ((-1/4 : ℝ) • v) (1/8 : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have he : x-(-1/4 : ℝ) • v = (1/8 : ℝ) • u := by dsimp only [x]; module
    rw [he, norm_smul]
    norm_num
    nlinarith only [(Khachiyan.mem_unitBall u).mp hu]
  refine ⟨x, post_cut_inner_ball hn hK hJ v hv hxball, ?_⟩
  dsimp only [postCutCoordinates, x]
  module

/-- The exact 8n+2 outer radius in (7.8), derived from the actual John rounding. -/
theorem post_cut_outer_ball (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K) (hJ : IsJohnNormalized K)
    (v : V n) (hv : ‖v‖ = 1) : postCutCoordinates v '' (K ∩ centralHalfspace 0 v) ⊆ Metric.closedBall 0 (initializationRatio n) := by
  rintro y ⟨x, hx, rfl⟩
  have hxnorm := normalized_body_norm_bound hn hK hJ hx.1
  have ht := norm_add_le x ((1/4 : ℝ) • v)
  rw [norm_smul, hv, mul_one] at ht
  norm_num at ht
  rw [Metric.mem_closedBall, dist_zero_right]
  dsimp only [postCutCoordinates, initializationRatio]
  rw [norm_smul]
  norm_num
  nlinarith only [hxnorm, ht]

theorem initializationRatio_le_ten (hn : 1 ≤ n) : initializationRatio n ≤ 10*(n : ℝ) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold initializationRatio
  linarith only [hnr]

/-- The O(n) assertion uses a genuine eventual bound, not an informal constant comparison. -/
theorem initializationRatio_isBigO : initializationRatio =O[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 10
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  letI : NeZero n := ⟨by omega⟩
  have h := initializationRatio_le_ten hn
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr : 0 ≤ initializationRatio n := by unfold initializationRatio; positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnr, abs_of_nonneg hr] using h

/-- Complete initialization scope: physical inner ball, coordinate radius ratio and dimension-order bound. -/
theorem central_cut_initialization (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K) (hJ : IsJohnNormalized K)
    (v : V n) (hv : ‖v‖ = 1) :
    Metric.closedBall ((-1/4 : ℝ) • v) (1/8 : ℝ) ⊆ K ∩ centralHalfspace 0 v ∧
    unitBall n ⊆ postCutCoordinates v '' (K ∩ centralHalfspace 0 v) ∧
    postCutCoordinates v '' (K ∩ centralHalfspace 0 v) ⊆ Metric.closedBall 0 (8*(n : ℝ)+2) ∧
    initializationRatio n ≤ 10*(n : ℝ) ∧ initializationRatio =O[Filter.atTop] (fun n : ℕ => (n : ℝ)) :=
  ⟨post_cut_inner_ball hn hK hJ v hv, post_cut_unitBall_subset hn hK hJ v hv, post_cut_outer_ball hn hK hJ v hv,
    initializationRatio_le_ten hn, initializationRatio_isBigO⟩

end SharpCut.Applications
