import SharpCut.Stability.ResidualAlgebra
import SharpCut.Equality.Body
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # Actual Euclidean distance from the pole and latitude equality set -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix Set
namespace SharpCut.Stability
open Certificate
variable {n N : ℕ}

theorem exists_unit_transverse (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    ∃ w : V n, ‖w‖ = 1 ∧ ⟪v,w⟫ = 0 := by
  cases n with
  | zero => omega
  | succ m =>
    obtain ⟨B, hB⟩ := Geometry.exists_axial_basis v hv
    have hi : (0 : Fin (m+1)) ≠ 1 := by intro h; have := congrArg Fin.val h; simp at this; omega
    refine ⟨B 1, B.orthonormal.norm_eq_one 1, ?_⟩
    rw [← hB]
    exact B.orthonormal.inner_eq_zero hi

/-- A unit direction is chosen even at a vanishing transverse component. -/
theorem transverse_unit_direction (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1) :
    ∃ w : V n, ‖w‖ = 1 ∧ ⟪v,w⟫ = 0 ∧ transverse v u = ‖transverse v u‖ • w := by
  let y := transverse v u
  have hy : ⟪v,y⟫ = 0 := axis_transverse_inner v u hv
  by_cases hz : y = 0
  · obtain ⟨w, hw, hvw⟩ := exists_unit_transverse hn v hv
    refine ⟨w, hw, hvw, ?_⟩
    change y = ‖y‖ • w
    simp only [hz, norm_zero, zero_smul]
  · have hp : 0 < ‖y‖ := norm_pos_iff.mpr hz
    refine ⟨‖y‖⁻¹ • y, ?_, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
    · rw [real_inner_smul_right, hy, mul_zero]
    · change y = ‖y‖ • (‖y‖⁻¹ • y)
      rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

/-- Rationalization of the transverse root difference with the exact factor three. -/
theorem root_difference_sq_le (b s r q : ℝ) (hb : 0 ≤ b) (hbh : b ≤ 1/2)
    (hs : -1 ≤ s) (hsh : s ≤ 1) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hrsq : r^2 = 1-s^2) (hqsq : q^2 = 1-b^2) : (r-q)^2 ≤ 3*(s-b)^2 := by
  have hsum : (s+b)^2 ≤ 9/4 := by
    have hl : -3/2 ≤ s+b := by linarith
    have hh : s+b ≤ 3/2 := by linarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ 3/2-(s+b)) (by linarith : 0 ≤ 3/2+(s+b))]
  have hqlo : 3/4 ≤ q^2 := by nlinarith [mul_nonneg hb (sub_nonneg.mpr hbh)]
  have hprod : (r-q)^2*(r+q)^2 = (s-b)^2*(s+b)^2 := by
    calc
      _ = (r^2-q^2)^2 := by ring
      _ = (b^2-s^2)^2 := by rw [hrsq, hqsq]; ring
      _ = _ := by ring
  have hlo : q^2*(r-q)^2 ≤ (r+q)^2*(r-q)^2 :=
    mul_le_mul_of_nonneg_right (by nlinarith : q^2 ≤ (r+q)^2) (sq_nonneg _)
  have hhi := mul_le_mul_of_nonneg_left hsum (sq_nonneg (s-b))
  have hqmul := mul_le_mul_of_nonneg_right hqlo (sq_nonneg (r-q))
  nlinarith only [hprod, hlo, hhi, hqmul]

/-- An actual point of the latitude set, giving the squared-distance bound (9.7). -/
theorem latitude_comparison (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    ∃ z ∈ Equality.modelContactSet v, ‖u-z‖^2 ≤ 4*(⟪u,v⟫-inverseDimension n)^2 := by
  obtain ⟨w, hw, hvw, hy⟩ := transverse_unit_direction hn v u hv
  let b := inverseDimension n
  let q := Real.sqrt (1-b^2)
  have hb := inverseDimension_bounds hn
  have hinside : 0 ≤ 1-b^2 := by dsimp [b]; nlinarith [mul_nonneg hb.1.le (sub_nonneg.mpr hb.2)]
  have hqsq : q^2 = 1-b^2 := Real.sq_sqrt hinside
  let z := b • v+q • w
  have hzu : ‖z‖ = 1 := by
    have hh := orthogonal_combination_norm_sq v w hv hvw b q
    change ‖z‖^2 = b^2+q^2*‖w‖^2 at hh
    rw [hw, one_pow, mul_one, hqsq] at hh
    nlinarith [norm_nonneg z]
  have hzh : ⟪z,v⟫ = b := by
    have hwv : ⟪w,v⟫ = 0 := by rw [real_inner_comm]; exact hvw
    simp only [z, inner_add_left, real_inner_smul_left, hwv, real_inner_self_eq_norm_sq, hv, one_pow, mul_one, mul_zero, add_zero]
  refine ⟨z, Or.inr ⟨hzu, hzh⟩, ?_⟩
  have hud : u-z = (⟪u,v⟫-b) • v+(‖transverse v u‖-q) • w := by
    calc
      _ = (⟪u,v⟫ • v+transverse v u)-(b • v+q • w) := by unfold transverse z; abel
      _ = (⟪u,v⟫ • v+‖transverse v u‖ • w)-(b • v+q • w) :=
        congrArg (fun y : V n => (⟪u,v⟫ • v+y)-(b • v+q • w)) hy
      _ = _ := by module
  rw [hud, orthogonal_combination_norm_sq v w hv hvw, hw, one_pow, mul_one]
  have hsu := abs_le.mp (by simpa only [hu, hv, mul_one] using abs_real_inner_le_norm u v)
  have hroot := root_difference_sq_le b ⟪u,v⟫ ‖transverse v u‖ q hb.1.le hb.2 hsu.1 hsu.2
    (norm_nonneg _) (Real.sqrt_nonneg _) (transverse_norm_sq v u hv hu) hqsq
  linarith only [hroot]


/-- The equality set is never empty: the pole is always present. -/
theorem modelContactSet_nonempty (v : V n) : (Equality.modelContactSet v).Nonempty :=
  ⟨-v, Or.inl (Set.mem_singleton _)⟩

/-- The genuine infimum distance obeys the pointwise scalar residual bound (9.6). -/
theorem contact_distance_residual (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    (3/32 : ℝ)*(Metric.infDist u (Equality.modelContactSet v))^2 ≤
      (1+⟪u,v⟫)*(⟪u,v⟫-inverseDimension n)^2/(1-boostParameter n*⟪u,v⟫) := by
  let s := ⟪u,v⟫
  let b := inverseDimension n
  let a := boostParameter n
  have hb := inverseDimension_bounds hn
  have ha : 0 < a ∧ a ≤ 1/3 := Scalar.lorentz_parameter_bounds b hb.1 hb.2
  have hs := abs_le.mp (by simpa only [hu, hv, mul_one] using abs_real_inner_le_norm u v)
  have hden : 0 < 1-a*s := by
    have h := certificate_denominator_lower hn hs.2
    change 2/3 ≤ 1-a*s at h
    linarith
  have hdenupper : 1-a*s ≤ 4/3 := by
    have hh := mul_le_mul_of_nonneg_left hs.1 ha.1.le
    change a*(-1) ≤ a*s at hh
    linarith [ha.2]
  have hspos : 0 ≤ 1+s := by have hsl : -1 ≤ s := hs.1; linarith only [hsl]
  change (3/32 : ℝ)*(Metric.infDist u (Equality.modelContactSet v))^2 ≤ (1+s)*(s-b)^2/(1-a*s)
  by_cases hl : s ≤ -1/2
  · have hpole : -v ∈ Equality.modelContactSet v := Or.inl (Set.mem_singleton _)
    have hdist := Metric.infDist_le_dist_of_mem (x := u) hpole
    rw [dist_eq_norm, sub_neg_eq_add] at hdist
    have hdsq := (sq_le_sq₀ Metric.infDist_nonneg (norm_nonneg _)).mpr hdist
    have hnorm : ‖u+v‖^2 = 2*(1+s) := by rw [norm_add_sq_real, hu, hv]; dsimp [s]; ring
    rw [hnorm] at hdsq
    have hsq : 1/4 ≤ (s-b)^2 := by
      have hsb : s-b ≤ -1/2 := by linarith [hb.1]
      nlinarith [sq_nonneg (s-b+1/2)]
    have hbase := mul_le_mul_of_nonneg_left hsq hspos
    have hratio : (3/16 : ℝ)*(1+s) ≤ (1+s)*(s-b)^2/(1-a*s) := by
      apply (le_div_iff₀ hden).mpr
      have hupper := mul_le_mul_of_nonneg_left hdenupper (by positivity : 0 ≤ (3/16 : ℝ)*(1+s))
      nlinarith only [hupper, hbase]
    linarith only [hdsq, hratio]
  · have hsh : -1/2 ≤ s := le_of_lt (lt_of_not_ge hl)
    obtain ⟨z, hz, hzs⟩ := latitude_comparison hn v u hv hu
    have hdist := Metric.infDist_le_dist_of_mem (x := u) hz
    rw [dist_eq_norm] at hdist
    have hdsq := (sq_le_sq₀ Metric.infDist_nonneg (norm_nonneg _)).mpr hdist
    have hds : (Metric.infDist u (Equality.modelContactSet v))^2 ≤ 4*(s-b)^2 := hdsq.trans hzs
    have hratio : (3/8 : ℝ)*(s-b)^2 ≤ (1+s)*(s-b)^2/(1-a*s) := by
      apply (le_div_iff₀ hden).mpr
      have hupper := mul_le_mul_of_nonneg_left hdenupper (by positivity : 0 ≤ (3/8 : ℝ)*(s-b)^2)
      have hlow := mul_le_mul_of_nonneg_right (by linarith : (1/2 : ℝ) ≤ 1+s) (sq_nonneg (s-b))
      nlinarith only [hupper, hlow]
    linarith only [hds, hratio]

/-- The third bound in (9.3), using positive John weights and actual set distance. -/
theorem weighted_contact_distance_bound (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (∑ i, F.weight i*(Metric.infDist (F.contact i) (Equality.modelContactSet v))^2) ≤
      (32/3 : ℝ)*frameDefect F v := by
  have h : (3/32 : ℝ)*(∑ i, F.weight i*(Metric.infDist (F.contact i) (Equality.modelContactSet v))^2) ≤
      frameDefect F v := by
    rw [Finset.mul_sum]
    unfold frameDefect defectTerm height
    apply Finset.sum_le_sum
    intro i _
    have hp := mul_le_mul_of_nonneg_left (contact_distance_residual hn v (F.contact i) hv (F.contact_unit i)) (F.weight_pos i).le
    convert hp using 1 <;> ring
  linarith only [h]

end SharpCut.Stability
