import SharpCut.Geometry
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The one-sided Euclidean polar used for John contact necessity

This is the real polar with bound one, not the absolute polar. Its bipolar
representation is proved by strong separation for a closed convex body
containing the unit ball. No contact frame is assumed.
-/

noncomputable section
open scoped RealInnerProductSpace
open Set
namespace SharpCut.John
variable {n : ℕ}

def polar (K : Set (V n)) : Set (V n) := {u | ∀ x ∈ K, ⟪u, x⟫ ≤ 1}
def contacts (K : Set (V n)) : Set (V n) := {u | ‖u‖ = 1 ∧ u ∈ polar K}

theorem zero_mem_polar (K : Set (V n)) : (0 : V n) ∈ polar K := by
  intro x hx
  simp

theorem polar_isClosed (K : Set (V n)) : IsClosed (polar K) := by
  have he : polar K = ⋂ x ∈ K, {u : V n | ⟪u, x⟫ ≤ (1 : ℝ)} := by
    ext u; simp [polar]
  rw [he]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro hx
  exact isClosed_le (continuous_id.inner continuous_const) continuous_const

theorem polar_subset_unitBall {K : Set (V n)} (hball : unitBall n ⊆ K) :
    polar K ⊆ unitBall n := by
  intro u hu
  rw [Khachiyan.mem_unitBall]
  by_cases hzero : u = 0
  · simp [hzero]
  · have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hzero
    have hx : ‖(‖u‖⁻¹ : ℝ) • u‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']
    have hunit : (‖u‖⁻¹ : ℝ) • u ∈ unitBall n := by
      rw [Khachiyan.mem_unitBall, hx]
    have h := hu _ (hball hunit)
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, pow_two] at h
    have he : ‖u‖⁻¹ * (‖u‖ * ‖u‖) = ‖u‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ hnorm.ne', one_mul]
    rwa [he] at h

theorem polar_isCompact {K : Set (V n)} (hball : unitBall n ⊆ K) : IsCompact (polar K) :=
  IsCompact.of_isClosed_subset (isCompact_closedBall (0 : V n) 1)
    (polar_isClosed K) (polar_subset_unitBall hball)

theorem contacts_isCompact {K : Set (V n)} (hball : unitBall n ⊆ K) : IsCompact (contacts K) := by
  have he : contacts K = polar K ∩ {u : V n | ‖u‖ = 1} := by
    ext u; simp [contacts, and_comm]
  rw [he]
  exact (polar_isCompact hball).inter_right (isClosed_eq continuous_norm continuous_const)

theorem mem_of_polar_constraints {K : Set (V n)} (hK : IsConvexBody K)
    (hball : unitBall n ⊆ K) {y : V n}
    (hy : ∀ u ∈ polar K, ⟪u, y⟫ ≤ 1) : y ∈ K := by
  by_contra hout
  obtain ⟨f, c, hc, hcy⟩ := geometric_hahn_banach_closed_point hK.2.1 hK.1.isClosed hout
  have hzero : (0 : V n) ∈ K := hball (by simp [Khachiyan.mem_unitBall])
  have hcp : 0 < c := by simpa using hc 0 hzero
  let z : V n := (InnerProductSpace.toDual ℝ (V n)).symm f
  have hz (x : V n) : ⟪z, x⟫ = f x := InnerProductSpace.toDual_symm_apply
  have hup : (c⁻¹ : ℝ) • z ∈ polar K := by
    intro x hx
    rw [real_inner_smul_left, hz]
    have h := mul_lt_mul_of_pos_left (hc x hx) (inv_pos.mpr hcp)
    rw [inv_mul_cancel₀ hcp.ne'] at h
    exact h.le
  have h := hy _ hup
  rw [real_inner_smul_left, hz] at h
  have hl := mul_le_mul_of_nonneg_left h hcp.le
  rw [← mul_assoc, mul_inv_cancel₀ hcp.ne', one_mul, mul_one] at hl
  linarith

theorem bipolar_iff {K : Set (V n)} (hK : IsConvexBody K) (hball : unitBall n ⊆ K)
    (y : V n) : y ∈ K ↔ ∀ u ∈ polar K, ⟪u, y⟫ ≤ 1 :=
  ⟨fun hy _ hu => hu y hy, mem_of_polar_constraints hK hball⟩

theorem contact_mem_body {K : Set (V n)} (hball : unitBall n ⊆ K)
    {u : V n} (hu : u ∈ contacts K) : u ∈ K := by
  apply hball
  rw [Khachiyan.mem_unitBall, hu.1]

theorem contact_not_mem_interior {K : Set (V n)} {u : V n} (hu : u ∈ contacts K) :
    u ∉ interior K := by
  intro hi
  obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
  have hx : u+(e/2 : ℝ) • u ∈ Metric.ball u e := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, hu.1, mul_one, Real.norm_eq_abs,
      abs_of_pos (half_pos he)]
    exact half_lt_self he
  have hs := hu.2 _ (hball hx)
  simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hu.1, one_pow, mul_one] at hs
  linarith

theorem contact_mem_frontier {K : Set (V n)} (hball : unitBall n ⊆ K)
    {u : V n} (hu : u ∈ contacts K) : u ∈ frontier K := by
  exact ⟨subset_closure (contact_mem_body hball hu), contact_not_mem_interior hu⟩

end SharpCut.John
