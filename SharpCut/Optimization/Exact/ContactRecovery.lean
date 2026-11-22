import SharpCut.Optimization.Exact.Optimality

/-! # Recovering active facet directions from zero cone pairings -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Optimization
variable {n N : ℕ}

/-- Equality in cone Cauchy-Schwarz, with all divisions justified by nonzero normals. -/
theorem positive_pairing_alignment (α τ : ℝ) (q x : V n) (hα : 0 < α) (hx : x ≠ 0)
    (hτ : ‖x‖ ≤ τ) (hq : ‖q‖ ≤ α) (hpair : α*τ-⟪q,x⟫ = 0) :
    τ = ‖x‖ ∧ q = α • (‖x‖⁻¹ • x) := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hinner := real_inner_le_norm q x
  have hprod := mul_le_mul_of_nonneg_right hq (norm_nonneg x)
  have hτα : α*τ ≤ α*‖x‖ := by nlinarith only [hinner, hprod, hpair]
  have ht : τ = ‖x‖ := le_antisymm (le_of_mul_le_mul_left hτα hα) hτ
  have hpair' : ⟪q,x⟫ = α*‖x‖ := by
    rw [ht] at hpair
    linarith only [hpair]
  have hnormq : ‖q‖ = α := by
    have hαq : α*‖x‖ ≤ ‖q‖*‖x‖ := by rw [← hpair']; exact hinner
    exact le_antisymm hq (le_of_mul_le_mul_right hαq hxpos)
  have hpunit : ‖α⁻¹ • q‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hα), hnormq, inv_mul_cancel₀ hα.ne']
  have hpinner : ⟪x,α⁻¹ • q⟫ = ‖x‖ := by
    rw [real_inner_smul_right, real_inner_comm q x]
    rw [hpair', ← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul]
  have hdir := unit_direction_of_active x (α⁻¹ • q) hx hpunit hpinner
  have hscaled := congrArg (fun u : V n => α • u) hdir
  rw [smul_smul, mul_inv_cancel₀ hα.ne', one_smul] at hscaled
  exact ⟨ht, hscaled⟩

/-- The active-support and direction conclusions of (2.15). -/
theorem kkt_active_contact {g : Fin N → V n} {β α : Fin N → ℝ} {q : Fin N → V n}
    {c : V n} {A : MatR n} (hg : ∀ r, g r ≠ 0) (hp : PrimalFeasible g β c A)
    (hd : DualFeasible g β α q) (hpair : ∀ r, conePairing g β α q c A r = 0)
    (r : Fin N) (hα : 0 < α r) :
    normalizedOffsets g β c r = facetLength g A r ∧ q r = α r • facetDirection g A r := by
  have hτ : ‖normalizedNormals g A r‖ ≤ normalizedOffsets g β c r := by
    unfold normalizedNormals normalizedOffsets
    linarith only [hp.2 r]
  have hx : normalizedNormals g A r ≠ 0 := norm_ne_zero_iff.mp (facetLength_pos g A hp.1 hg r).ne'
  exact positive_pairing_alignment (α r) (normalizedOffsets g β c r) (q r) (normalizedNormals g A r)
    hα hx hτ (hd.cone r) (hpair r)

/-- The direction identity extends to zero multipliers; the redundant facet receives zero weight. -/
theorem kkt_all_vectors {g : Fin N → V n} {β α : Fin N → ℝ} {q : Fin N → V n}
    {c : V n} {A : MatR n} (hg : ∀ r, g r ≠ 0) (hp : PrimalFeasible g β c A)
    (hd : DualFeasible g β α q) (hpair : ∀ r, conePairing g β α q c A r = 0) :
    ∀ r, q r = α r • facetDirection g A r := by
  intro r
  by_cases hz : α r = 0
  · have hq : q r = 0 := norm_eq_zero.mp (le_antisymm (by simpa only [hz] using hd.cone r) (norm_nonneg _))
    rw [hz, hq, zero_smul]
  · have hα : 0 < α r := lt_of_le_of_ne (dual_alpha_nonneg hd r) (Ne.symm hz)
    exact (kkt_active_contact hg hp hd hpair r hα).2

end SharpCut.Optimization
