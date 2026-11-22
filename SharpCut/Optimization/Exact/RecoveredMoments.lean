import SharpCut.Optimization.Exact.Sylvester

/-! # Full John moment recovery from the exact KKT equations -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Optimization
open Certificate
variable {n N : ℕ}

def recoveredWeight (g : Fin N → V n) (α : Fin N → ℝ) (A : MatR n) (r : Fin N) : ℝ := α r*facetLength g A r

theorem outer_scaled (r : ℝ) (u : V n) : outer (r • u) = r^2 • outer u := by
  ext i j
  simp only [Khachiyan.outer_apply, WithLp.ofLp_smul, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The recovered first moment is the actual linear image of dual balance. -/
theorem recovered_first_moment {g : Fin N → V n} {α : Fin N → ℝ} {A : MatR n}
    (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) (hbalance : ∑ r, α r • g r = 0) :
    (∑ r, recoveredWeight g α A r • facetDirection g A r) = 0 := by
  have hpoint (r : Fin N) : recoveredWeight g α A r • facetDirection g A r =
      Matrix.toEuclideanCLM (𝕜 := ℝ) A (α r • g r) := by
    have hp := facetLength_pos g A hA hg r
    rw [recoveredWeight, facetDirection, smul_smul, mul_assoc, mul_inv_cancel₀ hp.ne', mul_one, map_smul]
    rfl
  simp only [hpoint, ← map_sum, hbalance, map_zero]

/-- Ordered isotropy identity sum mu p p^T = A T A, with all scalar cancellations justified. -/
theorem recovered_second_identity {g : Fin N → V n} {α : Fin N → ℝ} {A : MatR n}
    (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) :
    (∑ r, recoveredWeight g α A r • outer (facetDirection g A r)) = A*contactMoment g α A*A := by
  have hpoint (r : Fin N) : recoveredWeight g α A r • outer (facetDirection g A r) =
      (α r/facetLength g A r) • (A*outer (g r)*A) := by
    have hp := facetLength_pos g A hA hg r
    rw [recoveredWeight, facetDirection, outer_scaled, smul_smul]
    change ((α r*facetLength g A r)*(facetLength g A r)⁻¹^2) • outer (Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)) = _
    rw [← outer_congruence A hA.isHermitian.isSymm]
    congr 1
    field_simp [hp.ne'] <;> ring
  simp only [hpoint, contactMoment, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- Positive Sylvester injectivity recovers the full noncommuting second moment. -/
theorem recovered_second_moment {g : Fin N → V n} {α : Fin N → ℝ} {q : Fin N → V n} {A : MatR n}
    (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) (hq : ∀ r, q r = α r • facetDirection g A r)
    (hM : aggregate g q = A⁻¹) :
    (∑ r, recoveredWeight g α A r • outer (facetDirection g A r)) = 1 := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  rw [recovered_second_identity hA hg, contactMoment_inverse_square hA hq hM]
  calc
    _ = (A*A⁻¹)*(A⁻¹*A) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv A hu, Matrix.nonsing_inv_mul A hu, Matrix.one_mul]

/-- Every contact direction, nonnegative weight, active support and John moment in (2.11)/(2.15). -/
theorem kkt_contact_moments {g : Fin N → V n} {β α : Fin N → ℝ} {q : Fin N → V n}
    {c : V n} {A : MatR n} (hg : ∀ r, g r ≠ 0) (hp : PrimalFeasible g β c A)
    (hd : DualFeasible g β α q) (hM : aggregate g q = A⁻¹) (hpair : ∀ r, conePairing g β α q c A r = 0) :
    (∀ r, ‖facetDirection g A r‖ = 1 ∧ 0 ≤ recoveredWeight g α A r) ∧
    (∀ r, 0 < α r → normalizedOffsets g β c r = facetLength g A r ∧ q r = α r • facetDirection g A r) ∧
    (∑ r, recoveredWeight g α A r • facetDirection g A r) = 0 ∧
    (∑ r, recoveredWeight g α A r • outer (facetDirection g A r)) = 1 ∧
    (∑ r, recoveredWeight g α A r) = (n : ℝ) ∧
    (∀ r, recoveredWeight g α A r*(normalizedOffsets g β c r-facetLength g A r) = 0) := by
  have hq := kkt_all_vectors hg hp hd hpair
  have hsecond := recovered_second_moment hp.1 hg hq hM
  refine ⟨fun r => ⟨facetDirection_unit g A hp.1 hg r,
    mul_nonneg (dual_alpha_nonneg hd r) (facetLength_pos g A hp.1 hg r).le⟩,
    kkt_active_contact hg hp hd hpair, recovered_first_moment hp.1 hg hd.balance, hsecond,
    Khachiyan.contact_weights_sum (facetDirection g A) (recoveredWeight g α A) (facetDirection_unit g A hp.1 hg) hsecond, ?_⟩
  intro r
  by_cases hz : α r = 0
  · simp only [recoveredWeight, hz, zero_mul]
  · have hα : 0 < α r := lt_of_le_of_ne (dual_alpha_nonneg hd r) (Ne.symm hz)
    rw [(kkt_active_contact hg hp hd hpair r hα).1, sub_self, mul_zero]

/-- Full Proposition 2.4, with both optimality directions and all recovered contact equations. -/
theorem kkt_optimality_and_contacts (hn : 1 ≤ n) (g : Fin N → V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hK : IsConvexBody (constraintPolytope g β))
    {c : V n} {A : MatR n} {α : Fin N → ℝ} {q : Fin N → V n}
    (hp : PrimalFeasible g β c A) (hd : DualFeasible g β α q) :
    ((PrimalOptimal g β c A ∧ DualOptimal g β α q) ↔
      aggregate g q = A⁻¹ ∧ ∀ r, conePairing g β α q c A r = 0) ∧
    ((PrimalOptimal g β c A ∧ DualOptimal g β α q) →
      (∀ r, ‖facetDirection g A r‖ = 1 ∧ 0 ≤ recoveredWeight g α A r) ∧
      (∀ r, 0 < α r → normalizedOffsets g β c r = facetLength g A r ∧ q r = α r • facetDirection g A r) ∧
      (∑ r, recoveredWeight g α A r • facetDirection g A r) = 0 ∧
      (∑ r, recoveredWeight g α A r • outer (facetDirection g A r)) = 1 ∧
      (∑ r, recoveredWeight g α A r) = (n : ℝ) ∧
      (∀ r, recoveredWeight g α A r*(normalizedOffsets g β c r-facetLength g A r) = 0)) := by
  have hi := optimality_iff_kkt hn g β hg hK hp hd
  refine ⟨hi, ?_⟩
  intro ho
  have he := hi.mp ho
  exact kkt_contact_moments hg hp hd he.1 he.2

end SharpCut.Optimization
