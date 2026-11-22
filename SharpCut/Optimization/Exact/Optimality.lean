import SharpCut.Optimization.Exact.Theorem
import SharpCut.Gap.MatrixDivergence
import SharpCut.Gap.Matching

/-! # Exact optimality iff inverse aggregate and zero cone pairings -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix Set
namespace SharpCut.Optimization
variable {n N : ℕ}

/-- A feasible inverse certificate proves the primal comparison with every feasible competitor. -/
theorem inverse_certificate_primal_optimal {g : Fin N → V n} {β α : Fin N → ℝ} {q : Fin N → V n}
    {c : V n} {A : MatR n} (hp : PrimalFeasible g β c A) (hd : DualFeasible g β α q)
    (hM : aggregate g q = A⁻¹) : PrimalOptimal g β c A := by
  refine ⟨hp, ?_⟩
  intro c' A' hp'
  apply (Real.log_le_log_iff hp'.1.det_pos hp.1.det_pos).mpr
  have h := (volume_certificate hp' hd).2
  rw [hM, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, one_div, inv_inv] at h
  exact h

/-- Every separately optimal feasible primal and dual pair has zero actual gap. -/
theorem optimal_pair_gap_zero (hn : 1 ≤ n) (g : Fin N → V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hK : IsConvexBody (constraintPolytope g β))
    {c : V n} {A : MatR n} {α : Fin N → ℝ} {q : Fin N → V n}
    (hp : PrimalOptimal g β c A) (hd : DualOptimal g β α q) : dualityGap A (aggregate g q) = 0 := by
  obtain ⟨⟨c₀, A₀, α₀, q₀, _hmax, hp₀, hd₀, _hM, _hpair, hvalue⟩, _hforall⟩ := exact_duality hn g β hg hK
  have hprimal := hp.2 c₀ A₀ hp₀.1
  have hdual := hd.2 α₀ q₀ hd₀.1
  have hgap := normalized_pair_gap_nonneg hp.1 hd.1
  unfold dualityGap at *
  linarith only [hprimal, hdual, hvalue, hgap]

/-- Zero gap is equivalent to both exact KKT equations, with all signs derived from feasibility. -/
theorem feasible_gap_zero_iff {g : Fin N → V n} {β α : Fin N → ℝ} {q : Fin N → V n}
    {c : V n} {A : MatR n} (hp : PrimalFeasible g β c A) (hd : DualFeasible g β α q) :
    dualityGap A (aggregate g q) = 0 ↔ aggregate g q = A⁻¹ ∧ ∀ r, conePairing g β α q c A r = 0 := by
  constructor
  · intro hz
    have he := normalized_pair_gap hp hd
    have hC := coneGap_nonneg hp hd
    have hD := pairDivergence_nonneg A (aggregate g q) hp.1 hd.positive
    have hzC : coneGap g β α q c A = 0 := by linarith only [hz, he, hC, hD]
    have hzD : pairDivergence A (aggregate g q) = 0 := by linarith only [hz, he, hC, hD]
    have hAeq := (Gap.pairDivergence_zero_iff A _ hp.1 hd.positive).mp hzD
    have hMeq : aggregate g q = A⁻¹ := by
      have hi : A*aggregate g q = 1 := by
        rw [hAeq]
        exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd.positive.det_pos.ne')
      exact (Matrix.inv_eq_right_inv hi).symm
    exact ⟨hMeq, (coneGap_zero_iff hp hd).mp hzC⟩
  · rintro ⟨hM, _hpair⟩
    have h := inverse_certificate_value hM
    unfold dualityGap
    linarith only [h]

/-- The optimality equivalence in Proposition 2.4; contact recovery is supplied separately. -/
theorem optimality_iff_kkt (hn : 1 ≤ n) (g : Fin N → V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hK : IsConvexBody (constraintPolytope g β))
    {c : V n} {A : MatR n} {α : Fin N → ℝ} {q : Fin N → V n}
    (hp : PrimalFeasible g β c A) (hd : DualFeasible g β α q) :
    (PrimalOptimal g β c A ∧ DualOptimal g β α q) ↔
      aggregate g q = A⁻¹ ∧ ∀ r, conePairing g β α q c A r = 0 := by
  constructor
  · rintro ⟨hpo, hdo⟩
    exact (feasible_gap_zero_iff hp hd).mp (optimal_pair_gap_zero hn g β hg hK hpo hdo)
  · rintro ⟨hM, _hpair⟩
    exact ⟨inverse_certificate_primal_optimal hp hd hM, inverse_certificate_dual_optimal hp hd hM⟩

end SharpCut.Optimization
