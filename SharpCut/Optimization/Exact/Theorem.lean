import SharpCut.Optimization.Exact.Multipliers

/-! # Attained exact primal-dual log-determinant optimization

Optimality means comparison with every feasible competitor of the actual
finite SOC log-determinant problems. Both attained optima are constructed;
no strong-duality or multiplier-existence premise is introduced.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix Set
namespace SharpCut.Optimization
variable {n N : ℕ}

def PrimalOptimal (g : Fin N → V n) (β : Fin N → ℝ) (c : V n) (A : MatR n) : Prop :=
  PrimalFeasible g β c A ∧ ∀ c' A', PrimalFeasible g β c' A' → Real.log A'.det ≤ Real.log A.det

def DualOptimal (g : Fin N → V n) (β α : Fin N → ℝ) (q : Fin N → V n) : Prop :=
  DualFeasible g β α q ∧ ∀ α' q', DualFeasible g β α' q' → Real.log (aggregate g q').det ≤ Real.log (aggregate g q).det

/-- The primal optimum is exactly the genuine maximal-volume ellipsoid shape optimum. -/
theorem primalOptimal_iff_isMaxDet (g : Fin N → V n) (β : Fin N → ℝ) (c : V n) (A : MatR n) :
    PrimalOptimal g β c A ↔ IsMaxDet (constraintPolytope g β) c A := by
  constructor
  · rintro ⟨hp, hopt⟩
    refine ⟨(primalFeasible_iff_containment g β c A).mp hp, ?_⟩
    intro c' A' hA'
    have hprimal := (primalFeasible_iff_containment g β c' A').mpr hA'
    exact (Real.log_le_log_iff hA'.1.det_pos hp.1.det_pos).mp (hopt c' A' hprimal)
  · intro hmax
    refine ⟨(primalFeasible_iff_containment g β c A).mpr hmax.feasible, ?_⟩
    intro c' A' hp'
    apply (Real.log_le_log_iff hp'.1.det_pos hmax.posDef.det_pos).mpr
    exact hmax.det_le c' A' ((primalFeasible_iff_containment g β c' A').mp hp')

/-- Feasibility and the constructed inverse aggregate imply dual optimality against every competitor. -/
theorem inverse_certificate_dual_optimal {g : Fin N → V n} {β α : Fin N → ℝ} {q : Fin N → V n}
    {c : V n} {A : MatR n} (hp : PrimalFeasible g β c A) (hd : DualFeasible g β α q)
    (hM : aggregate g q = A⁻¹) : DualOptimal g β α q := by
  refine ⟨hd, ?_⟩
  intro α' q' hd'
  apply (Real.log_le_log_iff hd'.positive.det_pos hd.positive.det_pos).mpr
  have hmul := det_mul_le_one_of_trace hp.1 hd'.positive (trace_bound hp hd')
  have hdet : (aggregate g q').det ≤ 1/A.det := by
    apply (le_div_iff₀ hp.1.det_pos).mpr
    nlinarith only [hmul]
  rw [hM, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  simpa only [one_div] using hdet

/-- The exact sum of attained primal and normalized dual objective values. -/
theorem inverse_certificate_value {g : Fin N → V n} {q : Fin N → V n} {A : MatR n}
    (hM : aggregate g q = A⁻¹) : Real.log A.det+Real.log (aggregate g q).det = 0 := by
  rw [hM, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv]
  ring

/-- Every actual John optimum admits attained optimal multipliers with all zero cone pairings. -/
theorem optimal_multipliers (hn : 1 ≤ n) (g : Fin N → V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hK : IsConvexBody (constraintPolytope g β))
    {c : V n} {A : MatR n} (hmax : IsMaxDet (constraintPolytope g β) c A) :
    ∃ α : Fin N → ℝ, ∃ q : Fin N → V n,
      DualOptimal g β α q ∧ aggregate g q = A⁻¹ ∧ (∀ r, conePairing g β α q c A r = 0) ∧
        Real.log A.det+Real.log (aggregate g q).det = 0 := by
  obtain ⟨α, q, hd, hM, hzero⟩ := optimal_dual_certificate hn g β hg hK hmax
  have hp := (primalFeasible_iff_containment g β c A).mpr hmax.feasible
  exact ⟨α, q, inverse_certificate_dual_optimal hp hd hM, hM, hzero, inverse_certificate_value hM⟩

/-- Proposition 2.3: both optima are attained and every actual optimum has an exact certificate. -/
theorem exact_duality (hn : 1 ≤ n) (g : Fin N → V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hK : IsConvexBody (constraintPolytope g β)) :
    (∃ c : V n, ∃ A : MatR n, ∃ α : Fin N → ℝ, ∃ q : Fin N → V n,
      IsMaxDet (constraintPolytope g β) c A ∧ PrimalOptimal g β c A ∧ DualOptimal g β α q ∧
        aggregate g q = A⁻¹ ∧ (∀ r, conePairing g β α q c A r = 0) ∧
          Real.log A.det+Real.log (aggregate g q).det = 0) ∧
    (∀ c A, IsMaxDet (constraintPolytope g β) c A →
      ∃ α : Fin N → ℝ, ∃ q : Fin N → V n,
        DualOptimal g β α q ∧ aggregate g q = A⁻¹ ∧ (∀ r, conePairing g β α q c A r = 0) ∧
          Real.log A.det+Real.log (aggregate g q).det = 0) := by
  letI : NeZero n := ⟨by omega⟩
  have hmax := Khachiyan.john_isMaxDet hK
  obtain ⟨α, q, hd, hM, hzero, hvalue⟩ := optimal_multipliers hn g β hg hK hmax
  refine ⟨⟨Khachiyan.johnCenter (constraintPolytope g β), Khachiyan.johnShape (constraintPolytope g β), α, q,
    hmax, (primalOptimal_iff_isMaxDet _ _ _ _).mpr hmax, hd, hM, hzero, hvalue⟩, ?_⟩
  intro c A hopt
  exact optimal_multipliers hn g β hg hK hopt

end SharpCut.Optimization
