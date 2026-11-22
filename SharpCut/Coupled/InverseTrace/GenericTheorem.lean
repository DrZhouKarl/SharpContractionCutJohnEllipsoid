import SharpCut.Coupled.InverseTrace.CauchyCoefficient

/-! # Generic all-test coupled inequality iff the effective inverse-trace bound -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Coupled.InverseTrace
variable {n : ℕ}

theorem effectiveMatrix_trace (E : MatR n) (j : V n) (β η : ℝ) :
    (effectiveMatrix E j β η).trace = E.trace+β*(n : ℝ)-‖j‖^2/η := by
  unfold effectiveMatrix
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    Khachiyan.trace_outer, smul_eq_mul]
  ring

/-- The cancellation of the rank-one vector term leaves the exact inverse-trace expression. -/
theorem effective_coefficient_trace (E : MatR n) (j : V n) (β η σ : ℝ)
    (hR : (effectiveMatrix E j β η).PosDef) (htrace : E.trace = σ) :
    coefficient (effectiveMatrix E j β η) j β η = σ-β*(n : ℝ)+β^2*((effectiveMatrix E j β η)⁻¹).trace := by
  rw [coefficient_trace_identity _ hR, effectiveMatrix_trace, htrace]
  ring

theorem coefficient_iff_inverse_trace (E : MatR n) (j : V n) (β η σ : ℝ)
    (hR : (effectiveMatrix E j β η).PosDef) (hβ : 0 < β) (htrace : E.trace = σ) :
    coefficient (effectiveMatrix E j β η) j β η ≤ σ ↔ ((effectiveMatrix E j β η)⁻¹).trace ≤ (n : ℝ)/β := by
  rw [effective_coefficient_trace E j β η σ hR htrace]
  constructor
  · intro h
    apply (le_div_iff₀ hβ).mpr
    apply le_of_mul_le_mul_left (a := β) _ hβ
    nlinarith only [h]
  · intro h
    have hm := mul_le_mul_of_nonneg_left ((le_div_iff₀ hβ).mp h) hβ.le
    nlinarith only [hm]

/-- The full generic inverse-trace equivalence. Effective positive definiteness is proved from all tests. -/
theorem all_tests_inverse_trace_iff (E : MatR n) (hE : E.IsHermitian) (j : V n) (β η σ : ℝ)
    (hβ : 0 < β) (hη : 0 < η) (hσ : 0 < σ) (htrace : E.trace = σ) :
    AllCoupledTests E j β η σ ↔ (effectiveMatrix E j β η).PosDef ∧
      ((effectiveMatrix E j β η)⁻¹).trace ≤ (n : ℝ)/β := by
  have hcomplete := all_tests_completion_iff E j β η σ hη.ne'
  have hRherm := effectiveMatrix_hermitian E j β η hE
  constructor
  · intro h
    have hc := hcomplete.mp h
    have hp := all_completed_tests_posDef _ j β η σ hRherm hβ hσ hc
    have hS := (completed_tests_iff_coefficient _ hp j β η σ hη hσ.le).mp hc
    exact ⟨hp, (coefficient_iff_inverse_trace E j β η σ hp hβ htrace).mp hS⟩
  · rintro ⟨hp, ht⟩
    have hS := (coefficient_iff_inverse_trace E j β η σ hp hβ htrace).mpr ht
    exact hcomplete.mpr ((completed_tests_iff_coefficient _ hp j β η σ hη hσ.le).mpr hS)

end SharpCut.Coupled.InverseTrace
