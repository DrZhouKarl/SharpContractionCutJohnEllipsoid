import SharpCut.Scalar.LossIntegral

/-! # Complete endpoint-logarithm and rational comparison scope of SUP-17 -/

noncomputable section
namespace SharpCut.Scalar

theorem endpoint_finite_identity (u : ℝ) (hu : 0 ≤ u) (hu3 : u ≤ 1/3) :
    1/(1-u^2) = 1+u^2+u^4+u^6/(1-u^2) ∧ 1/(1-u^2) ≤ 9/8 := by
  have hsq : u^2 ≤ 1/9 := by nlinarith only [hu, hu3]
  have hd : 0 < 1-u^2 := by linarith only [hsq]
  constructor
  · field_simp [hd.ne'] <;> ring
  · apply (div_le_iff₀ hd).mpr
    nlinarith only [hsq]

/-- The exact rational upper bound retained in the original supporting endpoint record. -/
theorem endpoint_exact_rational_upper : transformedRatio (1/4) ≤ (21144601309 : ℝ)/21319034625 := by
  rw [transformedRatio_quarter, log_thirteen_recombination]
  have h2 := log_two_le_rational
  have h1613 := log_sixteen_thirteen_ge_rational
  have heq : ((7956 : ℝ)*(23581/34020)-2106*(5064/24389)-4160)/925 = 21144601309/21319034625 := by norm_num
  nlinarith only [h2, h1613, heq]

/-- The original loss integral, its exact endpoint value and both strict rational comparisons. -/
theorem endpoint_full_certificate :
    lossRatio (1/4) = (2106*Real.log 13-468*Real.log 2-4160)/925 ∧
    lossRatio (1/4) ≤ (21144601309 : ℝ)/21319034625 ∧
    (21144601309 : ℝ)/21319034625 < 9919/10000 ∧ (9919 : ℝ)/10000 < 124/125 := by
  have ht := lossRatio_eq_transformedRatio (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) ≤ 1/4)
  rw [ht]
  exact ⟨transformedRatio_quarter, endpoint_exact_rational_upper, by norm_num, by norm_num⟩

/-- The two explicit logarithm bounds, including the exact finite rational identities from the record. -/
theorem endpoint_record_logarithms :
    Real.log 2 ≤ 2*((1/3 : ℝ)+1/81+1/1215)+1/6804 ∧
    2*((3/29 : ℝ)+(3/29)^3/3) ≤ Real.log (16/13) ∧
    2*((1/3 : ℝ)+1/81+1/1215)+1/6804 = 23581/34020 ∧
    2*((3/29 : ℝ)+(3/29)^3/3) = 5064/24389 := by
  have h2 := log_two_le_rational
  have h1613 := log_sixteen_thirteen_ge_rational
  norm_num at h2 h1613 ⊢
  exact ⟨h2, h1613⟩

end SharpCut.Scalar
