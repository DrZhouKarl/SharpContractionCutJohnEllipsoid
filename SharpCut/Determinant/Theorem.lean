import SharpCut.Determinant.Equality

/-! # The complete quantitative John-frame determinant theorem -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
open Certificate
variable {n N : ℕ}

theorem modelF0_exact_determinant (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (modelF0 v).det = (2-inverseDimension n)^(n+1)/((2 : ℝ)^n*(1-inverseDimension n)) := by
  rw [modelF0_det_explicit hn v hv, div_pow]
  have hb := inverseDimension_bounds hn
  have h1 : 1-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hp : (2-inverseDimension n)^(n+1) = (2-inverseDimension n)^(n-1)*(2-inverseDimension n)^2 := by
    rw [← pow_add]
    congr 1
    omega
  have h2 : (2 : ℝ)^n = (2 : ℝ)^(n-1)*2 := by
    conv_lhs => rw [show n = (n-1)+1 by omega, pow_succ]
  rw [hp, h2]
  field_simp [h1, pow_ne_zero (n-1) (by norm_num : (2 : ℝ) ≠ 0)] <;> ring

/-- Theorem 8.1, with all dimensions, both estimates and the full determinant equality iff. -/
theorem quantitative_frame_determinant (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    (1/1500 : ℝ)*frameDefect F v ≤ Real.log (normalizedCertificate F v).det ∧
    Real.log (normalizedCertificate F v).det ≤ frameDefect F v/(2*(2-inverseDimension n)) ∧
    (modelF0 v).det = (2-inverseDimension n)^(n+1)/((2 : ℝ)^n*(1-inverseDimension n)) ∧
    (modelF0 v).det ≤ (certificateF F v).det ∧
    ((certificateF F v).det = (modelF0 v).det ↔
      ∀ i, height F v i = -1 ∨ height F v i = inverseDimension n) ∧
    ((∀ i, height F v i = -1 ∨ height F v i = inverseDimension n) →
      certificateF F v = modelF0 v ∧ normalizedCertificate F v = 1) :=
  ⟨all_dimensions_logdet_lower F hn v hv, all_dimensions_logdet_upper F hn v hv,
    modelF0_exact_determinant hn v hv, certificateF_determinant_bound F hn v hv,
    certificateF_det_eq_model_iff F hn v hv, certificateF_matrix_eq_model_of_contacts F hn v hv⟩

end SharpCut.Determinant
