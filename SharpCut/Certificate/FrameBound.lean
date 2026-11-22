import SharpCut.Determinant.Theorem

/-! # The complete sharp John-frame certificate bound, Theorem 3.2 -/

noncomputable section
open scoped RealInnerProductSpace
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

theorem sharp_frame_determinant_bound (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) : 1/sharpRatio n ≤ (unrotatedQ F v).det := by
  have hr := sharpRatio_pos (show 1 ≤ n by omega)
  apply (div_le_iff₀ hr).mpr
  have h := Determinant.normalizedCertificate_det_ge_one F hn v hv
  rw [normalizedCertificate_det F hn v hv] at h
  simpa only [mul_comm] using h

theorem sharp_frame_equality (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    (unrotatedQ F v).det = 1/sharpRatio n ↔ ∀ i, height F v i = -1 ∨ height F v i = inverseDimension n := by
  have hr := sharpRatio_pos (show 1 ≤ n by omega)
  have he : (unrotatedQ F v).det = 1/sharpRatio n ↔ (normalizedCertificate F v).det = 1 := by
    rw [normalizedCertificate_det F hn v hv]
    constructor
    · intro h; rw [h]; field_simp [hr.ne']
    · intro h
      apply (eq_div_iff hr.ne').mpr
      simpa only [mul_comm] using h
  exact he.trans ((Determinant.normalizedCertificate_det_one_iff F hn v hv).trans (frameDefect_zero_iff F hn v hv))

theorem sharp_frame_model_matrix (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) (h : ∀ i, height F v i = -1 ∨ height F v i = inverseDimension n) :
    unrotatedQ F v = inverseModel v := by
  rw [ordered_factorization F hn v hv,
    (Determinant.certificateF_matrix_eq_model_of_contacts F hn v hv h).1, modelF0_mul_D hn v hv]

/-- Theorem 3.2 with actual certificate construction, positive determinant and both equality directions. -/
theorem john_frame_certificate_bound (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    IsUnit (unrotatedQ F v) ∧ 0 < (unrotatedQ F v).det ∧
    (1/1500 : ℝ)*frameDefect F v ≤ Real.log (sharpRatio n*(unrotatedQ F v).det) ∧
    Real.log (sharpRatio n*(unrotatedQ F v).det) ≤ frameDefect F v/(2*(2-inverseDimension n)) ∧
    1/sharpRatio n ≤ (unrotatedQ F v).det ∧
    ((unrotatedQ F v).det = 1/sharpRatio n ↔ ∀ i, height F v i = -1 ∨ height F v i = inverseDimension n) ∧
    ((∀ i, height F v i = -1 ∨ height F v i = inverseDimension n) → unrotatedQ F v = inverseModel v) := by
  have hp := unrotatedQ_det_pos F hn v hv
  have hq : IsUnit (unrotatedQ F v) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hp.ne')
  have hl := Determinant.all_dimensions_logdet_lower F hn v hv
  have hu := Determinant.all_dimensions_logdet_upper F hn v hv
  rw [normalizedCertificate_det F hn v hv] at hl hu
  exact ⟨hq, hp, hl, hu, sharp_frame_determinant_bound F hn v hv,
    sharp_frame_equality F hn v hv, sharp_frame_model_matrix F hn v hv⟩

end SharpCut.Certificate
