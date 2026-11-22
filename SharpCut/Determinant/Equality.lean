import SharpCut.Determinant.UpperBound

/-! # Exact determinant equality and the model matrix in every dimension -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
open Certificate
variable {n N : ℕ}

theorem normalizedCertificate_one_of_zero_defect (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) (hχ : frameDefect F v = 0) : normalizedCertificate F v = 1 := by
  have hz := zero_defect_transverse_blocks F hn v hv hχ
  have hx : axialDeficit F v = 0 := by rw [axialDeficit, hχ, zero_div]
  cases n with
  | zero => omega
  | succ m =>
    obtain ⟨b, hb⟩ := Geometry.exists_axial_basis (m := m) v hv
    have hs := (Geometry.inBasis_posDef b _ (normalizedCertificate_posDef F hn v hv)).isHermitian.isSymm
    have hc (i : Fin m) : Geometry.inBasis b (normalizedCertificate F v) i.succ 0 = 0 := by
      rw [Geometry.inBasis_entry, hb, normalized_mixed_bilinear F hn v (b i.succ) hv
        (Geometry.basis_tail_orthogonal b v hb i), hz.2, inner_zero_right]
    have he : Geometry.inBasis b (normalizedCertificate F v) = 1 := by
      ext i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · rw [Geometry.inBasis_entry, hb, normalized_axial_bilinear F hn v hv, hx, sub_zero]
          simp only [Matrix.one_apply_eq]
        · rw [← hs.apply 0 j.succ, hc]
          simp [Matrix.one_apply, eq_comm]
      · refine Fin.cases ?_ (fun j => ?_) j
        · rw [hc]
          simp [Matrix.one_apply]
        · rw [Geometry.inBasis_entry, normalized_transverse_bilinear F hn v (b i.succ) (b j.succ) hv
            (Geometry.basis_tail_orthogonal b v hb i) (Geometry.basis_tail_orthogonal b v hb j),
            hz.1, map_zero, ContinuousLinearMap.zero_apply, inner_zero_right, add_zero]
          simpa only [Matrix.one_apply, Fin.succ_inj] using
            (orthonormal_iff_ite.mp b.orthonormal i.succ j.succ)
    apply Geometry.inBasis_injective b
    rw [Geometry.inBasis_one]
    exact he

theorem normalizedCertificate_det_ge_one (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) : 1 ≤ (normalizedCertificate F v).det := by
  have h := all_dimensions_logdet_lower F hn v hv
  have hc : 0 ≤ (1/1500 : ℝ)*frameDefect F v := mul_nonneg (by norm_num) (frameDefect_nonneg F hn v hv)
  have hl : Real.log (1 : ℝ) ≤ Real.log (normalizedCertificate F v).det := by
    rw [Real.log_one]; exact hc.trans h
  exact (Real.log_le_log_iff (by norm_num) (normalizedCertificate_posDef F hn v hv).det_pos).mp hl

theorem normalizedCertificate_det_one_iff (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) : (normalizedCertificate F v).det = 1 ↔ frameDefect F v = 0 := by
  constructor
  · intro h
    have hl := all_dimensions_logdet_lower F hn v hv
    rw [h, Real.log_one] at hl
    have hc := frameDefect_nonneg F hn v hv
    nlinarith only [hl, hc]
  · intro h
    rw [normalizedCertificate_one_of_zero_defect F hn v hv h, Matrix.det_one]

theorem certificateF_model_of_normalized_one (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hΦ : normalizedCertificate F v = 1) : certificateF F v = modelF0 v := by
  have hu := (modelNormalizer_posDef hn v).isUnit
  have he : modelNormalizer v*certificateF F v*modelNormalizer v =
      modelNormalizer v*modelF0 v*modelNormalizer v := by
    rw [← normalizedCertificate, hΦ, modelNormalizer_congruence hn v]
  exact hu.mul_left_cancel (hu.mul_right_cancel he)

theorem certificateF_determinant_bound (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) : (modelF0 v).det ≤ (certificateF F v).det := by
  have h := mul_le_mul_of_nonneg_right (normalizedCertificate_det_ge_one F hn v hv) (modelF0_posDef hn v).det_pos.le
  rw [one_mul, normalizedCertificate_det_mul F hn v] at h
  exact h

theorem certificateF_det_eq_model_iff (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    (certificateF F v).det = (modelF0 v).det ↔ ∀ i, height F v i = -1 ∨ height F v i = inverseDimension n := by
  have hd : (normalizedCertificate F v).det = 1 ↔ (certificateF F v).det = (modelF0 v).det := by
    have he := normalizedCertificate_det_mul F hn v
    constructor
    · intro h; rw [h, one_mul] at he; exact he.symm
    · intro h
      rw [h] at he
      have he' : (normalizedCertificate F v).det*(modelF0 v).det = 1*(modelF0 v).det := by simpa only [one_mul] using he
      exact mul_right_cancel₀ (modelF0_posDef hn v).det_pos.ne' he'
  exact hd.symm.trans ((normalizedCertificate_det_one_iff F hn v hv).trans (frameDefect_zero_iff F hn v hv))

theorem certificateF_matrix_eq_model_of_contacts (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) (h : ∀ i, height F v i = -1 ∨ height F v i = inverseDimension n) :
    certificateF F v = modelF0 v ∧ normalizedCertificate F v = 1 := by
  have hχ := (frameDefect_zero_iff F hn v hv).mpr h
  have hΦ := normalizedCertificate_one_of_zero_defect F hn v hv hχ
  exact ⟨certificateF_model_of_normalized_one F hn v hΦ, hΦ⟩

end SharpCut.Determinant
