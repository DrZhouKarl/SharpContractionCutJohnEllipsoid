import SharpCut.Certificate.GramCoupling

/-! # The arbitrary-frame, arbitrary-axis two-dimensional determinant branch -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
open Certificate
variable {N : ℕ}

theorem dimension_two_determinant (F : JohnFrame 2 N) (v : V 2) (hv : ‖v‖ = 1) :
    1+(11/60 : ℝ)*frameDefect F v ≤ (normalizedCertificate F v).det := by
  have hbase : ∃ b : OrthonormalBasis (Fin 2) ℝ (V 2), b 0 = v :=
    Geometry.exists_axial_basis (m := 1) v hv
  obtain ⟨b, hb⟩ := hbase
  let w := b 1
  let A : Matrix (Fin 2) (Fin 2) ℝ := Geometry.inBasis b (normalizedCertificate F v)
  let E : Matrix (Fin 2) (Fin 2) ℝ := Geometry.inBasis b (transversePerturbation F v)
  let x := axialDeficit F v
  let σ := transverseSigma F v
  let c := ⟪w, transverseCoupling F v⟫
  have hw : ‖w‖ = 1 := b.orthonormal.norm_eq_one 1
  have horth : ⟪w, v⟫ = 0 := by
    rw [← hb]
    exact (orthonormal_iff_ite.mp b.orthonormal 1 0).trans (by norm_num)
  have hE00 : E 0 0 = 0 := by
    change Geometry.inBasis b (transversePerturbation F v) 0 0 = 0
    rw [Geometry.inBasis_entry, hb, transversePerturbation_axis F (by norm_num) v hv, inner_zero_right]
  have htr : E 0 0+E 1 1 = σ := by
    have he := Geometry.inBasis_trace b (transversePerturbation F v)
    rw [transversePerturbation_trace F (by norm_num) v hv] at he
    simpa only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply] using he
  have hE11 : ⟪w, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v) w⟫ = σ := by
    change ⟪b 1, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v) (b 1)⟫ = σ
    rw [← Geometry.inBasis_entry]
    linarith only [htr, hE00]
  have hA00 : A 0 0 = 1-x := by
    change Geometry.inBasis b (normalizedCertificate F v) 0 0 = 1-x
    rw [Geometry.inBasis_entry, hb]
    exact normalized_axial_bilinear F (by norm_num) v hv
  have hA11 : A 1 1 = 1+σ := by
    change Geometry.inBasis b (normalizedCertificate F v) 1 1 = 1+σ
    rw [Geometry.inBasis_entry]
    change ⟪w, Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizedCertificate F v) w⟫ = _
    rw [normalized_transverse_bilinear F (by norm_num) v w w hv horth horth,
      real_inner_self_eq_norm_sq, hw, one_pow, hE11]
  have hA10 : A 1 0 = c := by
    change Geometry.inBasis b (normalizedCertificate F v) 1 0 = c
    rw [Geometry.inBasis_entry, hb]
    exact normalized_mixed_bilinear F (by norm_num) v w hv horth
  have hsym : A.IsSymm :=
    (Geometry.inBasis_posDef b _ (normalizedCertificate_posDef F (by norm_num) v hv)).isHermitian.isSymm
  have hA01 : A 0 1 = c := (hsym.apply 1 0).trans hA10
  have hdet : (normalizedCertificate F v).det = (1-x)*(1+σ)-c^2 := by
    rw [← Geometry.inBasis_det b, Matrix.det_fin_two]
    change A 0 0*A 1 1-A 0 1*A 1 0 = _
    rw [hA00, hA11, hA01, hA10, pow_two]
  have hgram := transverse_coupling_bound F (by norm_num) v w hv horth
  have hc : ⟪transverseCoupling F v, w⟫ = c := real_inner_comm _ _
  rw [hc, hw, one_pow, mul_one, hE11] at hgram
  change c^2 ≤ x*(cutWeight 2-σ) at hgram
  dsimp [x, σ] at hdet hgram
  norm_num [axialDeficit, transverseSigma, inverseDimension, cutWeight] at hdet hgram
  nlinarith only [hdet, hgram]

theorem log_of_affine_lower (c χ value : ℝ) (hc : 0 < c) (hχ : 0 ≤ χ) (hχ2 : χ ≤ 2)
    (hl : 1+c*χ ≤ value) : c/(1+2*c)*χ ≤ Real.log value := by
  have hp : 0 < 1+c*χ := by positivity
  have hden : 0 < 1+2*c := by positivity
  have horder : 1+c*χ ≤ 1+2*c := by nlinarith
  have hfrac := div_le_div_of_nonneg_left (mul_nonneg hc.le hχ) hp horder
  have he : 1-(1+c*χ)⁻¹ = c*χ/(1+c*χ) := by
    field_simp [hp.ne']
    ring
  calc
    _ = c*χ/(1+2*c) := by ring
    _ ≤ c*χ/(1+c*χ) := hfrac
    _ = 1-(1+c*χ)⁻¹ := he.symm
    _ ≤ Real.log (1+c*χ) := Real.one_sub_inv_le_log_of_pos hp
    _ ≤ Real.log value := Real.log_le_log hp hl

theorem dimension_two_logdet (F : JohnFrame 2 N) (v : V 2) (hv : ‖v‖ = 1) :
    (11/82 : ℝ)*frameDefect F v ≤ Real.log (normalizedCertificate F v).det := by
  have hr := frameDefect_range F (by norm_num) v hv
  have h := log_of_affine_lower (11/60) (frameDefect F v) (normalizedCertificate F v).det
    (by norm_num) hr.1 hr.2.2 (dimension_two_determinant F v hv)
  norm_num at h
  exact h

theorem dimension_two_uniform_logdet (F : JohnFrame 2 N) (v : V 2) (hv : ‖v‖ = 1) :
    (1/1500 : ℝ)*frameDefect F v ≤ Real.log (normalizedCertificate F v).det :=
  (mul_le_mul_of_nonneg_right (by norm_num : (1/1500 : ℝ) ≤ 11/82)
    (frameDefect_nonneg F (by norm_num) v hv)).trans (dimension_two_logdet F v hv)

end SharpCut.Determinant
