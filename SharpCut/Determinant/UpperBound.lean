import SharpCut.Determinant.LowerBound

/-! # The common trace and log-determinant upper bound in all dimensions -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
open Certificate
variable {n N : ℕ}

/-- Export the logarithmic spectral step used by the reused contact certificate. -/
theorem posDef_logdet_trace (A : MatR n) (hA : A.PosDef) :
    Real.log A.det ≤ A.trace-(n : ℝ) := by
  have hlog : Real.log A.det = ∑ i, Real.log (hA.isHermitian.eigenvalues i) := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues]
    exact Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne')
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i))
  rw [Finset.sum_sub_distrib, ← Khachiyan.Spectral.trace_eq_sum hA.isHermitian] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  rw [hlog]
  exact hsum

theorem normalizedCertificate_trace (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (normalizedCertificate F v).trace = (n : ℝ)+transverseSigma F v-axialDeficit F v := by
  cases n with
  | zero => omega
  | succ m =>
    obtain ⟨b, hb⟩ := Geometry.exists_axial_basis (m := m) v hv
    have hE00 : Geometry.inBasis b (transversePerturbation F v) 0 0 = 0 := by
      rw [Geometry.inBasis_entry, hb, transversePerturbation_axis F hn v hv, inner_zero_right]
    have hF00 : Geometry.inBasis b (normalizedCertificate F v) 0 0 = 1-axialDeficit F v := by
      rw [Geometry.inBasis_entry, hb, normalized_axial_bilinear F hn v hv]
    have hdiag (i : Fin m) : Geometry.inBasis b (normalizedCertificate F v) i.succ i.succ =
        1+Geometry.inBasis b (transversePerturbation F v) i.succ i.succ := by
      rw [Geometry.inBasis_entry, normalized_transverse_bilinear F hn v (b i.succ) (b i.succ) hv
        (Geometry.basis_tail_orthogonal b v hb i) (Geometry.basis_tail_orthogonal b v hb i),
        real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one i.succ, one_pow, Geometry.inBasis_entry]
    have hsum : (∑ i : Fin m, Geometry.inBasis b (normalizedCertificate F v) i.succ i.succ) =
        (m : ℝ)+(∑ i : Fin m, Geometry.inBasis b (transversePerturbation F v) i.succ i.succ) := by
      simp_rw [hdiag]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
    have hF := Geometry.inBasis_trace b (normalizedCertificate F v)
    have hE := Geometry.inBasis_trace b (transversePerturbation F v)
    conv_lhs at hF => simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_succ]
    conv_lhs at hE => simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_succ]
    rw [hF00, hsum] at hF
    rw [hE00, zero_add, transversePerturbation_trace F hn v hv] at hE
    simp only [Nat.cast_succ]
    linarith only [hF, hE]

theorem sigma_minus_deficit (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) :
    transverseSigma F v-axialDeficit F v = frameDefect F v/(2*(2-inverseDimension n)) := by
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hp : 2+inverseDimension n ≠ 0 := by linarith [hb.1]
  unfold transverseSigma axialDeficit
  field_simp [hd, hp] <;> ring

theorem all_dimensions_logdet_upper (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    Real.log (normalizedCertificate F v).det ≤ frameDefect F v/(2*(2-inverseDimension n)) := by
  have h := posDef_logdet_trace (normalizedCertificate F v) (normalizedCertificate_posDef F hn v hv)
  rw [normalizedCertificate_trace F hn v hv] at h
  have he := sigma_minus_deficit F hn v
  linarith only [h, he]

end SharpCut.Determinant
