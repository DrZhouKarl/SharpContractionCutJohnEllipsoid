import SharpCut.Stability.BlockNorm
import SharpCut.Stability.LocalLogarithm

/-! # Complete local geometric coercivity at the exact paper thresholds -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Stability
open Certificate Gap
variable {n N : ℕ}

theorem normalized_trace_gain (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (normalizedCertificate F v).trace-(n : ℝ) = transverseSigma F v-axialDeficit F v := by
  have h := congrArg Matrix.trace (normalized_arrow_identity F hn v hv)
  have hj := transverseCoupling_orthogonal F v hv
  have hj' : ⟪transverseCoupling F v,v⟫ = 0 := by rw [real_inner_comm]; exact hj
  simp only [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, arrowPerturbation, Matrix.trace_add,
    Matrix.trace_smul, Khachiyan.trace_outer, trace_cross, real_inner_self_eq_norm_sq,
    hv, one_pow, hj, hj', transversePerturbation_trace F hn v hv, smul_eq_mul] at h
  linarith only [h]

theorem hermitian_eigenvalue_frobenius_bound (E : MatR n) (hE : E.IsHermitian) (i : Fin n) :
    |hE.eigenvalues i| ≤ frobeniusNorm E := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (hE.eigenvalues j)) (Finset.mem_univ i)
  rw [← hermitian_frobenius_spectral E hE] at h
  rw [← sq_abs] at h
  exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp h

theorem hermitian_operator_frobenius (E : MatR n) (hE : E.IsHermitian) : operatorNorm E ≤ frobeniusNorm E := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  exact hermitian_action_bound E hE (frobeniusNorm E) (Real.sqrt_nonneg _)
    (hermitian_eigenvalue_frobenius_bound E hE) u

/-- The strict operator bound in (9.12) includes the zero-defect case. -/
theorem local_operator_bound (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hsmall : transverseSigma F v ≤ 1/1000) : operatorNorm (normalizedCertificate F v-1) < 1/30 := by
  have hF := (normalizedCertificate_posDef F hn v hv).isHermitian.sub Matrix.isHermitian_one
  have hop := hermitian_operator_frobenius _ hF
  have hf := local_full_frobenius_bound F hn v hv hsmall
  have hfsmall : frobeniusNorm (normalizedCertificate F v-1) < 1/30 := by
    nlinarith only [hf, hsmall, Real.sqrt_nonneg (∑ i, ∑ j, (normalizedCertificate F v-1) i j^2)]
  exact hop.trans_lt hfsmall

theorem logdet_quadratic_lower (Y : MatR n) (hY : Y.PosDef)
    (hsmall : ∀ i, -(1/30 : ℝ) ≤ hY.isHermitian.eigenvalues i-1) :
    Y.trace-(n : ℝ)-(15/29 : ℝ)*(frobeniusNorm (Y-1))^2 ≤ Real.log Y.det := by
  have hlog : Real.log Y.det = ∑ i, Real.log (hY.isHermitian.eigenvalues i) := by
    rw [hY.isHermitian.det_eq_prod_eigenvalues]
    exact Real.log_prod (fun i _ => (hY.eigenvalues_pos i).ne')
  have htrace : Y.trace-(n : ℝ) = ∑ i, (hY.isHermitian.eigenvalues i-1) := by
    rw [Khachiyan.Spectral.trace_eq_sum hY.isHermitian]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  rw [htrace, Gap.frobenius_shift_spectral Y hY.isHermitian, hlog, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := logarithm_quadratic_lower (hY.isHermitian.eigenvalues i-1) (hsmall i)
  have heq : 1+(hY.isHermitian.eigenvalues i-1) = hY.isHermitian.eigenvalues i := by ring
  rwa [heq] at h

/-- The stronger 2*sigma/29 estimate displayed in (9.13). -/
theorem local_logdet_gain (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hsmall : transverseSigma F v ≤ 1/1000) :
    (2/29 : ℝ)*transverseSigma F v ≤ Real.log (normalizedCertificate F v).det := by
  have hY := normalizedCertificate_posDef F hn v hv
  have hnorm := local_full_frobenius_bound F hn v hv hsmall
  have he (i : Fin n) : -(1/30 : ℝ) ≤ hY.isHermitian.eigenvalues i-1 := by
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (hY.isHermitian.eigenvalues j-1)) (Finset.mem_univ i)
    rw [← Gap.frobenius_shift_spectral _ hY.isHermitian] at hi
    by_contra h
    have hl : hY.isHermitian.eigenvalues i-1 < -(1/30 : ℝ) := lt_of_not_ge h
    nlinarith only [hi, hnorm, hsmall, hl, sq_nonneg (hY.isHermitian.eigenvalues i-1+1/30)]
  have hlog := logdet_quadratic_lower _ hY he
  rw [normalized_trace_gain F hn v hv, axialDeficit_sigma F hn v] at hlog
  have hs := (transverseSigma_range F hn v hv).1
  have hbgain := mul_nonneg (inverseDimension_bounds hn).1.le hs
  nlinarith only [hlog, hnorm, hbgain]

theorem sigma_defect_relation (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) :
    ((2-inverseDimension n)*(2+inverseDimension n))*transverseSigma F v = 2*frameDefect F v := by
  have hb := inverseDimension_bounds hn
  have hd : ((2-inverseDimension n)*(2+inverseDimension n)) ≠ 0 := by
    apply mul_ne_zero <;> linarith [hb.1, hb.2]
  unfold transverseSigma
  exact mul_div_cancel₀ _ hd

/-- Lemma 9.3 in every n ≥ 2 with the exact sigma threshold and both bounds. -/
theorem local_coercivity (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hsmall : transverseSigma F v ≤ 1/1000) :
    transverseSigma F v/16 ≤ Real.log (normalizedCertificate F v).det ∧
      frameDefect F v/32 ≤ transverseSigma F v/16 := by
  have hg := local_logdet_gain F hn v hv hsmall
  have hs := (transverseSigma_range F hn v hv).1
  have hr := sigma_defect_relation F hn v
  have hprod := mul_nonneg (sq_nonneg (inverseDimension n)) hs
  constructor <;> nlinarith only [hg, hs, hr, hprod]

/-- The exact conversion used in the deferred proof of Lemma 6.1. -/
theorem sigma_from_small_defect (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hsmall : frameDefect F v ≤ 3/2000) : transverseSigma F v ≤ 1/1250 := by
  have hb := inverseDimension_bounds hn
  have hs := (transverseSigma_range F hn v hv).1
  have hden : 15/4 ≤ (2-inverseDimension n)*(2+inverseDimension n) := by
    nlinarith [mul_nonneg hb.1.le (sub_nonneg.mpr hb.2)]
  have hm := mul_le_mul_of_nonneg_right hden hs
  have hr := sigma_defect_relation F hn v
  nlinarith only [hm, hr, hsmall]

/-- Complete Lemma 6.1: two global bounds and its precise local implication. -/
theorem geometric_control (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (frobeniusNorm (unrotatedQ F v-inverseModel v))^2 ≤
      (1-inverseDimension n)/(2-inverseDimension n)*frameDefect F v ∧
    (∑ i, F.weight i*(Metric.infDist (F.contact i) (Equality.modelContactSet v))^2) ≤
      (32/3 : ℝ)*frameDefect F v ∧
    (frameDefect F v ≤ 3/2000 → frameDefect F v/32 ≤ geometricGap F v) := by
  refine ⟨certificate_residual_bound F hn v hv, weighted_contact_distance_bound F hn v hv, ?_⟩
  intro hsmall
  have hs : transverseSigma F v ≤ 1/1000 := (sigma_from_small_defect F hn v hv hsmall).trans (by norm_num)
  have h := local_coercivity F hn v hv hs
  have hl : geometricGap F v = Real.log (normalizedCertificate F v).det := by
    unfold geometricGap frameMatrix
    rw [polarMatrix_det (unrotatedQ_det_pos F hn v hv), normalizedCertificate_det F hn v hv]
  rw [hl]
  exact h.2.trans h.1

end SharpCut.Stability
