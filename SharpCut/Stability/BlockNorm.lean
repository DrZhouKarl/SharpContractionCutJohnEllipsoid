import SharpCut.Stability.LocalNorms

/-! # Exact Frobenius square of the full normalized arrow perturbation -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Stability
open Certificate
variable {n N : ℕ}

theorem cross_action (u w x : V n) : Matrix.toEuclideanCLM (𝕜 := ℝ) (cross u w) x = ⟪w,x⟫ • u := by
  apply WithLp.ofLp_injective 2
  simp only [Khachiyan.matrix_action_ofLp, cross, Matrix.vecMulVec_mulVec,
    ← Khachiyan.inner_eq_dotProduct, WithLp.ofLp_smul]
  ext i
  simp only [Pi.smul_apply, op_smul_eq_smul, smul_eq_mul]

theorem trace_cross (u w : V n) : (cross u w).trace = ⟪w,u⟫ := by
  rw [cross, Matrix.trace_vecMulVec, ← Khachiyan.inner_eq_dotProduct, real_inner_comm]

def arrowPerturbation (x : ℝ) (v j : V n) (E : MatR n) : MatR n :=
  (-x) • outer v+cross v j+cross j v+E

theorem arrowPerturbation_isHermitian (x : ℝ) (v j : V n) (E : MatR n) (hE : E.IsHermitian) :
    (arrowPerturbation x v j E).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  apply Matrix.IsSymm.ext
  intro i k
  simp only [arrowPerturbation, Matrix.add_apply, Matrix.smul_apply, cross, Matrix.vecMulVec_apply,
    Khachiyan.outer_apply, hE.isSymm.apply i k, smul_eq_mul]
  ring

theorem normalized_arrow_identity (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    normalizedCertificate F v-1 = arrowPerturbation (axialDeficit F v) v (transverseCoupling F v) (transversePerturbation F v) := by
  cases n with
  | zero => omega
  | succ m =>
    obtain ⟨B, hB⟩ := Geometry.exists_axial_basis v hv
    have hperp (i : Fin (m+1)) (hi : i ≠ 0) : ⟪B i,v⟫ = 0 := by rw [← hB]; exact B.orthonormal.inner_eq_zero hi
    have hE := transversePerturbation_isHermitian F v
    have hF := (normalizedCertificate_posDef F hn v hv).isHermitian
    have hEv := transversePerturbation_axis F hn v hv
    have hjv := transverseCoupling_orthogonal F v hv
    have hvj : ⟪transverseCoupling F v,v⟫ = 0 := by rw [real_inner_comm]; exact hjv
    apply Geometry.inBasis_injective B
    ext i k
    rw [Geometry.inBasis_sub, Geometry.inBasis_one]
    simp only [arrowPerturbation, Geometry.inBasis_add, Geometry.inBasis_smul]
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
    simp only [Geometry.inBasis_entry, Khachiyan.outer_action, cross_action, real_inner_smul_right, smul_eq_mul]
    by_cases hi : i = 0 <;> by_cases hk : k = 0
    · subst i; subst k
      simp only [hB, normalized_axial_bilinear F hn v hv, hEv, inner_zero_right,
        real_inner_self_eq_norm_sq, hv, one_pow, hjv, hvj, Matrix.one_apply_eq]
      ring
    · subst i
      have hik : (0 : Fin (m+1)) ≠ k := Ne.symm hk
      have hvk : ⟪v,B k⟫ = 0 := by rw [real_inner_comm]; exact hperp k hk
      have hflip : ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizedCertificate F v) (B k)⟫ =
          ⟪B k, Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizedCertificate F v) v⟫ := by
        rw [Khachiyan.inner_matrix_action_symm hF.isSymm, real_inner_comm]
      have hEz : ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v) (B k)⟫ = 0 := by
        rw [Khachiyan.inner_matrix_action_symm hE.isSymm, hEv, inner_zero_left]
      simp only [hB, hflip, normalized_mixed_bilinear F hn v (B k) hv (hperp k hk), hEz, hvk,
        hperp k hk, real_inner_self_eq_norm_sq, hv, one_pow, hjv, hvj, Matrix.one_apply_ne hik,
        mul_zero, zero_mul, zero_add, add_zero, sub_zero, one_mul, mul_one]
      rw [real_inner_comm (transverseCoupling F v) (B k)]
    · subst k
      simp only [hB, normalized_mixed_bilinear F hn v (B i) hv (hperp i hi), hEv, inner_zero_right,
        hperp i hi, real_inner_self_eq_norm_sq, hv, one_pow, hjv, hvj, Matrix.one_apply_ne hi,
        mul_zero, zero_mul, zero_add, add_zero, sub_zero, mul_one, one_mul]
    · have hvk : ⟪v,B k⟫ = 0 := by rw [real_inner_comm]; exact hperp k hk
      simp only [normalized_transverse_bilinear F hn v (B i) (B k) hv (hperp i hi) (hperp k hk),
        hperp i hi, hvk, mul_zero, zero_mul, zero_add, add_zero]
      rw [orthonormal_iff_ite.mp B.orthonormal i k, Matrix.one_apply]
      ring

/-- Squaring the actual symmetric perturbation, with all mixed traces checked. -/
theorem arrow_frobenius_sq (x : ℝ) (v j : V n) (E : MatR n) (hv : ‖v‖ = 1)
    (hj : ⟪v,j⟫ = 0) (hE : E.IsHermitian) (hEv : Matrix.toEuclideanCLM (𝕜 := ℝ) E v = 0) :
    (frobeniusNorm (arrowPerturbation x v j E))^2 = x^2+2*‖j‖^2+(frobeniusNorm E)^2 := by
  have hjv : ⟪j,v⟫ = 0 := by rw [real_inner_comm]; exact hj
  have hvEj : ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) E j⟫ = 0 := by
    rw [Khachiyan.inner_matrix_action_symm hE.isSymm, hEv, inner_zero_left]
  have htrace (A : MatR n) (u w : V n) : (A*cross u w).trace =
      ⟪w, Matrix.toEuclideanCLM (𝕜 := ℝ) A u⟫ := Optimization.trace_mul_cross A u w
  have hright (u w : V n) : (cross u w*E).trace = ⟪w, Matrix.toEuclideanCLM (𝕜 := ℝ) E u⟫ := by
    rw [Matrix.trace_mul_comm]
    exact Optimization.trace_mul_cross E u w
  rw [Gap.frobeniusNorm_sq_trace _ (arrowPerturbation_isHermitian x v j E hE), arrowPerturbation, pow_two,
    Gap.frobeniusNorm_sq_trace E hE, pow_two]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul]
  simp only [← cross_self]
  simp only [htrace, hright, cross_action,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow, hj, hjv, hEv,
    inner_zero_left, inner_zero_right, hvEj, smul_eq_mul]
  simp only [pow_two]
  ring

/-- Equation (9.12), at exactly the paper's sufficient threshold. -/
theorem local_full_frobenius_bound (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hsmall : transverseSigma F v ≤ 1/1000) :
    (frobeniusNorm (normalizedCertificate F v-1))^2 ≤ (5/6 : ℝ)*transverseSigma F v := by
  rw [normalized_arrow_identity F hn v hv, arrow_frobenius_sq _ v _ _ hv
    (transverseCoupling_orthogonal F v hv) (transversePerturbation_isHermitian F v)
    (transversePerturbation_axis F hn v hv)]
  have hm := local_metric_norm_bound F hn v hv hsmall
  have hc := local_coupling_bounds F hn v hv hsmall
  nlinarith only [hm, hc.1, hc.2, (transverseSigma_range F hn v hv).1]

end SharpCut.Stability
