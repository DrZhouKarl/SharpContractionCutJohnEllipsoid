import SharpCut.Certificate.CouplingTests

/-! # Direct finite weighted Cauchy–Schwarz, including zero-defect endpoints -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

theorem weighted_transverse_pointwise (F : JohnFrame n N) (v : V n) (hv : ‖v‖ = 1)
    (H : Fin N → V n) (i : Fin N) :
    (F.weight i/(1-boostParameter n*height F v i)*(height F v i-inverseDimension n)*
      ⟪transverse v (F.contact i), H i⟫)^2 ≤
        defectTerm F v i*(minusContactWeight F v i*‖H i‖^2) := by
  have h := abs_real_inner_le_norm (transverse v (F.contact i)) (H i)
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [sq_abs, mul_pow, transverse_norm_sq v (F.contact i) hv (F.contact_unit i)] at hs
  change ⟪transverse v (F.contact i), H i⟫^2 ≤ (1-(height F v i)^2)*‖H i‖^2 at hs
  have hm := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (sq_nonneg (F.weight i/(1-boostParameter n*height F v i)))
      (sq_nonneg (height F v i-inverseDimension n)))
  convert hm using 1 <;> (try simp only [defectTerm, minusContactWeight]) <;> ring

theorem weighted_transverse_cauchy (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (H : Fin N → V n) :
    (∑ i, F.weight i/(1-boostParameter n*height F v i)*(height F v i-inverseDimension n)*
      ⟪transverse v (F.contact i), H i⟫)^2 ≤
        frameDefect F v*(∑ i, minusContactWeight F v i*‖H i‖^2) := by
  rw [frameDefect]
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i hi => defectTerm_nonneg F hn v hv i)
    (fun i hi => mul_nonneg (minusContactWeight_nonneg F hn v hv i) (sq_nonneg _))
    (fun i hi => weighted_transverse_pointwise F v hv H i)

theorem coupling_test_cauchy (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (Z : MatR n) (hZ : Z.IsHermitian) (q : V n) :
    (couplingLinearTest F v Z q)^2 ≤ transverseSigma F v/2*couplingQuadraticTest F v Z q := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have hp : 0 < 2+inverseDimension n := by linarith [hb.1]
  have h := weighted_transverse_cauchy F hn v hv (couplingTestVector F v Z q)
  change (couplingLinearSum F v Z q)^2 ≤ frameDefect F v*(∑ i, minusContactWeight F v i*
    ‖couplingTestVector F v Z q i‖^2) at h
  rw [coupling_quadratic_identity F hn v hv Z hZ q] at h
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg (1/(2-inverseDimension n)))
  rw [coupling_linear_identity F hn v hv Z q]
  convert hm using 1 <;> (try unfold transverseSigma) <;> field_simp [hd.ne', hp.ne'] <;> ring

theorem coupling_quadratic_nonneg (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (Z : MatR n) (hZ : Z.IsHermitian) (q : V n) : 0 ≤ couplingQuadraticTest F v Z q := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have hp : 0 < 2+inverseDimension n := by linarith [hb.1]
  have hs : 0 ≤ ∑ i, minusContactWeight F v i*‖couplingTestVector F v Z q i‖^2 :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (minusContactWeight_nonneg F hn v hv i) (sq_nonneg _))
  rw [coupling_quadratic_identity F hn v hv Z hZ q] at hs
  exact nonneg_of_mul_nonneg_right hs (div_pos hd hp)

/-- The paper's selected-test variational inequality, extended to zero sigma. -/
theorem coupling_test_variational (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (Z : MatR n) (hZ : Z.IsHermitian) (q : V n) :
    2*couplingLinearTest F v Z q-couplingQuadraticTest F v Z q ≤ transverseSigma F v/2 := by
  have hc := coupling_test_cauchy F hn v hv Z hZ q
  have hq := coupling_quadratic_nonneg F hn v hv Z hZ q
  have hs := (transverseSigma_range F hn v hv).1
  have h := two_mul_le_add_of_sq_le_mul (div_nonneg hs (by norm_num : (0 : ℝ) ≤ 2)) hq hc
  linarith only [h]

/-- The exact completed-square identity displayed in (8.53). -/
theorem variational_completed_square (σ ell : ℝ) (hσ : σ ≠ 0) :
    2*ell-2*ell^2/σ = σ/2-(2/σ)*(ell-σ/2)^2 := by
  field_simp [hσ]
  ring

theorem variational_scalar_chain (σ ell Q : ℝ) (hσ : 0 < σ) (hc : ell^2 ≤ σ/2*Q) :
    2*ell-Q ≤ 2*ell-2*ell^2/σ ∧
      2*ell-2*ell^2/σ = σ/2-(2/σ)*(ell-σ/2)^2 ∧
        σ/2-(2/σ)*(ell-σ/2)^2 ≤ σ/2 := by
  have hq : 2*ell^2/σ ≤ Q := by
    apply (div_le_iff₀ hσ).mpr
    nlinarith only [hc]
  refine ⟨by linarith only [hq], variational_completed_square σ ell hσ.ne', ?_⟩
  have hn : 0 ≤ (2/σ)*(ell-σ/2)^2 := by positivity
  linarith only [hn]

end SharpCut.Certificate
