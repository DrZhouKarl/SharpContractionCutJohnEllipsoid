import SharpCut.Stability.Residual
import SharpCut.Certificate.DirectCoupling
import SharpCut.Gap.FrobeniusSpectral

/-! # Small-defect transverse spectral control, without assuming a positive E -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Stability
open Certificate
variable {n N : ℕ}

/-- The rational scalar implication used at both spectral endpoints in Lemma 9.3. -/
theorem small_deformation_eigenvalue (e : ℝ) (he : 0 < 1+2*e)
    (hsmall : e^2/(1+2*e) ≤ 1/2000) : |e| ≤ 1/40 := by
  have hq := (div_le_iff₀ he).mp hsmall
  apply abs_le.mpr
  constructor
  · by_contra h
    have hl : e < -(1/40) := lt_of_not_ge h
    nlinarith [sq_nonneg (e+1/40)]
  · by_contra h
    have hh : 1/40 < e := lt_of_not_ge h
    nlinarith [sq_nonneg (e-1/40)]

/-- Positive K=I+2E in the eigenbasis of E, with explicit eigenvalues. -/
theorem shifted_eigenbasis (E : MatR n) (hE : E.IsHermitian) :
    Geometry.inBasis hE.eigenvectorBasis (1+(2 : ℝ) • E) =
      Matrix.diagonal (fun i => 1+2*hE.eigenvalues i) := by
  rw [Geometry.inBasis_add, Geometry.inBasis_one, Geometry.inBasis_smul,
    Gap.inEigenbasis_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem shifted_eigenvalues_pos (E : MatR n) (hE : E.IsHermitian) (hK : (1+(2 : ℝ) • E).PosDef) (i : Fin n) :
    0 < 1+2*hE.eigenvalues i := by
  have h := (Geometry.inBasis_posDef hE.eigenvectorBasis _ hK).diag_pos (i := i)
  rwa [shifted_eigenbasis E hE, Matrix.diagonal_apply_eq] at h

theorem diagonal_inverse_nonzero (eigen : Fin n → ℝ) (heigen : ∀ i, eigen i ≠ 0) :
    (Matrix.diagonal eigen)⁻¹ = Matrix.diagonal (fun i => (eigen i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j; simp [heigen i]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

/-- Exact ambient trace identity; the null axial eigenvalue contributes zero. -/
theorem deformation_spectral (E : MatR n) (hE : E.IsHermitian) (hK : (1+(2 : ℝ) • E).PosDef) :
    (E^2*(1+(2 : ℝ) • E)⁻¹).trace = ∑ i, (hE.eigenvalues i)^2/(1+2*hE.eigenvalues i) := by
  rw [← Geometry.inBasis_trace hE.eigenvectorBasis, Geometry.inBasis_mul,
    ← Geometry.inBasis_inv hE.eigenvectorBasis _ hK, shifted_eigenbasis E hE]
  have hpow : Geometry.inBasis hE.eigenvectorBasis (E^2) = Matrix.diagonal (fun i => (hE.eigenvalues i)^2) := by
    rw [pow_two, Geometry.inBasis_mul, Gap.inEigenbasis_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [pow_two]
  rw [hpow, diagonal_inverse_nonzero _ (fun i => (shifted_eigenvalues_pos E hE hK i).ne'), Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_eq_mul_inv]

theorem couplingL_lt_one (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) : couplingL F v < 1 := by
  have hb := inverseDimension_bounds hn
  have hs := (transverseSigma_range F hn v hv).1
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have hden : 0 < 2-inverseDimension n+(inverseDimension n)^2 := by positivity
  have hratio : (2-inverseDimension n)*(1-inverseDimension n)/(2-inverseDimension n+(inverseDimension n)^2) < 1 := by
    apply (div_lt_one hden).mpr
    nlinarith only [hb.1]
  have hm : 0 ≤ (2-inverseDimension n)*transverseSigma F v/2 := by positivity
  unfold couplingL
  linarith only [hratio, hm]

/-- Direct coupling in ordinary sum form, including sigma=0. -/
theorem local_deformation_coupling (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    transverseDeformation F v+
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (couplingK F v)⁻¹ (transverseCoupling F v)‖^2 ≤ transverseSigma F v/2 := by
  have h := direct_coupling_bound F hn v hv
  have hdiff : 0 ≤ transverseSigma F v/2-transverseDeformation F v := sub_nonneg.mpr h.1
  have hmul := mul_le_mul_of_nonneg_right (couplingL_lt_one F hn v hv).le hdiff
  nlinarith only [h.2, hmul]

/-- All actual eigenvalues, including the zero axial one, lie in the prescribed interval. -/
theorem local_transverse_eigenvalues (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hsmall : transverseSigma F v ≤ 1/1000) (i : Fin n) :
    |(transversePerturbation_isHermitian F v).eigenvalues i| ≤ 1/40 := by
  have hE := transversePerturbation_isHermitian F v
  have hK : (1+(2 : ℝ) • transversePerturbation F v).PosDef := couplingK_posDef F hn v hv
  have hp := shifted_eigenvalues_pos (transversePerturbation F v) hE hK
  have hs : ∑ j, (hE.eigenvalues j)^2/(1+2*hE.eigenvalues j) ≤ transverseSigma F v/2 := by
    rw [← deformation_spectral _ hE hK]
    exact deformation_upper F hn v hv
  have hi : (hE.eigenvalues i)^2/(1+2*hE.eigenvalues i) ≤
      ∑ j, (hE.eigenvalues j)^2/(1+2*hE.eigenvalues j) :=
    Finset.single_le_sum (fun j _ => div_nonneg (sq_nonneg _) (hp j).le) (Finset.mem_univ i)
  exact small_deformation_eigenvalue _ (hp i) (by linarith only [hi, hs, hsmall])


/-- Exact squared action in any orthonormal basis that diagonalizes A. -/
theorem norm_sq_diagonal_basis (B : OrthonormalBasis (Fin n) ℝ (V n)) (A : MatR n) (eigen : Fin n → ℝ)
    (hA : Geometry.inBasis B A = Matrix.diagonal eigen) (u : V n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A u‖^2 = ∑ i, (eigen i)^2*(B.repr u i)^2 := by
  rw [← Geometry.basisMatrix_norm B (Matrix.toEuclideanCLM (𝕜 := ℝ) A u),
    ← Geometry.inBasis_action B A u, hA, EuclideanSpace.real_norm_sq_eq]
  simp only [Khachiyan.matrix_action_ofLp, Matrix.mulVec_diagonal, Geometry.basisMatrix_action_repr,
    mul_pow]

theorem hermitian_frobenius_spectral (E : MatR n) (hE : E.IsHermitian) :
    (frobeniusNorm E)^2 = ∑ i, (hE.eigenvalues i)^2 := by
  rw [Gap.frobeniusNorm_sq_trace _ hE, ← Geometry.inBasis_trace hE.eigenvectorBasis]
  have hpow : Geometry.inBasis hE.eigenvectorBasis (E^2) = Matrix.diagonal (fun i => (hE.eigenvalues i)^2) := by
    rw [pow_two, Geometry.inBasis_mul, Gap.inEigenbasis_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [pow_two]
  rw [hpow, Matrix.trace_diagonal]

/-- Spectral confinement controls E and j together at the paper's exact coefficients. -/
theorem local_metric_norm_bound (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hsmall : transverseSigma F v ≤ 1/1000) :
    (frobeniusNorm (transversePerturbation F v))^2+(20/21 : ℝ)*‖transverseCoupling F v‖^2 ≤
      (21/40 : ℝ)*transverseSigma F v := by
  let E := transversePerturbation F v
  have hE := transversePerturbation_isHermitian F v
  let B := hE.eigenvectorBasis
  have hK : (1+(2 : ℝ) • E).PosDef := couplingK_posDef F hn v hv
  have hp := shifted_eigenvalues_pos E hE hK
  have he (i : Fin n) : 19/20 ≤ 1+2*hE.eigenvalues i ∧ 1+2*hE.eigenvalues i ≤ 21/20 := by
    have h := abs_le.mp (local_transverse_eigenvalues F hn v hv hsmall i)
    constructor <;> linarith only [h.1, h.2]
  have hEnorm : (frobeniusNorm E)^2 ≤ (21/20 : ℝ)*transverseDeformation F v := by
    rw [hermitian_frobenius_spectral E hE]
    change _ ≤ (21/20 : ℝ)*(E^2*(1+(2 : ℝ) • E)⁻¹).trace
    rw [deformation_spectral E hE hK, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (hp i)).mpr
    have h := mul_le_mul_of_nonneg_right (he i).2 (sq_nonneg (hE.eigenvalues i))
    convert h using 1 <;> ring
  have hInv : Geometry.inBasis B (couplingK F v)⁻¹ = Matrix.diagonal (fun i => (1+2*hE.eigenvalues i)⁻¹) := by
    rw [← Geometry.inBasis_inv B _ (couplingK_posDef F hn v hv)]
    change (Geometry.inBasis hE.eigenvectorBasis (1+(2 : ℝ) • E))⁻¹ = _
    rw [shifted_eigenbasis E hE, diagonal_inverse_nonzero _ (fun i => (hp i).ne')]
  have hjnorm : (20/21 : ℝ)*‖transverseCoupling F v‖^2 ≤
      (21/20 : ℝ)*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (couplingK F v)⁻¹ (transverseCoupling F v)‖^2 := by
    rw [← B.repr.norm_map (transverseCoupling F v), EuclideanSpace.real_norm_sq_eq,
      norm_sq_diagonal_basis B _ _ hInv, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hinv : (20/21 : ℝ) ≤ (1+2*hE.eigenvalues i)⁻¹ := by
      rw [← one_div, le_div_iff₀ (hp i)]
      linarith only [(he i).2]
    have hs := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 20/21) (inv_pos.mpr (hp i)).le).mpr hinv
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (B.repr (transverseCoupling F v) i))
    nlinarith only [hm]
  have hcouple := local_deformation_coupling F hn v hv
  have hmul := mul_le_mul_of_nonneg_left hcouple (by norm_num : (0 : ℝ) ≤ 21/20)
  nlinarith only [hEnorm, hjnorm, hmul]

end SharpCut.Stability
