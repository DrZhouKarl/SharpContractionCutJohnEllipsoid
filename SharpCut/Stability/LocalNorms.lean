import SharpCut.Stability.LocalSpectrum

/-! # Local Euclidean coupling bounds without dimension factors -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Stability
open Certificate
variable {n N : ℕ}

/-- Operator control derived from the actual orthonormal spectral coordinates. -/
theorem hermitian_action_bound (E : MatR n) (hE : E.IsHermitian) (M : ℝ) (hM : 0 ≤ M)
    (he : ∀ i, |hE.eigenvalues i| ≤ M) (u : V n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) E u‖ ≤ M*‖u‖ := by
  have hs : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) E u‖^2 ≤ (M*‖u‖)^2 := by
    rw [norm_sq_diagonal_basis hE.eigenvectorBasis E _ (Gap.inEigenbasis_diagonal E hE), mul_pow,
      ← hE.eigenvectorBasis.repr.norm_map u, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (sq_le_sq' (abs_le.mp (he i)).1 (abs_le.mp (he i)).2) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp hs

theorem hermitian_quadratic_bound (E : MatR n) (hE : E.IsHermitian) (M : ℝ) (hM : 0 ≤ M)
    (he : ∀ i, |hE.eigenvalues i| ≤ M) (u : V n) :
    |⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) E u⟫| ≤ M*‖u‖^2 := by
  have h := abs_real_inner_le_norm u (Matrix.toEuclideanCLM (𝕜 := ℝ) E u)
  have hm := mul_le_mul_of_nonneg_left (hermitian_action_bound E hE M hM he u) (norm_nonneg u)
  exact h.trans (by convert hm using 1 <;> ring)

/-- The Gram constraint gives the additional coupling bound used in (9.12). -/
theorem local_gram_coupling (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hsmall : transverseSigma F v ≤ 1/1000) :
    ‖transverseCoupling F v‖^2 ≤ axialDeficit F v*(cutWeight n+1/40) := by
  let j := transverseCoupling F v
  have hj : ⟪j,v⟫ = 0 := by rw [real_inner_comm]; exact transverseCoupling_orthogonal F v hv
  have hgram := transverse_coupling_bound F hn v j hv hj
  rw [real_inner_self_eq_norm_sq] at hgram
  have hquad := abs_le.mp (hermitian_quadratic_bound (transversePerturbation F v)
    (transversePerturbation_isHermitian F v) (1/40) (by norm_num)
    (local_transverse_eigenvalues F hn v hv hsmall) j)
  have hx : 0 ≤ axialDeficit F v := by
    unfold axialDeficit
    have hb := inverseDimension_bounds hn
    exact div_nonneg (frameDefect_nonneg F hn v hv) (by have hb0 := hb.1; positivity)
  have hm := mul_le_mul_of_nonneg_left hquad.1 hx
  by_cases hz : ‖j‖^2 = 0
  · change ‖j‖^2 ≤ _
    rw [hz]
    exact mul_nonneg hx (by have hb0 := (inverseDimension_bounds hn).1; unfold cutWeight; positivity)
  · have hp : 0 < ‖j‖^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    change ‖j‖^2 ≤ _
    apply le_of_mul_le_mul_right (a := ‖j‖^2) _ hp
    nlinarith only [hgram, hm]

/-- Exact scalar collection of the x,t coefficients in the local argument. -/
theorem local_scalar_bounds (b σ : ℝ) (hb : 0 < b) (hbh : b ≤ 1/2)
    (hs : 0 ≤ σ) (hsh : σ ≤ 1/1000) :
    ((2-b)/4*σ)*((1+b)/2+1/40) ≤ (47/160 : ℝ)*σ ∧
    ((2-b)/4*σ)^2 ≤ σ/4000 := by
  have hdt : ((2-b)/4)*((1+b)/2) ≤ 9/32 := by nlinarith [sq_nonneg (b-1/2)]
  have hd : 0 ≤ (2-b)/4 ∧ (2-b)/4 ≤ 1/2 := by constructor <;> linarith
  have hm := mul_le_mul_of_nonneg_right hdt hs
  have hx := mul_le_mul_of_nonneg_right hd.2 hs
  have hxp : 0 ≤ (2-b)/4*σ := mul_nonneg hd.1 hs
  have hsprod := mul_le_mul_of_nonneg_right hsh hs
  constructor
  · nlinarith only [hm, hx]
  · have hsq := (sq_le_sq₀ hxp (by positivity : 0 ≤ σ/2)).mpr (by linarith only [hx])
    nlinarith only [hsq, hsprod]

theorem local_coupling_bounds (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hsmall : transverseSigma F v ≤ 1/1000) :
    ‖transverseCoupling F v‖^2 ≤ (47/160 : ℝ)*transverseSigma F v ∧
    (axialDeficit F v)^2 ≤ transverseSigma F v/4000 := by
  have hb := inverseDimension_bounds hn
  have hs := (transverseSigma_range F hn v hv).1
  have hscalar := local_scalar_bounds (inverseDimension n) (transverseSigma F v) hb.1 hb.2 hs hsmall
  have hgram := local_gram_coupling F hn v hv hsmall
  rw [axialDeficit_sigma F hn v, cutWeight] at hgram
  refine ⟨hgram.trans hscalar.1, ?_⟩
  rw [axialDeficit_sigma F hn v]
  exact hscalar.2

end SharpCut.Stability
