import SharpCut.Stability.PolarPerturbation
import SharpCut.Stability.CenterRecovery
import SharpCut.Gap.Matching

/-! # Ordered inverse and matching transfers for the actual ellipsoid shape -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Stability
open Certificate Gap Optimization
variable {n N : ℕ}

/-- Matching is transferred through a genuine positive square root. -/
theorem matching_shape_error (A M : MatR n) (hM : M.PosDef) (ell : ℝ) (hell : 0 < ell)
    (hq : ∀ u : V n, ell*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) M u⟫) :
    frobeniusNorm (A-M⁻¹) ≤ frobeniusNorm (matchingMatrix A M-1)/ell := by
  have hmatch : matchingMatrix M⁻¹ M = 1 := (matchingMatrix_one_iff M⁻¹ M hM).mpr rfl
  have hdiff : CFC.sqrt M*(A-M⁻¹)*CFC.sqrt M = matchingMatrix A M-1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    change matchingMatrix A M-matchingMatrix M⁻¹ M = _
    rw [hmatch]
  have h := sqrt_conjugation_lower M (A-M⁻¹) hM ell hell hq
  rwa [hdiff] at h

/-- Exact inverse difference in the paper's multiplication order. -/
theorem inverse_difference_ordered (A B : MatR n) (hA : A.PosDef) (hB : B.PosDef) :
    A⁻¹-B⁻¹ = A⁻¹*(B-A)*B⁻¹ := by
  have huA : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have huB : IsUnit B.det := isUnit_iff_ne_zero.mpr hB.det_pos.ne'
  symm
  calc
    _ = A⁻¹*(B*B⁻¹)-(A⁻¹*A)*B⁻¹ := by simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv B huB, Matrix.nonsing_inv_mul A huA, Matrix.mul_one, Matrix.one_mul]

/-- The inverse norm error uses both lower spectra and no dimension factor. -/
theorem inverse_difference_frobenius (A B : MatR n) (hA : A.PosDef) (hB : B.PosDef)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hAq : ∀ u : V n, a*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) A u⟫)
    (hBq : ∀ u : V n, b*‖u‖^2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) B u⟫) :
    frobeniusNorm (A⁻¹-B⁻¹) ≤ frobeniusNorm (A-B)/(a*b) := by
  rw [inverse_difference_ordered A B hA hB]
  have ht : B-A = -(A-B) := by abel
  have h1 := frobeniusNorm_mul_operator_left A⁻¹ (B-A)
  have h2 := frobeniusNorm_mul_operator_right (A⁻¹*(B-A)) B⁻¹
  have hopA := inverse_operator_bound A hA a ha hAq
  have hopB := inverse_operator_bound B hB b hb hBq
  have h3 := mul_le_mul_of_nonneg_right hopA (show 0 ≤ frobeniusNorm (B-A) from Real.sqrt_nonneg _)
  have h4 := mul_le_mul_of_nonneg_right hopB (show 0 ≤ frobeniusNorm (A⁻¹*(B-A)) from Real.sqrt_nonneg _)
  have h5 := mul_le_mul_of_nonneg_right (h1.trans h3) (show (0 : ℝ) ≤ 1/b from (div_pos (by norm_num) hb).le)
  rw [ht, frobeniusNorm_neg] at h5
  rw [← ht] at h5
  have hfinal : frobeniusNorm (A⁻¹*(B-A)*B⁻¹) ≤ (1/a*frobeniusNorm (A-B))*(1/b) := by
    have h4' : frobeniusNorm (A⁻¹*(B-A))*operatorNorm B⁻¹ ≤ frobeniusNorm (A⁻¹*(B-A))*(1/b) := by
      simpa only [mul_comm] using h4
    exact h2.trans (h4'.trans h5)
  have heq : (1/a*frobeniusNorm (A-B))*(1/b) = frobeniusNorm (A-B)/(a*b) := by
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  rwa [heq] at hfinal

/-- Matrix matching for the explicit pair, measured by the total volume deficit. -/
theorem near_extremal_matching (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (F : JohnFrame n N) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A)
    (hε : 0 ≤ volumeDeficit n A) (hsmall : volumeDeficit n A ≤ 1/1000000) :
    frobeniusNorm (matchingMatrix A (frameMatrix F v)-1) ≤ 2*Real.sqrt (volumeDeficit n A) := by
  have hp := frame_primal F hs v hA
  have hd := explicit_dual_feasible F hn v hv
  have he := exact_volume_deficit hn hK hJ F hs v hv hA
  have hgap := frame_pair_gap F hn hs v hv hA
  have hG : dualityGap A (frameMatrix F v) ≤ volumeDeficit n A := by nlinarith only [he.1, he.2.1, hgap]
  have hGsmall : dualityGap A (aggregate (cutNormals F v) (rotatedVectors F v (polarRotation (unrotatedQ F v)))) ≤ 1/4 := by
    rw [rotated_aggregate_eq_polar F hn v hv]
    exact hG.trans (hsmall.trans (by norm_num))
  have hm := matrix_matching hp hd hGsmall
  rw [rotated_aggregate_eq_polar F hn v hv] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hG) (by norm_num))

/-- The square-root inverse reconstruction displayed in (6.5). -/
theorem matching_error_reconstruction (A M : MatR n) (hM : M.PosDef) :
    A-M⁻¹ = (CFC.sqrt M)⁻¹*(matchingMatrix A M-1)*(CFC.sqrt M)⁻¹ := by
  have hS := sqrt_posDef M hM
  have hu : IsUnit (CFC.sqrt M).det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hmatch : matchingMatrix M⁻¹ M = 1 := (matchingMatrix_one_iff M⁻¹ M hM).mpr rfl
  have hdiff : CFC.sqrt M*(A-M⁻¹)*CFC.sqrt M = matchingMatrix A M-1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    change matchingMatrix A M-matchingMatrix M⁻¹ M = _
    rw [hmatch]
  rw [← hdiff]
  symm
  calc
    _ = ((CFC.sqrt M)⁻¹*CFC.sqrt M)*(A-M⁻¹)*(CFC.sqrt M*(CFC.sqrt M)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]

/-- The exact 30*sqrt(epsilon) shape bound for every nearly extremal feasible cut ellipsoid. -/
theorem near_extremal_shape_coefficient (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (F : JohnFrame n N) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A)
    (hε : 0 ≤ volumeDeficit n A) (hsmall : volumeDeficit n A ≤ 1/1000000) :
    frobeniusNorm (A-Sharpness.modelShape v) ≤ (20/7+1200/49 : ℝ)*Real.sqrt (volumeDeficit n A) := by
  have hQ := unrotatedQ_det_pos F hn v hv
  have hM := polarMatrix_posDef hQ
  have hM₀ := Sharpness.inverseModel_posDef hn v
  have hpolar := near_extremal_polar_bounds hn hK hJ F hs v hv hA hε hsmall
  have hMq := polar_quadratic_lower hn v hv (unrotatedQ F v) hQ hpolar.1
  have hM₀q := model_quadratic_seven_tenths hn v hv
  have hmatch := near_extremal_matching hn hK hJ F hs v hv hA hε hsmall
  have h1 := matching_shape_error A (frameMatrix F v) hM (7/10) (by norm_num) hMq
  have h2 := inverse_difference_frobenius (frameMatrix F v) (inverseModel v) hM hM₀
    (7/10) (7/10) (by norm_num) (by norm_num) hMq hM₀q
  have hmodel : Sharpness.modelShape v = (inverseModel v)⁻¹ := Sharpness.modelShape_eq_inverse hn v hv
  have hsplit : A-Sharpness.modelShape v = (A-(frameMatrix F v)⁻¹)+((frameMatrix F v)⁻¹-(inverseModel v)⁻¹) := by rw [hmodel]; abel
  have hnorm := frobeniusNorm_add_le (A-(frameMatrix F v)⁻¹) ((frameMatrix F v)⁻¹-(inverseModel v)⁻¹)
  rw [← hsplit] at hnorm
  have h1' := (le_div_iff₀ (by norm_num : (0 : ℝ) < 7/10)).mp h1
  have h2' := (le_div_iff₀ (by norm_num : (0 : ℝ) < (7/10)*(7/10))).mp h2
  have hp := Real.sqrt_nonneg (volumeDeficit n A)
  have hpolarnorm : frobeniusNorm (frameMatrix F v-inverseModel v) ≤ 12*Real.sqrt (volumeDeficit n A) := hpolar.2.2.2
  nlinarith only [hnorm, h1', h2', hmatch, hpolarnorm, hp]

/-- The final rounded shape constant in Theorem 6.2, including epsilon=0. -/
theorem near_extremal_shape_bound (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (F : JohnFrame n N) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A)
    (hε : 0 ≤ volumeDeficit n A) (hsmall : volumeDeficit n A ≤ 1/1000000) :
    frobeniusNorm (A-Sharpness.modelShape v) ≤ 30*Real.sqrt (volumeDeficit n A) := by
  have h := near_extremal_shape_coefficient hn hK hJ F hs v hv hA hε hsmall
  have hp := Real.sqrt_nonneg (volumeDeficit n A)
  nlinarith only [h, hp]

end SharpCut.Stability
