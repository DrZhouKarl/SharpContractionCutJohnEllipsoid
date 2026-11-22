import SharpCut.Paper.EquationGapEquality
import SharpCut.Determinant.DimensionThree

/-! # Explicit logarithmic and elimination intermediates in Section 8 -/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SharpCut.Paper

/-- The full scalar theta chain in (8.21), including equal theta endpoints. -/
theorem theta_log_chain (theta1 theta2 : ℝ) (h1 : 0 ≤ theta1)
    (h12 : theta1 ≤ theta2) (h2 : theta2 < 1) :
    1-(1-theta2)/(1-theta1) ≤ Real.log ((1-theta1)/(1-theta2)) ∧
    1-(1-theta2)/(1-theta1) = (theta2-theta1)/(1-theta1) ∧
    theta2-theta1 ≤ (theta2-theta1)/(1-theta1) := by
  have hd1 : 0 < 1-theta1 := by linarith only [h12, h2]
  have hd2 : 0 < 1-theta2 := by linarith only [h2]
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hd1 hd2)
  rw [inv_div] at hl
  refine ⟨hl, ?_, ?_⟩
  · field_simp [hd1.ne']; ring
  · apply (le_div_iff₀ hd1).mpr
    have hp := mul_nonneg (sub_nonneg.mpr h12) h1
    nlinarith only [hp]

/-- Substitution of the two theta definitions in (8.20)–(8.21). -/
theorem theta_drop_identities (H kappa tau z delta : ℝ)
    (hz : z+kappa ≠ 0) (hd : H*z-tau ≠ 0)
    (hz0 : z+delta+kappa ≠ 0) (hd0 : H*(z+delta)-tau ≠ 0) :
    (1-delta/(z+delta+kappa))/(1-H*delta/(H*(z+delta)-tau)) =
      ((z+kappa)/(H*z-tau))/((z+delta+kappa)/(H*(z+delta)-tau)) ∧
    H*delta/(H*(z+delta)-tau)-delta/(z+delta+kappa) =
      delta*(H/(H*(z+delta)-tau)-1/(z+delta+kappa)) := by
  constructor
  · have htop : 1-delta/(z+delta+kappa) = (z+kappa)/(z+delta+kappa) := by
      field_simp [hz0]; ring
    have hbot : 1-H*delta/(H*(z+delta)-tau) = (H*z-tau)/(H*(z+delta)-tau) := by
      field_simp [hd0]; ring
    rw [htop, hbot]
    field_simp [hz, hd, hz0, hd0] <;> ring
  · ring

/-- The domain restrictions for the two actual theta definitions in (8.21). -/
theorem theta_parameter_bounds (H kappa tau z delta : ℝ)
    (hH : 0 < H) (hkappa : 0 ≤ kappa) (htau : 0 ≤ tau)
    (hz : 0 < z) (hdelta : 0 ≤ delta) (hd : 0 < H*z-tau) :
    0 ≤ delta/(z+delta+kappa) ∧
    delta/(z+delta+kappa) ≤ H*delta/(H*(z+delta)-tau) ∧
    H*delta/(H*(z+delta)-tau) < 1 := by
  have hz0 : 0 < z+delta+kappa := by linarith only [hz, hdelta, hkappa]
  have hd0 : 0 < H*(z+delta)-tau := by
    have hp := mul_nonneg hH.le hdelta
    nlinarith only [hd, hp]
  refine ⟨div_nonneg hdelta hz0.le, ?_, ?_⟩
  · apply (div_le_div_iff₀ hz0 hd0).mpr
    have hp := mul_nonneg hdelta (add_nonneg (mul_nonneg hH.le hkappa) htau)
    nlinarith only [hp]
  · apply (div_lt_one hd0).mpr
    nlinarith only [hd]

/-- The closed natural-power determinant of F0 displayed in (8.4). -/
theorem model_determinant_closed {n : ℕ} (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    (Certificate.modelF0 v).det =
      (2-SharpCut.inverseDimension n)^(n+1)/
        ((2 : ℝ)^n*(1-SharpCut.inverseDimension n)) := by
  rw [Determinant.modelF0_det_explicit hn v hv, div_pow]
  have hp : (2-SharpCut.inverseDimension n)^(n+1) =
      (2-SharpCut.inverseDimension n)^(n-1)*(2-SharpCut.inverseDimension n)^2 := by
    rw [← pow_add]
    congr 1
    omega
  have ht : (2 : ℝ)^n = 2^(n-1)*2 := by
    conv_lhs => rw [show n = (n-1)+1 by omega, pow_succ]
  rw [hp, ht]
  have h1 : 1-SharpCut.inverseDimension n ≠ 0 := by
    have hb := SharpCut.inverseDimension_bounds hn
    linarith only [hb.2]
  field_simp [h1]
  <;> ring

/-- Positivity of the elimination denominator in (8.56) and (8.58). -/
theorem three_delta_positive (sigma z : ℝ) (hs : 0 ≤ sigma) (hsh : sigma ≤ 3/4)
    (hzh : z ≤ sigma*(1+sigma)) : 0 < (11/3 : ℝ)*(1+sigma)-z := by
  have hp := mul_le_mul_of_nonneg_right hsh (by linarith only [hs] : 0 ≤ 1+sigma)
  nlinarith only [hp, hzh, hs]

/-- The weighted constraint elimination in (8.61), before a determinant bound. -/
theorem three_adjugate_elimination (sigma z r omega : ℝ)
    (hs : 0 ≤ sigma) (hz : 0 ≤ z)
    (hdelta : 0 < (11/3 : ℝ)*(1+sigma)-z)
    (hgram : (2/3-sigma)*r+omega ≤
      5*sigma/12*((2/3)^2-2/3*sigma+(z-sigma)/4))
    (hvar : ((1+sigma)*(1+4*sigma)-z)*r-4*(1+sigma)*omega ≤
      (5/8-5*sigma/6)/2*z*(1+sigma+z)) :
    (1+sigma)*r-omega ≤
      ((5*sigma/12*((2/3)^2-2/3*sigma+(z-sigma)/4))*(3*(1+sigma)+z)+
        (5/6)*(5/8-5*sigma/6)*z*(1+sigma+z))/((11/3)*(1+sigma)-z) := by
  have hg := mul_le_mul_of_nonneg_left hgram
    (show 0 ≤ 3*(1+sigma)+z by linarith only [hs, hz])
  have hv := mul_le_mul_of_nonneg_left hvar (by norm_num : (0 : ℝ) ≤ 5/3)
  have hsum := add_le_add hg hv
  have hc : (3*(1+sigma)+z)*((2/3-sigma)*r+omega)+
      (5/3)*(((1+sigma)*(1+4*sigma)-z)*r-4*(1+sigma)*omega) =
      ((11/3)*(1+sigma)-z)*((1+sigma)*r-omega) := by ring
  rw [hc] at hsum
  apply (le_div_iff₀ hdelta).mpr
  nlinarith only [hsum]

/-- The exact polynomial lower chain (8.62), independently of its final simplification. -/
theorem three_polynomial_elimination (sigma z r omega value : ℝ)
    (hs : 0 ≤ sigma) (hz : 0 ≤ z)
    (hgram : (2/3-sigma)*r+omega ≤
      5*sigma/12*((2/3)^2-2/3*sigma+(z-sigma)/4))
    (hvar : ((1+sigma)*(1+4*sigma)-z)*r-4*(1+sigma)*omega ≤
      (5/8-5*sigma/6)/2*z*(1+sigma+z))
    (hvalue : value = (1-5*sigma/12)*(1+sigma+(z-sigma)/4)-((1+sigma)*r-omega)) :
    Determinant.dimensionThreePolynomial sigma z ≤
      108*((11/3)*(1+sigma)-z)*(value-1) := by
  have hg := mul_le_mul_of_nonneg_left hgram
    (show 0 ≤ 3*(1+sigma)+z by linarith only [hs, hz])
  have hv := mul_le_mul_of_nonneg_left hvar (by norm_num : (0 : ℝ) ≤ 5/3)
  have hsum := add_le_add hg hv
  have hc : (3*(1+sigma)+z)*((2/3-sigma)*r+omega)+
      (5/3)*(((1+sigma)*(1+4*sigma)-z)*r-4*(1+sigma)*omega) =
      ((11/3)*(1+sigma)-z)*((1+sigma)*r-omega) := by ring
  rw [hc] at hsum
  have hid : 108*
      ((3*(1+sigma)+z)*(5*sigma/12*((2/3)^2-2/3*sigma+(z-sigma)/4))+
        (5/3)*((5/8-5*sigma/6)/2*z*(1+sigma+z))-
        ((11/3)*(1+sigma)-z)*((1+sigma)*r-omega)) =
      108*((11/3)*(1+sigma)-z)*(value-1)-
        Determinant.dimensionThreePolynomial sigma z := by
    rw [hvalue]
    unfold Determinant.dimensionThreePolynomial
    ring
  have hnonneg := mul_nonneg (by norm_num : (0 : ℝ) ≤ 108) (sub_nonneg.mpr hsum)
  rw [hid] at hnonneg
  exact sub_nonneg.mp hnonneg

end SharpCut.Paper

namespace SharpCut.Paper
open Matrix Certificate
variable {n N : ℕ}

/-- The exact selected variational value in (8.54), on its stated L>0 branch. -/
theorem selected_coupling_value (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n)
    (hv : ‖v‖ = 1) (hL : 0 < couplingL F v) :
    let w := Matrix.toEuclideanCLM (𝕜 := ℝ) (couplingK F v)⁻¹ (transverseCoupling F v)
    let q := (1/couplingL F v) • w
    2*couplingLinearTest F v (couplingZ F v) q-couplingQuadraticTest F v (couplingZ F v) q =
      transverseDeformation F v+‖w‖^2/couplingL F v ∧
    transverseDeformation F v+‖w‖^2/couplingL F v ≤ transverseSigma F v/2 := by
  dsimp only
  let w := Matrix.toEuclideanCLM (𝕜 := ℝ) (couplingK F v)⁻¹ (transverseCoupling F v)
  let q := (1/couplingL F v) • w
  have he := congrArg (fun A : MatR n => ⟪q, Matrix.toEuclideanCLM (𝕜 := ℝ) A
      (transverseCoupling F v)⟫) (couplingZ_twice F hn v hv)
  simp only [matrix_action_smul, real_inner_smul_right, matrix_action_sub,
    inner_sub_right, map_one, ContinuousLinearMap.one_apply] at he
  have hq : ⟪q,w⟫ = ‖w‖^2/couplingL F v := by
    dsimp only [q]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have hnorm : couplingL F v*‖q‖^2 = ‖w‖^2/couplingL F v := by
    dsimp only [q]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [hL.ne']
    <;> ring
  constructor
  · change 2*couplingLinearTest F v (couplingZ F v) q-
      couplingQuadraticTest F v (couplingZ F v) q = _
    simp only [couplingLinearTest, couplingQuadraticTest]
    rw [(couplingZ_trace_identities F hn v hv).1,
      (couplingZ_trace_identities F hn v hv).2]
    change 2*(transverseDeformation F v+⟪q,transverseCoupling F v⟫)-
      (transverseDeformation F v+4*⟪q,Matrix.toEuclideanCLM (𝕜 := ℝ)
        (couplingZ F v) (transverseCoupling F v)⟫+couplingL F v*‖q‖^2) = _
    linarith only [he, hq, hnorm]
  · have h := selected_test_bound F hn v hv q
    change transverseDeformation F v+2*⟪q,w⟫-couplingL F v*‖q‖^2 ≤ _ at h
    linarith only [h, hq, hnorm]

end SharpCut.Paper
