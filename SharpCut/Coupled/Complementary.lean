import SharpCut.Coupled.ComplementaryTests

/-! # Complementary coupled Cauchy inequality, including pole and trace endpoints -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Coupled
open Certificate
variable {n N : ℕ}

theorem weighted_complementary_pointwise (F : JohnFrame n N) (v : V n) (hv : ‖v‖ = 1)
    (H : Fin N → V n) (i : Fin N) :
    (F.weight i/(1-boostParameter n*height F v i)*(height F v i+inverseDimension n)*
      ⟪transverse v (F.contact i),H i⟫)^2 ≤
      reverseDefectTerm F v i*(plusContactWeight F v i*‖H i‖^2) := by
  have h := abs_real_inner_le_norm (transverse v (F.contact i)) (H i)
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [sq_abs, mul_pow, transverse_norm_sq v (F.contact i) hv (F.contact_unit i)] at hs
  change ⟪transverse v (F.contact i),H i⟫^2 ≤ (1-(height F v i)^2)*‖H i‖^2 at hs
  have hm := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (sq_nonneg (F.weight i/(1-boostParameter n*height F v i)))
      (sq_nonneg (height F v i+inverseDimension n)))
  convert hm using 1 <;> (try simp only [reverseDefectTerm, plusContactWeight]) <;> ring

theorem weighted_complementary_cauchy (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (H : Fin N → V n) :
    (∑ i, F.weight i/(1-boostParameter n*height F v i)*(height F v i+inverseDimension n)*
      ⟪transverse v (F.contact i),H i⟫)^2 ≤
      reverseDefect F v*(∑ i, plusContactWeight F v i*‖H i‖^2) := by
  rw [reverseDefect]
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => div_nonneg (mul_nonneg (F.weight_pos i).le
      (mul_nonneg (sub_nonneg.mpr (F.heights_bounds v hv i).2) (sq_nonneg _)))
        (height_denominator_pos F hn v hv i).le)
    (fun i _ => mul_nonneg (plusContactWeight_nonneg F hn v hv i) (sq_nonneg _))
    (fun i _ => weighted_complementary_pointwise F v hv H i)

/-- Lemma 10.3 in the actual ambient transverse realization; no commuting tests or endpoint exclusions. -/
theorem complementary_cauchy (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (Z : MatR n) (hZ : Z.IsHermitian) (q : V n) :
    ((Z*(endpointShift n • projector v-transversePerturbation F v)).trace+⟪q,transverseCoupling F v⟫)^2 ≤
      traceRemainder F v*complementaryQuadratic F v Z q := by
  have hb := inverseDimension_bounds hn
  have hCpos : 0 < complementaryFactor n := by
    unfold complementaryFactor
    exact div_pos (by linarith [hb.2]) (mul_pos (by linarith [hb.2]) (by linarith [hb.1]))
  have h := weighted_complementary_cauchy F hn v hv (complementaryTestVector F v Z q)
  change (complementaryLinearSum F v Z q)^2 ≤ reverseDefect F v*(∑ i, plusContactWeight F v i*‖complementaryTestVector F v Z q i‖^2) at h
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg (complementaryScale n))
  rw [← mul_pow, ← complementary_linear_contact_identity F hn v hv Z q,
    complementary_quadratic_contact_identity F hn v hv Z hZ q] at hm
  have hr : (complementaryScale n)^2*(reverseDefect F v*(complementaryFactor n*complementaryQuadratic F v Z q)) =
      traceRemainder F v*complementaryQuadratic F v Z q := by
    calc
      _ = ((complementaryScale n)^2*reverseDefect F v)*complementaryFactor n*complementaryQuadratic F v Z q := by ring
      _ = _ := by rw [complementary_reverse_coefficient F hn v hv, div_mul_cancel₀ _ hCpos.ne']
  rwa [hr] at hm

/-- The full endpoint norm consequence in Section 10.4, including sigma=0 and tau=0. -/
theorem coupling_endpoint_norm (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    ‖transverseCoupling F v‖^2 ≤ ((2-inverseDimension n)/4)*transverseSigma F v*traceRemainder F v := by
  have h := general_cauchy F hn v hv 0 Matrix.isHermitian_zero (transverseCoupling F v)
  simp only [forwardQuadratic, Matrix.zero_mul, Matrix.trace_zero, pow_two, zero_add, map_zero,
    ContinuousLinearMap.zero_apply, inner_zero_right, mul_zero, add_zero, real_inner_self_eq_norm_sq] at h
  by_cases hz : ‖transverseCoupling F v‖^2 = 0
  · rw [hz]
    have hb := inverseDimension_bounds hn
    exact mul_nonneg (mul_nonneg (by linarith [hb.2]) (transverseSigma_range F hn v hv).1) (traceRemainder_nonneg F hn v hv)
  · have hp : 0 < ‖transverseCoupling F v‖^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    apply le_of_mul_le_mul_right (a := ‖transverseCoupling F v‖^2) _ hp
    nlinarith only [h]


/-- Subtraction transport for the literal transverse matrix block. -/
theorem tailBlock_sub {m : ℕ} (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (A C : MatR (m+1)) :
    Geometry.tailBlock B (A-C) = Geometry.tailBlock B A-Geometry.tailBlock B C := by
  unfold Geometry.tailBlock
  rw [Geometry.inBasis_sub]
  rfl

/-- Lemma 10.3 literally for every symmetric m-by-m matrix and Euclidean m-vector. -/
theorem complementary_cauchy_transverse {m : ℕ} (F : JohnFrame (m+1) N) (hm : 1 ≤ m) (v : V (m+1)) (hv : ‖v‖ = 1)
    (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (hB : B 0 = v)
    (Z : MatR m) (hZ : Z.IsHermitian) (q : V m) :
    ((Z*(endpointShift (m+1) • (1 : MatR m)-Geometry.tailBlock B (transversePerturbation F v))).trace+
      ⟪q,Geometry.tailCoordinates B (transverseCoupling F v)⟫)^2 ≤
    traceRemainder F v*((Z^2*(cutWeight (m+1) • (1 : MatR m)-Geometry.tailBlock B (transversePerturbation F v))).trace+
      2*⟪q,Matrix.toEuclideanCLM (𝕜 := ℝ) Z (Geometry.tailCoordinates B (transverseCoupling F v))⟫+
      ((2-inverseDimension (m+1))/4*transverseSigma F v)*‖q‖^2) := by
  have hn : 2 ≤ m+1 := by omega
  have hE := transversePerturbation_isHermitian F v
  have hEv := transversePerturbation_axis F hn v hv
  have hj := transverseCoupling_orthogonal F v hv
  let D : MatR (m+1) := endpointShift (m+1) • projector v-transversePerturbation F v
  let C : MatR (m+1) := cutWeight (m+1) • projector v-transversePerturbation F v
  have hD : D.IsHermitian := ((projector_posSemidef v hv).isHermitian.smul (by rfl)).sub hE
  have hC : C.IsHermitian := ((projector_posSemidef v hv).isHermitian.smul (by rfl)).sub hE
  have hDv : Matrix.toEuclideanCLM (𝕜 := ℝ) D v = 0 := by
    dsimp only [D]
    rw [matrix_action_sub, matrix_action_smul, projector_action, transverse_axis_zero v hv, hEv, smul_zero, sub_zero]
  have hCv : Matrix.toEuclideanCLM (𝕜 := ℝ) C v = 0 := by
    dsimp only [C]
    rw [matrix_action_sub, matrix_action_smul, projector_action, transverse_axis_zero v hv, hEv, smul_zero, sub_zero]
  have htailD : Geometry.tailBlock B D = endpointShift (m+1) • (1 : MatR m)-Geometry.tailBlock B (transversePerturbation F v) := by
    dsimp only [D]
    rw [tailBlock_sub, Geometry.tailBlock_smul, tail_projector B v hB]
  have htailC : Geometry.tailBlock B C = cutWeight (m+1) • (1 : MatR m)-Geometry.tailBlock B (transversePerturbation F v) := by
    dsimp only [C]
    rw [tailBlock_sub, Geometry.tailBlock_smul, tail_projector B v hB]
  have hZsq : (extendMatrix B Z)^2 = extendMatrix B (Z^2) := by rw [pow_two, extendMatrix_mul, pow_two]
  have h := complementary_cauchy F hn v hv (extendMatrix B Z) (extendMatrix_hermitian B Z hZ) (extendVector B q)
  change ((extendMatrix B Z*D).trace+⟪extendVector B q,transverseCoupling F v⟫)^2 ≤ _ at h
  rw [extension_trace_product B v hv hB D hD hDv Z, htailD, extension_inner B v _ hB hj] at h
  unfold complementaryQuadratic at h
  change _ ≤ traceRemainder F v*((((extendMatrix B Z)^2)*C).trace+
    2*⟪extendVector B q,Matrix.toEuclideanCLM (𝕜 := ℝ) (extendMatrix B Z) (transverseCoupling F v)⟫+
    ((2-inverseDimension (m+1))/4*transverseSigma F v)*‖extendVector B q‖^2) at h
  rw [hZsq, extension_trace_product B v hv hB C hC hCv (Z^2), htailC,
    extension_mixed_pairing B v _ hB hj, extendVector_norm] at h
  exact h


theorem endpointShift_dimension (hn : 2 ≤ n) : ((n : ℝ)-1)*endpointShift n = sigmaStar n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hdim : (n : ℝ)*inverseDimension n = 1 := by unfold inverseDimension; field_simp [hn0]
  unfold endpointShift sigmaStar
  rw [← mul_div_assoc]
  congr 1
  linear_combination 2*hdim

/-- The shifted transverse perturbation has exactly the complementary trace tau. -/
theorem complementary_trace (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (endpointShift n • projector v-transversePerturbation F v).trace = traceRemainder F v := by
  have hP : (projector v).trace = (n : ℝ)-1 := by
    simp only [projector, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, Khachiyan.trace_outer, hv, one_pow]
  rw [Matrix.trace_sub, Matrix.trace_smul, hP, smul_eq_mul, transversePerturbation_trace F hn v hv, mul_comm,
    endpointShift_dimension hn]
  rfl

/-- Both zero trace-range endpoints force the actual coupling vector to vanish. -/
theorem coupling_zero_endpoints (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hz : transverseSigma F v = 0 ∨ traceRemainder F v = 0) : transverseCoupling F v = 0 := by
  have h := coupling_endpoint_norm F hn v hv
  have hnorm : ‖transverseCoupling F v‖^2 = 0 := by
    rcases hz with hs | ht
    · rw [hs, mul_zero, zero_mul] at h
      exact le_antisymm h (sq_nonneg _)
    · rw [ht, mul_zero] at h
      exact le_antisymm h (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

def oppositeBeta (n : ℕ) : ℝ := cutWeight n-endpointShift n

theorem oppositeBeta_explicit (hn : 2 ≤ n) :
    oppositeBeta n = (1-inverseDimension n)^2*(2+inverseDimension n)/(2*(2-inverseDimension n+(inverseDimension n)^2)) := by
  have hh : 2-inverseDimension n+(inverseDimension n)^2 ≠ 0 := by nlinarith [(inverseDimension_bounds hn).2, sq_nonneg (inverseDimension n)]
  unfold oppositeBeta cutWeight endpointShift
  field_simp [hh] <;> ring

theorem oppositeBeta_pos (hn : 2 ≤ n) : 0 < oppositeBeta n := by
  have hb := inverseDimension_bounds hn
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hp : 0 < 2+inverseDimension n := by linarith [hb.1]
  have hh : 0 < 2-inverseDimension n+(inverseDimension n)^2 := by nlinarith [hb.2, sq_nonneg (inverseDimension n)]
  rw [oppositeBeta_explicit hn]
  positivity

end SharpCut.Coupled
