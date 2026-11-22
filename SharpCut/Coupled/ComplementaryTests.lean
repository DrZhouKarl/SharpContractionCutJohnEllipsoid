import SharpCut.Coupled.ComplementaryMoments

/-! # Exact complementary linear and quadratic test identities -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Coupled
open Certificate
variable {n N : ℕ}

def complementaryTestVector (F : JohnFrame n N) (v : V n) (Z : MatR n) (q : V n) (i : Fin N) : V n :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i))-
    (complementaryGamma n*(height F v i-inverseDimension n)) • q

def complementaryLinearSum (F : JohnFrame n N) (v : V n) (Z : MatR n) (q : V n) : ℝ :=
  ∑ i, F.weight i/(1-boostParameter n*height F v i)*(height F v i+inverseDimension n)*
    ⟪transverse v (F.contact i),complementaryTestVector F v Z q i⟫

def complementaryQuadratic (F : JohnFrame n N) (v : V n) (Z : MatR n) (q : V n) : ℝ :=
  (Z^2*(cutWeight n • projector v-transversePerturbation F v)).trace+
    2*⟪q,Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverseCoupling F v)⟫+
    ((2-inverseDimension n)/4*transverseSigma F v)*‖q‖^2

theorem trace_outer_linear (Z : MatR n) (y : V n) : (Z*outer y).trace = ⟪y,Matrix.toEuclideanCLM (𝕜 := ℝ) Z y⟫ :=
  Optimization.trace_mul_cross Z y y

theorem complementaryLinearSum_split (F : JohnFrame n N) (v : V n) (Z : MatR n) (q : V n) :
    complementaryLinearSum F v Z q = (Z*plusEndpointMoment F v).trace-
      complementaryGamma n*⟪differenceSquareMoment F v,q⟫ := by
  unfold complementaryLinearSum complementaryTestVector plusEndpointMoment differenceSquareMoment
  simp only [inner_sub_right, real_inner_smul_right, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, trace_outer_linear, sum_inner, real_inner_smul_left, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The exact complementary linear contact representation (10.16). -/
theorem complementary_linear_contact_identity (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (Z : MatR n) (q : V n) :
    (Z*(endpointShift n • projector v-transversePerturbation F v)).trace+⟪q,transverseCoupling F v⟫ =
      complementaryScale n*complementaryLinearSum F v Z q := by
  have hm := congrArg (fun A : MatR n => (Z*A).trace) (complementary_matrix_moment F hn v hv)
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at hm
  have hvect := congrArg (fun u : V n => ⟪u,q⟫) (gamma_difference_identity F hn v hv)
  rw [real_inner_smul_left, inner_neg_left, real_inner_comm q (transverseCoupling F v)] at hvect
  rw [← complementary_gamma_relation hn] at hvect
  rw [complementaryLinearSum_split]
  nlinarith only [hm, hvect]

theorem complementaryTestVector_norm_square (F : JohnFrame n N) (v : V n) (Z : MatR n) (q : V n) (i : Fin N) :
    ‖complementaryTestVector F v Z q i‖^2 =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i))‖^2-
      2*complementaryGamma n*(height F v i-inverseDimension n)*
        ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i)),q⟫+
      (complementaryGamma n)^2*(height F v i-inverseDimension n)^2*‖q‖^2 := by
  rw [complementaryTestVector, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, mul_pow]
  ring

theorem plus_scalar_mass (F : JohnFrame n N) (v : V n) :
    (∑ i, plusContactWeight F v i*(height F v i-inverseDimension n)^2) = frameDefect F v := by
  unfold plusContactWeight frameDefect defectTerm
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem complementary_mixed_pairing (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (Z : MatR n) (q : V n) :
    -complementaryGamma n*(∑ i, plusContactWeight F v i*(height F v i-inverseDimension n)*
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i)),q⟫) =
      complementaryFactor n*⟪q,Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverseCoupling F v)⟫ := by
  have h := congrArg (fun u : V n => ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Z u,q⟫) (complementary_mixed_moment F hn v hv)
  simp only [map_smul, real_inner_smul_left, plusMixedMoment, map_sum, sum_inner] at h
  rw [real_inner_comm q (Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverseCoupling F v))] at h
  exact h

/-- The exact complementary quadratic expansion in (10.18). -/
theorem complementary_quadratic_contact_identity (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (Z : MatR n) (hZ : Z.IsHermitian) (q : V n) :
    (∑ i, plusContactWeight F v i*‖complementaryTestVector F v Z q i‖^2) =
      complementaryFactor n*complementaryQuadratic F v Z q := by
  have hsplit : (∑ i, plusContactWeight F v i*‖complementaryTestVector F v Z q i‖^2) =
      (∑ i, plusContactWeight F v i*‖Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i))‖^2)-
      2*complementaryGamma n*(∑ i, plusContactWeight F v i*(height F v i-inverseDimension n)*
        ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i)),q⟫)+
      (complementaryGamma n)^2*(∑ i, plusContactWeight F v i*(height F v i-inverseDimension n)^2)*‖q‖^2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [complementaryTestVector_norm_square]
    ring
  have hM : (∑ i, plusContactWeight F v i • outer (transverse v (F.contact i))) = transversePlusMoment F v := rfl
  rw [hsplit, weighted_action_norm_square Z hZ, hM, transversePlusMoment_identity F hn v hv,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, plus_scalar_mass]
  have hm := complementary_mixed_pairing F hn v hv Z q
  have hs := congrArg (fun x : ℝ => x*‖q‖^2) (complementary_sigma_coefficient F hn v)
  unfold complementaryFactor at *
  unfold complementaryQuadratic
  nlinarith only [hm, hs]

end SharpCut.Coupled
