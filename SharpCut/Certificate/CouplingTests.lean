import SharpCut.Certificate.CouplingMoments

/-! # Exact linear and quadratic selected-test identities (8.52) -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

def couplingTestVector (F : JohnFrame n N) (v : V n) (Z : MatR n) (q : V n) (i : Fin N) : V n :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i))+
    (couplingGamma n*(height F v i+inverseDimension n)) • q

def couplingLinearTest (F : JohnFrame n N) (v : V n) (Z : MatR n) (q : V n) : ℝ :=
  (Z*transversePerturbation F v).trace+⟪q, transverseCoupling F v⟫

def couplingQuadraticTest (F : JohnFrame n N) (v : V n) (Z : MatR n) (q : V n) : ℝ :=
  (Z^2*(projector v+(2 : ℝ) • transversePerturbation F v)).trace+
    4*⟪q, Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverseCoupling F v)⟫+couplingL F v*‖q‖^2

def couplingLinearSum (F : JohnFrame n N) (v : V n) (Z : MatR n) (q : V n) : ℝ :=
  ∑ i, F.weight i/(1-boostParameter n*height F v i)*(height F v i-inverseDimension n)*
    ⟪transverse v (F.contact i), couplingTestVector F v Z q i⟫

theorem trace_action_square_outer (Z : MatR n) (hZ : Z.IsHermitian) (u : V n) :
    (Z^2*outer u).trace = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Z u‖^2 := by
  change (Z^2*Matrix.vecMulVec u.ofLp u.ofLp).trace = _
  rw [Optimization.trace_mul_cross, pow_two, matrix_action_mul,
    Khachiyan.inner_matrix_action_symm hZ.isSymm, real_inner_self_eq_norm_sq]

theorem weighted_action_norm_square {ι : Type*} [Fintype ι] (Z : MatR n) (hZ : Z.IsHermitian)
    (y : ι → V n) (w : ι → ℝ) :
    (∑ i, w i*‖Matrix.toEuclideanCLM (𝕜 := ℝ) Z (y i)‖^2) =
      (Z^2*(∑ i, w i • outer (y i))).trace := by
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    trace_action_square_outer Z hZ, smul_eq_mul]

theorem minus_scalar_mass (F : JohnFrame n N) (v : V n) :
    (∑ i, minusContactWeight F v i*(height F v i+inverseDimension n)^2) = reverseDefect F v := by
  unfold minusContactWeight reverseDefect reverseDefectTerm
  apply Finset.sum_congr rfl; intro i hi; ring

theorem couplingTestVector_norm_square (F : JohnFrame n N) (v : V n) (Z : MatR n)
    (q : V n) (i : Fin N) :
    ‖couplingTestVector F v Z q i‖^2 =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i))‖^2+
      2*couplingGamma n*(height F v i+inverseDimension n)*
        ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i)), q⟫+
      (couplingGamma n)^2*(height F v i+inverseDimension n)^2*‖q‖^2 := by
  rw [couplingTestVector, norm_add_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, mul_pow]
  ring

theorem gamma_mixed_pairing (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (Z : MatR n) (q : V n) :
    (∑ i, minusContactWeight F v i*(2*couplingGamma n*(height F v i+inverseDimension n)*
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i)), q⟫)) =
        (4*(2-inverseDimension n)/(2+inverseDimension n))*
          ⟪q, Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverseCoupling F v)⟫ := by
  have h := congrArg (fun u : V n => ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Z u, q⟫)
    (gamma_mixed_identity F hn v hv)
  simp only [map_smul, real_inner_smul_left] at h
  unfold minusMixedMoment at h
  simp only [map_sum, map_smul, sum_inner, real_inner_smul_left] at h
  calc
    _ = 2*(couplingGamma n*∑ i, minusContactWeight F v i*(height F v i+inverseDimension n)*
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i)), q⟫) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i hi; ring
    _ = _ := by rw [h, real_inner_comm]; ring

theorem coupling_quadratic_identity (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (Z : MatR n) (hZ : Z.IsHermitian) (q : V n) :
    (∑ i, minusContactWeight F v i*‖couplingTestVector F v Z q i‖^2) =
      (2-inverseDimension n)/(2+inverseDimension n)*couplingQuadraticTest F v Z q := by
  have hsplit : (∑ i, minusContactWeight F v i*‖couplingTestVector F v Z q i‖^2) =
      (∑ i, minusContactWeight F v i*‖Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i))‖^2)+
      (∑ i, minusContactWeight F v i*(2*couplingGamma n*(height F v i+inverseDimension n)*
        ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i)), q⟫))+
      (∑ i, minusContactWeight F v i*((couplingGamma n)^2*
        (height F v i+inverseDimension n)^2*‖q‖^2)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [couplingTestVector_norm_square]
    ring
  rw [hsplit, weighted_action_norm_square Z hZ, gamma_mixed_pairing F hn v hv Z q]
  change (Z^2*transverseMinusMoment F v).trace+_+_ = _
  rw [transverseMinusMoment_identity F hn v hv, Matrix.mul_smul, Matrix.trace_smul]
  have hscalar : (∑ i, minusContactWeight F v i*((couplingGamma n)^2*
      (height F v i+inverseDimension n)^2*‖q‖^2)) =
      (couplingGamma n)^2*reverseDefect F v*‖q‖^2 := by
    rw [← minus_scalar_mass F v, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i hi; ring
  rw [hscalar, gamma_reverse_identity F hn v hv]
  unfold couplingQuadraticTest
  simp only [smul_eq_mul]
  ring

theorem couplingLinearSum_split (F : JohnFrame n N) (v : V n) (Z : MatR n) (q : V n) :
    couplingLinearSum F v Z q =
      (∑ i, F.weight i/(1-boostParameter n*height F v i)*(height F v i-inverseDimension n)*
        ⟪transverse v (F.contact i), Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i))⟫)+
      couplingGamma n*(∑ i, F.weight i/(1-boostParameter n*height F v i)*
        ((height F v i)^2-(inverseDimension n)^2)*⟪transverse v (F.contact i), q⟫) := by
  unfold couplingLinearSum couplingTestVector
  simp only [inner_add_right, real_inner_smul_right, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i hi; ring

theorem coupling_linear_identity (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (Z : MatR n) (q : V n) :
    couplingLinearTest F v Z q = -(1/(2-inverseDimension n))*couplingLinearSum F v Z q := by
  have ht : (Z*transversePerturbation F v).trace = -(1/(2-inverseDimension n))*
      (∑ i, F.weight i/(1-boostParameter n*height F v i)*(height F v i-inverseDimension n)*
        ⟪transverse v (F.contact i), Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverse v (F.contact i))⟫) := by
    rw [transversePerturbation_explicit, Matrix.mul_smul, Matrix.trace_smul]
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      Khachiyan.outer_eq_vecMulVec, Optimization.trace_mul_cross, smul_eq_mul]
  have hq := congrArg (fun u : V n => ⟪u, q⟫) (gamma_difference_identity F hn v hv)
  unfold differenceSquareMoment at hq
  simp only [real_inner_smul_left, sum_inner, inner_neg_left] at hq
  rw [couplingLinearTest, ht, couplingLinearSum_split]
  have hc : ⟪q, transverseCoupling F v⟫ = ⟪transverseCoupling F v, q⟫ := real_inner_comm _ _
  rw [hc]
  linear_combination hq

end SharpCut.Certificate
