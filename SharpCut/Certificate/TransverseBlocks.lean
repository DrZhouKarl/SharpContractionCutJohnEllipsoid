import SharpCut.Certificate.ModelScales
import SharpCut.Determinant.LiftedBound

/-! # Coordinate-free blocks of the normalized certificate -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

def axialDeficit (F : JohnFrame n N) (v : V n) : ℝ :=
  frameDefect F v/(2*(2+inverseDimension n))

def transverseSigma (F : JohnFrame n N) (v : V n) : ℝ :=
  2*frameDefect F v/((2-inverseDimension n)*(2+inverseDimension n))

def transversePerturbation (F : JohnFrame n N) (v : V n) : MatR n :=
  (-(1/(2-inverseDimension n))) •
    (transverseMatrixMoment F v 1-inverseDimension n • transverseMatrixMoment F v 0)

def transverseCoupling (F : JohnFrame n N) (v : V n) : V n :=
  (modelAxialScale n*modelTransverseScale n) •
    Matrix.toEuclideanCLM (𝕜 := ℝ) (projector v)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedShape F (contactScalarFactor F v)) v)

theorem contact_factor_decomposition (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) (i : Fin N) :
    contactScalarFactor F v i = (2-inverseDimension n)/2-
      (height F v i-inverseDimension n)/(2*(1-boostParameter n*height F v i)) := by
  have hb := inverseDimension_bounds hn
  have hnon : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have ha : (2-inverseDimension n)*boostParameter n = inverseDimension n := by
    unfold boostParameter
    field_simp [hnon]
  have he : 1-cutWeight n*height F v i =
      (2-inverseDimension n)/2*(1-boostParameter n*height F v i)-
        (height F v i-inverseDimension n)/2 := by
    unfold cutWeight
    linear_combination (height F v i/2)*ha
  unfold contactScalarFactor
  rw [he]
  field_simp [(height_denominator_pos F hn v hv i).ne']

theorem weighted_transverse_shape (F : JohnFrame n N) (v : V n) (hv : ‖v‖ = 1)
    (f : Fin N → ℝ) :
    projector v*weightedShape F f*projector v =
      ∑ i, (F.weight i*f i) • outer (transverse v (F.contact i)) := by
  have hP : (projector v).IsSymm :=
    (Matrix.isHermitian_one.sub (Khachiyan.outer_posSemidef v).isHermitian).isSymm
  simp only [weightedShape, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, outer_congruence _ hP, projector_action]

theorem transverse_shape_decomposition (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    projector v*weightedShape F (contactScalarFactor F v)*projector v =
      ((2-inverseDimension n)/2) • projector v-
        (1/2 : ℝ) • (transverseMatrixMoment F v 1-
          inverseDimension n • transverseMatrixMoment F v 0) := by
  rw [weighted_transverse_shape F v hv]
  rw [← transverse_second_moment F v hv]
  unfold transverseMatrixMoment
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, pow_zero, pow_one, mul_one,
    smul_smul, ← sub_smul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [contact_factor_decomposition F hn v hv i]
  field_simp [(height_denominator_pos F hn v hv i).ne'] <;> ring

theorem transversePerturbation_shape (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    transversePerturbation F v =
      (modelTransverseScale n)^2 •
        (projector v*weightedShape F (contactScalarFactor F v)*projector v)-projector v := by
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  rw [modelTransverseScale_sq hn, transverse_shape_decomposition F hn v hv]
  ext i j
  simp only [transversePerturbation, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  field_simp [hd]
  ring

theorem transverse_trace_identity_of_moments (b dim chi N0 N1 N2 N3 : ℝ)
    (h0 : (2-b)*N0-b*N1 = (2-b)*dim)
    (h1 : (2-b)*N1-b*N2 = 0)
    (h2 : (2-b)*N2-b*N3 = 2-b)
    (hc : chi = N3+(1-2*b)*N2+(b^2-2*b)*N1+b^2*N0)
    (hd : b*dim = 1) (hden : 2-b ≠ 0) (hplus : 2+b ≠ 0) :
    -((N1-N3)-b*(N0-N2))/(2-b) = 2*chi/((2-b)*(2+b)) := by
  have he : -(2+b)*((N1-N3)-b*(N0-N2)) = 2*chi := by
    linear_combination b*h0-(1-b)*h1-h2-2*hc+(2-b)*hd
  field_simp [hden, hplus]
  linear_combination he

theorem transversePerturbation_trace (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) : (transversePerturbation F v).trace = transverseSigma F v := by
  let b := inverseDimension n
  have hb := inverseDimension_bounds hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hdim : b*(n : ℝ) = 1 := by dsimp [b, inverseDimension]; field_simp [hn0]
  have ha : (2-b)*boostParameter n = b := by
    change (2-b)*(b/(2-b)) = b
    field_simp [show 2-b ≠ 0 by linarith [hb.2]]
  obtain ⟨hm0, hm1, hm2⟩ := reweighted_moments F hn v hv
  have h0 := congrArg (fun x : ℝ => (2-b)*x) hm0
  have h1 := congrArg (fun x : ℝ => (2-b)*x) hm1
  have h2 := congrArg (fun x : ℝ => (2-b)*x) hm2
  simp only [mul_sub, ← mul_assoc, ha] at h0
  simp only [mul_sub, ← mul_assoc, ha, mul_zero] at h1
  simp only [mul_sub, ← mul_assoc, ha, mul_one] at h2
  have he := transverse_trace_identity_of_moments b (n : ℝ) (frameDefect F v)
    (reweightedMoment F v 0) (reweightedMoment F v 1)
    (reweightedMoment F v 2) (reweightedMoment F v 3)
    h0 h1 h2 (defect_expansion F v) hdim
    (by linarith [hb.2]) (by linarith [hb.1])
  rw [transversePerturbation, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul,
    transverseMatrixMoment_trace F v hv 1, transverseMatrixMoment_trace F v hv 0]
  dsimp [transverseSigma]
  convert he using 1 <;> ring

theorem axialDeficit_sigma (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) :
    axialDeficit F v = (2-inverseDimension n)/4*transverseSigma F v := by
  have hb := inverseDimension_bounds hn
  unfold axialDeficit transverseSigma
  field_simp [show 2-inverseDimension n ≠ 0 by linarith [hb.2],
    show 2+inverseDimension n ≠ 0 by linarith [hb.1]]
  ring

theorem transverseSigma_range (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    0 ≤ transverseSigma F v ∧ transverseSigma F v ≤
      2*(1-inverseDimension n)/(2-inverseDimension n+(inverseDimension n)^2) := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have hp : 0 < 2+inverseDimension n := by linarith [hb.1]
  have hg : 0 < 2-inverseDimension n+(inverseDimension n)^2 := by nlinarith [sq_nonneg (inverseDimension n)]
  have hc := frameDefect_range F hn v hv
  refine ⟨div_nonneg (mul_nonneg (by norm_num) hc.1) (mul_pos hd hp).le, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hc.2.1 (div_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hd hp)).le
  calc
    _ = (2/((2-inverseDimension n)*(2+inverseDimension n)))*frameDefect F v := by
      unfold transverseSigma; ring
    _ ≤ (2/((2-inverseDimension n)*(2+inverseDimension n)))*
      ((2-inverseDimension n)*(2+inverseDimension n)*(1-inverseDimension n)/
        (2-inverseDimension n+(inverseDimension n)^2)) := hm
    _ = _ := by field_simp [hd.ne', hp.ne', hg.ne']

end SharpCut.Certificate
