import SharpCut.Determinant.DimensionThreeInvariants
import SharpCut.Determinant.DimensionThreePolynomial
import SharpCut.Determinant.DimensionTwo

/-! # The complete arbitrary-frame three-dimensional determinant branch -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
open Certificate
variable {N : ℕ}

/-- Proposition 8.7: the actual frame supplies every matrix-to-scalar constraint. -/
theorem dimension_three_determinant (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1) :
    1+(36/385 : ℝ)*frameDefect F v ≤ (normalizedCertificate F v).det := by
  have hbase : ∃ b : OrthonormalBasis (Fin 3) ℝ (V 3), b 0 = v :=
    Geometry.exists_axial_basis (m := 2) v hv
  obtain ⟨b, hb⟩ := hbase
  let σ := (threeE F v b).trace
  let z := threeZ F v b
  let r := ‖threeJ F v b‖^2
  let ω := ⟪threeJ F v b, Matrix.toEuclideanCLM (𝕜 := ℝ) (threeE F v b) (threeJ F v b)⟫
  have hs := three_sigma_range F v hv b hb
  have hz := three_z_range F v hv b hb
  have hg := three_gram_scalar F v hv b hb
  have hvar := three_variational_scalar F v hv b hb
  have hcoef : (5/6 : ℝ)*(threeE F v b).trace = 5*(threeE F v b).trace/6 := by ring
  rw [hcoef] at hvar
  have hd := three_determinant_expression F v hv b hb
  have hx : axialDeficit F v = 5*(threeE F v b).trace/12 := by
    rw [axialDeficit_sigma F (by norm_num) v, ← threeE_trace F v hv b hb]
    norm_num [inverseDimension] <;> ring
  rw [hx] at hd
  have he : (normalizedCertificate F v).det =
      (1-5*σ/12)*(1+σ+(z-σ)/4)-((1+σ)*r-ω) := by
    dsimp [σ, z, r, ω]
    rw [hd]
    unfold threeZ
    ring
  have h := dimension_three_scalar_elimination σ z r ω (normalizedCertificate F v).det
    hs.1 hs.2 hz.1 hz.2 hg hvar he
  change 1+2*(threeE F v b).trace/11 ≤ _ at h
  rw [threeE_trace F v hv b hb] at h
  norm_num [transverseSigma, inverseDimension] at h
  convert h using 1 <;> ring

theorem dimension_three_logdet (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1) :
    (36/457 : ℝ)*frameDefect F v ≤ Real.log (normalizedCertificate F v).det := by
  have hr := frameDefect_range F (by norm_num) v hv
  have h := log_of_affine_lower (36/385) (frameDefect F v) (normalizedCertificate F v).det
    (by norm_num) hr.1 hr.2.2 (dimension_three_determinant F v hv)
  norm_num at h
  exact h

theorem dimension_three_uniform_logdet (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1) :
    (1/1500 : ℝ)*frameDefect F v ≤ Real.log (normalizedCertificate F v).det :=
  (mul_le_mul_of_nonneg_right (by norm_num : (1/1500 : ℝ) ≤ 36/457)
    (frameDefect_nonneg F (by norm_num) v hv)).trans (dimension_three_logdet F v hv)

end SharpCut.Determinant
