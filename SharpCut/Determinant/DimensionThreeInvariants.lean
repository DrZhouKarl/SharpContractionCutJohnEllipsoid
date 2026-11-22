import SharpCut.Determinant.DimensionThreeDeterminant

/-! # The actual three-dimensional scalar invariants and coupling inequalities -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
open Certificate
variable {N : ℕ}

def threeZ (F : JohnFrame 3 N) (v : V 3) (b : OrthonormalBasis (Fin 3) ℝ (V 3)) : ℝ :=
  (threeE F v b).trace+4*(threeE F v b).det

theorem threeK_det (F : JohnFrame 3 N) (v : V 3) (b : OrthonormalBasis (Fin 3) ℝ (V 3)) :
    (threeK F v b).det = 1+2*(threeE F v b).trace+4*(threeE F v b).det := by
  rw [threeK, det_one_add_scale_two]
  norm_num

theorem threeK_denominator_pos (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) : 0 < 1+2*(threeE F v b).trace+4*(threeE F v b).det := by
  rw [← threeK_det]
  exact (threeK_posDef F v hv b).det_pos

theorem three_deformation_identity (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    (threeE F v b).trace-2*transverseDeformation F v =
      threeZ F v b/(1+(threeE F v b).trace+threeZ F v b) := by
  rw [three_deformation_trace F v hv b hb]
  have h := inverse_trace_identity_two (threeE F v b) (threeK_denominator_pos F v hv b).ne'
  change (threeE F v b).trace-2*((threeE F v b)^2*(threeK F v b)⁻¹).trace = _ at h
  have he : 1+2*(threeE F v b).trace+4*(threeE F v b).det =
      1+(threeE F v b).trace+threeZ F v b := by unfold threeZ; ring
  rw [he] at h
  exact h

theorem three_z_range (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    0 ≤ threeZ F v b ∧ threeZ F v b ≤ (threeE F v b).trace*(1+(threeE F v b).trace) := by
  have hd : 0 < 1+(threeE F v b).trace+threeZ F v b := by
    have h := threeK_denominator_pos F v hv b
    unfold threeZ
    nlinarith only [h]
  have hA := deformation_upper F (by norm_num) v hv
  rw [← threeE_trace F v hv b hb] at hA
  have hdiff : 0 ≤ (threeE F v b).trace-2*transverseDeformation F v := by linarith only [hA]
  have hz := mul_nonneg hdiff hd.le
  rw [three_deformation_identity F v hv b hb, div_mul_cancel₀ _ hd.ne'] at hz
  refine ⟨hz, ?_⟩
  have hp := det_le_trace_sq_two (threeE F v b) (threeE_isHermitian F v b)
  unfold threeZ
  nlinarith only [hp]

theorem three_gram_scalar (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    ((2/3 : ℝ)-(threeE F v b).trace)*‖threeJ F v b‖^2+
      ⟪threeJ F v b, Matrix.toEuclideanCLM (𝕜 := ℝ) (threeE F v b) (threeJ F v b)⟫ ≤
        (5*(threeE F v b).trace/12)*
          ((2/3 : ℝ)^2-(2/3 : ℝ)*(threeE F v b).trace+(threeZ F v b-(threeE F v b).trace)/4) := by
  have hx : 0 ≤ axialDeficit F v := by
    unfold axialDeficit
    exact div_nonneg (frameDefect_nonneg F (by norm_num) v hv) (by norm_num [inverseDimension])
  have h := gram_adjugate_bound_two (threeN F v b) (threeN_posDef F v hv b hb) (threeJ F v b)
    (axialDeficit F v) hx (three_gram_quadratic F v hv b hb)
  rw [threeN, adjugate_pairing_scalar_sub_two, det_scalar_sub_two, axialDeficit_sigma F (by norm_num) v,
    ← threeE_trace F v hv b hb] at h
  norm_num [inverseDimension] at h
  unfold threeZ
  convert h using 1 <;> ring

theorem three_variational_scalar (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    (((1+(threeE F v b).trace)*(1+4*(threeE F v b).trace)-threeZ F v b)*‖threeJ F v b‖^2-
      4*(1+(threeE F v b).trace)*⟪threeJ F v b,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (threeE F v b) (threeJ F v b)⟫) ≤
      ((5/8 : ℝ)-(5/6 : ℝ)*(threeE F v b).trace)/2*
        threeZ F v b*(1+(threeE F v b).trace+threeZ F v b) := by
  have hd : 0 < (threeK F v b).det := (threeK_posDef F v hv b).det_pos
  have he : (threeK F v b).det = 1+(threeE F v b).trace+threeZ F v b := by rw [threeK_det]; unfold threeZ; ring
  have hbnd := (direct_coupling_bound F (by norm_num) v hv).2
  rw [← threeJ_inverse_norm F v hv b hb, ← threeE_trace F v hv b hb] at hbnd
  have hA := three_deformation_identity F v hv b hb
  rw [← he] at hA
  have hr : (threeE F v b).trace/2-transverseDeformation F v = threeZ F v b/(2*(threeK F v b).det) := by
    linear_combination (1/2 : ℝ)*hA
  rw [hr] at hbnd
  have hm := mul_le_mul_of_nonneg_left hbnd (sq_nonneg (threeK F v b).det)
  rw [inverse_norm_det _ (threeK_posDef F v hv b)] at hm
  have hadj : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (threeK F v b).adjugate (threeJ F v b)‖^2 =
      ((1+2*(threeE F v b).trace)^2-4*(threeE F v b).det)*‖threeJ F v b‖^2-
        4*(1+(threeE F v b).trace)*⟪threeJ F v b,
          Matrix.toEuclideanCLM (𝕜 := ℝ) (threeE F v b) (threeJ F v b)⟫ := by
    rw [threeK, adjugate_norm_square_two _ (threeE_isHermitian F v b)]
  rw [hadj] at hm
  have hL : couplingL F v = (5/8 : ℝ)-(5/6 : ℝ)*(threeE F v b).trace := by
    unfold couplingL
    rw [← threeE_trace F v hv b hb]
    norm_num [inverseDimension]
    ring
  rw [hL] at hm
  have hright : (threeK F v b).det^2*
      (couplingL F v*(threeZ F v b/(2*(threeK F v b).det))) =
      couplingL F v/2*threeZ F v b*(threeK F v b).det := by field_simp [hd.ne'] <;> ring
  rw [hL] at hright
  rw [hright, he] at hm
  unfold threeZ at hm ⊢
  convert hm using 1 <;> ring

end SharpCut.Determinant
