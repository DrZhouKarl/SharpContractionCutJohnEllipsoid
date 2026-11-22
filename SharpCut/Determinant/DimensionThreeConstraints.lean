import SharpCut.Determinant.DimensionThreeCoordinates

/-! # Native transverse positivity and the actual frame Gram constraint -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
open Certificate
variable {N : ℕ}

def threeN (F : JohnFrame 3 N) (v : V 3) (b : OrthonormalBasis (Fin 3) ℝ (V 3)) : MatR 2 :=
  (2/3 : ℝ) • (1 : MatR 2)-threeE F v b

theorem three_perturbation_embedding (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) (w : V 2) :
    ⟪w, Matrix.toEuclideanCLM (𝕜 := ℝ) (threeE F v b) w⟫ =
      ⟪Geometry.embedTail b w, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v)
        (Geometry.embedTail b w)⟫ := by
  have h := Geometry.tailBlock_bilinear b _ (transversePerturbation_isHermitian F v) v
    (Geometry.embedTail b w) (Geometry.embedTail b w) hv hb 0
    (by simpa only [zero_smul] using transversePerturbation_axis F (by norm_num) v hv)
    (Geometry.embedTail_orthogonal b v hb w) (Geometry.embedTail_orthogonal b v hb w)
  rwa [Geometry.tailCoordinates_embedTail] at h

theorem three_coupling_embedding (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) (w : V 2) :
    ⟪threeJ F v b, w⟫ = ⟪transverseCoupling F v, Geometry.embedTail b w⟫ := by
  have h := Geometry.tailCoordinates_inner b v (transverseCoupling F v) (Geometry.embedTail b w) hb
    (transverseCoupling_orthogonal F v hv) (Geometry.embedTail_orthogonal b v hb w)
  rwa [Geometry.tailCoordinates_embedTail] at h

theorem threeN_quadratic (F : JohnFrame 3 N) (v : V 3) (b : OrthonormalBasis (Fin 3) ℝ (V 3))
    (w : V 2) :
    ⟪w, Matrix.toEuclideanCLM (𝕜 := ℝ) (threeN F v b) w⟫ =
      (2/3 : ℝ)*‖w‖^2-⟪w, Matrix.toEuclideanCLM (𝕜 := ℝ) (threeE F v b) w⟫ := by
  rw [threeN, matrix_action_sub, matrix_action_smul, inner_sub_right, real_inner_smul_right,
    map_one, ContinuousLinearMap.one_apply, real_inner_self_eq_norm_sq]

theorem threeN_posDef (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) : (threeN F v b).PosDef := by
  have hH : (threeN F v b).IsHermitian :=
    (Matrix.isHermitian_one.smul (show IsSelfAdjoint (2/3 : ℝ) by rfl)).sub (threeE_isHermitian F v b)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hH
  intro x hx
  let w : V 2 := WithLp.toLp 2 x
  have hw0 : w ≠ 0 := by
    intro h; apply hx
    have he := congrArg (fun z : V 2 => z.ofLp) h
    simpa [w] using he
  have hu := Geometry.embedTail_orthogonal b v hb w
  have hu' : ⟪Geometry.embedTail b w, v⟫ = 0 := by rwa [real_inner_comm]
  have hu0 : Geometry.embedTail b w ≠ 0 := by
    intro h
    have he := Geometry.embedTail_norm b w
    rw [h, norm_zero] at he
    exact hw0 (norm_eq_zero.mp he.symm)
  have hs := (transverse_strict_bounds F (by norm_num) v (Geometry.embedTail b w) hv hu' hu0).2
  rw [Geometry.embedTail_norm, ← three_perturbation_embedding F v hv b hb w] at hs
  norm_num [cutWeight, inverseDimension] at hs
  have hp : 0 < ⟪w, Matrix.toEuclideanCLM (𝕜 := ℝ) (threeN F v b) w⟫ := by
    rw [threeN_quadratic]
    linarith only [hs]
  simpa only [Khachiyan.inner_matrix_action, WithLp.ofLp_toLp, star_trivial] using hp

theorem three_gram_quadratic (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) (w : V 2) :
    ⟪threeJ F v b, w⟫^2 ≤ axialDeficit F v*
      ⟪w, Matrix.toEuclideanCLM (𝕜 := ℝ) (threeN F v b) w⟫ := by
  have hu := Geometry.embedTail_orthogonal b v hb w
  have hu' : ⟪Geometry.embedTail b w, v⟫ = 0 := by rwa [real_inner_comm]
  have h := transverse_coupling_bound F (by norm_num) v (Geometry.embedTail b w) hv hu'
  rw [← three_coupling_embedding F v hv b hb w, Geometry.embedTail_norm,
    ← three_perturbation_embedding F v hv b hb w] at h
  norm_num [cutWeight, inverseDimension] at h
  rwa [threeN_quadratic] at ⊢

theorem three_sigma_range (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    0 ≤ (threeE F v b).trace ∧ (threeE F v b).trace ≤ 3/4 := by
  have h := transverseSigma_range F (by norm_num) v hv
  norm_num [inverseDimension] at h
  rwa [threeE_trace F v hv b hb]

end SharpCut.Determinant
