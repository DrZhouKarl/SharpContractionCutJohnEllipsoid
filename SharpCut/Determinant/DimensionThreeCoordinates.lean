import SharpCut.Geometry.TransverseCoordinates
import SharpCut.Certificate.ZeroDefect
import SharpCut.Determinant.TwoByTwo

/-! # The actual two-dimensional transverse matrix in a three-dimensional frame -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
open Certificate
variable {N : ℕ}

def threeE (F : JohnFrame 3 N) (v : V 3) (b : OrthonormalBasis (Fin 3) ℝ (V 3)) : MatR 2 :=
  Geometry.tailBlock (m := 2) b (transversePerturbation F v)

def threeJ (F : JohnFrame 3 N) (v : V 3) (b : OrthonormalBasis (Fin 3) ℝ (V 3)) : V 2 :=
  Geometry.tailCoordinates (m := 2) b (transverseCoupling F v)

def threeK (F : JohnFrame 3 N) (v : V 3) (b : OrthonormalBasis (Fin 3) ℝ (V 3)) : MatR 2 :=
  1+(2 : ℝ) • threeE F v b

theorem threeE_isHermitian (F : JohnFrame 3 N) (v : V 3) (b : OrthonormalBasis (Fin 3) ℝ (V 3)) :
    (threeE F v b).IsHermitian := Geometry.tailBlock_isHermitian b _ (transversePerturbation_isHermitian F v)

theorem threeE_coordinates (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    Geometry.inBasis b (transversePerturbation F v) = Geometry.diagAxis 0 (threeE F v b) :=
  Geometry.inBasis_axis_diagonal b _ (transversePerturbation_isHermitian F v) v hv hb 0
    (by simpa only [zero_smul] using transversePerturbation_axis F (by norm_num) v hv)

theorem threeE_trace (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    (threeE F v b).trace = transverseSigma F v := by
  rw [threeE, Geometry.tailBlock_trace_zero_axis b _ (transversePerturbation_isHermitian F v)
    v hv hb (transversePerturbation_axis F (by norm_num) v hv), transversePerturbation_trace F (by norm_num) v hv]

theorem threeK_tail (F : JohnFrame 3 N) (v : V 3) (b : OrthonormalBasis (Fin 3) ℝ (V 3)) :
    Geometry.tailBlock b (couplingK F v) = threeK F v b := by
  rw [couplingK, Geometry.tailBlock_add, Geometry.tailBlock_one, Geometry.tailBlock_smul]
  rfl

theorem threeK_posDef (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) : (threeK F v b).PosDef := by
  rw [← threeK_tail]
  exact Geometry.tailBlock_posDef b _ (couplingK_posDef F (by norm_num) v hv)

theorem threeK_coordinates (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    Geometry.inBasis b (couplingK F v) = Geometry.diagAxis 1 (threeK F v b) := by
  have h := Geometry.inBasis_axis_diagonal b _ (couplingK_posDef F (by norm_num) v hv).isHermitian
    v hv hb 1 (by simpa only [one_smul] using couplingK_axis F (by norm_num) v hv)
  rwa [threeK_tail] at h

theorem threeK_inv_coordinates (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    Geometry.inBasis b ((couplingK F v)⁻¹) = Geometry.diagAxis 1 ((threeK F v b)⁻¹) := by
  rw [← Geometry.inBasis_inv b _ (couplingK_posDef F (by norm_num) v hv),
    threeK_coordinates F v hv b hb, Geometry.diagAxis_inv_one _ (threeK_posDef F v hv b)]

theorem three_deformation_trace (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    transverseDeformation F v = ((threeE F v b)^2*(threeK F v b)⁻¹).trace := by
  have hp : Geometry.inBasis b ((transversePerturbation F v)^2) = Geometry.diagAxis 0 ((threeE F v b)^2) := by
    rw [pow_two, Geometry.inBasis_mul, threeE_coordinates F v hv b hb, Geometry.diagAxis_mul, zero_mul]
    rw [pow_two]
  rw [transverseDeformation, ← Geometry.inBasis_trace b, Geometry.inBasis_mul, hp,
    threeK_inv_coordinates F v hv b hb, Geometry.diagAxis_mul, zero_mul, Geometry.diagAxis_trace, zero_add]

theorem threeJ_norm (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    ‖threeJ F v b‖ = ‖transverseCoupling F v‖ :=
  Geometry.tailCoordinates_norm b v _ hb (transverseCoupling_orthogonal F v hv)

theorem threeJ_inverse_norm (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (threeK F v b)⁻¹ (threeJ F v b)‖ =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (couplingK F v)⁻¹ (transverseCoupling F v)‖ := by
  have h := Geometry.tailBlock_action_norm b (couplingK F v)⁻¹
    (couplingK_posDef F (by norm_num) v hv).inv.isHermitian v (transverseCoupling F v) hv hb 1
    (by simpa only [one_smul] using couplingK_inv_axis F (by norm_num) v hv)
    (transverseCoupling_orthogonal F v hv)
  rw [Geometry.tailBlock_inv_axis_one b _ (couplingK_posDef F (by norm_num) v hv) v hv hb
    (couplingK_axis F (by norm_num) v hv), threeK_tail] at h
  exact h

theorem threeJ_perturbation_pairing (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    ⟪threeJ F v b, Matrix.toEuclideanCLM (𝕜 := ℝ) (threeE F v b) (threeJ F v b)⟫ =
      ⟪transverseCoupling F v, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v)
        (transverseCoupling F v)⟫ :=
  Geometry.tailBlock_bilinear b _ (transversePerturbation_isHermitian F v) v _ _ hv hb 0
    (by simpa only [zero_smul] using transversePerturbation_axis F (by norm_num) v hv)
    (transverseCoupling_orthogonal F v hv) (transverseCoupling_orthogonal F v hv)

end SharpCut.Determinant
