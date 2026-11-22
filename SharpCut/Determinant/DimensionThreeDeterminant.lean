import SharpCut.Determinant.DimensionThreeConstraints
import SharpCut.Determinant.ArrowMatrix

/-! # The full normalized determinant in actual three-dimensional coordinates -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
open Certificate
variable {N : ℕ}

theorem threeJ_apply (F : JohnFrame 3 N) (v : V 3) (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (i : Fin 2) :
    threeJ F v b i = ⟪b i.succ, transverseCoupling F v⟫ := by
  rw [threeJ, Geometry.tailCoordinates, Geometry.tailVector_apply,
    Geometry.basisMatrix_action_repr, OrthonormalBasis.repr_apply_apply]

theorem threeE_apply (F : JohnFrame 3 N) (v : V 3) (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (i j : Fin 2) :
    threeE F v b i j = ⟪b i.succ, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v) (b j.succ)⟫ := by
  rw [threeE, Geometry.tailBlock, Matrix.submatrix_apply, Geometry.inBasis_entry]

theorem three_normalized_arrow (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    Geometry.inBasis b (normalizedCertificate F v) =
      arrowMatrix (1-axialDeficit F v) (1+threeE F v b) (threeJ F v b) := by
  have hs := (Geometry.inBasis_posDef b _ (normalizedCertificate_posDef F (by norm_num) v hv)).isHermitian.isSymm
  have hc (i : Fin 2) : Geometry.inBasis b (normalizedCertificate F v) i.succ 0 = threeJ F v b i := by
    rw [Geometry.inBasis_entry, hb, normalized_mixed_bilinear F (by norm_num) v (b i.succ) hv
      (Geometry.basis_tail_orthogonal b v hb i), threeJ_apply]
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [Geometry.inBasis_entry, hb, normalized_axial_bilinear F (by norm_num) v hv, arrow_zero_zero]
    · rw [← hs.apply 0 j.succ, hc, arrow_zero_succ]
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [hc, arrow_succ_zero]
    · rw [Geometry.inBasis_entry, normalized_transverse_bilinear F (by norm_num) v (b i.succ) (b j.succ) hv
        (Geometry.basis_tail_orthogonal b v hb i) (Geometry.basis_tail_orthogonal b v hb j),
        ← threeE_apply, arrow_succ_succ]
      simp only [Matrix.add_apply, Matrix.one_apply]
      have ho := orthonormal_iff_ite.mp b.orthonormal i.succ j.succ
      simpa only [Fin.succ_inj] using congrArg (fun z : ℝ => z+threeE F v b i j) ho

theorem three_determinant_expression (F : JohnFrame 3 N) (v : V 3) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin 3) ℝ (V 3)) (hb : b 0 = v) :
    (normalizedCertificate F v).det =
      (1-axialDeficit F v)*(1+(threeE F v b).trace+(threeE F v b).det)-
        ((1+(threeE F v b).trace)*‖threeJ F v b‖^2-
          ⟪threeJ F v b, Matrix.toEuclideanCLM (𝕜 := ℝ) (threeE F v b) (threeJ F v b)⟫) := by
  rw [← Geometry.inBasis_det b, three_normalized_arrow F v hv b hb, arrow_one_add_determinant]

end SharpCut.Determinant
