import SharpCut.Geometry.HeadTail
import SharpCut.Certificate.NormalizedBlocks

/-! # Actual orthonormal transverse blocks and inverse/vector transport -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Geometry
variable {m : ℕ}

def tailBlock (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (A : MatR (m+1)) : MatR m :=
  (inBasis b A).submatrix Fin.succ Fin.succ

theorem tailBlock_isHermitian (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (A : MatR (m+1)) (hA : A.IsHermitian) : (tailBlock b A).IsHermitian :=
  (inBasis_isHermitian b A hA).submatrix _

theorem tailBlock_posDef (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (A : MatR (m+1)) (hA : A.PosDef) : (tailBlock b A).PosDef :=
  (inBasis_posDef b A hA).submatrix (Fin.succ_injective m)

theorem tailBlock_one (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) :
    tailBlock b (1 : MatR (m+1)) = 1 := by
  unfold tailBlock
  rw [inBasis_one]
  ext i j
  simp [Matrix.one_apply]

theorem tailBlock_add (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (A B : MatR (m+1)) :
    tailBlock b (A+B) = tailBlock b A+tailBlock b B := by
  unfold tailBlock
  rw [inBasis_add]
  rfl

theorem tailBlock_smul (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (r : ℝ) (A : MatR (m+1)) :
    tailBlock b (r • A) = r • tailBlock b A := by
  unfold tailBlock
  rw [inBasis_smul]
  rfl

theorem basis_tail_orthogonal (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (v : V (m+1)) (hb : b 0 = v) (i : Fin m) : ⟪b i.succ, v⟫ = 0 := by
  rw [← hb]
  simpa only [Fin.succ_ne_zero, ite_false] using (orthonormal_iff_ite.mp b.orthonormal i.succ 0)

theorem inBasis_axis_diagonal (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (A : MatR (m+1)) (hA : A.IsHermitian) (v : V (m+1)) (hv : ‖v‖ = 1)
    (hb : b 0 = v) (a : ℝ) (ha : Matrix.toEuclideanCLM (𝕜 := ℝ) A v = a • v) :
    inBasis b A = diagAxis a (tailBlock b A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [inBasis_entry, hb, ha, real_inner_smul_right, real_inner_self_eq_norm_sq, hv,
        one_pow, mul_one, diagAxis_zero_zero]
    · rw [inBasis_entry, hb, Khachiyan.inner_matrix_action_symm hA.isSymm, ha,
        real_inner_smul_left, diagAxis_zero_succ]
      have he : ⟪v, b j.succ⟫ = 0 := by
        simpa only [real_inner_comm] using basis_tail_orthogonal b v hb j
      rw [he, mul_zero]
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [inBasis_entry, hb, ha, real_inner_smul_right, basis_tail_orthogonal b v hb i,
        mul_zero, diagAxis_succ_zero]
    · rfl

theorem tailBlock_trace_zero_axis (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (A : MatR (m+1)) (hA : A.IsHermitian) (v : V (m+1)) (hv : ‖v‖ = 1)
    (hb : b 0 = v) (ha : Matrix.toEuclideanCLM (𝕜 := ℝ) A v = 0) :
    (tailBlock b A).trace = A.trace := by
  have he := inBasis_axis_diagonal b A hA v hv hb 0 (by simpa only [zero_smul] using ha)
  have ht := inBasis_trace b A
  rw [he, diagAxis_trace, zero_add] at ht
  exact ht

def tailCoordinates (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (u : V (m+1)) : V m :=
  tailVector (Matrix.toEuclideanCLM (𝕜 := ℝ) (basisMatrix b) u)

theorem coordinates_pad_of_orthogonal (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (v u : V (m+1)) (hb : b 0 = v) (hu : ⟪v, u⟫ = 0) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (basisMatrix b) u = padTail (tailCoordinates b u) := by
  symm
  apply padTail_tailVector
  rw [basisMatrix_action_repr, OrthonormalBasis.repr_apply_apply, hb, hu]

theorem tailCoordinates_norm (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (v u : V (m+1)) (hb : b 0 = v) (hu : ⟪v, u⟫ = 0) :
    ‖tailCoordinates b u‖ = ‖u‖ := by
  have h := basisMatrix_norm b u
  rw [coordinates_pad_of_orthogonal b v u hb hu, padTail_norm] at h
  exact h

theorem tailBlock_action_norm (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (A : MatR (m+1)) (hA : A.IsHermitian) (v u : V (m+1)) (hv : ‖v‖ = 1)
    (hb : b 0 = v) (a : ℝ) (ha : Matrix.toEuclideanCLM (𝕜 := ℝ) A v = a • v)
    (hu : ⟪v, u⟫ = 0) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (tailBlock b A) (tailCoordinates b u)‖ =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A u‖ := by
  have h := congrArg norm (inBasis_action b A u)
  rw [inBasis_axis_diagonal b A hA v hv hb a ha,
    coordinates_pad_of_orthogonal b v u hb hu, diagAxis_action_pad, padTail_norm, basisMatrix_norm] at h
  exact h

theorem tailBlock_bilinear (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (A : MatR (m+1)) (hA : A.IsHermitian) (v x y : V (m+1)) (hv : ‖v‖ = 1)
    (hb : b 0 = v) (a : ℝ) (ha : Matrix.toEuclideanCLM (𝕜 := ℝ) A v = a • v)
    (hx : ⟪v, x⟫ = 0) (hy : ⟪v, y⟫ = 0) :
    ⟪tailCoordinates b x, Matrix.toEuclideanCLM (𝕜 := ℝ) (tailBlock b A) (tailCoordinates b y)⟫ =
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A y⟫ := by
  have h := basisMatrix_inner b x (Matrix.toEuclideanCLM (𝕜 := ℝ) A y)
  rw [← inBasis_action b A y, inBasis_axis_diagonal b A hA v hv hb a ha,
    coordinates_pad_of_orthogonal b v x hb hx, coordinates_pad_of_orthogonal b v y hb hy,
    diagAxis_action_pad, padTail_inner] at h
  exact h

theorem tailBlock_inv_axis_one (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (A : MatR (m+1)) (hA : A.PosDef) (v : V (m+1)) (hv : ‖v‖ = 1)
    (hb : b 0 = v) (ha : Matrix.toEuclideanCLM (𝕜 := ℝ) A v = v) :
    tailBlock b A⁻¹ = (tailBlock b A)⁻¹ := by
  have he : inBasis b (A⁻¹) = diagAxis 1 ((tailBlock b A)⁻¹) := by
    rw [← inBasis_inv b A hA,
      inBasis_axis_diagonal b A hA.isHermitian v hv hb 1 (by simpa only [one_smul] using ha),
      diagAxis_inv_one _ (tailBlock_posDef b A hA)]
  change (inBasis b A⁻¹).submatrix Fin.succ Fin.succ = _
  rw [he]
  rfl

theorem tailCoordinates_inner (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (v x y : V (m+1)) (hb : b 0 = v) (hx : ⟪v, x⟫ = 0) (hy : ⟪v, y⟫ = 0) :
    ⟪tailCoordinates b x, tailCoordinates b y⟫ = ⟪x, y⟫ := by
  have h := basisMatrix_inner b x y
  rwa [coordinates_pad_of_orthogonal b v x hb hx, coordinates_pad_of_orthogonal b v y hb hy,
    padTail_inner] at h

def embedTail (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (w : V m) : V (m+1) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (basisMatrix b)ᵀ (padTail w)

theorem coordinates_embedTail (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (w : V m) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (basisMatrix b) (embedTail b w) = padTail w := by
  apply WithLp.ofLp_injective 2
  simp only [embedTail, Khachiyan.matrix_action_ofLp, Matrix.mulVec_mulVec,
    basisMatrix_left_orthogonal b, Matrix.one_mulVec]

theorem tailCoordinates_embedTail (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (w : V m) :
    tailCoordinates b (embedTail b w) = w := by
  rw [tailCoordinates, coordinates_embedTail]
  ext i
  rfl

theorem embedTail_norm (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (w : V m) :
    ‖embedTail b w‖ = ‖w‖ := by
  have h := basisMatrix_norm b (embedTail b w)
  rw [coordinates_embedTail, padTail_norm] at h
  exact h.symm

theorem embedTail_orthogonal (b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (v : V (m+1)) (hb : b 0 = v) (w : V m) : ⟪v, embedTail b w⟫ = 0 := by
  rw [← hb, ← OrthonormalBasis.repr_apply_apply b (embedTail b w) 0,
    ← basisMatrix_action_repr, coordinates_embedTail, padTail_zero]

end SharpCut.Geometry
