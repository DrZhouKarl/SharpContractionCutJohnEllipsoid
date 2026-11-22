import SharpCut.Certificate.Polar

/-! # Actual orthonormal axial coordinates and determinant-preserving matrix transport -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix Set
namespace SharpCut.Geometry
variable {n : ℕ}

theorem exists_axial_basis {m : ℕ} (v : V (m+1)) (hv : ‖v‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)), b 0 = v := by
  have h : Orthonormal ℝ (({0} : Set (Fin (m+1))).domRestrict (fun _ => v)) :=
    orthonormal_subsingleton_iff.mpr (fun i => hv)
  obtain ⟨b, hb⟩ := h.exists_orthonormalBasis_extension_of_card_eq
    (by simp [V, Khachiyan.V] : Module.finrank ℝ (V (m+1)) = Fintype.card (Fin (m+1)))
  exact ⟨b, hb 0 (by simp)⟩

def basisMatrix (b : OrthonormalBasis (Fin n) ℝ (V n)) : MatR n :=
  Matrix.of (fun i j => b i j)

def inBasis (b : OrthonormalBasis (Fin n) ℝ (V n)) (A : MatR n) : MatR n :=
  basisMatrix b*A*(basisMatrix b)ᵀ

theorem basisMatrix_left_orthogonal (b : OrthonormalBasis (Fin n) ℝ (V n)) :
    basisMatrix b*(basisMatrix b)ᵀ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  change (b i).ofLp ⬝ᵥ (b j).ofLp = (1 : MatR n) i j
  rw [← Khachiyan.inner_eq_dotProduct]
  simpa only [Matrix.one_apply] using (orthonormal_iff_ite.mp b.orthonormal i j)

theorem basisMatrix_right_orthogonal (b : OrthonormalBasis (Fin n) ℝ (V n)) :
    (basisMatrix b)ᵀ*basisMatrix b = 1 := mul_eq_one_comm.mp (basisMatrix_left_orthogonal b)

theorem inBasis_det (b : OrthonormalBasis (Fin n) ℝ (V n)) (A : MatR n) :
    (inBasis b A).det = A.det := by
  have h := congrArg Matrix.det (basisMatrix_left_orthogonal b)
  simp only [Matrix.det_mul, Matrix.det_one] at h
  calc
    _ = A.det*((basisMatrix b).det*((basisMatrix b)ᵀ).det) := by
      simp only [inBasis, Matrix.det_mul]; ring
    _ = _ := by rw [h, mul_one]

theorem inBasis_trace (b : OrthonormalBasis (Fin n) ℝ (V n)) (A : MatR n) :
    (inBasis b A).trace = A.trace := by
  rw [inBasis, Matrix.trace_mul_comm (basisMatrix b*A) (basisMatrix b)ᵀ,
    ← Matrix.mul_assoc, basisMatrix_right_orthogonal b, Matrix.one_mul]

theorem inBasis_one (b : OrthonormalBasis (Fin n) ℝ (V n)) :
    inBasis b (1 : MatR n) = 1 := by
  rw [inBasis, Matrix.mul_one, basisMatrix_left_orthogonal b]

theorem inBasis_mul (b : OrthonormalBasis (Fin n) ℝ (V n)) (A B : MatR n) :
    inBasis b (A*B) = inBasis b A*inBasis b B := by
  unfold inBasis
  calc
    _ = basisMatrix b*(A*((basisMatrix b)ᵀ*basisMatrix b)*B)*(basisMatrix b)ᵀ := by
      rw [basisMatrix_right_orthogonal b, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem inBasis_inv (b : OrthonormalBasis (Fin n) ℝ (V n)) (A : MatR n) (hA : A.PosDef) :
    (inBasis b A)⁻¹ = inBasis b A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← inBasis_mul, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), inBasis_one]

theorem inBasis_add (b : OrthonormalBasis (Fin n) ℝ (V n)) (A B : MatR n) :
    inBasis b (A+B) = inBasis b A+inBasis b B := by
  simp only [inBasis, Matrix.mul_add, Matrix.add_mul]

theorem inBasis_sub (b : OrthonormalBasis (Fin n) ℝ (V n)) (A B : MatR n) :
    inBasis b (A-B) = inBasis b A-inBasis b B := by
  simp only [inBasis, Matrix.mul_sub, Matrix.sub_mul]

theorem inBasis_smul (b : OrthonormalBasis (Fin n) ℝ (V n)) (r : ℝ) (A : MatR n) :
    inBasis b (r • A) = r • inBasis b A := by
  simp only [inBasis, Matrix.mul_smul, Matrix.smul_mul]

theorem inBasis_entry (b : OrthonormalBasis (Fin n) ℝ (V n)) (A : MatR n) (i j : Fin n) :
    inBasis b A i j = ⟪b i, Matrix.toEuclideanCLM (𝕜 := ℝ) A (b j)⟫ := by
  unfold inBasis
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [basisMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Khachiyan.inner_matrix_action, dotProduct, Matrix.mulVec]

theorem basisMatrix_conjTranspose (b : OrthonormalBasis (Fin n) ℝ (V n)) :
    (basisMatrix b)ᴴ = (basisMatrix b)ᵀ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]

theorem inBasis_posDef (b : OrthonormalBasis (Fin n) ℝ (V n)) (A : MatR n) (hA : A.PosDef) :
    (inBasis b A).PosDef := by
  have hd : IsUnit (basisMatrix b).det := by
    apply isUnit_iff_ne_zero.mpr
    have h := congrArg Matrix.det (basisMatrix_left_orthogonal b)
    simp only [Matrix.det_mul, Matrix.det_one, Matrix.det_transpose] at h
    intro h0; rw [h0, zero_mul] at h; norm_num at h
  have hu : IsUnit (basisMatrix b) := (Matrix.isUnit_iff_isUnit_det _).mpr hd
  have h := hA.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hu)
  rwa [basisMatrix_conjTranspose] at h

theorem basisMatrix_norm (b : OrthonormalBasis (Fin n) ℝ (V n)) (x : V n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (basisMatrix b) x‖ = ‖x‖ :=
  Certificate.euclidean_norm_of_orthogonal _ (basisMatrix_right_orthogonal b) x

theorem inBasis_isHermitian (b : OrthonormalBasis (Fin n) ℝ (V n)) (A : MatR n)
    (hA : A.IsHermitian) : (inBasis b A).IsHermitian := by
  have h := Matrix.isHermitian_mul_mul_conjTranspose (basisMatrix b) hA
  rwa [basisMatrix_conjTranspose] at h

theorem basisMatrix_inner (b : OrthonormalBasis (Fin n) ℝ (V n)) (x y : V n) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (basisMatrix b) x,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (basisMatrix b) y⟫ = ⟪x, y⟫ := by
  rw [Khachiyan.inner_eq_dotProduct, Khachiyan.matrix_action_ofLp, Khachiyan.matrix_action_ofLp]
  rw [dotProduct_comm (basisMatrix b*ᵥx.ofLp) (basisMatrix b*ᵥy.ofLp)]
  rw [← Matrix.dotProduct_transpose_mulVec (basisMatrix b) x.ofLp,
    Matrix.mulVec_mulVec, basisMatrix_right_orthogonal b, Matrix.one_mulVec,
    ← Khachiyan.inner_eq_dotProduct]

theorem inBasis_action (b : OrthonormalBasis (Fin n) ℝ (V n)) (A : MatR n) (x : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (inBasis b A)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (basisMatrix b) x) =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (basisMatrix b) (Matrix.toEuclideanCLM (𝕜 := ℝ) A x) := by
  apply WithLp.ofLp_injective 2
  simp only [Khachiyan.matrix_action_ofLp, Matrix.mulVec_mulVec, inBasis,
    Matrix.mul_assoc, basisMatrix_right_orthogonal b, Matrix.mul_one]

theorem basisMatrix_action_repr (b : OrthonormalBasis (Fin n) ℝ (V n)) (x : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (basisMatrix b) x = b.repr x := by
  ext i
  rw [Khachiyan.matrix_action_ofLp, OrthonormalBasis.repr_apply_apply]
  change (b i).ofLp ⬝ᵥ x.ofLp = ⟪b i, x⟫
  exact (Khachiyan.inner_eq_dotProduct _ _).symm

theorem fromBasis_inBasis (b : OrthonormalBasis (Fin n) ℝ (V n)) (A : MatR n) :
    (basisMatrix b)ᵀ*inBasis b A*basisMatrix b = A := by
  calc
    _ = ((basisMatrix b)ᵀ*basisMatrix b)*A*((basisMatrix b)ᵀ*basisMatrix b) := by
      simp only [inBasis, Matrix.mul_assoc]
    _ = _ := by rw [basisMatrix_right_orthogonal b, Matrix.one_mul, Matrix.mul_one]

theorem inBasis_injective (b : OrthonormalBasis (Fin n) ℝ (V n)) : Function.Injective (inBasis b) := by
  intro A B h
  have he := congrArg (fun M : MatR n => (basisMatrix b)ᵀ*M*basisMatrix b) h
  rwa [fromBasis_inBasis b A, fromBasis_inBasis b B] at he

end SharpCut.Geometry
