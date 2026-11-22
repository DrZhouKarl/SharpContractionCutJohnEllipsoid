import SharpCut.Coupled.General
import SharpCut.Geometry.TransverseCoordinates

/-! # Every actual m-by-m transverse test as an ambient orthonormal extension -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Coupled
open Certificate Geometry
variable {m : ℕ}

def extendMatrix (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (Z : MatR m) : MatR (m+1) :=
  (basisMatrix B)ᵀ*diagAxis 0 Z*basisMatrix B

def extendVector (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (q : V m) : V (m+1) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (basisMatrix B)ᵀ (padTail q)

theorem inBasis_extendMatrix (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (Z : MatR m) :
    inBasis B (extendMatrix B Z) = diagAxis 0 Z := by
  calc
    _ = (basisMatrix B*(basisMatrix B)ᵀ)*diagAxis 0 Z*(basisMatrix B*(basisMatrix B)ᵀ) := by
      simp only [inBasis, extendMatrix, Matrix.mul_assoc]
    _ = _ := by rw [basisMatrix_left_orthogonal B, Matrix.one_mul, Matrix.mul_one]

theorem diagAxis_hermitian (Z : MatR m) (hZ : Z.IsHermitian) : (diagAxis 0 Z).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  apply Matrix.IsSymm.ext
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [diagAxis_zero_zero, diagAxis_zero_succ, diagAxis_succ_zero, diagAxis_succ_succ,
      hZ.isSymm.apply]

theorem extendMatrix_hermitian (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (Z : MatR m) (hZ : Z.IsHermitian) :
    (extendMatrix B Z).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  change (extendMatrix B Z)ᵀ = extendMatrix B Z
  simp only [extendMatrix, Matrix.transpose_mul, Matrix.transpose_transpose, (diagAxis_hermitian Z hZ).isSymm.eq,
    Matrix.mul_assoc]

theorem basis_action_extendVector (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (q : V m) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (basisMatrix B) (extendVector B q) = padTail q := by
  rw [extendVector, ← matrix_action_mul, basisMatrix_left_orthogonal B, map_one, ContinuousLinearMap.one_apply]

theorem extendVector_norm (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (q : V m) : ‖extendVector B q‖ = ‖q‖ := by
  rw [← basisMatrix_norm B (extendVector B q), basis_action_extendVector, padTail_norm]

theorem tail_projector (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (v : V (m+1)) (hB : B 0 = v) :
    tailBlock B (projector v) = 1 := by
  ext i j
  change inBasis B (projector v) i.succ j.succ = _
  rw [inBasis_entry, projector_action, transverse, basis_tail_orthogonal B v hB j, zero_smul, sub_zero]
  simpa only [Matrix.one_apply, Fin.succ_inj] using (orthonormal_iff_ite.mp B.orthonormal i.succ j.succ)

theorem projector_inBasis (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (v : V (m+1)) (hv : ‖v‖ = 1) (hB : B 0 = v) :
    inBasis B (projector v) = diagAxis 0 (1 : MatR m) := by
  have hP := (projector_posSemidef v hv).isHermitian
  have ha : Matrix.toEuclideanCLM (𝕜 := ℝ) (projector v) v = (0 : ℝ) • v := by
    rw [projector_action, transverse_axis_zero v hv, zero_smul]
  rw [inBasis_axis_diagonal B (projector v) hP v hv hB 0 ha, tail_projector B v hB]

theorem diagAxis_add (a b : ℝ) (A C : MatR m) : diagAxis a A+diagAxis b C = diagAxis (a+b) (A+C) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem diagAxis_smul (r a : ℝ) (A : MatR m) : r • diagAxis a A = diagAxis (r*a) (r • A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

/-- Exact trace product of the lifted test and an axis-annihilating Hermitian coefficient. -/
theorem extension_trace_product (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (v : V (m+1)) (hv : ‖v‖ = 1) (hB : B 0 = v) (A : MatR (m+1)) (hA : A.IsHermitian)
    (ha : Matrix.toEuclideanCLM (𝕜 := ℝ) A v = 0) (Z : MatR m) :
    (extendMatrix B Z*A).trace = (Z*tailBlock B A).trace := by
  rw [← inBasis_trace B, inBasis_mul, inBasis_extendMatrix,
    inBasis_axis_diagonal B A hA v hv hB 0 (by simpa only [zero_smul] using ha),
    diagAxis_mul, diagAxis_trace, zero_mul, zero_add]

/-- The mixed vector pairing is preserved by the actual orthogonal extension. -/
theorem extension_mixed_pairing (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (v u : V (m+1)) (hB : B 0 = v) (hu : ⟪v,u⟫ = 0) (Z : MatR m) (q : V m) :
    ⟪extendVector B q, Matrix.toEuclideanCLM (𝕜 := ℝ) (extendMatrix B Z) u⟫ =
      ⟪q, Matrix.toEuclideanCLM (𝕜 := ℝ) Z (tailCoordinates B u)⟫ := by
  rw [← basisMatrix_inner B, basis_action_extendVector,
    ← inBasis_action B (extendMatrix B Z) u, inBasis_extendMatrix,
    coordinates_pad_of_orthogonal B v u hB hu, diagAxis_action_pad, padTail_inner]


theorem extendMatrix_mul (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (Z W : MatR m) :
    extendMatrix B Z*extendMatrix B W = extendMatrix B (Z*W) := by
  apply inBasis_injective B
  rw [inBasis_mul, inBasis_extendMatrix, inBasis_extendMatrix, inBasis_extendMatrix,
    diagAxis_mul, zero_mul]

theorem extension_inner (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (v u : V (m+1)) (hB : B 0 = v) (hu : ⟪v,u⟫ = 0) (q : V m) :
    ⟪extendVector B q,u⟫ = ⟪q,tailCoordinates B u⟫ := by
  rw [← basisMatrix_inner B, basis_action_extendVector, coordinates_pad_of_orthogonal B v u hB hu, padTail_inner]

/-- Lemma 10.2 literally on every symmetric m-by-m test and every Euclidean m-vector. -/
theorem general_cauchy_transverse {N : ℕ} (F : JohnFrame (m+1) N) (hm : 1 ≤ m) (v : V (m+1)) (hv : ‖v‖ = 1)
    (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (hB : B 0 = v)
    (Z : MatR m) (hZ : Z.IsHermitian) (q : V m) :
    ((Z*tailBlock B (transversePerturbation F v)).trace+⟪q,tailCoordinates B (transverseCoupling F v)⟫)^2 ≤
      transverseSigma F v*((Z^2*(tailBlock B (transversePerturbation F v)+(1/2 : ℝ) • (1 : MatR m))).trace+
        2*⟪q,Matrix.toEuclideanCLM (𝕜 := ℝ) Z (tailCoordinates B (transverseCoupling F v))⟫+
        ((2-inverseDimension (m+1))/4*traceRemainder F v)*‖q‖^2) := by
  have hn : 2 ≤ m+1 := by omega
  have hE := transversePerturbation_isHermitian F v
  have hEv := transversePerturbation_axis F hn v hv
  have hj := transverseCoupling_orthogonal F v hv
  let C : MatR (m+1) := transversePerturbation F v+(1/2 : ℝ) • projector v
  have hC : C.IsHermitian := hE.add ((projector_posSemidef v hv).isHermitian.smul (by rfl))
  have hCv : Matrix.toEuclideanCLM (𝕜 := ℝ) C v = 0 := by
    dsimp only [C]
    rw [matrix_action_add, matrix_action_smul, hEv, projector_action,
      transverse_axis_zero v hv, smul_zero, add_zero]
  have htail : tailBlock B C = tailBlock B (transversePerturbation F v)+(1/2 : ℝ) • (1 : MatR m) := by
    dsimp only [C]
    rw [tailBlock_add, tailBlock_smul, tail_projector B v hB]
  have hZsq : (extendMatrix B Z)^2 = extendMatrix B (Z^2) := by rw [pow_two, extendMatrix_mul, pow_two]
  have hc := general_cauchy F hn v hv (extendMatrix B Z) (extendMatrix_hermitian B Z hZ) (extendVector B q)
  rw [extension_trace_product B v hv hB _ hE hEv, extension_inner B v _ hB hj] at hc
  unfold forwardQuadratic at hc
  change _ ≤ transverseSigma F v*((((extendMatrix B Z)^2)*C).trace+
    2*⟪extendVector B q,Matrix.toEuclideanCLM (𝕜 := ℝ) (extendMatrix B Z) (transverseCoupling F v)⟫+
    ((2-inverseDimension (m+1))/4*traceRemainder F v)*‖extendVector B q‖^2) at hc
  rw [hZsq, extension_trace_product B v hv hB C hC hCv (Z^2), htail,
    extension_mixed_pairing B v _ hB hj, extendVector_norm] at hc
  exact hc

end SharpCut.Coupled
