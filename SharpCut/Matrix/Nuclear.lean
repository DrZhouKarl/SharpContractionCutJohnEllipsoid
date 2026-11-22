import SharpCut.Optimization.PolarContraction
import SharpCut.Stability.FrameNorms
import Khachiyan.RankOne

/-! # The actual nuclear norm and its attained contraction dual representation

The definition is the trace of the positive Gram square root, hence the sum
of singular values. The dual attainer uses the inverse square root on positive
eigenspaces and zero on the kernel; no nonsingularity hypothesis is imposed.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix Set
namespace SharpCut.Nuclear
open Certificate Optimization
variable {n : ℕ}

def rowGram (X : MatR n) : MatR n := X*Xᵀ

theorem rowGram_posSemidef (X : MatR n) : (rowGram X).PosSemidef := by
  unfold rowGram
  rw [← real_conjTranspose X]
  exact Matrix.posSemidef_self_mul_conjTranspose X

def nuclearNorm (X : MatR n) : ℝ := (CFC.sqrt (rowGram X)).trace

theorem sqrt_eq_real_cfc {G : MatR n} (hG : G.PosSemidef) : CFC.sqrt G = cfc Real.sqrt G := by
  rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hG.nonneg]
  congr 1
  funext t
  exact (Real.sqrt_eq_rpow t).symm

theorem nuclearNorm_spectral (X : MatR n) :
    nuclearNorm X = ∑ i, Real.sqrt ((rowGram_posSemidef X).isHermitian.eigenvalues i) := by
  rw [nuclearNorm, sqrt_eq_real_cfc (rowGram_posSemidef X),
    Khachiyan.Spectral.trace_cfc (rowGram_posSemidef X).isHermitian]

theorem nuclearNorm_nonneg (X : MatR n) : 0 ≤ nuclearNorm X := by
  rw [nuclearNorm_spectral]
  exact Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)

theorem inner_action_transpose (X : MatR n) (u v : V n) :
    ⟪u,Matrix.toEuclideanCLM (𝕜 := ℝ) X v⟫ = ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Xᵀ u,v⟫ := by
  rw [Khachiyan.inner_eq_dotProduct, Khachiyan.inner_eq_dotProduct,
    Khachiyan.matrix_action_ofLp, Khachiyan.matrix_action_ofLp]
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rowGram_quadratic (X : MatR n) (u : V n) :
    ⟪u,Matrix.toEuclideanCLM (𝕜 := ℝ) (rowGram X) u⟫ =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Xᵀ u‖^2 := by
  simpa only [rowGram, Matrix.transpose_transpose] using transpose_gram_quadratic Xᵀ u

theorem singular_action_norm (X : MatR n) (i : Fin n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Xᵀ ((rowGram_posSemidef X).isHermitian.eigenvectorBasis i)‖ =
      Real.sqrt ((rowGram_posSemidef X).isHermitian.eigenvalues i) := by
  let hG := rowGram_posSemidef X
  let b := hG.isHermitian.eigenvectorBasis
  have hq := rowGram_quadratic X (b i)
  rw [Gap.eigenvector_action _ hG.isHermitian i, real_inner_smul_right,
    real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one i, one_pow, mul_one] at hq
  have hs := Real.sq_sqrt (hG.eigenvalues_nonneg i)
  nlinarith only [hq, hs, Real.sqrt_nonneg (hG.isHermitian.eigenvalues i),
    norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) Xᵀ (b i))]

/-- General trace/nuclear/operator bound for every matrix, including singular X and R. -/
theorem trace_le_nuclear_operator (X R : MatR n) :
    (X*Rᵀ).trace ≤ nuclearNorm X*operatorNorm R := by
  let hG := rowGram_posSemidef X
  let b := hG.isHermitian.eigenvectorBasis
  have htrace : (X*Rᵀ).trace = ∑ i, ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Xᵀ (b i),
      Matrix.toEuclideanCLM (𝕜 := ℝ) Rᵀ (b i)⟫ := by
    rw [← Geometry.inBasis_trace b, Matrix.trace]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply, Geometry.inBasis_entry, matrix_action_mul, inner_action_transpose]
  have heach (i : Fin n) :
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Xᵀ (b i),Matrix.toEuclideanCLM (𝕜 := ℝ) Rᵀ (b i)⟫ ≤
        Real.sqrt (hG.isHermitian.eigenvalues i)*operatorNorm R := by
    have hnorm := ContinuousLinearMap.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℝ) Rᵀ) (b i)
    change _ ≤ operatorNorm Rᵀ*‖b i‖ at hnorm
    rw [operatorNorm_transpose, b.orthonormal.norm_eq_one i, mul_one] at hnorm
    calc
      _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Xᵀ (b i)‖*‖Matrix.toEuclideanCLM (𝕜 := ℝ) Rᵀ (b i)‖ := real_inner_le_norm _ _
      _ ≤ _ := by
        rw [singular_action_norm X i]
        exact mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
  rw [htrace, nuclearNorm_spectral, Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => heach i)

theorem trace_le_nuclear (X R : MatR n) (hR : operatorNorm R ≤ 1) : (X*Rᵀ).trace ≤ nuclearNorm X := by
  have h := trace_le_nuclear_operator X R
  have hm := mul_le_mul_of_nonneg_left hR (nuclearNorm_nonneg X)
  nlinarith only [h, hm]

theorem inEigenbasis_cfc (G : MatR n) (hG : G.IsHermitian) (f : ℝ → ℝ) :
    Geometry.inBasis hG.eigenvectorBasis (cfc f G) = Matrix.diagonal (fun i => f (hG.eigenvalues i)) := by
  ext i j
  rw [Geometry.inBasis_entry,
    Khachiyan.RankOne.cfc_action_of_eigenvector hG (hG.eigenvectorBasis j) (hG.eigenvalues j)
      (Gap.eigenvector_action G hG j) f,
    real_inner_smul_right, orthonormal_iff_ite.mp hG.eigenvectorBasis.orthonormal i j, Matrix.diagonal_apply]
  split_ifs with hij
  · subst j; simp only [mul_one]
  · simp only [mul_zero]

theorem posSemidef_of_inBasis (b : OrthonormalBasis (Fin n) ℝ (V n)) (G : MatR n)
    (hG : (Geometry.inBasis b G).PosSemidef) : G.PosSemidef := by
  have h := hG.conjTranspose_mul_mul_same (Geometry.basisMatrix b)
  rw [Geometry.basisMatrix_conjTranspose] at h
  have he : (Geometry.basisMatrix b)ᵀ*Geometry.inBasis b G*Geometry.basisMatrix b = G := by
    calc
      _ = ((Geometry.basisMatrix b)ᵀ*Geometry.basisMatrix b)*G*
          ((Geometry.basisMatrix b)ᵀ*Geometry.basisMatrix b) := by simp only [Geometry.inBasis, Matrix.mul_assoc]
      _ = G := by rw [Geometry.basisMatrix_right_orthogonal, Matrix.one_mul, Matrix.mul_one]
  rwa [he] at h

def pseudoInverseRoot (t : ℝ) : ℝ := if 0 < t then 1/Real.sqrt t else 0

theorem pseudoInverseRoot_identities (t : ℝ) (ht : 0 ≤ t) :
    (pseudoInverseRoot t)^2*t ≤ 1 ∧ t*pseudoInverseRoot t = Real.sqrt t := by
  by_cases hp : 0 < t
  · have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr hp
    have he1 : (pseudoInverseRoot t)^2*t = 1 := by
      rw [pseudoInverseRoot, ite_eq_left hp, div_pow, one_pow, Real.sq_sqrt ht]
      field_simp
    have he2 : t*pseudoInverseRoot t = Real.sqrt t := by
      rw [pseudoInverseRoot, ite_eq_left hp]
      field_simp
      nlinarith only [Real.sq_sqrt ht]
    exact ⟨he1.le, he2⟩
  · have hz : t = 0 := le_antisymm (le_of_not_gt hp) ht
    simp only [hz, pseudoInverseRoot, lt_self_iff_false, ite_false, Real.sqrt_zero, zero_mul, zero_pow (by omega : 2 ≠ 0)]
    norm_num

theorem operatorNorm_le_one_of_rowGram (R : MatR n) (hR : (1-rowGram R).PosSemidef) : operatorNorm R ≤ 1 := by
  rw [← operatorNorm_transpose R]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  have hq : 0 ≤ ⟪u,Matrix.toEuclideanCLM (𝕜 := ℝ) (1-rowGram R) u⟫ := by
    simpa only [Khachiyan.inner_matrix_action, star_trivial] using hR.dotProduct_mulVec_nonneg u.ofLp
  rw [matrix_action_sub, inner_sub_right, map_one, ContinuousLinearMap.one_apply,
    real_inner_self_eq_norm_sq, rowGram_quadratic] at hq
  rw [one_mul]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith only [hq])

/-- The full contraction dual maximum is attained, with the nullspace explicitly retained. -/
theorem nuclear_dual_attainment (X : MatR n) :
    ∃ R : MatR n, operatorNorm R ≤ 1 ∧ (X*Rᵀ).trace = nuclearNorm X := by
  let G := rowGram X
  have hG : G.PosSemidef := rowGram_posSemidef X
  let b := hG.isHermitian.eigenvectorBasis
  let B : MatR n := cfc pseudoInverseRoot G
  let R : MatR n := B*X
  have hB : B.IsHermitian := cfc_predicate pseudoInverseRoot G
  have hdiagB : Geometry.inBasis b B = Matrix.diagonal (fun i => pseudoInverseRoot (hG.isHermitian.eigenvalues i)) :=
    inEigenbasis_cfc G hG.isHermitian pseudoInverseRoot
  have hdiagG : Geometry.inBasis b G = Matrix.diagonal hG.isHermitian.eigenvalues := Gap.inEigenbasis_diagonal G hG.isHermitian
  have hrow : rowGram R = B*G*B := by
    simp only [rowGram, R, Matrix.transpose_mul, hB.isSymm.eq, G, Matrix.mul_assoc]
  have hdiag : Geometry.inBasis b (1-rowGram R) =
      Matrix.diagonal (fun i => 1-(pseudoInverseRoot (hG.isHermitian.eigenvalues i))^2*hG.isHermitian.eigenvalues i) := by
    rw [hrow, Geometry.inBasis_sub, Geometry.inBasis_one, Geometry.inBasis_mul, Geometry.inBasis_mul,
      hdiagB, hdiagG, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext i
    ring
  have hPSD : (1-rowGram R).PosSemidef := by
    apply posSemidef_of_inBasis b
    rw [hdiag, Matrix.posSemidef_diagonal_iff]
    exact fun i => sub_nonneg.mpr (pseudoInverseRoot_identities _ (hG.eigenvalues_nonneg i)).1
  have he : (X*Rᵀ).trace = nuclearNorm X := by
    have hprod : X*Rᵀ = G*B := by simp only [R, Matrix.transpose_mul, hB.isSymm.eq, G, rowGram, Matrix.mul_assoc]
    rw [hprod, ← Geometry.inBasis_trace b, Geometry.inBasis_mul, hdiagG, hdiagB,
      Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, nuclearNorm_spectral]
    apply Finset.sum_congr rfl
    intro i _
    exact (pseudoInverseRoot_identities _ (hG.eigenvalues_nonneg i)).2
  exact ⟨R, operatorNorm_le_one_of_rowGram R hPSD, he⟩

theorem nuclearNorm_triangle (X Y : MatR n) : nuclearNorm (X+Y) ≤ nuclearNorm X+nuclearNorm Y := by
  obtain ⟨R, hR, he⟩ := nuclear_dual_attainment (X+Y)
  rw [← he, Matrix.add_mul, Matrix.trace_add]
  exact add_le_add (trace_le_nuclear X R hR) (trace_le_nuclear Y R hR)

end SharpCut.Nuclear
