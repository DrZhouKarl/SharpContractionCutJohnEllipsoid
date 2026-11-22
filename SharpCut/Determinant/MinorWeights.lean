import SharpCut.Determinant.CauchyBinet
import SharpCut.Certificate.ModelDeterminant

/-! # Squared maximal-minor weights and their exact column marginals -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
variable {n N : ℕ}

def columnVector (X : Matrix (Fin n) (Fin N) ℝ) (j : Fin N) : V n :=
  WithLp.toLp 2 (fun i => X i j)

theorem minorWeight_square (X : Matrix (Fin n) (Fin N) ℝ) (s : Finset (Fin N))
    (e : Fin n ≃ s) :
    minorWeight X s = (X.submatrix id (fun i => (e i : Fin N))).det^2 := by
  let G := (Xᵀ*X).submatrix (Subtype.val : s → Fin N) (Subtype.val : s → Fin N)
  let M := X.submatrix id (fun i => (e i : Fin N))
  have he : (G.submatrix e e).det = G.det := Matrix.det_submatrix_equiv_self e G
  have hM : G.submatrix e e = Mᵀ*M := by
    ext i j
    simp only [G, M, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, id_eq]
  change G.det = M.det^2
  rw [← he, hM, Matrix.det_mul, Matrix.det_transpose, pow_two]

theorem weightedGram_single_gain (X : Matrix (Fin n) (Fin N) ℝ) (j : Fin N) :
    weightedGram X (fun k => if k = j then 2 else 1) = X*Xᵀ+outer (columnVector X j) := by
  ext i l
  change (∑ k, (X*Matrix.diagonal (fun k => if k = j then (2 : ℝ) else 1)) i k*X l k) =
    (∑ k, X i k*X l k)+X i j*X l j
  simp only [Matrix.mul_diagonal]
  have hf (k : Fin N) : (if k = j then 2 else 1 : ℝ) = 1+(if k = j then 1 else 0) := by
    by_cases h : k = j <;> norm_num [h]
  simp_rw [hf, mul_add, mul_one, add_mul]
  rw [Finset.sum_add_distrib]
  simp [mul_ite, ite_mul]

theorem prod_single_gain (s : Finset (Fin N)) (j : Fin N) :
    (∏ k ∈ s, (if k = j then 2 else 1 : ℝ)) = 1+(if j ∈ s then 1 else 0) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ih]
    by_cases hj : a = j
    · subst a; norm_num [ha]
    · simp [hj, Ne.symm hj]

theorem minor_column_marginal (X : Matrix (Fin n) (Fin N) ℝ) (hX : X*Xᵀ = 1) (j : Fin N) :
    (∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
      if j ∈ s then minorWeight X s else 0) = ‖columnVector X j‖^2 := by
  have h := weighted_gram_expansion X (fun k => if k = j then 2 else 1)
  rw [weightedGram_single_gain, hX] at h
  change (1+Matrix.vecMulVec (columnVector X j).ofLp (columnVector X j).ofLp).det = _ at h
  rw [Certificate.det_one_add_cross, real_inner_self_eq_norm_sq] at h
  simp_rw [prod_single_gain, mul_add, mul_one, mul_ite, mul_one, mul_zero] at h
  rw [Finset.sum_add_distrib, minor_weights_sum X hX] at h
  linarith

end SharpCut.Determinant
