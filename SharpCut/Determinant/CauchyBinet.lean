import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# Rectangular determinant expansion through principal-minor coefficients

The Weinstein--Aronszajn polynomial identity and the coefficient/minor theorem
give the rectangular Cauchy--Binet interface. All identities are kernel proofs;
no numerical minor calculation is trusted.
-/

noncomputable section
open scoped BigOperators
open Matrix Polynomial
namespace SharpCut.Determinant

def univIndexEquiv (n : ℕ) : (Finset.univ : Finset (Fin n)) ≃ Fin n where
  toFun := Subtype.val
  invFun := fun i => ⟨i, Finset.mem_univ i⟩
  left_inv := fun _ => by rfl
  right_inv := fun _ => rfl

theorem leading_reverse_coeff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.det (1+(Polynomial.X : Polynomial ℝ) • M.map Polynomial.C)).coeff n = M.det := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  have hp : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [hp]
  simp only [Finset.sum_singleton]
  exact Matrix.det_submatrix_equiv_self (univIndexEquiv n) M

theorem reverse_product_identity {n N : ℕ} (A : Matrix (Fin n) (Fin N) ℝ)
    (B : Matrix (Fin N) (Fin n) ℝ) :
    Matrix.det (1+(Polynomial.X : Polynomial ℝ) • (A*B).map Polynomial.C) =
      Matrix.det (1+(Polynomial.X : Polynomial ℝ) • (B*A).map Polynomial.C) := by
  have hab : (A*B).map Polynomial.C = A.map Polynomial.C*B.map Polynomial.C := by
    ext i j
    simp [Matrix.mul_apply, Matrix.map_apply]
  have hba : (B*A).map Polynomial.C = B.map Polynomial.C*A.map Polynomial.C := by
    ext i j
    simp [Matrix.mul_apply, Matrix.map_apply]
  have h := Matrix.det_one_add_mul_comm (A.map Polynomial.C)
    ((Polynomial.X : Polynomial ℝ) • B.map Polynomial.C)
  simpa only [Matrix.mul_smul, Matrix.smul_mul, ← hab, ← hba] using h

theorem rectangular_principal_minors {n N : ℕ} (A : Matrix (Fin n) (Fin N) ℝ)
    (B : Matrix (Fin N) (Fin n) ℝ) :
    (A*B).det = ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
      ((B*A).submatrix (Subtype.val : s → Fin N) (Subtype.val : s → Fin N)).det := by
  rw [← leading_reverse_coeff (A*B), reverse_product_identity,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors]

def minorWeight {n N : ℕ} (X : Matrix (Fin n) (Fin N) ℝ) (s : Finset (Fin N)) : ℝ :=
  ((Xᵀ*X).submatrix (Subtype.val : s → Fin N) (Subtype.val : s → Fin N)).det

theorem minorWeight_nonneg {n N : ℕ} (X : Matrix (Fin n) (Fin N) ℝ) (s : Finset (Fin N)) :
    0 ≤ minorWeight X s := by
  have h := Matrix.posSemidef_conjTranspose_mul_self X
  have hs : Xᴴ = Xᵀ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
  rw [hs] at h
  exact (h.submatrix (Subtype.val : s → Fin N)).det_nonneg

def weightedGram {n N : ℕ} (X : Matrix (Fin n) (Fin N) ℝ) (f : Fin N → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := X*Matrix.diagonal f*Xᵀ

theorem scaled_principal_minor {n N : ℕ} (X : Matrix (Fin n) (Fin N) ℝ)
    (f : Fin N → ℝ) (s : Finset (Fin N)) :
    ((Matrix.diagonal f*Xᵀ)*X).submatrix (Subtype.val : s → Fin N) (Subtype.val : s → Fin N) =
      Matrix.diagonal (fun i : s => f i) *
        (Xᵀ*X).submatrix (Subtype.val : s → Fin N) (Subtype.val : s → Fin N) := by
  rw [Matrix.mul_assoc]
  ext i j
  change (Matrix.diagonal f*(Xᵀ*X)) (i : Fin N) (j : Fin N) = _
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul]
  rfl

theorem weighted_gram_expansion {n N : ℕ} (X : Matrix (Fin n) (Fin N) ℝ) (f : Fin N → ℝ) :
    (weightedGram X f).det = ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
      minorWeight X s * ∏ i ∈ s, f i := by
  rw [weightedGram, Matrix.mul_assoc, rectangular_principal_minors]
  apply Finset.sum_congr rfl
  intro s hs
  rw [scaled_principal_minor, Matrix.det_mul, Matrix.det_diagonal]
  simp only [minorWeight, Finset.univ_eq_attach, Finset.prod_attach]
  ring

theorem minor_weights_sum {n N : ℕ} (X : Matrix (Fin n) (Fin N) ℝ) (hX : X*Xᵀ = 1) :
    (∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard n, minorWeight X s) = 1 := by
  have h := weighted_gram_expansion X (fun _ => 1)
  simpa only [weightedGram, Matrix.diagonal_one, Matrix.mul_one, hX, Matrix.det_one,
    Finset.prod_const_one, mul_one] using h.symm

theorem weightedGram_posDef {n N : ℕ} (X : Matrix (Fin n) (Fin N) ℝ)
    (hX : X*Xᵀ = 1) (f : Fin N → ℝ) (hf : ∀ i, 0 < f i) : (weightedGram X f).PosDef := by
  have hi : Function.Injective X.vecMul := by
    have hl : Function.LeftInverse (fun y => y ᵥ* Xᵀ) (fun x => x ᵥ* X) := by
      intro x
      change (x ᵥ* X) ᵥ* Xᵀ = x
      rw [Matrix.vecMul_vecMul, hX, Matrix.vecMul_one]
    exact hl.injective
  have hD : (Matrix.diagonal f).PosDef := Matrix.PosDef.diagonal hf
  have h := hD.mul_mul_conjTranspose_same hi
  have hs : Xᴴ = Xᵀ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
  rwa [hs] at h

end SharpCut.Determinant
