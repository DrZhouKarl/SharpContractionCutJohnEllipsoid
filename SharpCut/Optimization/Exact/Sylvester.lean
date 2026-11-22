import SharpCut.Optimization.Exact.ContactRecovery

/-! # Genuine positive Sylvester injectivity for noncommuting contact moments -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Optimization
open Certificate
variable {n N : ℕ}

/-- Positive eigenvalues force every entry to vanish, without assuming H commutes with A. -/
theorem positive_sylvester_zero (A H : MatR n) (hA : A.PosDef) (hzero : A*H+H*A = 0) : H = 0 := by
  let B := hA.isHermitian.eigenvectorBasis
  have h := congrArg (Geometry.inBasis B) hzero
  rw [Geometry.inBasis_add, Geometry.inBasis_mul, Geometry.inBasis_mul, Gap.inEigenbasis_diagonal] at h
  have hz : Geometry.inBasis B (0 : MatR n) = 0 := by simp only [Geometry.inBasis, Matrix.mul_zero, Matrix.zero_mul]
  rw [hz] at h
  apply Geometry.inBasis_injective B
  rw [hz]
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply] at hij
  have hpos : 0 < hA.isHermitian.eigenvalues i+hA.isHermitian.eigenvalues j := add_pos (hA.eigenvalues_pos i) (hA.eigenvalues_pos j)
  have hprod : (hA.isHermitian.eigenvalues i+hA.isHermitian.eigenvalues j)*Geometry.inBasis B H i j = 0 := by
    linear_combination hij
  exact (mul_eq_zero.mp hprod).resolve_left hpos.ne'

def contactMoment (g : Fin N → V n) (α : Fin N → ℝ) (A : MatR n) : MatR n :=
  ∑ r, (α r/facetLength g A r) • outer (g r)

/-- The exact symmetrized aggregate equation for the original facet moment. -/
theorem contactMoment_aggregate (g : Fin N → V n) (α : Fin N → ℝ) (q : Fin N → V n) (A : MatR n)
    (hA : A.PosDef) (hq : ∀ r, q r = α r • facetDirection g A r) :
    aggregate g q = (1/2 : ℝ) • (A*contactMoment g α A+contactMoment g α A*A) := by
  have hpoint (r : Fin N) : symmetricOuter (q r) (g r) =
      (1/2 : ℝ) • ((α r/facetLength g A r) • (A*outer (g r)+outer (g r)*A)) := by
    rw [hq r, facetDirection]
    change symmetricOuter (α r • ((facetLength g A r)⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r))) (g r) = _
    rw [symmetricOuter, smul_smul]
    change (1/2 : ℝ) • (cross ((α r*(facetLength g A r)⁻¹) • Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)) (g r)+
      cross (g r) ((α r*(facetLength g A r)⁻¹) • Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r))) = _
    rw [cross_smul_left, cross_smul_right, ← mul_cross, ← cross_mul A hA.isHermitian.isSymm, cross_self,
      ← smul_add]
    simp only [div_eq_mul_inv]
  unfold aggregate contactMoment
  simp only [hpoint, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib, ← Finset.smul_sum]

/-- The matrix equation AT+TA=2 A^-1 identifies T=A^-2 through positive Sylvester injectivity. -/
theorem contactMoment_inverse_square {g : Fin N → V n} {α : Fin N → ℝ} {q : Fin N → V n} {A : MatR n}
    (hA : A.PosDef) (hq : ∀ r, q r = α r • facetDirection g A r) (hM : aggregate g q = A⁻¹) :
    contactMoment g α A = A⁻¹*A⁻¹ := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hagg := contactMoment_aggregate g α q A hA hq
  rw [hM] at hagg
  have heq : A*contactMoment g α A+contactMoment g α A*A = (2 : ℝ) • A⁻¹ := by
    have h := congrArg (fun M : MatR n => (2 : ℝ) • M) hagg
    rw [smul_smul] at h
    norm_num at h
    exact h.symm
  have hzero : A*(contactMoment g α A-A⁻¹*A⁻¹)+(contactMoment g α A-A⁻¹*A⁻¹)*A = 0 := by
    have hleft : A*(A⁻¹*A⁻¹) = A⁻¹ := by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hu, Matrix.one_mul]
    have hright : (A⁻¹*A⁻¹)*A = A⁻¹ := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul A hu, Matrix.mul_one]
    simp only [Matrix.mul_sub, Matrix.sub_mul, hleft, hright]
    rw [show A*contactMoment g α A-A⁻¹+(contactMoment g α A*A-A⁻¹) =
        (A*contactMoment g α A+contactMoment g α A*A)-(A⁻¹+A⁻¹) by abel, heq, two_smul, sub_self]
  exact sub_eq_zero.mp (positive_sylvester_zero A _ hA hzero)

end SharpCut.Optimization
