import SharpCut.Matrix.Nuclear

/-! # Rank-one, finite-sum and logarithmic nuclear inequalities on real matrices -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Nuclear
open Certificate Optimization
variable {n : ℕ}

@[simp] theorem nuclearNorm_zero : nuclearNorm (0 : MatR n) = 0 := by
  simp [nuclearNorm, rowGram]

theorem nuclearNorm_smul_nonneg (r : ℝ) (hr : 0 ≤ r) (X : MatR n) : nuclearNorm (r • X) = r*nuclearNorm X := by
  apply le_antisymm
  · obtain ⟨R, hR, he⟩ := nuclear_dual_attainment (r • X)
    rw [← he, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (trace_le_nuclear X R hR) hr
  · obtain ⟨R, hR, he⟩ := nuclear_dual_attainment X
    have h := trace_le_nuclear (r • X) R hR
    rwa [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, he] at h

theorem nuclearNorm_sum {ι : Type*} (s : Finset ι) (X : ι → MatR n) :
    nuclearNorm (∑ i ∈ s, X i) ≤ ∑ i ∈ s, nuclearNorm (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (nuclearNorm_triangle (X i) (∑ j ∈ s, X j)).trans (add_le_add le_rfl hs)

theorem cross_product (u v w z : V n) : cross u v*cross w z = ⟪v,w⟫ • cross u z := by
  rw [cross, cross, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, ← Khachiyan.inner_eq_dotProduct]
  rfl

theorem rowGram_cross (u v : V n) : rowGram (cross u v) = ‖v‖^2 • outer u := by
  rw [rowGram, cross_transpose, cross_product, real_inner_self_eq_norm_sq, cross_self]

/-- Exact rank-one nuclear norm, including zero vectors and hence all singular boundary cases. -/
theorem nuclearNorm_cross (u v : V n) : nuclearNorm (cross u v) = ‖u‖*‖v‖ := by
  by_cases hu : u = 0
  · subst u
    simp [cross, nuclearNorm_zero]
  · have hup : 0 < ‖u‖ := norm_pos_iff.mpr hu
    let S : MatR n := (‖v‖/‖u‖) • outer u
    have hS : S.PosSemidef := (Khachiyan.outer_posSemidef u).smul (div_nonneg (norm_nonneg _) hup.le)
    have ho : outer u*outer u = ‖u‖^2 • outer u := by
      simpa only [cross_self, real_inner_self_eq_norm_sq] using cross_product u u u u
    have hecoef : (‖v‖/‖u‖)^2*‖u‖^2 = ‖v‖^2 := by field_simp [hup.ne']
    have hsquare : S^2 = rowGram (cross u v) := by
      dsimp only [S]
      rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, ho, smul_smul, smul_smul, rowGram_cross]
      congr 1
      nlinarith only [hecoef]
    rw [nuclearNorm, ← hsquare, CFC.sqrt_sq S hS.nonneg]
    dsimp only [S]
    rw [Matrix.trace_smul, Khachiyan.trace_outer, smul_eq_mul]
    field_simp [hup.ne']

def singularValue (X : MatR n) (i : Fin n) : ℝ :=
  ((CFC.sqrt_nonneg (rowGram X)).posSemidef.isHermitian).eigenvalues i

theorem singularValue_nonneg (X : MatR n) (i : Fin n) : 0 ≤ singularValue X i :=
  (CFC.sqrt_nonneg (rowGram X)).posSemidef.eigenvalues_nonneg i

theorem nuclearNorm_eq_sum_singularValues (X : MatR n) : nuclearNorm X = ∑ i, singularValue X i :=
  Khachiyan.Spectral.trace_eq_sum (CFC.sqrt_nonneg (rowGram X)).posSemidef.isHermitian

theorem singularValue_pos (X : MatR n) (hX : 0 < X.det) (i : Fin n) : 0 < singularValue X i :=
  (polarMatrix_posDef hX).eigenvalues_pos i

/-- The singular-value logarithmic sum uses det X>0 before removing the determinant absolute value. -/
theorem nuclear_logdet_spectral (X : MatR n) (hX : 0 < X.det) :
    nuclearNorm X-(n : ℝ)-Real.log X.det = ∑ i, (singularValue X i-1-Real.log (singularValue X i)) ∧
      0 ≤ nuclearNorm X-(n : ℝ)-Real.log X.det := by
  have hS := polarMatrix_posDef hX
  have hdet : (CFC.sqrt (rowGram X)).det = X.det := polarMatrix_det hX
  have hlog : Real.log X.det = ∑ i, Real.log (singularValue X i) := by
    rw [← hdet]
    change Real.log (polarMatrix X).det = ∑ i, Real.log (singularValue X i)
    rw [hS.isHermitian.det_eq_prod_eigenvalues]
    exact Real.log_prod (fun i _ => (singularValue_pos X hX i).ne')
  have he : nuclearNorm X-(n : ℝ)-Real.log X.det = ∑ i, (singularValue X i-1-Real.log (singularValue X i)) := by
    rw [nuclearNorm_eq_sum_singularValues, hlog]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  refine ⟨he, ?_⟩
  rw [he]
  apply Finset.sum_nonneg
  intro i _
  linarith only [Real.log_le_sub_one_of_pos (singularValue_pos X hX i)]

end SharpCut.Nuclear
