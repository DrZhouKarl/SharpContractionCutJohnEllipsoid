import SharpCut.Certificate.ContactGram
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Coupling control derived from the positive contact Gram matrix -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

theorem sum_outer_bilinear {ι : Type*} [Fintype ι] (q : ι → V n) (w : ι → ℝ) (x y : V n) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, w i • outer (q i)) y⟫ =
      ∑ i, w i*⟪q i, x⟫*⟪q i, y⟫ := by
  rw [matrix_action_sum]
  simp only [inner_sum, matrix_action_smul, real_inner_smul_right,
    Khachiyan.outer_action, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_comm x (q i)]
  ring

theorem finite_gram_cauchy {ι : Type*} [Fintype ι] (q : ι → V n) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (x y : V n) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, w i • outer (q i)) y⟫^2 ≤
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, w i • outer (q i)) x⟫*
        ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, w i • outer (q i)) y⟫ := by
  rw [sum_outer_bilinear, sum_outer_quadratic, sum_outer_quadratic]
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i hi => mul_nonneg (hw i) (sq_nonneg ⟪q i, x⟫))
    (fun i hi => mul_nonneg (hw i) (sq_nonneg ⟪q i, y⟫))
    (fun i hi => le_of_eq (by ring))

theorem gramVector_axial_pairing (F : JohnFrame n N) (v : V n) (hv : ‖v‖ = 1) (i : Fin N) :
    ⟪gramVector F v i, v⟫ = gramAxialScale n*(height F v i-inverseDimension n) := by
  have hy : ⟪transverse v (F.contact i), v⟫ = 0 := by
    simpa only [real_inner_comm] using axis_transverse_inner v (F.contact i) hv
  rw [gramVector, inner_add_left, real_inner_smul_left, real_inner_smul_left, hy,
    real_inner_self_eq_norm_sq, hv, one_pow, mul_one, mul_zero, add_zero]

theorem gramVector_transverse_pairing (F : JohnFrame n N) (v u : V n)
    (hu : ⟪u, v⟫ = 0) (i : Fin N) :
    ⟪gramVector F v i, u⟫ = gramTransverseScale n*⟪transverse v (F.contact i), u⟫ := by
  have hu' : ⟪v, u⟫ = 0 := by rwa [real_inner_comm]
  rw [gramVector, inner_add_left, real_inner_smul_left, real_inner_smul_left, hu', mul_zero, zero_add]

theorem contactGram_axial (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (contactGram F v) v⟫ = axialDeficit F v := by
  rw [contactGram, sum_outer_quadratic]
  simp_rw [gramVector_axial_pairing F v hv]
  exact gram_axial_mass F hn v

theorem contactGram_transverse (F : JohnFrame n N) (hn : 2 ≤ n)
    (v u : V n) (hv : ‖v‖ = 1) (hu : ⟪u, v⟫ = 0) :
    ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (contactGram F v) u⟫ =
      cutWeight n*‖u‖^2-⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v) u⟫ := by
  have he : ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (contactGram F v) u⟫ =
      (gramTransverseScale n)^2*⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePlusMoment F v) u⟫ := by
    rw [contactGram, sum_outer_quadratic, transversePlusMoment, sum_outer_quadratic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [gramVector_transverse_pairing F v u hu i]
    change gramWeight F v i*(gramTransverseScale n*⟪transverse v (F.contact i), u⟫)^2 = _
    unfold gramWeight
    ring
  rw [he, ← real_inner_smul_right, ← matrix_action_smul, gram_transverse_mass F hn v hv,
    matrix_action_sub, inner_sub_right, matrix_action_smul, real_inner_smul_right,
    projector_transverse_identity v u hu, real_inner_self_eq_norm_sq]

theorem contactGram_mixed (F : JohnFrame n N) (hn : 2 ≤ n)
    (v u : V n) (hv : ‖v‖ = 1) (hu : ⟪u, v⟫ = 0) :
    ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (contactGram F v) u⟫ = -⟪transverseCoupling F v, u⟫ := by
  rw [contactGram, sum_outer_bilinear]
  simp_rw [gramVector_axial_pairing F v hv, gramVector_transverse_pairing F v u hu]
  calc
    _ = ⟪∑ i, (gramWeight F v i*(gramAxialScale n*(height F v i-inverseDimension n))*
          gramTransverseScale n) • transverse v (F.contact i), u⟫ := by
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro i hi
      rw [real_inner_smul_left]
      ring
    _ = _ := by rw [gram_mixed_mass F hn v hv, inner_neg_left]

/-- The Gram bound used by both low-dimensional determinant branches. -/
theorem transverse_coupling_bound (F : JohnFrame n N) (hn : 2 ≤ n)
    (v u : V n) (hv : ‖v‖ = 1) (hu : ⟪u, v⟫ = 0) :
    ⟪transverseCoupling F v, u⟫^2 ≤ axialDeficit F v*
      (cutWeight n*‖u‖^2-⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v) u⟫) := by
  have h := finite_gram_cauchy (gramVector F v) (gramWeight F v)
    (gramWeight_nonneg F hn v hv) v u
  change ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (contactGram F v) u⟫^2 ≤
    ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (contactGram F v) v⟫*
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (contactGram F v) u⟫ at h
  rw [contactGram_axial F hn v hv, contactGram_transverse F hn v u hv hu,
    contactGram_mixed F hn v u hv hu, neg_sq] at h
  exact h

end SharpCut.Certificate
