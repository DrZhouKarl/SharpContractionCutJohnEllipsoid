import SharpCut.Certificate.DefectRange
import SharpCut.Certificate.MatrixGeometry
import SharpCut.Certificate.Factorization
import SharpCut.Certificate.ModelDeterminant

/-!
# Coordinate-free transverse John moments

The ambient matrices act on the actual Euclidean space. The identity on the
transverse space is represented by the orthogonal projector, whose null axis
is kept explicit until an orthonormal coordinate system is chosen.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

theorem cross_mul (A : MatR n) (hA : A.IsSymm) (u w : V n) :
    cross u w*A = cross u (Matrix.toEuclideanCLM (𝕜 := ℝ) A w) := by
  apply Matrix.transpose_injective
  rw [Matrix.transpose_mul, hA.eq, cross_transpose, mul_cross, cross_transpose]

theorem outer_congruence (A : MatR n) (hA : A.IsSymm) (u : V n) :
    A*outer u*A = outer (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) := by
  change A*cross u u*A = _
  rw [mul_cross, cross_mul A hA, cross_self]

theorem transverse_axis_zero (v : V n) (hv : ‖v‖ = 1) : transverse v v = 0 := by
  simp only [transverse, real_inner_self_eq_norm_sq, hv, one_pow, one_smul, sub_self]

theorem transverse_first_moment (F : JohnFrame n N) (v : V n) :
    (∑ i, F.weight i • transverse v (F.contact i)) = 0 := by
  have h := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (projector v)) F.first_moment
  simpa only [map_sum, map_smul, map_zero, projector_action] using h

theorem transverse_mixed_moment (F : JohnFrame n N) (v : V n) (hv : ‖v‖ = 1) :
    (∑ i, (F.weight i*height F v i) • transverse v (F.contact i)) = 0 := by
  have h := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (projector v)) (F.reconstruction v)
  simpa only [map_sum, map_smul, projector_action, height, transverse_axis_zero v hv] using h

theorem transverse_second_moment (F : JohnFrame n N) (v : V n) (hv : ‖v‖ = 1) :
    (∑ i, F.weight i • outer (transverse v (F.contact i))) = projector v := by
  have hP : (projector v).IsSymm :=
    (Matrix.isHermitian_one.sub (Khachiyan.outer_posSemidef v).isHermitian).isSymm
  have hi (i : Fin N) : outer (transverse v (F.contact i)) =
      projector v*outer (F.contact i)*projector v := by
    rw [outer_congruence _ hP, projector_action]
  calc
    _ = ∑ i, projector v*(F.weight i • outer (F.contact i))*projector v := by
      apply Finset.sum_congr rfl
      intro i hi'
      rw [hi, Matrix.mul_smul, Matrix.smul_mul]
    _ = projector v*(∑ i, F.weight i • outer (F.contact i))*projector v := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
    _ = _ := by rw [F.second_moment, Matrix.mul_one, projector_idempotent v hv]

def transverseVectorMoment (F : JohnFrame n N) (v : V n) (r : ℕ) : V n :=
  ∑ i, (F.weight i/(1-boostParameter n*height F v i)*(height F v i)^r) •
    transverse v (F.contact i)

def transverseMatrixMoment (F : JohnFrame n N) (v : V n) (r : ℕ) : MatR n :=
  ∑ i, (F.weight i/(1-boostParameter n*height F v i)*(height F v i)^r) •
    outer (transverse v (F.contact i))

theorem transverse_vector_recurrence (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) (r : ℕ) :
    transverseVectorMoment F v r-boostParameter n • transverseVectorMoment F v (r+1) =
      ∑ i, (F.weight i*(height F v i)^r) • transverse v (F.contact i) := by
  unfold transverseVectorMoment
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul, ← sub_smul]
  congr 1
  rw [pow_succ]
  field_simp [(height_denominator_pos F hn v hv i).ne']

theorem transverse_matrix_recurrence (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) (r : ℕ) :
    transverseMatrixMoment F v r-boostParameter n • transverseMatrixMoment F v (r+1) =
      ∑ i, (F.weight i*(height F v i)^r) • outer (transverse v (F.contact i)) := by
  unfold transverseMatrixMoment
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul, ← sub_smul]
  congr 1
  rw [pow_succ]
  field_simp [(height_denominator_pos F hn v hv i).ne']

theorem transverse_moments (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    transverseVectorMoment F v 0 = boostParameter n • transverseVectorMoment F v 1 ∧
    transverseVectorMoment F v 1 = boostParameter n • transverseVectorMoment F v 2 ∧
    transverseMatrixMoment F v 0-boostParameter n • transverseMatrixMoment F v 1 = projector v := by
  refine ⟨?_, ?_, ?_⟩
  · have h := transverse_vector_recurrence F hn v hv 0
    simp only [pow_zero, mul_one, transverse_first_moment] at h
    exact sub_eq_zero.mp h
  · have h := transverse_vector_recurrence F hn v hv 1
    simp only [pow_one, transverse_mixed_moment F v hv] at h
    exact sub_eq_zero.mp h
  · simpa only [pow_zero, mul_one, transverse_second_moment F v hv] using
      transverse_matrix_recurrence F hn v hv 0

theorem transverseMatrixMoment_trace (F : JohnFrame n N) (v : V n) (hv : ‖v‖ = 1) (r : ℕ) :
    (transverseMatrixMoment F v r).trace = reweightedMoment F v r-reweightedMoment F v (r+2) := by
  unfold transverseMatrixMoment reweightedMoment
  simp only [Matrix.trace_sum, Matrix.trace_smul, Khachiyan.trace_outer,
    transverse_norm_sq v _ hv, F.contact_unit, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [height, pow_add]
  ring

end SharpCut.Certificate
