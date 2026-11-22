import SharpCut.Simplex.Properties
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-! # The contact polytope is an actual full-dimensional regular simplex

The vertices are -n times the unit normals. Exact nonnegative barycentric
coordinates prove the whole polytope/hull equality. Affine independence is
derived from the regular Gram matrix, not placed in an assumed certificate.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix Set
namespace SharpCut.Simplex
variable {m : ℕ}

theorem vertex_gram_all (m : ℕ) (i j : Fin (m+2)) :
    ⟪vertex m i,vertex m j⟫ = if i = j then ((m : ℝ)+1)^2 else -((m : ℝ)+1) := by
  classical
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl,real_inner_self_eq_norm_sq,vertex_norm]
  · rw [ite_eq_right hij,vertex,vertex,real_inner_smul_left,real_inner_smul_right,
      normal_gram m i j hij,inverseDimension]
    simp only [Nat.cast_add,Nat.cast_one]
    have hp : (m : ℝ)+1 ≠ 0 := by positivity
    field_simp [hp] <;> ring

theorem vertex_weighted_gram_sum (m : ℕ) (a : Fin (m+2) → ℝ) (j : Fin (m+2)) :
    (∑ i, a i*⟪vertex m i,vertex m j⟫) =
      (((m : ℝ)+1)*((m : ℝ)+2))*a j-((m : ℝ)+1)*(∑ i, a i) := by
  classical
  have he (i : Fin (m+2)) : ⟪vertex m i,vertex m j⟫ =
      (if i = j then ((m : ℝ)+1)*((m : ℝ)+2) else 0)-((m : ℝ)+1) := by
    rw [vertex_gram_all]
    split_ifs <;> ring
  simp only [he,mul_sub,Finset.sum_sub_distrib,mul_ite,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,← Finset.sum_mul]
  ring

theorem vertices_affineIndependent (m : ℕ) : AffineIndependent ℝ (vertex m) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hzero
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero Finset.univ w (vertex m) hw (0 : V (m+1)),
    Finset.weightedVSubOfPoint_apply] at hzero
  simp only [vsub_eq_sub,sub_zero] at hzero
  intro j
  have h := congrArg (fun x : V (m+1) => ⟪x,vertex m j⟫) hzero
  simp only [sum_inner,real_inner_smul_left,inner_zero_left] at h
  rw [vertex_weighted_gram_sum,hw,mul_zero,sub_zero] at h
  have hc : ((m : ℝ)+1)*((m : ℝ)+2) ≠ 0 := by positivity
  exact (mul_eq_zero.mp h).resolve_left hc

theorem vertex_mem_body (m : ℕ) (i : Fin (m+2)) : vertex m i ∈ body m := by
  intro j
  change ⟪normal m j,vertex m i⟫ ≤ 1
  by_cases hji : j = i
  · subst j
    rw [vertex,real_inner_smul_right,real_inner_self_eq_norm_sq,normal_unit,one_pow,mul_one]
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith only [hm]
  · have he : ⟪normal m j,vertex m i⟫ = 1 := by
      rw [vertex,real_inner_smul_right,normal_gram m j i hji,inverseDimension]
      simp only [Nat.cast_add,Nat.cast_one]
      have hp : (m : ℝ)+1 ≠ 0 := by positivity
      field_simp [hp] <;> ring
    exact he.le

def baryWeight (m : ℕ) (x : V (m+1)) (i : Fin (m+2)) : ℝ :=
  (1-⟪normal m i,x⟫)/((m : ℝ)+2)

theorem baryWeight_nonneg {x : V (m+1)} (hx : x ∈ body m) (i : Fin (m+2)) : 0 ≤ baryWeight m x i :=
  div_nonneg (sub_nonneg.mpr (hx i)) (by positivity)

theorem baryWeight_sum (m : ℕ) (x : V (m+1)) : (∑ i, baryWeight m x i) = 1 := by
  have hz : (∑ i, ⟪normal m i,x⟫) = 0 := by
    have h := congrArg (fun y : V (m+1) => ⟪y,x⟫) (normal_sum m)
    simpa only [sum_inner,inner_zero_left] using h
  simp only [baryWeight,← Finset.sum_div,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,hz,sub_zero,Nat.cast_add,Nat.cast_ofNat]
  have hp : (m : ℝ)+2 ≠ 0 := by positivity
  exact div_self hp

theorem baryWeight_reconstruction (m : ℕ) (x : V (m+1)) : (∑ i, baryWeight m x i • vertex m i) = x := by
  have he (i : Fin (m+2)) : baryWeight m x i • vertex m i =
      (-johnWeight (m+1)) • normal m i+(johnWeight (m+1)*⟪normal m i,x⟫) • normal m i := by
    rw [vertex,smul_smul,← add_smul]
    congr 1
    unfold baryWeight johnWeight
    simp only [Nat.cast_add,Nat.cast_one]
    ring
  calc
    _ = ∑ i, ((-johnWeight (m+1)) • normal m i+(johnWeight (m+1)*⟪normal m i,x⟫) • normal m i) :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ = (-johnWeight (m+1)) • (∑ i, normal m i)+
        ∑ i, (johnWeight (m+1)*⟪normal m i,x⟫) • normal m i := by
      rw [Finset.sum_add_distrib,Finset.smul_sum]
    _ = x := by
      rw [normal_sum,smul_zero,zero_add]
      simpa only [normal,regular_weights] using (regularFrame m).reconstruction x

theorem body_eq_vertex_hull (m : ℕ) : body m = convexHull ℝ (Set.range (vertex m)) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact mem_convexHull_of_exists_fintype (baryWeight m x) (vertex m)
      (baryWeight_nonneg hx) (baryWeight_sum m x) (fun i => ⟨i,rfl⟩) (baryWeight_reconstruction m x)
  · exact convexHull_min (by rintro _ ⟨i,rfl⟩; exact vertex_mem_body m i) (body_isConvexBody m).2.1

/-- An actual full-dimensional regular simplex exists in each positive dimension. -/
theorem regular_simplex_geometry (m : ℕ) :
    AffineIndependent ℝ (vertex m) ∧ body m = convexHull ℝ (Set.range (vertex m)) ∧
    IsConvexBody (body m) ∧ IsJohnNormalized (body m) ∧
    (∑ i, vertex m i) = 0 ∧
    (∀ i j, i ≠ j → ‖vertex m i-vertex m j‖^2 = 2*((m : ℝ)+1)*((m : ℝ)+2)) :=
  ⟨vertices_affineIndependent m,body_eq_vertex_hull m,body_isConvexBody m,body_isJohnNormalized m,
    vertex_sum m,vertex_dist_sq m⟩

end SharpCut.Simplex
