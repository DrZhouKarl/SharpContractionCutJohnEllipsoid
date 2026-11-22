import SharpCut.Simplex.RegularGram

/-! # Unweighted regular contact identities and centered regular vertices -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix Set
namespace SharpCut.Simplex
open Certificate
variable {m : ℕ}

def normal (m : ℕ) : Fin (m+2) → V (m+1) := (regularFrame m).contact
def vertex (m : ℕ) (i : Fin (m+2)) : V (m+1) := (-((m : ℝ)+1)) • normal m i
def body (m : ℕ) : Set (V (m+1)) := (regularFrame m).polytope

theorem normal_unit (m : ℕ) (i : Fin (m+2)) : ‖normal m i‖ = 1 := (regularFrame m).contact_unit i
theorem normal_gram (m : ℕ) (i j : Fin (m+2)) (hij : i ≠ j) :
    ⟪normal m i,normal m j⟫ = -inverseDimension (m+1) := regular_gram m i j hij

theorem normal_sum (m : ℕ) : (∑ i, normal m i) = 0 := by
  have hp : 0 < johnWeight (m+1) := johnWeight_pos (by omega)
  have he : johnWeight (m+1) • (∑ i, normal m i) = 0 := by
    rw [Finset.smul_sum]
    calc
      _ = ∑ i, (regularFrame m).weight i • (regularFrame m).contact i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [regular_weights]
        rfl
      _ = 0 := (regularFrame m).first_moment
  exact (smul_eq_zero.mp he).resolve_left hp.ne'

theorem normal_outer_sum (m : ℕ) :
    (∑ i, outer (normal m i)) = (((m : ℝ)+2)/((m : ℝ)+1)) • (1 : MatR (m+1)) := by
  have hp : 0 < johnWeight (m+1) := johnWeight_pos (by omega)
  have he : johnWeight (m+1) • (∑ i, outer (normal m i)) = (1 : MatR (m+1)) := by
    rw [Finset.smul_sum]
    calc
      _ = ∑ i, (regularFrame m).weight i • outer ((regularFrame m).contact i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [regular_weights]
        rfl
      _ = 1 := (regularFrame m).second_moment
  have h := congrArg (fun A : MatR (m+1) => (johnWeight (m+1))⁻¹ • A) he
  rw [smul_smul,inv_mul_cancel₀ hp.ne',one_smul] at h
  have hc : (johnWeight (m+1))⁻¹ = ((m : ℝ)+2)/((m : ℝ)+1) := by
    rw [johnWeight,inv_div]
    simp only [Nat.cast_add,Nat.cast_one]
    ring
  rwa [hc] at h

theorem vertex_sum (m : ℕ) : (∑ i, vertex m i) = 0 := by
  simp only [vertex,← Finset.smul_sum,normal_sum,smul_zero]

theorem vertex_outer_sum (m : ℕ) :
    (∑ i, outer (vertex m i)) = (((m : ℝ)+1)*((m : ℝ)+2)) • (1 : MatR (m+1)) := by
  have ho (i : Fin (m+2)) : outer (vertex m i) = (((m : ℝ)+1)^2) • outer (normal m i) := by
    ext a b
    simp only [vertex,Khachiyan.outer_apply,WithLp.ofLp_smul,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  simp only [ho,← Finset.smul_sum,normal_outer_sum,smul_smul]
  congr 1
  have hp : (m : ℝ)+1 ≠ 0 := by positivity
  field_simp [hp] <;> ring

theorem vertex_norm (m : ℕ) (i : Fin (m+2)) : ‖vertex m i‖ = (m : ℝ)+1 := by
  simp only [vertex,norm_smul,normal_unit,Real.norm_eq_abs,mul_one,abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ (m : ℝ)+1)]

theorem vertex_dist_sq (m : ℕ) (i j : Fin (m+2)) (hij : i ≠ j) :
    ‖vertex m i-vertex m j‖^2 = 2*((m : ℝ)+1)*((m : ℝ)+2) := by
  rw [norm_sub_sq_real,vertex_norm,vertex_norm]
  have hinner : ⟪vertex m i,vertex m j⟫ = -((m : ℝ)+1) := by
    rw [vertex,vertex,real_inner_smul_left,real_inner_smul_right,normal_gram m i j hij,inverseDimension]
    simp only [Nat.cast_add,Nat.cast_one]
    have hp : (m : ℝ)+1 ≠ 0 := by positivity
    field_simp [hp] <;> ring
  rw [hinner]
  ring

theorem body_isConvexBody (m : ℕ) : IsConvexBody (body m) := (regularFrame m).polytope_isConvexBody
theorem body_isJohnNormalized (m : ℕ) : IsJohnNormalized (body m) := (regularFrame m).polytope_isJohnNormalized

end SharpCut.Simplex
