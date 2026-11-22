import SharpCut.Examples.PyramidVertices

/-! # Five nonredundant supporting facets of the actual square-pyramid model -/

noncomputable section
open scoped RealInnerProductSpace
open Set
namespace SharpCut.Examples.SquarePyramid

theorem distinct_contact_inner_bound (i j : Fin 5) (hij : i ≠ j) :
    ⟪frame.contact i,frame.contact j⟫ ≤ (1/9 : ℝ) := by
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  fin_cases i <;> fin_cases j <;> norm_num at hij <;>
    norm_num [contact_array,inner_point] <;>
    nlinarith only [hs]

/-- Removing any of the five inequalities changes the body; the witness obeys all remaining inequalities. -/
theorem defining_facet_nonredundant (i : Fin 5) :
    ∃ x : V 3, 1 < ⟪frame.contact i,x⟫ ∧ ∀ j : Fin 5, j ≠ i → ⟪frame.contact j,x⟫ ≤ 1 := by
  refine ⟨(2 : ℝ) • frame.contact i,?_,?_⟩
  · rw [real_inner_smul_right,real_inner_self_eq_norm_sq,frame.contact_unit i,one_pow]
    norm_num
  · intro j hji
    rw [real_inner_smul_right]
    linarith only [distinct_contact_inner_bound j i hji]

theorem contact_injective : Function.Injective frame.contact := by
  intro i j he
  by_contra hij
  have h := distinct_contact_inner_bound i j hij
  rw [he,real_inner_self_eq_norm_sq,frame.contact_unit j,one_pow] at h
  norm_num at h

theorem latitude_contacts_and_weights (i : Fin 4) :
    frame.contact i.succ 2 = (1/3 : ℝ) ∧ frame.weight i.succ = (9/16 : ℝ) := by
  have hz : lateralBasis i 2 = 0 := by fin_cases i <;> simp [lateralBasis,coordinateAxis,EuclideanSpace.single_apply]
  rw [contact_function,weight_function]
  simp [Fin.cases_succ,vertical,coordinateAxis,EuclideanSpace.single_apply,hz,
    WithLp.ofLp_add,WithLp.ofLp_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]

end SharpCut.Examples.SquarePyramid
