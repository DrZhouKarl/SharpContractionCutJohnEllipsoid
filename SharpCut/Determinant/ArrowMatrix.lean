import SharpCut.Determinant.TwoByTwo

/-! # Exact three-by-three axial/transverse determinant expansion -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
open Certificate

def arrowMatrix (a : ℝ) (B : MatR 2) (j : V 2) : MatR 3 :=
  Matrix.of (Fin.cases (Fin.cases a j.ofLp) (fun i => Fin.cases (j i) (fun k => B i k)))

@[simp] theorem arrow_zero_zero (a : ℝ) (B : MatR 2) (j : V 2) : arrowMatrix a B j 0 0 = a := rfl
@[simp] theorem arrow_zero_succ (a : ℝ) (B : MatR 2) (j : V 2) (i : Fin 2) : arrowMatrix a B j 0 i.succ = j i := rfl
@[simp] theorem arrow_succ_zero (a : ℝ) (B : MatR 2) (j : V 2) (i : Fin 2) : arrowMatrix a B j i.succ 0 = j i := rfl
@[simp] theorem arrow_succ_succ (a : ℝ) (B : MatR 2) (j : V 2) (i k : Fin 2) :
    arrowMatrix a B j i.succ k.succ = B i k := rfl

theorem arrow_determinant (a : ℝ) (B : MatR 2) (j : V 2) :
    (arrowMatrix a B j).det = a*B.det-⟪j, Matrix.toEuclideanCLM (𝕜 := ℝ) B.adjugate j⟫ := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two, Khachiyan.inner_matrix_action, Matrix.adjugate_fin_two]
  rw [show (1 : Fin 3) = (0 : Fin 2).succ by rfl, show (2 : Fin 3) = (1 : Fin 2).succ by rfl]
  simp only [arrow_zero_zero, arrow_zero_succ, arrow_succ_zero, arrow_succ_succ]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem arrow_one_add_determinant (x : ℝ) (E : MatR 2) (j : V 2) :
    (arrowMatrix (1-x) (1+E) j).det =
      (1-x)*(1+E.trace+E.det)-((1+E.trace)*‖j‖^2-⟪j, Matrix.toEuclideanCLM (𝕜 := ℝ) E j⟫) := by
  have hd : (1+E).det = 1+E.trace+E.det := by
    simpa only [one_smul, one_mul, one_pow] using det_one_add_scale_two E 1
  have ha : (1+E).adjugate = (1+E.trace) • (1 : MatR 2)-E := by
    simpa only [one_smul, one_mul] using adjugate_one_add_scale_two E 1
  rw [arrow_determinant, hd, ha, matrix_action_sub, matrix_action_smul,
    inner_sub_right, real_inner_smul_right, map_one, ContinuousLinearMap.one_apply,
    real_inner_self_eq_norm_sq]

end SharpCut.Determinant
