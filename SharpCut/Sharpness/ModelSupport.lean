import SharpCut.Sharpness.ModelEllipsoid
import SharpCut.Certificate.Feasibility

/-! # Exact support values and actual model ellipsoid containment -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Sharpness
open Certificate
variable {n N : ℕ}

theorem modelShape_norm_sq (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (modelShape v) u‖^2 =
      ⟪u, v⟫^2/4+(1-⟪u, v⟫^2)/(1-inverseDimension n) := by
  have hb := inverseDimension_bounds hn
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hs : ((Real.sqrt (1-inverseDimension n))⁻¹)^2 = 1/(1-inverseDimension n) := by
    rw [inv_pow, Real.sq_sqrt h1.le, one_div]
  have hc : ⟪v, u⟫ = ⟪u, v⟫ := real_inner_comm _ _
  rw [modelShape_action hn v u hv, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hv, one_pow, mul_one,
    real_inner_smul_left, real_inner_smul_right, axis_transverse_inner v u hv,
    mul_zero, zero_mul, add_zero, zero_add]
  rw [hs, transverse_norm_sq v u hv hu, hc]
  ring

theorem model_support_height (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (hheight : ⟪u, v⟫ = -1 ∨ ⟪u, v⟫ = inverseDimension n) :
    ⟪u, modelCenter v⟫+‖Matrix.toEuclideanCLM (𝕜 := ℝ) (modelShape v) u‖ = 1 := by
  have hb := inverseDimension_bounds hn
  have hsq := modelShape_norm_sq hn v u hv hu
  have hnorm := norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) (modelShape v) u)
  rw [modelCenter, real_inner_smul_right]
  rcases hheight with hs | hs
  · rw [hs] at hsq ⊢
    norm_num at hsq ⊢
    nlinarith only [hsq, hnorm]
  · rw [hs] at hsq ⊢
    have he : (inverseDimension n)^2/4+(1-(inverseDimension n)^2)/(1-inverseDimension n) =
        (1+inverseDimension n/2)^2 := by
      field_simp [show 1-inverseDimension n ≠ 0 by linarith [hb.2]] <;> ring
    rw [he] at hsq
    nlinarith only [hsq, hnorm, hb.1]

theorem model_cut_support (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    ⟪v, modelCenter v⟫+‖Matrix.toEuclideanCLM (𝕜 := ℝ) (modelShape v) v‖ = 0 := by
  rw [modelCenter, real_inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow, mul_one,
    modelShape_axis hn v hv, norm_smul, hv]
  norm_num

theorem model_feasible_contact_cut (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hh : ∀ i, height F v i = -1 ∨ height F v i = inverseDimension n) :
    IsFeasible (F.polytope ∩ centralHalfspace 0 v) (modelCenter v) (modelShape v) := by
  have hp : Optimization.PrimalFeasible (cutNormals F v) (cutOffsets N) (modelCenter v) (modelShape v) := by
    refine ⟨modelShape_posDef hn v hv, ?_⟩
    intro r
    refine Fin.cases ?_ (fun i => ?_) r
    · simp only [cutNormals, cutOffsets, Fin.cases_zero]
      exact (model_cut_support hn v hv).le
    · simp only [cutNormals, cutOffsets, Fin.cases_succ]
      exact (model_support_height hn v (F.contact i) hv (F.contact_unit i) (hh i)).le
  have h := (Optimization.primalFeasible_iff_containment _ _ _ _).mp hp
  rwa [cut_polytope] at h

end SharpCut.Sharpness
