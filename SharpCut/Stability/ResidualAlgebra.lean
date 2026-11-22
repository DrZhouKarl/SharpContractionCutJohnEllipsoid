import SharpCut.Stability.FrameNorms
import SharpCut.Certificate.ModelScales

/-! # Exact contact residual for the ordered Lorentz certificate -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Stability
open Certificate
variable {n N : ℕ}

/-- Equation (9.4), on the actual Euclidean space. -/
def contactResidual (v u : V n) : V n :=
  (-(⟪u,v⟫-inverseDimension n)/((2-inverseDimension n)*(1-boostParameter n*⟪u,v⟫))) •
    (((1-inverseDimension n)*(⟪u,v⟫+1)) • v+Real.sqrt (1-inverseDimension n) • transverse v u)

theorem residual_scalar_coefficients (b s : ℝ) (hd : 2-b ≠ 0) (hden : 1-b/(2-b)*s ≠ 0) :
    (1-(1+b)/2*s)/(1-b/(2-b)*s)*(s-b/(2-b))-(2-(1+b)/2)*s+b =
      -(s-b)/((2-b)*(1-b/(2-b)*s))*((1-b)*(s+1)) ∧
    2/(2-b)*(1-(1+b)/2*s)/(1-b/(2-b)*s)-1 =
      -(s-b)/((2-b)*(1-b/(2-b)*s)) := by
  have hD : 2-b-b*s ≠ 0 := by
    have he : 2-b-b*s = (2-b)*(1-b/(2-b)*s) := by field_simp [hd] <;> ring
    rw [he]
    exact mul_ne_zero hd hden
  constructor <;> field_simp [hd, hD, hden] <;> ring

theorem contactResidual_expansion (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    contactResidual v u =
      (1-cutWeight n*⟪u,v⟫) • lorentzDirection v u-
        Matrix.toEuclideanCLM (𝕜 := ℝ) (inverseModel v) u+
        (cutWeight n*⟪u,v⟫+inverseDimension n) • v := by
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hs := abs_le.mp (by simpa only [hu, hv, mul_one] using abs_real_inner_le_norm u v)
  have hden : 1-boostParameter n*⟪u,v⟫ ≠ 0 := by
    have h := certificate_denominator_lower hn hs.2
    change 2/3 ≤ 1-boostParameter n*⟪u,v⟫ at h
    linarith
  have hc := residual_scalar_coefficients (inverseDimension n) ⟪u,v⟫ hd hden
  have hM : Matrix.toEuclideanCLM (𝕜 := ℝ) (inverseModel v) u =
      (2*⟪u,v⟫) • v+Real.sqrt (1-inverseDimension n) • transverse v u := by
    apply WithLp.ofLp_injective 2
    have ho := congrArg (fun x : V n => x.ofLp) (Khachiyan.outer_action v u)
    have hp := congrArg (fun x : V n => x.ofLp) (projector_action v u)
    simp only [Khachiyan.matrix_action_ofLp, WithLp.ofLp_smul] at ho hp
    simp only [inverseModel, Khachiyan.matrix_action_ofLp, Matrix.add_mulVec, Matrix.smul_mulVec,
      ho, hp, WithLp.ofLp_add, WithLp.ofLp_smul, smul_smul]
    rw [real_inner_comm v u]
  rw [hM]
  have hk : Real.sqrt (1-(boostParameter n)^2) =
      2*Real.sqrt (1-inverseDimension n)/(2-inverseDimension n) := boostScale_explicit hn
  ext j
  simp only [contactResidual, lorentzDirection, WithLp.ofLp_smul,
    WithLp.ofLp_add, WithLp.ofLp_sub, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
    smul_eq_mul]
  rw [hk]
  simp only [cutWeight, boostParameter, div_eq_mul_inv, _root_.mul_inv_rev] at hc ⊢
  linear_combination -(v j)*hc.1-Real.sqrt (1-inverseDimension n)*(transverse v u j)*hc.2


/-- The exact squared norm in (9.5), before any weighted summation. -/
theorem contactResidual_norm_sq (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    ‖contactResidual v u‖^2 =
      (1-inverseDimension n)/(2-inverseDimension n)*
        ((1+⟪u,v⟫)*(⟪u,v⟫-inverseDimension n)^2/(1-boostParameter n*⟪u,v⟫)) := by
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hs := abs_le.mp (by simpa only [hu, hv, mul_one] using abs_real_inner_le_norm u v)
  have hden : 1-boostParameter n*⟪u,v⟫ ≠ 0 := by
    have h := certificate_denominator_lower hn hs.2
    change 2/3 ≤ 1-boostParameter n*⟪u,v⟫ at h
    linarith
  rw [contactResidual, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    orthogonal_combination_norm_sq v (transverse v u) hv (axis_transverse_inner v u hv),
    transverse_norm_sq v u hv hu, Real.sq_sqrt (by linarith [hb.2] : 0 ≤ 1-inverseDimension n)]
  generalize hb_def : inverseDimension n = b at *
  generalize ha_def : boostParameter n = a at *
  generalize hs_def : ⟪u,v⟫ = s at *
  have ha : (2-b)*a = b := by
    rw [← hb_def, ← ha_def]
    unfold boostParameter
    exact mul_div_cancel₀ _ (by rw [hb_def]; exact hd)
  have hp : (1-b)^2*(s+1)^2+(1-b)*(1-s^2) = (1-b)*(s+1)*(2-b)*(1-a*s) := by
    linear_combination (1-b)*(s+1)*s*ha
  rw [mul_pow, hp]
  simp only [div_pow, mul_pow, neg_sq]
  field_simp [hd, hden] <;> ring

theorem cross_add_right (u w z : V n) : cross u (w+z) = cross u w+cross u z := by
  ext i j
  simp only [cross, Matrix.vecMulVec_apply, WithLp.ofLp_add, Pi.add_apply, Matrix.add_apply]
  ring

theorem cross_sub_right (u w z : V n) : cross u (w-z) = cross u w-cross u z := by
  apply Matrix.transpose_injective
  rw [cross_transpose, Matrix.transpose_sub, cross_transpose, cross_transpose, cross_sub_left]

/-- Isotropy supplies the model term; balance removes the constant vector. -/
theorem residual_aggregate (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    unrotatedQ F v-inverseModel v = ∑ i, F.weight i • cross (F.contact i) (contactResidual v (F.contact i)) := by
  have hM : (inverseModel v).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [inverseModel, projector, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Khachiyan.outer_apply, Matrix.one_apply, smul_eq_mul]
    simp only [eq_comm]
    ring
  have hm : (∑ i, F.weight i • cross (F.contact i)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (inverseModel v) (F.contact i))) = inverseModel v := by
    simp only [← cross_mul (inverseModel v) hM, cross_self, ← Matrix.smul_mul, ← Matrix.sum_mul,
      F.second_moment, Matrix.one_mul]
  have hr : (∑ i, F.weight i • cross (F.contact i)
      ((cutWeight n*⟪F.contact i,v⟫+inverseDimension n) • v)) = cutWeight n • outer v := by
    have hx : (∑ i, (F.weight i*(cutWeight n*⟪F.contact i,v⟫+inverseDimension n)) • F.contact i) =
        cutWeight n • v := by
      simp only [mul_add, add_smul, Finset.sum_add_distrib]
      have ht : (∑ i, (F.weight i*(cutWeight n*⟪F.contact i,v⟫)) • F.contact i) =
          cutWeight n • (∑ i, (F.weight i*⟪F.contact i,v⟫) • F.contact i) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul]
        congr 1
        ring
      have hb : (∑ i, (F.weight i*inverseDimension n) • F.contact i) =
          inverseDimension n • (∑ i, F.weight i • F.contact i) := by
        rw [Finset.smul_sum]
        simp only [smul_smul, mul_comm]
      rw [ht, hb, F.reconstruction, F.first_moment, smul_zero, add_zero]
    have hc := congrArg (fun x : V n => cross x v) hx
    simpa only [cross_sum_left, cross_smul_left, cross_smul_right, smul_smul, cross_self] using hc
  simp only [contactResidual_expansion hn v _ hv (F.contact_unit _), cross_add_right,
    cross_sub_right, cross_smul_right, smul_add, smul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, smul_smul]
  simp only [cross_smul_right, smul_smul] at hr
  rw [hm, hr]
  unfold unrotatedQ originalWeight
  abel

/-- The first bound of (9.3), with its exact coefficient. -/
theorem certificate_residual_bound (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (frobeniusNorm (unrotatedQ F v-inverseModel v))^2 ≤
      (1-inverseDimension n)/(2-inverseDimension n)*frameDefect F v := by
  rw [residual_aggregate F hn v hv]
  have h := F.weighted_matrix_bessel (fun i => contactResidual v (F.contact i))
  simp only [contactResidual_norm_sq hn v _ hv (F.contact_unit _)] at h
  convert h using 1
  unfold frameDefect defectTerm height
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end SharpCut.Stability
