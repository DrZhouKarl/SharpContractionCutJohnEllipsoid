import SharpCut.Certificate.LorentzBlock
import SharpCut.Sharpness.ModelSupport

/-! # Exact Lorentz-to-model support direction matching at the pole and latitude -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Certificate
variable {n : ℕ}

theorem lorentz_pole (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) : lorentzDirection v (-v) = -v := by
  have hb := inverseDimension_bounds hn
  have ha : 0 < boostParameter n := (Scalar.lorentz_parameter_bounds _ hb.1 hb.2).1
  have hden : 1+boostParameter n ≠ 0 := by linarith
  have hs : ⟪-v,v⟫ = -1 := by rw [inner_neg_left, real_inner_self_eq_norm_sq, hv, one_pow]
  have hy : transverse v (-v) = 0 := by unfold transverse; rw [hs]; module
  rw [lorentzDirection, hs, hy, smul_zero, add_zero, smul_smul]
  have he : (1-boostParameter n*(-1))⁻¹*(-1-boostParameter n) = -1 := by field_simp [hden] <;> ring
  rw [he, neg_one_smul]

/-- The latitude coefficient identities used by the exact direction matching (3.9). -/
theorem model_latitude_coefficients (hn : 2 ≤ n) :
    (1-boostParameter n*inverseDimension n)⁻¹*(inverseDimension n-boostParameter n) =
      (1+inverseDimension n/2)⁻¹*(inverseDimension n/2) ∧
    (1-boostParameter n*inverseDimension n)⁻¹*boostScale n =
      (1+inverseDimension n/2)⁻¹*(Real.sqrt (1-inverseDimension n))⁻¹ := by
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have h1 : 1-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hp : 2+inverseDimension n ≠ 0 := by linarith [hb.1]
  have hs : Real.sqrt (1-inverseDimension n) ≠ 0 := (Real.sqrt_pos.mpr (by linarith [hb.2])).ne'
  have hsq := Real.sq_sqrt (by linarith [hb.2] : 0 ≤ 1-inverseDimension n)
  have hden : 1-boostParameter n*inverseDimension n ≠ 0 := by
    have he : 1-boostParameter n*inverseDimension n = (1-inverseDimension n)*(2+inverseDimension n)/(2-inverseDimension n) := by
      unfold boostParameter
      field_simp [hd] <;> ring
    rw [he]
    exact div_ne_zero (mul_ne_zero h1 hp) hd
  have hlin : 2-inverseDimension n-(inverseDimension n)^2 ≠ 0 := by
    have he : 2-inverseDimension n-(inverseDimension n)^2 = (1-inverseDimension n)*(2+inverseDimension n) := by ring
    rw [he]
    exact mul_ne_zero h1 hp
  constructor
  · unfold boostParameter
    field_simp [hd, h1, hp, hden, hlin] <;> ring
  · rw [boostScale_explicit hn, ← Real.sqrt_div_self (x := 1-inverseDimension n)]
    unfold boostParameter
    field_simp [hd, h1, hp, hs, hden, hlin] <;> ring

/-- The independently stated exact model direction matching (3.9), including both equality heights. -/
theorem lorentz_model_direction (hn : 2 ≤ n) (v u : V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (hh : ⟪u,v⟫ = -1 ∨ ⟪u,v⟫ = inverseDimension n) :
    lorentzDirection v u = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u‖⁻¹ •
      Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u := by
  rcases hh with hp | hb
  · have hu' : u = -v := by
      have hs : ‖u+v‖^2 = 0 := by rw [norm_add_sq_real, hu, hv, hp]; norm_num
      exact eq_neg_of_add_eq_zero_left (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))
    rw [hu', lorentz_pole hn v hv, map_neg, Sharpness.modelShape_axis hn v hv]
    norm_num [norm_smul, hv, smul_smul]
  · have hsupport := Sharpness.model_support_height hn v u hv hu (Or.inr hb)
    have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Sharpness.modelShape v) u‖ = 1+inverseDimension n/2 := by
      rw [Sharpness.modelCenter, real_inner_smul_right, hb] at hsupport
      linarith only [hsupport]
    rw [hnorm, lorentzDirection, hb, Sharpness.modelShape_action hn v u hv, real_inner_comm u v, hb,
      smul_add, smul_smul, smul_smul, smul_add, smul_smul, smul_smul]
    have hc := model_latitude_coefficients hn
    change ((1-boostParameter n*inverseDimension n)⁻¹*(inverseDimension n-boostParameter n)) • v+
      ((1-boostParameter n*inverseDimension n)⁻¹*boostScale n) • transverse v u = _
    rw [hc.1, hc.2]
    module


/-- The model latitude and transverse matching equations uniquely select the stated parameters. -/
theorem model_matching_parameters (b a t : ℝ) (hb : 0 < b) (hb2 : b ≤ 1/2) (hden : 1-a*b ≠ 0)
    (ha : (b-a)/(1-a*b) = b/(2+b)) (ht : 1-t*b = (1-b)*(1+b/2)) :
    a = b/(2-b) ∧ t = (1+b)/2 := by
  have hd : 2-b ≠ 0 := by linarith only [hb2]
  have hp : 2+b ≠ 0 := by linarith only [hb]
  have h1 : 1+b ≠ 0 := by linarith only [hb]
  have hclear := (div_eq_div_iff hden hp).mp ha
  have hprod : ((2-b)*a-b)*(1+b) = 0 := by linear_combination -hclear
  have he := (mul_eq_zero.mp hprod).resolve_right h1
  have htp : b*(t-(1+b)/2) = 0 := by nlinarith only [ht]
  refine ⟨(eq_div_iff hd).mpr ?_, ?_⟩
  · nlinarith only [he]
  · exact sub_eq_zero.mp ((mul_eq_zero.mp htp).resolve_left hb.ne')

end SharpCut.Certificate
