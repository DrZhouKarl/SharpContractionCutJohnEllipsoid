import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Exact positive logarithmic gain from an axial deficit -/

noncomputable section
namespace SharpCut.Determinant

theorem inverse_fraction_lower_bound (H κ t z ρ : ℝ)
    (hH : 0 < H) (hκ : 0 ≤ κ) (hz : 0 < z) (hρz : 1 ≤ ρ*z)
    (hd : 0 < H-t^2*ρ) :
    0 < H*z-t^2 ∧ (z+κ)/(H*z-t^2) ≤ (1+κ*ρ)/(H-t^2*ρ) := by
  have hd2 : 0 < H*z-t^2 := by
    have hp := mul_pos hd hz
    have hh := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hρz)
    nlinarith
  refine ⟨hd2, (div_le_div_iff₀ hd2 hd).mpr ?_⟩
  have hh := mul_nonneg (show 0 ≤ H*κ+t^2 by positivity) (sub_nonneg.mpr hρz)
  nlinarith only [hh]

def modelAxial (b : ℝ) : ℝ := 3*(2-b)/4
def axialDrop (b : ℝ) : ℝ := (2-b)^2/(4*(1-b)*(2+b))
def axialKappa (b : ℝ) : ℝ := ((1+b)/2)/(1-b/(2-b))
def schurConstant (b : ℝ) : ℝ := 1/b+(b/(2-b))*((1+b)/2)
def liftedGainCoefficient (b : ℝ) : ℝ :=
  (1+b)*(b^2+b+2)/(2*(2-b)*(1-b)*(2+b)*(3+b))

theorem axialKappa_explicit (b : ℝ) (hb : b ≤ 1/2) :
    axialKappa b = (1+b)*(2-b)/(4*(1-b)) := by
  have hd : 2-b ≠ 0 := by linarith
  have h1 : 1-b ≠ 0 := by linarith
  have ha : 1-b/(2-b) = 2*(1-b)/(2-b) := by field_simp [hd]; ring
  unfold axialKappa
  rw [ha]
  field_simp [hd, h1]
  ring

theorem model_axial_plus_kappa (b : ℝ) (hb : b ≤ 1/2) :
    modelAxial b+axialKappa b = (2-b)^2/(2*(1-b)) := by
  have hd : 2-b ≠ 0 := by linarith
  have h1 : 1-b ≠ 0 := by linarith
  rw [axialKappa_explicit b hb]
  unfold modelAxial
  field_simp [hd, h1]
  ring

theorem model_schur_denominator (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 1/2) :
    schurConstant b*modelAxial b-((1+b)/2)^2 = (2-b)^2*(3+b)/(8*b) := by
  have hd : 2-b ≠ 0 := by linarith
  unfold schurConstant modelAxial
  field_simp [hb.ne', hd]
  ring

theorem gain_coefficient_identity (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 1/2) :
    axialDrop b*(schurConstant b/
      (schurConstant b*modelAxial b-((1+b)/2)^2)-1/(modelAxial b+axialKappa b)) =
        liftedGainCoefficient b := by
  rw [model_axial_plus_kappa b hb2, model_schur_denominator b hb hb2]
  have hd : 2-b ≠ 0 := by linarith
  have h1 : 1-b ≠ 0 := by linarith
  have h2 : 2+b ≠ 0 := by linarith
  have h3 : 3+b ≠ 0 := by linarith
  unfold axialDrop schurConstant liftedGainCoefficient
  field_simp [hb.ne', hd, h1, h2, h3]
  ring

theorem model_fraction_value (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 1/2) :
    (1/b)*(modelAxial b+axialKappa b)/
      (schurConstant b*modelAxial b-((1+b)/2)^2) = 4/((1-b)*(3+b)) := by
  rw [model_axial_plus_kappa b hb2, model_schur_denominator b hb hb2]
  have hd : 2-b ≠ 0 := by linarith
  have h1 : 1-b ≠ 0 := by linarith
  have h3 : 3+b ≠ 0 := by linarith
  field_simp [hb.ne', hd, h1, h3]
  ring

def heightFactor (b s : ℝ) : ℝ := (1-((1+b)/2)*s)/(1-(b/(2-b))*s)

theorem heightFactor_endpoints (b : ℝ) (hbpos : 0 < b) (hb : b ≤ 1/2) :
    heightFactor b (-1) = (2-b)*(3+b)/4 ∧ heightFactor b b = (2-b)/2 := by
  have hd : 2-b ≠ 0 := by linarith
  have h1 : 1-b ≠ 0 := by linarith
  have h2 : 2+b ≠ 0 := by linarith
  have hpole : 1-(b/(2-b))*(-1) = 2/(2-b) := by field_simp [hd]; ring
  have hlat : 1-(b/(2-b))*b = (1-b)*(2+b)/(2-b) := by field_simp [hd]; ring
  constructor
  · unfold heightFactor
    rw [hpole]
    field_simp [hd]
    ring
  · unfold heightFactor
    rw [hlat]
    field_simp [hd, h1, h2]
    ring

/-- The manuscript's theta estimate, expressed without auxiliary theta variables. -/
theorem log_fraction_gain (H κ τ z z0 Δ : ℝ)
    (hH : 0 < H) (hκ : 0 ≤ κ) (hτ : 0 ≤ τ) (hz : 0 < z)
    (hΔ : 0 ≤ Δ) (hz0 : z0 = z+Δ) (hd : 0 < H*z-τ) :
    Δ*(H/(H*z0-τ)-1/(z0+κ)) ≤
      Real.log ((z+κ)/(H*z-τ))-Real.log ((z0+κ)/(H*z0-τ)) := by
  have hzκ : 0 < z+κ := by linarith
  have hz0κ : 0 < z0+κ := by linarith
  have hd0 : 0 < H*z0-τ := by nlinarith
  have hN : 0 ≤ Δ*(H*κ+τ) := mul_nonneg hΔ (by positivity)
  have hden : (z+κ)*(H*z0-τ) ≤ (H*z0-τ)*(z0+κ) := by
    nlinarith
  have hc : H/(H*z0-τ)-1/(z0+κ) =
      (H*κ+τ)/((H*z0-τ)*(z0+κ)) := by
    field_simp [hd0.ne', hz0κ.ne']
    ring
  have he : 1-((z+κ)*(H*z0-τ)/((H*z-τ)*(z0+κ)))⁻¹ =
      Δ*(H*κ+τ)/((z+κ)*(H*z0-τ)) := by
    rw [inv_div]
    field_simp [hzκ.ne', hd0.ne']
    rw [hz0]
    ring
  have hlog : Real.log ((z+κ)*(H*z0-τ)/((H*z-τ)*(z0+κ))) =
      Real.log ((z+κ)/(H*z-τ))-Real.log ((z0+κ)/(H*z0-τ)) := by
    rw [Real.log_div (mul_pos hzκ hd0).ne' (mul_pos hd hz0κ).ne',
      Real.log_mul hzκ.ne' hd0.ne', Real.log_mul hd.ne' hz0κ.ne',
      Real.log_div hzκ.ne' hd.ne', Real.log_div hz0κ.ne' hd0.ne']
    ring
  calc
    _ = Δ*(H*κ+τ)/((H*z0-τ)*(z0+κ)) := by rw [hc, mul_div_assoc]
    _ ≤ Δ*(H*κ+τ)/((z+κ)*(H*z0-τ)) :=
      div_le_div_of_nonneg_left hN (mul_pos hzκ hd0) hden
    _ = 1-((z+κ)*(H*z0-τ)/((H*z-τ)*(z0+κ)))⁻¹ := he.symm
    _ ≤ _ := Real.one_sub_inv_le_log_of_pos
      (div_pos (mul_pos hzκ hd0) (mul_pos hd hz0κ))
    _ = _ := hlog

end SharpCut.Determinant
