import SharpCut.Determinant.LiftedBlocks
import SharpCut.Determinant.LogGain
import SharpCut.Certificate.Normalization

/-! # The lifted determinant gain and its exact model normalization -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
open Certificate
set_option autoImplicit false
variable {n N : ℕ}

def frameLogSum (F : JohnFrame n N) (v : V n) : ℝ :=
  ∑ i, F.weight i*Real.log (contactScalarFactor F v i)

def modelLogSum (n : ℕ) : ℝ :=
  Real.log (heightFactor (inverseDimension n) (-1))/(1+inverseDimension n)+
    Real.log (heightFactor (inverseDimension n) (inverseDimension n))/
      (inverseDimension n*(1+inverseDimension n))

theorem dimension_inverseDimension (n : ℕ) : (n : ℝ) = 1/inverseDimension n := by
  simp [inverseDimension, one_div]

theorem model_log_average (hn : 2 ≤ n) :
    (1+inverseDimension n)*modelLogSum n =
      Real.log ((2-inverseDimension n)*(3+inverseDimension n)/4)+
        (n : ℝ)*Real.log ((2-inverseDimension n)/2) := by
  have hb := inverseDimension_bounds hn
  rw [modelLogSum, (heightFactor_endpoints _ hb.1 hb.2).1,
    (heightFactor_endpoints _ hb.1 hb.2).2, dimension_inverseDimension n]
  field_simp [hb.1.ne', show 1+inverseDimension n ≠ 0 by linarith [hb.1]]

theorem modelF0_det_explicit (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (modelF0 v).det = ((2-inverseDimension n)/2)^(n-1)*
      ((2-inverseDimension n)^2/(2*(1-inverseDimension n))) := by
  have hb := inverseDimension_bounds hn
  have hr : 0 < (2-inverseDimension n)/2 := by linarith [hb.2]
  have h1 : 1-inverseDimension n ≠ 0 := by linarith [hb.2]
  have he : modelF0 v = ((2-inverseDimension n)/2) • (1 : MatR n)+
      ((2-inverseDimension n)^2/(2*(1-inverseDimension n))-
        (2-inverseDimension n)/2) • outer v := by
    simp only [modelF0, projector, smul_sub, sub_smul]
    abel
  rw [he, det_axial_update (by omega) v hv _ _ hr.ne']
  ring

theorem model_log_determinant (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    Real.log (modelF0 v).det = (1+inverseDimension n)*modelLogSum n-
      Real.log (inverseDimension n)+
        Real.log ((modelAxial (inverseDimension n)+axialKappa (inverseDimension n))/
          (schurConstant (inverseDimension n)*modelAxial (inverseDimension n)-(cutWeight n)^2)) := by
  let b := inverseDimension n
  have hb := inverseDimension_bounds hn
  have hbp : 0 < b := hb.1
  have hd : 0 < 2-b := by dsimp [b]; linarith [hb.2]
  have h1 : 0 < 1-b := by dsimp [b]; linarith [hb.2]
  have h3 : 0 < 3+b := by dsimp [b]; linarith [hb.1]
  have hr : 0 < (2-b)/2 := by positivity
  have hp : 0 < (2-b)*(3+b)/4 := by positivity
  have hcoef : 0 < (2-b)^2/(2*(1-b)) := by positivity
  have hmodelden : 0 < schurConstant b*modelAxial b-((1+b)/2)^2 := by
    rw [model_schur_denominator b hb.1 hb.2]
    positivity
  have hnum : 0 < modelAxial b+axialKappa b := by
    rw [model_axial_plus_kappa b hb.2]
    positivity
  have hprod : ((2-b)/2)*((2-b)*(3+b)/4)*(4/((1-b)*(3+b))) =
      (2-b)^2/(2*(1-b)) := by
    field_simp [h1.ne', h3.ne']
  have hlratio : -Real.log b+Real.log ((modelAxial b+axialKappa b)/
      (schurConstant b*modelAxial b-((1+b)/2)^2)) =
        Real.log (4/((1-b)*(3+b))) := by
    rw [← Real.log_inv, ← Real.log_mul (inv_pos.mpr hb.1).ne'
      (div_pos hnum hmodelden).ne']
    congr 1
    change b⁻¹*((modelAxial b+axialKappa b)/
      (schurConstant b*modelAxial b-((1+b)/2)^2)) = _
    rw [← one_div b, ← mul_div_assoc, model_fraction_value b hb.1 hb.2]
  rw [modelF0_det_explicit hn v hv, model_log_average hn]
  change Real.log (((2-b)/2)^(n-1)*((2-b)^2/(2*(1-b)))) =
    Real.log ((2-b)*(3+b)/4)+(n : ℝ)*Real.log ((2-b)/2)-Real.log b+
      Real.log ((modelAxial b+axialKappa b)/(schurConstant b*modelAxial b-((1+b)/2)^2))
  rw [Real.log_mul (pow_pos hr _).ne' hcoef.ne', Real.log_pow, ← hprod,
    Real.log_mul (mul_pos hr hp).ne' (by positivity), Real.log_mul hr.ne' hp.ne',
    Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  linarith only [hlratio]

theorem schurConstant_dimension (n : ℕ) :
    schurConstant (inverseDimension n) = (n : ℝ)+boostParameter n*cutWeight n := by
  rw [schurConstant, ← dimension_inverseDimension n]
  rfl

theorem certificate_log_comparison (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    (1+inverseDimension n)*frameLogSum F v-Real.log (inverseDimension n)+
      Real.log ((axisMoment (weightedShape F (contactScalarFactor F v)) v+
        axialKappa (inverseDimension n))/
        (schurConstant (inverseDimension n)*axisMoment (weightedShape F (contactScalarFactor F v)) v-
          (cutWeight n)^2)) ≤ Real.log (certificateF F v).det := by
  let B := weightedShape F (contactScalarFactor F v)
  let b := inverseDimension n
  let κ := axialKappa b
  let H := schurConstant b
  let ρ := inverseAxisMoment B v
  let z := axisMoment B v
  let t := cutWeight n
  have hB : B.PosDef := contactShape_posDef F hn v hv
  have hb := inverseDimension_bounds hn
  have hbp : 0 < b := hb.1
  have hd2 : 0 < 2-b := by dsimp [b]; linarith [hb.2]
  have h1 : 0 < 1-b := by dsimp [b]; linarith [hb.2]
  have hH : 0 < H := by dsimp [H, schurConstant]; positivity
  have hκ : 0 < κ := by dsimp [κ]; rw [axialKappa_explicit b hb.2]; positivity
  have hz : 0 < z := axisMoment_pos B hB v hv
  have hρ : 0 < ρ := inverseAxisMoment_pos B hB v hv
  have hd : 0 < H-t^2*ρ := by
    dsimp [H, b, t, ρ]
    rw [schurConstant_dimension]
    exact contact_schur_positive F hn v hv
  have hcz : 1 ≤ ρ*z := by
    simpa only [mul_comm] using inverse_axis_cauchy B hB v hv
  obtain ⟨hdz, hratio⟩ := inverse_fraction_lower_bound H κ t z ρ hH hκ.le hz hcz hd
  have hlog := Real.log_le_log (div_pos (by linarith : 0 < z+κ) hdz) hratio
  have hnum : 0 < 1+κ*ρ := by positivity
  rw [Real.log_div (by linarith : z+κ ≠ 0) hdz.ne', Real.log_div hnum.ne' hd.ne'] at hlog
  have hdetF : (certificateF F v).det = B.det*(1+κ*ρ) :=
    det_posDef_rank_one B hB v κ
  have hdetA : (liftedMoment F (contactScalarFactor F v)).det = b*B.det*(H-t^2*ρ) := by
    dsimp [b, B, H, t, ρ]
    rw [schurConstant_dimension]
    exact lifted_contact_det F hn v hv
  have hlogF : Real.log (certificateF F v).det = Real.log B.det+Real.log (1+κ*ρ) := by
    rw [hdetF, Real.log_mul hB.det_pos.ne' hnum.ne']
  have hlogA : Real.log (liftedMoment F (contactScalarFactor F v)).det =
      Real.log b+Real.log B.det+Real.log (H-t^2*ρ) := by
    rw [hdetA, Real.log_mul (mul_pos hbp hB.det_pos).ne' hd.ne',
      Real.log_mul hbp.ne' hB.det_pos.ne']
  have hlift := lifted_logdet F hn _ (contactScalarFactor_pos F hn v hv)
  change (1+b)*frameLogSum F v ≤ _ at hlift
  rw [hlogA] at hlift
  change (1+b)*frameLogSum F v-Real.log b+Real.log ((z+κ)/(H*z-t^2)) ≤ _
  rw [Real.log_div (by linarith : z+κ ≠ 0) hdz.ne', hlogF]
  linarith only [hlift, hlog]

theorem contact_axial_log_gain (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    liftedGainCoefficient (inverseDimension n)*frameDefect F v ≤
      Real.log ((axisMoment (weightedShape F (contactScalarFactor F v)) v+axialKappa (inverseDimension n))/
        (schurConstant (inverseDimension n)*axisMoment (weightedShape F (contactScalarFactor F v)) v-(cutWeight n)^2))-
      Real.log ((modelAxial (inverseDimension n)+axialKappa (inverseDimension n))/
        (schurConstant (inverseDimension n)*modelAxial (inverseDimension n)-(cutWeight n)^2)) := by
  let b := inverseDimension n
  let B := weightedShape F (contactScalarFactor F v)
  let z := axisMoment B v
  let κ := axialKappa b
  let H := schurConstant b
  have hb := inverseDimension_bounds hn
  have hbp : 0 < b := hb.1
  have hd2 : 0 < 2-b := by dsimp [b]; linarith [hb.2]
  have h1 : 0 < 1-b := by dsimp [b]; linarith [hb.2]
  have hH : 0 < H := by dsimp [H, schurConstant]; positivity
  have hκ : 0 < κ := by dsimp [κ]; rw [axialKappa_explicit b hb.2]; positivity
  have hz : 0 < z := axisMoment_pos B (contactShape_posDef F hn v hv) v hv
  have hc : 0 ≤ frameDefect F v := frameDefect_nonneg F hn v hv
  have hdrop : 0 < axialDrop b := by dsimp [axialDrop]; positivity
  have hΔ : 0 ≤ axialDrop b*frameDefect F v := mul_nonneg hdrop.le hc
  have hmodel : modelAxial b = z+axialDrop b*frameDefect F v := by
    have he := axial_defect_identity F hn v hv
    rw [← contactShape_axial] at he
    change z = modelAxial b-axialDrop b*frameDefect F v at he
    linarith
  have hd : 0 < H*z-(cutWeight n)^2 := by
    have hsch := contact_schur_positive F hn v hv
    rw [← schurConstant_dimension] at hsch
    have hcz : 1 ≤ inverseAxisMoment B v*z := by
      simpa only [mul_comm] using
        (inverse_axis_cauchy B (contactShape_posDef F hn v hv) v hv)
    exact (inverse_fraction_lower_bound H κ (cutWeight n) z (inverseAxisMoment B v)
      hH hκ.le hz hcz hsch).1
  have h := log_fraction_gain H κ ((cutWeight n)^2) z (modelAxial b)
    (axialDrop b*frameDefect F v) hH hκ.le (sq_nonneg _) hz hΔ hmodel hd
  have he : (axialDrop b*frameDefect F v)*
      (H/(H*modelAxial b-(cutWeight n)^2)-1/(modelAxial b+κ)) =
      liftedGainCoefficient b*frameDefect F v := by
    calc
      _ = (axialDrop b*(H/(H*modelAxial b-(cutWeight n)^2)-1/(modelAxial b+κ)))*
          frameDefect F v := by ring
      _ = _ := by
        change (axialDrop b*(schurConstant b/
          (schurConstant b*modelAxial b-((1+b)/2)^2)-1/(modelAxial b+axialKappa b)))*
          frameDefect F v = _
        rw [gain_coefficient_identity b hb.1 hb.2]
  rw [he] at h
  exact h

theorem normalizedCertificate_log (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    Real.log (normalizedCertificate F v).det =
      Real.log (certificateF F v).det-Real.log (modelF0 v).det := by
  have h := normalizedCertificate_det_mul F hn v
  have hl := congrArg Real.log h
  rw [Real.log_mul (normalizedCertificate_posDef F hn v hv).det_pos.ne'
    (modelF0_posDef hn v).det_pos.ne'] at hl
  linarith only [hl]

/-- Lemma 8.2; the proof in fact also gives this gain for dimensions two and three. -/
theorem lifted_determinant_bound (F : JohnFrame n N) (hn : 4 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    (1+inverseDimension n)*(frameLogSum F v-modelLogSum n)+
      liftedGainCoefficient (inverseDimension n)*frameDefect F v ≤
        Real.log (normalizedCertificate F v).det := by
  have hn2 : 2 ≤ n := by omega
  have h1 := certificate_log_comparison F hn2 v hv
  have h2 := contact_axial_log_gain F hn2 v hv
  rw [normalizedCertificate_log F hn2 v hv, model_log_determinant hn2 v hv]
  nlinarith only [h1, h2]

end SharpCut.Determinant
