import SharpCut.Certificate.TransverseTilts

/-! # The positive contact Gram representation underlying low-dimensional coupling -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

def gramAxialScale (n : ℕ) : ℝ := (Real.sqrt (2*(2+inverseDimension n)))⁻¹
def gramTransverseScale (n : ℕ) : ℝ :=
  Real.sqrt ((1-inverseDimension n)*(2+inverseDimension n)/(2*(2-inverseDimension n)))

def gramWeight (F : JohnFrame n N) (v : V n) (i : Fin N) : ℝ :=
  F.weight i/(1-boostParameter n*height F v i)*(1+height F v i)

def gramVector (F : JohnFrame n N) (v : V n) (i : Fin N) : V n :=
  (gramAxialScale n*(height F v i-inverseDimension n)) • v+
    gramTransverseScale n • transverse v (F.contact i)

def contactGram (F : JohnFrame n N) (v : V n) : MatR n :=
  ∑ i, gramWeight F v i • outer (gramVector F v i)

def gramMixedMoment (F : JohnFrame n N) (v : V n) : V n :=
  ∑ i, (gramWeight F v i*(height F v i-inverseDimension n)) • transverse v (F.contact i)

theorem gramWeight_nonneg (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) (i : Fin N) : 0 ≤ gramWeight F v i := by
  have hlow : -1 ≤ height F v i := (F.heights_bounds v hv i).1
  exact mul_nonneg (div_pos (F.weight_pos i) (height_denominator_pos F hn v hv i)).le (by linarith)

theorem contactGram_posSemidef (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) : (contactGram F v).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun i hi => (Khachiyan.outer_posSemidef _).smul
    (gramWeight_nonneg F hn v hv i))

theorem gramScales_pos (hn : 2 ≤ n) : 0 < gramAxialScale n ∧ 0 < gramTransverseScale n := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hp : 0 < 2+inverseDimension n := by linarith [hb.1]
  dsimp [gramAxialScale, gramTransverseScale]
  constructor <;> positivity

theorem gramScales_squares (hn : 2 ≤ n) :
    (gramAxialScale n)^2 = 1/(2*(2+inverseDimension n)) ∧
      (gramTransverseScale n)^2 = (1-inverseDimension n)*(2+inverseDimension n)/
        (2*(2-inverseDimension n)) := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hp : 0 < 2+inverseDimension n := by linarith [hb.1]
  constructor
  · unfold gramAxialScale
    rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 2*(2+inverseDimension n)), one_div]
  · exact Real.sq_sqrt (by positivity)

theorem gramScales_product (hn : 2 ≤ n) :
    gramAxialScale n*gramTransverseScale n =
      (2-inverseDimension n)/4*(modelAxialScale n*modelTransverseScale n) := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have hp : 0 < 2+inverseDimension n := by linarith [hb.1]
  have hs : (gramAxialScale n*gramTransverseScale n)^2 =
      ((2-inverseDimension n)/4*(modelAxialScale n*modelTransverseScale n))^2 := by
    rw [mul_pow, (gramScales_squares hn).1, (gramScales_squares hn).2,
      mul_pow, div_pow, mul_pow, modelAxialScale_sq hn, modelTransverseScale_sq hn]
    field_simp [hd.ne', hp.ne'] <;> ring
  have hpos := gramScales_pos hn
  have hm := modelScales_pos hn
  have hr : 0 < (2-inverseDimension n)/4*(modelAxialScale n*modelTransverseScale n) :=
    mul_pos (div_pos hd (by norm_num)) (mul_pos hm.1 hm.2)
  nlinarith [mul_pos hpos.1 hpos.2]

theorem gramMixedMoment_expansion (F : JohnFrame n N) (v : V n) :
    gramMixedMoment F v = transverseVectorMoment F v 2+
      (1-inverseDimension n) • transverseVectorMoment F v 1-
        inverseDimension n • transverseVectorMoment F v 0 := by
  unfold gramMixedMoment transverseVectorMoment gramWeight
  simp only [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    smul_smul, ← add_smul, ← sub_smul, pow_zero, pow_one, mul_one]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

theorem weighted_transverse_action (F : JohnFrame n N) (v : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (projector v)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedShape F (contactScalarFactor F v)) v) =
        transverseVectorMoment F v 1-cutWeight n • transverseVectorMoment F v 2 := by
  rw [weightedShape_action]
  simp only [map_sum, map_smul, projector_action]
  unfold transverseVectorMoment
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, smul_smul, ← sub_smul, pow_one]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  unfold contactScalarFactor height
  ring

theorem gramMixedMoment_coupling (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    (gramAxialScale n*gramTransverseScale n) • gramMixedMoment F v = -transverseCoupling F v := by
  have hm := transverse_moments F hn v hv
  rw [gramScales_product hn, gramMixedMoment_expansion, hm.1, hm.2.1,
    transverseCoupling, weighted_transverse_action, hm.2.1]
  simp only [smul_add, smul_sub, smul_smul, ← add_smul, ← sub_smul, ← neg_smul]
  congr 1
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  unfold boostParameter cutWeight
  field_simp [hd] <;> ring

theorem transverseCoupling_explicit (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    transverseCoupling F v =
      (-Real.sqrt (1-inverseDimension n)/
        (inverseDimension n*Real.sqrt (2-inverseDimension n))) •
          (transverseVectorMoment F v 1-inverseDimension n • transverseVectorMoment F v 0) := by
  have hm := transverse_moments F hn v hv
  rw [transverseCoupling, weighted_transverse_action, hm.1, hm.2.1,
    modelScaleProduct_explicit hn]
  simp only [smul_sub, smul_smul, ← sub_smul]
  congr 1
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have hs : Real.sqrt (2-inverseDimension n) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  unfold boostParameter cutWeight
  field_simp [hb.1.ne', hd.ne', hs] <;> ring

theorem gram_axial_mass (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) :
    (∑ i, gramWeight F v i*(gramAxialScale n*(height F v i-inverseDimension n))^2) =
      axialDeficit F v := by
  rw [axialDeficit, frameDefect, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow, (gramScales_squares hn).1]
  unfold gramWeight defectTerm
  ring

theorem sum_axis_gram {ι : Type*} [Fintype ι] (v : V n) (y : ι → V n) (w a : ι → ℝ) (β : ℝ) :
    (∑ i, w i • outer (a i • v+β • y i)) =
      (∑ i, w i*(a i)^2) • outer v+
        cross v (∑ i, (w i*a i*β) • y i)+
        cross (∑ i, (w i*a i*β) • y i) v+
        β^2 • (∑ i, w i • outer (y i)) := by
  ext j k
  simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply, Khachiyan.outer_apply,
    cross, Matrix.vecMulVec_apply, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sum,
    Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem gram_mixed_mass (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (∑ i, (gramWeight F v i*(gramAxialScale n*(height F v i-inverseDimension n))*
      gramTransverseScale n) • transverse v (F.contact i)) = -transverseCoupling F v := by
  calc
    _ = (gramAxialScale n*gramTransverseScale n) • gramMixedMoment F v := by
      rw [gramMixedMoment, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul]
      congr 1
      ring
    _ = _ := gramMixedMoment_coupling F hn v hv

theorem gram_transverse_mass (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (gramTransverseScale n)^2 • transversePlusMoment F v =
      cutWeight n • projector v-transversePerturbation F v := by
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have h1 : 1-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hp : 2+inverseDimension n ≠ 0 := by linarith [hb.1]
  rw [(gramScales_squares hn).2, transversePlusMoment_identity F hn v hv, smul_smul]
  have hc : ((1-inverseDimension n)*(2+inverseDimension n)/(2*(2-inverseDimension n)))*
      (2*(2-inverseDimension n)/((1-inverseDimension n)*(2+inverseDimension n))) = 1 := by
    field_simp [hd, h1, hp]
  rw [hc, one_smul]

/-- The ambient form of the paper's positive axial/transverse block Gram matrix. -/
theorem contactGram_identity (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    contactGram F v = axialDeficit F v • outer v-
      cross v (transverseCoupling F v)-cross (transverseCoupling F v) v+
        (cutWeight n • projector v-transversePerturbation F v) := by
  unfold contactGram gramVector
  rw [sum_axis_gram, gram_axial_mass F hn v,
    gram_mixed_mass F hn v hv]
  change axialDeficit F v • outer v+cross v (-transverseCoupling F v)+
    cross (-transverseCoupling F v) v+(gramTransverseScale n)^2 • transversePlusMoment F v = _
  rw [gram_transverse_mass F hn v hv]
  have hright : cross v (-transverseCoupling F v) = -cross v (transverseCoupling F v) := by
    simpa only [neg_one_smul] using cross_smul_right (-1 : ℝ) v (transverseCoupling F v)
  have hleft : cross (-transverseCoupling F v) v = -cross (transverseCoupling F v) v := by
    simpa only [neg_one_smul] using cross_smul_left (-1 : ℝ) (transverseCoupling F v) v
  rw [hright, hleft]
  abel

end SharpCut.Certificate
