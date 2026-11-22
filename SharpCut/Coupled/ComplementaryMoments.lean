import SharpCut.Coupled.Coordinates

/-! # Actual complementary contact moments and endpoint coefficients -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Coupled
open Certificate
variable {n N : ℕ}

def endpointShift (n : ℕ) : ℝ := 2*inverseDimension n/(2-inverseDimension n+(inverseDimension n)^2)
def complementaryScale (n : ℕ) : ℝ := (1-boostParameter n*inverseDimension n)/(2-inverseDimension n+(inverseDimension n)^2)
def complementaryGamma (n : ℕ) : ℝ := Real.sqrt (2-inverseDimension n)/(Real.sqrt (1-inverseDimension n)*(2+inverseDimension n))
def plusContactWeight (F : JohnFrame n N) (v : V n) (i : Fin N) : ℝ :=
  F.weight i/(1-boostParameter n*height F v i)*(1+height F v i)
def plusEndpointMoment (F : JohnFrame n N) (v : V n) : MatR n :=
  ∑ i, (F.weight i/(1-boostParameter n*height F v i)*(height F v i+inverseDimension n)) • outer (transverse v (F.contact i))
def plusMixedMoment (F : JohnFrame n N) (v : V n) : V n :=
  ∑ i, (plusContactWeight F v i*(height F v i-inverseDimension n)) • transverse v (F.contact i)

theorem plusContactWeight_nonneg (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (i : Fin N) :
    0 ≤ plusContactWeight F v i := by
  have hs : 0 ≤ 1+height F v i := by
    have hlo : -1 ≤ height F v i := (F.heights_bounds v hv i).1
    linarith only [hlo]
  exact mul_nonneg (div_pos (F.weight_pos i) (height_denominator_pos F hn v hv i)).le hs

theorem complementaryScale_explicit (hn : 2 ≤ n) :
    complementaryScale n = (1-inverseDimension n)*(2+inverseDimension n)/
      ((2-inverseDimension n)*(2-inverseDimension n+(inverseDimension n)^2)) := by
  have hd : 2-inverseDimension n ≠ 0 := by linarith [(inverseDimension_bounds hn).2]
  have hh : 2-inverseDimension n+(inverseDimension n)^2 ≠ 0 := by nlinarith [(inverseDimension_bounds hn).2, sq_nonneg (inverseDimension n)]
  unfold complementaryScale boostParameter
  field_simp [hd, hh] <;> ring

theorem complementary_gamma_relation (hn : 2 ≤ n) :
    complementaryScale n*complementaryGamma n = couplingGamma n/(2-inverseDimension n) := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hh : 0 < 2-inverseDimension n+(inverseDimension n)^2 := by positivity
  have hplus : 0 < 2+inverseDimension n := by linarith [hb.1]
  have hroot : Real.sqrt (1-inverseDimension n) ≠ 0 := (Real.sqrt_pos.mpr h1).ne'
  calc
    _ = ((1-inverseDimension n)/Real.sqrt (1-inverseDimension n))*Real.sqrt (2-inverseDimension n)/
        ((2-inverseDimension n)*(2-inverseDimension n+(inverseDimension n)^2)) := by
      rw [complementaryScale_explicit hn]
      unfold complementaryGamma
      field_simp [hd.ne', hh.ne', hplus.ne', hroot] <;> ring
    _ = _ := by
      rw [Real.div_sqrt]
      unfold couplingGamma
      field_simp [hd.ne', hh.ne'] <;> ring

theorem plusEndpointMoment_expansion (F : JohnFrame n N) (v : V n) :
    plusEndpointMoment F v = transverseMatrixMoment F v 1+inverseDimension n • transverseMatrixMoment F v 0 := by
  unfold plusEndpointMoment transverseMatrixMoment
  simp only [pow_one, pow_zero, mul_one, Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul, ← add_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

/-- The matrix term in the exact complementary linear contact identity (10.16). -/
theorem complementary_matrix_moment (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    complementaryScale n • plusEndpointMoment F v = endpointShift n • projector v-transversePerturbation F v := by
  have hm := (transverse_moments F hn v hv).2.2
  rw [plusEndpointMoment_expansion, ← hm, transversePerturbation]
  ext i j
  simp only [smul_add, smul_sub, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  have hd : 2-inverseDimension n ≠ 0 := by linarith [(inverseDimension_bounds hn).2]
  have hh : 2-inverseDimension n+(inverseDimension n)^2 ≠ 0 := by nlinarith [(inverseDimension_bounds hn).2, sq_nonneg (inverseDimension n)]
  unfold complementaryScale endpointShift boostParameter
  field_simp [hd, hh] <;> ring

theorem plusMixedMoment_expansion (F : JohnFrame n N) (v : V n) :
    plusMixedMoment F v = transverseVectorMoment F v 2+(1-inverseDimension n) • transverseVectorMoment F v 1-
      inverseDimension n • transverseVectorMoment F v 0 := by
  unfold plusMixedMoment plusContactWeight transverseVectorMoment
  simp only [pow_one, pow_zero, mul_one, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    smul_smul, ← add_smul, ← sub_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

/-- The complementary mixed contact sum is a fixed multiple of the shared difference-square moment. -/
theorem plusMixedMoment_difference (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    plusMixedMoment F v = (2/(2-inverseDimension n+(inverseDimension n)^2)) • differenceSquareMoment F v := by
  have hm := transverse_moments F hn v hv
  have hd : 2-inverseDimension n ≠ 0 := by linarith [(inverseDimension_bounds hn).2]
  have hh : 2-inverseDimension n+(inverseDimension n)^2 ≠ 0 := by nlinarith [(inverseDimension_bounds hn).2, sq_nonneg (inverseDimension n)]
  have he : 1+(1-inverseDimension n)*boostParameter n-inverseDimension n*(boostParameter n)^2 =
      (2/(2-inverseDimension n+(inverseDimension n)^2))*(1-(inverseDimension n)^2*(boostParameter n)^2) := by
    unfold boostParameter
    field_simp [hd, hh] <;> ring
  rw [plusMixedMoment_expansion, differenceSquareMoment_expansion, hm.1, hm.2.1]
  simp only [smul_smul]
  calc
    _ = (1+(1-inverseDimension n)*boostParameter n-inverseDimension n*(boostParameter n)^2) • transverseVectorMoment F v 2 := by module
    _ = _ := by rw [he]; module


def complementaryFactor (n : ℕ) : ℝ := 2*(2-inverseDimension n)/((1-inverseDimension n)*(2+inverseDimension n))

theorem complementary_factor_scale (hn : 2 ≤ n) :
    complementaryFactor n*complementaryScale n = 2/(2-inverseDimension n+(inverseDimension n)^2) := by
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have h1 : 1-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hp : 2+inverseDimension n ≠ 0 := by linarith [hb.1]
  have hh : 2-inverseDimension n+(inverseDimension n)^2 ≠ 0 := by nlinarith [hb.2, sq_nonneg (inverseDimension n)]
  rw [complementaryScale_explicit hn]
  unfold complementaryFactor
  field_simp [hd, h1, hp, hh] <;> ring

theorem complementary_mixed_moment (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (-complementaryGamma n) • plusMixedMoment F v = complementaryFactor n • transverseCoupling F v := by
  have hbase := gamma_difference_identity F hn v hv
  have hc := congrArg (fun u : V n => (-complementaryFactor n) • u) hbase
  rw [plusMixedMoment_difference F hn v hv, ← complementary_factor_scale hn, smul_smul]
  rw [smul_smul] at hc
  have he : -complementaryGamma n*(complementaryFactor n*complementaryScale n) =
      -complementaryFactor n*(couplingGamma n/(2-inverseDimension n)) := by
    rw [← complementary_gamma_relation hn]
    ring
  rw [he]
  simpa only [smul_neg, neg_smul, neg_neg] using hc

theorem complementaryGamma_square (hn : 2 ≤ n) :
    (complementaryGamma n)^2 = (2-inverseDimension n)/((1-inverseDimension n)*(2+inverseDimension n)^2) := by
  have hb := inverseDimension_bounds hn
  unfold complementaryGamma
  rw [div_pow, mul_pow, Real.sq_sqrt (by linarith [hb.2] : 0 ≤ 2-inverseDimension n),
    Real.sq_sqrt (by linarith [hb.2] : 0 ≤ 1-inverseDimension n)]

theorem complementary_sigma_coefficient (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) :
    (complementaryGamma n)^2*frameDefect F v =
      complementaryFactor n*((2-inverseDimension n)/4*transverseSigma F v) := by
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have h1 : 1-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hp : 2+inverseDimension n ≠ 0 := by linarith [hb.1]
  rw [complementaryGamma_square hn]
  unfold complementaryFactor transverseSigma
  field_simp [hd, h1, hp] <;> ring

/-- The first complementary prefactor in (10.18), including both trace endpoints. -/
theorem complementary_reverse_coefficient (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (complementaryScale n)^2*reverseDefect F v = traceRemainder F v/complementaryFactor n := by
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have h1 : 1-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hp : 2+inverseDimension n ≠ 0 := by linarith [hb.1]
  have hh : 2-inverseDimension n+(inverseDimension n)^2 ≠ 0 := by nlinarith [hb.2, sq_nonneg (inverseDimension n)]
  have hg := general_reverse_contact_identity F hn v hv
  rw [couplingGamma_sq hn] at hg
  have hr := congrArg (fun x : ℝ => (1-inverseDimension n)*(2+inverseDimension n)^2/(2-inverseDimension n)^3*x) hg
  rw [complementaryScale_explicit hn]
  unfold complementaryFactor
  convert hr using 1 <;> field_simp [hd, h1, hp, hh] <;> ring

end SharpCut.Coupled
