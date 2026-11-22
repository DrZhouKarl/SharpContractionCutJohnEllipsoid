import SharpCut.Certificate.CouplingFoundation

/-! # Exact gamma-weighted moments in the direct coupling certificate -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

def minusContactWeight (F : JohnFrame n N) (v : V n) (i : Fin N) : ℝ :=
  F.weight i/(1-boostParameter n*height F v i)*(1-height F v i)

def minusMixedMoment (F : JohnFrame n N) (v : V n) : V n :=
  ∑ i, (minusContactWeight F v i*(height F v i+inverseDimension n)) • transverse v (F.contact i)

def differenceSquareMoment (F : JohnFrame n N) (v : V n) : V n :=
  ∑ i, (F.weight i/(1-boostParameter n*height F v i)*
    ((height F v i)^2-(inverseDimension n)^2)) • transverse v (F.contact i)

theorem minusContactWeight_nonneg (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) (i : Fin N) : 0 ≤ minusContactWeight F v i :=
  mul_nonneg (div_pos (F.weight_pos i) (height_denominator_pos F hn v hv i)).le
    (sub_nonneg.mpr (F.heights_bounds v hv i).2)

theorem couplingGamma_explicit (hn : 2 ≤ n) :
    couplingGamma n = Real.sqrt ((2-inverseDimension n)*(1-inverseDimension n))/
      (2-inverseDimension n+(inverseDimension n)^2) := by
  have hb := inverseDimension_bounds hn
  rw [Real.sqrt_mul (by linarith [hb.2] : 0 ≤ 2-inverseDimension n)]
  rfl

theorem couplingGamma_as_scales (hn : 2 ≤ n) :
    couplingGamma n = (2-inverseDimension n)^2/
      (2*(2-inverseDimension n+(inverseDimension n)^2))*(modelAxialScale n*modelTransverseScale n) := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have hg : 0 < 2-inverseDimension n+(inverseDimension n)^2 := by nlinarith [sq_nonneg (inverseDimension n)]
  have hs : Real.sqrt (2-inverseDimension n) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  calc
    _ = ((2-inverseDimension n)/Real.sqrt (2-inverseDimension n))*
        (Real.sqrt (1-inverseDimension n)/(2-inverseDimension n+(inverseDimension n)^2)) := by
      rw [Real.div_sqrt]; unfold couplingGamma; ring
    _ = _ := by
      rw [modelScaleProduct_explicit hn]
      field_simp [hd.ne', hg.ne', hs] <;> ring

theorem minusMixedMoment_expansion (F : JohnFrame n N) (v : V n) :
    minusMixedMoment F v = -transverseVectorMoment F v 2+
      (1-inverseDimension n) • transverseVectorMoment F v 1+
        inverseDimension n • transverseVectorMoment F v 0 := by
  unfold minusMixedMoment minusContactWeight transverseVectorMoment
  simp only [Finset.smul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    smul_smul, ← add_smul, ← neg_smul, pow_one, pow_zero, mul_one]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

theorem differenceSquareMoment_expansion (F : JohnFrame n N) (v : V n) :
    differenceSquareMoment F v = transverseVectorMoment F v 2-
      (inverseDimension n)^2 • transverseVectorMoment F v 0 := by
  unfold differenceSquareMoment transverseVectorMoment
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, smul_smul, ← sub_smul,
    pow_zero, mul_one]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

theorem gamma_mixed_identity (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    couplingGamma n • minusMixedMoment F v =
      (2*(2-inverseDimension n)/(2+inverseDimension n)) • transverseCoupling F v := by
  have hm := transverse_moments F hn v hv
  rw [couplingGamma_as_scales hn, minusMixedMoment_expansion, hm.1, hm.2.1,
    transverseCoupling, weighted_transverse_action, hm.2.1]
  simp only [smul_add, smul_sub, smul_neg, smul_smul, ← add_smul, ← sub_smul, ← neg_smul]
  congr 1
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hp : 2+inverseDimension n ≠ 0 := by linarith [hb.1]
  have hg : 2-inverseDimension n+(inverseDimension n)^2 ≠ 0 := by nlinarith [sq_nonneg (inverseDimension n), hb.2]
  unfold boostParameter cutWeight
  field_simp [hd, hp, hg] <;> ring

theorem gamma_difference_identity (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (couplingGamma n/(2-inverseDimension n)) • differenceSquareMoment F v = -transverseCoupling F v := by
  have hm := transverse_moments F hn v hv
  rw [couplingGamma_as_scales hn, differenceSquareMoment_expansion, hm.1, hm.2.1,
    transverseCoupling, weighted_transverse_action, hm.2.1]
  simp only [smul_sub, smul_smul, ← sub_smul, ← neg_smul]
  congr 1
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hg : 2-inverseDimension n+(inverseDimension n)^2 ≠ 0 := by nlinarith [sq_nonneg (inverseDimension n), hb.2]
  unfold boostParameter cutWeight
  field_simp [hd, hg] <;> ring

theorem gamma_reverse_identity (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (couplingGamma n)^2*reverseDefect F v =
      (2-inverseDimension n)/(2+inverseDimension n)*couplingL F v := by
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hp : 2+inverseDimension n ≠ 0 := by linarith [hb.1]
  have hg : 2-inverseDimension n+(inverseDimension n)^2 ≠ 0 := by nlinarith [sq_nonneg (inverseDimension n), hb.2]
  have hr := reverse_defect_identity F hn v hv
  have hr' : (1-inverseDimension n)*(2+inverseDimension n)^2/
      (2-inverseDimension n+(inverseDimension n)^2)^2*reverseDefect F v =
        (2-inverseDimension n)*(2+inverseDimension n)*(1-inverseDimension n)/
          (2-inverseDimension n+(inverseDimension n)^2)-frameDefect F v := by linarith only [hr]
  rw [couplingGamma_sq hn]
  calc
    _ = ((2-inverseDimension n)/(2+inverseDimension n)^2)*
        ((1-inverseDimension n)*(2+inverseDimension n)^2/
          (2-inverseDimension n+(inverseDimension n)^2)^2*reverseDefect F v) := by
      field_simp [hd, hp, hg] <;> ring
    _ = _ := by
      rw [hr']
      unfold couplingL transverseSigma
      field_simp [hd, hp, hg] <;> ring

end SharpCut.Certificate
