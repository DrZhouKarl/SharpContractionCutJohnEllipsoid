import SharpCut.Scalar.HermiteLoss
import SharpCut.Determinant.LiftedBound

/-! # John weighted Hermite interpolation and Lemma 8.3 -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
open Certificate
variable {n N : ℕ}

theorem john_hermite_average (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n)
    (hv : ‖v‖ = 1) (pole latitude slope : ℝ) :
    (∑ i, F.weight i*Scalar.hermiteQuadratic (inverseDimension n) pole latitude slope (height F v i)) =
      pole/(1+inverseDimension n)+latitude/(inverseDimension n*(1+inverseDimension n)) := by
  let b := inverseDimension n
  let c := (pole-latitude+(1+b)*slope)/(1+b)^2
  have hb := inverseDimension_bounds hn
  have hninv : (n : ℝ) = 1/b := dimension_inverseDimension n
  have hlin : (∑ i, F.weight i*(height F v i-b)) = -b*(n : ℝ) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, height,
      F.scalar_first_moment, F.weight_sum, zero_sub]
    ring
  have hquad : (∑ i, F.weight i*(height F v i-b)^2) = 1+b^2*(n : ℝ) := by
    calc
      _ = (∑ i, F.weight i*(height F v i)^2)-
          2*b*(∑ i, F.weight i*height F v i)+b^2*(∑ i, F.weight i) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i hi; ring
      _ = _ := by
        simp only [Certificate.height, F.scalar_first_moment, F.scalar_second_moment, F.weight_sum, hv]
        ring
  have he : (∑ i, F.weight i*Scalar.hermiteQuadratic b pole latitude slope (height F v i)) =
      latitude*(∑ i, F.weight i)+slope*(∑ i, F.weight i*(height F v i-b))+
        c*(∑ i, F.weight i*(height F v i-b)^2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [Scalar.hermiteQuadratic, c]
    ring
  rw [he, F.weight_sum, hlin, hquad, hninv]
  change latitude*(1/b)+slope*(-b*(1/b))+c*(1+b^2*(1/b)) =
    pole/(1+b)+latitude/(b*(1+b))
  have hb0 : b ≠ 0 := hb.1.ne'
  have hb1 : 1+b ≠ 0 := by linarith [hb.1]
  dsimp [c]
  field_simp [hb0, hb1] <;> ring

theorem logarithmicHermite_average (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    (∑ i, F.weight i*Scalar.logarithmicHermite (inverseDimension n) (height F v i)) =
      modelLogSum n := john_hermite_average F hn v hv _ _ _

/-- Lemma 8.3, with the original a..t loss integral. -/
theorem interpolation_loss (F : JohnFrame n N) (hn : 4 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    -(1-boostParameter n)*
      (∫ z in boostParameter n..cutWeight n, Scalar.originalIntegrand (inverseDimension n) z)*
        frameDefect F v ≤ frameLogSum F v-modelLogSum n := by
  have hn2 : 2 ≤ n := by omega
  have hb := inverseDimension_bounds hn2
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hbq : inverseDimension n ≤ 1/4 := one_div_le_one_div_of_le (by norm_num) hnreal
  have hp (i : Fin N) := mul_le_mul_of_nonneg_left
    (Scalar.logarithmic_hermite_loss hb.1 hbq
      (F.heights_bounds v hv i).1 (F.heights_bounds v hv i).2) (F.weight_pos i).le
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i)
  have hleft : (∑ i, F.weight i*
      (-(1-Scalar.scalarA (inverseDimension n))*
        (∫ z in Scalar.scalarA (inverseDimension n)..Scalar.scalarT (inverseDimension n),
          Scalar.originalIntegrand (inverseDimension n) z)*
        ((1+height F v i)*(height F v i-inverseDimension n)^2)/
          (1-Scalar.scalarA (inverseDimension n)*height F v i))) =
        -(1-boostParameter n)*
          (∫ z in boostParameter n..cutWeight n, Scalar.originalIntegrand (inverseDimension n) z)*
            frameDefect F v := by
    rw [frameDefect, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [Scalar.scalarA, Scalar.scalarT, boostParameter, cutWeight, defectTerm]
    ring
  have hright : (∑ i, F.weight i*
      (Real.log (heightFactor (inverseDimension n) (height F v i))-
        Scalar.logarithmicHermite (inverseDimension n) (height F v i))) =
      frameLogSum F v-modelLogSum n := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [logarithmicHermite_average F hn2 v hv]
    rfl
  simp only [Certificate.height] at hleft hright
  rw [hleft, hright] at h
  exact h

end SharpCut.Determinant
