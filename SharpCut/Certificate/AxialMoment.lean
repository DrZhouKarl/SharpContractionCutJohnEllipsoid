import SharpCut.Certificate.ReweightedShape
import Mathlib.Tactic.LinearCombination

/-! # The exact axial defect identity (8.7), derived from John moments -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace SharpCut.Certificate

theorem axial_identity_of_moments (b dim chi N0 N1 N2 N3 : ℝ)
    (h0 : (2-b)*N0-b*N1 = (2-b)*dim)
    (h1 : (2-b)*N1-b*N2 = 0)
    (h2 : (2-b)*N2-b*N3 = 2-b)
    (hc : chi = N3+(1-2*b)*N2+(b^2-2*b)*N1+b^2*N0)
    (hd : b*dim = 1) (hb1 : 1-b ≠ 0) (hb2 : 2+b ≠ 0) :
    N2-(1+b)/2*N3 = 3*(2-b)/4-(2-b)^2/(4*(1-b)*(2+b))*chi := by
  have hclear : 4*(1-b)*(2+b)*(N2-(1+b)/2*N3)+(2-b)^2*chi =
      3*(2-b)*(1-b)*(2+b) := by
    linear_combination ((2-b)*b^2)*h0+(-4*b*(1-b))*h1+
      (6-5*b-2*b^2)*h2+(2-b)^2*hc+(2-b)^2*b*hd
  field_simp [hb1, hb2]
  nlinarith only [hclear]

theorem axial_defect_identity {n N : ℕ} (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n)
    (hv : ‖v‖ = 1) :
    reweightedMoment F v 2-cutWeight n*reweightedMoment F v 3 =
      3*(2-inverseDimension n)/4-
        (2-inverseDimension n)^2/(4*(1-inverseDimension n)*(2+inverseDimension n))*frameDefect F v := by
  let b := inverseDimension n
  have hb := inverseDimension_bounds hn
  have hdn : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hbdim : b*(n : ℝ) = 1 := by dsimp [b, inverseDimension]; field_simp [hdn]
  have ha : (2-b)*boostParameter n = b := by
    change (2-b)*(b/(2-b)) = b
    field_simp [show 2-b ≠ 0 by linarith [hb.2]]
  obtain ⟨hm0, hm1, hm2⟩ := reweighted_moments F hn v hv
  have h0 := congrArg (fun x : ℝ => (2-b)*x) hm0
  have h1 := congrArg (fun x : ℝ => (2-b)*x) hm1
  have h2 := congrArg (fun x : ℝ => (2-b)*x) hm2
  simp only [mul_sub, ← mul_assoc, ha] at h0
  simp only [mul_sub, ← mul_assoc, ha, mul_zero] at h1
  simp only [mul_sub, ← mul_assoc, ha, mul_one] at h2
  exact axial_identity_of_moments b (n : ℝ) (frameDefect F v)
    (reweightedMoment F v 0) (reweightedMoment F v 1)
    (reweightedMoment F v 2) (reweightedMoment F v 3)
    h0 h1 h2 (defect_expansion F v) hbdim
    (by linarith [hb.2]) (by linarith [hb.1])

theorem contactShape_axial {n N : ℕ} (F : JohnFrame n N) (v : V n) :
    ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedShape F (contactScalarFactor F v)) v⟫ =
      reweightedMoment F v 2-cutWeight n*reweightedMoment F v 3 := by
  rw [weightedShape_inner]
  unfold reweightedMoment contactScalarFactor
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change F.weight i*((1-cutWeight n*height F v i)/(1-boostParameter n*height F v i))*(height F v i)^2 = _
  ring

end SharpCut.Certificate
