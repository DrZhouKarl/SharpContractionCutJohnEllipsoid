import SharpCut.Certificate.AxialMoment

/-! # The reverse contact defect and the sharp scalar range identity (8.45) -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace SharpCut.Certificate
variable {n N : ℕ}

def reverseDefectTerm (F : JohnFrame n N) (v : V n) (i : Fin N) : ℝ :=
  F.weight i*((1-height F v i)*(height F v i+inverseDimension n)^2)/
    (1-boostParameter n*height F v i)

def reverseDefect (F : JohnFrame n N) (v : V n) : ℝ := ∑ i, reverseDefectTerm F v i

theorem reverseDefect_nonneg (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) : 0 ≤ reverseDefect F v := by
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (mul_nonneg (F.weight_pos i).le
    (mul_nonneg (sub_nonneg.mpr (F.heights_bounds v hv i).2) (sq_nonneg _)))
      (height_denominator_pos F hn v hv i).le

theorem reverseDefect_expansion (F : JohnFrame n N) (v : V n) :
    reverseDefect F v = -reweightedMoment F v 3+
      (1-2*inverseDimension n)*reweightedMoment F v 2+
      (2*inverseDimension n-(inverseDimension n)^2)*reweightedMoment F v 1+
      (inverseDimension n)^2*reweightedMoment F v 0 := by
  unfold reverseDefect reverseDefectTerm reweightedMoment
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    pow_zero, pow_one, mul_one]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem reverse_identity_of_moments (b dim chi rev N0 N1 N2 N3 : ℝ)
    (h0 : (2-b)*N0-b*N1 = (2-b)*dim)
    (h1 : (2-b)*N1-b*N2 = 0)
    (h2 : (2-b)*N2-b*N3 = 2-b)
    (hc : chi = N3+(1-2*b)*N2+(b^2-2*b)*N1+b^2*N0)
    (hr : rev = -N3+(1-2*b)*N2+(2*b-b^2)*N1+b^2*N0)
    (hd : b*dim = 1) (hden : 2-b+b^2 ≠ 0) :
    chi+(1-b)*(2+b)^2/(2-b+b^2)^2*rev =
      (2-b)*(2+b)*(1-b)/(2-b+b^2) := by
  have hclear : (2-b+b^2)^2*chi+(1-b)*(2+b)^2*rev =
      (2-b)*(2+b)*(1-b)*(2-b+b^2) := by
    linear_combination ((2-b)*b^2*(b^2+b+2))*h0+
      (2*b^2*(1-b)*(2-b))*h1+(4-8*b+b^2-b^3)*h2+
      (2-b+b^2)^2*hc+(1-b)*(2+b)^2*hr+(2-b)^2*b*(b^2+b+2)*hd
  field_simp [hden]
  linear_combination hclear

theorem reverse_defect_identity (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    frameDefect F v+
      (1-inverseDimension n)*(2+inverseDimension n)^2/
        (2-inverseDimension n+(inverseDimension n)^2)^2*reverseDefect F v =
      (2-inverseDimension n)*(2+inverseDimension n)*(1-inverseDimension n)/
        (2-inverseDimension n+(inverseDimension n)^2) := by
  let b := inverseDimension n
  have hb := inverseDimension_bounds hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hdim : b*(n : ℝ) = 1 := by dsimp [b, inverseDimension]; field_simp [hn0]
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
  exact reverse_identity_of_moments b (n : ℝ) (frameDefect F v) (reverseDefect F v)
    (reweightedMoment F v 0) (reweightedMoment F v 1)
    (reweightedMoment F v 2) (reweightedMoment F v 3)
    h0 h1 h2 (defect_expansion F v) (reverseDefect_expansion F v) hdim
    (by nlinarith [hb.2, sq_nonneg b])

theorem frameDefect_range (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    0 ≤ frameDefect F v ∧
      frameDefect F v ≤ (2-inverseDimension n)*(2+inverseDimension n)*(1-inverseDimension n)/
        (2-inverseDimension n+(inverseDimension n)^2) ∧ frameDefect F v ≤ 2 := by
  have hb := inverseDimension_bounds hn
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have h2 : 0 < 2+inverseDimension n := by linarith [hb.1]
  have hd : 0 < 2-inverseDimension n+(inverseDimension n)^2 := by
    nlinarith [hb.2, sq_nonneg (inverseDimension n)]
  have he := reverse_defect_identity F hn v hv
  have hnrev := reverseDefect_nonneg F hn v hv
  have hp : 0 ≤ (1-inverseDimension n)*(2+inverseDimension n)^2/
      (2-inverseDimension n+(inverseDimension n)^2)^2*reverseDefect F v := by positivity
  have hbound : frameDefect F v ≤ (2-inverseDimension n)*(2+inverseDimension n)*(1-inverseDimension n)/
      (2-inverseDimension n+(inverseDimension n)^2) := by linarith only [he, hp]
  refine ⟨frameDefect_nonneg F hn v hv, hbound, hbound.trans ?_⟩
  apply (div_le_iff₀ hd).mpr
  have hpoly : 0 ≤ inverseDimension n*(2+3*inverseDimension n-(inverseDimension n)^2) := by
    have hh := mul_nonneg hb.1.le (show 0 ≤ 1/2-inverseDimension n from sub_nonneg.mpr hb.2)
    have hi : 0 ≤ 2+3*inverseDimension n-(inverseDimension n)^2 := by nlinarith
    exact mul_nonneg hb.1.le hi
  nlinarith only [hpoly]

end SharpCut.Certificate
