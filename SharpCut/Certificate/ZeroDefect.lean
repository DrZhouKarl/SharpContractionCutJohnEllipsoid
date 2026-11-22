import SharpCut.Certificate.DirectCoupling

/-! # Exact zero endpoints of the transverse defect -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

theorem transverseSigma_zero_iff (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) :
    transverseSigma F v = 0 ↔ frameDefect F v = 0 := by
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hp : 2+inverseDimension n ≠ 0 := by linarith [hb.1]
  unfold transverseSigma
  simp only [div_eq_zero_iff, mul_eq_zero, show (2 : ℝ) ≠ 0 by norm_num,
    hd, hp, false_or, or_false]

theorem zero_defect_contact_terms (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hχ : frameDefect F v = 0) (i : Fin N) :
    (F.weight i/(1-boostParameter n*height F v i)*(height F v i-inverseDimension n)) •
      transverse v (F.contact i) = 0 ∧
    (F.weight i/(1-boostParameter n*height F v i)*(height F v i-inverseDimension n)) •
      outer (transverse v (F.contact i)) = 0 := by
  have hs := (frameDefect_zero_iff F hn v hv).mp hχ i
  rcases hs with hs | hs
  · have hy : transverse v (F.contact i) = 0 := by
      have he := transverse_norm_sq v (F.contact i) hv (F.contact_unit i)
      change ‖transverse v (F.contact i)‖^2 = 1-(height F v i)^2 at he
      rw [hs] at he
      norm_num at he
      exact he
    rw [hy, smul_zero]
    have ho : outer (0 : V n) = 0 := by
      ext j k
      simp only [Khachiyan.outer_apply, WithLp.ofLp_zero, Pi.zero_apply, zero_mul, Matrix.zero_apply]
    rw [ho, smul_zero]
    exact ⟨rfl, rfl⟩
  · rw [hs, sub_self, mul_zero, zero_smul, zero_smul]
    exact ⟨rfl, rfl⟩

theorem zero_defect_transverse_blocks (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hχ : frameDefect F v = 0) : transversePerturbation F v = 0 ∧ transverseCoupling F v = 0 := by
  constructor
  · rw [transversePerturbation_explicit]
    have he : (∑ i, (F.weight i/(1-boostParameter n*height F v i)*(height F v i-inverseDimension n)) •
      outer (transverse v (F.contact i))) = 0 :=
        Finset.sum_eq_zero (fun i hi => (zero_defect_contact_terms F hn v hv hχ i).2)
    rw [he, smul_zero]
  · rw [transverseCoupling_contact_sum F hn v hv]
    have he : (∑ i, (F.weight i/(1-boostParameter n*height F v i)*(height F v i-inverseDimension n)) •
      transverse v (F.contact i)) = 0 :=
        Finset.sum_eq_zero (fun i hi => (zero_defect_contact_terms F hn v hv hχ i).1)
    rw [he, smul_zero]

theorem zero_sigma_transverse_blocks (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (hσ : transverseSigma F v = 0) : transversePerturbation F v = 0 ∧ transverseCoupling F v = 0 :=
  zero_defect_transverse_blocks F hn v hv ((transverseSigma_zero_iff F hn v).mp hσ)

end SharpCut.Certificate
