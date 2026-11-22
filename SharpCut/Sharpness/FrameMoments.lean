import SharpCut.Sharpness.ContactConstruction

/-! # All defining John identities of the pole-and-latitude witness -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Sharpness
variable {m : ℕ}

theorem dimension_balance (m : ℕ) :
    (m : ℝ)*inverseDimension (m+1) = 1-inverseDimension (m+1) := by
  have hp : 0 < (m : ℝ)+1 := by positivity
  unfold inverseDimension
  rw [Nat.cast_add, Nat.cast_one]
  field_simp [hp.ne'] <;> ring

theorem moment_coefficients (hm : 1 ≤ m) :
    (m : ℝ)*(2*(1/(2*(1-(inverseDimension (m+1))^2)))*inverseDimension (m+1)) =
      1/(1+inverseDimension (m+1)) ∧
    1/(1+inverseDimension (m+1))+
      (m : ℝ)*(2*(1/(2*(1-(inverseDimension (m+1))^2)))*(inverseDimension (m+1))^2) = 1 ∧
    2*(1/(2*(1-(inverseDimension (m+1))^2)))*(latitudeScale m)^2 = 1 := by
  let b := inverseDimension (m+1)
  have hb := inverseDimension_bounds (show 2 ≤ m+1 by omega)
  have h1 : 1-b ≠ 0 := by dsimp [b]; linarith [hb.2]
  have hp : 1+b ≠ 0 := by dsimp [b]; linarith [hb.1]
  have hq : 1-b^2 ≠ 0 := by dsimp [b]; nlinarith [hb.1, hb.2]
  have hf : 1-b^2 = (1-b)*(1+b) := by ring
  have hc : 2*(1/(2*(1-b^2))) = 1/(1-b^2) := by field_simp [hq]
  have hbal := dimension_balance m
  change (m : ℝ)*b = 1-b at hbal
  change (m : ℝ)*(2*(1/(2*(1-b^2)))*b) = 1/(1+b) ∧
    1/(1+b)+(m : ℝ)*(2*(1/(2*(1-b^2)))*b^2) = 1 ∧
      2*(1/(2*(1-b^2)))*(latitudeScale m)^2 = 1
  rw [hc]
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = ((m : ℝ)*b)/(1-b^2) := by ring
      _ = (1-b)/(1-b^2) := by rw [hbal]
      _ = _ := by rw [hf]; field_simp [h1, hp]
  · have he : (m : ℝ)*(1/(1-b^2)*b^2) = b/(1+b) := by
      calc
        _ = ((m : ℝ)*b)*b/(1-b^2) := by ring
        _ = (1-b)*b/(1-b^2) := by rw [hbal]
        _ = _ := by rw [hf]; field_simp [h1, hp]
    rw [he]
    field_simp [hp]
  · rw [latitudeScale_sq hm]
    change 1/(1-b^2)*(1-b^2) = 1
    field_simp [hq]

theorem latitude_pair_first (m : ℕ) (k : Fin m) :
    weight m (Sum.inr (k,true)) • contact m (Sum.inr (k,true))+
      weight m (Sum.inr (k,false)) • contact m (Sum.inr (k,false)) =
        (2*(1/(2*(1-(inverseDimension (m+1))^2)))*inverseDimension (m+1)) • axis m := by
  ext j
  simp [contact, weight, WithLp.ofLp_add, WithLp.ofLp_smul, smul_eq_mul]
  ring

theorem latitude_pair_second (m : ℕ) (k : Fin m) :
    weight m (Sum.inr (k,true)) • outer (contact m (Sum.inr (k,true)))+
      weight m (Sum.inr (k,false)) • outer (contact m (Sum.inr (k,false))) =
        (2*(1/(2*(1-(inverseDimension (m+1))^2)))*(inverseDimension (m+1))^2) • outer (axis m)+
        (2*(1/(2*(1-(inverseDimension (m+1))^2)))*(latitudeScale m)^2) • outer (transverseBasis m k) := by
  ext i j
  simp [contact, weight, Khachiyan.outer_apply, WithLp.ofLp_add, WithLp.ofLp_smul, smul_eq_mul]
  ring

theorem frame_first_moment (hm : 1 ≤ m) :
    (∑ i : ContactIndex m, weight m i • contact m i) = 0 := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_unique, Fintype.sum_bool, latitude_pair_first]
  change (1/(1+inverseDimension (m+1))) • (-axis m)+
    (∑ k : Fin m, (2*(1/(2*(1-(inverseDimension (m+1))^2)))*inverseDimension (m+1)) • axis m) = 0
  rw [← Finset.sum_smul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [(moment_coefficients hm).1, smul_neg]
  abel

theorem frame_second_moment (hm : 1 ≤ m) :
    (∑ i : ContactIndex m, weight m i • outer (contact m i)) = 1 := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_unique, Fintype.sum_bool, latitude_pair_second]
  have hneg : outer (-axis m) = outer (axis m) := by
    ext i j
    simp [Khachiyan.outer_apply]
  let wp : ℝ := 1/(1+inverseDimension (m+1))
  let wl : ℝ := 1/(2*(1-(inverseDimension (m+1))^2))
  change wp • outer (-axis m)+(∑ k : Fin m,
    ((2*wl*(inverseDimension (m+1))^2) • outer (axis m)+
      (2*wl*(latitudeScale m)^2) • outer (transverseBasis m k))) = 1
  rw [hneg, Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.smul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp [wp, wl]
  rw [← add_assoc, ← add_smul, (moment_coefficients hm).2.1, (moment_coefficients hm).2.2,
    one_smul, one_smul, transverse_outer_sum, Certificate.projector]
  abel

def extremalFrame (m : ℕ) (hm : 1 ≤ m) : JohnFrame (m+1) (Fintype.card (ContactIndex m)) :=
  JohnFrame.ofFinite (contact m) (weight m) (contact_unit hm) (weight_pos hm)
    (frame_first_moment hm) (frame_second_moment hm)

end SharpCut.Sharpness
