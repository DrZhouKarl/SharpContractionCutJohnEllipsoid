import SharpCut.Simplex.Construction

/-! # Exact uniform John weights and the regular simplex contact Gram matrix -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Simplex
open Certificate Geometry Sharpness Equality
variable {n N : ℕ}

theorem pole_weight_identity (n : ℕ) : 1/(1+inverseDimension (n+1)) = johnWeight (n+1) := by
  unfold inverseDimension johnWeight
  simp only [Nat.cast_add,Nat.cast_one]
  have hp : (n : ℝ)+1 ≠ 0 := by positivity
  have hq : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp [hp,hq] <;> ring

theorem latitude_weight_identity (hn : 1 ≤ n) :
    johnWeight n/(1-(inverseDimension (n+1))^2) = johnWeight (n+1) := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold johnWeight inverseDimension
  simp only [Nat.cast_add,Nat.cast_one]
  have hp : (n : ℝ)+1 ≠ 0 := by positivity
  have hq : (n : ℝ)+2 ≠ 0 := by positivity
  have hden : 1-(1/((n : ℝ)+1))^2 ≠ 0 := by
    have hb := inverseDimension_bounds (show 2 ≤ n+1 by omega)
    dsimp only [inverseDimension] at hb
    simp only [Nat.cast_add,Nat.cast_one] at hb
    nlinarith only [hb.1,hb.2]
  have he : 1-(1/((n : ℝ)+1))^2 = (n : ℝ)*((n : ℝ)+2)/((n : ℝ)+1)^2 := by
    field_simp [hp] <;> ring
  rw [he]
  field_simp [hp,hq,hnp.ne'] <;> ring

theorem latitude_gram_identity (hn : 1 ≤ n) :
    (inverseDimension (n+1))^2+(1-(inverseDimension (n+1))^2)*(-inverseDimension n) = -inverseDimension (n+1) := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold inverseDimension
  simp only [Nat.cast_add,Nat.cast_one]
  have hp : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp [hnp.ne',hp] <;> ring

theorem lift_weights (F : JohnFrame n N) (hn : 1 ≤ n) (hw : ∀ i, F.weight i = johnWeight n) :
    ∀ i, (liftFrame F hn).weight i = johnWeight (n+1) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact pole_weight_identity n
  · change F.weight j/(1-(inverseDimension (n+1))^2) = johnWeight (n+1)
    rw [hw,latitude_weight_identity hn]

theorem regular_weights (m : ℕ) : ∀ i, (regularFrame m).weight i = johnWeight (m+1) := by
  induction m with
  | zero => intro i; norm_num [regularFrame,baseFrame,johnWeight]
  | succ m ih =>
    intro i
    exact lift_weights (regularFrame m) (by omega) ih i

theorem padTail_inner_axis (x : V n) : ⟪padTail x,axis n⟫ = 0 := by
  rw [real_inner_comm]
  exact padTail_axis_inner x

theorem lift_gram (F : JohnFrame n N) (hn : 1 ≤ n)
    (hg : ∀ i j, i ≠ j → ⟪F.contact i,F.contact j⟫ = -inverseDimension n) :
    ∀ i j, i ≠ j → ⟪(liftFrame F hn).contact i,(liftFrame F hn).contact j⟫ = -inverseDimension (n+1) := by
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · intro j
    refine Fin.cases ?_ (fun b => ?_) j
    · intro h; exact (h rfl).elim
    · intro h
      simp [liftFrame,frameFromTransverse,familyContact,inner_add_right,real_inner_smul_right,
        real_inner_self_eq_norm_sq,padTail_axis_inner]
  · intro j
    refine Fin.cases ?_ (fun b => ?_) j
    · intro h
      simp [liftFrame,frameFromTransverse,familyContact,inner_add_left,real_inner_smul_left,
        real_inner_self_eq_norm_sq,padTail_inner_axis]
    · intro h
      have hab : a ≠ b := by intro he; exact h (congrArg Fin.succ he)
      have he : ⟪(liftFrame F hn).contact a.succ,(liftFrame F hn).contact b.succ⟫ =
          (inverseDimension (n+1))^2+(familyRadius (n+1))^2*(-inverseDimension n) := by
        simp only [liftFrame,frameFromTransverse,familyContact,Fin.cases_succ,
          inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
          padTail_axis_inner,padTail_inner_axis,padTail_inner,hg a b hab,
          real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
          axis_norm,one_pow,mul_one,mul_zero,zero_mul,add_zero,zero_add]
        ring
      rw [he,familyRadius_sq (show 2 ≤ n+1 by omega),latitude_gram_identity hn]

theorem base_gram (i j : Fin 2) (hij : i ≠ j) : ⟪baseFrame.contact i,baseFrame.contact j⟫ = -inverseDimension 1 := by
  fin_cases i <;> fin_cases j <;> norm_num at hij <;>
    simp [baseFrame,baseContact,inverseDimension,real_inner_self_eq_norm_sq]

theorem regular_gram (m : ℕ) : ∀ i j, i ≠ j →
    ⟪(regularFrame m).contact i,(regularFrame m).contact j⟫ = -inverseDimension (m+1) := by
  induction m with
  | zero => exact base_gram
  | succ m ih => exact lift_gram (regularFrame m) (by omega) ih

theorem regular_gram_all (m : ℕ) (i j : Fin (m+2)) :
    ⟪(regularFrame m).contact i,(regularFrame m).contact j⟫ = if i = j then 1 else -inverseDimension (m+1) := by
  classical
  by_cases h : i = j
  · subst j
    rw [real_inner_self_eq_norm_sq,(regularFrame m).contact_unit i,one_pow,ite_eq_left rfl]
  · rw [ite_eq_right h]
    exact regular_gram m i j h

end SharpCut.Simplex
