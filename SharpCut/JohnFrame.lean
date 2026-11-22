import SharpCut.Geometry
import Khachiyan.ContactCertificate

/-!
# Finite John frames

Only the four defining contact conditions are fields. Total weight, spanning,
scalar moments and the supporting polytope bound are derived. Supporting a
body is a separate predicate and is not assumed by arbitrary-frame algebra.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix

namespace SharpCut

structure JohnFrame (n N : ℕ) where
  contact : Fin N → V n
  weight : Fin N → ℝ
  contact_unit : ∀ i, ‖contact i‖ = 1
  weight_pos : ∀ i, 0 < weight i
  first_moment : ∑ i, weight i • contact i = 0
  second_moment : ∑ i, weight i • outer (contact i) = 1

namespace JohnFrame
variable {n N : ℕ} (F : JohnFrame n N)

def Supports (K : Set (V n)) : Prop := ∀ i, ∀ x ∈ K, ⟪F.contact i, x⟫ ≤ 1

def polytope : Set (V n) := {x | ∀ i, ⟪F.contact i, x⟫ ≤ 1}

theorem weight_sum : ∑ i, F.weight i = (n : ℝ) :=
  Khachiyan.contact_weights_sum F.contact F.weight F.contact_unit F.second_moment

theorem scalar_first_moment (x : V n) :
    ∑ i, F.weight i * ⟪F.contact i, x⟫ = 0 := by
  have h := congrArg (fun y : V n => ⟪y, x⟫) F.first_moment
  simpa only [sum_inner, real_inner_smul_left, inner_zero_left] using h

theorem reconstruction (x : V n) :
    ∑ i, (F.weight i * ⟪F.contact i, x⟫) • F.contact i = x := by
  have h := congrArg (fun A : MatR n => A *ᵥ x.ofLp) F.second_moment
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  have ho (i : Fin N) : outer (F.contact i) *ᵥ x.ofLp =
      ⟪F.contact i, x⟫ • (F.contact i).ofLp := by
    have hi := congrArg (fun y : V n => y.ofLp)
      (Khachiyan.outer_action (F.contact i) x)
    simpa only [Khachiyan.matrix_action_ofLp, WithLp.ofLp_smul] using hi
  simp only [ho, smul_smul] at h
  ext j
  have hj := congrFun h j
  simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] using hj

theorem scalar_second_moment (x : V n) :
    ∑ i, F.weight i * ⟪F.contact i, x⟫^2 = ‖x‖^2 := by
  have h := congrArg (fun y : V n => ⟪y, x⟫) (F.reconstruction x)
  simpa only [sum_inner, real_inner_smul_left, real_inner_self_eq_norm_sq,
    pow_two, mul_assoc] using h

theorem heights_bounds (v : V n) (hv : ‖v‖ = 1) (i : Fin N) :
    -1 ≤ ⟪F.contact i, v⟫ ∧ ⟪F.contact i, v⟫ ≤ 1 := by
  have h := abs_real_inner_le_norm (F.contact i) v
  rw [F.contact_unit i, hv, mul_one] at h
  exact abs_le.mp h

theorem unitBall_subset_polytope : unitBall n ⊆ F.polytope := by
  intro x hx i
  have h := real_inner_le_norm (F.contact i) x
  rw [F.contact_unit i, one_mul] at h
  exact h.trans (Khachiyan.mem_unitBall x |>.mp hx)

theorem supporting_subset {K : Set (V n)} (h : F.Supports K) : K ⊆ F.polytope := by
  intro x hx i
  exact h i x hx

theorem polytope_isJohnNormalized : IsJohnNormalized F.polytope :=
  Khachiyan.isJohnNormalized_of_contacts F.unitBall_subset_polytope
    F.contact F.weight F.contact_unit F.weight_pos
    (fun i _x hx => hx i) F.first_moment F.second_moment

theorem norm_le_dimension_of_mem_polytope {x : V n} (hx : x ∈ F.polytope) :
    ‖x‖ ≤ (n : ℝ) := by
  have hre : ∑ i, (F.weight i * (1-⟪F.contact i, x⟫)) • F.contact i = -x := by
    simp only [mul_sub, mul_one, sub_smul, Finset.sum_sub_distrib,
      F.first_moment, F.reconstruction, zero_sub]
  have hweights : ∑ i, F.weight i * (1-⟪F.contact i, x⟫) = (n : ℝ) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, F.weight_sum,
      F.scalar_first_moment, sub_zero]
  calc
    ‖x‖ = ‖-x‖ := (norm_neg x).symm
    _ = ‖∑ i, (F.weight i * (1-⟪F.contact i, x⟫)) • F.contact i‖ := congrArg norm hre.symm
    _ ≤ ∑ i, ‖(F.weight i * (1-⟪F.contact i, x⟫)) • F.contact i‖ := norm_sum_le _ _
    _ = ∑ i, F.weight i * (1-⟪F.contact i, x⟫) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, F.contact_unit i, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (F.weight_pos i).le (sub_nonneg.mpr (hx i)))]
    _ = (n : ℝ) := hweights

end JohnFrame
end SharpCut
