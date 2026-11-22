import SharpCut.Optimization.Convexity

/-! # Lorentz cone self-duality with the exact scalar-vector cone pairing -/

noncomputable section
open scoped RealInnerProductSpace
namespace SharpCut.Optimization
variable {n : ℕ}

def LorentzFeasible (τ : ℝ) (x : V n) : Prop := ‖x‖ ≤ τ

def LorentzDualFeasible (α : ℝ) (q : V n) : Prop :=
  ∀ τ : ℝ, ∀ x : V n, LorentzFeasible τ x → 0 ≤ α*τ-⟪q,x⟫

/-- The minus sign convention is exactly the one used by the SOC certificate. -/
theorem lorentz_pairing_nonneg (α τ : ℝ) (q x : V n) (hα : ‖q‖ ≤ α) (hτ : ‖x‖ ≤ τ) : 0 ≤ α*τ-⟪q,x⟫ := by
  have hα0 : 0 ≤ α := (norm_nonneg q).trans hα
  have hinner := real_inner_le_norm q x
  have h1 := mul_le_mul_of_nonneg_right hα (norm_nonneg x)
  have h2 := mul_le_mul_of_nonneg_left hτ hα0
  nlinarith only [hinner, h1, h2]

/-- Exact Lorentz self-duality, including zero vector and zero scalar boundaries. -/
theorem lorentz_self_dual (α : ℝ) (q : V n) : LorentzDualFeasible α q ↔ ‖q‖ ≤ α := by
  constructor
  · intro h
    by_cases hz : q = 0
    · have ht := h 1 0 (by simp [LorentzFeasible])
      simp only [hz, norm_zero, mul_one, inner_zero_right, sub_zero] at ht ⊢
      exact ht
    · have hp : 0 < ‖q‖ := norm_pos_iff.mpr hz
      let x := ‖q‖⁻¹ • q
      have hx : ‖x‖ = 1 := by
        dsimp only [x]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
      have ht := h 1 x (hx.le)
      have hi : ⟪q,x⟫ = ‖q‖ := by
        dsimp only [x]
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq, pow_two,
          ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
      rw [hi, mul_one] at ht
      linarith only [ht]
  · intro h τ x hx
    exact lorentz_pairing_nonneg α τ q x h hx


/-- Standard plus-sign Euclidean scalar-vector self-duality of the Lorentz cone. -/
theorem lorentz_self_dual_plus (α : ℝ) (q : V n) :
    (∀ τ : ℝ, ∀ x : V n, ‖x‖ ≤ τ → 0 ≤ α*τ+⟪q,x⟫) ↔ ‖q‖ ≤ α := by
  constructor
  · intro h
    have hd : LorentzDualFeasible α (-q) := by
      intro τ x hx
      have ht := h τ x hx
      simpa only [inner_neg_left, sub_neg_eq_add] using ht
    simpa only [norm_neg] using (lorentz_self_dual α (-q)).mp hd
  · intro h τ x hx
    have hd : ‖-q‖ ≤ α := by simpa only [norm_neg] using h
    have ht := lorentz_pairing_nonneg α τ (-q) x hd hx
    simpa only [inner_neg_left, sub_neg_eq_add] using ht

end SharpCut.Optimization
