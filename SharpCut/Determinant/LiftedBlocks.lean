import SharpCut.Determinant.LiftedFrame
import SharpCut.Determinant.SchurGeometry

/-! # Block form of the actual lifted contact moment -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
open Certificate
set_option autoImplicit false
variable {n N : ℕ}

def liftedIndex (n : ℕ) : Fin n ⊕ Unit ≃ Fin (n+1) where
  toFun := Sum.elim Fin.succ (fun _ => 0)
  invFun := Fin.cases (Sum.inr ()) Sum.inl
  left_inv := by intro i; cases i <;> simp
  right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

def liftedWeightedDirection (F : JohnFrame n N) (f : Fin N → ℝ) : V n :=
  ∑ i, (F.weight i*f i) • F.contact i

theorem liftedMoment_block (F : JohnFrame n N) (hn : 2 ≤ n) (f : Fin N → ℝ) :
    (liftedMoment F f).submatrix (liftedIndex n) (liftedIndex n) =
      borderedMatrix (Certificate.weightedShape F f)
        (Real.sqrt (inverseDimension n) • liftedWeightedDirection F f)
        (inverseDimension n*(∑ i, F.weight i*f i)) := by
  ext j k
  cases j with
  | inl j =>
    cases k with
    | inl k =>
      simp only [Matrix.submatrix_apply, liftedIndex, Equiv.coe_fn_mk, Sum.elim_inl,
        liftedMoment_entry, liftedVector, WithLp.ofLp_toLp, Fin.cases_succ,
        borderedMatrix, Matrix.fromBlocks_apply₁₁, Certificate.weightedShape,
        Matrix.sum_apply, Matrix.smul_apply, Khachiyan.outer_apply, smul_eq_mul, mul_assoc]
    | inr k =>
      simp only [Matrix.submatrix_apply, liftedIndex, Equiv.coe_fn_mk, Sum.elim_inl,
        Sum.elim_inr, liftedMoment_entry, liftedVector, WithLp.ofLp_toLp,
        Fin.cases_succ, Fin.cases_zero, borderedMatrix, Matrix.fromBlocks_apply₁₂,
        Matrix.replicateCol_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
        liftedWeightedDirection, WithLp.ofLp_sum, Finset.sum_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi; ring
  | inr j =>
    cases k with
    | inl k =>
      simp only [Matrix.submatrix_apply, liftedIndex, Equiv.coe_fn_mk, Sum.elim_inl,
        Sum.elim_inr, liftedMoment_entry, liftedVector, WithLp.ofLp_toLp,
        Fin.cases_succ, Fin.cases_zero, borderedMatrix, Matrix.fromBlocks_apply₂₁,
        Matrix.replicateRow_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
        liftedWeightedDirection, WithLp.ofLp_sum, Finset.sum_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi; ring
    | inr k =>
      simp only [Matrix.submatrix_apply, liftedIndex, Equiv.coe_fn_mk, Sum.elim_inr,
        liftedMoment_entry, liftedVector, WithLp.ofLp_toLp, Fin.cases_zero,
        borderedMatrix, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
        Matrix.one_apply, Subsingleton.elim j k, ite_true, smul_eq_mul, mul_one]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = (Real.sqrt (inverseDimension n))^2*(F.weight i*f i) := by ring
        _ = _ := by rw [Real.sq_sqrt (inverseDimension_bounds hn).1.le]

theorem liftedMoment_det (F : JohnFrame n N) (hn : 2 ≤ n) (f : Fin N → ℝ)
    (hf : ∀ i, 0 < f i) :
    (liftedMoment F f).det = (Certificate.weightedShape F f).det*
      (inverseDimension n*(∑ i, F.weight i*f i)-
        axisMoment (Certificate.weightedShape F f)⁻¹
          (Real.sqrt (inverseDimension n) • liftedWeightedDirection F f)) := by
  rw [← Matrix.det_submatrix_equiv_self (liftedIndex n), liftedMoment_block F hn f]
  exact borderedMatrix_det _ (Certificate.weightedShape_posDef F f hf) _ _

theorem contact_scalar_sum (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (∑ i, F.weight i*Certificate.contactScalarFactor F v i) = (n : ℝ)+
      (boostParameter n)^2*axisMoment (Certificate.weightedShape F
        (Certificate.contactScalarFactor F v)) v-boostParameter n*cutWeight n := by
  have he : (∑ i, F.weight i*Certificate.contactScalarFactor F v i) =
      Certificate.reweightedMoment F v 0-cutWeight n*Certificate.reweightedMoment F v 1 := by
    unfold Certificate.contactScalarFactor Certificate.reweightedMoment
    simp only [pow_zero, pow_one, mul_one]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he, axisMoment, Certificate.contactShape_axial]
  obtain ⟨h0, h1, h2⟩ := Certificate.reweighted_moments F hn v hv
  linear_combination h0+(boostParameter n-cutWeight n)*h1-boostParameter n*cutWeight n*h2

theorem lifted_contact_det (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (liftedMoment F (Certificate.contactScalarFactor F v)).det =
      inverseDimension n*(Certificate.weightedShape F (Certificate.contactScalarFactor F v)).det*
        ((n : ℝ)+boostParameter n*cutWeight n-(cutWeight n)^2*
          inverseAxisMoment (Certificate.weightedShape F (Certificate.contactScalarFactor F v)) v) := by
  rw [liftedMoment_det F hn _ (Certificate.contactScalarFactor_pos F hn v hv),
    contact_scalar_sum F hn v hv, axisMoment_smul,
    Real.sq_sqrt (inverseDimension_bounds hn).1.le]
  rw [show liftedWeightedDirection F (Certificate.contactScalarFactor F v) =
    Certificate.weightedDirection F v from rfl,
    Certificate.weighted_direction_balance F hn v hv,
    inverse_axial_combination _ (Certificate.contactShape_posDef F hn v hv) v hv]
  ring

theorem contact_schur_positive (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    0 < (n : ℝ)+boostParameter n*cutWeight n-(cutWeight n)^2*
      inverseAxisMoment (weightedShape F (contactScalarFactor F v)) v := by
  have h := (liftedMoment_posDef F hn _ (contactScalarFactor_pos F hn v hv)).det_pos
  rw [lifted_contact_det F hn v hv] at h
  exact pos_of_mul_pos_right h
    (mul_pos (inverseDimension_bounds hn).1 (contactShape_posDef F hn v hv).det_pos).le

end SharpCut.Determinant
