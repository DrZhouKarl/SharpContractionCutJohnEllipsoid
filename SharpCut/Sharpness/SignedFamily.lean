import SharpCut.Equality.TransverseFamily

/-! # The signed transverse family in every positive transverse dimension -/

noncomputable section
open scoped RealInnerProductSpace BigOperators ENNReal
open Matrix Set
namespace SharpCut.Sharpness
variable {m : ℕ}

def signedTransverse (m : ℕ) (i : Fin m × Bool) : V (m+1) :=
  (if i.2 then (1 : ℝ) else -1) • transverseBasis m i.1

theorem signed_transverse_unit (m : ℕ) (i : Fin m × Bool) : ‖signedTransverse m i‖ = 1 := by
  rcases i with ⟨k,b⟩
  cases b <;> simp [signedTransverse]

theorem signed_transverse_perp (m : ℕ) (i : Fin m × Bool) : ⟪axis m,signedTransverse m i⟫ = 0 := by
  simp only [signedTransverse, real_inner_smul_right, axis_basis_orthogonal, mul_zero]

theorem signed_contact_formula (m : ℕ) (i : Fin m × Bool) :
    contact m (Sum.inr i) = inverseDimension (m+1) • axis m+latitudeScale m • signedTransverse m i := by
  rcases i with ⟨k,b⟩
  cases b <;> simp [contact,signedTransverse,smul_smul]

theorem signed_transverse_balance (m : ℕ) : (∑ i : Fin m × Bool, (1/2 : ℝ) • signedTransverse m i) = 0 := by
  rw [Fintype.sum_prod_type]
  have hpair (k : Fin m) : (∑ b : Bool, (1/2 : ℝ) • signedTransverse m (k,b)) = 0 := by
    simp [Fintype.sum_bool, signedTransverse]
  simp only [hpair, Finset.sum_const_zero]

theorem signed_transverse_isotropy (m : ℕ) :
    (∑ i : Fin m × Bool, (1/2 : ℝ) • outer (signedTransverse m i)) = Certificate.projector (axis m) := by
  have hneg (u : V (m+1)) : outer (-u) = outer u := by ext i j; simp [Khachiyan.outer_apply]
  rw [Fintype.sum_prod_type]
  have hpair (k : Fin m) : (∑ b : Bool, (1/2 : ℝ) • outer (signedTransverse m (k,b))) = outer (transverseBasis m k) := by
    simp only [Fintype.sum_bool, signedTransverse, Bool.false_eq_true, ite_true, ite_false, one_smul, neg_one_smul, hneg]
    module
  simp only [hpair, transverse_outer_sum]

/-- The signed example has actual sharp cut volume and the actual new John ellipsoid. -/
theorem signed_family_geometry (hm : 1 ≤ m) :
    IsConvexBody (extremalBody m hm) ∧ IsJohnNormalized (extremalBody m hm) ∧
    maxEllipsoidVolume (extremalBody m hm ∩ centralHalfspace 0 (axis m)) =
      ENNReal.ofReal (sharpRatio (m+1))*maxEllipsoidVolume (extremalBody m hm) ∧
    IsMaxDet (extremalBody m hm ∩ centralHalfspace 0 (axis m)) (modelCenter (axis m)) (modelShape (axis m)) ∧
    Khachiyan.johnEllipsoid (extremalBody m hm ∩ centralHalfspace 0 (axis m)) = Equality.modelEllipsoid (axis m) := by
  letI : NeZero (m+1) := ⟨by omega⟩
  have hK := extremalBody_isConvexBody hm
  have hJ := extremalBody_isJohnNormalized hm
  have he := extremalBody_attainment hm
  rw [extremalBody_center hm] at he
  exact ⟨hK, hJ, he, Equality.model_isMaxDet_of_equality (by omega) hK hJ _ (axis_norm m) he,
    Equality.newJohnEllipsoid_model (by omega) hK hJ _ (axis_norm m) he⟩

end SharpCut.Sharpness
