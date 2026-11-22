import SharpCut.Sharpness.FrameMoments
import SharpCut.Sharpness.ModelSupport

/-! # Actual fixed-dimensional attainment of the sharp contraction constant -/

noncomputable section
open scoped RealInnerProductSpace BigOperators ENNReal
open Matrix Set MeasureTheory
namespace SharpCut.Sharpness
open Certificate
variable {m n : ℕ}

theorem contact_model_heights (m : ℕ) (i : ContactIndex m) :
    ⟪contact m i, axis m⟫ = -1 ∨ ⟪contact m i, axis m⟫ = inverseDimension (m+1) := by
  cases i with
  | inl i => left; simp [contact, real_inner_self_eq_norm_sq]
  | inr i =>
    right
    have ho : ⟪transverseBasis m i.1, axis m⟫ = 0 := by
      simpa only [real_inner_comm] using axis_basis_orthogonal m i.1
    simp only [contact, Sum.elim_inr, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, axis_norm, one_pow, mul_one, ho, mul_zero, add_zero]

theorem extremalFrame_heights (hm : 1 ≤ m) (i : Fin (Fintype.card (ContactIndex m))) :
    height (extremalFrame m hm) (axis m) i = -1 ∨
      height (extremalFrame m hm) (axis m) i = inverseDimension (m+1) := by
  rw [height, extremalFrame, JohnFrame.ofFinite_contact]
  exact contact_model_heights m _

def extremalBody (m : ℕ) (hm : 1 ≤ m) : Set (V (m+1)) := (extremalFrame m hm).polytope

theorem extremalBody_isConvexBody (hm : 1 ≤ m) : IsConvexBody (extremalBody m hm) :=
  (extremalFrame m hm).polytope_isConvexBody

theorem extremalBody_isJohnNormalized (hm : 1 ≤ m) : IsJohnNormalized (extremalBody m hm) :=
  (extremalFrame m hm).polytope_isJohnNormalized

theorem axis_ne_zero (m : ℕ) : axis m ≠ 0 := by
  intro h
  have he := congrArg (fun u : V (m+1) => u 0) h
  simpa only [axis_zero, WithLp.ofLp_zero, Pi.zero_apply, one_ne_zero] using he

theorem extremalBody_center (hm : 1 ≤ m) : Khachiyan.johnCenter (extremalBody m hm) = 0 :=
  Khachiyan.johnCenter_eq_of_isMaxDet (extremalBody_isConvexBody hm) (extremalBody_isJohnNormalized hm)

theorem extremal_candidate_feasible (hm : 1 ≤ m) :
    IsFeasible (extremalBody m hm ∩ centralHalfspace 0 (axis m))
      (modelCenter (axis m)) (modelShape (axis m)) :=
  model_feasible_contact_cut (extremalFrame m hm) (by omega) (axis m) (axis_norm m) (extremalFrame_heights hm)

theorem extremalBody_attainment (hm : 1 ≤ m) :
    maxEllipsoidVolume (extremalBody m hm ∩ centralHalfspace (Khachiyan.johnCenter (extremalBody m hm)) (axis m)) =
      ENNReal.ofReal (sharpRatio (m+1))*maxEllipsoidVolume (extremalBody m hm) := by
  have hu := (Geometry.sharp_center_cut_upper (show 1 ≤ m+1 by omega) (extremalBody_isConvexBody hm) (axis_ne_zero m)).2
  have hl : volume (ellipsoid (modelCenter (axis m)) (modelShape (axis m))) ≤
      maxEllipsoidVolume (extremalBody m hm ∩ centralHalfspace 0 (axis m)) :=
    Khachiyan.volume_le_maxEllipsoidVolume (extremal_candidate_feasible hm)
  have hbody : maxEllipsoidVolume (extremalBody m hm) = volume (unitBall (m+1)) :=
    Geometry.normalized_volume (extremalBody_isJohnNormalized hm)
  have hc : volume (ellipsoid (modelCenter (axis m)) (modelShape (axis m))) =
      ENNReal.ofReal (sharpRatio (m+1))*maxEllipsoidVolume (extremalBody m hm) := by
    rw [Khachiyan.volume_ellipsoid_eq_det (modelShape_posDef (by omega) (axis m) (axis_norm m)),
      modelShape_det (by omega) (axis m) (axis_norm m), hbody]
  rw [hc] at hl
  rw [extremalBody_center hm]
  rw [extremalBody_center hm] at hu
  exact le_antisymm hu hl

/-- A body and genuine central cut attain the sharp value in every fixed positive dimension. -/
theorem fixed_dimension_attainment [NeZero n] (hn : 1 ≤ n) :
    ∃ (K : Set (V n)) (v : V n), IsConvexBody K ∧ v ≠ 0 ∧
      maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v) =
        ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K := by
  by_cases h1 : n = 1
  · subst n; exact fixed_dimension_attainment_one
  · cases n with
    | zero => omega
    | succ m =>
      have hm : 1 ≤ m := by omega
      exact ⟨extremalBody m hm, axis m, extremalBody_isConvexBody hm, axis_ne_zero m, extremalBody_attainment hm⟩

end SharpCut.Sharpness
