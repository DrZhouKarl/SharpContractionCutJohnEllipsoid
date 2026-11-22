import SharpCut.JohnFrame

/-! # Geometric properties of the finite contact polytope

These results assume exactly a finite frame. The existence of a supporting
frame for a general normalized body remains the separate John-necessity target.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace SharpCut.JohnFrame
variable {n N : ℕ} (F : SharpCut.JohnFrame n N)

theorem polytope_isClosed : IsClosed F.polytope := by
  have he : F.polytope = ⋂ i, {x | ⟪F.contact i, x⟫ ≤ (1 : ℝ)} := by
    ext x; simp [polytope]
  rw [he]
  apply isClosed_iInter
  intro i
  exact isClosed_le (continuous_const.inner continuous_id) continuous_const

theorem polytope_convex : Convex ℝ F.polytope := by
  intro x hx y hy a b ha hb hab i
  simp only [inner_add_right, real_inner_smul_right]
  calc
    a*⟪F.contact i, x⟫+b*⟪F.contact i, y⟫ ≤ a*1+b*1 :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = 1 := by simpa using hab

theorem polytope_isCompact : IsCompact F.polytope := by
  apply Metric.isCompact_of_isClosed_isBounded F.polytope_isClosed
  apply (isCompact_closedBall (0 : V n) (n : ℝ)).isBounded.subset
  intro x hx
  simpa [Metric.mem_closedBall] using F.norm_le_dimension_of_mem_polytope hx

theorem polytope_isConvexBody : IsConvexBody F.polytope := by
  refine ⟨F.polytope_isCompact, F.polytope_convex, 0, ?_⟩
  have hsub : Metric.ball (0 : V n) 1 ⊆ F.polytope :=
    Metric.ball_subset_closedBall.trans F.unitBall_subset_polytope
  exact interior_maximal hsub Metric.isOpen_ball (by simp)

theorem cut_volume_comparison {K : Set (V n)} (hs : F.Supports K) (v : V n) :
    maxEllipsoidVolume (K ∩ centralHalfspace 0 v) ≤
      maxEllipsoidVolume (F.polytope ∩ centralHalfspace 0 v) := by
  apply Khachiyan.maxEllipsoidVolume_mono
  intro x hx
  exact ⟨F.supporting_subset hs hx.1, hx.2⟩

end SharpCut.JohnFrame
