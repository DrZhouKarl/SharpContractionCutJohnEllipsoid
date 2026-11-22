import SharpCut.Examples.PyramidFacets
import Mathlib.Analysis.Convex.Combination

/-! # A supporting plane commutes with taking a convex hull -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Set Matrix
namespace SharpCut.Examples.SquarePyramid

theorem supporting_plane_hull (S : Set (V 3)) (u : V 3) (c : ℝ)
    (hsupport : ∀ z ∈ S, ⟪u,z⟫ ≤ c) :
    convexHull ℝ S ∩ {x | ⟪u,x⟫ = c} = convexHull ℝ (S ∩ {x | ⟪u,x⟫ = c}) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨hx,hplane⟩
    change ⟪u,x⟫ = c at hplane
    obtain ⟨ι,inst,w,z,hw0,hw1,hz,hcomb⟩ := mem_convexHull_iff_exists_fintype.mp hx
    letI : Fintype ι := inst
    have hvalue : (∑ i, w i*⟪u,z i⟫) = c := by
      have h := congrArg (fun y : V 3 => ⟪u,y⟫) hcomb
      simpa only [inner_sum,real_inner_smul_right,hplane] using h
    have hsum : (∑ i, w i*(c-⟪u,z i⟫)) = 0 := by
      simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hw1,one_mul,hvalue,sub_self]
    have hzero (i : ι) : w i*(c-⟪u,z i⟫) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hw0 i) (sub_nonneg.mpr (hsupport _ (hz i))))).mp hsum i (Finset.mem_univ i)
    let t : Finset ι := Finset.univ.filter (fun i => 0 < w i)
    have hweights : (∑ i ∈ t, w i) = 1 := by
      have he : (∑ i ∈ t, w i) = ∑ i, w i := by
        dsimp only [t]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs with hi
        · rfl
        · exact (le_antisymm (le_of_not_gt hi) (hw0 i)).symm
      rw [he,hw1]
    have hcomb' : (∑ i ∈ t, w i • z i) = x := by
      have he : (∑ i ∈ t, w i • z i) = ∑ i, w i • z i := by
        dsimp only [t]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs with hi
        · rfl
        · have hwi : w i = 0 := le_antisymm (le_of_not_gt hi) (hw0 i)
          simp only [hwi,zero_smul]
      rw [he,hcomb]
    have hmem (i : ι) (hi : i ∈ t) : z i ∈ convexHull ℝ (S ∩ {x | ⟪u,x⟫ = c}) := by
      have hp : 0 < w i := (Finset.mem_filter.mp hi).2
      have he : c-⟪u,z i⟫ = 0 := (mul_eq_zero.mp (hzero i)).resolve_left hp.ne'
      exact subset_convexHull ℝ _ ⟨hz i,(sub_eq_zero.mp he).symm⟩
    have h := (convex_convexHull ℝ (S ∩ {x | ⟪u,x⟫ = c})).sum_mem
      (fun i _ => hw0 i) hweights hmem
    rwa [hcomb'] at h
  · have hplane : Convex ℝ {x : V 3 | ⟪u,x⟫ = c} := by
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq,inner_add_right,real_inner_smul_right] at hx hy ⊢
      rw [hx,hy]
      nlinarith only [congrArg (fun t : ℝ => t*c) hab]
    exact Set.subset_inter (convexHull_mono Set.inter_subset_left)
      (convexHull_min Set.inter_subset_right hplane)

end SharpCut.Examples.SquarePyramid
