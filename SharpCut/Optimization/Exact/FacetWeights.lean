import SharpCut.Optimization.Exact.ActiveFacets

/-! # Grouping genuine John contact weights by active defining facet -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix Set
namespace SharpCut.Optimization
variable {n N J : ℕ}

def groupedWeight (assignment : Fin J → Fin N) (w : Fin J → ℝ) (r : Fin N) : ℝ :=
  ∑ i, if assignment i = r then w i else 0

/-- Finite pushforward of scalar weights into any real module. -/
theorem grouped_weight_sum {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (assignment : Fin J → Fin N) (w : Fin J → ℝ) (x : Fin N → M) :
    (∑ r, groupedWeight assignment w r • x r) = ∑ i, w i • x (assignment i) := by
  unfold groupedWeight
  simp only [Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem groupedWeight_nonneg (assignment : Fin J → Fin N) (w : Fin J → ℝ) (hw : ∀ i, 0 ≤ w i) (r : Fin N) :
    0 ≤ groupedWeight assignment w r := by
  unfold groupedWeight
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> first | exact hw i | exact le_refl 0

theorem facetDirection_unit (g : Fin N → V n) (A : MatR n) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) (r : Fin N) :
    ‖facetDirection g A r‖ = 1 := by
  have hp := facetLength_pos g A hA hg r
  rw [facetDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  change (facetLength g A r)⁻¹*facetLength g A r = 1
  exact inv_mul_cancel₀ hp.ne'

/-- Only actual contact moments and active-facet complementarity are fields.
No dual feasibility or desired inverse aggregate is included. -/
structure FacetJohnData (g : Fin N → V n) (β : Fin N → ℝ) (c : V n) (A : MatR n) where
  weight : Fin N → ℝ
  nonnegative : ∀ r, 0 ≤ weight r
  first : ∑ r, weight r • facetDirection g A r = 0
  second : ∑ r, weight r • outer (facetDirection g A r) = 1
  active : ∀ r, weight r*(normalizedOffsets g β c r-facetLength g A r) = 0

/-- John necessity supplies the data; no contact frame is assumed at the optimum. -/
theorem exists_facet_john_data (hn : 1 ≤ n) (g : Fin N → V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hK : IsConvexBody (constraintPolytope g β))
    {c : V n} {A : MatR n} (hmax : IsMaxDet (constraintPolytope g β) c A) :
    Nonempty (FacetJohnData g β c A) := by
  letI : NeZero n := ⟨by omega⟩
  have hJ := hmax.isJohnNormalized
  have hbody := hK.normalizedBody c hmax.posDef
  obtain ⟨J, F, hs⟩ := John.exists_supporting_frame hn hbody hJ
  have hp := (primalFeasible_iff_containment g β c A).mpr hmax.feasible
  have hball : unitBall n ⊆ Khachiyan.normalizedBody (constraintPolytope g β) c A := by
    simpa only [Khachiyan.ellipsoid_zero_one] using hJ.subset
  have hassign (i : Fin J) : ∃ r, F.contact i = facetDirection g A r ∧ normalizedOffsets g β c r = facetLength g A r :=
    normalized_contact_facet g β hg hp (F.contact i) (F.contact_unit i) (hs i) hball
  classical
  choose assignment hdir hactive using hassign
  let μ := groupedWeight assignment F.weight
  refine ⟨{ weight := μ
            nonnegative := groupedWeight_nonneg assignment F.weight (fun i => (F.weight_pos i).le)
            first := ?_
            second := ?_
            active := ?_ }⟩
  · rw [grouped_weight_sum]
    simp only [← hdir]
    exact F.first_moment
  · rw [grouped_weight_sum]
    simp only [← hdir]
    exact F.second_moment
  · intro r
    unfold μ groupedWeight
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi
    · rw [← hi, hactive i, sub_self, mul_zero]
    · rw [zero_mul]

theorem FacetJohnData.weight_sum {g : Fin N → V n} {β : Fin N → ℝ} {c : V n} {A : MatR n}
    (D : FacetJohnData g β c A) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) : ∑ r, D.weight r = (n : ℝ) :=
  Khachiyan.contact_weights_sum (facetDirection g A) D.weight (facetDirection_unit g A hA hg) D.second

end SharpCut.Optimization
