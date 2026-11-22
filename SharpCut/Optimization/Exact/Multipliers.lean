import SharpCut.Optimization.Exact.FacetWeights

/-! # Constructing exact normalized dual multipliers from derived facet John moments -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix Set
namespace SharpCut.Optimization
open Certificate
variable {n N : ℕ} {g : Fin N → V n} {β : Fin N → ℝ} {c : V n} {A : MatR n}

def FacetJohnData.alpha (D : FacetJohnData g β c A) (r : Fin N) : ℝ := D.weight r/facetLength g A r
def FacetJohnData.vector (D : FacetJohnData g β c A) (r : Fin N) : V n := D.alpha r • facetDirection g A r

theorem facet_normal_reconstruction (g : Fin N → V n) (A : MatR n) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) (r : Fin N) :
    g r = facetLength g A r • Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (facetDirection g A r) := by
  have hp := facetLength_pos g A hA hg r
  rw [facetDirection, map_smul, smul_smul, mul_inv_cancel₀ hp.ne']
  simp only [normalizedNormals, Determinant.posDef_inverse_action A hA, one_smul]

theorem FacetJohnData.alpha_nonneg (D : FacetJohnData g β c A) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) (r : Fin N) :
    0 ≤ D.alpha r := div_nonneg (D.nonnegative r) (facetLength_pos g A hA hg r).le

theorem FacetJohnData.alpha_length (D : FacetJohnData g β c A) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) (r : Fin N) :
    D.alpha r*facetLength g A r = D.weight r := div_mul_cancel₀ _ (facetLength_pos g A hA hg r).ne'

theorem FacetJohnData.alpha_active (D : FacetJohnData g β c A) (r : Fin N) :
    D.alpha r*(normalizedOffsets g β c r-facetLength g A r) = 0 := by
  have h := congrArg (fun x : ℝ => x/facetLength g A r) (D.active r)
  unfold FacetJohnData.alpha
  convert h using 1 <;> ring

theorem FacetJohnData.normal_balance (D : FacetJohnData g β c A) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) :
    (∑ r, D.alpha r • g r) = 0 := by
  have hpoint (r : Fin N) : D.alpha r • g r = Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (D.weight r • facetDirection g A r) := by
    rw [facet_normal_reconstruction g A hA hg r, smul_smul, D.alpha_length hA hg, map_smul]
  simp only [hpoint, ← map_sum, D.first, map_zero]

theorem FacetJohnData.normalization (D : FacetJohnData g β c A) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) :
    (∑ r, D.alpha r*β r) = (n : ℝ) := by
  have hpoint (r : Fin N) : D.alpha r*β r = D.alpha r*⟪g r,c⟫+D.weight r := by
    have ha := D.alpha_active r
    have hl := D.alpha_length hA hg r
    unfold normalizedOffsets at ha
    nlinarith only [ha, hl]
  have hbalance := congrArg (fun u : V n => ⟪u,c⟫) (D.normal_balance hA hg)
  simp only [sum_inner, real_inner_smul_left, inner_zero_left] at hbalance
  simp only [hpoint, Finset.sum_add_distrib, hbalance, D.weight_sum hA hg, zero_add]

theorem FacetJohnData.vector_norm (D : FacetJohnData g β c A) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) (r : Fin N) :
    ‖D.vector r‖ = D.alpha r := by
  rw [FacetJohnData.vector, norm_smul, facetDirection_unit g A hA hg r, mul_one,
    Real.norm_eq_abs, abs_of_nonneg (D.alpha_nonneg hA hg r)]

theorem FacetJohnData.direction_pairing (D : FacetJohnData g β c A) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) (r : Fin N) :
    ⟪D.vector r, normalizedNormals g A r⟫ = D.weight r := by
  have hp := facetLength_pos g A hA hg r
  rw [FacetJohnData.vector, facetDirection, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  change D.alpha r*((facetLength g A r)⁻¹*(facetLength g A r)^2) = _
  have he : (facetLength g A r)⁻¹*(facetLength g A r)^2 = facetLength g A r := by
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  rw [he, D.alpha_length hA hg]

theorem FacetJohnData.pairings_zero (D : FacetJohnData g β c A) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) (r : Fin N) :
    conePairing g β D.alpha D.vector c A r = 0 := by
  unfold conePairing coneHeight
  have hp := D.direction_pairing hA hg r
  change ⟪D.vector r, Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ = D.weight r at hp
  rw [hp]
  have ha := D.alpha_active r
  have hl := D.alpha_length hA hg r
  unfold normalizedOffsets at ha
  nlinarith only [ha, hl]

/-- The unsymmetrized aggregate in (2.13), derived in its stated multiplication order. -/
theorem FacetJohnData.raw_aggregate (D : FacetJohnData g β c A) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) :
    rawAggregate g D.vector = A⁻¹ := by
  have hpoint (r : Fin N) : cross (D.vector r) (g r) = D.weight r • (outer (facetDirection g A r)*A⁻¹) := by
    rw [FacetJohnData.vector, facet_normal_reconstruction g A hA hg r, cross_smul_left, cross_smul_right,
      smul_smul, D.alpha_length hA hg, ← cross_mul A⁻¹ hA.inv.isHermitian.isSymm, cross_self]
  unfold rawAggregate
  simp only [hpoint, ← Matrix.smul_mul, ← Matrix.sum_mul, D.second, Matrix.one_mul]

theorem FacetJohnData.aggregate_inverse (D : FacetJohnData g β c A) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) :
    aggregate g D.vector = A⁻¹ := by
  rw [aggregate_eq_symRaw, D.raw_aggregate hA hg, hA.inv.isHermitian.isSymm.eq]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-- No desired matrix or feasibility fact was stored in the contact data. -/
theorem FacetJohnData.dual_feasible (D : FacetJohnData g β c A) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) :
    DualFeasible g β D.alpha D.vector := by
  refine ⟨fun r => (D.vector_norm hA hg r).le, D.normal_balance hA hg, D.normalization hA hg, ?_⟩
  rw [D.aggregate_inverse hA hg]
  exact hA.inv

/-- Constructed inverse aggregate and zero pairings at every actual optimum. -/
theorem optimal_dual_certificate (hn : 1 ≤ n) (g : Fin N → V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hK : IsConvexBody (constraintPolytope g β))
    {c : V n} {A : MatR n} (hmax : IsMaxDet (constraintPolytope g β) c A) :
    ∃ α : Fin N → ℝ, ∃ q : Fin N → V n, DualFeasible g β α q ∧ aggregate g q = A⁻¹ ∧
      ∀ r, conePairing g β α q c A r = 0 := by
  obtain ⟨D⟩ := exists_facet_john_data hn g β hg hK hmax
  exact ⟨D.alpha, D.vector, D.dual_feasible hmax.posDef hg, D.aggregate_inverse hmax.posDef hg,
    D.pairings_zero hmax.posDef hg⟩

end SharpCut.Optimization
