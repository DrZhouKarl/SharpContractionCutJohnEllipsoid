import SharpCut.Stability.Theorem

/-! # Active defining facets of genuine John contacts after affine normalization -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix Set
namespace SharpCut.Optimization
open Certificate
variable {n N : ℕ}

def normalizedNormals (g : Fin N → V n) (A : MatR n) : Fin N → V n := fun r => Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)
def normalizedOffsets (g : Fin N → V n) (β : Fin N → ℝ) (c : V n) : Fin N → ℝ := fun r => β r-⟪g r,c⟫
def facetLength (g : Fin N → V n) (A : MatR n) (r : Fin N) : ℝ := ‖normalizedNormals g A r‖
def facetDirection (g : Fin N → V n) (A : MatR n) (r : Fin N) : V n := (facetLength g A r)⁻¹ • normalizedNormals g A r

theorem normalized_polytope (g : Fin N → V n) (β : Fin N → ℝ) (c : V n) (A : MatR n) (hA : A.PosDef) :
    Khachiyan.normalizedBody (constraintPolytope g β) c A = constraintPolytope (normalizedNormals g A) (normalizedOffsets g β c) := by
  rw [Khachiyan.normalizedBody_eq_preimage hA]
  ext u
  simp only [Set.mem_preimage, constraintPolytope, Set.mem_setOf_eq, Khachiyan.denormalizePoint,
    normalizedNormals, normalizedOffsets, inner_add_right]
  apply forall_congr'
  intro r
  rw [Khachiyan.inner_matrix_action_symm hA.isHermitian.isSymm]
  constructor <;> intro h <;> linarith only [h]

/-- If all defining inequalities are strict, the point is genuinely interior. -/
theorem strict_facets_mem_interior (g : Fin N → V n) (β : Fin N → ℝ) (u : V n)
    (hu : ∀ r, ⟪g r,u⟫ < β r) : u ∈ interior (constraintPolytope g β) := by
  let O : Set (V n) := ⋂ r, {x | ⟪g r,x⟫ < β r}
  have hO : IsOpen O := isOpen_iInter_of_finite (fun r => isOpen_lt (continuous_const.inner continuous_id) continuous_const)
  have huO : u ∈ O := by simpa only [O, Set.mem_iInter, Set.mem_setOf_eq] using hu
  have hsub : O ⊆ constraintPolytope g β := by
    intro x hx r
    exact (Set.mem_iInter.mp hx r).le
  exact (interior_maximal hsub hO) huO

/-- A unit contact with its supporting plane must lie on some defining facet. -/
theorem contact_active_facet (g : Fin N → V n) (β : Fin N → ℝ)
    (hball : unitBall n ⊆ constraintPolytope g β) (u : V n) (hu : ‖u‖ = 1)
    (hs : ∀ x ∈ constraintPolytope g β, ⟪u,x⟫ ≤ 1) : ∃ r, ⟪g r,u⟫ = β r := by
  have humem : u ∈ constraintPolytope g β := hball (by rw [Khachiyan.mem_unitBall, hu])
  by_contra hn
  have hstrict : ∀ r, ⟪g r,u⟫ < β r := by
    intro r
    exact lt_of_le_of_ne (humem r) (by intro he; exact hn ⟨r, he⟩)
  exact John.contact_not_mem_interior ⟨hu, hs⟩ (strict_facets_mem_interior g β u hstrict)

theorem facetLength_pos (g : Fin N → V n) (A : MatR n) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) (r : Fin N) :
    0 < facetLength g A r := by
  apply norm_pos_iff.mpr
  intro hz
  have h := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹) hz
  unfold normalizedNormals at h
  rw [Determinant.posDef_inverse_action A hA, map_zero] at h
  exact hg r h

/-- Equality in (2.10) identifies the actual transformed facet direction. -/
theorem unit_direction_of_active (a p : V n) (ha : a ≠ 0) (hp : ‖p‖ = 1) (heq : ⟪a,p⟫ = ‖a‖) :
    p = ‖a‖⁻¹ • a := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hunit : ‖‖a‖⁻¹ • a‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hapos), inv_mul_cancel₀ hapos.ne']
  have hinner : ⟪p, ‖a‖⁻¹ • a⟫ = 1 := by
    rw [real_inner_smul_right, real_inner_comm a p, heq, inv_mul_cancel₀ hapos.ne']
  have hnorm : ‖p-‖a‖⁻¹ • a‖^2 = 0 := by rw [norm_sub_sq_real, hp, hunit, hinner]; norm_num
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))

/-- Each contact of the normalized optimal body is assigned an active original facet. -/
theorem normalized_contact_facet (g : Fin N → V n) (β : Fin N → ℝ) (hg : ∀ r, g r ≠ 0)
    {c : V n} {A : MatR n} (hp : PrimalFeasible g β c A) (u : V n) (hu : ‖u‖ = 1)
    (hs : ∀ x ∈ Khachiyan.normalizedBody (constraintPolytope g β) c A, ⟪u,x⟫ ≤ 1)
    (hball : unitBall n ⊆ Khachiyan.normalizedBody (constraintPolytope g β) c A) :
    ∃ r, u = facetDirection g A r ∧ normalizedOffsets g β c r = facetLength g A r := by
  rw [normalized_polytope g β c A hp.1] at hs hball
  obtain ⟨r, hr⟩ := contact_active_facet (normalizedNormals g A) (normalizedOffsets g β c) hball u hu hs
  have hsupport := hp.2 r
  have hCauchy := real_inner_le_norm (normalizedNormals g A r) u
  rw [hu, mul_one, hr] at hCauchy
  have hlen : normalizedOffsets g β c r = facetLength g A r := by
    change _ ≤ ‖normalizedNormals g A r‖ at hCauchy
    unfold normalizedOffsets facetLength normalizedNormals at *
    linarith only [hsupport, hCauchy]
  have hneq : normalizedNormals g A r ≠ 0 := by
    have h := facetLength_pos g A hp.1 hg r
    exact norm_ne_zero_iff.mp h.ne'
  have hdir := unit_direction_of_active (normalizedNormals g A r) u hneq hu (hr.trans hlen)
  exact ⟨r, hdir, hlen⟩

end SharpCut.Optimization
