import SharpCut.Optimization.Lagrangian
import SharpCut.Optimization.Exact.Theorem
import SharpCut.Certificate.Feasibility

/-! # The unnormalized dual, optimal positive scale and strict primal seed -/

noncomputable section
open scoped RealInnerProductSpace BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
open Matrix Set MeasureTheory
namespace SharpCut.Optimization
variable {n N : ℕ}
attribute [local instance] Classical.propDecidable

def balanceVector (g : Fin N → V n) (α : Fin N → ℝ) : V n := ∑ r, α r • g r
def dualMass (β α : Fin N → ℝ) : ℝ := ∑ r, α r*β r
def originalLagrangian (g : Fin N → V n) (β α : Fin N → ℝ) (q : Fin N → V n)
    (c : V n) (A : MatR n) : ℝ := Real.log A.det+coneGap g β α q c A

structure UnnormalizedDualFeasible (g : Fin N → V n) (α : Fin N → ℝ) (q : Fin N → V n) : Prop where
  cone : ∀ r, ‖q r‖ ≤ α r
  balance : balanceVector g α = 0
  positive : (aggregate g q).PosDef

def unnormalizedDualObjective (g : Fin N → V n) (β α : Fin N → ℝ) (q : Fin N → V n) : ℝ :=
  dualMass β α-(n : ℝ)-Real.log (aggregate g q).det

theorem aggregate_hermitian (g q : Fin N → V n) : (aggregate g q).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  change (aggregate g q)ᵀ = aggregate g q
  rw [Certificate.aggregate_eq_symRaw, Matrix.transpose_smul, Matrix.transpose_add,
    Matrix.transpose_transpose, add_comm]

theorem original_lagrangian_identity (g q : Fin N → V n) (β α : Fin N → ℝ)
    (c : V n) (A : MatR n) (hA : A.PosDef) :
    originalLagrangian g β α q c A = lagrangian (balanceVector g α) (aggregate g q) (dualMass β α) c A := by
  have htrace : (A*aggregate g q).trace = ∑ r, ⟪q r, Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ := by
    simp only [aggregate, Matrix.mul_sum, Matrix.trace_sum, trace_mul_symmetricOuter hA.isHermitian.isSymm]
  have hbalance : ⟪balanceVector g α,c⟫ = ∑ r, α r*⟪g r,c⟫ := by
    simp only [balanceVector, sum_inner, real_inner_smul_left]
  simp only [originalLagrangian, coneGap, conePairing, coneHeight, lagrangian, dualMass,
    htrace, hbalance, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Every finite/infinite branch of the raw multiplier Lagrangian, without cone or balance assumptions. -/
theorem original_lagrangian_supremum (hn : 1 ≤ n) (g q : Fin N → V n) (β α : Fin N → ℝ) :
    sSup {z : EReal | ∃ c A, A.PosDef ∧ z = (originalLagrangian g β α q c A : EReal)} =
      if balanceVector g α = 0 ∧ (aggregate g q).PosDef
      then (dualMass β α-(n : ℝ)-Real.log (aggregate g q).det : EReal) else ⊤ := by
  have hsets : {z : EReal | ∃ c A, A.PosDef ∧ z = (originalLagrangian g β α q c A : EReal)} =
      lagrangianValues (balanceVector g α) (aggregate g q) (dualMass β α) := by
    ext z
    constructor <;> rintro ⟨c, A, hA, he⟩
    · exact ⟨c, A, hA, he.trans (congrArg (fun x : ℝ => (x : EReal)) (original_lagrangian_identity g q β α c A hA))⟩
    · exact ⟨c, A, hA, he.trans (congrArg (fun x : ℝ => (x : EReal)) (original_lagrangian_identity g q β α c A hA).symm)⟩
  rw [hsets]
  exact lagrangian_conjugate hn _ _ (aggregate_hermitian g q) _

theorem unnormalized_trace_bound {g q : Fin N → V n} {β α : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g β c A) (hd : UnnormalizedDualFeasible g α q) :
    (A*aggregate g q).trace ≤ dualMass β α := by
  have hbal : ∑ r, α r*⟪g r,c⟫ = 0 := by
    have h := congrArg (fun x : V n => ⟪x,c⟫) hd.balance
    simpa only [balanceVector, sum_inner, real_inner_smul_left, inner_zero_left] using h
  have heach (r : Fin N) : ⟪q r, Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ ≤ α r*(β r-⟪g r,c⟫) := by
    calc
      _ ≤ ‖q r‖*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ := real_inner_le_norm _ _
      _ ≤ α r*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ :=
        mul_le_mul_of_nonneg_right (hd.cone r) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hp.2 r]) ((norm_nonneg _).trans (hd.cone r))
  calc
    _ = ∑ r, ⟪q r, Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ := by
      simp only [aggregate, Matrix.mul_sum, Matrix.trace_sum, trace_mul_symmetricOuter hp.1.isHermitian.isSymm]
    _ ≤ ∑ r, α r*(β r-⟪g r,c⟫) := Finset.sum_le_sum (fun r _ => heach r)
    _ = dualMass β α := by simp only [mul_sub, Finset.sum_sub_distrib, hbal, dualMass, sub_zero]

theorem unnormalized_mass_positive (hn : 1 ≤ n) {g q : Fin N → V n} {β α : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g β c A) (hd : UnnormalizedDualFeasible g α q) :
    0 < (A*aggregate g q).trace ∧ (A*aggregate g q).trace ≤ dualMass β α ∧ 0 < dualMass β α := by
  letI : NeZero n := ⟨by omega⟩
  have hpos := (matchingMatrix_posDef A (aggregate g q) hp.1 hd.positive).trace_pos
  rw [matchingMatrix_trace A (aggregate g q) hd.positive] at hpos
  have hbound := unnormalized_trace_bound hp hd
  exact ⟨hpos, hbound, hpos.trans_le hbound⟩

theorem aggregate_scale (g q : Fin N → V n) (ρ : ℝ) :
    aggregate g (fun r => ρ • q r) = ρ • aggregate g q := by
  unfold aggregate symmetricOuter
  simp only [WithLp.ofLp_smul, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec,
    smul_add, smul_smul, Finset.smul_sum]
  congr 1
  ext i j
  ring

theorem unnormalized_scale {g q : Fin N → V n} {α : Fin N → ℝ}
    (hd : UnnormalizedDualFeasible g α q) (ρ : ℝ) (hρ : 0 < ρ) :
    UnnormalizedDualFeasible g (fun r => ρ*α r) (fun r => ρ • q r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    exact mul_le_mul_of_nonneg_left (hd.cone r) hρ.le
  · have h : balanceVector g (fun r => ρ*α r) = ρ • balanceVector g α := by
      simp only [balanceVector, ← smul_smul, Finset.smul_sum]
    rw [h, hd.balance, smul_zero]
  · rw [aggregate_scale]
    exact hd.positive.smul hρ

def scaleObjective (s : ℝ) (M : MatR n) (ρ : ℝ) : ℝ :=
  ρ*s-(n : ℝ)-(n : ℝ)*Real.log ρ-Real.log M.det

theorem scaled_objective_identity (g q : Fin N → V n) (β α : Fin N → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hM : (aggregate g q).PosDef) :
    unnormalizedDualObjective g β (fun r => ρ*α r) (fun r => ρ • q r) =
      scaleObjective (dualMass β α) (aggregate g q) ρ := by
  have hmass : dualMass β (fun r => ρ*α r) = ρ*dualMass β α := by
    simp only [dualMass, Finset.mul_sum, mul_assoc]
  rw [unnormalizedDualObjective, hmass, aggregate_scale, Matrix.det_smul, Fintype.card_fin,
    Real.log_mul (pow_ne_zero _ hρ.ne') hM.det_pos.ne', Real.log_pow]
  unfold scaleObjective
  ring

/-- Exact scalar deficit and global optimum scale, on the full positive domain. -/
theorem optimal_scale (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s) (M : MatR n) (ρ : ℝ) (hρ : 0 < ρ) :
    scaleObjective s M ρ-scaleObjective s M ((n : ℝ)/s) =
      (n : ℝ)*(ρ*s/(n : ℝ)-1-Real.log (ρ*s/(n : ℝ))) ∧
    scaleObjective s M ((n : ℝ)/s) ≤ scaleObjective s M ρ := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have he : scaleObjective s M ρ-scaleObjective s M ((n : ℝ)/s) =
      (n : ℝ)*(ρ*s/(n : ℝ)-1-Real.log (ρ*s/(n : ℝ))) := by
    simp only [scaleObjective, Real.log_div (mul_ne_zero hρ.ne' hs.ne') hnpos.ne',
      Real.log_mul hρ.ne' hs.ne', Real.log_div hnpos.ne' hs.ne']
    field_simp
    ring
  have hu : 0 < ρ*s/(n : ℝ) := div_pos (mul_pos hρ hs) hnpos
  have hnonneg : 0 ≤ (n : ℝ)*(ρ*s/(n : ℝ)-1-Real.log (ρ*s/(n : ℝ))) :=
    mul_nonneg hnpos.le (by linarith only [Real.log_le_sub_one_of_pos hu])
  exact ⟨he, by linarith only [he, hnonneg]⟩

theorem normalize_unnormalized (hn : 1 ≤ n) {g q : Fin N → V n} {β α : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g β c A) (hd : UnnormalizedDualFeasible g α q) :
    DualFeasible g β (fun r => ((n : ℝ)/dualMass β α)*α r)
      (fun r => ((n : ℝ)/dualMass β α) • q r) := by
  have hs := (unnormalized_mass_positive hn hp hd).2.2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hscaled := unnormalized_scale hd ((n : ℝ)/dualMass β α) (div_pos hnpos hs)
  refine ⟨hscaled.cone, hscaled.balance, ?_, hscaled.positive⟩
  calc
    _ = ((n : ℝ)/dualMass β α)*dualMass β α := by
      simp only [dualMass, Finset.mul_sum, mul_assoc]
    _ = (n : ℝ) := div_mul_cancel₀ _ hs.ne'

theorem unnormalized_weak_duality {g q : Fin N → V n} {β α : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g β c A) (hd : UnnormalizedDualFeasible g α q) :
    Real.log A.det ≤ unnormalizedDualObjective g β α q := by
  have hconj := logdet_conjugate_bound (aggregate g q) A hd.positive hp.1
  have htrace := unnormalized_trace_bound hp hd
  unfold unnormalizedDualObjective
  linarith only [hconj, htrace]

/-- The unnormalized minimum is attained at the same actual optimum with normalized mass n. -/
theorem unnormalized_dual_attainment (hn : 1 ≤ n) (g : Fin N → V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hP : IsConvexBody (constraintPolytope g β)) :
    ∃ c A α q, IsMaxDet (constraintPolytope g β) c A ∧ UnnormalizedDualFeasible g α q ∧
      dualMass β α = (n : ℝ) ∧ unnormalizedDualObjective g β α q = Real.log A.det ∧
      (∀ α' q', UnnormalizedDualFeasible g α' q' →
        unnormalizedDualObjective g β α q ≤ unnormalizedDualObjective g β α' q') := by
  obtain ⟨c, A, α, q, hmax, hpr, hd, hM, _, hvalue⟩ := (exact_duality hn g β hg hP).1
  have he : unnormalizedDualObjective g β α q = Real.log A.det := by
    rw [unnormalizedDualObjective, show dualMass β α = (n : ℝ) from hd.1.normalization]
    linarith only [hvalue]
  refine ⟨c, A, α, q, hmax, ⟨hd.1.cone, hd.1.balance, hd.1.positive⟩, hd.1.normalization, he, ?_⟩
  intro α' q' hd'
  rw [he]
  exact unnormalized_weak_duality hpr.1 hd'

/-- A genuine positive-radius spherical seed is strictly feasible for every nonzero facet. -/
theorem strictly_feasible_ball_seed (hn : 1 ≤ n) (g : Fin N → V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hP : IsConvexBody (constraintPolytope g β)) :
    ∃ c : V n, ∃ ε : ℝ, 0 < ε ∧
      (ε • (1 : MatR n)).PosDef ∧
      (∀ r, ⟪g r,c⟫+‖Matrix.toEuclideanCLM (𝕜 := ℝ) (ε • (1 : MatR n)) (g r)‖ < β r) ∧
      Metric.closedBall c ε ⊆ constraintPolytope g β := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨c, ε, hε, hball⟩ := Khachiyan.exists_positive_ball_subset hP
  have hp : PrimalFeasible g β c (ε • (1 : MatR n)) := by
    apply (primalFeasible_iff_containment _ _ _ _).mpr
    exact ⟨Matrix.PosDef.one.smul hε, by rw [Applications.scalar_ball_ellipsoid c ε hε]; exact hball⟩
  refine ⟨c, ε/2, half_pos hε, Matrix.PosDef.one.smul (half_pos hε), ?_, ?_⟩
  · intro r
    have hsupport := hp.2 r
    simp only [Certificate.matrix_action_smul, map_one, ContinuousLinearMap.one_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos hε] at hsupport
    rw [Certificate.matrix_action_smul, map_one, ContinuousLinearMap.one_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    nlinarith only [hsupport, mul_pos hε (norm_pos_iff.mpr (hg r))]
  · exact (Metric.closedBall_subset_closedBall (by linarith : ε/2 ≤ ε)).trans hball

end SharpCut.Optimization
