import SharpCut.Optimization.Exact.Theorem
import SharpCut.Applications.Stopping
import SharpCut.Certificate.Feasibility
import Mathlib.Topology.Order.Compact

/-! # Attained determinant extrema for the full and fixed-weight normalized dual

The fixed-weight feasible set is open at the positive-definiteness boundary.
We maximize on its compact positive-semidefinite closure and use a genuine
positive certificate to show that the maximizer lies in the original set.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
open Matrix Set MeasureTheory
namespace SharpCut.Optimization
variable {n N : ℕ}

def dualDeterminants (g : Fin N → V n) (β : Fin N → ℝ) : Set ℝ :=
  {d | ∃ α q, DualFeasible g β α q ∧ d = (aggregate g q).det}

def dualDeterminantMaximum (g : Fin N → V n) (β : Fin N → ℝ) : ℝ :=
  sSup (dualDeterminants g β)

def fixedDualDeterminants (g : Fin N → V n) (β α : Fin N → ℝ) : Set ℝ :=
  {d | ∃ q, DualFeasible g β α q ∧ d = (aggregate g q).det}

def fixedDualDeterminantMaximum (g : Fin N → V n) (β α : Fin N → ℝ) : ℝ :=
  sSup (fixedDualDeterminants g β α)

theorem dualOptimal_isGreatest {g q : Fin N → V n} {β α : Fin N → ℝ}
    (hd : DualOptimal g β α q) :
    IsGreatest (dualDeterminants g β) (aggregate g q).det := by
  refine ⟨⟨α, q, hd.1, rfl⟩, ?_⟩
  rintro d ⟨α', q', hd', rfl⟩
  exact (Real.log_le_log_iff hd'.positive.det_pos hd.1.positive.det_pos).mp (hd.2 α' q' hd')

theorem dual_determinant_maximum_attained (hn : 1 ≤ n) (g : Fin N → V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hP : IsConvexBody (constraintPolytope g β)) :
    ∃ c A α q, IsMaxDet (constraintPolytope g β) c A ∧ DualFeasible g β α q ∧
      IsGreatest (dualDeterminants g β) (aggregate g q).det ∧
      dualDeterminantMaximum g β = (aggregate g q).det ∧
      (aggregate g q).det = A.det⁻¹ := by
  obtain ⟨c, A, α, q, hmax, _, hd, hM, _, _⟩ := (exact_duality hn g β hg hP).1
  have hgreat := dualOptimal_isGreatest hd
  refine ⟨c, A, α, q, hmax, hd.1, hgreat, hgreat.csSup_eq, ?_⟩
  rw [hM, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]

theorem continuous_aggregate (g : Fin N → V n) : Continuous (aggregate g) := by
  unfold aggregate symmetricOuter
  fun_prop

theorem fixed_dual_determinant_attained {g q₀ : Fin N → V n} {β α : Fin N → ℝ}
    (hseed : DualFeasible g β α q₀) :
    ∃ q, DualFeasible g β α q ∧
      IsGreatest (fixedDualDeterminants g β α) (aggregate g q).det ∧
      fixedDualDeterminantMaximum g β α = (aggregate g q).det ∧
      (aggregate g q₀).det ≤ (aggregate g q).det := by
  let balls : Set (Fin N → V n) := Set.pi Set.univ (fun r => Metric.closedBall 0 (α r))
  let S : Set (Fin N → V n) := balls ∩ {q | (aggregate g q).PosSemidef}
  have hc : IsCompact balls := isCompact_univ_pi (fun r => isCompact_closedBall 0 (α r))
  have hclosed : IsClosed {q | (aggregate g q).PosSemidef} :=
    Matrix.posSemidef_is_closed.preimage (continuous_aggregate g)
  have hcompact : IsCompact S := hc.inter_right hclosed
  have hball (q : Fin N → V n) : q ∈ balls ↔ ∀ r, ‖q r‖ ≤ α r := by
    simp [balls, Set.mem_pi, Metric.mem_closedBall, dist_zero_right]
  have hq₀ : q₀ ∈ S := ⟨(hball q₀).mpr hseed.cone, hseed.positive.posSemidef⟩
  have hcont : Continuous (fun q => (aggregate g q).det) := (continuous_aggregate g).matrix_det
  obtain ⟨q, hq, hmax⟩ := hcompact.exists_isMaxOn ⟨q₀, hq₀⟩ hcont.continuousOn
  have hlower : (aggregate g q₀).det ≤ (aggregate g q).det := hmax hq₀
  have hpos : 0 < (aggregate g q).det := hseed.positive.det_pos.trans_le hlower
  have hd : DualFeasible g β α q :=
    ⟨(hball q).mp hq.1, hseed.balance, hseed.normalization,
      hq.2.posDef_iff_det_ne_zero.mpr hpos.ne'⟩
  have hgreat : IsGreatest (fixedDualDeterminants g β α) (aggregate g q).det := by
    refine ⟨⟨q, hd, rfl⟩, ?_⟩
    rintro d ⟨q', hd', rfl⟩
    exact hmax ⟨(hball q').mpr hd'.cone, hd'.positive.posSemidef⟩
  exact ⟨q, hd, hgreat, hgreat.csSup_eq, hlower⟩

theorem fixed_dual_le_full {g q₀ : Fin N → V n} {β α : Fin N → ℝ}
    (hseed : DualFeasible g β α q₀) (hn : 1 ≤ n) (hg : ∀ r, g r ≠ 0)
    (hP : IsConvexBody (constraintPolytope g β)) :
    (aggregate g q₀).det ≤ fixedDualDeterminantMaximum g β α ∧
      fixedDualDeterminantMaximum g β α ≤ dualDeterminantMaximum g β := by
  obtain ⟨q, hd, _, hfixed, hlow⟩ := fixed_dual_determinant_attained hseed
  obtain ⟨c, A, α', q', _, _, hgreat, hfull, _⟩ := dual_determinant_maximum_attained hn g β hg hP
  rw [hfixed, hfull]
  exact ⟨hlow, hgreat.2 ⟨α, q, hd, rfl⟩⟩

theorem dual_maximum_volume_identity [NeZero n] (hn : 1 ≤ n) (g : Fin N → V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hP : IsConvexBody (constraintPolytope g β)) :
    0 < dualDeterminantMaximum g β ∧
      (maxEllipsoidVolume (constraintPolytope g β)).toReal / (volume (unitBall n)).toReal =
        (dualDeterminantMaximum g β)⁻¹ := by
  obtain ⟨c, A, α, q, hmax, hd, _, hD, hdet⟩ := dual_determinant_maximum_attained hn g β hg hP
  have hκpos := Khachiyan.unitBall_volume_pos (n := n)
  have hκfin : volume (unitBall n) < ∞ := (isCompact_closedBall (0 : V n) 1).measure_lt_top
  have hκ : 0 < (volume (unitBall n)).toReal := ENNReal.toReal_pos_iff.mpr ⟨hκpos, hκfin⟩
  have hvol := congrArg ENNReal.toReal hmax.maxEllipsoidVolume_eq_det
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hmax.posDef.det_pos.le] at hvol
  rw [hD, hdet, inv_inv]
  exact ⟨inv_pos.mpr hmax.posDef.det_pos, (div_eq_iff hκ.ne').mpr hvol⟩

end SharpCut.Optimization
