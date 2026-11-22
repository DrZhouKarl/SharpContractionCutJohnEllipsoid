import SharpCut.Certificate.Polar
import SharpCut.Optimization.Certificate

/-!
# Explicit normalized dual feasibility after one common left polar rotation

The new cut occupies zero in Fin (N+1); every original contact is reindexed by
Fin.succ. Feasibility is proved from the frame, not stored as an assumed field.
The sharp determinant lower bound remains a separate theorem.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

def cutNormals (F : JohnFrame n N) (v : V n) : Fin (N+1) → V n := Fin.cases v F.contact
def cutOffsets (N : ℕ) : Fin (N+1) → ℝ := Fin.cases 0 (fun _ => 1)
def cutAlpha (F : JohnFrame n N) (v : V n) : Fin (N+1) → ℝ :=
  Fin.cases (cutWeight n) (originalWeight F v)
def rotatedVectors (F : JohnFrame n N) (v : V n) (U : MatR n) : Fin (N+1) → V n :=
  Fin.cases (cutWeight n • Matrix.toEuclideanCLM (𝕜 := ℝ) U v)
    (fun i => originalWeight F v i • Matrix.toEuclideanCLM (𝕜 := ℝ) U (lorentzDirection v (F.contact i)))
def rawAggregate {k : ℕ} (g q : Fin k → V n) : MatR n := ∑ i, cross (q i) (g i)

theorem cut_polytope (F : JohnFrame n N) (v : V n) :
    Optimization.constraintPolytope (cutNormals F v) (cutOffsets N) =
      F.polytope ∩ centralHalfspace 0 v := by
  ext x
  simp [Optimization.constraintPolytope, cutNormals, cutOffsets,
    JohnFrame.polytope, centralHalfspace, Fin.forall_fin_succ, and_comm]

theorem aggregate_eq_symRaw {k : ℕ} (g q : Fin k → V n) :
    Optimization.aggregate g q = (1/2 : ℝ) • (rawAggregate g q+(rawAggregate g q)ᵀ) := by
  unfold Optimization.aggregate Optimization.symmetricOuter rawAggregate cross
  simp only [Matrix.transpose_sum, Matrix.transpose_vecMulVec, smul_add, Finset.smul_sum,
    Finset.sum_add_distrib]

theorem raw_rotated_aggregate (F : JohnFrame n N) (v : V n) (U : MatR n) :
    rawAggregate (cutNormals F v) (rotatedVectors F v U) = U*(unrotatedQ F v)ᵀ := by
  have ho : (outer v)ᵀ = outer v := by
    ext i j; simp only [Khachiyan.outer_apply, Matrix.transpose_apply]; ring
  simp only [rawAggregate, Fin.sum_univ_succ, cutNormals, rotatedVectors,
    Fin.cases_zero, Fin.cases_succ, cross_smul_left]
  simp only [unrotatedQ, Matrix.transpose_add, Matrix.transpose_sum, Matrix.transpose_smul,
    cross_transpose, ho, Matrix.mul_add, Matrix.mul_sum, Matrix.mul_smul,
    mul_cross, ← cross_self]
  rw [add_comm]

theorem rotated_aggregate_eq_polar (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    Optimization.aggregate (cutNormals F v)
      (rotatedVectors F v (polarRotation (unrotatedQ F v))) = polarMatrix (unrotatedQ F v) := by
  have hQ := unrotatedQ_det_pos F hn v hv
  have hs : (polarMatrix (unrotatedQ F v))ᵀ = polarMatrix (unrotatedQ F v) :=
    (polarMatrix_posDef hQ).isHermitian.isSymm
  rw [aggregate_eq_symRaw, raw_rotated_aggregate, polarRotation_aggregate hQ, hs]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

theorem explicit_dual_feasible (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    Optimization.DualFeasible (cutNormals F v) (cutOffsets N) (cutAlpha F v)
      (rotatedVectors F v (polarRotation (unrotatedQ F v))) := by
  have hQ := unrotatedQ_det_pos F hn v hv
  have ht : 0 < cutWeight n := by unfold cutWeight; linarith [(inverseDimension_bounds hn).1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    refine Fin.cases ?_ (fun i => ?_) r
    · simp only [rotatedVectors, cutAlpha, Fin.cases_zero, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht, polarRotation_norm hQ, hv, mul_one]
      exact le_rfl
    · have hi := (originalWeight_lower F v hn hv i).2
      simp only [rotatedVectors, cutAlpha, Fin.cases_succ, norm_smul, Real.norm_eq_abs,
        abs_of_pos hi, polarRotation_norm hQ, lorentzDirection_unit hn v (F.contact i) hv (F.contact_unit i), mul_one]
      exact le_rfl
  · simp only [cutNormals, cutAlpha, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
    simpa only [add_comm] using balanced_normals F v
  · simp only [cutOffsets, cutAlpha, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
      mul_zero, mul_one, zero_add, originalWeight_sum]
  · rw [rotated_aggregate_eq_polar F hn v hv]
    exact polarMatrix_posDef hQ

/-- Every feasible cut ellipsoid receives a proved instance-specific determinant bound. -/
theorem frame_volume_certificate (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    {c : V n} {A : MatR n} (hp : IsFeasible (F.polytope ∩ centralHalfspace 0 v) c A) :
    (A*polarMatrix (unrotatedQ F v)).trace ≤ (n : ℝ) ∧ A.det ≤ 1/(unrotatedQ F v).det := by
  have hpr : Optimization.PrimalFeasible (cutNormals F v) (cutOffsets N) c A := by
    apply (Optimization.primalFeasible_iff_containment _ _ _ _).mpr
    rwa [cut_polytope]
  have h := Optimization.volume_certificate hpr (explicit_dual_feasible F hn v hv)
  rw [rotated_aggregate_eq_polar F hn v hv, polarMatrix_det (unrotatedQ_det_pos F hn v hv)] at h
  exact h

end SharpCut.Certificate
