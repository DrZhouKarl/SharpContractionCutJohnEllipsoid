import SharpCut.Optimization.Certificate
import SharpCut.Determinant.UpperBound

/-! # Exact SOC pairings and the positive matrix divergence -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Optimization
variable {n N : ℕ}

def coneHeight (g : Fin N → V n) (beta : Fin N → ℝ) (c : V n) (r : Fin N) : ℝ :=
  beta r-⟪g r, c⟫

def conePairing (g : Fin N → V n) (beta alpha : Fin N → ℝ) (q : Fin N → V n)
    (c : V n) (A : MatR n) (r : Fin N) : ℝ :=
  alpha r*coneHeight g beta c r-⟪q r, Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫

def coneGap (g : Fin N → V n) (beta alpha : Fin N → ℝ) (q : Fin N → V n) (c : V n) (A : MatR n) : ℝ :=
  ∑ r, conePairing g beta alpha q c A r

def matchingMatrix (A M : MatR n) : MatR n := CFC.sqrt M*A*CFC.sqrt M
def matrixDivergence (Y : MatR n) : ℝ := Y.trace-(n : ℝ)-Real.log Y.det
def pairDivergence (A M : MatR n) : ℝ := matrixDivergence (matchingMatrix A M)
def dualityGap (A M : MatR n) : ℝ := -Real.log M.det-Real.log A.det

theorem sqrt_posDef (M : MatR n) (hM : M.PosDef) : (CFC.sqrt M).PosDef := by
  rw [CFC.sqrt_eq_rpow]
  exact Khachiyan.Spectral.rpow_posDef hM _

theorem matchingMatrix_posDef (A M : MatR n) (hA : A.PosDef) (hM : M.PosDef) :
    (matchingMatrix A M).PosDef := by
  have hs := sqrt_posDef M hM
  have h := hA.conjTranspose_mul_mul_same hs.mulVec_injective
  rwa [hs.isHermitian.eq] at h

theorem matchingMatrix_trace (A M : MatR n) (hM : M.PosDef) :
    (matchingMatrix A M).trace = (A*M).trace := by
  rw [matchingMatrix, Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg,
    Matrix.trace_mul_comm]

theorem matchingMatrix_det (A M : MatR n) (hM : M.PosDef) :
    (matchingMatrix A M).det = A.det*M.det := by
  calc
    _ = A.det*(CFC.sqrt M*CFC.sqrt M).det := by
      simp only [matchingMatrix, Matrix.det_mul]; ring
    _ = _ := by rw [CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg]

theorem matrixDivergence_nonneg (Y : MatR n) (hY : Y.PosDef) : 0 ≤ matrixDivergence Y := by
  have h := Determinant.posDef_logdet_trace Y hY
  unfold matrixDivergence
  linarith only [h]

theorem pairDivergence_nonneg (A M : MatR n) (hA : A.PosDef) (hM : M.PosDef) :
    0 ≤ pairDivergence A M := matrixDivergence_nonneg _ (matchingMatrix_posDef A M hA hM)

theorem conePairing_nonneg {g q : Fin N → V n} {beta alpha : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g beta c A) (hd : DualFeasible g beta alpha q) (r : Fin N) :
    0 ≤ conePairing g beta alpha q c A r := by
  have h : ⟪q r, Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ ≤ alpha r*(beta r-⟪g r, c⟫) := by
    calc
      _ ≤ ‖q r‖*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ := real_inner_le_norm _ _
      _ ≤ alpha r*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ :=
        mul_le_mul_of_nonneg_right (hd.cone r) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hp.2 r]) (dual_alpha_nonneg hd r)
  unfold conePairing coneHeight
  exact sub_nonneg.mpr h

theorem coneGap_nonneg {g q : Fin N → V n} {beta alpha : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g beta c A) (hd : DualFeasible g beta alpha q) :
    0 ≤ coneGap g beta alpha q c A := Finset.sum_nonneg (fun r hr => conePairing_nonneg hp hd r)

theorem coneGap_trace {g q : Fin N → V n} {beta alpha : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g beta c A) (hd : DualFeasible g beta alpha q) :
    coneGap g beta alpha q c A = (n : ℝ)-(A*aggregate g q).trace := by
  have hb : (∑ r, alpha r*⟪g r, c⟫) = 0 := by
    have h := congrArg (fun u : V n => ⟪u, c⟫) hd.balance
    simpa only [sum_inner, real_inner_smul_left, inner_zero_left] using h
  have ht : (A*aggregate g q).trace = ∑ r, ⟪q r, Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ := by
    simp only [aggregate, Matrix.mul_sum, Matrix.trace_sum, trace_mul_symmetricOuter hp.1.isHermitian.isSymm]
  simp only [coneGap, conePairing, coneHeight, mul_sub, Finset.sum_sub_distrib, hd.normalization, hb,
    ht, sub_zero]

theorem normalized_pair_gap {g q : Fin N → V n} {beta alpha : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g beta c A) (hd : DualFeasible g beta alpha q) :
    dualityGap A (aggregate g q) = coneGap g beta alpha q c A+pairDivergence A (aggregate g q) := by
  rw [coneGap_trace hp hd]
  unfold dualityGap pairDivergence matrixDivergence
  rw [matchingMatrix_trace _ _ hd.positive, matchingMatrix_det _ _ hd.positive,
    Real.log_mul hp.1.det_pos.ne' hd.positive.det_pos.ne']
  ring

theorem normalized_pair_gap_nonneg {g q : Fin N → V n} {beta alpha : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g beta c A) (hd : DualFeasible g beta alpha q) :
    0 ≤ dualityGap A (aggregate g q) := by
  rw [normalized_pair_gap hp hd]
  exact add_nonneg (coneGap_nonneg hp hd) (pairDivergence_nonneg _ _ hp.1 hd.positive)

theorem coneGap_zero_iff {g q : Fin N → V n} {beta alpha : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g beta c A) (hd : DualFeasible g beta alpha q) :
    coneGap g beta alpha q c A = 0 ↔ ∀ r, conePairing g beta alpha q c A r = 0 := by
  have h := Finset.sum_eq_zero_iff_of_nonneg (fun r (_ : r ∈ Finset.univ) => conePairing_nonneg hp hd r)
  simpa only [coneGap, Finset.mem_univ, forall_true_left] using h

end SharpCut.Optimization
