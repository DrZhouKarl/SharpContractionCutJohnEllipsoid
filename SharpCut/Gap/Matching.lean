import SharpCut.Gap.ScalarCoercivity
import SharpCut.Gap.FrobeniusSpectral

/-! # Matrix matching from the actual normalized primal-dual gap -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Gap
open Optimization
variable {n N : ℕ}

theorem eigenvalue_divergence_le (Y : MatR n) (hY : Y.PosDef) (i : Fin n) :
    scalarDivergence (hY.isHermitian.eigenvalues i) ≤ matrixDivergence Y := by
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) => scalarDivergence_nonneg (hY.eigenvalues_pos j)) (Finset.mem_univ i)
  rwa [← matrixDivergence_spectral Y hY] at h

theorem small_divergence_eigenvalues (Y : MatR n) (hY : Y.PosDef) (hsmall : matrixDivergence Y ≤ 1/4) :
    ∀ i, hY.isHermitian.eigenvalues i < 2 := by
  intro i
  by_contra h
  have hl := scalarDivergence_gt_quarter (le_of_not_gt h)
  have hu := eigenvalue_divergence_le Y hY i
  linarith only [hl, hu, hsmall]

theorem frobenius_divergence_square (Y : MatR n) (hY : Y.PosDef) (hsmall : matrixDivergence Y ≤ 1/4) :
    (frobeniusNorm (Y-1))^2 ≤ 4*matrixDivergence Y := by
  have he := small_divergence_eigenvalues Y hY hsmall
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i hi => scalarDivergence_quadratic (hY.eigenvalues_pos i) (he i).le)
  rw [← frobenius_shift_spectral Y hY.isHermitian, ← Finset.mul_sum,
    ← matrixDivergence_spectral Y hY] at h
  exact h

theorem frobenius_divergence_control (Y : MatR n) (hY : Y.PosDef) (hsmall : matrixDivergence Y ≤ 1/4) :
    frobeniusNorm (Y-1) ≤ 2*Real.sqrt (matrixDivergence Y) := by
  have h := frobenius_divergence_square Y hY hsmall
  have hd := matrixDivergence_nonneg Y hY
  have hf : 0 ≤ frobeniusNorm (Y-1) := Real.sqrt_nonneg _
  have hs := Real.sq_sqrt hd
  have hn := Real.sqrt_nonneg (matrixDivergence Y)
  nlinarith only [h, hf, hs, hn]

/-- Lemma 4.2: G>=0 and every spectral restriction are derived from normalized feasibility. -/
theorem matrix_matching {g q : Fin N → V n} {beta alpha : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g beta c A) (hd : DualFeasible g beta alpha q)
    (hsmall : dualityGap A (aggregate g q) ≤ 1/4) :
    frobeniusNorm (matchingMatrix A (aggregate g q)-1) ≤ 2*Real.sqrt (dualityGap A (aggregate g q)) := by
  have hY := matchingMatrix_posDef A (aggregate g q) hp.1 hd.positive
  have he := normalized_pair_gap hp hd
  have hc := coneGap_nonneg hp hd
  have hD : matrixDivergence (matchingMatrix A (aggregate g q)) ≤ dualityGap A (aggregate g q) := by
    change pairDivergence A (aggregate g q) ≤ dualityGap A (aggregate g q)
    linarith only [he, hc]
  have h := frobenius_divergence_control _ hY (hD.trans hsmall)
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hD) (by norm_num))

end SharpCut.Gap
