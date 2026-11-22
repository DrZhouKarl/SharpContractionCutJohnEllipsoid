import SharpCut.Gap.Matching
import SharpCut.Gap.VolumeInterpretation

/-! # Exact Lorentz cone residuals and quantitative complementarity -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Gap
open Optimization
variable {n N : ℕ}

theorem cone_sum_of_squares (α τ : ℝ) (q x : V n) :
    2*α*τ*(α*τ-⟪q, x⟫) = ‖α • x-τ • q‖^2+
      α^2*(τ^2-‖x‖^2)+τ^2*(α^2-‖q‖^2) := by
  rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right]
  have hc : ⟪x, q⟫ = ⟪q, x⟫ := real_inner_comm _ _
  rw [hc]
  ring

theorem cone_normalized_residual (α τ : ℝ) (q x : V n) (hα : 0 < α) (hτ : 0 < τ)
    (hq : ‖q‖ ≤ α) (hx : ‖x‖ ≤ τ) :
    α*τ*‖τ⁻¹ • x-α⁻¹ • q‖^2 ≤ 2*(α*τ-⟪q, x⟫) := by
  have hx2 := (sq_le_sq₀ (norm_nonneg x) hτ.le).mpr hx
  have hq2 := (sq_le_sq₀ (norm_nonneg q) hα.le).mpr hq
  have hs := cone_sum_of_squares α τ q x
  have hn1 : 0 ≤ α^2*(τ^2-‖x‖^2) := mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hx2)
  have hn2 : 0 ≤ τ^2*(α^2-‖q‖^2) := mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hq2)
  have hd : (α*τ) • (τ⁻¹ • x-α⁻¹ • q) = α • x-τ • q := by
    rw [smul_sub, smul_smul, smul_smul]
    have h1 : α*τ*τ⁻¹ = α := by rw [mul_assoc, mul_inv_cancel₀ hτ.ne', mul_one]
    have h2 : α*τ*α⁻¹ = τ := by rw [mul_right_comm, mul_inv_cancel₀ hα.ne', one_mul]
    rw [h1, h2]
  have hb : ‖(α*τ) • (τ⁻¹ • x-α⁻¹ • q)‖^2 ≤ 2*α*τ*(α*τ-⟪q, x⟫) := by
    rw [hd]
    linarith only [hs, hn1, hn2]
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hb
  have hmul : (α*τ)*(α*τ*‖τ⁻¹ • x-α⁻¹ • q‖^2) ≤ (α*τ)*(2*(α*τ-⟪q, x⟫)) := by
    nlinarith only [hb]
  exact le_of_mul_le_mul_left hmul (mul_pos hα hτ)

theorem coneHeight_pos_of_normal {g : Fin N → V n} {beta : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g beta c A) (r : Fin N) (hg : g r ≠ 0) : 0 < coneHeight g beta c r := by
  have hn : Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r) ≠ 0 := Khachiyan.normalized_normal_ne_zero hp.1 hg
  have hh : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ ≤ coneHeight g beta c r := by
    unfold coneHeight
    linarith [hp.2 r]
  exact (norm_pos_iff.mpr hn).trans_le hh

def directionResidualSum (g : Fin N → V n) (beta alpha : Fin N → ℝ) (q : Fin N → V n)
    (c : V n) (A : MatR n) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r => 0 < alpha r), alpha r*coneHeight g beta c r*
    ‖(coneHeight g beta c r)⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)-(alpha r)⁻¹ • q r‖^2

theorem directionResidualSum_bound {g q : Fin N → V n} {beta alpha : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g beta c A) (hd : DualFeasible g beta alpha q) (hg : ∀ r, g r ≠ 0) :
    directionResidualSum g beta alpha q c A ≤ 2*coneGap g beta alpha q c A := by
  classical
  let s := Finset.univ.filter (fun r => 0 < alpha r)
  have hpoint (r : Fin N) (hr : r ∈ s) : alpha r*coneHeight g beta c r*
      ‖(coneHeight g beta c r)⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)-(alpha r)⁻¹ • q r‖^2 ≤
        2*conePairing g beta alpha q c A r := by
    have ha : 0 < alpha r := (Finset.mem_filter.mp hr).2
    have ht := coneHeight_pos_of_normal hp r (hg r)
    have hx : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ ≤ coneHeight g beta c r := by
      unfold coneHeight; linarith [hp.2 r]
    exact cone_normalized_residual _ _ _ _ ha ht (hd.cone r) hx
  have hsum := Finset.sum_le_sum (fun r hr => hpoint r hr)
  have hsubset : s ⊆ Finset.univ := Finset.filter_subset _ _
  have hcone : (∑ r ∈ s, conePairing g beta alpha q c A r) ≤ coneGap g beta alpha q c A :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun r hr hrs => conePairing_nonneg hp hd r)
  change _ ≤ 2*(∑ r, conePairing g beta alpha q c A r)
  calc
    _ ≤ ∑ r ∈ s, 2*conePairing g beta alpha q c A r := hsum
    _ = 2*(∑ r ∈ s, conePairing g beta alpha q c A r) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hcone (by norm_num)

theorem pairDivergence_symm (A M : MatR n) (hA : A.PosDef) (hM : M.PosDef) :
    pairDivergence M A = pairDivergence A M := by
  unfold pairDivergence matrixDivergence
  rw [matchingMatrix_trace _ _ hA, matchingMatrix_trace _ _ hM, matchingMatrix_det _ _ hA,
    matchingMatrix_det _ _ hM, Matrix.trace_mul_comm M A, mul_comm M.det A.det]

/-- Proposition 9.1: exact cone residual and both symmetric shape-matching estimates. -/
theorem quantitative_complementarity {g q : Fin N → V n} {beta alpha : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g beta c A) (hd : DualFeasible g beta alpha q) (hg : ∀ r, g r ≠ 0)
    {ε : ℝ} (hgap : dualityGap A (aggregate g q) ≤ ε) (hε : ε ≤ 1/4) :
    frobeniusNorm (matchingMatrix A (aggregate g q)-1) ≤ 2*Real.sqrt ε ∧
    directionResidualSum g beta alpha q c A ≤ 2*ε ∧
    frobeniusNorm (matchingMatrix (aggregate g q) A-1) ≤ 2*Real.sqrt ε := by
  have h := matrix_matching hp hd (hgap.trans hε)
  have he := normalized_pair_gap hp hd
  have hc := coneGap_nonneg hp hd
  have hD := pairDivergence_nonneg A (aggregate g q) hp.1 hd.positive
  have hdg : pairDivergence A (aggregate g q) ≤ dualityGap A (aggregate g q) := by linarith only [he, hc]
  have hcg : coneGap g beta alpha q c A ≤ dualityGap A (aggregate g q) := by linarith only [he, hD]
  refine ⟨h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hgap) (by norm_num)), ?_, ?_⟩
  · exact (directionResidualSum_bound hp hd hg).trans (mul_le_mul_of_nonneg_left (hcg.trans hgap) (by norm_num))
  · have hh := frobenius_divergence_control (matchingMatrix (aggregate g q) A)
      (matchingMatrix_posDef _ _ hd.positive hp.1)
      (show matrixDivergence (matchingMatrix (aggregate g q) A) ≤ 1/4 by
        change pairDivergence (aggregate g q) A ≤ 1/4
        rw [pairDivergence_symm _ _ hp.1 hd.positive]
        exact hdg.trans (hgap.trans hε))
    have hdε : matrixDivergence (matchingMatrix (aggregate g q) A) ≤ ε := by
      change pairDivergence (aggregate g q) A ≤ ε
      rw [pairDivergence_symm _ _ hp.1 hd.positive]
      exact hdg.trans hgap
    exact hh.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdε) (by norm_num))

end SharpCut.Gap
