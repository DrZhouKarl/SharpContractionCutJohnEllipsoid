import SharpCut.Optimization.Gaps
import SharpCut.Geometry.AxialCoordinates

/-! # The exact zero set of the positive matrix divergence -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Gap
open Optimization
variable {n : ℕ}

def scalarDivergence (t : ℝ) : ℝ := t-1-Real.log t

theorem scalarDivergence_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ scalarDivergence t := by
  have h := Real.log_le_sub_one_of_pos ht
  unfold scalarDivergence
  linarith only [h]

theorem scalarDivergence_zero_iff {t : ℝ} (ht : 0 < t) : scalarDivergence t = 0 ↔ t = 1 := by
  constructor
  · intro h
    by_contra hn
    have hs := Real.log_lt_sub_one_of_pos ht hn
    unfold scalarDivergence at h
    linarith only [h, hs]
  · intro h
    rw [h]
    norm_num [scalarDivergence]

theorem matrixDivergence_spectral (Y : MatR n) (hY : Y.PosDef) :
    matrixDivergence Y = ∑ i, scalarDivergence (hY.isHermitian.eigenvalues i) := by
  have hl : Real.log Y.det = ∑ i, Real.log (hY.isHermitian.eigenvalues i) := by
    rw [hY.isHermitian.det_eq_prod_eigenvalues]
    exact Real.log_prod (fun i hi => (hY.eigenvalues_pos i).ne')
  have ht := Khachiyan.Spectral.trace_eq_sum hY.isHermitian
  unfold matrixDivergence scalarDivergence
  rw [hl, ht]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

theorem eigenvector_action (Y : MatR n) (hY : Y.IsHermitian) (i : Fin n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) Y (hY.eigenvectorBasis i) =
      hY.eigenvalues i • hY.eigenvectorBasis i := by
  apply WithLp.ofLp_injective 2
  simpa only [Khachiyan.matrix_action_ofLp, WithLp.ofLp_smul] using hY.mulVec_eigenvectorBasis i

theorem matrixDivergence_zero_iff (Y : MatR n) (hY : Y.PosDef) : matrixDivergence Y = 0 ↔ Y = 1 := by
  constructor
  · intro h
    rw [matrixDivergence_spectral Y hY] at h
    have he (i : Fin n) : hY.isHermitian.eigenvalues i = 1 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i (_ : i ∈ Finset.univ) => scalarDivergence_nonneg (hY.eigenvalues_pos i))).mp h i (Finset.mem_univ i)
      exact (scalarDivergence_zero_iff (hY.eigenvalues_pos i)).mp hz
    let b := hY.isHermitian.eigenvectorBasis
    apply Geometry.inBasis_injective b
    rw [Geometry.inBasis_one]
    ext i j
    rw [Geometry.inBasis_entry, eigenvector_action Y hY.isHermitian j, he j, one_smul]
    simpa only [Matrix.one_apply] using (orthonormal_iff_ite.mp b.orthonormal i j)
  · intro h
    rw [h]
    norm_num [matrixDivergence, Matrix.trace_one]

theorem matchingMatrix_one_iff (A M : MatR n) (hM : M.PosDef) :
    matchingMatrix A M = 1 ↔ A = M⁻¹ := by
  have hS := sqrt_posDef M hM
  have hu : IsUnit (CFC.sqrt M).det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hs : CFC.sqrt M*CFC.sqrt M = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  constructor
  · intro h
    have he := congrArg (fun B : MatR n => B*(CFC.sqrt M)⁻¹) h
    simp only [matchingMatrix, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.one_mul] at he
    have hm : M*A = 1 := by rw [← hs, Matrix.mul_assoc, he, Matrix.mul_nonsing_inv _ hu]
    exact (Matrix.inv_eq_right_inv hm).symm
  · intro h
    have hi : M⁻¹ = (CFC.sqrt M)⁻¹*(CFC.sqrt M)⁻¹ := by
      apply Matrix.inv_eq_left_inv
      calc
        _ = ((CFC.sqrt M)⁻¹*(CFC.sqrt M)⁻¹)*(CFC.sqrt M*CFC.sqrt M) :=
          congrArg (fun B : MatR n => ((CFC.sqrt M)⁻¹*(CFC.sqrt M)⁻¹)*B) hs.symm
        _ = (CFC.sqrt M)⁻¹*((CFC.sqrt M)⁻¹*CFC.sqrt M)*CFC.sqrt M := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]
    rw [matchingMatrix, h, hi]
    calc
      _ = (CFC.sqrt M*(CFC.sqrt M)⁻¹)*((CFC.sqrt M)⁻¹*CFC.sqrt M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

theorem pairDivergence_zero_iff (A M : MatR n) (hA : A.PosDef) (hM : M.PosDef) :
    pairDivergence A M = 0 ↔ A = M⁻¹ :=
  (matrixDivergence_zero_iff (matchingMatrix A M) (matchingMatrix_posDef A M hA hM)).trans
    (matchingMatrix_one_iff A M hM)

end SharpCut.Gap
