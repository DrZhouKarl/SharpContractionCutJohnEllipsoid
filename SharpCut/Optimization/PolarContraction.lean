import SharpCut.Optimization.GramContractions

/-! # Optimality among actual common Euclidean contractions -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Optimization
open Certificate
variable {n N : ℕ}

def symmetricPart (A : MatR n) : MatR n := (1/2 : ℝ) • (A+Aᵀ)
def skewPart (A : MatR n) : MatR n := (1/2 : ℝ) • (A-Aᵀ)

theorem symmetric_skew_sum (A : MatR n) : symmetricPart A+skewPart A = A := by
  ext i j
  simp only [symmetricPart, skewPart, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem skewPart_transpose (A : MatR n) : (skewPart A)ᵀ = -skewPart A := by
  ext i j
  simp only [skewPart, Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-- The skew Gram determinant comparison used in the proof of Proposition 10.1. -/
theorem positive_plus_skew_det (A K : MatR n) (hA : A.PosDef) (hK : Kᵀ = -K) : A.det ≤ |(A+K).det| := by
  let S := CFC.sqrt A
  let T := S⁻¹*K*S⁻¹
  have hS : S.PosDef := sqrt_posDef A hA
  have hu : IsUnit S.det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hs : S*S = A := CFC.sqrt_mul_sqrt_self _ hA.posSemidef.nonneg
  have hT : Tᵀ = -T := by
    dsimp only [T]
    simp only [Matrix.transpose_mul, hS.inv.isHermitian.isSymm.eq, hK, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hfac : A+K = S*(1+T)*S := by
    symm
    calc
      _ = S*S+(S*S⁻¹)*K*(S⁻¹*S) := by simp only [T, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hs, Matrix.mul_nonsing_inv S hu, Matrix.nonsing_inv_mul S hu, Matrix.one_mul, Matrix.mul_one]
  have hdet : (A+K).det = S.det*(1+T).det*S.det := by rw [hfac, Matrix.det_mul, Matrix.det_mul]
  have hSdet : S.det^2 = A.det := by
    have h := congrArg Matrix.det hs
    simpa only [Matrix.det_mul, pow_two] using h
  have hTabs : 1 ≤ |(1+T).det| := by
    have h := (skew_gram_identity T hT).2
    nlinarith only [h, sq_abs (1+T).det, abs_nonneg (1+T).det]
  have hmult := mul_le_mul_of_nonneg_left hTabs (sq_nonneg S.det)
  have habs : |(A+K).det| = S.det^2*|(1+T).det| := by
    rw [hdet, abs_mul, abs_mul, abs_of_pos hS.det_pos]
    ring
  rw [habs, ← hSdet]
  nlinarith only [hmult]

/-- Generic determinant upper bound for every Euclidean contraction and positive symmetric part. -/
theorem common_contraction_det (Q R : MatR n) (hQ : 0 < Q.det) (hR : operatorNorm R ≤ 1)
    (hN : (symmetricPart (R*Qᵀ)).PosDef) : (symmetricPart (R*Qᵀ)).det ≤ Q.det := by
  have h := positive_plus_skew_det (symmetricPart (R*Qᵀ)) (skewPart (R*Qᵀ)) hN (skewPart_transpose _)
  rw [symmetric_skew_sum] at h
  have hdetR := (contraction_gram_bounds R hR).2.2.2.2.2
  have hmult := mul_le_mul_of_nonneg_right hdetR hQ.le
  have habs : |(R*Qᵀ).det| = |R.det| * Q.det := by
    rw [Matrix.det_mul, Matrix.det_transpose, abs_mul, abs_of_pos hQ]
  rw [habs] at h
  nlinarith only [h, hmult]

/-- The actual common left polar rotation attains equality with a positive aggregate. -/
theorem common_polar_attainment (Q : MatR n) (hQ : 0 < Q.det) :
    operatorNorm (polarRotation Q) ≤ 1 ∧ (symmetricPart (polarRotation Q*Qᵀ)).PosDef ∧
      (symmetricPart (polarRotation Q*Qᵀ)).det = Q.det := by
  have hM := polarMatrix_posDef hQ
  have hsym : symmetricPart (polarRotation Q*Qᵀ) = polarMatrix Q := by
    rw [polarRotation_aggregate hQ, symmetricPart, hM.isHermitian.isSymm.eq]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  refine ⟨?_, by rw [hsym]; exact hM, by rw [hsym]; exact polarMatrix_det hQ⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [polarRotation_norm hQ u, one_mul]

/-- Full Proposition 10.1, for the explicit frame certificate in every n>=2. -/
theorem common_contraction_optimal (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (∀ R : MatR n, operatorNorm R ≤ 1 → (symmetricPart (R*(unrotatedQ F v)ᵀ)).PosDef →
      (symmetricPart (R*(unrotatedQ F v)ᵀ)).det ≤ (unrotatedQ F v).det) ∧
    operatorNorm (polarRotation (unrotatedQ F v)) ≤ 1 ∧
    (symmetricPart (polarRotation (unrotatedQ F v)*(unrotatedQ F v)ᵀ)).PosDef ∧
    (symmetricPart (polarRotation (unrotatedQ F v)*(unrotatedQ F v)ᵀ)).det = (unrotatedQ F v).det := by
  have hQ := unrotatedQ_det_pos F hn v hv
  exact ⟨fun R hR hN => common_contraction_det _ R hQ hR hN, common_polar_attainment _ hQ⟩

end SharpCut.Optimization
