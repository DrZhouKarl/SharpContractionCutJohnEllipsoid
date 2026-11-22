import SharpCut.Certificate.Factorization
import SharpCut.Certificate.ModelDeterminant

/-! # Positive normalization and the exact determinant bridge det Fhat = R_n det Q -/

noncomputable section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

def modelRoot (v : V n) : MatR n := CFC.sqrt (modelF0 v)
def modelNormalizer (v : V n) : MatR n := (modelRoot v)⁻¹
def normalizedCertificate (F : JohnFrame n N) (v : V n) : MatR n :=
  modelNormalizer v*certificateF F v*modelNormalizer v

theorem modelRoot_posDef (hn : 2 ≤ n) (v : V n) : (modelRoot v).PosDef := by
  unfold modelRoot
  rw [CFC.sqrt_eq_rpow]
  exact Khachiyan.Spectral.rpow_posDef (modelF0_posDef hn v) _

theorem modelNormalizer_posDef (hn : 2 ≤ n) (v : V n) : (modelNormalizer v).PosDef :=
  (modelRoot_posDef hn v).inv

theorem modelNormalizer_congruence (hn : 2 ≤ n) (v : V n) :
    modelNormalizer v*modelF0 v*modelNormalizer v = 1 := by
  have hs : modelRoot v*modelRoot v = modelF0 v :=
    CFC.sqrt_mul_sqrt_self _ (modelF0_posDef hn v).posSemidef.nonneg
  have hunit : IsUnit (modelRoot v).det := isUnit_iff_ne_zero.mpr (modelRoot_posDef hn v).det_pos.ne'
  unfold modelNormalizer
  rw [← hs, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul,
    Matrix.mul_nonsing_inv _ hunit]

theorem normalizedCertificate_posDef (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (normalizedCertificate F v).PosDef := by
  have hN := modelNormalizer_posDef hn v
  have hs : (modelNormalizer v)ᴴ = modelNormalizer v := hN.isHermitian
  have h := (certificateF_posDef F hn v hv).conjTranspose_mul_mul_same hN.mulVec_injective
  rwa [hs] at h

theorem normalizedCertificate_det_mul (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) :
    (normalizedCertificate F v).det*(modelF0 v).det = (certificateF F v).det := by
  have h := congrArg Matrix.det (modelNormalizer_congruence hn v)
  simp only [Matrix.det_mul, Matrix.det_one] at h
  calc
    _ = (certificateF F v).det*
        ((modelNormalizer v).det*(modelF0 v).det*(modelNormalizer v).det) := by
      simp only [normalizedCertificate, Matrix.det_mul]
      ring
    _ = _ := by rw [h, mul_one]

theorem normalizedCertificate_det (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (normalizedCertificate F v).det = sharpRatio n*(unrotatedQ F v).det := by
  have h0 := model_determinant_normalization hn v hv
  have hnz := (modelF0_posDef hn v).det_pos.ne'
  apply mul_right_cancel₀ hnz
  calc
    _ = (certificateF F v).det := normalizedCertificate_det_mul F hn v
    _ = (certificateF F v).det*(sharpRatio n*(modelF0 v).det*(certificateD v).det) := by rw [h0, mul_one]
    _ = _ := by rw [ordered_factorization F hn v hv, Matrix.det_mul]; ring

end SharpCut.Certificate
