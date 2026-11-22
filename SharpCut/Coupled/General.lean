import SharpCut.Certificate.DirectCoupling

/-! # The full coupled Cauchy inequality on the actual transverse Euclidean geometry -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Coupled
open Certificate
variable {n N : ℕ}

def sigmaStar (n : ℕ) : ℝ := 2*(1-inverseDimension n)/(2-inverseDimension n+(inverseDimension n)^2)
def traceRemainder (F : JohnFrame n N) (v : V n) : ℝ := sigmaStar n-transverseSigma F v

def forwardQuadratic (F : JohnFrame n N) (v : V n) (Z : MatR n) (q : V n) : ℝ :=
  (Z^2*(transversePerturbation F v+(1/2 : ℝ) • projector v)).trace+
    2*⟪q, Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverseCoupling F v)⟫+
      ((2-inverseDimension n)/4*traceRemainder F v)*‖q‖^2

theorem traceRemainder_nonneg (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    0 ≤ traceRemainder F v := sub_nonneg.mpr (transverseSigma_range F hn v hv).2

theorem couplingL_remainder (F : JohnFrame n N) (v : V n) :
    couplingL F v = (2-inverseDimension n)/2*traceRemainder F v := by
  unfold couplingL traceRemainder sigmaStar
  ring

theorem forwardQuadratic_twice (F : JohnFrame n N) (v : V n) (Z : MatR n) (q : V n) :
    couplingQuadraticTest F v Z q = 2*forwardQuadratic F v Z q := by
  unfold couplingQuadraticTest forwardQuadratic
  rw [couplingL_remainder]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  ring

/-- Lemma 10.2. P is exactly the identity on v-perp, and no commuting restriction is added.
The statement even permits ambient symmetric tests and ambient q; all transverse
m-by-m tests are included through the proved orthonormal coordinate bridge. -/
theorem general_cauchy (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (Z : MatR n) (hZ : Z.IsHermitian) (q : V n) :
    ((Z*transversePerturbation F v).trace+⟪q,transverseCoupling F v⟫)^2 ≤
      transverseSigma F v*forwardQuadratic F v Z q := by
  have h := coupling_test_cauchy F hn v hv Z hZ q
  rw [forwardQuadratic_twice, couplingLinearTest] at h
  convert h using 1 <;> ring

/-- The exact linear contact-sum identity in (10.11). -/
theorem general_linear_contact_identity (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (Z : MatR n) (q : V n) :
    (Z*transversePerturbation F v).trace+⟪q,transverseCoupling F v⟫ =
      -(1/(2-inverseDimension n))*couplingLinearSum F v Z q :=
  coupling_linear_identity F hn v hv Z q

/-- The square expansion (10.14), preserving the exact factor and all mixed terms. -/
theorem general_quadratic_contact_identity (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (Z : MatR n) (hZ : Z.IsHermitian) (q : V n) :
    (∑ i, minusContactWeight F v i*‖couplingTestVector F v Z q i‖^2) =
      (2*(2-inverseDimension n)/(2+inverseDimension n))*forwardQuadratic F v Z q := by
  rw [coupling_quadratic_identity F hn v hv Z hZ q, forwardQuadratic_twice]
  ring

/-- The third moment identity in (10.13), in the original complementary defect. -/
theorem general_reverse_contact_identity (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (couplingGamma n)^2*reverseDefect F v =
      (2-inverseDimension n)^2/(2*(2+inverseDimension n))*traceRemainder F v := by
  rw [gamma_reverse_identity F hn v hv, couplingL_remainder]
  have hp : 2+inverseDimension n ≠ 0 := by linarith [(inverseDimension_bounds hn).1]
  field_simp [hp] <;> ring

end SharpCut.Coupled
