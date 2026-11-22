import SharpCut.Coupled.InverseTrace.TransverseTheorem

/-! # Explicit coefficients and optimal tests recorded in (10.22)-(10.25) -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Coupled.InverseTrace
open Certificate Geometry
variable {m N : ℕ}

def forwardR (F : JohnFrame (m+1) N) (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (v : V (m+1)) : MatR m :=
  effectiveMatrix (transverseE F B v) (transverseJ F B v) (1/2) (forwardEta F v)

def reverseR (F : JohnFrame (m+1) N) (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (v : V (m+1)) : MatR m :=
  cutWeight (m+1) • (1 : MatR m)-transverseE F B v-(1/axialDeficit F v) • outer (transverseJ F B v)

theorem forward_coefficient_formula (F : JohnFrame (m+1) N) (hm : 1 ≤ m) (v : V (m+1)) (hv : ‖v‖ = 1)
    (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (hB : B 0 = v) (hR : (forwardR F B v).PosDef) :
    coefficient (forwardR F B v) (transverseJ F B v) (1/2) (forwardEta F v) =
      transverseSigma F v-(m : ℝ)/2+(1/4 : ℝ)*((forwardR F B v)⁻¹).trace := by
  have h := effective_coefficient_trace (transverseE F B v) (transverseJ F B v) (1/2) (forwardEta F v)
    (transverseSigma F v) hR (transverseE_trace F hm B v hv hB)
  dsimp only [forwardR]
  convert h using 1 <;> ring

theorem reverseR_effective (F : JohnFrame (m+1) N) (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (v : V (m+1)) :
    reverseR F B v = effectiveMatrix (endpointShift (m+1) • (1 : MatR m)-transverseE F B v)
      (transverseJ F B v) (oppositeBeta (m+1)) (axialDeficit F v) := by
  unfold reverseR effectiveMatrix oppositeBeta
  module

/-- Exact complementary coefficient (10.24), with trace tau expanded into m e* - sigma. -/
theorem reverse_coefficient_formula (F : JohnFrame (m+1) N) (hm : 1 ≤ m) (v : V (m+1)) (hv : ‖v‖ = 1)
    (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (hB : B 0 = v) (hR : (reverseR F B v).PosDef) :
    coefficient (reverseR F B v) (transverseJ F B v) (oppositeBeta (m+1)) (axialDeficit F v) =
      (-cutWeight (m+1)+2*endpointShift (m+1))*(m : ℝ)-transverseSigma F v+
        (oppositeBeta (m+1))^2*((reverseR F B v)⁻¹).trace := by
  have h := effective_coefficient_trace (endpointShift (m+1) • (1 : MatR m)-transverseE F B v)
    (transverseJ F B v) (oppositeBeta (m+1)) (axialDeficit F v) (traceRemainder F v)
    (by rw [← reverseR_effective]; exact hR) (complementary_transverse_trace F hm B v hv hB)
  rw [← reverseR_effective] at h
  have hdim : (m : ℝ)*endpointShift (m+1) = sigmaStar (m+1) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using endpointShift_dimension (show 2 ≤ m+1 by omega)
  unfold traceRemainder at h
  unfold oppositeBeta at h ⊢
  rw [← hdim] at h
  nlinarith only [h]

/-- The two optimal completed tests displayed in (10.23) and its complementary counterpart. -/
theorem inverse_trace_optimal_tests (R : MatR m) (hR : R.PosDef) (j : V m) (β η : ℝ) (hη : 0 < η) :
    (1-β • R⁻¹).IsHermitian ∧
    completedLinear R j β (1-β • R⁻¹) ((1/η) • j) = coefficient R j β η ∧
    completedQuadratic R η (1-β • R⁻¹) ((1/η) • j) = coefficient R j β η :=
  ⟨bestMatrix_hermitian R hR β, (best_test_attains R hR j β η hη.ne').1, (best_test_attains R hR j β η hη.ne').2⟩

/-- The inverse-trace cancellation chain (10.25) has no hidden division by a zero beta. -/
theorem reverse_coefficient_trace_iff (F : JohnFrame (m+1) N) (hm : 1 ≤ m) (v : V (m+1)) (hv : ‖v‖ = 1)
    (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (hB : B 0 = v) (hR : (reverseR F B v).PosDef) :
    coefficient (reverseR F B v) (transverseJ F B v) (oppositeBeta (m+1)) (axialDeficit F v) ≤ traceRemainder F v ↔
      ((reverseR F B v)⁻¹).trace ≤ (m : ℝ)/oppositeBeta (m+1) := by
  have h := coefficient_iff_inverse_trace (endpointShift (m+1) • (1 : MatR m)-transverseE F B v)
    (transverseJ F B v) (oppositeBeta (m+1)) (axialDeficit F v) (traceRemainder F v)
    (by rw [← reverseR_effective]; exact hR) (oppositeBeta_pos (show 2 ≤ m+1 by omega))
    (complementary_transverse_trace F hm B v hv hB)
  rwa [← reverseR_effective] at h

end SharpCut.Coupled.InverseTrace
