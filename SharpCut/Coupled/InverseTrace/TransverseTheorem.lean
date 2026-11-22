import SharpCut.Coupled.InverseTrace.GenericTheorem

/-! # Both exact inverse-trace equivalences on the actual transverse John blocks -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Coupled.InverseTrace
open Certificate Geometry
variable {m N : ℕ}

def transverseE (F : JohnFrame (m+1) N) (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (v : V (m+1)) : MatR m :=
  tailBlock B (transversePerturbation F v)
def transverseJ (F : JohnFrame (m+1) N) (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (v : V (m+1)) : V m :=
  tailCoordinates B (transverseCoupling F v)
def forwardEta (F : JohnFrame (m+1) N) (v : V (m+1)) : ℝ := (2-inverseDimension (m+1))/4*traceRemainder F v

theorem transverseE_hermitian (F : JohnFrame (m+1) N) (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (v : V (m+1)) :
    (transverseE F B v).IsHermitian := tailBlock_isHermitian B _ (transversePerturbation_isHermitian F v)

theorem transverseE_trace (F : JohnFrame (m+1) N) (hm : 1 ≤ m) (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1)))
    (v : V (m+1)) (hv : ‖v‖ = 1) (hB : B 0 = v) : (transverseE F B v).trace = transverseSigma F v := by
  have hn : 2 ≤ m+1 := by omega
  rw [transverseE, tailBlock_trace_zero_axis B _ (transversePerturbation_isHermitian F v) v hv hB
    (transversePerturbation_axis F hn v hv), transversePerturbation_trace F hn v hv]

theorem forwardEta_pos (F : JohnFrame (m+1) N) (hm : 1 ≤ m) (v : V (m+1))
    (hσ : transverseSigma F v < sigmaStar (m+1)) : 0 < forwardEta F v := by
  have hb := inverseDimension_bounds (show 2 ≤ m+1 by omega)
  exact mul_pos (by linarith [hb.2]) (sub_pos.mpr hσ)

/-- The forward equivalence (10.19), proved for all tests rather than only an optimizer. -/
theorem forward_inverse_trace_iff (F : JohnFrame (m+1) N) (hm : 1 ≤ m) (v : V (m+1)) (hv : ‖v‖ = 1)
    (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (hB : B 0 = v)
    (hσ : 0 < transverseSigma F v) (hσstar : transverseSigma F v < sigmaStar (m+1)) :
    AllCoupledTests (transverseE F B v) (transverseJ F B v) (1/2) (forwardEta F v) (transverseSigma F v) ↔
      (effectiveMatrix (transverseE F B v) (transverseJ F B v) (1/2) (forwardEta F v)).PosDef ∧
      ((effectiveMatrix (transverseE F B v) (transverseJ F B v) (1/2) (forwardEta F v))⁻¹).trace ≤ 2*(m : ℝ) := by
  have h := all_tests_inverse_trace_iff (transverseE F B v) (transverseE_hermitian F B v) (transverseJ F B v)
    (1/2) (forwardEta F v) (transverseSigma F v) (by norm_num) (forwardEta_pos F hm v hσstar) hσ
    (transverseE_trace F hm B v hv hB)
  have hnum : (m : ℝ)/(1/2) = 2*(m : ℝ) := by ring
  rwa [hnum] at h

/-- The complementary coefficient E'=e*I-E has exactly trace tau. -/
theorem complementary_transverse_trace (F : JohnFrame (m+1) N) (hm : 1 ≤ m)
    (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (v : V (m+1)) (hv : ‖v‖ = 1) (hB : B 0 = v) :
    (endpointShift (m+1) • (1 : MatR m)-transverseE F B v).trace = traceRemainder F v := by
  have hdim : (m : ℝ)*endpointShift (m+1) = sigmaStar (m+1) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using endpointShift_dimension (show 2 ≤ m+1 by omega)
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
    transverseE_trace F hm B v hv hB, mul_comm, hdim]
  rfl

/-- The complementary equivalence (10.20), retaining beta=t-e*>0 and x=d*sigma/4. -/
theorem complementary_inverse_trace_iff (F : JohnFrame (m+1) N) (hm : 1 ≤ m) (v : V (m+1)) (hv : ‖v‖ = 1)
    (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (hB : B 0 = v)
    (hσ : 0 < transverseSigma F v) (hσstar : transverseSigma F v < sigmaStar (m+1)) :
    (∀ Z : MatR m, Z.IsHermitian → ∀ q : V m,
      ((Z*(endpointShift (m+1) • (1 : MatR m)-transverseE F B v)).trace+⟪q,transverseJ F B v⟫)^2 ≤
        traceRemainder F v*((Z^2*(cutWeight (m+1) • (1 : MatR m)-transverseE F B v)).trace+
          2*⟪q,Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverseJ F B v)⟫+axialDeficit F v*‖q‖^2)) ↔
      (cutWeight (m+1) • (1 : MatR m)-transverseE F B v-(1/axialDeficit F v) • outer (transverseJ F B v)).PosDef ∧
      ((cutWeight (m+1) • (1 : MatR m)-transverseE F B v-(1/axialDeficit F v) • outer (transverseJ F B v))⁻¹).trace ≤
        (m : ℝ)/oppositeBeta (m+1) := by
  have hn : 2 ≤ m+1 := by omega
  have hE := transverseE_hermitian F B v
  have hE' : (endpointShift (m+1) • (1 : MatR m)-transverseE F B v).IsHermitian :=
    (Matrix.isHermitian_one.smul (by rfl)).sub hE
  have hτ : 0 < traceRemainder F v := sub_pos.mpr hσstar
  have hx : 0 < axialDeficit F v := by
    rw [axialDeficit_sigma F hn v]
    exact mul_pos (by linarith [(inverseDimension_bounds hn).2]) hσ
  have hg := all_tests_inverse_trace_iff (endpointShift (m+1) • (1 : MatR m)-transverseE F B v) hE'
    (transverseJ F B v) (oppositeBeta (m+1)) (axialDeficit F v) (traceRemainder F v)
    (oppositeBeta_pos hn) hx hτ (complementary_transverse_trace F hm B v hv hB)
  have hcoeff : (endpointShift (m+1) • (1 : MatR m)-transverseE F B v)+oppositeBeta (m+1) • (1 : MatR m) =
      cutWeight (m+1) • (1 : MatR m)-transverseE F B v := by unfold oppositeBeta; module
  simpa only [AllCoupledTests, originalLinear, originalQuadratic, effectiveMatrix, hcoeff] using hg

/-- Full Lemma 10.4: the two stated all-test inverse-trace equivalences. -/
theorem inverse_trace_interpretation (F : JohnFrame (m+1) N) (hm : 1 ≤ m) (v : V (m+1)) (hv : ‖v‖ = 1)
    (B : OrthonormalBasis (Fin (m+1)) ℝ (V (m+1))) (hB : B 0 = v)
    (hσ : 0 < transverseSigma F v) (hσstar : transverseSigma F v < sigmaStar (m+1)) :
    (AllCoupledTests (transverseE F B v) (transverseJ F B v) (1/2) (forwardEta F v) (transverseSigma F v) ↔
      (effectiveMatrix (transverseE F B v) (transverseJ F B v) (1/2) (forwardEta F v)).PosDef ∧
      ((effectiveMatrix (transverseE F B v) (transverseJ F B v) (1/2) (forwardEta F v))⁻¹).trace ≤ 2*(m : ℝ)) ∧
    ((∀ Z : MatR m, Z.IsHermitian → ∀ q : V m,
      ((Z*(endpointShift (m+1) • (1 : MatR m)-transverseE F B v)).trace+⟪q,transverseJ F B v⟫)^2 ≤
        traceRemainder F v*((Z^2*(cutWeight (m+1) • (1 : MatR m)-transverseE F B v)).trace+
          2*⟪q,Matrix.toEuclideanCLM (𝕜 := ℝ) Z (transverseJ F B v)⟫+axialDeficit F v*‖q‖^2)) ↔
      (cutWeight (m+1) • (1 : MatR m)-transverseE F B v-(1/axialDeficit F v) • outer (transverseJ F B v)).PosDef ∧
      ((cutWeight (m+1) • (1 : MatR m)-transverseE F B v-(1/axialDeficit F v) • outer (transverseJ F B v))⁻¹).trace ≤
        (m : ℝ)/oppositeBeta (m+1)) :=
  ⟨forward_inverse_trace_iff F hm v hv B hB hσ hσstar, complementary_inverse_trace_iff F hm v hv B hB hσ hσstar⟩

end SharpCut.Coupled.InverseTrace
