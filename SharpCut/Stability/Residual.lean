import SharpCut.Stability.ContactDistance
import SharpCut.Stability.NormalizationResidual

/-! # Complete geometric residual lemma and global contact stability -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Stability
open Certificate Gap
variable {n N : ℕ}

/-- Lemma 9.2: all three exact bounds, for any frame in every dimension n ≥ 2. -/
theorem geometric_residual (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (frobeniusNorm (unrotatedQ F v-inverseModel v))^2 ≤
      (1-inverseDimension n)/(2-inverseDimension n)*frameDefect F v ∧
    (frobeniusNorm (normalizedCertificate F v-1))^2 ≤ frameDefect F v/(2-inverseDimension n) ∧
    (∑ i, F.weight i*(Metric.infDist (F.contact i) (Equality.modelContactSet v))^2) ≤
      (32/3 : ℝ)*frameDefect F v :=
  ⟨certificate_residual_bound F hn v hv, normalized_residual_bound F hn v hv,
    weighted_contact_distance_bound F hn v hv⟩

/-- The unconditional global geometric stability inequalities in (9.8). -/
theorem global_geometric_stability (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (F : JohnFrame n N) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A) :
    frameDefect F v ≤ 1500*volumeDeficit n A ∧
    (∑ i, F.weight i*(Metric.infDist (F.contact i) (Equality.modelContactSet v))^2) ≤
      16000*volumeDeficit n A ∧
    (1/1000 : ℝ)*(frobeniusNorm (normalizedCertificate F v-1))^2 ≤
      Real.log (normalizedCertificate F v).det := by
  have he := exact_volume_deficit hn hK hJ F hs v hv hA
  have hdist := weighted_contact_distance_bound F hn v hv
  have hnrm := normalized_residual_bound F hn v hv
  have hgeom := geometricGap_lower F hn v hv
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have hquad : (2-inverseDimension n)*(frobeniusNorm (normalizedCertificate F v-1))^2 ≤ frameDefect F v :=
    by simpa only [mul_comm] using (le_div_iff₀ hd).mp hnrm
  have hlow := mul_le_mul_of_nonneg_right (show (3/2 : ℝ) ≤ 2-inverseDimension n by linarith [hb.2])
    (sq_nonneg (frobeniusNorm (normalizedCertificate F v-1)))
  have hlog : geometricGap F v = Real.log (normalizedCertificate F v).det := by
    unfold geometricGap
    rw [normalizedCertificate_det F hn v hv]
    unfold frameMatrix
    rw [polarMatrix_det (unrotatedQ_det_pos F hn v hv)]
  refine ⟨he.2.2.2.2.2, ?_, ?_⟩
  · nlinarith only [hdist, he.2.2.2.2.2]
  · rw [← hlog]
    nlinarith only [hgeom, hquad, hlow]

end SharpCut.Stability
