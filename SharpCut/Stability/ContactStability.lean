import SharpCut.Stability.LocalCoercivity

/-! # Contact and certificate estimates for a nearly extremal feasible ellipsoid

These are three of the five estimates in Theorem 6.2. Shape and center are
separate remaining obligations; this module does not claim the full theorem.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Stability
open Certificate Gap
variable {n N : ℕ}

theorem near_extremal_contact_stability (hn : 2 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hJ : IsJohnNormalized K) (F : JohnFrame n N) (hs : F.Supports K)
    (v : V n) (hv : ‖v‖ = 1) {c : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace 0 v) c A)
    (hε : 0 ≤ volumeDeficit n A) (hsmall : volumeDeficit n A ≤ 1/1000000) :
    frameDefect F v ≤ 32*volumeDeficit n A ∧
    frobeniusNorm (unrotatedQ F v-inverseModel v) ≤ 4*Real.sqrt (volumeDeficit n A) ∧
    (∑ i, F.weight i*(Metric.infDist (F.contact i) (Equality.modelContactSet v))^2) ≤
      (1024/3 : ℝ)*volumeDeficit n A := by
  have he := exact_volume_deficit hn hK hJ F hs v hv hA
  have hgeom : geometricGap F v ≤ volumeDeficit n A := by nlinarith only [he.1, he.2.2.1, he.2.2.2.1]
  have hsmallχ : frameDefect F v ≤ 3/2000 := by nlinarith only [he.2.2.2.2.2, hsmall]
  have hχ : frameDefect F v ≤ 32*volumeDeficit n A := by
    have hg := (geometric_control F hn v hv).2.2 hsmallχ
    nlinarith only [hg, hgeom]
  have hq := certificate_residual_bound F hn v hv
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have hcoeff : (1-inverseDimension n)/(2-inverseDimension n) ≤ 1/2 := by
    apply (div_le_iff₀ hd).mpr
    linarith only [hb.1]
  have hq2 := mul_le_mul_of_nonneg_right hcoeff (frameDefect_nonneg F hn v hv)
  have hsq := Real.sq_sqrt hε
  have hnorm : frobeniusNorm (unrotatedQ F v-inverseModel v) ≤ 4*Real.sqrt (volumeDeficit n A) := by
    have hp := Real.sqrt_nonneg (volumeDeficit n A)
    have hn := Real.sqrt_nonneg (∑ i, ∑ j, (unrotatedQ F v-inverseModel v) i j^2)
    nlinarith only [hq, hq2, hχ, hsq, hp, hn]
  have hdist := weighted_contact_distance_bound F hn v hv
  refine ⟨hχ, hnorm, ?_⟩
  nlinarith only [hdist, hχ]

end SharpCut.Stability
