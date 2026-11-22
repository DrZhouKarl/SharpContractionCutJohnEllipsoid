import SharpCut.John.PolarBody
import SharpCut.John.UniformBarrier
import SharpCut.John.MatrixPerturbation
import Khachiyan.EllipsoidGeometry

/-!
# Uniform feasible improvement of a normalized John ellipsoid

Compactness controls every polar constraint at once. Positive definiteness and
the increasing determinant are derived independently. This is the substantive
maximality contradiction in the contact-necessity proof.
-/

noncomputable section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Matrix Set
namespace SharpCut.John
variable {n : ℕ}

def perturbSlack (u : V n) : ℝ := 1-‖u‖^2
def perturbSlope (a : V n) (H : MatR n) (u : V n) : ℝ :=
  ⟪a, u⟫+⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) H u⟫
def perturbRemainder (a : V n) (H : MatR n) (u : V n) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H u‖^2-⟪a, u⟫^2

theorem perturbation_action (H : MatR n) (e : ℝ) (u : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (1+e • H) u =
      u+e • Matrix.toEuclideanCLM (𝕜 := ℝ) H u := by
  apply WithLp.ofLp_injective 2
  simp only [Khachiyan.matrix_action_ofLp, WithLp.ofLp_add, WithLp.ofLp_smul,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

theorem perturbation_action_norm_sq (H : MatR n) (e : ℝ) (u : V n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (1+e • H) u‖^2 =
      ‖u‖^2+2*e*⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) H u⟫+
        e^2*‖Matrix.toEuclideanCLM (𝕜 := ℝ) H u‖^2 := by
  rw [perturbation_action, norm_add_sq_real]
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem exists_uniform_feasible_perturbation {K : Set (V n)} (hK : IsConvexBody K)
    (hball : unitBall n ⊆ K) (a : V n) (H : MatR n) (hH : H.IsSymm)
    (hcontact : ∀ u ∈ contacts K, perturbSlope a H u < 0) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ e : ℝ, 0 < e → e ≤ delta →
      IsFeasible K (e • a) (1+e • H) := by
  have hs : ∀ u ∈ polar K, 0 ≤ perturbSlack u := by
    intro u hu
    have hb := Khachiyan.mem_unitBall u |>.mp (polar_subset_unitBall hball hu)
    have hn := norm_nonneg u
    have hp := mul_nonneg (show 0 ≤ 1-‖u‖ by linarith) (show 0 ≤ 1+‖u‖ by linarith)
    unfold perturbSlack
    nlinarith
  have hz : ∀ u ∈ polar K, perturbSlack u = 0 → perturbSlope a H u < 0 := by
    intro u hu hzero
    have hunit : ‖u‖ = 1 := by dsimp [perturbSlack] at hzero; nlinarith [norm_nonneg u]
    exact hcontact u ⟨hunit, hu⟩
  obtain ⟨d, hd, hbarrier⟩ := uniform_quadratic_barrier (polar_isCompact hball)
    ⟨0, zero_mem_polar K⟩ perturbSlack (perturbSlope a H) (perturbRemainder a H)
    (by unfold perturbSlack; fun_prop)
    (by unfold perturbSlope; fun_prop)
    (by unfold perturbRemainder; fun_prop) hs hz
  have ho : 0 ≤ operatorNorm H := norm_nonneg _
  have ha : 0 ≤ ‖a‖ := norm_nonneg _
  have dh : 0 < 2*(operatorNorm H+1) := by linarith
  have da : 0 < 2*(‖a‖+1) := by linarith
  refine ⟨min d (min (1/(2*(operatorNorm H+1))) (1/(2*(‖a‖+1)))),
    lt_min hd (lt_min (one_div_pos.mpr dh) (one_div_pos.mpr da)), ?_⟩
  intro e he hed
  have heD : e ≤ d := hed.trans (min_le_left _ _)
  have heH : e ≤ 1/(2*(operatorNorm H+1)) :=
    hed.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heA : e ≤ 1/(2*(‖a‖+1)) :=
    hed.trans ((min_le_right _ _).trans (min_le_right _ _))
  have heHb := (le_div_iff₀ dh).mp heH
  have heAb := (le_div_iff₀ da).mp heA
  have hsmall : e*operatorNorm H < 1 := by nlinarith
  have hPD := identity_smul_posDef H hH he.le hsmall
  refine ⟨hPD, ?_⟩
  intro y hy
  apply mem_of_polar_constraints hK hball
  intro u hu
  have hn := Khachiyan.mem_unitBall u |>.mp (polar_subset_unitBall hball hu)
  have hdot : ⟪a, u⟫ ≤ ‖a‖ := by
    have hcs := real_inner_le_norm a u
    have hb := mul_le_mul_of_nonneg_left hn ha
    simpa only [mul_one] using hcs.trans hb
  have hcenter : 0 < 1-e*⟪a, u⟫ := by
    have hmul := mul_le_mul_of_nonneg_left hdot he.le
    nlinarith
  have hb := hbarrier e he heD u hu
  dsimp [perturbSlack, perturbSlope, perturbRemainder] at hb
  have hsq : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (1+e • H) u‖^2 ≤ (1-e*⟪a, u⟫)^2 := by
    rw [perturbation_action_norm_sq]
    nlinarith
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (1+e • H) u‖ ≤ 1-e*⟪a, u⟫ := by
    nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) (1+e • H) u)]
  have hsupport := Khachiyan.ellipsoid_support_le hPD.isHermitian.isSymm (v := u) hy
  have hcentereq : ⟪u, e • a⟫ = e*⟪a, u⟫ := by
    rw [real_inner_smul_right, real_inner_comm]
  rw [hcentereq] at hsupport
  linarith

theorem no_strict_contact_improver {K : Set (V n)} (hK : IsConvexBody K)
    (hmax : IsJohnNormalized K) (a : V n) (H : MatR n) (hH : H.IsSymm)
    (htrace : 0 < H.trace) (hcontact : ∀ u ∈ contacts K, perturbSlope a H u < 0) : False := by
  obtain ⟨df, hdf, hf⟩ := exists_uniform_feasible_perturbation hK hmax.unitBall_subset a H hH hcontact
  obtain ⟨dd, hdd, hd⟩ := determinant_increases_near_identity H htrace
  let e := min df dd/2
  have he : 0 < e := half_pos (lt_min hdf hdd)
  have hem : e < min df dd := half_lt_self (lt_min hdf hdd)
  have hedf : e ≤ df := (hem.trans_le (min_le_left _ _)).le
  have hedd : e < dd := hem.trans_le (min_le_right _ _)
  have hle := hmax.det_le (e • a) (1+e • H) (hf e he hedf)
  rw [Matrix.det_one] at hle
  exact (not_lt_of_ge hle) (hd e he hedd)

end SharpCut.John
