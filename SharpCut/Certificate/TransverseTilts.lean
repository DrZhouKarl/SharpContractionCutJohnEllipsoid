import SharpCut.Certificate.NormalizedBlocks

/-! # Positive tilted transverse moments and their exact block identities -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

def transversePlusMoment (F : JohnFrame n N) (v : V n) : MatR n :=
  ∑ i, (F.weight i/(1-boostParameter n*height F v i)*(1+height F v i)) •
    outer (transverse v (F.contact i))

def transverseMinusMoment (F : JohnFrame n N) (v : V n) : MatR n :=
  ∑ i, (F.weight i/(1-boostParameter n*height F v i)*(1-height F v i)) •
    outer (transverse v (F.contact i))

theorem transversePlusMoment_eq (F : JohnFrame n N) (v : V n) :
    transversePlusMoment F v = transverseMatrixMoment F v 0+transverseMatrixMoment F v 1 := by
  unfold transversePlusMoment transverseMatrixMoment
  simp only [pow_zero, pow_one, mul_one, ← Finset.sum_add_distrib, ← add_smul]
  apply Finset.sum_congr rfl; intro i hi; congr 1; ring

theorem transverseMinusMoment_eq (F : JohnFrame n N) (v : V n) :
    transverseMinusMoment F v = transverseMatrixMoment F v 0-transverseMatrixMoment F v 1 := by
  unfold transverseMinusMoment transverseMatrixMoment
  simp only [pow_zero, pow_one, mul_one, ← Finset.sum_sub_distrib, ← sub_smul]
  apply Finset.sum_congr rfl; intro i hi; congr 1; ring

theorem transversePlusMoment_identity (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    transversePlusMoment F v =
      (2*(2-inverseDimension n)/((1-inverseDimension n)*(2+inverseDimension n))) •
        (cutWeight n • projector v-transversePerturbation F v) := by
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have h1 : 1-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hp : 2+inverseDimension n ≠ 0 := by linarith [hb.1]
  have he := (transverse_moments F hn v hv).2.2
  rw [transversePlusMoment_eq, ← he, transversePerturbation]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    boostParameter, cutWeight]
  field_simp [hd, h1, hp] <;> ring

theorem transverseMinusMoment_identity (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    transverseMinusMoment F v = ((2-inverseDimension n)/(2+inverseDimension n)) •
      (projector v+(2 : ℝ) • transversePerturbation F v) := by
  have hb := inverseDimension_bounds hn
  have hd : 2-inverseDimension n ≠ 0 := by linarith [hb.2]
  have hp : 2+inverseDimension n ≠ 0 := by linarith [hb.1]
  have he := (transverse_moments F hn v hv).2.2
  rw [transverseMinusMoment_eq, ← he, transversePerturbation]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, boostParameter]
  field_simp [hd, hp] <;> ring

theorem transversePlusMoment_posSemidef (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) : (transversePlusMoment F v).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i hi
  have hd := height_denominator_pos F hn v hv i
  have hlow : -1 ≤ height F v i := (F.heights_bounds v hv i).1
  have hp : 0 ≤ 1+height F v i := by linarith
  exact (Khachiyan.outer_posSemidef _).smul (mul_nonneg (div_pos (F.weight_pos i) hd).le hp)

theorem matrix_action_sum {ι : Type*} [Fintype ι] (A : ι → MatR n) (u : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, A i) u =
      ∑ i, Matrix.toEuclideanCLM (𝕜 := ℝ) (A i) u := by
  apply WithLp.ofLp_injective 2
  simp only [Khachiyan.matrix_action_ofLp, Matrix.sum_mulVec, WithLp.ofLp_sum]

theorem sum_outer_quadratic {ι : Type*} [Fintype ι] (q : ι → V n) (w : ι → ℝ) (u : V n) :
    ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, w i • outer (q i)) u⟫ =
      ∑ i, w i*⟪q i, u⟫^2 := by
  rw [matrix_action_sum]
  simp only [inner_sum, matrix_action_smul, real_inner_smul_right,
    Khachiyan.outer_action, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_comm u (q i)]
  ring

theorem transverse_contact_pairing (F : JohnFrame n N) (v u : V n) (i : Fin N)
    (hu : ⟪u, v⟫ = 0) : ⟪transverse v (F.contact i), u⟫ = ⟪F.contact i, u⟫ := by
  have hu' : ⟪v, u⟫ = 0 := by rwa [real_inner_comm]
  rw [transverse, inner_sub_left, real_inner_smul_left, hu', mul_zero, sub_zero]

theorem transverse_height_strict (F : JohnFrame n N) (v u : V n) (hv : ‖v‖ = 1)
    (i : Fin N) (hi : ⟪transverse v (F.contact i), u⟫ ≠ 0) :
    -1 < height F v i ∧ height F v i < 1 := by
  have hy : transverse v (F.contact i) ≠ 0 := by intro h; simp only [h, inner_zero_left] at hi; contradiction
  have hp : 0 < ‖transverse v (F.contact i)‖^2 := pow_pos (norm_pos_iff.mpr hy) 2
  rw [transverse_norm_sq v (F.contact i) hv (F.contact_unit i)] at hp
  change 0 < 1-(height F v i)^2 at hp
  constructor <;> nlinarith

theorem transverse_weighted_positive (F : JohnFrame n N) (v u : V n) (hv : ‖v‖ = 1)
    (hu : ⟪u, v⟫ = 0) (hu0 : u ≠ 0) (w : Fin N → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwp : ∀ i, ⟪transverse v (F.contact i), u⟫ ≠ 0 → 0 < w i) :
    0 < ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, w i • outer (transverse v (F.contact i))) u⟫ := by
  have hs : 0 < ∑ i, F.weight i*⟪F.contact i, u⟫^2 := by
    rw [F.scalar_second_moment]
    exact pow_pos (norm_pos_iff.mpr hu0) 2
  have hex : ∃ i, 0 < F.weight i*⟪F.contact i, u⟫^2 := by
    by_contra h
    push Not at h
    have he := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => h i)
    linarith
  obtain ⟨i, hi⟩ := hex
  have hi0 : ⟪transverse v (F.contact i), u⟫ ≠ 0 := by
    rw [transverse_contact_pairing F v u i hu]
    intro h; rw [h, zero_pow (by decide : 2 ≠ 0), mul_zero] at hi; linarith
  have hisq : 0 < ⟪transverse v (F.contact i), u⟫^2 := sq_pos_of_ne_zero hi0
  have him : 0 < w i*⟪transverse v (F.contact i), u⟫^2 := mul_pos (hwp i hi0) hisq
  have hsum := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) => mul_nonneg (hw j) (sq_nonneg ⟪transverse v (F.contact j), u⟫))
      (Finset.mem_univ i)
  rw [sum_outer_quadratic]
  exact him.trans_le hsum

theorem transversePlusMoment_positive (F : JohnFrame n N) (hn : 2 ≤ n)
    (v u : V n) (hv : ‖v‖ = 1) (hu : ⟪u, v⟫ = 0) (hu0 : u ≠ 0) :
    0 < ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePlusMoment F v) u⟫ := by
  apply transverse_weighted_positive F v u hv hu hu0
  · intro i
    have hlow : -1 ≤ height F v i := (F.heights_bounds v hv i).1
    exact mul_nonneg (div_pos (F.weight_pos i) (height_denominator_pos F hn v hv i)).le (by linarith)
  · intro i hi
    have hlow := (transverse_height_strict F v u hv i hi).1
    exact mul_pos (div_pos (F.weight_pos i) (height_denominator_pos F hn v hv i)) (by linarith)

theorem transverseMinusMoment_positive (F : JohnFrame n N) (hn : 2 ≤ n)
    (v u : V n) (hv : ‖v‖ = 1) (hu : ⟪u, v⟫ = 0) (hu0 : u ≠ 0) :
    0 < ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (transverseMinusMoment F v) u⟫ := by
  apply transverse_weighted_positive F v u hv hu hu0
  · intro i
    exact mul_nonneg (div_pos (F.weight_pos i) (height_denominator_pos F hn v hv i)).le
      (sub_nonneg.mpr (F.heights_bounds v hv i).2)
  · intro i hi
    have hhigh := (transverse_height_strict F v u hv i hi).2
    exact mul_pos (div_pos (F.weight_pos i) (height_denominator_pos F hn v hv i)) (by linarith)

theorem transverse_strict_bounds (F : JohnFrame n N) (hn : 2 ≤ n)
    (v u : V n) (hv : ‖v‖ = 1) (hu : ⟪u, v⟫ = 0) (hu0 : u ≠ 0) :
    -(1/2 : ℝ)*‖u‖^2 < ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v) u⟫ ∧
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v) u⟫ < cutWeight n*‖u‖^2 := by
  have hb := inverseDimension_bounds hn
  have hd : 0 < 2-inverseDimension n := by linarith [hb.2]
  have h1 : 0 < 1-inverseDimension n := by linarith [hb.2]
  have hp : 0 < 2+inverseDimension n := by linarith [hb.1]
  have hm := transverseMinusMoment_positive F hn v u hv hu hu0
  have hpl := transversePlusMoment_positive F hn v u hv hu hu0
  rw [transverseMinusMoment_identity F hn v hv, matrix_action_smul, real_inner_smul_right] at hm
  rw [transversePlusMoment_identity F hn v hv, matrix_action_smul, real_inner_smul_right] at hpl
  have hm' := pos_of_mul_pos_right hm (div_pos hd hp).le
  have hp' := pos_of_mul_pos_right hpl (div_pos (mul_pos (by norm_num) hd) (mul_pos h1 hp)).le
  rw [matrix_action_add, inner_add_right, matrix_action_smul, real_inner_smul_right,
    projector_transverse_identity v u hu, real_inner_self_eq_norm_sq] at hm'
  rw [matrix_action_sub, inner_sub_right, matrix_action_smul, real_inner_smul_right,
    projector_transverse_identity v u hu, real_inner_self_eq_norm_sq] at hp'
  constructor <;> linarith

theorem transverseMinusMoment_posSemidef (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) : (transverseMinusMoment F v).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i hi
  have hd := height_denominator_pos F hn v hv i
  have hp : 0 ≤ 1-height F v i := sub_nonneg.mpr (F.heights_bounds v hv i).2
  exact (Khachiyan.outer_posSemidef _).smul (mul_nonneg (div_pos (F.weight_pos i) hd).le hp)

end SharpCut.Certificate
