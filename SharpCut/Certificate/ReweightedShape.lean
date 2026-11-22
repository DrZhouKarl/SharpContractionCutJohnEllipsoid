import SharpCut.Certificate.Defect
import SharpCut.Optimization.Certificate

/-! # Strict positivity of the reweighted John contact matrix

Positivity is derived from the frame's identity second moment and positive
scalar reweighting. No determinant bound is assumed. Matrix order is Loewner
order; quadratic forms are paired with actual Euclidean vectors.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

def weightedShape (F : JohnFrame n N) (f : Fin N → ℝ) : MatR n :=
  ∑ i, (F.weight i*f i) • outer (F.contact i)

theorem weightedShape_inner (F : JohnFrame n N) (f : Fin N → ℝ) (x : V n) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedShape F f) x⟫ =
      ∑ i, F.weight i*f i*⟪F.contact i, x⟫^2 := by
  calc
    _ = (weightedShape F f * outer x).trace := by
      simpa only [Khachiyan.outer_eq_vecMulVec] using
        (Optimization.trace_mul_cross (weightedShape F f) x x).symm
    _ = (outer x * weightedShape F f).trace := Matrix.trace_mul_comm _ _
    _ = ∑ i, F.weight i*f i*(outer x * outer (F.contact i)).trace := by
      simp only [weightedShape, Matrix.mul_sum, Matrix.mul_smul,
        Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show outer (F.contact i) = Matrix.vecMulVec (F.contact i).ofLp
        (F.contact i).ofLp from rfl, Optimization.trace_mul_cross,
        Khachiyan.outer_action, real_inner_smul_right, real_inner_comm (F.contact i) x]
      ring

theorem weightedShape_posDef (F : JohnFrame n N) (f : Fin N → ℝ) (hf : ∀ i, 0 < f i) :
    (weightedShape F f).PosDef := by
  have horder : 0 ≤ weightedShape F f := by
    unfold weightedShape
    apply Finset.sum_nonneg
    intro i _
    exact ((Khachiyan.outer_posSemidef (F.contact i)).smul
      (mul_pos (F.weight_pos i) (hf i)).le).nonneg
  have hpsd : (weightedShape F f).PosSemidef := by
    simpa only [sub_zero] using (Matrix.le_iff.mp horder)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.isHermitian
  intro x hx
  let xE : V n := WithLp.toLp 2 x
  have hxE : xE ≠ 0 := by
    intro h
    apply hx
    have he := congrArg (fun y : V n => y.ofLp) h
    simpa [xE] using he
  have hs : 0 < ∑ i, F.weight i*⟪F.contact i, xE⟫^2 := by
    rw [F.scalar_second_moment]
    exact pow_pos (norm_pos_iff.mpr hxE) 2
  have hex : ∃ i, 0 < F.weight i*⟪F.contact i, xE⟫^2 := by
    by_contra h
    push_neg at h
    have hsum := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => h i)
    linarith
  obtain ⟨i, hi⟩ := hex
  have hi' : 0 < F.weight i*f i*⟪F.contact i, xE⟫^2 := by
    simpa only [mul_assoc, mul_left_comm] using mul_pos (hf i) hi
  have hnonneg (j : Fin N) : 0 ≤ F.weight j*f j*⟪F.contact j, xE⟫^2 :=
    mul_nonneg (mul_pos (F.weight_pos j) (hf j)).le (sq_nonneg _)
  have hsum := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hnonneg j)
    (Finset.mem_univ i)
  have hpos := hi'.trans_le hsum
  rw [← weightedShape_inner] at hpos
  simpa only [Khachiyan.inner_matrix_action, WithLp.ofLp_toLp, star_trivial] using hpos

def contactScalarFactor (F : JohnFrame n N) (v : V n) (i : Fin N) : ℝ :=
  (1-cutWeight n*height F v i)/(1-boostParameter n*height F v i)

theorem contactScalarFactor_pos (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n)
    (hv : ‖v‖ = 1) (i : Fin N) : 0 < contactScalarFactor F v i := by
  have hb := inverseDimension_bounds hn
  have hnum := Scalar.balanced_weight_lower (inverseDimension n) (height F v i) 1
    hb.1.le hb.2 (F.heights_bounds v hv i).2 (by norm_num)
  have hnumerator : 0 < 1-cutWeight n*height F v i := by
    simpa only [cutWeight, one_mul] using hnum.2
  exact div_pos hnumerator (height_denominator_pos F hn v hv i)

theorem contactShape_posDef (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (weightedShape F (contactScalarFactor F v)).PosDef :=
  weightedShape_posDef F _ (contactScalarFactor_pos F hn v hv)

def certificateF (F : JohnFrame n N) (v : V n) : MatR n :=
  weightedShape F (contactScalarFactor F v)+
    (cutWeight n/(1-boostParameter n)) • outer v

theorem certificateF_posDef (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    (certificateF F v).PosDef := by
  have hb := inverseDimension_bounds hn
  have ha := Scalar.lorentz_parameter_bounds (inverseDimension n) hb.1 hb.2
  have hal : boostParameter n ≤ 1/3 := ha.2
  have ht : 0 < cutWeight n := by unfold cutWeight; linarith [hb.1]
  have hd : 0 < 1-boostParameter n := by linarith [hal]
  exact (contactShape_posDef F hn v hv).add_posSemidef
    ((Khachiyan.outer_posSemidef v).smul (div_pos ht hd).le)

end SharpCut.Certificate
