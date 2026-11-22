import SharpCut.Certificate.MatrixGeometry

/-! # The ordered factorization Q = F D of the Lorentz aggregate -/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

def cross (u w : V n) : MatR n := Matrix.vecMulVec u.ofLp w.ofLp
def weightedDirection (F : JohnFrame n N) (v : V n) : V n :=
  ∑ i, (F.weight i*contactScalarFactor F v i) • F.contact i
def unrotatedQ (F : JohnFrame n N) (v : V n) : MatR n :=
  (∑ i, originalWeight F v i • cross (F.contact i) (lorentzDirection v (F.contact i)))+
    cutWeight n • outer v

@[simp] theorem cross_self (u : V n) : cross u u = outer u := rfl
@[simp] theorem cross_transpose (u w : V n) : (cross u w)ᵀ = cross w u := by
  ext i j
  simp only [cross, Matrix.vecMulVec_apply, Matrix.transpose_apply]
  ring

theorem mul_cross (A : MatR n) (u w : V n) :
    A*cross u w = cross (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) w := by
  unfold cross
  rw [Matrix.mul_vecMulVec, Khachiyan.matrix_action_ofLp]
@[simp] theorem cross_smul_left (r : ℝ) (u w : V n) : cross (r • u) w = r • cross u w := by
  ext i j
  simp only [cross, Matrix.vecMulVec, Matrix.of_apply, WithLp.ofLp_smul, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring
@[simp] theorem cross_smul_right (r : ℝ) (u w : V n) : cross u (r • w) = r • cross u w := by
  ext i j
  simp only [cross, Matrix.vecMulVec, Matrix.of_apply, WithLp.ofLp_smul, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring
@[simp] theorem cross_sub_left (u w v : V n) : cross (u-w) v = cross u v-cross w v := by
  ext i j
  simp only [cross, Matrix.vecMulVec, Matrix.of_apply, WithLp.ofLp_sub, Pi.sub_apply, Matrix.sub_apply]
  ring

theorem cross_sum_left {ι : Type*} [Fintype ι] (u : ι → V n) (v : V n) :
    cross (∑ i, u i) v = ∑ i, cross (u i) v := by
  ext j k
  simp only [cross, Matrix.vecMulVec, Matrix.of_apply, WithLp.ofLp_sum, Finset.sum_apply, Matrix.sum_apply]
  rw [Finset.sum_mul]

theorem weightedShape_action (F : JohnFrame n N) (f : Fin N → ℝ) (x : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedShape F f) x =
      ∑ i, (F.weight i*f i*⟪F.contact i, x⟫) • F.contact i := by
  apply WithLp.ofLp_injective 2
  have ho (i : Fin N) : outer (F.contact i) *ᵥ x.ofLp =
      ⟪F.contact i, x⟫ • (F.contact i).ofLp := by
    have h := congrArg (fun y : V n => y.ofLp) (Khachiyan.outer_action (F.contact i) x)
    simpa only [Khachiyan.matrix_action_ofLp, WithLp.ofLp_smul] using h
  simp only [Khachiyan.matrix_action_ofLp, weightedShape, Matrix.sum_mulVec, Matrix.smul_mulVec,
    WithLp.ofLp_sum, WithLp.ofLp_smul, ho, smul_smul]

theorem weighted_direction_balance (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    weightedDirection F v = boostParameter n •
      Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedShape F (contactScalarFactor F v)) v-cutWeight n • v := by
  have hc : weightedDirection F v-boostParameter n •
      Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedShape F (contactScalarFactor F v)) v =
      ∑ i, originalWeight F v i • F.contact i := by
    rw [weightedShape_action, weightedDirection, Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, ← sub_smul]
    congr 1
    have hd := height_denominator_pos F hn v hv i
    have hf : contactScalarFactor F v i*(1-boostParameter n*height F v i) =
        1-cutWeight n*height F v i := div_mul_cancel₀ _ hd.ne'
    calc
      _ = F.weight i*(contactScalarFactor F v i*(1-boostParameter n*height F v i)) := by
        unfold height; ring
      _ = originalWeight F v i := by rw [hf]; rfl
  have hz : (∑ i, originalWeight F v i • F.contact i) = -(cutWeight n • v) :=
    eq_neg_of_add_eq_zero_left (balanced_normals F v)
  calc
    _ = (weightedDirection F v-boostParameter n •
        Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedShape F (contactScalarFactor F v)) v)+
        boostParameter n • Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedShape F (contactScalarFactor F v)) v := by abel
    _ = _ := by rw [hc, hz]; abel

theorem lorentz_cross_term (F : JohnFrame n N) (v : V n) (i : Fin N) :
    originalWeight F v i • cross (F.contact i) (lorentzDirection v (F.contact i)) =
      boostScale n • ((F.weight i*contactScalarFactor F v i) • outer (F.contact i))+
      (1-boostScale n) • ((F.weight i*contactScalarFactor F v i*height F v i) • cross (F.contact i) v)-
      boostParameter n • ((F.weight i*contactScalarFactor F v i) • cross (F.contact i) v) := by
  ext j k
  simp only [originalWeight, cross, Matrix.vecMulVec, Matrix.of_apply, lorentzDirection, transverse,
    contactScalarFactor, height, boostScale, WithLp.ofLp_smul, WithLp.ofLp_add, WithLp.ofLp_sub,
    Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Khachiyan.outer_apply, smul_eq_mul]
  ring

theorem unrotatedQ_decomposition (F : JohnFrame n N) (v : V n) :
    unrotatedQ F v = boostScale n • weightedShape F (contactScalarFactor F v)+
      (1-boostScale n) • cross
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedShape F (contactScalarFactor F v)) v) v-
      boostParameter n • cross (weightedDirection F v) v+cutWeight n • outer v := by
  have hs0 : cross (weightedDirection F v) v =
      ∑ i, (F.weight i*contactScalarFactor F v i) • cross (F.contact i) v := by
    rw [weightedDirection, cross_sum_left]
    simp only [cross_smul_left]
  have hs1 : cross
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedShape F (contactScalarFactor F v)) v) v =
      ∑ i, (F.weight i*contactScalarFactor F v i*height F v i) • cross (F.contact i) v := by
    rw [weightedShape_action, cross_sum_left]
    simp only [cross_smul_left, height]
  rw [hs0, hs1]
  simp only [unrotatedQ, lorentz_cross_term, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.smul_sum, weightedShape]

theorem mul_outer_eq_cross (B : MatR n) (v : V n) :
    B*outer v = cross (Matrix.toEuclideanCLM (𝕜 := ℝ) B v) v := by
  change B*Matrix.vecMulVec v.ofLp v.ofLp =
    Matrix.vecMulVec (Matrix.toEuclideanCLM (𝕜 := ℝ) B v).ofLp v.ofLp
  rw [Matrix.mul_vecMulVec, Khachiyan.matrix_action_ofLp]

theorem mul_certificateD (B : MatR n) (v : V n) :
    B*certificateD v = boostScale n • B+
      ((boostScale n)^2-boostScale n) • cross (Matrix.toEuclideanCLM (𝕜 := ℝ) B v) v := by
  simp only [certificateD, projector, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_sub, Matrix.mul_one, mul_outer_eq_cross, smul_sub, sub_smul]
  abel

theorem outer_mul_certificateD (v : V n) (hv : ‖v‖ = 1) :
    outer v*certificateD v = (boostScale n)^2 • outer v := by
  rw [certificateD, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    outer_mul_projector v hv, outer_idempotent v hv, smul_zero, zero_add]

theorem ordered_factorization (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    unrotatedQ F v = certificateF F v*certificateD v := by
  obtain ⟨hk, hk1, hksq⟩ := boostScale_bounds hn
  have hb := inverseDimension_bounds hn
  have ha : boostParameter n ≤ 1/3 :=
    (Scalar.lorentz_parameter_bounds (inverseDimension n) hb.1 hb.2).2
  have ha0 : 1-boostParameter n ≠ 0 := by linarith
  have hc : (cutWeight n/(1-boostParameter n))*(boostScale n)^2 =
      cutWeight n*(1+boostParameter n) := by
    rw [hksq]
    field_simp [ha0] <;> ring
  have hFD : certificateF F v*certificateD v =
      boostScale n • weightedShape F (contactScalarFactor F v)+
      ((boostScale n)^2-boostScale n) • cross
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedShape F (contactScalarFactor F v)) v) v+
      (cutWeight n*(1+boostParameter n)) • outer v := by
    rw [certificateF, Matrix.add_mul, Matrix.smul_mul, mul_certificateD,
      outer_mul_certificateD v hv, smul_smul, hc]
  rw [hFD, unrotatedQ_decomposition, weighted_direction_balance F hn v hv,
    cross_sub_left, cross_smul_left, cross_smul_left, cross_self]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hksq]
  ring

theorem unrotatedQ_det_pos (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) :
    0 < (unrotatedQ F v).det := by
  rw [ordered_factorization F hn v hv, Matrix.det_mul]
  exact mul_pos (certificateF_posDef F hn v hv).det_pos (certificateD_posDef hn v hv).det_pos

end SharpCut.Certificate
