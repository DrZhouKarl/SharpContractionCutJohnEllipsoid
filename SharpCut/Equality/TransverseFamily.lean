import SharpCut.Equality.Theorem

/-! # Arbitrary transverse John frames generate the full extremal contact family -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Equality
open Certificate
variable {n N : ℕ}

def familyRadius (n : ℕ) : ℝ := Real.sqrt (1-(inverseDimension n)^2)
def familyContact (v : V n) (w : Fin N → V n) : Fin (N+1) → V n :=
  Fin.cases (-v) (fun i => inverseDimension n • v+familyRadius n • w i)
def familyWeight (μ : Fin N → ℝ) : Fin (N+1) → ℝ :=
  Fin.cases (1/(1+inverseDimension n)) (fun i => μ i/(1-(inverseDimension n)^2))

theorem familyRadius_sq (hn : 2 ≤ n) : (familyRadius n)^2 = 1-(inverseDimension n)^2 := by
  have hb := inverseDimension_bounds hn
  exact Real.sq_sqrt (by nlinarith [hb.1, hb.2])

theorem transverse_weight_sum (v : V n) (hv : ‖v‖ = 1) (w : Fin N → V n) (μ : Fin N → ℝ)
    (hw : ∀ i, ‖w i‖ = 1) (hsecond : ∑ i, μ i • outer (w i) = projector v) :
    ∑ i, μ i = (n : ℝ)-1 := by
  have h := congrArg Matrix.trace hsecond
  simp only [Matrix.trace_sum, Matrix.trace_smul, Khachiyan.trace_outer, hw, one_pow,
    smul_eq_mul, mul_one, projector, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, hv] at h
  exact h

theorem latitude_weight_sum (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1)
    (w : Fin N → V n) (μ : Fin N → ℝ) (hw : ∀ i, ‖w i‖ = 1)
    (hsecond : ∑ i, μ i • outer (w i) = projector v) :
    (∑ i, μ i/(1-(inverseDimension n)^2)) = 1/(inverseDimension n*(1+inverseDimension n)) := by
  have hb := inverseDimension_bounds hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hq : 1-(inverseDimension n)^2 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hp : 1+inverseDimension n ≠ 0 := by linarith [hb.1]
  have hnb : (n : ℝ)*inverseDimension n = 1 := by unfold inverseDimension; field_simp [hn0]
  have he : ((n : ℝ)-1)*inverseDimension n*(1+inverseDimension n) = 1-(inverseDimension n)^2 := by
    linear_combination (1+inverseDimension n)*hnb
  rw [← Finset.sum_div, transverse_weight_sum v hv w μ hw hsecond]
  field_simp [hb.1.ne', hq, hp]
  linear_combination he

theorem family_contact_unit (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (w : Fin N → V n)
    (hw : ∀ i, ‖w i‖ = 1) (hperp : ∀ i, ⟪v, w i⟫ = 0) (j : Fin (N+1)) :
    ‖familyContact v w j‖ = 1 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [familyContact, Fin.cases_zero, norm_neg, hv]
  · have hs : ‖familyContact v w i.succ‖^2 = 1 := by
      simp only [familyContact, Fin.cases_succ]
      rw [norm_add_sq_real]
      simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hv, hw, one_pow, mul_one,
        real_inner_smul_left, real_inner_smul_right, hperp, mul_zero, zero_mul, add_zero]
      rw [familyRadius_sq hn]
      ring
    nlinarith [norm_nonneg (familyContact v w i.succ)]

theorem family_weight_pos (hn : 2 ≤ n) (μ : Fin N → ℝ) (hμ : ∀ i, 0 < μ i) (j : Fin (N+1)) :
    0 < familyWeight (n := n) μ j := by
  have hb := inverseDimension_bounds hn
  refine Fin.cases ?_ (fun i => ?_) j
  · exact div_pos (by norm_num) (by linarith [hb.1])
  · exact div_pos (hμ i) (by nlinarith [hb.1, hb.2])

theorem scaled_vector_balance (hn : 2 ≤ n) (w : Fin N → V n) (μ : Fin N → ℝ)
    (hfirst : ∑ i, μ i • w i = 0) :
    (∑ i, (μ i/(1-(inverseDimension n)^2)) • w i) = 0 := by
  calc
    _ = (1/(1-(inverseDimension n)^2)) • (∑ i, μ i • w i) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl; intro i hi; rw [smul_smul]; congr 1; ring
    _ = 0 := by rw [hfirst, smul_zero]

theorem family_first_moment (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (w : Fin N → V n)
    (μ : Fin N → ℝ) (hw : ∀ i, ‖w i‖ = 1) (hfirst : ∑ i, μ i • w i = 0)
    (hsecond : ∑ i, μ i • outer (w i) = projector v) :
    (∑ j, familyWeight (n := n) μ j • familyContact v w j) = 0 := by
  have hb := inverseDimension_bounds hn
  have hs := latitude_weight_sum hn v hv w μ hw hsecond
  have hz := scaled_vector_balance hn w μ hfirst
  simp only [familyWeight, familyContact, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
    smul_add, smul_smul, Finset.sum_add_distrib]
  have hvsum : (∑ i, (μ i/(1-(inverseDimension n)^2)*inverseDimension n) • v) =
      (inverseDimension n/(inverseDimension n*(1+inverseDimension n))) • v := by
    rw [← Finset.sum_smul, ← Finset.sum_mul, hs]
    congr 1
    ring
  have hwsum : (∑ i, (μ i/(1-(inverseDimension n)^2)*familyRadius n) • w i) = 0 := by
    have he := congrArg (fun u : V n => familyRadius n • u) hz
    rw [Finset.smul_sum] at he
    simpa only [smul_smul, mul_comm, smul_zero] using he
  rw [hvsum, hwsum, add_zero]
  have hc : inverseDimension n/(inverseDimension n*(1+inverseDimension n)) = 1/(1+inverseDimension n) := by
    field_simp [hb.1.ne', show 1+inverseDimension n ≠ 0 by linarith [hb.1]]
  rw [hc, smul_neg]
  abel

theorem family_second_moment (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (w : Fin N → V n)
    (μ : Fin N → ℝ) (hw : ∀ i, ‖w i‖ = 1) (hfirst : ∑ i, μ i • w i = 0)
    (hsecond : ∑ i, μ i • outer (w i) = projector v) :
    (∑ j, familyWeight (n := n) μ j • outer (familyContact v w j)) = 1 := by
  have hb := inverseDimension_bounds hn
  have hq : 1-(inverseDimension n)^2 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hp : 1+inverseDimension n ≠ 0 := by linarith [hb.1]
  have hs := latitude_weight_sum hn v hv w μ hw hsecond
  have hz := scaled_vector_balance hn w μ hfirst
  have hscalar : (∑ i, (μ i/(1-(inverseDimension n)^2))*(inverseDimension n)^2) =
      inverseDimension n/(1+inverseDimension n) := by
    rw [← Finset.sum_mul, hs]
    field_simp [hb.1.ne', hp]
  have hmix : (∑ i, (μ i/(1-(inverseDimension n)^2)*inverseDimension n*familyRadius n) • w i) = 0 := by
    have h := congrArg (fun u : V n => (inverseDimension n*familyRadius n) • u) hz
    rw [Finset.smul_sum] at h
    simpa only [smul_smul, mul_assoc, mul_left_comm, mul_comm, smul_zero] using h
  have hmatrix : (∑ i, (μ i/(1-(inverseDimension n)^2)) • outer (w i)) =
      (1/(1-(inverseDimension n)^2)) • projector v := by
    calc
      _ = (1/(1-(inverseDimension n)^2)) • (∑ i, μ i • outer (w i)) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl; intro i hi; rw [smul_smul]; congr 1; ring
      _ = _ := by rw [hsecond]
  have hneg : outer (-v) = outer v := by ext i j; simp [Khachiyan.outer_apply]
  have hr : cross v (0 : V n) = 0 := by ext i j; simp [cross, Matrix.vecMulVec_apply]
  have hl : cross (0 : V n) v = 0 := by ext i j; simp [cross, Matrix.vecMulVec_apply]
  simp only [familyWeight, familyContact, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
  rw [hneg, sum_axis_gram, hscalar, hmix, hr, hl, hmatrix, smul_smul, familyRadius_sq hn]
  simp only [add_zero]
  have hscale : (1-(inverseDimension n)^2)*(1/(1-(inverseDimension n)^2)) = 1 := by field_simp [hq]
  rw [hscale, one_smul, ← add_assoc, ← add_smul]
  have haxis : 1/(1+inverseDimension n)+inverseDimension n/(1+inverseDimension n) = 1 := by field_simp [hp]
  rw [haxis, one_smul, projector]
  abel

def frameFromTransverse (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (w : Fin N → V n)
    (μ : Fin N → ℝ) (hw : ∀ i, ‖w i‖ = 1) (hμ : ∀ i, 0 < μ i) (hperp : ∀ i, ⟪v, w i⟫ = 0)
    (hfirst : ∑ i, μ i • w i = 0) (hsecond : ∑ i, μ i • outer (w i) = projector v) : JohnFrame n (N+1) :=
  { contact := familyContact v w
    weight := familyWeight (n := n) μ
    contact_unit := family_contact_unit hn v hv w hw hperp
    weight_pos := family_weight_pos hn μ hμ
    first_moment := family_first_moment hn v hv w μ hw hfirst hsecond
    second_moment := family_second_moment hn v hv w μ hw hfirst hsecond }

/-- Proposition 5.2: arbitrary transverse John data produce an extremal John frame. -/
theorem transverse_extremal_construction (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (w : Fin N → V n)
    (μ : Fin N → ℝ) (hw : ∀ i, ‖w i‖ = 1) (hμ : ∀ i, 0 < μ i) (hperp : ∀ i, ⟪v, w i⟫ = 0)
    (hfirst : ∑ i, μ i • w i = 0) (hsecond : ∑ i, μ i • outer (w i) = projector v) :
    ∃ F : JohnFrame n (N+1), F.contact = familyContact v w ∧ F.weight = familyWeight (n := n) μ ∧
      ∀ j, F.contact j ∈ modelContactSet v := by
  refine ⟨frameFromTransverse hn v hv w μ hw hμ hperp hfirst hsecond, rfl, rfl, ?_⟩
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [frameFromTransverse, familyContact, Fin.cases_zero, modelContactSet,
      Set.mem_union, Set.mem_singleton_iff, true_or]
  · apply (modelContactSet_iff _ v (family_contact_unit hn v hv w hw hperp i.succ) hv).mpr
    right
    have hp : ⟪w i, v⟫ = 0 := by simpa only [real_inner_comm] using hperp i
    simp only [frameFromTransverse, familyContact, Fin.cases_succ, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hv, one_pow, mul_one, hp, mul_zero, add_zero]

end SharpCut.Equality
