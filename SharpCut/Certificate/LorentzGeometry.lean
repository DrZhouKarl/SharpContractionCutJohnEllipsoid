import SharpCut.JohnFrame
import SharpCut.Scalar.Constants
import SharpCut.Certificate.LorentzAlgebra

/-!
# Lorentz directions on the actual Euclidean sphere

The scalar numerator identity is now applied to Euclidean vectors. All
denominators are positive on the n ≥ 2 domain. The balanced weights and
directions are constructed from the defining John moments alone.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace SharpCut.Certificate

def boostParameter (n : ℕ) : ℝ := inverseDimension n/(2-inverseDimension n)
def cutWeight (n : ℕ) : ℝ := (1+inverseDimension n)/2

def transverse {n : ℕ} (v u : V n) : V n := u-⟪u, v⟫ • v

def lorentzDirection {n : ℕ} (v u : V n) : V n :=
  (1-boostParameter n*⟪u, v⟫)⁻¹ •
    ((⟪u, v⟫-boostParameter n) • v +
      Real.sqrt (1-(boostParameter n)^2) • transverse v u)

theorem axis_transverse_inner {n : ℕ} (v u : V n) (hv : ‖v‖ = 1) :
    ⟪v, transverse v u⟫ = 0 := by
  simp only [transverse, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hv, one_pow, mul_one]
  rw [real_inner_comm]
  ring

theorem transverse_norm_sq {n : ℕ} (v u : V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    ‖transverse v u‖^2 = 1-⟪u, v⟫^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [transverse, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hv, hu, one_pow, mul_one]
  rw [real_inner_comm v u]
  ring

theorem orthogonal_combination_norm_sq {n : ℕ} (v y : V n)
    (hv : ‖v‖ = 1) (hvy : ⟪v, y⟫ = 0) (a k : ℝ) :
    ‖a • v+k • y‖^2 = a^2+k^2*‖y‖^2 := by
  have hyv : ⟪y, v⟫ = 0 := by rw [real_inner_comm]; exact hvy
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, hv, one_pow, hvy, hyv]
  ring

theorem lorentzDirection_unit {n : ℕ} (hn : 2 ≤ n) (v u : V n)
    (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) : ‖lorentzDirection v u‖ = 1 := by
  let a := boostParameter n
  let s := ⟪u, v⟫
  let k := Real.sqrt (1-a^2)
  have hb := inverseDimension_bounds hn
  have ha : 0 < a ∧ a ≤ 1/3 :=
    Scalar.lorentz_parameter_bounds (inverseDimension n) hb.1 hb.2
  have ham := mul_nonneg ha.1.le (sub_nonneg.mpr ha.2)
  have hapos : 0 ≤ 1-a^2 := by nlinarith
  have hk : k^2 = 1-a^2 := Real.sq_sqrt hapos
  have hs : s ≤ 1 := by
    have h := real_inner_le_norm u v
    simpa only [hu, hv, mul_one] using h
  have hd : 0 < 1-a*s := by
    have h := certificate_denominator_lower hn hs
    change 2/3 ≤ 1-a*s at h
    linarith
  have hnum : ‖(s-a) • v+k • transverse v u‖^2 = (1-a*s)^2 := by
    rw [orthogonal_combination_norm_sq v (transverse v u) hv
      (axis_transverse_inner v u hv), hk, transverse_norm_sq v u hv hu]
    exact lorentz_norm_numerator a s
  have hnumeq : ‖(s-a) • v+k • transverse v u‖ = 1-a*s := by
    nlinarith [norm_nonneg ((s-a) • v+k • transverse v u)]
  change ‖(1-a*s)⁻¹ • ((s-a) • v+k • transverse v u)‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), hnumeq,
    inv_mul_cancel₀ hd.ne']

variable {n N : ℕ} (F : JohnFrame n N) (v : V n)

def originalWeight (i : Fin N) : ℝ :=
  F.weight i * (1-cutWeight n*⟪F.contact i, v⟫)

theorem originalWeight_lower (hn : 2 ≤ n) (hv : ‖v‖ = 1) (i : Fin N) :
    F.weight i/4 ≤ originalWeight F v i ∧ 0 < originalWeight F v i := by
  have hb := inverseDimension_bounds hn
  exact Scalar.balanced_weight_lower _ _ _ hb.1.le hb.2
    (F.heights_bounds v hv i).2 (F.weight_pos i)

theorem originalWeight_sum : ∑ i, originalWeight F v i = (n : ℝ) := by
  have ht : ∑ i, F.weight i*(cutWeight n*⟪F.contact i, v⟫) = 0 := by
    calc
      _ = cutWeight n * ∑ i, F.weight i*⟪F.contact i, v⟫ := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ = 0 := by rw [F.scalar_first_moment, mul_zero]
  simp only [originalWeight, mul_sub, mul_one, Finset.sum_sub_distrib,
    F.weight_sum, ht, sub_zero]

theorem balanced_normals :
    (∑ i, originalWeight F v i • F.contact i)+cutWeight n • v = 0 := by
  have ht : ∑ i, (F.weight i*(cutWeight n*⟪F.contact i, v⟫)) • F.contact i =
      cutWeight n • v := by
    calc
      _ = cutWeight n • ∑ i, (F.weight i*⟪F.contact i, v⟫) • F.contact i := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul]
        congr 1
        ring
      _ = _ := congrArg (fun x : V n => cutWeight n • x) (F.reconstruction v)
  simp only [originalWeight, mul_sub, mul_one, sub_smul,
    Finset.sum_sub_distrib, F.first_moment, ht, zero_sub, neg_add_cancel]

end SharpCut.Certificate
