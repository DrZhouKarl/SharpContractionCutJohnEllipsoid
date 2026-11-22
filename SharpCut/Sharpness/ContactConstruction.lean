import SharpCut.JohnFrame.Finite
import SharpCut.Geometry.SharpUpper

/-! # Explicit pole-and-latitude contact vectors in every fixed dimension -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Sharpness
variable {m : ℕ}

def axis (m : ℕ) : V (m+1) := EuclideanSpace.single 0 (1 : ℝ)
def transverseBasis (m : ℕ) (k : Fin m) : V (m+1) := EuclideanSpace.single k.succ (1 : ℝ)
def latitudeScale (m : ℕ) : ℝ := Real.sqrt (1-(inverseDimension (m+1))^2)
abbrev ContactIndex (m : ℕ) := Unit ⊕ (Fin m × Bool)

def contact (m : ℕ) : ContactIndex m → V (m+1) :=
  Sum.elim (fun _ => -axis m) (fun i =>
    inverseDimension (m+1) • axis m+
      (if i.2 then latitudeScale m else -latitudeScale m) • transverseBasis m i.1)

def weight (m : ℕ) : ContactIndex m → ℝ :=
  Sum.elim (fun _ => 1/(1+inverseDimension (m+1)))
    (fun _ => 1/(2*(1-(inverseDimension (m+1))^2)))

@[simp] theorem axis_norm (m : ℕ) : ‖axis m‖ = 1 := by simp [axis]
@[simp] theorem basis_norm (m : ℕ) (k : Fin m) : ‖transverseBasis m k‖ = 1 := by simp [transverseBasis]
@[simp] theorem axis_zero (m : ℕ) : axis m 0 = 1 := by simp [axis]
@[simp] theorem axis_succ (m : ℕ) (k : Fin m) : axis m k.succ = 0 := by simp [axis]
@[simp] theorem basis_zero (m : ℕ) (k : Fin m) : transverseBasis m k 0 = 0 := by simp [transverseBasis, eq_comm]
@[simp] theorem basis_succ (m : ℕ) (i k : Fin m) :
    transverseBasis m k i.succ = if i = k then 1 else 0 := by simp [transverseBasis]

theorem axis_basis_orthogonal (m : ℕ) (k : Fin m) : ⟪axis m, transverseBasis m k⟫ = 0 := by
  rw [axis, EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul, basis_zero]

theorem latitudeScale_sq (hm : 1 ≤ m) : (latitudeScale m)^2 = 1-(inverseDimension (m+1))^2 := by
  have hb := inverseDimension_bounds (show 2 ≤ m+1 by omega)
  have hp : 0 ≤ 1-(inverseDimension (m+1))^2 := by nlinarith [hb.1, hb.2]
  exact Real.sq_sqrt hp

theorem contact_unit (hm : 1 ≤ m) (i : ContactIndex m) : ‖contact m i‖ = 1 := by
  cases i with
  | inl i => simp [contact]
  | inr i =>
    have hb := inverseDimension_bounds (show 2 ≤ m+1 by omega)
    have hs := latitudeScale_sq hm
    have hnorm : ‖contact m (Sum.inr i)‖^2 = 1 := by
      simp only [contact, Sum.elim_inr]
      rw [norm_add_sq_real]
      simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, axis_norm, basis_norm, one_pow, mul_one,
        real_inner_smul_left, real_inner_smul_right, axis_basis_orthogonal, mul_zero, zero_mul, zero_add, add_zero]
      cases i.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true, neg_sq] <;> nlinarith only [hs]
    nlinarith [norm_nonneg (contact m (Sum.inr i))]

theorem weight_pos (hm : 1 ≤ m) (i : ContactIndex m) : 0 < weight m i := by
  have hb := inverseDimension_bounds (show 2 ≤ m+1 by omega)
  have hp : 0 < 1-(inverseDimension (m+1))^2 := by nlinarith [hb.1, hb.2]
  cases i with
  | inl i => exact div_pos (by norm_num) (by linarith [hb.1])
  | inr i => exact div_pos (by norm_num) (mul_pos (by norm_num) hp)

theorem sum_outer_standard (n : ℕ) :
    (∑ k : Fin n, outer (EuclideanSpace.single k (1 : ℝ))) = (1 : MatR n) := by
  ext i j
  simp only [Matrix.sum_apply, Khachiyan.outer_apply, EuclideanSpace.single_apply, Matrix.one_apply,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [eq_comm]

theorem transverse_outer_sum (m : ℕ) :
    (∑ k : Fin m, outer (transverseBasis m k)) = Certificate.projector (axis m) := by
  have h := sum_outer_standard (m+1)
  rw [Fin.sum_univ_succ] at h
  change outer (axis m)+(∑ k : Fin m, outer (transverseBasis m k)) = 1 at h
  unfold Certificate.projector
  calc
    _ = (outer (axis m)+(∑ k : Fin m, outer (transverseBasis m k)))-outer (axis m) := by abel
    _ = _ := by rw [h]

end SharpCut.Sharpness
