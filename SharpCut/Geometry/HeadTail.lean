import SharpCut.Geometry.AxialCoordinates

/-! # Euclidean head/tail vectors and axial block diagonal matrices -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Geometry
variable {m : ℕ}

def padTail (y : V m) : V (m+1) := WithLp.toLp 2 (Fin.cases 0 y.ofLp)
def tailVector (x : V (m+1)) : V m := WithLp.toLp 2 (fun i => x i.succ)

def diagAxis (a : ℝ) (E : MatR m) : MatR (m+1) :=
  Matrix.of (Fin.cases (Fin.cases a (fun _ => 0)) (fun i => Fin.cases 0 (fun j => E i j)))

@[simp] theorem padTail_zero (y : V m) : padTail y 0 = 0 := rfl
@[simp] theorem padTail_succ (y : V m) (i : Fin m) : padTail y i.succ = y i := rfl
@[simp] theorem tailVector_apply (x : V (m+1)) (i : Fin m) : tailVector x i = x i.succ := rfl
@[simp] theorem diagAxis_zero_zero (a : ℝ) (E : MatR m) : diagAxis a E 0 0 = a := rfl
@[simp] theorem diagAxis_zero_succ (a : ℝ) (E : MatR m) (i : Fin m) : diagAxis a E 0 i.succ = 0 := rfl
@[simp] theorem diagAxis_succ_zero (a : ℝ) (E : MatR m) (i : Fin m) : diagAxis a E i.succ 0 = 0 := rfl
@[simp] theorem diagAxis_succ_succ (a : ℝ) (E : MatR m) (i j : Fin m) : diagAxis a E i.succ j.succ = E i j := rfl

theorem padTail_tailVector (x : V (m+1)) (hx : x 0 = 0) : padTail (tailVector x) = x := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa only [padTail_zero] using hx.symm
  · rfl

theorem padTail_inner (x y : V m) : ⟪padTail x, padTail y⟫ = ⟪x, y⟫ := by
  rw [Khachiyan.inner_eq_dotProduct, Khachiyan.inner_eq_dotProduct]
  simp only [dotProduct, Fin.sum_univ_succ, padTail_zero, padTail_succ, zero_mul, zero_add]

theorem padTail_norm (y : V m) : ‖padTail y‖ = ‖y‖ := by
  have h := padTail_inner y y
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (padTail y), norm_nonneg y]

theorem diagAxis_one : diagAxis 1 (1 : MatR m) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, eq_comm]

theorem diagAxis_mul (a b : ℝ) (E F : MatR m) :
    diagAxis a E*diagAxis b F = diagAxis (a*b) (E*F) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply]

theorem diagAxis_trace (a : ℝ) (E : MatR m) : (diagAxis a E).trace = a+E.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_succ,
    diagAxis_zero_zero, diagAxis_succ_succ]

theorem diagAxis_inv_one (E : MatR m) (hE : E.PosDef) :
    (diagAxis 1 E)⁻¹ = diagAxis 1 E⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [diagAxis_mul, one_mul,
    Matrix.mul_nonsing_inv E (isUnit_iff_ne_zero.mpr hE.det_pos.ne'), diagAxis_one]

theorem diagAxis_action_pad (a : ℝ) (E : MatR m) (y : V m) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (diagAxis a E) (padTail y) =
      padTail (Matrix.toEuclideanCLM (𝕜 := ℝ) E y) := by
  apply WithLp.ofLp_injective 2
  funext i
  simp only [Khachiyan.matrix_action_ofLp, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [padTail_zero, diagAxis_zero_zero, diagAxis_zero_succ, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  · simp only [padTail_zero, padTail_succ, diagAxis_succ_zero, diagAxis_succ_succ,
      mul_zero, zero_add, Khachiyan.matrix_action_ofLp, Matrix.mulVec, dotProduct]

end SharpCut.Geometry
