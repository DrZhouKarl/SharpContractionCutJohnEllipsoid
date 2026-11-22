import SharpCut.Certificate.MatrixGeometry
import SharpCut.Certificate.NormalizedBlocks

/-! # The explicit homogeneous Lorentz block action recorded in (10.27) -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

def homogeneousPoint (t : ℝ) (u : V n) : V (n+1) := WithLp.toLp 2 (Fin.cases t u.ofLp)

def homogeneousLorentzBlock (v : V n) : MatR (n+1) :=
  Matrix.of (Fin.cases
    (Fin.cases 1 (fun j => -boostParameter n*v j))
    (fun i => Fin.cases (-boostParameter n*v i) (fun j => (outer v+boostScale n • projector v) i j)))

@[simp] theorem homogeneousPoint_zero (t : ℝ) (u : V n) : homogeneousPoint t u 0 = t := rfl
@[simp] theorem homogeneousPoint_succ (t : ℝ) (u : V n) (i : Fin n) : homogeneousPoint t u i.succ = u i := rfl

/-- Exact action of the actual (n+1)-dimensional block matrix, for every Euclidean u. -/
theorem homogeneous_lorentz_action (v u : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (homogeneousLorentzBlock v) (homogeneousPoint 1 u) =
      homogeneousPoint (1-boostParameter n*⟪u,v⟫)
        ((⟪u,v⟫-boostParameter n) • v+boostScale n • transverse v u) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Khachiyan.matrix_action_ofLp]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, homogeneousLorentzBlock, Matrix.of_apply,
      Fin.cases_zero, Fin.cases_succ, homogeneousPoint_zero, homogeneousPoint_succ, mul_one]
    rw [Khachiyan.inner_eq_dotProduct]
    simp only [dotProduct]
    have hs : (∑ j, (-boostParameter n*v j)*u j) = -boostParameter n*(∑ j, u j*v j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hs]
    ring
  · rw [Khachiyan.matrix_action_ofLp]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, homogeneousLorentzBlock, Matrix.of_apply,
      Fin.cases_zero, Fin.cases_succ, homogeneousPoint_zero, homogeneousPoint_succ, mul_one]
    have hsum : (∑ j, (outer v+boostScale n • projector v) i j*u j) =
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (outer v+boostScale n • projector v) u) i := by
      rw [Khachiyan.matrix_action_ofLp]
      rfl
    rw [hsum, matrix_action_add, matrix_action_smul, Khachiyan.outer_action, projector_action]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [real_inner_comm u v]
    ring

/-- Division by the positive first component is exactly the original unit Lorentz direction. -/
theorem homogeneous_lorentz_contact (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (i : Fin N) :
    0 < 1-boostParameter n*⟪F.contact i,v⟫ ∧
    lorentzDirection v (F.contact i) = (1-boostParameter n*⟪F.contact i,v⟫)⁻¹ •
      ((⟪F.contact i,v⟫-boostParameter n) • v+boostScale n • transverse v (F.contact i)) ∧
    ‖lorentzDirection v (F.contact i)‖ = 1 :=
  ⟨height_denominator_pos F hn v hv i, rfl, lorentzDirection_unit hn v (F.contact i) hv (F.contact_unit i)⟩

end SharpCut.Certificate
