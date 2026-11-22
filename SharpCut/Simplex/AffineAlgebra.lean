import SharpCut.Simplex.Model
import SharpCut.Stability.BlockNorm

/-! # Explicit affine interpolation of every simplex vertex

The matrix is a cross covariance against the certified regular vertices.
Affine independence of the arbitrary vertices proves its invertibility;
invertibility and the desired covariance are not assumed.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix Set
namespace SharpCut.Simplex
open Certificate
variable {m : ℕ}

def frameScale (m : ℕ) : ℝ := ((m : ℝ)+1)*((m : ℝ)+2)
def centroid (p : Fin (m+2) → V (m+1)) : V (m+1) := (1/((m : ℝ)+2)) • (∑ i, p i)
def centered (p : Fin (m+2) → V (m+1)) (i : Fin (m+2)) : V (m+1) := p i-centroid p
def interpolationMatrix (p : Fin (m+2) → V (m+1)) : MatR (m+1) :=
  (1/frameScale m) • (∑ i, cross (centered p i) (vertex m i))

theorem frameScale_pos (m : ℕ) : 0 < frameScale m := by unfold frameScale; positivity

theorem centered_sum (p : Fin (m+2) → V (m+1)) : (∑ i, centered p i) = 0 := by
  have hconst : (∑ _ : Fin (m+2), centroid p) = ((m : ℝ)+2) • centroid p := by
    have h : (∑ _ : Fin (m+2), centroid p) = (∑ _ : Fin (m+2), (1 : ℝ)) • centroid p := by
      rw [Finset.sum_smul]
      simp only [one_smul]
    rw [h]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_add,Nat.cast_ofNat]
  have hc : centered p = (fun i => p i-centroid p) := by funext i; rfl
  rw [hc]
  rw [Finset.sum_sub_distrib,hconst,centroid,smul_smul]
  have hp : (m : ℝ)+2 ≠ 0 := by positivity
  rw [mul_one_div_cancel hp,one_smul,sub_self]

theorem centered_vertex_gram (p : Fin (m+2) → V (m+1)) (j : Fin (m+2)) :
    (∑ i, ⟪vertex m i,vertex m j⟫ • centered p i) = frameScale m • centered p j := by
  classical
  have he (i : Fin (m+2)) : ⟪vertex m i,vertex m j⟫ =
      (if i = j then frameScale m else 0)-((m : ℝ)+1) := by
    rw [vertex_gram_all,frameScale]
    split_ifs <;> ring
  simp only [he,sub_smul,ite_smul,zero_smul,Finset.sum_sub_distrib,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,← Finset.smul_sum,centered_sum,smul_zero,sub_zero]

theorem interpolation_vertex (p : Fin (m+2) → V (m+1)) (j : Fin (m+2)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (interpolationMatrix p) (vertex m j) = centered p j := by
  rw [interpolationMatrix,matrix_action_smul,matrix_action_sum]
  simp only [Stability.cross_action]
  rw [centered_vertex_gram,smul_smul,one_div,inv_mul_cancel₀ (frameScale_pos m).ne',one_smul]

theorem vertex_reconstruction (m : ℕ) (x : V (m+1)) :
    (∑ i, ⟪vertex m i,x⟫ • vertex m i) = frameScale m • x := by
  have h := congrArg (fun A : MatR (m+1) => Matrix.toEuclideanCLM (𝕜 := ℝ) A x) (vertex_outer_sum m)
  simpa only [matrix_action_sum,Khachiyan.outer_action,matrix_action_smul,map_one,ContinuousLinearMap.one_apply,frameScale] using h

theorem interpolation_kernel_zero (p : Fin (m+2) → V (m+1)) (hp : AffineIndependent ℝ p)
    (x : V (m+1)) (hx : Matrix.toEuclideanCLM (𝕜 := ℝ) (interpolationMatrix p) x = 0) : x = 0 := by
  let a : Fin (m+2) → ℝ := fun i => ⟪vertex m i,x⟫
  have ha : (∑ i, a i) = 0 := by
    have h := congrArg (fun z : V (m+1) => ⟪z,x⟫) (vertex_sum m)
    simpa only [sum_inner,inner_zero_left] using h
  have hrec : (∑ i, a i • vertex m i) = frameScale m • x := vertex_reconstruction m x
  have hcentered : (∑ i, a i • centered p i) = 0 := by
    have h := congrArg (fun z : V (m+1) => Matrix.toEuclideanCLM (𝕜 := ℝ) (interpolationMatrix p) z) hrec
    simpa only [map_sum,map_smul,interpolation_vertex,hx,smul_zero] using h
  have hpoints : (∑ i, a i • p i) = 0 := by
    have he (i : Fin (m+2)) : p i = centered p i+centroid p := by simp only [centered,sub_add_cancel]
    calc
      _ = ∑ i, a i • (centered p i+centroid p) := Finset.sum_congr rfl (fun i _ => congrArg (fun z => a i • z) (he i))
      _ = (∑ i, a i • centered p i)+(∑ i, a i) • centroid p := by
        simp only [smul_add,Finset.sum_add_distrib,← Finset.sum_smul]
      _ = 0 := by rw [hcentered,ha,zero_smul,zero_add]
  have hweighted : Finset.univ.weightedVSub p a = (0 : V (m+1)) := by
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero Finset.univ a p ha (0 : V (m+1)),
      Finset.weightedVSubOfPoint_apply]
    simpa only [vsub_eq_sub,sub_zero] using hpoints
  have hz : ∀ i, a i = 0 := (affineIndependent_iff_of_fintype ℝ p).mp hp a ha hweighted
  simp only [hz,zero_smul,Finset.sum_const_zero] at hrec
  exact (smul_eq_zero.mp hrec.symm).resolve_left (frameScale_pos m).ne'

theorem interpolation_det_isUnit (p : Fin (m+2) → V (m+1)) (hp : AffineIndependent ℝ p) :
    IsUnit (interpolationMatrix p).det := by
  have hlin : Function.Injective (Matrix.toEuclideanCLM (𝕜 := ℝ) (interpolationMatrix p)) := by
    intro x y he
    have hzero : Matrix.toEuclideanCLM (𝕜 := ℝ) (interpolationMatrix p) (x-y) = 0 := by rw [map_sub,he,sub_self]
    exact sub_eq_zero.mp (interpolation_kernel_zero p hp (x-y) hzero)
  have hvec : Function.Injective (interpolationMatrix p).mulVec := by
    intro x y he
    have h : Matrix.toEuclideanCLM (𝕜 := ℝ) (interpolationMatrix p) (WithLp.toLp 2 x) =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (interpolationMatrix p) (WithLp.toLp 2 y) := by
      apply WithLp.ofLp_injective 2
      simpa only [Khachiyan.matrix_action_ofLp,WithLp.ofLp_toLp] using he
    have hxy := hlin h
    exact congrArg WithLp.ofLp hxy
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hvec)

theorem outer_linear_image (C : MatR (m+1)) (u : V (m+1)) :
    outer (Matrix.toEuclideanCLM (𝕜 := ℝ) C u) = C*outer u*Cᵀ := by
  have ho (v : V (m+1)) : outer v = Matrix.vecMulVec v.ofLp v.ofLp := by ext i j; rfl
  rw [ho,ho,Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul,Matrix.vecMul_transpose,Khachiyan.matrix_action_ofLp]

theorem centered_covariance (p : Fin (m+2) → V (m+1)) :
    (∑ i, outer (centered p i)) = frameScale m • (interpolationMatrix p*(interpolationMatrix p)ᵀ) := by
  have he (i : Fin (m+2)) : outer (centered p i) = interpolationMatrix p*outer (vertex m i)*(interpolationMatrix p)ᵀ := by
    rw [← interpolation_vertex p i,outer_linear_image]
  simp only [he,← Matrix.mul_sum,← Matrix.sum_mul,vertex_outer_sum,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]
  rfl

end SharpCut.Simplex
