import SharpCut.John.PolarBody
import SharpCut.John.CompactConvexHull
import SharpCut.John.FeasiblePerturbation
import SharpCut.Optimization.Certificate

/-!
# Euclidean contact moments and separating quadratic forms

The moment space records vector coordinates and all matrix coordinates. Its
Euclidean norm is used throughout. Symmetrizing the matrix component preserves
its pairing with contact atoms and its trace; no matrix commutativity is used.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix Set
namespace SharpCut.John
variable {n : ℕ}

abbrev MomentSpace (n : ℕ) := EuclideanSpace ℝ (Fin n ⊕ (Fin n × Fin n))

def contactAtom (u : V n) : MomentSpace n :=
  WithLp.toLp 2 (Sum.elim (fun i => u i) (fun ij => u ij.1*u ij.2))

def targetMoment (n : ℕ) : MomentSpace n :=
  WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun ij => (1 : MatR n) ij.1 ij.2/(n : ℝ)))

def vectorCoefficient (z : MomentSpace n) : V n := WithLp.toLp 2 (fun i => z (Sum.inl i))
def matrixCoefficient (z : MomentSpace n) : MatR n := fun i j => z (Sum.inr (i, j))
def symmetricCoefficient (z : MomentSpace n) : MatR n :=
  (1/2 : ℝ) • (matrixCoefficient z+(matrixCoefficient z)ᵀ)
def separatingShape (z : MomentSpace n) (c : ℝ) : MatR n :=
  symmetricCoefficient z-c • 1

@[simp] theorem contactAtom_inl (u : V n) (i : Fin n) : contactAtom u (Sum.inl i) = u i := rfl
@[simp] theorem contactAtom_inr (u : V n) (i j : Fin n) :
    contactAtom u (Sum.inr (i, j)) = u i*u j := rfl
@[simp] theorem targetMoment_inl (i : Fin n) : targetMoment n (Sum.inl i) = 0 := rfl
@[simp] theorem targetMoment_inr (i j : Fin n) :
    targetMoment n (Sum.inr (i, j)) = (1 : MatR n) i j/(n : ℝ) := rfl

theorem moment_inner (x y : MomentSpace n) : ⟪x, y⟫ = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

theorem contactAtom_continuous : Continuous (contactAtom (n := n)) := by
  unfold contactAtom
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n ⊕ (Fin n × Fin n) => ℝ)).comp
  apply continuous_pi
  intro i
  cases i with
  | inl j =>
    change Continuous (fun u : V n => u j)
    fun_prop
  | inr ij =>
    change Continuous (fun u : V n => u ij.1*u ij.2)
    fun_prop

theorem contactAtoms_isCompact {K : Set (V n)} (hball : unitBall n ⊆ K) :
    IsCompact (contactAtom '' contacts K) :=
  (contacts_isCompact hball).image contactAtom_continuous

theorem atom_pairing (z : MomentSpace n) (u : V n) :
    ⟪z, contactAtom u⟫ = ⟪vectorCoefficient z, u⟫+
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCoefficient z) u⟫ := by
  rw [moment_inner, Khachiyan.inner_eq_dotProduct, Khachiyan.inner_matrix_action]
  simp only [contactAtom, vectorCoefficient, matrixCoefficient, WithLp.ofLp_toLp,
    dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, Matrix.mulVec, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change z (Sum.inr (i, j))*(u i*u j) = u i*(z (Sum.inr (i, j))*u j)
  ring

theorem target_pairing (z : MomentSpace n) :
    ⟪z, targetMoment n⟫ = (matrixCoefficient z).trace/(n : ℝ) := by
  rw [moment_inner]
  unfold dotProduct
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [targetMoment_inl, targetMoment_inr, mul_zero, Finset.sum_const_zero, zero_add]
  have ht (i j : Fin n) : z (Sum.inr (i, j))*((1 : MatR n) i j/(n : ℝ)) =
      if j = i then z (Sum.inr (i, i))/(n : ℝ) else 0 := by
    by_cases h : j = i
    · subst j; simp [Matrix.one_apply, div_eq_mul_inv]
    · simp [Matrix.one_apply, h, Ne.symm h]
  simp_rw [ht]
  simp [matrixCoefficient, Matrix.trace, Finset.sum_div]

theorem symmetricCoefficient_quadratic (z : MomentSpace n) (u : V n) :
    ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (symmetricCoefficient z) u⟫ =
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCoefficient z) u⟫ := by
  have ho : (outer u)ᵀ = outer u := by
    ext i j
    simp only [Matrix.transpose_apply, Khachiyan.outer_apply]
    ring
  have ht : ((matrixCoefficient z)ᵀ * outer u).trace = (matrixCoefficient z * outer u).trace := by
    calc
      _ = ((outer u * matrixCoefficient z)ᵀ).trace := by rw [Matrix.transpose_mul, ho]
      _ = (outer u * matrixCoefficient z).trace := Matrix.trace_transpose _
      _ = _ := Matrix.trace_mul_comm _ _
  have hcross (A : MatR n) : (A * outer u).trace =
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) A u⟫ := Optimization.trace_mul_cross A u u
  rw [← hcross, symmetricCoefficient, Matrix.smul_mul, Matrix.add_mul,
    Matrix.trace_smul, Matrix.trace_add, ht, hcross]
  simp only [smul_eq_mul]
  ring

theorem separatingShape_symmetric (z : MomentSpace n) (c : ℝ) : (separatingShape z c).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [separatingShape, symmetricCoefficient, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · subst j; ring
  · simp only [hij, Ne.symm hij, if_false]
    ring

theorem separatingShape_contact_pairing (z : MomentSpace n) (c : ℝ) (u : V n)
    (hu : ‖u‖ = 1) : perturbSlope (vectorCoefficient z) (separatingShape z c) u =
      ⟪z, contactAtom u⟫-c := by
  have hshape : ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (separatingShape z c) u⟫ =
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (symmetricCoefficient z) u⟫-c*‖u‖^2 := by
    have hs : u.ofLp ⬝ᵥ u.ofLp = ‖u‖^2 := by
      rw [← Khachiyan.inner_eq_dotProduct u u, real_inner_self_eq_norm_sq]
    simp only [Khachiyan.inner_matrix_action, separatingShape, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, hs, smul_eq_mul]
  unfold perturbSlope
  rw [hshape, symmetricCoefficient_quadratic, atom_pairing, hu, one_pow, mul_one]
  ring

theorem separatingShape_trace (z : MomentSpace n) (c : ℝ) :
    (separatingShape z c).trace = (matrixCoefficient z).trace-(n : ℝ)*c := by
  simp only [separatingShape, symmetricCoefficient, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_transpose, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  ring

theorem separatingShape_trace_positive {n : ℕ} (hn : 1 ≤ n) (z : MomentSpace n)
    (c : ℝ) (hc : c < ⟪z, targetMoment n⟫) : 0 < (separatingShape z c).trace := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [target_pairing] at hc
  have hmul := (lt_div_iff₀ hp).mp hc
  rw [separatingShape_trace]
  nlinarith

end SharpCut.John
