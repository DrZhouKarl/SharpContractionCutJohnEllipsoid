import SharpCut.Geometry
import Khachiyan.ContactCertificate

/-!
# The normalized SOC log-determinant volume certificate

This is Lemma 2.1. The dual data store exactly the finite feasibility conditions,
not an assumed trace/determinant inequality. The determinant argument uses a
symmetric positive-definite conjugate, preserving multiplication order.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace SharpCut.Optimization
variable {n N : ℕ}

def constraintPolytope (g : Fin N → V n) (beta : Fin N → ℝ) : Set (V n) :=
  {x | ∀ r, ⟪g r, x⟫ ≤ beta r}

def PrimalFeasible (g : Fin N → V n) (beta : Fin N → ℝ) (c : V n) (A : MatR n) : Prop :=
  A.PosDef ∧ ∀ r, ⟪g r, c⟫ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ ≤ beta r

def symmetricOuter (q g : V n) : MatR n :=
  (1/2 : ℝ) • (Matrix.vecMulVec q.ofLp g.ofLp + Matrix.vecMulVec g.ofLp q.ofLp)

def aggregate (g q : Fin N → V n) : MatR n := ∑ r, symmetricOuter (q r) (g r)

structure DualFeasible (g : Fin N → V n) (beta alpha : Fin N → ℝ)
    (q : Fin N → V n) : Prop where
  cone : ∀ r, ‖q r‖ ≤ alpha r
  balance : ∑ r, alpha r • g r = 0
  normalization : ∑ r, alpha r * beta r = (n : ℝ)
  positive : (aggregate g q).PosDef

theorem primalFeasible_iff_containment (g : Fin N → V n) (beta : Fin N → ℝ)
    (c : V n) (A : MatR n) :
    PrimalFeasible g beta c A ↔ IsFeasible (constraintPolytope g beta) c A := by
  constructor
  · rintro ⟨hA, hsupport⟩
    refine ⟨hA, ?_⟩
    intro x hx r
    exact (Khachiyan.ellipsoid_support_le hA.isHermitian.isSymm hx).trans (hsupport r)
  · rintro ⟨hA, hsubset⟩
    refine ⟨hA, ?_⟩
    intro r
    obtain ⟨x, hx, heq⟩ := Khachiyan.ellipsoid_support_attained hA.isHermitian.isSymm (g r)
    have h := hsubset hx r
    rwa [heq] at h

theorem trace_mul_cross (A : MatR n) (g q : V n) :
    (A * Matrix.vecMulVec g.ofLp q.ofLp).trace =
      ⟪q, Matrix.toEuclideanCLM (𝕜 := ℝ) A g⟫ := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, Khachiyan.inner_matrix_action]
  exact dotProduct_comm _ _

theorem trace_mul_symmetricOuter {A : MatR n} (hA : A.IsSymm) (q g : V n) :
    (A * symmetricOuter q g).trace = ⟪q, Matrix.toEuclideanCLM (𝕜 := ℝ) A g⟫ := by
  unfold symmetricOuter
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add,
    trace_mul_cross, trace_mul_cross]
  rw [Khachiyan.inner_matrix_action_symm hA, real_inner_comm]
  ring

theorem dual_alpha_nonneg {g q : Fin N → V n} {beta alpha : Fin N → ℝ}
    (hd : DualFeasible g beta alpha q) (r : Fin N) : 0 ≤ alpha r :=
  (norm_nonneg (q r)).trans (hd.cone r)

theorem trace_bound {g q : Fin N → V n} {beta alpha : Fin N → ℝ}
    {c : V n} {A : MatR n}
    (hp : PrimalFeasible g beta c A) (hd : DualFeasible g beta alpha q) :
    (A * aggregate g q).trace ≤ (n : ℝ) := by
  have hbalance : ∑ r, alpha r * ⟪g r, c⟫ = 0 := by
    have h := congrArg (fun x : V n => ⟪x, c⟫) hd.balance
    simpa only [sum_inner, real_inner_smul_left, inner_zero_left] using h
  have heach (r : Fin N) : ⟪q r, Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ ≤
      alpha r * (beta r-⟪g r, c⟫) := by
    calc
      _ ≤ ‖q r‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ := real_inner_le_norm _ _
      _ ≤ alpha r * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ :=
        mul_le_mul_of_nonneg_right (hd.cone r) (norm_nonneg _)
      _ ≤ alpha r * (beta r-⟪g r, c⟫) :=
        mul_le_mul_of_nonneg_left (by linarith [hp.2 r]) (dual_alpha_nonneg hd r)
  calc
    _ = ∑ r, ⟪q r, Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ := by
      simp only [aggregate, Matrix.mul_sum, Matrix.trace_sum,
        trace_mul_symmetricOuter hp.1.isHermitian.isSymm]
    _ ≤ ∑ r, alpha r * (beta r-⟪g r, c⟫) := Finset.sum_le_sum (fun r _ => heach r)
    _ = (n : ℝ) := by
      simp only [mul_sub, Finset.sum_sub_distrib, hd.normalization, hbalance, sub_zero]

theorem det_mul_le_one_of_trace {A M : MatR n} (hA : A.PosDef) (hM : M.PosDef)
    (ht : (A*M).trace ≤ (n : ℝ)) : A.det * M.det ≤ 1 := by
  have hS : (CFC.sqrt M).PosDef := by
    rw [CFC.sqrt_eq_rpow]
    exact Khachiyan.Spectral.rpow_posDef hM _
  have hsym : (CFC.sqrt M)ᴴ = CFC.sqrt M := hS.isHermitian
  have hY := hA.conjTranspose_mul_mul_same hS.mulVec_injective
  rw [hsym] at hY
  have htrace : (CFC.sqrt M * A * CFC.sqrt M).trace = (A*M).trace := by
    rw [Matrix.trace_mul_cycle,
      CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg, Matrix.trace_mul_comm]
  have hdet : (CFC.sqrt M * A * CFC.sqrt M).det = A.det * M.det := by
    calc
      _ = A.det * (CFC.sqrt M * CFC.sqrt M).det := by
        simp only [Matrix.det_mul]
        ring
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg]
  have hyt : (CFC.sqrt M * A * CFC.sqrt M).trace ≤ (n : ℝ) := by
    rw [htrace]
    exact ht
  have h := Khachiyan.det_le_one_of_trace_le hY hyt
  rwa [hdet] at h

/-- Lemma 2.1, with every normalized dual constraint explicitly required. -/
theorem volume_certificate {g q : Fin N → V n} {beta alpha : Fin N → ℝ}
    {c : V n} {A : MatR n}
    (hp : PrimalFeasible g beta c A) (hd : DualFeasible g beta alpha q) :
    (A * aggregate g q).trace ≤ (n : ℝ) ∧ A.det ≤ 1/(aggregate g q).det := by
  have ht := trace_bound hp hd
  refine ⟨ht, ?_⟩
  apply (le_div_iff₀ hd.positive.det_pos).mpr
  exact det_mul_le_one_of_trace hp.1 hd.positive ht

end SharpCut.Optimization
