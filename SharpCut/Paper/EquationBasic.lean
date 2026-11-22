import SharpCut.Optimization.Gaps
import SharpCut.FiniteReduction
import SharpCut.Certificate.Feasibility

/-! # Explicit equation correspondence for the initial certificate/reduction calculations

The named results already admit equivalent proofs. These lemmas retain the
independently displayed intermediate chains (2.6), (2.7) and (2.19).
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix Set
namespace SharpCut.Paper
open Optimization
variable {n N : ℕ}

theorem positive_det_le_mean_trace (hn : 1 ≤ n) (Y : MatR n) (hY : Y.PosDef) :
    Y.det ≤ (Y.trace/(n : ℝ))^n := by
  letI : NeZero n := ⟨by omega⟩
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have htrace : 0 < Y.trace := hY.trace_pos
  have hscale : (((n : ℝ)/Y.trace) • Y).PosDef := hY.smul (div_pos hnreal htrace)
  have ht : (((n : ℝ)/Y.trace) • Y).trace ≤ (n : ℝ) := by
    simpa only [Matrix.trace_smul,smul_eq_mul,div_mul_cancel₀ _ htrace.ne'] using (le_rfl : (n : ℝ) ≤ n)
  have h := Khachiyan.det_le_one_of_trace_le hscale ht
  rw [Matrix.det_smul,Fintype.card_fin] at h
  have hmul := mul_le_mul_of_nonneg_left h (pow_nonneg (div_nonneg htrace.le hnreal.le) n)
  have hc : (Y.trace/(n : ℝ))^n*((n : ℝ)/Y.trace)^n = 1 := by
    rw [← mul_pow]
    have he : (Y.trace/(n : ℝ))*((n : ℝ)/Y.trace) = 1 := by field_simp [htrace.ne',hnreal.ne']
    rw [he,one_pow]
  have he : (Y.trace/(n : ℝ))^n*(((n : ℝ)/Y.trace)^n*Y.det) = Y.det := by rw [← mul_assoc,hc,one_mul]
  rwa [he,mul_one] at hmul

theorem normalized_trace_chain {g q : Fin N → V n} {β α : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g β c A) (hd : DualFeasible g β α q) :
    (A*aggregate g q).trace = ∑ r, ⟪q r,Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ ∧
    (∑ r, ⟪q r,Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫) ≤ ∑ r, α r*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ ∧
    (∑ r, α r*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖) ≤ ∑ r, α r*(β r-⟪g r,c⟫) ∧
    (∑ r, α r*(β r-⟪g r,c⟫)) = (n : ℝ) := by
  have hbal : (∑ r, α r*⟪g r,c⟫) = 0 := by
    have h := congrArg (fun x : V n => ⟪x,c⟫) hd.balance
    simpa only [sum_inner,real_inner_smul_left,inner_zero_left] using h
  refine ⟨?_,?_,?_,?_⟩
  · simp only [aggregate,Matrix.mul_sum,Matrix.trace_sum,trace_mul_symmetricOuter hp.1.isHermitian.isSymm]
  · apply Finset.sum_le_sum
    intro r _
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hd.cone r) (norm_nonneg _))
  · exact Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (by linarith only [hp.2 r]) (dual_alpha_nonneg hd r))
  · simp only [mul_sub,Finset.sum_sub_distrib,hd.normalization,hbal,sub_zero]

theorem active_facet_support_chain {g : Fin N → V n} {β : Fin N → ℝ} {c p : V n} {A : MatR n}
    (hp : PrimalFeasible g β c A) (r : Fin N) (hunit : ‖p‖ = 1)
    (hactive : ⟪g r,c⟫+⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r),p⟫ = β r) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ ≤ β r-⟪g r,c⟫ ∧
    β r-⟪g r,c⟫ = ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r),p⟫ ∧
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r),p⟫ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖*‖p‖ ∧
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖*‖p‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ := by
  exact ⟨by linarith only [hp.2 r],by linarith only [hactive],real_inner_le_norm _ _,by rw [hunit,mul_one]⟩

theorem frame_balanced_weight_chain (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n) (hv : ‖v‖ = 1) (i : Fin N) :
    F.weight i*(1-Certificate.cutWeight n) ≤ Certificate.originalWeight F v i ∧
    F.weight i/4 ≤ F.weight i*(1-Certificate.cutWeight n) := by
  have hb := inverseDimension_bounds hn
  have ht : 0 ≤ Certificate.cutWeight n := by unfold Certificate.cutWeight; linarith only [hb.1]
  have hlow : (1/4 : ℝ) ≤ 1-Certificate.cutWeight n := by unfold Certificate.cutWeight; linarith only [hb.2]
  have hs := mul_le_mul_of_nonneg_left (F.heights_bounds v hv i).2 ht
  refine ⟨?_,?_⟩
  · change F.weight i*(1-Certificate.cutWeight n) ≤ F.weight i*(1-Certificate.cutWeight n*⟪F.contact i,v⟫)
    exact mul_le_mul_of_nonneg_left (by linarith only [hs]) (F.weight_pos i).le
  · simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hlow (F.weight_pos i).le

theorem normalized_determinant_chain (hn : 1 ≤ n) {g q : Fin N → V n} {β α : Fin N → ℝ} {c : V n} {A : MatR n}
    (hp : PrimalFeasible g β c A) (hd : DualFeasible g β α q) :
    let Y := matchingMatrix A (aggregate g q)
    A.det*(aggregate g q).det = Y.det ∧ Y.det = ∏ i, (matchingMatrix_posDef A _ hp.1 hd.positive).isHermitian.eigenvalues i ∧
    Y.det ≤ ((A*aggregate g q).trace/(n : ℝ))^n ∧ ((A*aggregate g q).trace/(n : ℝ))^n ≤ 1 := by
  letI : NeZero n := ⟨by omega⟩
  have hY := matchingMatrix_posDef A (aggregate g q) hp.1 hd.positive
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht := trace_bound hp hd
  have hpos : 0 < (A*aggregate g q).trace := by
    rw [← matchingMatrix_trace A _ hd.positive]
    exact hY.trace_pos
  have hdet := positive_det_le_mean_trace hn _ hY
  rw [matchingMatrix_trace A _ hd.positive] at hdet
  refine ⟨(matchingMatrix_det A _ hd.positive).symm,hY.isHermitian.det_eq_prod_eigenvalues,hdet,?_⟩
  have hmean : (A*aggregate g q).trace/(n : ℝ) ≤ 1 := (div_le_iff₀ hnreal).mpr (by simpa only [one_mul] using ht)
  simpa only [one_pow] using pow_le_pow_left₀ (div_nonneg hpos.le hnreal.le) hmean n

theorem frame_radius_polynomial (F : JohnFrame n N) (x : V n) :
    (∑ i, F.weight i*(1-⟪F.contact i,x⟫)*(‖x‖+⟪F.contact i,x⟫)) = (n : ℝ)*‖x‖-‖x‖^2 := by
  have he (i : Fin N) : F.weight i*(1-⟪F.contact i,x⟫)*(‖x‖+⟪F.contact i,x⟫) =
      ‖x‖*F.weight i+(1-‖x‖)*(F.weight i*⟪F.contact i,x⟫)-F.weight i*⟪F.contact i,x⟫^2 := by ring
  simp only [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    F.weight_sum,F.scalar_first_moment,F.scalar_second_moment,mul_zero,add_zero]
  ring

theorem frame_radius_polynomial_nonneg (F : JohnFrame n N) {x : V n} (hx : x ∈ F.polytope) :
    0 ≤ ∑ i, F.weight i*(1-⟪F.contact i,x⟫)*(‖x‖+⟪F.contact i,x⟫) := by
  apply Finset.sum_nonneg
  intro i _
  have h := abs_real_inner_le_norm (F.contact i) x
  rw [F.contact_unit i,one_mul] at h
  have hlo := (abs_le.mp h).1
  exact mul_nonneg (mul_nonneg (F.weight_pos i).le (sub_nonneg.mpr (hx i))) (by linarith only [hlo])

end SharpCut.Paper
