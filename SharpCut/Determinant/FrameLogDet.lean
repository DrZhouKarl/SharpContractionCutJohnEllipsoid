import SharpCut.Determinant.MinorWeights
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Finite-frame log-determinant inequality with exact minor marginals -/

noncomputable section
open scoped BigOperators
open Matrix Finset Set
namespace SharpCut.Determinant
variable {n N : ℕ}

theorem minor_log_marginal_sum (X : Matrix (Fin n) (Fin N) ℝ) (hX : X*Xᵀ = 1)
    (L : Fin N → ℝ) :
    (∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
      minorWeight X s*∑ i ∈ s, L i) = ∑ i, ‖columnVector X i‖^2*L i := by
  let t := (Finset.univ : Finset (Fin N)).powersetCard n
  have hin (s : Finset (Fin N)) : minorWeight X s*(∑ i ∈ s, L i) =
      ∑ i : Fin N, if i ∈ s then minorWeight X s*L i else 0 := by
    have hf : Finset.univ.filter (fun i : Fin N => i ∈ s) = s := by ext i; simp
    rw [Finset.mul_sum, ← Finset.sum_filter, hf]
  calc
    _ = ∑ s ∈ t, ∑ i : Fin N, if i ∈ s then minorWeight X s*L i else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hin s
    _ = ∑ i : Fin N, ∑ s ∈ t, if i ∈ s then minorWeight X s*L i else 0 := Finset.sum_comm
    _ = ∑ i : Fin N, (∑ s ∈ t, if i ∈ s then minorWeight X s else 0)*L i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      simp only [ite_mul, zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [minor_column_marginal X hX i]

theorem finite_frame_logdet (X : Matrix (Fin n) (Fin N) ℝ) (hX : X*Xᵀ = 1)
    (f : Fin N → ℝ) (hf : ∀ i, 0 < f i) :
    (∑ i, ‖columnVector X i‖^2*Real.log (f i)) ≤ Real.log (weightedGram X f).det := by
  let t := (Finset.univ : Finset (Fin N)).powersetCard n
  have hsum : ∑ s ∈ t, minorWeight X s = 1 := minor_weights_sum X hX
  have hpos : ∀ s ∈ t, (∏ i ∈ s, f i) ∈ Ioi (0 : ℝ) := by
    intro s hs
    exact Finset.prod_pos (fun i hi => hf i)
  have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (fun s (_ : s ∈ t) => minorWeight_nonneg X s) hsum hpos
  simp only [smul_eq_mul] at h
  have hlog (s : Finset (Fin N)) : Real.log (∏ i ∈ s, f i) = ∑ i ∈ s, Real.log (f i) :=
    Real.log_prod (fun i hi => (hf i).ne')
  simp_rw [hlog] at h
  rw [minor_log_marginal_sum X hX] at h
  rw [weighted_gram_expansion X f]
  exact h

end SharpCut.Determinant
