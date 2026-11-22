import SharpCut.Optimization.Exact.RecoveredMoments
import Mathlib.Data.Finset.Max

/-! # The spectral trace coercivity displayed in the KKT contact proof -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Optimization
variable {n : ℕ}

def spectralMinimum (A : MatR n) (hA : A.PosDef) (hn : 1 ≤ n) : ℝ := by
  letI : NeZero n := ⟨by omega⟩
  exact (Finset.univ.image hA.isHermitian.eigenvalues).min' (Finset.univ_nonempty.image _)

theorem spectralMinimum_le (A : MatR n) (hA : A.PosDef) (hn : 1 ≤ n) (i : Fin n) :
    spectralMinimum A hA hn ≤ hA.isHermitian.eigenvalues i := by
  unfold spectralMinimum
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

theorem spectralMinimum_pos (A : MatR n) (hA : A.PosDef) (hn : 1 ≤ n) : 0 < spectralMinimum A hA hn := by
  letI : NeZero n := ⟨by omega⟩
  have hmem : spectralMinimum A hA hn ∈ Finset.univ.image hA.isHermitian.eigenvalues :=
    Finset.min'_mem _ _
  obtain ⟨i, _hi, he⟩ := Finset.mem_image.mp hmem
  rw [← he]
  exact hA.eigenvalues_pos i

theorem sylvester_trace_identity (A H : MatR n) :
    (H*(A*H+H*A)).trace = 2*(A*H^2).trace := by
  rw [Matrix.mul_add, Matrix.trace_add, pow_two]
  have h1 : (H*(A*H)).trace = (A*(H*H)).trace := by
    rw [Matrix.trace_mul_comm H (A*H), Matrix.mul_assoc]
  have h2 : (H*(H*A)).trace = (A*(H*H)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (H*H) A]
  rw [h1, h2]
  ring

/-- Equation (2.16): actual minimum eigenvalue and actual Frobenius norm, preserving order. -/
theorem sylvester_trace_coercivity (hn : 1 ≤ n) (A H : MatR n) (hA : A.PosDef) (hH : H.IsHermitian) :
    (H*(A*H+H*A)).trace = 2*(A*H^2).trace ∧
      2*spectralMinimum A hA hn*(frobeniusNorm H)^2 ≤ (H*(A*H+H*A)).trace := by
  have hq := Stability.hermitian_quadratic_lower A hA.isHermitian (spectralMinimum A hA hn) (spectralMinimum_le A hA hn)
  have hp := Stability.frobeniusPair_left_lower A H (spectralMinimum A hA hn) hq
  rw [Stability.frobeniusPair_trace, hH.isSymm.eq] at hp
  have ht : (H*(A*H)).trace = (A*H^2).trace := by
    rw [pow_two, Matrix.trace_mul_comm H (A*H), Matrix.mul_assoc]
  rw [ht] at hp
  refine ⟨sylvester_trace_identity A H, ?_⟩
  rw [sylvester_trace_identity]
  nlinarith only [hp]

end SharpCut.Optimization
