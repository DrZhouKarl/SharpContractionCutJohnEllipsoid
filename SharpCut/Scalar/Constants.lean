import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SharpCut.Scalar.Domains

/-! # The manuscript's exact fixed-dimensional constant and certificate domains -/

noncomputable section
namespace SharpCut

/-- Dimension zero has no geometric interpretation; all geometry requires n ≥ 1. -/
def sharpRatio (n : ℕ) : ℝ :=
  if n = 0 then 0 else if n = 1 then 1/2 else
    1/2 * ((n : ℝ)/((n : ℝ)-1))^(((n : ℝ)-1)/2)

def inverseDimension (n : ℕ) : ℝ := 1/(n : ℝ)

@[simp] theorem sharpRatio_one : sharpRatio 1 = 1/2 := by norm_num [sharpRatio]

theorem inverseDimension_bounds {n : ℕ} (hn : 2 ≤ n) :
    0 < inverseDimension n ∧ inverseDimension n ≤ 1/2 := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have htwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · exact one_div_pos.mpr hp
  · change 1/(n : ℝ) ≤ 1/2
    exact one_div_le_one_div_of_le (by norm_num) htwo

theorem sharpRatio_pos {n : ℕ} (hn : 1 ≤ n) : 0 < sharpRatio n := by
  have hn0 : n ≠ 0 := by omega
  by_cases hn1 : n = 1
  · subst n; norm_num
  · have hn2 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    simp only [sharpRatio, if_neg hn0, if_neg hn1]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (div_pos (by linarith) (by linarith)) _)

theorem certificate_denominator_lower {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : s ≤ 1) :
    2/3 ≤ 1-inverseDimension n/(2-inverseDimension n)*s :=
  Scalar.lorentz_denominator_lower _ _ (inverseDimension_bounds hn).1
    (inverseDimension_bounds hn).2 hs

end SharpCut
