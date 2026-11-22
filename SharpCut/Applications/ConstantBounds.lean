import SharpCut.Optimization.PolarContraction

/-! # Exact contraction constant is positive and strictly below one in every positive dimension -/

noncomputable section
namespace SharpCut.Applications
variable {n : ℕ}

theorem log_two_lower : (2/3 : ℝ) ≤ Real.log 2 := by
  have h := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  norm_num at h
  exact h

theorem sharpRatio_log_negative (hn : 1 ≤ n) : Real.log (sharpRatio n) < 0 := by
  by_cases h1 : n = 1
  · subst n
    rw [sharpRatio_one]
    exact Real.log_neg (by norm_num) (by norm_num)
  · have hn0 : n ≠ 0 := by omega
    have hnreal : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hm : 0 < (n : ℝ)-1 := by linarith only [hnreal]
    have ha : 0 < (n : ℝ)/((n : ℝ)-1) := div_pos (by linarith only [hnreal]) hm
    have hab : 1 < (n : ℝ)/((n : ℝ)-1) := by apply (one_lt_div hm).mpr; linarith
    have hlog := Real.log_lt_sub_one_of_pos ha (by linarith only [hab])
    have hmul := mul_lt_mul_of_pos_left hlog (div_pos hm (by norm_num : (0 : ℝ) < 2))
    have heq : (((n : ℝ)-1)/2)*((n : ℝ)/((n : ℝ)-1)-1) = 1/2 := by field_simp [hm.ne'] <;> ring
    rw [heq] at hmul
    have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
    rw [sharpRatio, ite_eq_right hn0, ite_eq_right h1,
      Real.log_mul (by norm_num : (1/2 : ℝ) ≠ 0) (Real.rpow_pos_of_pos ha _).ne',
      Real.log_rpow ha, hhalf]
    linarith only [hmul, log_two_lower]

theorem sharpRatio_lt_one (hn : 1 ≤ n) : sharpRatio n < 1 := by
  have h := sharpRatio_log_negative hn
  apply (Real.log_lt_log_iff (sharpRatio_pos hn) (by norm_num : (0 : ℝ) < 1)).mp
  simpa only [Real.log_one] using h

theorem sharpRatio_log_decrease_pos (hn : 1 ≤ n) : 0 < -Real.log (sharpRatio n) := neg_pos.mpr (sharpRatio_log_negative hn)

end SharpCut.Applications
