import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import SharpCut.Scalar.EndpointArithmetic

/-! # Kernel-checked analytic endpoint logarithm certificates

The upper log-two bound uses six terms of mathlib's finite Taylor bound;
the paper's exact rational upper value is retained. The lower bound uses
the same two-term positive partial sum as the supporting manuscript record.
-/

namespace SharpCut.Scalar
open Finset

theorem log_two_le_rational : Real.log 2 ≤ (23581 : ℝ)/34020 := by
  have h := Real.log_div_le_sum_range_add (x := (1 : ℝ)/3) (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_sixteen_thirteen_ge_rational : (5064 : ℝ)/24389 ≤ Real.log (16/13) := by
  have h := Real.sum_range_le_log_div (x := (3 : ℝ)/29) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_thirteen_recombination : Real.log 13 = 4*Real.log 2-Real.log (16/13) := by
  have h16 : Real.log (16 : ℝ) = 4*Real.log 2 := by
    rw [show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]
    norm_num
  have hd := Real.log_div (x := (16 : ℝ)) (y := 13) (by norm_num) (by norm_num)
  rw [h16] at hd
  linarith

theorem endpoint_logarithm_certificate :
    (2106*Real.log 13-468*Real.log 2-4160)/925 < (124 : ℝ)/125 := by
  have h := endpoint_bound_of_log_bounds (Real.log 2) (Real.log (16/13))
    log_two_le_rational log_sixteen_thirteen_ge_rational
  rw [log_thirteen_recombination]
  nlinarith

end SharpCut.Scalar
