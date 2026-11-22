import SharpCut.Scalar.ConstantSeries
import SharpCut.Sharpness.LegacyCone
import SharpCut.Applications.Initialization

/-! # Strict dimension monotonicity, full series and rigorous O(n^-4)

The dimension-one value remains a separate branch. The series applies for
n>=2 and the asymptotic assertion is a genuine eventual norm estimate.
-/

noncomputable section
open scoped BigOperators
open Filter Set
namespace SharpCut.Applications
open Scalar
variable {n : ℕ}

theorem negative_log_sharpRatio_formula (hn : 2 ≤ n) :
    -Real.log (sharpRatio n) = Real.log 2+((n : ℝ)-1)/2*Real.log (1-1/(n : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hm : 0 < (n : ℝ)-1 := by linarith only [hn1]
  have hbase : (n : ℝ)/((n : ℝ)-1) = (1-1/(n : ℝ))⁻¹ := by
    field_simp [hnpos.ne', hm.ne']
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  rw [sharpRatio, ite_eq_right (by omega : n ≠ 0), ite_eq_right (by omega : n ≠ 1),
    Real.log_mul (by norm_num : (1/2 : ℝ) ≠ 0) (Real.rpow_pos_of_pos (div_pos hnpos hm) _).ne',
    Real.log_rpow (div_pos hnpos hm), hhalf, hbase, Real.log_inv]
  ring

theorem dimension_series_value (hn : 2 ≤ n) :
    constantSeriesValue (1/(n : ℝ)) = -Real.log (sharpRatio n)-Real.log 2+1/2 := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [negative_log_sharpRatio_formula hn, constantSeriesValue]
  field_simp
  ring

theorem sharpRatio_hasSum (hn : 2 ≤ n) :
    HasSum (fun j : ℕ => 1/(2*((j : ℝ)+1)*((j : ℝ)+2)*(n : ℝ)^(j+1)))
      (-Real.log (sharpRatio n)-Real.log 2+1/2) := by
  have hb := inverseDimension_bounds hn
  dsimp only [inverseDimension] at hb
  have hs := constantSeries_hasSum (1/(n : ℝ)) hb.1 (by linarith only [hb.2])
  have hterm (j : ℕ) : constantSeriesTerm (1/(n : ℝ)) j =
      1/(2*((j : ℝ)+1)*((j : ℝ)+2)*(n : ℝ)^(j+1)) := by
    unfold constantSeriesTerm
    simp only [div_pow, one_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  have hf : constantSeriesTerm (1/(n : ℝ)) =
      (fun j : ℕ => 1/(2*((j : ℝ)+1)*((j : ℝ)+2)*(n : ℝ)^(j+1))) := by
    funext j
    exact hterm j
  rw [hf, dimension_series_value hn] at hs
  exact hs

theorem sharpRatio_full_series (hn : 2 ≤ n) :
    -Real.log (sharpRatio n) = Real.log 2-1/2+
      ∑' j : ℕ, 1/(2*((j : ℝ)+1)*((j : ℝ)+2)*(n : ℝ)^(j+1)) := by
  have h := (sharpRatio_hasSum hn).tsum_eq
  linarith only [h]

theorem sharpRatio_series_absolute (hn : 2 ≤ n) :
    Summable (fun j : ℕ => |1/(2*((j : ℝ)+1)*((j : ℝ)+2)*(n : ℝ)^(j+1))|) := by
  have hnonneg (j : ℕ) : 0 ≤ 1/(2*((j : ℝ)+1)*((j : ℝ)+2)*(n : ℝ)^(j+1)) := by positivity
  simpa only [abs_of_nonneg (hnonneg _)] using (sharpRatio_hasSum hn).summable

theorem dimension_coefficient_difference (j : ℕ) (n : ℕ) :
    (1/(2*((j : ℝ)+1))-1/(2*((j : ℝ)+2)))*(1/(n : ℝ))^(j+1) =
      1/(2*((j : ℝ)+1)*((j : ℝ)+2)*(n : ℝ)^(j+1)) := by
  have h1 : (j : ℝ)+1 ≠ 0 := by positivity
  have h2 : (j : ℝ)+2 ≠ 0 := by positivity
  have hc : 1/(2*((j : ℝ)+1))-1/(2*((j : ℝ)+2)) = 1/(2*((j : ℝ)+1)*((j : ℝ)+2)) := by
    field_simp [h1, h2]
    ring
  rw [hc]
  simp only [div_pow, one_pow, div_eq_mul_inv, mul_inv_rev]
  ring

theorem sharpRatio_alternative_series (hn : 2 ≤ n) :
    -Real.log (sharpRatio n) = Real.log 2-1/2+
      ∑' j : ℕ, (1/(2*((j : ℝ)+1))-1/(2*((j : ℝ)+2)))*(1/(n : ℝ))^(j+1) := by
  simp only [dimension_coefficient_difference]
  exact sharpRatio_full_series hn

theorem sharpRatio_gt_half (hn : 2 ≤ n) : (1/2 : ℝ) < sharpRatio n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hm : 0 < (n : ℝ)-1 := by linarith only [hn1]
  have hb : 1 < (n : ℝ)/((n : ℝ)-1) := (one_lt_div hm).mpr (by linarith)
  have hp := Real.one_lt_rpow hb (div_pos hm (by norm_num : (0 : ℝ) < 2))
  rw [sharpRatio, ite_eq_right (by omega : n ≠ 0), ite_eq_right (by omega : n ≠ 1)]
  nlinarith only [hp]

theorem sharpRatio_strictMonoOn : StrictMonoOn sharpRatio {n : ℕ | 1 ≤ n} := by
  intro n hn m hm hnm
  by_cases h1 : n = 1
  · subst n
    rw [sharpRatio_one]
    exact sharpRatio_gt_half (by omega)
  · have hn2 : 2 ≤ n := by simp only [mem_setOf_eq] at hn; omega
    have hm2 : 2 ≤ m := by omega
    have hnr : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hmr : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hxy : 1/(m : ℝ) < 1/(n : ℝ) := one_div_lt_one_div_of_lt hnr (by exact_mod_cast hnm)
    have hb := inverseDimension_bounds hn2
    dsimp only [inverseDimension] at hb
    have h := constantSeries_strictMono (1/(m : ℝ)) (1/(n : ℝ))
      (one_div_pos.mpr hmr) hxy (by linarith only [hb.2])
    rw [dimension_series_value hm2, dimension_series_value hn2] at h
    apply (Real.log_lt_log_iff (sharpRatio_pos (by omega)) (sharpRatio_pos (by omega))).mp
    linarith only [h]

theorem sharpRatio_limit : Tendsto sharpRatio atTop (nhds Khachiyan.rStar) :=
  (Filter.tendsto_add_atTop_iff_nat 1).mp Sharpness.sharpRatio_shifted_limit

theorem sharpRatio_all_dimension_bounds (hn : 1 ≤ n) :
    (1/2 : ℝ) ≤ sharpRatio n ∧ sharpRatio n < Real.sqrt (Real.exp 1)/2 := by
  have hlow : (1/2 : ℝ) ≤ sharpRatio n := by
    by_cases h1 : n = 1
    · subst n; rw [sharpRatio_one]
    · exact (sharpRatio_gt_half (by omega)).le
  have hstrict : sharpRatio n < sharpRatio (n+1) := sharpRatio_strictMonoOn (show 1 ≤ n from hn) (show 1 ≤ n+1 by omega) (show n < n+1 by omega)
  have hupper := Khachiyan.Cone.volumeRatio_le_rStar hn
  rw [(Sharpness.legacy_cone_attainment hn).2.2.2.2.2] at hupper
  rw [Khachiyan.Scalar.rStar_eq_sqrt_exp_one] at hupper
  exact ⟨hlow, hstrict.trans_le hupper⟩

def negativeLogTruncation (n : ℕ) : ℝ :=
  Real.log 2-1/2+1/(4*(n : ℝ))+1/(12*(n : ℝ)^2)+1/(24*(n : ℝ)^3)

def negativeLogRemainder (n : ℕ) : ℝ := -Real.log (sharpRatio n)-negativeLogTruncation n

theorem negativeLogRemainder_eq_tail (hn : 2 ≤ n) :
    negativeLogRemainder n = constantSeriesValue (1/(n : ℝ))-
      ((1/(n : ℝ))/4+(1/(n : ℝ))^2/12+(1/(n : ℝ))^3/24) := by
  rw [negativeLogRemainder, negativeLogTruncation, dimension_series_value hn]
  simp only [div_pow, one_pow, div_eq_mul_inv, mul_inv_rev]
  ring

/-- A quantitative bound valid at every n>=2, stronger than the asymptotic notation. -/
theorem negativeLogRemainder_bounds (hn : 2 ≤ n) :
    0 ≤ negativeLogRemainder n ∧ negativeLogRemainder n ≤ 1/(20*(n : ℝ)^4) := by
  have hb := inverseDimension_bounds hn
  dsimp only [inverseDimension] at hb
  have hx1 : 1/(n : ℝ) < 1 := by linarith only [hb.2]
  have ht := constantSeries_fourth_tail (1/(n : ℝ)) hb.1 hx1
  rw [← negativeLogRemainder_eq_tail hn] at ht
  have hden : (20 : ℝ) ≤ 40*(1-1/(n : ℝ)) := by linarith only [hb.2]
  have hbound : (1/(n : ℝ))^4/(40*(1-1/(n : ℝ))) ≤ (1/(n : ℝ))^4/20 :=
    div_le_div_of_nonneg_left (pow_nonneg hb.1.le _) (by norm_num) hden
  have he : (1/(n : ℝ))^4/20 = 1/(20*(n : ℝ)^4) := by
    simp only [div_pow, one_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at hbound
  exact ⟨ht.1, ht.2.trans hbound⟩

theorem negativeLogRemainder_isBigO : negativeLogRemainder =O[atTop] (fun n : ℕ => 1/(n : ℝ)^4) := by
  apply Asymptotics.IsBigO.of_bound (1/20 : ℝ)
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
  have hb := negativeLogRemainder_bounds hn
  have hpow : 0 ≤ 1/(n : ℝ)^4 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb.1, abs_of_nonneg hpow]
  convert hb.2 using 1
  ring

/-- The complete dimension series and exact first three coefficients with a certified fourth-order remainder. -/
theorem sharpRatio_series_and_asymptotics (hn : 2 ≤ n) :
    HasSum (fun j : ℕ => 1/(2*((j : ℝ)+1)*((j : ℝ)+2)*(n : ℝ)^(j+1)))
      (-Real.log (sharpRatio n)-Real.log 2+1/2) ∧
    -Real.log (sharpRatio n) = Real.log 2-1/2+
      ∑' j : ℕ, 1/(2*((j : ℝ)+1)*((j : ℝ)+2)*(n : ℝ)^(j+1)) ∧
    -Real.log (sharpRatio n) = negativeLogTruncation n+negativeLogRemainder n ∧
    0 ≤ negativeLogRemainder n ∧ negativeLogRemainder n ≤ 1/(20*(n : ℝ)^4) ∧
    negativeLogRemainder =O[atTop] (fun k : ℕ => 1/(k : ℝ)^4) := by
  refine ⟨sharpRatio_hasSum hn, sharpRatio_full_series hn, ?_,
    (negativeLogRemainder_bounds hn).1, (negativeLogRemainder_bounds hn).2, negativeLogRemainder_isBigO⟩
  unfold negativeLogRemainder
  ring

end SharpCut.Applications
