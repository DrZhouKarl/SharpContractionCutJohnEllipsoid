import SharpCut.Scalar.Constants
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Full positive-coefficient series and an explicit fourth-order tail

The coefficients are 1/(2j(j+1)), j>=1. All infinite sums below have proved
summability. The tail estimate is valid throughout 0<x<1.
-/

noncomputable section
open scoped BigOperators
open Filter Finset
namespace SharpCut.Scalar

def constantSeriesTerm (x : ℝ) (j : ℕ) : ℝ :=
  x^(j+1)/(2*((j : ℝ)+1)*((j : ℝ)+2))

def constantSeriesValue (x : ℝ) : ℝ := 1/2+(1-x)/(2*x)*Real.log (1-x)

theorem constantSeries_hasSum (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasSum (constantSeriesTerm x) (constantSeriesValue x) := by
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_of_pos hx])
  have htail : HasSum (fun j : ℕ => x^(j+2)/((j : ℝ)+2)) (-Real.log (1-x)-x) := by
    have hshift : HasSum (fun j : ℕ => x^((j+1)+1)/(((j+1 : ℕ) : ℝ)+1)) (-Real.log (1-x)-x) := by
      apply (hasSum_nat_add_iff (f := fun j : ℕ => x^(j+1)/((j : ℝ)+1)) 1).mpr
      simpa only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, zero_add, div_one,
        sub_add_cancel] using hlog
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hshift
  have hsum := (hlog.mul_left (1/2 : ℝ)).sub (htail.mul_left (1/(2*x)))
  have hterm (j : ℕ) : (1/2 : ℝ)*(x^(j+1)/((j : ℝ)+1))-
      (1/(2*x))*(x^(j+2)/((j : ℝ)+2)) = constantSeriesTerm x j := by
    unfold constantSeriesTerm
    rw [show j+2 = (j+1)+1 by omega, pow_succ]
    have h1 : (j : ℝ)+1 ≠ 0 := by positivity
    have h2 : (j : ℝ)+2 ≠ 0 := by positivity
    field_simp [hx.ne', h1, h2]
    ring
  have hvalue : (1/2 : ℝ)*(-Real.log (1-x))-(1/(2*x))*(-Real.log (1-x)-x) = constantSeriesValue x := by
    unfold constantSeriesValue
    field_simp [hx.ne']
    ring
  simpa only [hterm, hvalue] using hsum

theorem constantSeriesTerm_nonneg (x : ℝ) (hx : 0 ≤ x) (j : ℕ) : 0 ≤ constantSeriesTerm x j := by
  unfold constantSeriesTerm
  positivity

theorem constantSeries_strictMono (x y : ℝ) (hx : 0 < x) (hxy : x < y) (hy1 : y < 1) :
    constantSeriesValue x < constantSeriesValue y := by
  have hy : 0 < y := hx.trans hxy
  have hsx := constantSeries_hasSum x hx (hxy.trans hy1)
  have hsy := constantSeries_hasSum y hy hy1
  have hle : constantSeriesTerm x ≤ constantSeriesTerm y := by
    intro j
    unfold constantSeriesTerm
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx.le hxy.le _) (by positivity)
  have h0 : constantSeriesTerm x 0 < constantSeriesTerm y 0 := by
    norm_num only [constantSeriesTerm, zero_add, pow_one, Nat.cast_zero, zero_add]
    exact div_lt_div_of_pos_right hxy (by norm_num)
  have h := Summable.tsum_lt_tsum hle h0 hsx.summable hsy.summable
  rwa [hsx.tsum_eq, hsy.tsum_eq] at h

theorem constantSeries_fourth_tail (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    0 ≤ constantSeriesValue x-(x/4+x^2/12+x^3/24) ∧
      constantSeriesValue x-(x/4+x^2/12+x^3/24) ≤ x^4/(40*(1-x)) := by
  have hs := constantSeries_hasSum x hx hx1
  have ht : Summable (fun j => constantSeriesTerm x (j+3)) := (summable_nat_add_iff 3).mpr hs.summable
  have hsplit := hs.summable.sum_add_tsum_nat_add 3
  have hfirst : (∑ j ∈ Finset.range 3, constantSeriesTerm x j) = x/4+x^2/12+x^3/24 := by
    norm_num [Finset.sum_range_succ, constantSeriesTerm]
  rw [hfirst, hs.tsum_eq] at hsplit
  have he : constantSeriesValue x-(x/4+x^2/12+x^3/24) = ∑' j, constantSeriesTerm x (j+3) := by
    linarith only [hsplit]
  have hg := (hasSum_geometric_of_lt_one hx.le hx1).mul_left (x^4/40)
  have hcompare (j : ℕ) : constantSeriesTerm x (j+3) ≤ (x^4/40)*x^j := by
    have hden : (40 : ℝ) ≤ 2*((j : ℝ)+4)*((j : ℝ)+5) := by
      have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
      nlinarith only [hj, sq_nonneg (j : ℝ)]
    unfold constantSeriesTerm
    norm_num only [Nat.cast_add, Nat.cast_ofNat, add_assoc]
    calc
      _ ≤ x^(j+4)/40 := div_le_div_of_nonneg_left (pow_nonneg hx.le _) (by norm_num) hden
      _ = (x^4/40)*x^j := by rw [show j+4 = 4+j by omega, pow_add]; ring
  have hbound := ht.tsum_le_tsum hcompare hg.summable
  rw [hg.tsum_eq] at hbound
  rw [he]
  refine ⟨tsum_nonneg (fun j => constantSeriesTerm_nonneg x hx.le _), ?_⟩
  convert hbound using 1
  rw [div_eq_mul_inv, mul_inv_rev]
  ring

end SharpCut.Scalar
