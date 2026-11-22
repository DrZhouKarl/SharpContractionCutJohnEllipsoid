import SharpCut.Certificate.LorentzGeometry

/-!
# The weighted contact defect and its exact zero set

The defect is computed from the original positive-weight frame. Its zero
condition concerns every contact; no unweighted pointwise stability is claimed.
The reweighted recurrence is the finite-moment input of equations (8.5)--(8.6).
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace SharpCut.Certificate
variable {n N : ℕ}

def height (F : JohnFrame n N) (v : V n) (i : Fin N) : ℝ := ⟪F.contact i, v⟫

def defectTerm (F : JohnFrame n N) (v : V n) (i : Fin N) : ℝ :=
  F.weight i*((1+height F v i)*(height F v i-inverseDimension n)^2)/
    (1-boostParameter n*height F v i)

def frameDefect (F : JohnFrame n N) (v : V n) : ℝ := ∑ i, defectTerm F v i

def reweightedMoment (F : JohnFrame n N) (v : V n) (r : ℕ) : ℝ :=
  ∑ i, F.weight i/(1-boostParameter n*height F v i)*(height F v i)^r

theorem height_denominator_pos (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n)
    (hv : ‖v‖ = 1) (i : Fin N) : 0 < 1-boostParameter n*height F v i := by
  have h := certificate_denominator_lower hn (F.heights_bounds v hv i).2
  change 2/3 ≤ 1-boostParameter n*height F v i at h
  linarith

theorem defectTerm_nonneg (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n)
    (hv : ‖v‖ = 1) (i : Fin N) : 0 ≤ defectTerm F v i := by
  have hs : 0 ≤ 1+height F v i := by
    have h := (F.heights_bounds v hv i).1
    change -1 ≤ height F v i at h
    linarith
  exact div_nonneg
    (mul_nonneg (F.weight_pos i).le (mul_nonneg hs (sq_nonneg _)))
    (height_denominator_pos F hn v hv i).le

theorem frameDefect_nonneg (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n)
    (hv : ‖v‖ = 1) : 0 ≤ frameDefect F v :=
  Finset.sum_nonneg (fun i _ => defectTerm_nonneg F hn v hv i)

theorem defectTerm_zero_iff (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n)
    (hv : ‖v‖ = 1) (i : Fin N) :
    defectTerm F v i = 0 ↔ height F v i = -1 ∨ height F v i = inverseDimension n := by
  have hd := height_denominator_pos F hn v hv i
  simp only [defectTerm, div_eq_zero_iff, mul_eq_zero, (F.weight_pos i).ne', hd.ne',
    false_or, or_false, sq_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro (h | h)
    · left; linarith
    · exact Or.inr h
  · rintro (h | h)
    · left; rw [h]; ring
    · exact Or.inr h

theorem frameDefect_zero_iff (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n)
    (hv : ‖v‖ = 1) :
    frameDefect F v = 0 ↔ ∀ i, height F v i = -1 ∨ height F v i = inverseDimension n := by
  have hz := Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => defectTerm_nonneg F hn v hv i)
  constructor
  · intro h i
    exact (defectTerm_zero_iff F hn v hv i).mp (hz.mp h i (Finset.mem_univ i))
  · intro h
    exact hz.mpr (fun i _ => (defectTerm_zero_iff F hn v hv i).mpr (h i))

theorem reweighted_recurrence (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n)
    (hv : ‖v‖ = 1) (r : ℕ) :
    reweightedMoment F v r-boostParameter n*reweightedMoment F v (r+1) =
      ∑ i, F.weight i*(height F v i)^r := by
  unfold reweightedMoment
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  field_simp [(height_denominator_pos F hn v hv i).ne']

theorem reweighted_moments (F : JohnFrame n N) (hn : 2 ≤ n) (v : V n)
    (hv : ‖v‖ = 1) :
    reweightedMoment F v 0-boostParameter n*reweightedMoment F v 1 = (n : ℝ) ∧
    reweightedMoment F v 1-boostParameter n*reweightedMoment F v 2 = 0 ∧
    reweightedMoment F v 2-boostParameter n*reweightedMoment F v 3 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [pow_zero, mul_one, F.weight_sum] using reweighted_recurrence F hn v hv 0
  · simpa only [pow_one, height, F.scalar_first_moment] using reweighted_recurrence F hn v hv 1
  · simpa only [height, F.scalar_second_moment, hv, one_pow] using reweighted_recurrence F hn v hv 2

theorem defect_expansion (F : JohnFrame n N) (v : V n) :
    frameDefect F v = reweightedMoment F v 3+
      (1-2*inverseDimension n)*reweightedMoment F v 2+
      ((inverseDimension n)^2-2*inverseDimension n)*reweightedMoment F v 1+
      (inverseDimension n)^2*reweightedMoment F v 0 := by
  unfold frameDefect defectTerm reweightedMoment
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, pow_zero, pow_one, mul_one]
  apply Finset.sum_congr rfl
  intro i _
  ring

end SharpCut.Certificate
