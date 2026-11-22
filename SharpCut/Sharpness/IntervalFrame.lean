import SharpCut.Sharpness.FrameMoments

/-! # A genuine contact-frame witness in dimension one -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Sharpness

def intervalContact (s : Bool) : V 1 := if s then axis 0 else -axis 0

theorem intervalContact_unit (s : Bool) : ‖intervalContact s‖ = 1 := by
  cases s <;> simp [intervalContact]

theorem interval_first_moment : (∑ s : Bool, (1/2 : ℝ) • intervalContact s) = 0 := by
  simp [Fintype.sum_bool, intervalContact, smul_neg]

theorem interval_second_moment : (∑ s : Bool, (1/2 : ℝ) • outer (intervalContact s)) = 1 := by
  rw [Fintype.sum_bool]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [intervalContact, Khachiyan.outer_apply, axis_zero] <;> norm_num

def intervalFrame : JohnFrame 1 (Fintype.card Bool) :=
  JohnFrame.ofFinite intervalContact (fun _ => 1/2) intervalContact_unit (fun _ => by norm_num)
    interval_first_moment interval_second_moment

end SharpCut.Sharpness
