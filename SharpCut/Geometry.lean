import Khachiyan.Basic

/-!
# Euclidean geometry and the manuscript's cut orientation

These aliases preserve the legacy library's actual Euclidean norm, ellipsoid
sets, positive-definite shape requirement and maximal Lebesgue-volume functional.
The paper retains the nonpositive side of the cut.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace SharpCut

abbrev V := Khachiyan.V
abbrev MatR := Khachiyan.MatR
abbrev unitBall := Khachiyan.unitBall
abbrev ellipsoid := @Khachiyan.ellipsoid
abbrev outer := @Khachiyan.outer
abbrev IsConvexBody := @Khachiyan.IsConvexBody
abbrev IsFeasible := @Khachiyan.IsFeasible
abbrev IsMaxDet := @Khachiyan.IsMaxDet
abbrev IsJohnNormalized := @Khachiyan.IsJohnNormalized
abbrev maxEllipsoidVolume := @Khachiyan.maxEllipsoidVolume

def centralHalfspace {n : ℕ} (c v : V n) : Set (V n) :=
  {x | ⟪v, x-c⟫ ≤ 0}

theorem centralHalfspace_eq_legacy {n : ℕ} (c v : V n) :
    centralHalfspace c v = Khachiyan.centralHalfspace c (-v) := by
  ext x
  simp [centralHalfspace, Khachiyan.centralHalfspace]

@[simp] theorem mem_centralHalfspace {n : ℕ} (c v x : V n) :
    x ∈ centralHalfspace c v ↔ ⟪v, x-c⟫ ≤ 0 := Iff.rfl

end SharpCut
