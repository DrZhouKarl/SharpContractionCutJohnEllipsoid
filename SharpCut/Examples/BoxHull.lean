import SharpCut.Examples.SquarePyramid

/-! # Exact convex-hull description of a horizontal square in Euclidean 3-space -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Set
namespace SharpCut.Examples.SquarePyramid

def squareVertices (w z : ℝ) : Fin 4 → V 3 :=
  ![point (-w) (-w) z,point w (-w) z,point (-w) w z,point w w z]

theorem point_combo (a b x₀ y₀ z₀ x₁ y₁ z₁ : ℝ) :
    a • point x₀ y₀ z₀+b • point x₁ y₁ z₁ =
      point (a*x₀+b*x₁) (a*y₀+b*y₁) (a*z₀+b*z₁) := by
  ext i
  fin_cases i <;> rfl

theorem square_convex_hull (w z x y : ℝ) (hw : 0 < w) (hx : |x| ≤ w) (hy : |y| ≤ w) :
    point x y z ∈ convexHull ℝ (Set.range (squareVertices w z)) := by
  let H := convexHull ℝ (Set.range (squareVertices w z))
  have hc : Convex ℝ H := convex_convexHull ℝ _
  have hcorner (i : Fin 4) : squareVertices w z i ∈ H := subset_convexHull ℝ _ ⟨i,rfl⟩
  let a := (x+w)/(2*w)
  let b := (y+w)/(2*w)
  have hxabs := abs_le.mp hx
  have hyabs := abs_le.mp hy
  have h2w : 0 < 2*w := by positivity
  have ha0 : 0 ≤ a := div_nonneg (by linarith only [hxabs.1]) h2w.le
  have ha1 : a ≤ 1 := (div_le_iff₀ h2w).mpr (by linarith only [hxabs.2])
  have hb0 : 0 ≤ b := div_nonneg (by linarith only [hyabs.1]) h2w.le
  have hb1 : b ≤ 1 := (div_le_iff₀ h2w).mpr (by linarith only [hyabs.2])
  have hbottom : point x (-w) z ∈ H := by
    have h : (1-a) • squareVertices w z 0+a • squareVertices w z 1 ∈ H :=
      hc (hcorner 0) (hcorner 1) (by linarith only [ha1]) ha0 (by ring)
    change (1-a) • point (-w) (-w) z+a • point w (-w) z ∈ H at h
    rw [point_combo] at h
    have he : point ((1-a)*(-w)+a*w) ((1-a)*(-w)+a*(-w)) ((1-a)*z+a*z) = point x (-w) z := by
      congr 1 <;> dsimp only [a] <;> field_simp [hw.ne'] <;> ring
    rwa [he] at h
  have htop : point x w z ∈ H := by
    have h : (1-a) • squareVertices w z 2+a • squareVertices w z 3 ∈ H :=
      hc (hcorner 2) (hcorner 3) (by linarith only [ha1]) ha0 (by ring)
    change (1-a) • point (-w) w z+a • point w w z ∈ H at h
    rw [point_combo] at h
    have he : point ((1-a)*(-w)+a*w) ((1-a)*w+a*w) ((1-a)*z+a*z) = point x w z := by
      congr 1 <;> dsimp only [a] <;> field_simp [hw.ne'] <;> ring
    rwa [he] at h
  have h : (1-b) • point x (-w) z+b • point x w z ∈ H :=
    hc hbottom htop (by linarith only [hb1]) hb0 (by ring)
  rw [point_combo] at h
  have he : point ((1-b)*x+b*x) ((1-b)*(-w)+b*w) ((1-b)*z+b*z) = point x y z := by
    congr 1 <;> dsimp only [b] <;> field_simp [hw.ne'] <;> ring
  rwa [he] at h

end SharpCut.Examples.SquarePyramid
