import SharpCut.Examples.BoxHull
import Mathlib.Analysis.Convex.Extreme

/-! # Exact vertex hulls of the square pyramid and its central-cut frustum -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Set
namespace SharpCut.Examples.SquarePyramid

def width (z : ℝ) : ℝ := (3-z)*Real.sqrt 2/4
def apex : V 3 := point 0 0 3
def pyramidVertices : Set (V 3) := {apex} ∪ Set.range (squareVertices (Real.sqrt 2) (-1))
def frustumVertices : Set (V 3) :=
  Set.range (squareVertices (Real.sqrt 2) (-1)) ∪ Set.range (squareVertices (3*Real.sqrt 2/4) 0)

theorem sqrt_two_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
theorem width_base : width (-1) = Real.sqrt 2 := by unfold width; ring
theorem width_cut : width 0 = 3*Real.sqrt 2/4 := by unfold width; ring
theorem width_apex : width 3 = 0 := by simp [width]

theorem width_support (z : ℝ) : 2*Real.sqrt 2*width z = 3-z := by
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  unfold width
  linear_combination ((3-z)/2)*hs

theorem body_width (p : V 3) : p ∈ body ↔ -1 ≤ p 2 ∧ |p 0| ≤ width (p 2) ∧ |p 1| ≤ width (p 2) := by
  have ha : 0 < 2*Real.sqrt 2 := by positivity
  have hw := width_support (p 2)
  constructor
  · rintro ⟨hz,hx,hy⟩
    refine ⟨hz, le_of_mul_le_mul_left ?_ ha, le_of_mul_le_mul_left ?_ ha⟩
    all_goals linarith only [hw,hx,hy]
  · rintro ⟨hz,hx,hy⟩
    have hxx := mul_le_mul_of_nonneg_left hx ha.le
    have hyy := mul_le_mul_of_nonneg_left hy ha.le
    refine ⟨hz,?_,?_⟩
    all_goals linarith only [hw,hxx,hyy]

theorem level_vertex_mem_body (z : ℝ) (hz : -1 ≤ z) (hz3 : z ≤ 3) (i : Fin 4) :
    squareVertices (width z) z i ∈ body := by
  have hw : 0 ≤ width z := by unfold width; positivity
  rw [body_width]
  fin_cases i <;> simp [squareVertices, point, abs_of_nonneg hw, abs_neg, hz]

theorem apex_mem_body : apex ∈ body := by rw [body_width]; norm_num [apex, point, width_apex]

theorem base_vertex_mem_body (i : Fin 4) : squareVertices (Real.sqrt 2) (-1) i ∈ body := by
  have h := level_vertex_mem_body (-1) (by norm_num) (by norm_num) i
  rwa [width_base] at h

theorem pyramid_vertices_subset : pyramidVertices ⊆ body := by
  rintro p (hp | ⟨i,rfl⟩)
  · rw [Set.mem_singleton_iff] at hp
    rw [hp]
    exact apex_mem_body
  · exact base_vertex_mem_body i

/-- Every point in the pyramid is an exact convex combination of its apex and a point in the base square. -/
theorem body_eq_vertex_hull : body = convexHull ℝ pyramidVertices := by
  apply Set.Subset.antisymm
  · intro p hp
    let H := convexHull ℝ pyramidVertices
    have hc : Convex ℝ H := convex_convexHull ℝ _
    have hap : apex ∈ H := subset_convexHull ℝ _ (Or.inl (Set.mem_singleton _))
    obtain ⟨hz,hx,hy⟩ := (body_width p).mp hp
    have hz3 : p 2 ≤ 3 := by
      have ha : 0 ≤ 2*Real.sqrt 2*|p 0| := by positivity
      linarith only [hp.2.1,ha]
    let a := (3-p 2)/4
    have ha0 : 0 ≤ a := by dsimp only [a]; positivity
    have ha1 : a ≤ 1 := by dsimp only [a]; linarith only [hz]
    have hw : width (p 2) = a*Real.sqrt 2 := by dsimp only [a,width]; ring
    by_cases hzero : a = 0
    · have hzA : p 2 = 3 := by dsimp only [a] at hzero; linarith only [hzero]
      have hx0 : p 0 = 0 := by
        rw [hw,hzero,zero_mul] at hx
        exact abs_eq_zero.mp (le_antisymm hx (abs_nonneg _))
      have hy0 : p 1 = 0 := by
        rw [hw,hzero,zero_mul] at hy
        exact abs_eq_zero.mp (le_antisymm hy (abs_nonneg _))
      have he : p = apex := by
        calc
          p = point (p 0) (p 1) (p 2) := (point_coordinates p).symm
          _ = apex := by rw [hx0,hy0,hzA]; rfl
      rw [he]
      exact hap
    · have hap0 : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hzero)
      have hxb : |p 0/a| ≤ Real.sqrt 2 := by
        rw [abs_div, abs_of_pos hap0]
        apply (div_le_iff₀ hap0).mpr
        rw [hw] at hx
        simpa only [mul_comm] using hx
      have hyb : |p 1/a| ≤ Real.sqrt 2 := by
        rw [abs_div, abs_of_pos hap0]
        apply (div_le_iff₀ hap0).mpr
        rw [hw] at hy
        simpa only [mul_comm] using hy
      have hbase := square_convex_hull (Real.sqrt 2) (-1) (p 0/a) (p 1/a) sqrt_two_pos hxb hyb
      have hq : point (p 0/a) (p 1/a) (-1) ∈ H :=
        (convexHull_mono (fun _ h => Or.inr h)) hbase
      have h : a • point (p 0/a) (p 1/a) (-1)+(1-a) • apex ∈ H :=
        hc hq hap ha0 (by linarith only [ha1]) (by ring)
      change a • point (p 0/a) (p 1/a) (-1)+(1-a) • point 0 0 3 ∈ H at h
      rw [point_combo] at h
      have he : point (a*(p 0/a)+(1-a)*0) (a*(p 1/a)+(1-a)*0) (a*(-1)+(1-a)*3) = p := by
        calc
          _ = point (p 0) (p 1) (p 2) := by
            congr 1 <;> field_simp [hzero] <;> dsimp only [a] <;> ring
          _ = p := point_coordinates p
      rwa [he] at h
  · exact convexHull_min pyramid_vertices_subset body_isConvexBody.2.1

theorem frustum_vertices_subset : frustumVertices ⊆ cutBody := by
  rintro p (⟨i,rfl⟩ | ⟨i,rfl⟩)
  · refine ⟨base_vertex_mem_body i,?_⟩
    fin_cases i <;> norm_num [squareVertices,point]
  · have h := level_vertex_mem_body 0 (by norm_num) (by norm_num) i
    rw [width_cut] at h
    refine ⟨h,?_⟩
    fin_cases i <;> norm_num [squareVertices,point]

/-- The retained cut body is exactly the convex hull of the four base and four cut-plane vertices. -/
theorem cut_eq_vertex_hull : cutBody = convexHull ℝ frustumVertices := by
  apply Set.Subset.antisymm
  · intro p hp
    let H := convexHull ℝ frustumVertices
    have hc : Convex ℝ H := convex_convexHull ℝ _
    obtain ⟨hz,hx,hy⟩ := (body_width p).mp hp.1
    have hz0 : p 2 ≤ 0 := hp.2
    let a := p 2+1
    let w := width (p 2)
    let t := 3*Real.sqrt 2/4
    have ha0 : 0 ≤ a := by dsimp only [a]; linarith only [hz]
    have ha1 : a ≤ 1 := by dsimp only [a]; linarith only [hz0]
    have hw : 0 < w := by
      dsimp only [w,width]
      exact div_pos (mul_pos (by linarith only [hz0]) sqrt_two_pos) (by norm_num)
    have ht : 0 < t := by dsimp only [t]; positivity
    have hux : |p 0/w| ≤ 1 := by rw [abs_div,abs_of_pos hw]; exact (div_le_iff₀ hw).mpr (by simpa only [one_mul] using hx)
    have huy : |p 1/w| ≤ 1 := by rw [abs_div,abs_of_pos hw]; exact (div_le_iff₀ hw).mpr (by simpa only [one_mul] using hy)
    have hxb : |Real.sqrt 2*(p 0/w)| ≤ Real.sqrt 2 := by
      rw [abs_mul,abs_of_pos sqrt_two_pos]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hux sqrt_two_pos.le
    have hyb : |Real.sqrt 2*(p 1/w)| ≤ Real.sqrt 2 := by
      rw [abs_mul,abs_of_pos sqrt_two_pos]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left huy sqrt_two_pos.le
    have hxt : |t*(p 0/w)| ≤ t := by rw [abs_mul,abs_of_pos ht]; simpa only [mul_one] using mul_le_mul_of_nonneg_left hux ht.le
    have hyt : |t*(p 1/w)| ≤ t := by rw [abs_mul,abs_of_pos ht]; simpa only [mul_one] using mul_le_mul_of_nonneg_left huy ht.le
    have hb0 := square_convex_hull (Real.sqrt 2) (-1) (Real.sqrt 2*(p 0/w)) (Real.sqrt 2*(p 1/w)) sqrt_two_pos hxb hyb
    have ht0 := square_convex_hull t 0 (t*(p 0/w)) (t*(p 1/w)) ht hxt hyt
    have hbH : point (Real.sqrt 2*(p 0/w)) (Real.sqrt 2*(p 1/w)) (-1) ∈ H :=
      (convexHull_mono (fun _ h => Or.inl h)) hb0
    have htH : point (t*(p 0/w)) (t*(p 1/w)) 0 ∈ H :=
      (convexHull_mono (fun _ h => Or.inr h)) ht0
    have h : (1-a) • point (Real.sqrt 2*(p 0/w)) (Real.sqrt 2*(p 1/w)) (-1)+
        a • point (t*(p 0/w)) (t*(p 1/w)) 0 ∈ H := hc hbH htH (by linarith only [ha1]) ha0 (by ring)
    have hwidth : (1-a)*Real.sqrt 2+a*t = w := by dsimp only [a,t,w,width]; ring
    have hcoord (x : ℝ) : (1-a)*(Real.sqrt 2*(x/w))+a*(t*(x/w)) = x := by
      calc
        _ = ((1-a)*Real.sqrt 2+a*t)*(x/w) := by ring
        _ = w*(x/w) := by rw [hwidth]
        _ = x := by field_simp [hw.ne']
    have hheight : (1-a)*(-1)+a*0 = p 2 := by dsimp only [a]; ring
    rw [point_combo,hcoord,hcoord,hheight,point_coordinates] at h
    exact h
  · exact convexHull_min frustum_vertices_subset cut_isConvexBody.2.1

end SharpCut.Examples.SquarePyramid
