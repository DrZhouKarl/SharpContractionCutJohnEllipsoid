import SharpCut.Examples.PyramidHull

/-! # The stated pyramid and frustum generators are exactly their extreme points -/

noncomputable section
open scoped RealInnerProductSpace
open Set
namespace SharpCut.Examples.SquarePyramid

theorem upper_endpoint_average (a b s t c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a+b = 1)
    (hs : s ≤ c) (ht : t ≤ c) (he : a*s+b*t = c) : s = c ∧ t = c := by
  have hzero : a*(c-s)+b*(c-t) = 0 := by linear_combination c*hab-he
  have h1 : 0 ≤ a*(c-s) := mul_nonneg ha.le (sub_nonneg.mpr hs)
  have h2 : 0 ≤ b*(c-t) := mul_nonneg hb.le (sub_nonneg.mpr ht)
  have hz1 : a*(c-s) = 0 := by linarith only [hzero,h1,h2]
  have hz2 : b*(c-t) = 0 := by linarith only [hzero,h1,h2]
  have he1 : c-s = 0 := (mul_eq_zero.mp hz1).resolve_left ha.ne'
  have he2 : c-t = 0 := (mul_eq_zero.mp hz2).resolve_left hb.ne'
  constructor <;> linarith only [he1,he2]

theorem signed_endpoint_average (a b s t w σ : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a+b = 1)
    (hs : |s| ≤ w) (ht : |t| ≤ w) (hσ : σ = -1 ∨ σ = 1) (he : a*s+b*t = σ*w) : s = σ*w := by
  obtain ⟨hsl,hsu⟩ := abs_le.mp hs
  obtain ⟨htl,htu⟩ := abs_le.mp ht
  rcases hσ with rfl | rfl
  · have he' : a*(-s)+b*(-t) = w := by nlinarith only [he]
    have h := (upper_endpoint_average a b (-s) (-t) w ha hb hab (by linarith) (by linarith) he').1
    linarith only [h]
  · have h := (upper_endpoint_average a b s t w ha hb hab hsu htu (by simpa only [one_mul] using he)).1
    simpa only [one_mul] using h

theorem combo_coordinate (a b : ℝ) (p q r : V 3) (he : a • p+b • q = r) (i : Fin 3) :
    a*p i+b*q i = r i := by
  have h := congrArg (fun x : V 3 => x i) he
  simpa only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h

theorem horizontal_corner_extreme (K : Set (V 3)) (w z δ sx sy : ℝ) (hδ : δ ≠ 0)
    (hsx : sx = -1 ∨ sx = 1) (hsy : sy = -1 ∨ sy = 1)
    (hmem : point (sx*w) (sy*w) z ∈ K) (hface : ∀ q ∈ K, δ*q 2 ≤ δ*z)
    (hbox : ∀ q ∈ K, q 2 = z → |q 0| ≤ w ∧ |q 1| ≤ w) :
    point (sx*w) (sy*w) z ∈ K.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨hmem,?_⟩
  intro p hp q hq hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hz : a*p 2+b*q 2 = z := by simpa only [point_two] using combo_coordinate a b p q _ he 2
  have hzδ : a*(δ*p 2)+b*(δ*q 2) = δ*z := by linear_combination δ*hz
  have hlevels := upper_endpoint_average a b (δ*p 2) (δ*q 2) (δ*z) ha hb hab (hface p hp) (hface q hq) hzδ
  have hpz : p 2 = z := mul_left_cancel₀ hδ hlevels.1
  have hqz : q 2 = z := mul_left_cancel₀ hδ hlevels.2
  have hbp := hbox p hp hpz
  have hbq := hbox q hq hqz
  have hpx := signed_endpoint_average a b (p 0) (q 0) w sx ha hb hab hbp.1 hbq.1 hsx
    (by simpa only [point_zero] using combo_coordinate a b p q _ he 0)
  have hpy := signed_endpoint_average a b (p 1) (q 1) w sy ha hb hab hbp.2 hbq.2 hsy
    (by simpa only [point_one] using combo_coordinate a b p q _ he 1)
  calc
    p = point (p 0) (p 1) (p 2) := (point_coordinates p).symm
    _ = point (sx*w) (sy*w) z := by rw [hpx,hpy,hpz]

def cornerSigns : Fin 4 → ℝ × ℝ := ![(-1,-1),(1,-1),(-1,1),(1,1)]

theorem square_vertex_signs (w z : ℝ) (i : Fin 4) :
    squareVertices w z i = point ((cornerSigns i).1*w) ((cornerSigns i).2*w) z := by
  fin_cases i <;> simp [squareVertices,cornerSigns]

theorem corner_signs (i : Fin 4) : ((cornerSigns i).1 = -1 ∨ (cornerSigns i).1 = 1) ∧
    ((cornerSigns i).2 = -1 ∨ (cornerSigns i).2 = 1) := by fin_cases i <;> norm_num [cornerSigns]

theorem square_vertices_extreme (K : Set (V 3)) (w z δ : ℝ) (hδ : δ ≠ 0)
    (hmem : ∀ i, squareVertices w z i ∈ K) (hface : ∀ q ∈ K, δ*q 2 ≤ δ*z)
    (hbox : ∀ q ∈ K, q 2 = z → |q 0| ≤ w ∧ |q 1| ≤ w) (i : Fin 4) :
    squareVertices w z i ∈ K.extremePoints ℝ := by
  rw [square_vertex_signs]
  exact horizontal_corner_extreme K w z δ _ _ hδ (corner_signs i).1 (corner_signs i).2
    (by rw [← square_vertex_signs]; exact hmem i) hface hbox

theorem body_height_upper {p : V 3} (hp : p ∈ body) : p 2 ≤ 3 := by
  have hnonneg : 0 ≤ 2*Real.sqrt 2*|p 0| := by positivity
  linarith only [hp.2.1,hnonneg]

theorem body_at_apex {p : V 3} (hp : p ∈ body) (hz : p 2 = 3) : p = apex := by
  have h := (body_width p).mp hp
  rw [hz,width_apex] at h
  have hx : p 0 = 0 := abs_eq_zero.mp (le_antisymm h.2.1 (abs_nonneg _))
  have hy : p 1 = 0 := abs_eq_zero.mp (le_antisymm h.2.2 (abs_nonneg _))
  calc
    p = point (p 0) (p 1) (p 2) := (point_coordinates p).symm
    _ = apex := by rw [hx,hy,hz]; rfl

theorem apex_extreme : apex ∈ body.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨apex_mem_body,?_⟩
  intro p hp q hq hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hz : a*p 2+b*q 2 = 3 := by simpa only [apex,point_two] using combo_coordinate a b p q _ he 2
  exact body_at_apex hp (upper_endpoint_average a b (p 2) (q 2) 3 ha hb hab (body_height_upper hp) (body_height_upper hq) hz).1

theorem base_vertices_extreme (i : Fin 4) : squareVertices (Real.sqrt 2) (-1) i ∈ body.extremePoints ℝ := by
  apply square_vertices_extreme body (Real.sqrt 2) (-1) (-1) (by norm_num) base_vertex_mem_body
  · intro q hq
    linarith only [hq.1]
  · intro q hq hz
    have h := (body_width q).mp hq
    rw [hz,width_base] at h
    exact h.2

theorem body_extremePoints : body.extremePoints ℝ = pyramidVertices := by
  apply Set.Subset.antisymm
  · rw [body_eq_vertex_hull]
    exact extremePoints_convexHull_subset
  · rintro p (hp | ⟨i,rfl⟩)
    · rw [Set.mem_singleton_iff] at hp
      rw [hp]
      exact apex_extreme
    · exact base_vertices_extreme i

theorem cut_base_vertices_extreme (i : Fin 4) : squareVertices (Real.sqrt 2) (-1) i ∈ cutBody.extremePoints ℝ := by
  apply square_vertices_extreme cutBody (Real.sqrt 2) (-1) (-1) (by norm_num)
    (fun i => frustum_vertices_subset (Or.inl ⟨i,rfl⟩))
  · intro q hq
    linarith only [hq.1.1]
  · intro q hq hz
    have h := (body_width q).mp hq.1
    rw [hz,width_base] at h
    exact h.2

theorem cut_top_vertices_extreme (i : Fin 4) : squareVertices (3*Real.sqrt 2/4) 0 i ∈ cutBody.extremePoints ℝ := by
  apply square_vertices_extreme cutBody (3*Real.sqrt 2/4) 0 1 (by norm_num)
    (fun i => frustum_vertices_subset (Or.inr ⟨i,rfl⟩))
  · intro q hq
    simpa only [one_mul,mul_zero,Set.mem_setOf_eq] using hq.2
  · intro q hq hz
    have h := (body_width q).mp hq.1
    rw [hz,width_cut] at h
    exact h.2

theorem cut_extremePoints : cutBody.extremePoints ℝ = frustumVertices := by
  apply Set.Subset.antisymm
  · rw [cut_eq_vertex_hull]
    exact extremePoints_convexHull_subset
  · rintro p (⟨i,rfl⟩ | ⟨i,rfl⟩)
    · exact cut_base_vertices_extreme i
    · exact cut_top_vertices_extreme i

end SharpCut.Examples.SquarePyramid
