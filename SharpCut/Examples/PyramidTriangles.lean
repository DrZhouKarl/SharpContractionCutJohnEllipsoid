import SharpCut.Examples.PyramidFaceModels

/-! # The four side faces are genuine affine two-dimensional triangles -/

noncomputable section
open scoped BigOperators
open Set
namespace SharpCut.Examples.SquarePyramid

theorem apex_edge_affineIndependent (p q : V 3) (hp : p 2 = -1) (hq : q 2 = -1)
    (k : Fin 3) (hne : p k ≠ q k) : AffineIndependent ℝ ![apex,p,q] := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hzero
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero Finset.univ w ![apex,p,q] hw (0 : V 3),
    Finset.weightedVSubOfPoint_apply] at hzero
  simp only [vsub_eq_sub,sub_zero] at hzero
  have hsum : w 0+w 1+w 2 = 0 := by simpa only [Fin.sum_univ_three] using hw
  have hcoord (i : Fin 3) : w 0*apex i+w 1*p i+w 2*q i = 0 := by
    have h := congrArg (fun x : V 3 => x i) hzero
    simpa [Fin.sum_univ_three,WithLp.ofLp_add,WithLp.ofLp_smul,WithLp.ofLp_zero,
      Pi.add_apply,Pi.smul_apply,Pi.zero_apply,smul_eq_mul] using h
  have hz := hcoord 2
  rw [apex,point_two,hp,hq] at hz
  have hw0 : w 0 = 0 := by linarith only [hz,hsum]
  have hw12 : w 1+w 2 = 0 := by linarith only [hw0,hsum]
  have hk := hcoord k
  rw [hw0,zero_mul,zero_add] at hk
  have hprod : w 1*(p k-q k) = 0 := by linear_combination hk-q k*hw12
  have hw1 : w 1 = 0 := (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hne)
  have hw2 : w 2 = 0 := by linarith only [hw12,hw1]
  intro i
  fin_cases i
  · exact hw0
  · exact hw1
  · exact hw2

theorem side_triangles_affineIndependent (i : Fin 4) : AffineIndependent ℝ (sideTriangle i) := by
  fin_cases i
  · change AffineIndependent ℝ ![apex,baseVertex 1,baseVertex 3]
    apply apex_edge_affineIndependent _ _ (by rfl) (by rfl) 1
    change -(Real.sqrt 2) ≠ Real.sqrt 2
    linarith only [sqrt_two_pos]
  · change AffineIndependent ℝ ![apex,baseVertex 0,baseVertex 2]
    apply apex_edge_affineIndependent _ _ (by rfl) (by rfl) 1
    change -(Real.sqrt 2) ≠ Real.sqrt 2
    linarith only [sqrt_two_pos]
  · change AffineIndependent ℝ ![apex,baseVertex 2,baseVertex 3]
    apply apex_edge_affineIndependent _ _ (by rfl) (by rfl) 0
    change -(Real.sqrt 2) ≠ Real.sqrt 2
    linarith only [sqrt_two_pos]
  · change AffineIndependent ℝ ![apex,baseVertex 0,baseVertex 1]
    apply apex_edge_affineIndependent _ _ (by rfl) (by rfl) 0
    change -(Real.sqrt 2) ≠ Real.sqrt 2
    linarith only [sqrt_two_pos]

theorem four_triangular_facets (i : Fin 4) :
    facet i.succ = convexHull ℝ (Set.range (sideTriangle i)) ∧ AffineIndependent ℝ (sideTriangle i) :=
  ⟨side_facet_hull i,side_triangles_affineIndependent i⟩

end SharpCut.Examples.SquarePyramid
