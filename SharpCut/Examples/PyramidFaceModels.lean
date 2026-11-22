import SharpCut.Examples.SupportingFace
import Mathlib.Data.Set.Card

/-! # Exact square base and triangular side-face descriptions -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Set Matrix
namespace SharpCut.Examples.SquarePyramid

def baseVertex (i : Fin 4) : V 3 := squareVertices (Real.sqrt 2) (-1) i
def vertexFive : Fin 5 → V 3 := ![apex,baseVertex 0,baseVertex 1,baseVertex 2,baseVertex 3]
def sideTriangle : Fin 4 → Fin 3 → V 3 :=
  ![![apex,baseVertex 1,baseVertex 3],![apex,baseVertex 0,baseVertex 2],
    ![apex,baseVertex 2,baseVertex 3],![apex,baseVertex 0,baseVertex 1]]
def facetVertexModel : Fin 5 → Set (V 3) :=
  ![Set.range baseVertex,Set.range (sideTriangle 0),Set.range (sideTriangle 1),
    Set.range (sideTriangle 2),Set.range (sideTriangle 3)]
def facetVertexSet (i : Fin 5) : Set (V 3) := pyramidVertices ∩ {p | ⟪frame.contact i,p⟫ = 1}
def facet (i : Fin 5) : Set (V 3) := body ∩ {p | ⟪frame.contact i,p⟫ = 1}
def facetScores : Matrix (Fin 5) (Fin 5) ℝ :=
  !![-3,1,1,1,1;
     1,-5/3,1,-5/3,1;
     1,1,-5/3,1,-5/3;
     1,-5/3,-5/3,1,1;
     1,1,1,-5/3,-5/3]

theorem vertex_five_range : Set.range vertexFive = pyramidVertices := by
  ext p
  simp [vertexFive,pyramidVertices,baseVertex,Set.mem_range,Fin.exists_fin_succ,eq_comm] <;> tauto

theorem vertex_five_injective : Function.Injective vertexFive := by
  intro i j he
  by_contra hij
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    have hx := congrArg (fun p : V 3 => p 0) he
    have hy := congrArg (fun p : V 3 => p 1) he
    have hz := congrArg (fun p : V 3 => p 2) he
    norm_num [vertexFive,baseVertex,squareVertices,apex,point] at hx <;>
      norm_num [vertexFive,baseVertex,squareVertices,apex,point] at hy <;>
      norm_num [vertexFive,baseVertex,squareVertices,apex,point] at hz <;> linarith [sqrt_two_pos]

theorem five_extreme_points : (body.extremePoints ℝ).ncard = 5 := by
  rw [body_extremePoints,← vertex_five_range,Set.ncard_range_of_injective vertex_five_injective]
  norm_num

theorem facet_scores (i j : Fin 5) : ⟪frame.contact i,vertexFive j⟫ = facetScores i j := by
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  fin_cases i <;> fin_cases j <;>
    norm_num [contact_array,vertexFive,baseVertex,squareVertices,apex,inner_point,facetScores] <;>
    nlinarith only [hs]

theorem facet_vertices_formula (i : Fin 5) : facetVertexSet i = facetVertexModel i := by
  have he : facetVertexSet i = {p | ∃ j : Fin 5, vertexFive j = p ∧ facetScores i j = 1} := by
    ext p
    constructor
    · rintro ⟨hp,hplane⟩
      rw [← vertex_five_range] at hp
      obtain ⟨j,rfl⟩ := hp
      exact ⟨j,rfl,by rwa [← facet_scores]⟩
    · rintro ⟨j,rfl,hplane⟩
      exact ⟨by rw [← vertex_five_range]; exact ⟨j,rfl⟩,(facet_scores i j).trans hplane⟩
  rw [he]
  fin_cases i <;> ext p <;>
    simp [facetVertexModel,sideTriangle,Set.mem_range,Fin.exists_fin_succ,vertexFive,facetScores,eq_comm] <;> norm_num <;> tauto

/-- Each actual supporting face is the convex hull of exactly its stated vertices. -/
theorem facet_hull_formula (i : Fin 5) : facet i = convexHull ℝ (facetVertexModel i) := by
  have hsupport : ∀ p ∈ pyramidVertices, ⟪frame.contact i,p⟫ ≤ 1 := by
    intro p hp
    have h := pyramid_vertices_subset hp
    rw [← polytope_eq_body] at h
    exact h i
  have h := supporting_plane_hull pyramidVertices (frame.contact i) 1 hsupport
  rw [← body_eq_vertex_hull] at h
  change facet i = convexHull ℝ (facetVertexSet i) at h
  rwa [facet_vertices_formula] at h

theorem base_facet_hull : facet 0 = convexHull ℝ (Set.range (squareVertices (Real.sqrt 2) (-1))) := by
  have h := facet_hull_formula 0
  have hm : facetVertexModel 0 = Set.range baseVertex := rfl
  have hf : baseVertex = squareVertices (Real.sqrt 2) (-1) := by funext i; rfl
  rw [hm,hf] at h
  exact h

theorem side_facet_hull (i : Fin 4) : facet i.succ = convexHull ℝ (Set.range (sideTriangle i)) := by
  have h := facet_hull_formula i.succ
  have he : facetVertexModel i.succ = Set.range (sideTriangle i) := by fin_cases i <;> rfl
  rwa [he] at h

end SharpCut.Examples.SquarePyramid
