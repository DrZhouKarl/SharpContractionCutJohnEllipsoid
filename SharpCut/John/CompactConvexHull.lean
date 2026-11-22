import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compact convex hulls in finite dimensions

A finite union of images of a compact simplex times a compact finite power
supplies the closure needed by the contact-moment separation proof. Empty
sets are included; no nonempty contact set is assumed.
-/

noncomputable section
open scoped BigOperators
open Set
namespace SharpCut.John
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def combinationDomain (C : Set E) (k : ℕ) : Set ((Fin k → ℝ) × (Fin k → E)) :=
  {p | (∀ i, 0 ≤ p.1 i) ∧ (∑ i, p.1 i) = 1 ∧ ∀ i, p.2 i ∈ C}

def combinationMap (k : ℕ) (p : (Fin k → ℝ) × (Fin k → E)) : E := ∑ i, p.1 i • p.2 i

theorem combinationMap_continuous (k : ℕ) : Continuous (combinationMap (E := E) k) := by
  unfold combinationMap
  fun_prop

theorem combinationDomain_isCompact {C : Set E} (hC : IsCompact C) (k : ℕ) :
    IsCompact (combinationDomain C k) := by
  have he : combinationDomain C k =
      stdSimplex ℝ (Fin k) ×ˢ {z : Fin k → E | ∀ i, z i ∈ C} := by
    ext p; simp [combinationDomain, stdSimplex, and_assoc]
  rw [he]
  exact (isCompact_stdSimplex ℝ (Fin k)).prod (isCompact_pi_infinite (fun _ => hC))

theorem combination_mem_convexHull {C : Set E} {k : ℕ}
    {p : (Fin k → ℝ) × (Fin k → E)} (hp : p ∈ combinationDomain C k) :
    combinationMap k p ∈ convexHull ℝ C := by
  exact (convex_convexHull ℝ C).sum_mem (fun i _ => hp.1 i) hp.2.1
    (fun i _ => subset_convexHull ℝ C (hp.2.2 i))

theorem convexHull_mem_bounded_combination {C : Set E} {x : E} (hx : x ∈ convexHull ℝ C) :
    ∃ k : Fin (Module.finrank ℝ E+2),
      x ∈ combinationMap (E := E) k.val '' combinationDomain C k.val := by
  classical
  obtain ⟨ι, hi, z, w, hz, hai, hw, hsum, hcombo⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  letI := hi
  have hcard : Fintype.card ι ≤ Module.finrank ℝ E+1 :=
    hai.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  let k : Fin (Module.finrank ℝ E+2) := ⟨Fintype.card ι, by omega⟩
  let e : Fin k.val ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨k, ((w ∘ e), (z ∘ e)), ?_, ?_⟩
  · refine ⟨fun i => (hw (e i)).le, ?_, fun i => hz ⟨e i, rfl⟩⟩
    exact (e.sum_comp w).trans hsum
  · exact (e.sum_comp (fun i => w i • z i)).trans hcombo

theorem compact_convexHull {C : Set E} (hC : IsCompact C) : IsCompact (convexHull ℝ C) := by
  have he : convexHull ℝ C = ⋃ k : Fin (Module.finrank ℝ E+2),
      combinationMap (E := E) k.val '' combinationDomain C k.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := convexHull_mem_bounded_combination hx
      exact mem_iUnion.mpr ⟨k, hk⟩
    · intro hx
      obtain ⟨k, p, hp, rfl⟩ := mem_iUnion.mp hx
      exact combination_mem_convexHull hp
  rw [he]
  exact isCompact_iUnion (fun k =>
    (combinationDomain_isCompact hC k.val).image (combinationMap_continuous k.val))

end SharpCut.John
