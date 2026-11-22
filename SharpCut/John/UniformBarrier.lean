import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Algebra.Order.Group

/-!
# A uniform compact first-order improvement

This compactness lemma absorbs the quadratic remainder of an ellipsoid
perturbation. At a zero of the original slack, a strictly negative first-order
term suffices. No contact nonemptiness or finite contact enumeration is assumed.
-/

noncomputable section
open Set
namespace SharpCut.John
variable {X : Type u} [TopologicalSpace X]

theorem uniform_quadratic_barrier {S : Set X} (hS : IsCompact S) (hSn : S.Nonempty)
    (r h q : X → ℝ) (hrc : ContinuousOn r S) (hhc : ContinuousOn h S)
    (hqc : ContinuousOn q S) (hr : ∀ x ∈ S, 0 ≤ r x)
    (hz : ∀ x ∈ S, r x = 0 → h x < 0) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ e : ℝ, 0 < e → e ≤ delta →
      ∀ x ∈ S, 0 ≤ r x-2*e*h x-e^2*q x := by
  have hgpos : ∀ x ∈ S, 0 < max (r x) (-h x) := by
    intro x hx
    by_cases h0 : r x = 0
    · exact (neg_pos.mpr (hz x hx h0)).trans_le (le_max_right _ _)
    · have hne : 0 ≠ r x := fun he => h0 he.symm
      exact ((hr x hx).lt_of_ne hne).trans_le (le_max_left _ _)
  have hgcont : ContinuousOn (fun x => max (r x) (-h x)) S := hrc.sup hhc.neg
  obtain ⟨xm, hxm, hmin⟩ := hS.exists_isMinOn hSn hgcont
  let m := max (r xm) (-h xm)
  have hm : 0 < m := hgpos xm hxm
  obtain ⟨xM, hxM, hmax⟩ := hS.exists_isMaxOn hSn (hhc.abs.add hqc.abs)
  let M := |h xM|+|q xM|
  have hM : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hbds : ∀ x ∈ S, |h x| ≤ M ∧ |q x| ≤ M := by
    intro x hx
    have hb : |h x|+|q x| ≤ M := hmax hx
    constructor <;> linarith [abs_nonneg (h x), abs_nonneg (q x)]
  have hd : 0 < 8*M+1 := by linarith
  refine ⟨min 1 (m/(8*M+1)), lt_min (by norm_num) (div_pos hm hd), ?_⟩
  intro e he hed x hx
  have he1 : e ≤ 1 := hed.trans (min_le_left _ _)
  have heB : e*(8*M+1) ≤ m :=
    (le_div_iff₀ hd).mp (hed.trans (min_le_right _ _))
  have heM : 0 ≤ e*M := mul_nonneg he.le hM
  have he2 : e^2 ≤ e := by nlinarith
  have hq : q x ≤ M := (le_abs_self _).trans (hbds x hx).2
  have hh : h x ≤ M := (le_abs_self _).trans (hbds x hx).1
  have hq2 := mul_le_mul_of_nonneg_left hq (sq_nonneg e)
  have hq1 := mul_le_mul_of_nonneg_right he2 hM
  have hg : m ≤ max (r x) (-h x) := hmin hx
  rcases le_max_iff.mp hg with hrm | hhm
  · have hh2 := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*e by positivity)
    nlinarith
  · have hhneg : h x ≤ -m := by linarith
    have hh2 := mul_le_mul_of_nonneg_left hhneg (show 0 ≤ 2*e by positivity)
    have hem : e*M ≤ m := by nlinarith
    have hqM := mul_le_mul_of_nonneg_left hem he.le
    nlinarith [hr x hx]

end SharpCut.John
