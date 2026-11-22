import SharpCut.Applications.Rounding

/-! # Exact normalized dual models for offset and simultaneous full-dimensional cuts

These are formulations and attained certificates. No new sharp contraction
profile for offset or prescribed multiple cuts is asserted.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix Set
namespace SharpCut.Optimization
variable {n N L : ℕ}

def offsetNormals (u : Fin N → V n) (v : V n) : Fin (N+1) → V n := Fin.cases v u
def offsetOffsets (η : ℝ) : Fin (N+1) → ℝ := Fin.cases η (fun _ => 1)
def offsetPolytope (u : Fin N → V n) (v : V n) (η : ℝ) : Set (V n) :=
  constraintPolytope u (fun _ => 1) ∩ {x | ⟪v,x⟫ ≤ η}

theorem offset_constraints (u : Fin N → V n) (v : V n) (η : ℝ) :
    constraintPolytope (offsetNormals u v) (offsetOffsets η) = offsetPolytope u v η := by
  ext x
  simp [constraintPolytope, offsetNormals, offsetOffsets, offsetPolytope, Fin.forall_fin_succ, and_comm]

theorem offset_normalization {u : Fin N → V n} {v : V n} {η : ℝ} {α : Fin (N+1) → ℝ} {q : Fin (N+1) → V n}
    (hd : DualFeasible (offsetNormals u v) (offsetOffsets η) α q) :
    (∑ i : Fin N, α i.succ)+η*α 0 = (n : ℝ) ∧ (∑ i, α i.succ • u i)+α 0 • v = 0 := by
  have hn := hd.normalization
  have hb := hd.balance
  simp only [Fin.sum_univ_succ, offsetNormals, offsetOffsets, Fin.cases_zero, Fin.cases_succ, mul_one] at hn hb
  exact ⟨by nlinarith only [hn], by simpa only [add_comm] using hb⟩

/-- Actual offset-cut optimum and dual optimum are attained with the changed normalization. -/
theorem offset_cut_duality (hn : 1 ≤ n) (u : Fin N → V n) (v : V n) (η : ℝ)
    (hu : ∀ i, u i ≠ 0) (hv : v ≠ 0) (hP : IsConvexBody (offsetPolytope u v η)) :
    ∃ c : V n, ∃ A : MatR n, ∃ α : Fin (N+1) → ℝ, ∃ q : Fin (N+1) → V n,
      IsMaxDet (offsetPolytope u v η) c A ∧
      PrimalOptimal (offsetNormals u v) (offsetOffsets η) c A ∧
      DualOptimal (offsetNormals u v) (offsetOffsets η) α q ∧ aggregate (offsetNormals u v) q = A⁻¹ ∧
      (∀ r, conePairing (offsetNormals u v) (offsetOffsets η) α q c A r = 0) ∧
      (∑ i : Fin N, α i.succ)+η*α 0 = (n : ℝ) ∧ (∑ i, α i.succ • u i)+α 0 • v = 0 ∧
      Real.log A.det+Real.log (aggregate (offsetNormals u v) q).det = 0 := by
  have hg : ∀ r, offsetNormals u v r ≠ 0 := by intro r; refine Fin.cases hv (fun i => hu i) r
  have hbody : IsConvexBody (constraintPolytope (offsetNormals u v) (offsetOffsets η)) := by rw [offset_constraints]; exact hP
  obtain ⟨⟨c, A, α, q, hmax, hp, hd, hM, hzero, hvalue⟩, _hforall⟩ := exact_duality hn (offsetNormals u v) (offsetOffsets η) hg hbody
  have hnorm := offset_normalization hd.1
  rw [offset_constraints] at hmax
  exact ⟨c, A, α, q, hmax, hp, hd, hM, hzero, hnorm.1, hnorm.2, hvalue⟩

def multipleNormals (u : Fin N → V n) (v : Fin L → V n) : Fin (N+L) → V n := Fin.addCases u v
def multipleOffsets (η : Fin L → ℝ) : Fin (N+L) → ℝ := Fin.addCases (fun _ => 1) η
def multiplePolytope (u : Fin N → V n) (v : Fin L → V n) (η : Fin L → ℝ) : Set (V n) :=
  constraintPolytope u (fun _ => 1) ∩ {x | ∀ j, ⟪v j,x⟫ ≤ η j}

theorem multiple_constraints (u : Fin N → V n) (v : Fin L → V n) (η : Fin L → ℝ) :
    constraintPolytope (multipleNormals u v) (multipleOffsets η) = multiplePolytope u v η := by
  ext x
  simp only [constraintPolytope, multiplePolytope, Set.mem_setOf_eq, Set.mem_inter_iff, Fin.forall_fin_add,
    multipleNormals, multipleOffsets, Fin.addCases_left, Fin.addCases_right]

theorem multiple_normalization {u : Fin N → V n} {v : Fin L → V n} {η : Fin L → ℝ}
    {α : Fin (N+L) → ℝ} {q : Fin (N+L) → V n} (hd : DualFeasible (multipleNormals u v) (multipleOffsets η) α q) :
    (∑ i, α (Fin.castAdd L i))+(∑ j, α (Fin.natAdd N j)*η j) = (n : ℝ) ∧
    (∑ i, α (Fin.castAdd L i) • u i)+(∑ j, α (Fin.natAdd N j) • v j) = 0 := by
  have hn := hd.normalization
  have hb := hd.balance
  rw [Fin.sum_univ_add] at hn hb
  simp only [multipleNormals, multipleOffsets, Fin.addCases_left, Fin.addCases_right, mul_one] at hn hb
  exact ⟨hn, hb⟩

/-- Exact full-dimensional simultaneous-cut duality with all normals in the balance equation. -/
theorem multiple_cut_duality (hn : 1 ≤ n) (u : Fin N → V n) (v : Fin L → V n) (η : Fin L → ℝ)
    (hu : ∀ i, u i ≠ 0) (hv : ∀ j, v j ≠ 0) (hP : IsConvexBody (multiplePolytope u v η)) :
    ∃ c : V n, ∃ A : MatR n, ∃ α : Fin (N+L) → ℝ, ∃ q : Fin (N+L) → V n,
      IsMaxDet (multiplePolytope u v η) c A ∧
      PrimalOptimal (multipleNormals u v) (multipleOffsets η) c A ∧
      DualOptimal (multipleNormals u v) (multipleOffsets η) α q ∧ aggregate (multipleNormals u v) q = A⁻¹ ∧
      (∀ r, conePairing (multipleNormals u v) (multipleOffsets η) α q c A r = 0) ∧
      (∑ i, α (Fin.castAdd L i))+(∑ j, α (Fin.natAdd N j)*η j) = (n : ℝ) ∧
      (∑ i, α (Fin.castAdd L i) • u i)+(∑ j, α (Fin.natAdd N j) • v j) = 0 ∧
      Real.log A.det+Real.log (aggregate (multipleNormals u v) q).det = 0 := by
  have hg : ∀ r, multipleNormals u v r ≠ 0 := by
    intro r
    refine Fin.addCases ?_ ?_ r
    · intro i; simpa only [multipleNormals, Fin.addCases_left] using hu i
    · intro j; simpa only [multipleNormals, Fin.addCases_right] using hv j
  have hbody : IsConvexBody (constraintPolytope (multipleNormals u v) (multipleOffsets η)) := by rw [multiple_constraints]; exact hP
  obtain ⟨⟨c, A, α, q, hmax, hp, hd, hM, hzero, hvalue⟩, _hforall⟩ := exact_duality hn (multipleNormals u v) (multipleOffsets η) hg hbody
  have hnorm := multiple_normalization hd.1
  rw [multiple_constraints] at hmax
  exact ⟨c, A, α, q, hmax, hp, hd, hM, hzero, hnorm.1, hnorm.2, hvalue⟩

end SharpCut.Optimization
