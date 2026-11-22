import SharpCut.John.ContactMoments
import SharpCut.JohnFrame
import Khachiyan.GeometricBound

/-!
# John contact necessity for an arbitrary convex body

Separation of the compact contact-moment hull produces a trace-positive
symmetric improving direction if the normalized target is missing. The actual
uniform feasible perturbation contradicts global ellipsoid maximality.
Carathéodory then supplies finite strictly positive contact weights.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix Set
namespace SharpCut.John
variable {n : ℕ}

theorem target_in_contact_hull (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hmax : IsJohnNormalized K) : targetMoment n ∈ convexHull ℝ (contactAtom '' contacts K) := by
  by_contra hout
  have hcomp := compact_convexHull (contactAtoms_isCompact hmax.unitBall_subset)
  obtain ⟨f, c, hc, htarget⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (contactAtom '' contacts K)) hcomp.isClosed hout
  let z : MomentSpace n := (InnerProductSpace.toDual ℝ (MomentSpace n)).symm f
  have hz (x : MomentSpace n) : ⟪z, x⟫ = f x := InnerProductSpace.toDual_symm_apply
  have htrace : 0 < (separatingShape z c).trace :=
    separatingShape_trace_positive hn z c (by rw [hz]; exact htarget)
  have hdir : ∀ u ∈ contacts K, perturbSlope (vectorCoefficient z) (separatingShape z c) u < 0 := by
    intro u hu
    rw [separatingShape_contact_pairing z c u hu.1]
    have h := hc (contactAtom u) (subset_convexHull ℝ _ ⟨u, hu, rfl⟩)
    rw [← hz] at h
    linarith
  exact no_strict_contact_improver hK hmax (vectorCoefficient z) (separatingShape z c)
    (separatingShape_symmetric z c) htrace hdir

theorem exists_supporting_frame (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hmax : IsJohnNormalized K) : ∃ N : ℕ, ∃ F : JohnFrame n N, F.Supports K := by
  classical
  obtain ⟨ι, hi, z, w, hz, _hai, hw, _hsum, hcombo⟩ :=
    eq_pos_convex_span_of_mem_convexHull (target_in_contact_hull hn hK hmax)
  letI := hi
  have hzi : ∀ i : ι, ∃ u : V n, u ∈ contacts K ∧ contactAtom u = z i :=
    fun i => hz ⟨i, rfl⟩
  choose u hu hatom using hzi
  have hraw : ∑ i, w i • contactAtom (u i) = targetMoment n := by
    simpa only [hatom] using hcombo
  have hfirst (j : Fin n) : ∑ i, w i*u i j = 0 := by
    have h := congrArg (fun p : MomentSpace n => p.ofLp (Sum.inl j)) hraw
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    change (∑ i, w i*u i j) = 0 at h
    exact h
  have hsecond (j k : Fin n) : ∑ i, w i*(u i j*u i k) = (1 : MatR n) j k/(n : ℝ) := by
    have h := congrArg (fun p : MomentSpace n => p.ofLp (Sum.inr (j, k))) hraw
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    change (∑ i, w i*(u i j*u i k)) = (1 : MatR n) j k/(n : ℝ) at h
    exact h
  let N := Fintype.card ι
  let e : Fin N ≃ ι := (Fintype.equivFin ι).symm
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hv0 : ∑ i : Fin N, ((n : ℝ)*w (e i)) • u (e i) = 0 := by
    apply WithLp.ofLp_injective 2
    ext j
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    calc
      _ = (n : ℝ)*∑ i : Fin N, w (e i)*u (e i) j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
      _ = (n : ℝ)*∑ i : ι, w i*u i j :=
        congrArg (fun x : ℝ => (n : ℝ)*x) (e.sum_comp (fun i : ι => w i*u i j))
      _ = 0 := by rw [hfirst, mul_zero]
  have hm0 : ∑ i : Fin N, ((n : ℝ)*w (e i)) • outer (u (e i)) = 1 := by
    ext j k
    simp only [Matrix.sum_apply, Matrix.smul_apply, Khachiyan.outer_apply, smul_eq_mul]
    calc
      _ = (n : ℝ)*∑ i : Fin N, w (e i)*(u (e i) j*u (e i) k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
      _ = (n : ℝ)*∑ i : ι, w i*(u i j*u i k) :=
        congrArg (fun x : ℝ => (n : ℝ)*x) (e.sum_comp (fun i : ι => w i*(u i j*u i k)))
      _ = (1 : MatR n) j k := by rw [hsecond]; field_simp [hnpos.ne']
  let F : JohnFrame n N := {
    contact := fun i => u (e i)
    weight := fun i => (n : ℝ)*w (e i)
    contact_unit := fun i => (hu (e i)).1
    weight_pos := fun i => mul_pos hnpos (hw (e i))
    first_moment := hv0
    second_moment := hm0 }
  exact ⟨N, F, fun i x hx => (hu (e i)).2 x hx⟩

end SharpCut.John

namespace SharpCut.Geometry
variable {n : ℕ}

/-- Lemma 2.2, with actual maximality and actual boundary contacts. -/
theorem john_contact_iff (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    (hball : unitBall n ⊆ K) :
    IsJohnNormalized K ↔ ∃ N : ℕ, ∃ F : JohnFrame n N,
      F.Supports K ∧ ∀ i, F.contact i ∈ frontier K := by
  constructor
  · intro hmax
    obtain ⟨N, F, hs⟩ := John.exists_supporting_frame hn hK hmax
    exact ⟨N, F, hs, fun i => John.contact_mem_frontier hball ⟨F.contact_unit i, hs i⟩⟩
  · rintro ⟨N, F, hs, _⟩
    exact Khachiyan.isJohnNormalized_of_contacts hball F.contact F.weight
      F.contact_unit F.weight_pos hs F.first_moment F.second_moment

theorem john_normalized_iff_parameters [NeZero n] (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K) :
    IsJohnNormalized K ↔ Khachiyan.johnCenter K = 0 ∧ Khachiyan.johnShape K = 1 := by
  letI : NeZero n := ⟨by omega⟩
  constructor
  · intro h
    exact ⟨Khachiyan.johnCenter_eq_of_isMaxDet hK h, Khachiyan.johnShape_eq_of_isMaxDet hK h⟩
  · rintro ⟨hc, hs⟩
    have h := Khachiyan.john_isMaxDet hK
    rwa [hc, hs] at h

end SharpCut.Geometry
