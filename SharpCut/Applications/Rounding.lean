import SharpCut.Applications.Initialization

/-! # General and centrally symmetric John rounding with actual affine ellipsoid sets -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix Set
namespace SharpCut.Applications
open Certificate
variable {n : ℕ} [NeZero n]

def CentrallySymmetric (K : Set (V n)) : Prop := ∃ z : V n, ∀ x ∈ K, (2 : ℝ) • z-x ∈ K

/-- Symmetry supplies a second feasible ellipse with the reflected center and the same positive shape. -/
theorem reflect_feasible {K : Set (V n)} {c z : V n} {A : MatR n}
    (hsym : ∀ x ∈ K, (2 : ℝ) • z-x ∈ K) (hA : IsFeasible K c A) : IsFeasible K ((2 : ℝ) • z-c) A := by
  refine ⟨hA.1, ?_⟩
  rintro x ⟨u, hu, rfl⟩
  have hneg : -u ∈ unitBall n := (Khachiyan.mem_unitBall (-u)).mpr (by simpa only [norm_neg] using (Khachiyan.mem_unitBall u).mp hu)
  have hx : c+Matrix.toEuclideanCLM (𝕜 := ℝ) A (-u) ∈ K := hA.2 ⟨-u, hneg, rfl⟩
  have href := hsym _ hx
  have he : (2 : ℝ) • z-(c+Matrix.toEuclideanCLM (𝕜 := ℝ) A (-u)) =
      ((2 : ℝ) • z-c)+Matrix.toEuclideanCLM (𝕜 := ℝ) A u := by rw [map_neg]; abel
  rwa [he] at href

/-- The genuine unique John center is the symmetry center; no center equality is assumed. -/
theorem symmetry_center_eq {K : Set (V n)} (hK : IsConvexBody K) {c z : V n} {A : MatR n}
    (hsym : ∀ x ∈ K, (2 : ℝ) • z-x ∈ K) (hmax : IsMaxDet K c A) : c = z := by
  have hmax' : IsMaxDet K ((2 : ℝ) • z-c) A := ⟨reflect_feasible hsym hmax.feasible, hmax.det_le⟩
  have hcenter := (Khachiyan.isMaxDet_unique hK.2.1 hK.1.isClosed hmax hmax').1
  have he : c-z = (1/2 : ℝ) • (c-((2 : ℝ) • z-c)) := by module
  rw [← hcenter, sub_self, smul_zero] at he
  exact sub_eq_zero.mp he

/-- Affine John normalization preserves the derived central symmetry about zero. -/
theorem normalized_body_symmetric {K : Set (V n)} (hK : IsConvexBody K) (hsym : CentrallySymmetric K)
    {c : V n} {A : MatR n} (hmax : IsMaxDet K c A) :
    ∀ u ∈ Khachiyan.normalizedBody K c A, -u ∈ Khachiyan.normalizedBody K c A := by
  obtain ⟨z, hz⟩ := hsym
  have hc := symmetry_center_eq hK hz hmax
  subst z
  intro u hu
  rw [Khachiyan.normalizedBody_eq_preimage hmax.posDef] at hu ⊢
  have href := hz _ hu
  have he : (2 : ℝ) • c-Khachiyan.denormalizePoint c A u = Khachiyan.denormalizePoint c A (-u) := by
    unfold Khachiyan.denormalizePoint
    rw [map_neg]
    module
  rwa [he] at href

/-- In symmetric John coordinates, every selected frame supplies the exact squared sqrt(n) bound. -/
theorem symmetric_normalized_norm_bound (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K) (hJ : IsJohnNormalized K)
    (hsym : ∀ x ∈ K, -x ∈ K) {x : V n} (hx : x ∈ K) : ‖x‖ ≤ Real.sqrt (n : ℝ) := by
  obtain ⟨N, F, hs⟩ := John.exists_supporting_frame hn hK hJ
  have hheight (i : Fin N) : |⟪F.contact i,x⟫| ≤ 1 := by
    have hp := hs i x hx
    have hm := hs i (-x) (hsym x hx)
    rw [inner_neg_right] at hm
    exact abs_le.mpr ⟨by linarith only [hm], hp⟩
  have hsq (i : Fin N) : ⟪F.contact i,x⟫^2 ≤ 1 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr (hheight i)
    simpa only [sq_abs, one_pow] using h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hsq i) (F.weight_pos i).le)
  rw [F.scalar_second_moment] at hsum
  simp only [mul_one, F.weight_sum] at hsum
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsqrt := Real.sq_sqrt hn0
  nlinarith only [hsum, hsqrt, norm_nonneg x, Real.sqrt_nonneg (n : ℝ)]

/-- A normalized radius bound gives actual containment in the dilated John ellipsoid. -/
theorem mem_dilated_ellipsoid (c : V n) (A : MatR n) (hA : A.PosDef) (R : ℝ) (hR : 0 < R) (x : V n)
    (hnorm : ‖Khachiyan.normalizePoint c A x‖ ≤ R) : x ∈ Khachiyan.ellipsoid c (R • A) := by
  let u : V n := (1/R) • Khachiyan.normalizePoint c A x
  have hu : u ∈ unitBall n := by
    rw [Khachiyan.mem_unitBall]
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hR)]
    have h : ‖Khachiyan.normalizePoint c A x‖/R ≤ 1 := (div_le_iff₀ hR).mpr (by simpa only [one_mul] using hnorm)
    convert h using 1 <;> ring
  refine ⟨u, hu, ?_⟩
  dsimp only [u]
  rw [matrix_action_smul, map_smul, smul_smul, show R*(1/R) = 1 by field_simp [hR.ne'], one_smul]
  exact Khachiyan.denormalize_normalize hA c x

/-- General John rounding for every actual optimum, after derived finite-frame normalization. -/
theorem john_affine_rounding (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K) {c : V n} {A : MatR n}
    (hmax : IsMaxDet K c A) : Khachiyan.ellipsoid c A ⊆ K ∧ K ⊆ Khachiyan.ellipsoid c ((n : ℝ) • A) := by
  have hN := hK.normalizedBody c hmax.posDef
  have hJ := hmax.isJohnNormalized
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine ⟨hmax.subset, ?_⟩
  intro x hx
  have hxN : Khachiyan.normalizePoint c A x ∈ Khachiyan.normalizedBody K c A := ⟨x, hx, rfl⟩
  exact mem_dilated_ellipsoid c A hmax.posDef (n : ℝ) hnpos x (normalized_body_norm_bound hn hN hJ hxN)

/-- The centrally symmetric sqrt(n) rounding factor, for actual bodies and actual John ellipsoids. -/
theorem symmetric_john_affine_rounding (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K) (hsym : CentrallySymmetric K)
    {c : V n} {A : MatR n} (hmax : IsMaxDet K c A) :
    Khachiyan.ellipsoid c A ⊆ K ∧ K ⊆ Khachiyan.ellipsoid c (Real.sqrt (n : ℝ) • A) := by
  have hN := hK.normalizedBody c hmax.posDef
  have hJ := hmax.isJohnNormalized
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine ⟨hmax.subset, ?_⟩
  intro x hx
  have hxN : Khachiyan.normalizePoint c A x ∈ Khachiyan.normalizedBody K c A := ⟨x, hx, rfl⟩
  exact mem_dilated_ellipsoid c A hmax.posDef (Real.sqrt (n : ℝ)) (Real.sqrt_pos.mpr hnpos) x
    (symmetric_normalized_norm_bound hn hN hJ (normalized_body_symmetric hK hsym hmax) hxN)


/-- Complete SUP-03: actual general/symmetric rounding and unchanged sharp contact-polytope supremum. -/
theorem john_rounding_and_contact_supremum (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K) :
    (∀ c : V n, ∀ A : MatR n, IsMaxDet K c A → Khachiyan.ellipsoid c A ⊆ K ∧ K ⊆ Khachiyan.ellipsoid c ((n : ℝ) • A)) ∧
    (CentrallySymmetric K → ∀ c : V n, ∀ A : MatR n, IsMaxDet K c A →
      Khachiyan.ellipsoid c A ⊆ K ∧ K ⊆ Khachiyan.ellipsoid c (Real.sqrt (n : ℝ) • A)) ∧
    Geometry.optimalConstant n = sharpRatio n ∧ Geometry.contactOptimalConstant n = sharpRatio n :=
  ⟨fun c A hmax => john_affine_rounding hn hK hmax,
    fun hsym c A hmax => symmetric_john_affine_rounding hn hK hsym hmax,
    Geometry.optimalConstant_eq hn, Geometry.contactOptimalConstant_eq hn⟩

end SharpCut.Applications
