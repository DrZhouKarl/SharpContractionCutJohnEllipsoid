import SharpCut.Sharpness.Attainment
import SharpCut.Sharpness.IntervalFrame

/-! # The sharp geometric theorem and attained fixed-dimensional suprema -/

noncomputable section
open scoped RealInnerProductSpace ENNReal
open Set MeasureTheory
namespace SharpCut.Geometry
variable {n : ℕ} [NeZero n]

def volumeRatios (n : ℕ) [NeZero n] : Set ℝ :=
  {r | ∃ (K : Set (V n)) (v : V n), IsConvexBody K ∧ v ≠ 0 ∧
    r = (maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v)).toReal/
      (maxEllipsoidVolume K).toReal}

def contactVolumeRatios (n : ℕ) [NeZero n] : Set ℝ :=
  {r | ∃ N : ℕ, ∃ F : JohnFrame n N, ∃ v : V n, v ≠ 0 ∧
    r = (maxEllipsoidVolume (F.polytope ∩ centralHalfspace (Khachiyan.johnCenter F.polytope) v)).toReal/
      (maxEllipsoidVolume F.polytope).toReal}

def optimalConstant (n : ℕ) [NeZero n] : ℝ := sSup (volumeRatios n)
def contactOptimalConstant (n : ℕ) [NeZero n] : ℝ := sSup (contactVolumeRatios n)

theorem ratio_eq_of_attainment (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K) {v : V n}
    (he : maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v) =
      ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K) :
    (maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v)).toReal/
      (maxEllipsoidVolume K).toReal = sharpRatio n := by
  have h := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sharpRatio_pos hn).le] at h
  exact (div_eq_iff (Khachiyan.john_isMaxDet hK).maxEllipsoidVolume_toReal_pos.ne').mpr h

theorem sharpRatio_mem_volumeRatios (hn : 1 ≤ n) : sharpRatio n ∈ volumeRatios n := by
  obtain ⟨K, v, hK, hv, he⟩ := Sharpness.fixed_dimension_attainment hn
  exact ⟨K, v, hK, hv, (ratio_eq_of_attainment hn hK he).symm⟩

theorem volumeRatios_upper (hn : 1 ≤ n) : ∀ r ∈ volumeRatios n, r ≤ sharpRatio n := by
  intro r hr
  rcases hr with ⟨K, v, hK, hv, rfl⟩
  exact sharp_center_cut_ratio_upper hn hK hv

theorem volumeRatios_isGreatest (hn : 1 ≤ n) : IsGreatest (volumeRatios n) (sharpRatio n) :=
  ⟨sharpRatio_mem_volumeRatios hn, volumeRatios_upper hn⟩

theorem volumeRatios_nonempty_bounded (hn : 1 ≤ n) : (volumeRatios n).Nonempty ∧ BddAbove (volumeRatios n) :=
  ⟨⟨sharpRatio n, sharpRatio_mem_volumeRatios hn⟩, ⟨sharpRatio n, volumeRatios_upper hn⟩⟩

theorem optimalConstant_eq (hn : 1 ≤ n) : optimalConstant n = sharpRatio n :=
  (volumeRatios_isGreatest hn).csSup_eq

theorem fixed_contact_attainment (hn : 1 ≤ n) :
    ∃ N : ℕ, ∃ F : JohnFrame n N, ∃ v : V n, v ≠ 0 ∧
      maxEllipsoidVolume (F.polytope ∩ centralHalfspace (Khachiyan.johnCenter F.polytope) v) =
        ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume F.polytope := by
  by_cases h1 : n = 1
  · subst n
    exact ⟨Fintype.card Bool, Sharpness.intervalFrame, Sharpness.axis 0, Sharpness.axis_ne_zero 0,
      center_cut_volume_eq_one Sharpness.intervalFrame.polytope_isConvexBody (Sharpness.axis_ne_zero 0)⟩
  · cases n with
    | zero => omega
    | succ m =>
      have hm : 1 ≤ m := by omega
      exact ⟨Fintype.card (Sharpness.ContactIndex m), Sharpness.extremalFrame m hm, Sharpness.axis m,
        Sharpness.axis_ne_zero m, Sharpness.extremalBody_attainment hm⟩

theorem contactVolumeRatios_subset : contactVolumeRatios n ⊆ volumeRatios n := by
  rintro r ⟨N, F, v, hv, he⟩
  exact ⟨F.polytope, v, F.polytope_isConvexBody, hv, he⟩

theorem sharpRatio_mem_contactVolumeRatios (hn : 1 ≤ n) : sharpRatio n ∈ contactVolumeRatios n := by
  obtain ⟨N, F, v, hv, he⟩ := fixed_contact_attainment hn
  exact ⟨N, F, v, hv, (ratio_eq_of_attainment hn F.polytope_isConvexBody he).symm⟩

theorem contactVolumeRatios_isGreatest (hn : 1 ≤ n) : IsGreatest (contactVolumeRatios n) (sharpRatio n) :=
  ⟨sharpRatio_mem_contactVolumeRatios hn, fun r hr => volumeRatios_upper hn r (contactVolumeRatios_subset hr)⟩

theorem contactOptimalConstant_eq (hn : 1 ≤ n) : contactOptimalConstant n = sharpRatio n :=
  (contactVolumeRatios_isGreatest hn).csSup_eq

/-- Theorem 3.1 on actual convex bodies, central cuts and fixed-dimensional attainment. -/
theorem sharp_central_cut_contraction (hn : 1 ≤ n) {K : Set (V n)} (hK : IsConvexBody K)
    {v : V n} (hv : v ≠ 0) :
    IsConvexBody (K ∩ centralHalfspace (Khachiyan.johnCenter K) v) ∧
    maxEllipsoidVolume (K ∩ centralHalfspace (Khachiyan.johnCenter K) v) ≤
      ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume K ∧
    (∃ (L : Set (V n)) (u : V n), IsConvexBody L ∧ u ≠ 0 ∧
      maxEllipsoidVolume (L ∩ centralHalfspace (Khachiyan.johnCenter L) u) =
        ENNReal.ofReal (sharpRatio n)*maxEllipsoidVolume L) ∧
    optimalConstant n = sharpRatio n ∧ contactOptimalConstant n = sharpRatio n :=
  ⟨(sharp_center_cut_upper hn hK hv).1, (sharp_center_cut_upper hn hK hv).2,
    Sharpness.fixed_dimension_attainment hn, optimalConstant_eq hn, contactOptimalConstant_eq hn⟩

end SharpCut.Geometry
