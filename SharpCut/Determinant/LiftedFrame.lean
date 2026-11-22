import SharpCut.Determinant.FrameLogDet
import SharpCut.Certificate.AxialMoment

/-!
# Actual Euclidean lifted John frames

The constant coordinate is placed first. This is a fixed reindexing of the
manuscript's last-coordinate lift and preserves Gram determinants. The row
isometry and the column weights are derived from the defining John moments.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Determinant
variable {n N : ℕ}

def liftedVector (b : ℝ) (u : V n) : V (n+1) :=
  WithLp.toLp 2 (Fin.cases (Real.sqrt b) u)

def liftedMatrix (F : JohnFrame n N) : Matrix (Fin (n+1)) (Fin N) ℝ :=
  fun j i => Real.sqrt (F.weight i)*liftedVector (inverseDimension n) (F.contact i) j

def liftedMoment (F : JohnFrame n N) (f : Fin N → ℝ) : MatR (n+1) :=
  weightedGram (liftedMatrix F) f

theorem liftedMoment_entry (F : JohnFrame n N) (f : Fin N → ℝ) (j k : Fin (n+1)) :
    liftedMoment F f j k = ∑ i, F.weight i*f i*
      liftedVector (inverseDimension n) (F.contact i) j*
      liftedVector (inverseDimension n) (F.contact i) k := by
  unfold liftedMoment weightedGram
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, liftedMatrix]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = (Real.sqrt (F.weight i))^2*f i*
        liftedVector (inverseDimension n) (F.contact i) j*
        liftedVector (inverseDimension n) (F.contact i) k := by ring
    _ = _ := by rw [Real.sq_sqrt (F.weight_pos i).le]

theorem liftedVector_norm_sq (b : ℝ) (hb : 0 ≤ b) (u : V n) :
    ‖liftedVector b u‖^2 = b+‖u‖^2 := by
  have hu : (∑ i, u i*u i) = ‖u‖^2 := by
    rw [← real_inner_self_eq_norm_sq, Khachiyan.inner_eq_dotProduct]
    rfl
  rw [← real_inner_self_eq_norm_sq, Khachiyan.inner_eq_dotProduct]
  simp only [dotProduct, Fin.sum_univ_succ, liftedVector, WithLp.ofLp_toLp,
    Fin.cases_zero, Fin.cases_succ]
  rw [← pow_two, Real.sq_sqrt hb, hu]

theorem lifted_column_norm_sq (F : JohnFrame n N) (hn : 2 ≤ n) (i : Fin N) :
    ‖columnVector (liftedMatrix F) i‖^2 = F.weight i*(1+inverseDimension n) := by
  have he : columnVector (liftedMatrix F) i =
      (Real.sqrt (F.weight i)) • liftedVector (inverseDimension n) (F.contact i) := by
    ext j
    rfl
  rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    Real.sq_sqrt (F.weight_pos i).le,
    liftedVector_norm_sq _ (inverseDimension_bounds hn).1.le, F.contact_unit i, one_pow]
  ring

theorem lifted_gram_entry (F : JohnFrame n N) (j k : Fin (n+1)) :
    (liftedMatrix F*(liftedMatrix F)ᵀ) j k =
      ∑ i, F.weight i*liftedVector (inverseDimension n) (F.contact i) j*
        liftedVector (inverseDimension n) (F.contact i) k := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, liftedMatrix]
  apply Finset.sum_congr rfl
  intro i hi
  have hs := Real.sq_sqrt (F.weight_pos i).le
  calc
    _ = (Real.sqrt (F.weight i))^2 *
        liftedVector (inverseDimension n) (F.contact i) j *
        liftedVector (inverseDimension n) (F.contact i) k := by ring
    _ = _ := by rw [hs]

theorem lifted_row_isometry (F : JohnFrame n N) (hn : 2 ≤ n) :
    liftedMatrix F*(liftedMatrix F)ᵀ = 1 := by
  have hb := inverseDimension_bounds hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hbn : inverseDimension n*(n : ℝ) = 1 := by unfold inverseDimension; field_simp [hn0]
  have hf (j : Fin n) : (∑ i, F.weight i*F.contact i j) = 0 := by
    have h := congrArg (fun x : V n => x.ofLp j) F.first_moment
    simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero,
      Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using h
  have hs (j k : Fin n) : (∑ i, F.weight i*(F.contact i j*F.contact i k)) = (1 : MatR n) j k := by
    have h := congrArg (fun A : MatR n => A j k) F.second_moment
    simpa only [Matrix.sum_apply, Matrix.smul_apply, Khachiyan.outer_apply, smul_eq_mul] using h
  ext j k
  rw [lifted_gram_entry]
  refine Fin.cases ?_ (fun j => ?_) j
  · refine Fin.cases ?_ (fun k => ?_) k
    · simp only [liftedVector, Fin.cases_zero, Matrix.one_apply_eq]
      have he : (∑ i, F.weight i*Real.sqrt (inverseDimension n)*Real.sqrt (inverseDimension n)) =
          inverseDimension n*∑ i, F.weight i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = (Real.sqrt (inverseDimension n))^2 * F.weight i := by ring
          _ = _ := by rw [Real.sq_sqrt hb.1.le]
      rw [he, F.weight_sum, hbn]
    · change (∑ i, F.weight i*Real.sqrt (inverseDimension n)*F.contact i k) = 0
      calc
        _ = Real.sqrt (inverseDimension n)*(∑ i, F.weight i*F.contact i k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i hi; ring
        _ = 0 := by rw [hf, mul_zero]
  · refine Fin.cases ?_ (fun k => ?_) k
    · change (∑ i, F.weight i*F.contact i j*Real.sqrt (inverseDimension n)) = 0
      rw [← Finset.sum_mul, hf, zero_mul]
    · simp only [liftedVector, WithLp.ofLp_toLp, Fin.cases_succ,
        Matrix.one_apply, Fin.succ_inj]
      simpa only [mul_assoc, Matrix.one_apply] using hs j k

theorem lifted_logdet (F : JohnFrame n N) (hn : 2 ≤ n) (f : Fin N → ℝ) (hf : ∀ i, 0 < f i) :
    (1+inverseDimension n)*(∑ i, F.weight i*Real.log (f i)) ≤ Real.log (liftedMoment F f).det := by
  have h := finite_frame_logdet (liftedMatrix F) (lifted_row_isometry F hn) f hf
  simp only [lifted_column_norm_sq F hn] at h
  calc
    _ = ∑ i, F.weight i*(1+inverseDimension n)*Real.log (f i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi; ring
    _ ≤ _ := h

theorem liftedMoment_posDef (F : JohnFrame n N) (hn : 2 ≤ n) (f : Fin N → ℝ) (hf : ∀ i, 0 < f i) :
    (liftedMoment F f).PosDef := weightedGram_posDef _ (lifted_row_isometry F hn) f hf

end SharpCut.Determinant
