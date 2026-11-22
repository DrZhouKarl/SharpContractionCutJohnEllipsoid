import SharpCut.Geometry
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # A central halfspace bisects the ordinary Lebesgue volume of a Euclidean ball

The boundary plane is a proper linear kernel and has Haar measure zero.
Negation exchanges the two half-balls and preserves the actual Euclidean
Lebesgue volume. This statement is distinct from the maximum-ellipse volume.
-/

noncomputable section
open scoped RealInnerProductSpace ENNReal
open Set MeasureTheory
namespace SharpCut.Geometry
variable {n : ℕ}

def innerFunctional (v : V n) : V n →ₗ[ℝ] ℝ :=
  { toFun := fun x => ⟪v,x⟫
    map_add' := fun x y => inner_add_right v x y
    map_smul' := by intro a x; simp only [real_inner_smul_right,smul_eq_mul]; rfl }

theorem central_plane_volume_zero (v : V n) (hv : ‖v‖ = 1) : volume {x : V n | ⟪v,x⟫ = 0} = 0 := by
  have hproper : (innerFunctional v).ker ≠ ⊤ := by
    intro htop
    have hmem : v ∈ (innerFunctional v).ker := by rw [htop]; trivial
    change ⟪v,v⟫ = 0 at hmem
    rw [real_inner_self_eq_norm_sq,hv,one_pow] at hmem
    norm_num at hmem
  exact MeasureTheory.Measure.addHaar_submodule volume (innerFunctional v).ker hproper

def negativeHalfBall (v : V n) : Set (V n) := unitBall n ∩ {x | ⟪v,x⟫ ≤ 0}
def positiveHalfBall (v : V n) : Set (V n) := unitBall n ∩ {x | 0 ≤ ⟪v,x⟫}

theorem half_ball_measurable (v : V n) : MeasurableSet (negativeHalfBall v) ∧ MeasurableSet (positiveHalfBall v) := by
  have hb : MeasurableSet (unitBall n) := (isCompact_closedBall (0 : V n) 1).isClosed.measurableSet
  have hm : MeasurableSet {x : V n | ⟪v,x⟫ ≤ 0} := (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hp : MeasurableSet {x : V n | 0 ≤ ⟪v,x⟫} := (isClosed_le continuous_const (by fun_prop)).measurableSet
  exact ⟨hb.inter hm,hb.inter hp⟩

theorem half_ball_volume_equal (v : V n) : volume (positiveHalfBall v) = volume (negativeHalfBall v) := by
  have hpre : (fun x : V n => -x) ⁻¹' negativeHalfBall v = positiveHalfBall v := by
    ext x
    simp only [negativeHalfBall,positiveHalfBall,Set.mem_preimage,Set.mem_inter_iff,Set.mem_setOf_eq,
      Khachiyan.mem_unitBall,norm_neg,inner_neg_right,neg_nonpos]
  have h := (LinearIsometryEquiv.neg ℝ (E := V n)).measurePreserving.measure_preimage
    (half_ball_measurable v).1.nullMeasurableSet
  change volume ((fun x : V n => -x) ⁻¹' negativeHalfBall v) = volume (negativeHalfBall v) at h
  rwa [hpre] at h

theorem unit_ball_half_volume (v : V n) (hv : ‖v‖ = 1) :
    volume (unitBall n ∩ centralHalfspace 0 v) = ENNReal.ofReal (1/2 : ℝ)*volume (unitBall n) := by
  have hunion : negativeHalfBall v ∪ positiveHalfBall v = unitBall n := by
    ext x
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      rcases le_total ⟪v,x⟫ 0 with hm | hp
      · exact Or.inl ⟨hx,hm⟩
      · exact Or.inr ⟨hx,hp⟩
  have hnull : volume (negativeHalfBall v ∩ positiveHalfBall v) = 0 := by
    apply le_antisymm
    · calc
        _ ≤ volume {x : V n | ⟪v,x⟫ = 0} := measure_mono (fun x hx => le_antisymm hx.1.2 hx.2.2)
        _ = 0 := central_plane_volume_zero v hv
    · exact bot_le
  have he := measure_union_add_inter (μ := volume) (negativeHalfBall v) (half_ball_measurable v).2
  rw [hunion,hnull,half_ball_volume_equal,add_zero] at he
  have hbfin : volume (unitBall n) ≠ ∞ := (isCompact_closedBall (0 : V n) 1).measure_lt_top.ne
  have hmfin : volume (negativeHalfBall v) ≠ ∞ := ne_of_lt ((measure_mono Set.inter_subset_left).trans_lt
    (isCompact_closedBall (0 : V n) 1).measure_lt_top)
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add hmfin hmfin] at hr
  have heReal : (volume (negativeHalfBall v)).toReal = (1/2 : ℝ)*(volume (unitBall n)).toReal := by linarith only [hr]
  have h := congrArg ENNReal.ofReal heReal
  rw [ENNReal.ofReal_toReal hmfin,ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2),ENNReal.ofReal_toReal hbfin] at h
  simpa only [negativeHalfBall,centralHalfspace,sub_zero] using h

end SharpCut.Geometry
