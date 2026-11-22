import SharpCut.Equality.TransverseFamily
import SharpCut.Geometry.HeadTail

/-! # Constructive regular-simplex John frames in every positive dimension

The interval is the base case. The next dimension embeds the old contacts
isometrically into the transverse hyperplane and adds the pole/latitude
frame. Only defining John conditions enter the construction.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Simplex
open Certificate Geometry Sharpness Equality
variable {n N : ℕ}

@[simp] theorem padTail_add (x y : V n) : padTail (x+y) = padTail x+padTail y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem padTail_smul (a : ℝ) (x : V n) : padTail (a • x) = a • padTail x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem padTail_zero_vector : padTail (0 : V n) = 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem padTail_sum {ι : Type*} (s : Finset ι) (x : ι → V n) :
    padTail (∑ i ∈ s, x i) = ∑ i ∈ s, padTail (x i) := by
  ext k
  refine Fin.cases ?_ (fun j => ?_) k <;>
    simp [WithLp.ofLp_sum,Finset.sum_apply]

theorem padTail_axis_inner (x : V n) : ⟪axis n,padTail x⟫ = 0 := by
  rw [axis,EuclideanSpace.inner_single_left]
  simp

theorem embedded_first_moment (F : JohnFrame n N) : (∑ i, F.weight i • padTail (F.contact i)) = 0 := by
  calc
    _ = ∑ i, padTail (F.weight i • F.contact i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (padTail_smul _ _).symm
    _ = padTail (∑ i, F.weight i • F.contact i) := (padTail_sum Finset.univ _).symm
    _ = 0 := by rw [F.first_moment,padTail_zero_vector]

theorem embedded_second_moment (F : JohnFrame n N) :
    (∑ i, F.weight i • outer (padTail (F.contact i))) = projector (axis n) := by
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  · simp [Matrix.sum_apply,Matrix.smul_apply,Khachiyan.outer_apply,projector,Matrix.one_apply]
  · simp [Matrix.sum_apply,Matrix.smul_apply,Khachiyan.outer_apply,projector,Matrix.one_apply,eq_comm]
  · simp [Matrix.sum_apply,Matrix.smul_apply,Khachiyan.outer_apply,projector,Matrix.one_apply,eq_comm]
  · have h := congrArg (fun A : MatR n => A a b) F.second_moment
    simpa only [Matrix.sum_apply,Matrix.smul_apply,Khachiyan.outer_apply,padTail_succ,
      projector,Matrix.sub_apply,Matrix.one_apply,axis_succ,zero_mul,sub_zero,Fin.succ_inj] using h

def liftFrame (F : JohnFrame n N) (hn : 1 ≤ n) : JohnFrame (n+1) (N+1) :=
  frameFromTransverse (by omega) (axis n) (axis_norm n) (fun i => padTail (F.contact i)) F.weight
    (fun i => by rw [padTail_norm]; exact F.contact_unit i) F.weight_pos
    (fun i => padTail_axis_inner _) (embedded_first_moment F) (embedded_second_moment F)

def baseContact : Fin 2 → V 1 := ![-axis 0,axis 0]

theorem base_unit (i : Fin 2) : ‖baseContact i‖ = 1 := by fin_cases i <;> simp [baseContact]
theorem base_first : (∑ i : Fin 2, (1/2 : ℝ) • baseContact i) = 0 := by
  simp [Fin.sum_univ_two,baseContact,smul_neg]
theorem base_second : (∑ i : Fin 2, (1/2 : ℝ) • outer (baseContact i)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Fin.sum_univ_two,baseContact,Khachiyan.outer_apply]

def baseFrame : JohnFrame 1 2 :=
  { contact := baseContact
    weight := fun _ => 1/2
    contact_unit := base_unit
    weight_pos := fun _ => by norm_num
    first_moment := base_first
    second_moment := base_second }

def regularFrame : (m : ℕ) → JohnFrame (m+1) (m+2)
  | 0 => baseFrame
  | m+1 => liftFrame (regularFrame m) (by omega)

def johnWeight (n : ℕ) : ℝ := (n : ℝ)/((n : ℝ)+1)

theorem johnWeight_pos (hn : 1 ≤ n) : 0 < johnWeight n := by
  unfold johnWeight
  have hp : 0 < (n : ℝ) := by exact_mod_cast hn
  positivity

end SharpCut.Simplex
