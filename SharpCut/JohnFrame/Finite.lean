import SharpCut.JohnFrame

/-! # Proven finite-index reindexing of John contact data -/

noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace SharpCut.JohnFrame
variable {n : ℕ} {ι : Type*} [Fintype ι]

def ofFinite (u : ι → V n) (w : ι → ℝ) (hu : ∀ i, ‖u i‖ = 1) (hw : ∀ i, 0 < w i)
    (hfirst : ∑ i, w i • u i = 0) (hsecond : ∑ i, w i • outer (u i) = 1) :
    JohnFrame n (Fintype.card ι) :=
  let e := (Fintype.equivFin ι).symm
  { contact := fun j => u (e j)
    weight := fun j => w (e j)
    contact_unit := fun j => hu (e j)
    weight_pos := fun j => hw (e j)
    first_moment := (e.sum_comp (fun i => w i • u i)).trans hfirst
    second_moment := (e.sum_comp (fun i => w i • outer (u i))).trans hsecond }

@[simp] theorem ofFinite_contact (u : ι → V n) (w : ι → ℝ) (hu : ∀ i, ‖u i‖ = 1)
    (hw : ∀ i, 0 < w i) (hfirst : ∑ i, w i • u i = 0) (hsecond : ∑ i, w i • outer (u i) = 1)
    (j : Fin (Fintype.card ι)) :
    (ofFinite u w hu hw hfirst hsecond).contact j = u ((Fintype.equivFin ι).symm j) := rfl

end SharpCut.JohnFrame
