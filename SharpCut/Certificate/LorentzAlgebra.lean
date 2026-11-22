import Lean
import Init.Grind.Ordered.Field

/-!
# Algebra of the Lorentz directions

The scalar norm identity (3.8) and the model matching in Section 3.3.
Actual Euclidean vectors and finite-frame constraints remain separate targets.
-/

namespace SharpCut.Certificate
open Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast
variable {R : Type u} [Field R] [LE R] [LT R]
  [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

theorem lorentz_norm_numerator (a s : R) :
    (s-a)^2 + (1-a^2)*(1-s^2) = (1-a*s)^2 := by
  grind

theorem lorentz_unit_square (a s : R) (h : 1-a*s ≠ 0) :
    ((s-a)^2 + (1-a^2)*(1-s^2))/(1-a*s)^2 = 1 := by
  rw [lorentz_norm_numerator]
  grind

theorem lorentz_pole_fixed (a : R) (h : 1+a ≠ 0) :
    (-1-a)/(1+a) = -1 := by
  grind

theorem lorentz_latitude_matching (b : R)
    (hd : 2-b ≠ 0) (hb1 : 1-b ≠ 0) (hbp : 2+b ≠ 0) :
    (b-b/(2-b))/(1-b/(2-b)*b) = b/(2+b) := by
  have hfact : 1-b/(2-b)*b = (1-b)*(2+b)/(2-b) := by grind
  rw [hfact]
  simp only [Field.div_eq_mul_inv, Field.inv_mul, Field.inv_inv]
  grind

theorem lorentz_parameter_square (b : R) (h : 2-b ≠ 0) :
    1-(b/(2-b))^2 = 4*(1-b)/(2-b)^2 := by
  grind

theorem transverse_model_matching (b : R) :
    1-(1+b)/2*b = (1-b)*(1+b/2) := by
  grind

end SharpCut.Certificate
