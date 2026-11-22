import SharpCut
import Init.Grind.Ordered.Rat

open Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast Semiring.ofNat
variable {R : Type u} [Lean.Grind.Field R] [LE R] [LT R]
  [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

example (b s : R) (hb : 0 < b) (hbh : b ≤ 1/2) (hs : s ≤ 1) :
    2/3 ≤ 1-b/(2-b)*s :=
  SharpCut.Scalar.lorentz_denominator_lower b s hb hbh hs

example (b : R) (hb : 0 < b) (hbh : b ≤ 1/4) :
    1/12 ≤ (1+b)*(b^2+b+2)/(2*(2-b)*(1-b)*(2+b)*(3+b)) :=
  SharpCut.Scalar.gain_coefficient_lower b hb hbh

example (sigma z : R) (hs : 0 ≤ sigma) (hsh : sigma ≤ 3/4)
    (hz : 0 ≤ z) (hzh : z ≤ sigma*(1+sigma)) :
    72*sigma*(1+sigma) ≤
      72*sigma*(1+sigma)+(171/4-53/4*sigma+75*sigma^2)*z+(-333/4+75*sigma)*z^2 :=
  SharpCut.Determinant.dimension_three_polynomial_lower sigma z hs hsh hz hzh

example (sigma z r omega value : R)
    (hs : 0 ≤ sigma) (hsh : sigma ≤ 3/4)
    (hz : 0 ≤ z) (hzh : z ≤ sigma*(1+sigma))
    (hg : (2/3-sigma)*r+omega ≤ 5*sigma/12*((2/3)^2-2/3*sigma+(z-sigma)/4))
    (hv : ((1+sigma)*(1+4*sigma)-z)*r-4*(1+sigma)*omega ≤
      (5/8-5*sigma/6)/2*z*(1+sigma+z))
    (he : value = (1-5*sigma/12)*(1+sigma+(z-sigma)/4)-((1+sigma)*r-omega)) :
    1+2*sigma/11 ≤ value :=
  SharpCut.Determinant.dimension_three_scalar_elimination sigma z r omega value
    hs hsh hz hzh hg hv he

example : (21144601309 : Rat)/21319034625 < 9919/10000 :=
  SharpCut.Scalar.endpoint_strict_comparison

example (z b s : R) (hz : 1+z ≠ 0) (hb : 1-b*z ≠ 0)
    (hs : 1-z*s ≠ 0) (hbp : 1+b ≠ 0) :
    s/(1-z*s) -
      (b/(1-z*b)+(s-b)/(1-z*b)^2+
        ((-1)/(1+z)-b/(1-z*b)+(1+b)/(1-z*b)^2)/(1+b)^2*(s-b)^2) =
      z^2*(1+s)*(s-b)^2/((1+z)*(1-b*z)^2*(1-z*s)) :=
  SharpCut.Scalar.rational_hermite_remainder z b s hz hb hs hbp

run_cmd Lean.logInfo "SHARPCUT_STATEMENTS_PASS"

open scoped RealInnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator

/-- Independent contract for the complete finite normalized volume certificate. -/
example {n N : ℕ} {g q : Fin N → SharpCut.V n} {beta alpha : Fin N → ℝ}
    {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hA : A.PosDef)
    (hp : ∀ r, ⟪g r, c⟫+‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ ≤ beta r)
    (hc : ∀ r, ‖q r‖ ≤ alpha r)
    (hb : ∑ r, alpha r • g r = 0)
    (hn : ∑ r, alpha r * beta r = (n : ℝ))
    (hm : (SharpCut.Optimization.aggregate g q).PosDef) :
    (A*SharpCut.Optimization.aggregate g q).trace ≤ (n : ℝ) ∧
      A.det ≤ 1/(SharpCut.Optimization.aggregate g q).det :=
  SharpCut.Optimization.volume_certificate ⟨hA, hp⟩ ⟨hc, hb, hn, hm⟩

example {K : Set (SharpCut.V 1)} (hK : SharpCut.IsConvexBody K)
    {v : SharpCut.V 1} (hv : v ≠ 0) :
    SharpCut.maxEllipsoidVolume (K ∩ SharpCut.centralHalfspace (Khachiyan.johnCenter K) v) =
      ENNReal.ofReal (SharpCut.sharpRatio 1) * SharpCut.maxEllipsoidVolume K :=
  SharpCut.center_cut_volume_eq_one hK hv

example {n N : ℕ} (F : SharpCut.JohnFrame n N) :
    ∑ i, F.weight i = (n : ℝ) ∧ SharpCut.IsConvexBody F.polytope ∧
      SharpCut.IsJohnNormalized F.polytope :=
  ⟨F.weight_sum, F.polytope_isConvexBody, F.polytope_isJohnNormalized⟩

example : (2106*Real.log 13-468*Real.log 2-4160)/925 < (124 : ℝ)/125 :=
  SharpCut.Scalar.endpoint_logarithm_certificate

run_cmd Lean.logInfo "SHARPCUT_GEOMETRY_STATEMENTS_PASS"

/-- The scalar certificate uses exactly the original integral and all real b. -/
example {b : ℝ} (hb : 0 < b) (hbq : b ≤ 1/4) :
    1/125 < 1-(4*(1-b)^2*(2+b)*(3+b)/(b^2+b+2) *
      ∫ z in b/(2-b)..(1+b)/2, z^2/((1-z^2)*(1-b*z)^2)) ∧
    1/12 ≤ (1+b)*(b^2+b+2)/(2*(2-b)*(1-b)*(2+b)*(3+b)) :=
  SharpCut.Scalar.uniform_certificate hb hbq

example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    SharpCut.Certificate.frameDefect F v = 0 ↔
      ∀ i, ⟪F.contact i, v⟫ = -1 ∨ ⟪F.contact i, v⟫ = 1/(n : ℝ) :=
  SharpCut.Certificate.frameDefect_zero_iff F hn v hv

example {n : ℕ} (A : SharpCut.MatR n) :
    SharpCut.frobeniusNorm A = Real.sqrt (∑ i, ∑ j, A i j^2) := rfl

run_cmd Lean.logInfo "SHARPCUT_SCALAR_STATEMENTS_PASS"

/-- The actual John characterization, including every positive dimension and boundary contact. -/
example {n : ℕ} (hn : 1 ≤ n) {K : Set (SharpCut.V n)}
    (hK : SharpCut.IsConvexBody K) (hb : SharpCut.unitBall n ⊆ K) :
    SharpCut.IsJohnNormalized K ↔ ∃ N : ℕ, ∃ F : SharpCut.JohnFrame n N,
      F.Supports K ∧ ∀ i, F.contact i ∈ frontier K :=
  SharpCut.Geometry.john_contact_iff hn hK hb

run_cmd Lean.logInfo "SHARPCUT_JOHN_STATEMENTS_PASS"

example {n : ℕ} (hn : 1 ≤ n) {K : Set (SharpCut.V n)}
    (hK : SharpCut.IsConvexBody K) (h : SharpCut.IsJohnNormalized K)
    {N : ℕ} (F : SharpCut.JohnFrame n N) (hs : F.Supports K)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    SharpCut.IsConvexBody F.polytope ∧ K ⊆ F.polytope ∧ SharpCut.IsJohnNormalized F.polytope ∧
      SharpCut.maxEllipsoidVolume F.polytope = SharpCut.maxEllipsoidVolume K ∧
      SharpCut.maxEllipsoidVolume K = MeasureTheory.volume (SharpCut.unitBall n) ∧
      SharpCut.IsConvexBody (K ∩ SharpCut.centralHalfspace 0 v) ∧
      SharpCut.IsConvexBody (F.polytope ∩ SharpCut.centralHalfspace 0 v) ∧
      SharpCut.maxEllipsoidVolume (K ∩ SharpCut.centralHalfspace 0 v) ≤
        SharpCut.maxEllipsoidVolume (F.polytope ∩ SharpCut.centralHalfspace 0 v) :=
  SharpCut.Geometry.contact_reduction hn hK h F hs v hv

run_cmd Lean.logInfo "SHARPCUT_REDUCTION_STATEMENTS_PASS"

example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    SharpCut.Certificate.unrotatedQ F v =
      SharpCut.Certificate.certificateF F v*SharpCut.Certificate.certificateD v ∧
    0 < (SharpCut.Certificate.unrotatedQ F v).det ∧
    SharpCut.Optimization.DualFeasible (SharpCut.Certificate.cutNormals F v)
      (SharpCut.Certificate.cutOffsets N) (SharpCut.Certificate.cutAlpha F v)
      (SharpCut.Certificate.rotatedVectors F v
        (SharpCut.Certificate.polarRotation (SharpCut.Certificate.unrotatedQ F v))) :=
  ⟨SharpCut.Certificate.ordered_factorization F hn v hv,
    SharpCut.Certificate.unrotatedQ_det_pos F hn v hv,
    SharpCut.Certificate.explicit_dual_feasible F hn v hv⟩

example {n N : ℕ} (X : Matrix (Fin n) (Fin N) ℝ) (hX : X*X.transpose = 1)
    (f : Fin N → ℝ) (hf : ∀ i, 0 < f i) :
    (∑ i, ‖SharpCut.Determinant.columnVector X i‖^2*Real.log (f i)) ≤
      Real.log (SharpCut.Determinant.weightedGram X f).det :=
  SharpCut.Determinant.finite_frame_logdet X hX f hf

run_cmd Lean.logInfo "SHARPCUT_CERTIFICATE_FRAME_STATEMENTS_PASS"

/-- Lemma 8.2 with the original scalar sums and gain coefficient expanded. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 4 ≤ n)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    (1+1/(n : ℝ))*
      ((∑ i, F.weight i*Real.log
        ((1-((1+1/(n : ℝ))/2)*⟪F.contact i, v⟫)/
          (1-((1/(n : ℝ))/(2-1/(n : ℝ)))*⟪F.contact i, v⟫)))-
        (Real.log ((2-1/(n : ℝ))*(3+1/(n : ℝ))/4)/(1+1/(n : ℝ))+
          Real.log ((2-1/(n : ℝ))/2)/((1/(n : ℝ))*(1+1/(n : ℝ)))))+
      ((1+1/(n : ℝ))*((1/(n : ℝ))^2+1/(n : ℝ)+2)/
        (2*(2-1/(n : ℝ))*(1-1/(n : ℝ))*(2+1/(n : ℝ))*(3+1/(n : ℝ))))*
        (∑ i, F.weight i*((1+⟪F.contact i, v⟫)*(⟪F.contact i, v⟫-1/(n : ℝ))^2)/
          (1-((1/(n : ℝ))/(2-1/(n : ℝ)))*⟪F.contact i, v⟫)) ≤
      Real.log (SharpCut.Certificate.normalizedCertificate F v).det := by
  have hb := SharpCut.inverseDimension_bounds (show 2 ≤ n by omega)
  have h := SharpCut.Determinant.lifted_determinant_bound F hn v hv
  simp only [SharpCut.Determinant.modelLogSum] at h
  rw [(SharpCut.Determinant.heightFactor_endpoints _ hb.1 hb.2).1,
    (SharpCut.Determinant.heightFactor_endpoints _ hb.1 hb.2).2] at h
  simp only [SharpCut.Determinant.frameLogSum, SharpCut.Certificate.contactScalarFactor,
    SharpCut.Certificate.frameDefect, SharpCut.Certificate.defectTerm,
    SharpCut.Determinant.liftedGainCoefficient, SharpCut.Certificate.cutWeight,
    SharpCut.Certificate.boostParameter, SharpCut.Certificate.height,
    SharpCut.inverseDimension] at h
  exact h

run_cmd Lean.logInfo "SHARPCUT_LIFTED_BOUND_STATEMENTS_PASS"

/-- Exact integrated Hermite remainder, expanded independently of its named definitions. -/
example (b s : ℝ) (hb : 0 < b) (hbq : b ≤ 1/4) (hsm : -1 ≤ s) (hs : s ≤ 1) :
    let a := b/(2-b)
    let t := (1+b)/2
    let ℓ : ℝ → ℝ := fun r => Real.log ((1-t*r)/(1-a*r))
    let slope := a/(1-a*b)-t/(1-t*b)
    ℓ s-(ℓ b+slope*(s-b)+((ℓ (-1)-ℓ b+(1+b)*slope)/(1+b)^2)*(s-b)^2) =
      -(1+s)*(s-b)^2*∫ z in a..t, z^2/((1+z)*(1-b*z)^2*(1-z*s)) := by
  exact SharpCut.Scalar.logarithmic_hermite_remainder hb hbq hs

/-- Lemma 8.3 retains the original scalar integral and all John weights. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 4 ≤ n)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    let b : ℝ := 1/(n : ℝ)
    let a := b/(2-b)
    let t := (1+b)/2
    let L := ∑ i, F.weight i*Real.log ((1-t*⟪F.contact i, v⟫)/(1-a*⟪F.contact i, v⟫))
    let L0 := Real.log ((2-b)*(3+b)/4)/(1+b)+Real.log ((2-b)/2)/(b*(1+b))
    let χ := (∑ i, F.weight i*((1+⟪F.contact i, v⟫)*(⟪F.contact i, v⟫-b)^2)/(1-a*⟪F.contact i, v⟫));
    -(1-a)*(∫ z in a..t, z^2/((1-z^2)*(1-b*z)^2))*χ ≤ L-L0 := by
  have hb := SharpCut.inverseDimension_bounds (show 2 ≤ n by omega)
  have h := SharpCut.Determinant.interpolation_loss F hn v hv
  simp only [SharpCut.Determinant.modelLogSum] at h
  rw [(SharpCut.Determinant.heightFactor_endpoints _ hb.1 hb.2).1,
    (SharpCut.Determinant.heightFactor_endpoints _ hb.1 hb.2).2] at h
  exact h

example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 4 ≤ n)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    (1/1500 : ℝ)*(∑ i, F.weight i*((1+⟪F.contact i, v⟫)*
      (⟪F.contact i, v⟫-1/(n : ℝ))^2)/(1-((1/(n : ℝ))/(2-1/(n : ℝ)))*⟪F.contact i, v⟫)) ≤
        Real.log (SharpCut.Certificate.normalizedCertificate F v).det :=
  SharpCut.Determinant.higher_dimensional_uniform_logdet F hn v hv

run_cmd Lean.logInfo "SHARPCUT_HERMITE_STATEMENTS_PASS"

/-- Lemma 8.5: every intrinsic block, original contact formula, range and strict test. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    let b : ℝ := 1/(n : ℝ)
    let d := 2-b
    let a := b/d
    let t := (1+b)/2
    let s : Fin N → ℝ := fun i => ⟪F.contact i, v⟫
    let y : Fin N → SharpCut.V n := fun i => F.contact i-s i • v
    let χ := (∑ i, F.weight i*((1+s i)*(s i-b)^2)/(1-a*s i));
    let x := χ/(2*(2+b))
    let σ := 2*χ/(d*(2+b))
    let E := SharpCut.Certificate.transversePerturbation F v
    let j := SharpCut.Certificate.transverseCoupling F v
    let P := (1 : SharpCut.MatR n)-SharpCut.outer v
    let Fhat := SharpCut.Certificate.normalizedCertificate F v
    ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) Fhat v⟫ = 1-x ∧
    (∀ u w : SharpCut.V n, ⟪u, v⟫ = 0 → ⟪w, v⟫ = 0 →
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) Fhat w⟫ = ⟪u, w⟫+⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) E w⟫) ∧
    (∀ u : SharpCut.V n, ⟪u, v⟫ = 0 → ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) Fhat v⟫ = ⟪u, j⟫) ∧
    E.trace = σ ∧ E.IsHermitian ∧ x = d/4*σ ∧
    E = (-(1/d)) • (∑ i, (F.weight i/(1-a*s i)*(s i-b)) • SharpCut.outer (y i)) ∧
    j = (-Real.sqrt (1-b)/(b*Real.sqrt d)) • (∑ i, (F.weight i/(1-a*s i)*(s i-b)) • y i) ∧
    (0 ≤ σ ∧ σ ≤ 2*(1-b)/(d+b^2)) ∧ (0 ≤ χ ∧ χ ≤ 2) ∧
    (x • SharpCut.outer v-SharpCut.Certificate.cross v j-SharpCut.Certificate.cross j v+(t • P-E)).PosSemidef ∧
    (∀ u : SharpCut.V n, ⟪u, v⟫ = 0 → u ≠ 0 →
      -(1/2 : ℝ)*‖u‖^2 < ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) E u⟫ ∧
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) E u⟫ < t*‖u‖^2) :=
  SharpCut.Certificate.block_identities_and_constraints F hn v hv

/-- The actual Gram representation and arbitrary transverse coupling test. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n)
    (v u : SharpCut.V n) (hv : ‖v‖ = 1) (hu : ⟪u, v⟫ = 0) :
    (SharpCut.Certificate.contactGram F v).PosSemidef ∧
      ⟪SharpCut.Certificate.transverseCoupling F v, u⟫^2 ≤
        SharpCut.Certificate.axialDeficit F v*
          (SharpCut.Certificate.cutWeight n*‖u‖^2-
            ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (SharpCut.Certificate.transversePerturbation F v) u⟫) :=
  ⟨SharpCut.Certificate.contactGram_posSemidef F hn v hv,
    SharpCut.Certificate.transverse_coupling_bound F hn v u hv hu⟩

example {N : ℕ} (F : SharpCut.JohnFrame 2 N) (v : SharpCut.V 2) (hv : ‖v‖ = 1) :
    let χ := ∑ i, F.weight i*((1+⟪F.contact i, v⟫)*(⟪F.contact i, v⟫-1/2)^2)/(1-(1/3)*⟪F.contact i, v⟫);
    1+(11/60 : ℝ)*χ ≤ (SharpCut.Certificate.normalizedCertificate F v).det ∧
      (11/82 : ℝ)*χ ≤ Real.log (SharpCut.Certificate.normalizedCertificate F v).det := by
  have hd := SharpCut.Determinant.dimension_two_determinant F v hv
  have hl := SharpCut.Determinant.dimension_two_logdet F v hv
  norm_num [SharpCut.Certificate.frameDefect, SharpCut.Certificate.defectTerm,
    SharpCut.Certificate.height, SharpCut.Certificate.boostParameter, SharpCut.inverseDimension] at hd hl
  exact ⟨hd, hl⟩

run_cmd Lean.logInfo "SHARPCUT_BLOCK_DIMENSION_TWO_STATEMENTS_PASS"

/-- Lemma 8.6, including actual inverse positivity and both zero endpoints. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    let b : ℝ := 1/(n : ℝ)
    let d := 2-b
    let χ := SharpCut.Certificate.frameDefect F v
    let σ := 2*χ/(d*(2+b))
    let E := SharpCut.Certificate.transversePerturbation F v
    let j := SharpCut.Certificate.transverseCoupling F v
    let K : SharpCut.MatR n := 1+(2 : ℝ) • E
    let L := d*(1-b)/(d+b^2)-d*σ/2
    let A := (E^2*K⁻¹).trace
    0 ≤ L ∧ K.PosDef ∧ Matrix.toEuclideanCLM (𝕜 := ℝ) K v = v ∧
      Matrix.toEuclideanCLM (𝕜 := ℝ) E v = 0 ∧ 0 ≤ A ∧ A ≤ σ/2 ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) K⁻¹ j‖^2 ≤ L*(σ/2-A) :=
  ⟨SharpCut.Certificate.couplingL_nonneg F hn v hv,
    SharpCut.Certificate.couplingK_posDef F hn v hv,
    SharpCut.Certificate.couplingK_axis F hn v hv,
    SharpCut.Certificate.transversePerturbation_axis F hn v hv,
    SharpCut.Certificate.deformation_lower F hn v hv,
    (SharpCut.Certificate.direct_coupling_bound F hn v hv).1,
    (SharpCut.Certificate.direct_coupling_bound F hn v hv).2⟩

/-- Exact selected-test identities with the original single-square-root gamma. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) (Z : SharpCut.MatR n) (hZ : Z.IsHermitian)
    (hZv : Matrix.toEuclideanCLM (𝕜 := ℝ) Z v = 0) (q : SharpCut.V n) :
    let b : ℝ := 1/(n : ℝ)
    let d := 2-b
    let a := b/d
    let γ := Real.sqrt (d*(1-b))/(d+b^2)
    let s : Fin N → ℝ := fun i => ⟪F.contact i, v⟫
    let y : Fin N → SharpCut.V n := fun i => F.contact i-s i • v
    let ν : Fin N → ℝ := fun i => F.weight i/(1-a*s i)
    let E := SharpCut.Certificate.transversePerturbation F v
    let j := SharpCut.Certificate.transverseCoupling F v
    let K : SharpCut.MatR n := 1+(2 : ℝ) • E
    let σ := 2*SharpCut.Certificate.frameDefect F v/(d*(2+b))
    let L := d*(1-b)/(d+b^2)-d*σ/2
    let ℓ := (Z*E).trace+⟪q, j⟫
    let Q := (Z^2*K).trace+4*⟪q, Matrix.toEuclideanCLM (𝕜 := ℝ) Z j⟫+L*‖q‖^2
    let H : Fin N → SharpCut.V n := fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) Z (y i)+(γ*(s i+b)) • q
    ℓ = -(1/d)*(∑ i, ν i*(s i-b)*⟪y i, H i⟫) ∧
      (∑ i, ν i*(1-s i)*‖H i‖^2) = d/(2+b)*Q := by
  have h1 := SharpCut.Certificate.coupling_linear_identity F hn v hv Z q
  have h2 := SharpCut.Certificate.coupling_quadratic_identity F hn v hv Z hZ q
  rw [SharpCut.Certificate.coupling_quadratic_full F v Z hZ hZv q] at h2
  have hγ := SharpCut.Certificate.couplingGamma_explicit hn
  simp only [SharpCut.inverseDimension] at hγ
  dsimp only
  rw [← hγ]
  exact ⟨h1, h2⟩

example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    (SharpCut.Certificate.transverseSigma F v = 0 →
      SharpCut.Certificate.transversePerturbation F v = 0 ∧ SharpCut.Certificate.transverseCoupling F v = 0) ∧
    (SharpCut.Certificate.couplingL F v = 0 → SharpCut.Certificate.transverseCoupling F v = 0) :=
  ⟨SharpCut.Certificate.zero_sigma_transverse_blocks F hn v hv,
    SharpCut.Certificate.coupling_zero_of_L_zero F hn v hv⟩

run_cmd Lean.logInfo "SHARPCUT_DIRECT_COUPLING_STATEMENTS_PASS"

example (σ ell Q : ℝ) (hσ : 0 < σ) (hc : ell^2 ≤ σ/2*Q) :
    2*ell-Q ≤ 2*ell-2*ell^2/σ ∧
      2*ell-2*ell^2/σ = σ/2-(2/σ)*(ell-σ/2)^2 ∧
        σ/2-(2/σ)*(ell-σ/2)^2 ≤ σ/2 :=
  SharpCut.Certificate.variational_scalar_chain σ ell Q hσ hc

/-- Proposition 8.7 on arbitrary three-dimensional frames and unit axes. -/
example {N : ℕ} (F : SharpCut.JohnFrame 3 N) (v : SharpCut.V 3) (hv : ‖v‖ = 1) :
    let χ := ∑ i, F.weight i*((1+⟪F.contact i, v⟫)*(⟪F.contact i, v⟫-1/3)^2)/(1-(1/5)*⟪F.contact i, v⟫);
    1+(36/385 : ℝ)*χ ≤ (SharpCut.Certificate.normalizedCertificate F v).det ∧
      (36/457 : ℝ)*χ ≤ Real.log (SharpCut.Certificate.normalizedCertificate F v).det := by
  have hd := SharpCut.Determinant.dimension_three_determinant F v hv
  have hl := SharpCut.Determinant.dimension_three_logdet F v hv
  norm_num [SharpCut.Certificate.frameDefect, SharpCut.Certificate.defectTerm,
    SharpCut.Certificate.height, SharpCut.Certificate.boostParameter, SharpCut.inverseDimension] at hd hl
  exact ⟨hd, hl⟩

/-- Theorem 8.1 with the original defect, model determinant and every equality quantifier. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    let b : ℝ := 1/(n : ℝ)
    let d := 2-b
    let χ := (∑ i, F.weight i*((1+⟪F.contact i, v⟫)*(⟪F.contact i, v⟫-b)^2)/
      (1-(b/d)*⟪F.contact i, v⟫));
    let Fhat := SharpCut.Certificate.normalizedCertificate F v
    let F0 := SharpCut.Certificate.modelF0 v
    let Fsym := SharpCut.Certificate.certificateF F v
    (1/1500 : ℝ)*χ ≤ Real.log Fhat.det ∧ Real.log Fhat.det ≤ χ/(2*d) ∧
    F0.det = d^(n+1)/((2 : ℝ)^n*(1-b)) ∧ F0.det ≤ Fsym.det ∧
    (Fsym.det = F0.det ↔ ∀ i, ⟪F.contact i, v⟫ = -1 ∨ ⟪F.contact i, v⟫ = b) ∧
    ((∀ i, ⟪F.contact i, v⟫ = -1 ∨ ⟪F.contact i, v⟫ = b) → Fsym = F0 ∧ Fhat = 1) :=
  SharpCut.Determinant.quantitative_frame_determinant F hn v hv

/-- Theorem 3.2 on the constructed, generally nonsymmetric certificate Q. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    let b : ℝ := 1/(n : ℝ)
    let d := 2-b
    let χ := (∑ i, F.weight i*((1+⟪F.contact i, v⟫)*(⟪F.contact i, v⟫-b)^2)/
      (1-(b/d)*⟪F.contact i, v⟫));
    let Q := SharpCut.Certificate.unrotatedQ F v
    let R := SharpCut.sharpRatio n
    IsUnit Q ∧ 0 < Q.det ∧ (1/1500 : ℝ)*χ ≤ Real.log (R*Q.det) ∧
    Real.log (R*Q.det) ≤ χ/(2*d) ∧ 1/R ≤ Q.det ∧
    (Q.det = 1/R ↔ ∀ i, ⟪F.contact i, v⟫ = -1 ∨ ⟪F.contact i, v⟫ = b) ∧
    ((∀ i, ⟪F.contact i, v⟫ = -1 ∨ ⟪F.contact i, v⟫ = b) →
      Q = (2 : ℝ) • SharpCut.outer v+Real.sqrt (1-b) • ((1 : SharpCut.MatR n)-SharpCut.outer v)) :=
  SharpCut.Certificate.john_frame_certificate_bound F hn v hv

/-- Actual geometric upper bound: no supporting frame or candidate ellipsoid is supplied. -/
example {n : ℕ} [NeZero n] (hn : 1 ≤ n) {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K)
    {v : SharpCut.V n} (hv : v ≠ 0) :
    SharpCut.IsConvexBody (K ∩ {x | ⟪v, x-Khachiyan.johnCenter K⟫ ≤ 0}) ∧
      SharpCut.maxEllipsoidVolume (K ∩ {x | ⟪v, x-Khachiyan.johnCenter K⟫ ≤ 0}) ≤
        ENNReal.ofReal (SharpCut.sharpRatio n)*SharpCut.maxEllipsoidVolume K :=
  SharpCut.Geometry.sharp_center_cut_upper hn hK hv

example {n : ℕ} [NeZero n] (hn : 1 ≤ n) {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K)
    {v : SharpCut.V n} (hv : v ≠ 0) :
    (SharpCut.maxEllipsoidVolume (K ∩ {x | ⟪v, x-Khachiyan.johnCenter K⟫ ≤ 0})).toReal/
      (SharpCut.maxEllipsoidVolume K).toReal ≤ SharpCut.sharpRatio n :=
  SharpCut.Geometry.sharp_center_cut_ratio_upper hn hK hv

run_cmd Lean.logInfo "SHARPCUT_FULL_FRAME_GEOMETRIC_UPPER_STATEMENTS_PASS"

/-- The complete sharp theorem uses actual cuts and witnesses in each fixed positive dimension. -/
example {n : ℕ} [NeZero n] (hn : 1 ≤ n) {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K)
    {v : SharpCut.V n} (hv : v ≠ 0) :
    SharpCut.IsConvexBody (K ∩ {x | ⟪v, x-Khachiyan.johnCenter K⟫ ≤ 0}) ∧
    SharpCut.maxEllipsoidVolume (K ∩ {x | ⟪v, x-Khachiyan.johnCenter K⟫ ≤ 0}) ≤
      ENNReal.ofReal (SharpCut.sharpRatio n)*SharpCut.maxEllipsoidVolume K ∧
    (∃ (L : Set (SharpCut.V n)) (u : SharpCut.V n), SharpCut.IsConvexBody L ∧ u ≠ 0 ∧
      SharpCut.maxEllipsoidVolume (L ∩ {x | ⟪u, x-Khachiyan.johnCenter L⟫ ≤ 0}) =
        ENNReal.ofReal (SharpCut.sharpRatio n)*SharpCut.maxEllipsoidVolume L) ∧
    SharpCut.Geometry.optimalConstant n = SharpCut.sharpRatio n ∧
      SharpCut.Geometry.contactOptimalConstant n = SharpCut.sharpRatio n :=
  SharpCut.Geometry.sharp_central_cut_contraction hn hK hv

/-- Both genuine sets of real volume ratios have a greatest element, not only a limiting value. -/
example {n : ℕ} [NeZero n] (hn : 1 ≤ n) :
    IsGreatest (SharpCut.Geometry.volumeRatios n) (SharpCut.sharpRatio n) ∧
    IsGreatest (SharpCut.Geometry.contactVolumeRatios n) (SharpCut.sharpRatio n) ∧
    (SharpCut.Geometry.volumeRatios n).Nonempty ∧ BddAbove (SharpCut.Geometry.volumeRatios n) :=
  ⟨SharpCut.Geometry.volumeRatios_isGreatest hn, SharpCut.Geometry.contactVolumeRatios_isGreatest hn,
    (SharpCut.Geometry.volumeRatios_nonempty_bounded hn).1, (SharpCut.Geometry.volumeRatios_nonempty_bounded hn).2⟩

example {n : ℕ} (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    (SharpCut.Sharpness.modelShape v).PosDef ∧
      (SharpCut.Sharpness.modelShape v).det = SharpCut.sharpRatio n ∧
      (SharpCut.Sharpness.modelShape v)*SharpCut.Certificate.inverseModel v = 1 :=
  ⟨SharpCut.Sharpness.modelShape_posDef hn v hv, SharpCut.Sharpness.modelShape_det hn v hv,
    SharpCut.Sharpness.modelShape_mul_inverseModel hn v hv⟩

example {m : ℕ} (hm : 1 ≤ m) :
    SharpCut.IsConvexBody (SharpCut.Sharpness.extremalBody m hm) ∧
    SharpCut.IsFeasible (SharpCut.Sharpness.extremalBody m hm ∩
      {x | ⟪SharpCut.Sharpness.axis m, x⟫ ≤ 0})
        (SharpCut.Sharpness.modelCenter (SharpCut.Sharpness.axis m))
        (SharpCut.Sharpness.modelShape (SharpCut.Sharpness.axis m)) ∧
    SharpCut.maxEllipsoidVolume (SharpCut.Sharpness.extremalBody m hm ∩
      {x | ⟪SharpCut.Sharpness.axis m, x-Khachiyan.johnCenter (SharpCut.Sharpness.extremalBody m hm)⟫ ≤ 0}) =
        ENNReal.ofReal (SharpCut.sharpRatio (m+1))*SharpCut.maxEllipsoidVolume (SharpCut.Sharpness.extremalBody m hm) :=
  ⟨SharpCut.Sharpness.extremalBody_isConvexBody hm,
    (by simpa only [SharpCut.centralHalfspace, sub_zero] using SharpCut.Sharpness.extremal_candidate_feasible hm),
    SharpCut.Sharpness.extremalBody_attainment hm⟩

run_cmd Lean.logInfo "SHARPCUT_CORE_SHARP_STATEMENTS_PASS"

/-- Proposition 4.1: the actual explicit certificate and original cone pairings. -/
example {n N : ℕ} (hn : 2 ≤ n) {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K)
    (hJ : SharpCut.IsJohnNormalized K) (F : SharpCut.JohnFrame n N) (hs : F.Supports K)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hA : SharpCut.IsFeasible (K ∩ SharpCut.centralHalfspace 0 v) c A) :
    let M := SharpCut.Certificate.polarMatrix (SharpCut.Certificate.unrotatedQ F v)
    let g := SharpCut.Certificate.cutNormals F v
    let β := SharpCut.Certificate.cutOffsets N
    let α := SharpCut.Certificate.cutAlpha F v
    let q := SharpCut.Certificate.rotatedVectors F v (SharpCut.Certificate.polarRotation (SharpCut.Certificate.unrotatedQ F v))
    let C := (∑ r, (α r*(β r-⟪g r, c⟫)-⟪q r, Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫));
    let Y := CFC.sqrt M*A*CFC.sqrt M
    let D := Y.trace-(n : ℝ)-Real.log Y.det
    let Δ := Real.log (SharpCut.sharpRatio n*M.det)
    let ε := Real.log (SharpCut.sharpRatio n/A.det)
    ε = Δ+C+D ∧ 0 ≤ Δ ∧ 0 ≤ C ∧ 0 ≤ D ∧
      SharpCut.Certificate.frameDefect F v ≤ 1500*Δ ∧ SharpCut.Certificate.frameDefect F v ≤ 1500*ε :=
  SharpCut.Gap.exact_volume_deficit hn hK hJ F hs v hv hA

example {n : ℕ} [NeZero n] (hn : 2 ≤ n) {K : Set (SharpCut.V n)}
    {c v a : SharpCut.V n} {S A : SharpCut.MatR n} (hmax : SharpCut.IsMaxDet K c S)
    (hcut : SharpCut.IsMaxDet (K ∩ SharpCut.centralHalfspace c v) a A) :
    Real.log (SharpCut.sharpRatio n/(Khachiyan.affineShape (S⁻¹*A)).det) =
      Real.log (SharpCut.sharpRatio n*(SharpCut.maxEllipsoidVolume K).toReal/
        (SharpCut.maxEllipsoidVolume (K ∩ SharpCut.centralHalfspace c v)).toReal) :=
  SharpCut.Gap.affine_optimal_volume_deficit hn hmax hcut

example {n : ℕ} (A M : SharpCut.MatR n) (hA : A.PosDef) (hM : M.PosDef) :
    SharpCut.Optimization.pairDivergence A M = 0 ↔ A = M⁻¹ :=
  SharpCut.Gap.pairDivergence_zero_iff A M hA hM

/-- Lemma 4.2: the gap and both matrix factors are actual normalized feasible data. -/
example {n N : ℕ} {g q : Fin N → SharpCut.V n} {β α : Fin N → ℝ} {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hp : SharpCut.Optimization.PrimalFeasible g β c A) (hd : SharpCut.Optimization.DualFeasible g β α q)
    (hsmall : -Real.log (SharpCut.Optimization.aggregate g q).det-Real.log A.det ≤ 1/4) :
    SharpCut.frobeniusNorm (CFC.sqrt (SharpCut.Optimization.aggregate g q)*A*
      CFC.sqrt (SharpCut.Optimization.aggregate g q)-1) ≤
        2*Real.sqrt (-Real.log (SharpCut.Optimization.aggregate g q).det-Real.log A.det) :=
  SharpCut.Gap.matrix_matching hp hd hsmall

example (t : ℝ) (ht : 0 < t) : (t-1)^2/(2*max 1 t) ≤ t-1-Real.log t :=
  SharpCut.Gap.scalarDivergence_coercive ht

/-- Theorem 5.1 retains the actual candidate inclusion and every supporting frame. -/
example {n : ℕ} [NeZero n] (hn : 2 ≤ n) {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K)
    (hJ : SharpCut.IsJohnNormalized K) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    let E := SharpCut.ellipsoid ((-1/2 : ℝ) • v)
      ((1/2 : ℝ) • SharpCut.outer v+(Real.sqrt (1-1/(n : ℝ)))⁻¹ • ((1 : SharpCut.MatR n)-SharpCut.outer v))
    let Z : Set (SharpCut.V n) := {-v} ∪ {u | ‖u‖ = 1 ∧ ⟪u, v⟫ = 1/(n : ℝ)}
    (SharpCut.maxEllipsoidVolume (K ∩ SharpCut.centralHalfspace 0 v) =
      ENNReal.ofReal (SharpCut.sharpRatio n)*SharpCut.maxEllipsoidVolume K ↔
      ∃ N : ℕ, ∃ F : SharpCut.JohnFrame n N, (∀ i, F.contact i ∈ Z) ∧
        convexHull ℝ (SharpCut.unitBall n ∪ E) ⊆ K ∧ K ⊆ F.polytope) ∧
    (SharpCut.maxEllipsoidVolume (K ∩ SharpCut.centralHalfspace 0 v) =
      ENNReal.ofReal (SharpCut.sharpRatio n)*SharpCut.maxEllipsoidVolume K →
        Khachiyan.johnEllipsoid (K ∩ SharpCut.centralHalfspace 0 v) = E) ∧
    (SharpCut.maxEllipsoidVolume (K ∩ SharpCut.centralHalfspace 0 v) =
      ENNReal.ofReal (SharpCut.sharpRatio n)*SharpCut.maxEllipsoidVolume K →
        ∀ N : ℕ, ∀ F : SharpCut.JohnFrame n N, F.Supports K → ∀ i, F.contact i ∈ Z) ∧
    (∀ N : ℕ, ∀ F : SharpCut.JohnFrame n N,
      SharpCut.maxEllipsoidVolume (F.polytope ∩ SharpCut.centralHalfspace 0 v) =
        ENNReal.ofReal (SharpCut.sharpRatio n)*SharpCut.maxEllipsoidVolume F.polytope ↔ ∀ i, F.contact i ∈ Z) :=
  SharpCut.Equality.equality_classification hn hK hJ v hv

/-- Proposition 5.2 uses arbitrary transverse contact data, not only the special witness. -/
example {n N : ℕ} (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) (w : Fin N → SharpCut.V n)
    (μ : Fin N → ℝ) (hw : ∀ i, ‖w i‖ = 1) (hμ : ∀ i, 0 < μ i) (hperp : ∀ i, ⟪v, w i⟫ = 0)
    (hfirst : ∑ i, μ i • w i = 0) (hsecond : ∑ i, μ i • SharpCut.outer (w i) = (1 : SharpCut.MatR n)-SharpCut.outer v) :
    ∃ F : SharpCut.JohnFrame n (N+1),
      F.contact = Fin.cases (-v) (fun i => (1/(n : ℝ)) • v+Real.sqrt (1-(1/(n : ℝ))^2) • w i) ∧
      F.weight = Fin.cases (1/(1+1/(n : ℝ))) (fun i => μ i/(1-(1/(n : ℝ))^2)) ∧
      ∀ j, F.contact j ∈ ({-v} ∪ {u | ‖u‖ = 1 ∧ ⟪u, v⟫ = 1/(n : ℝ)}) :=
  SharpCut.Equality.transverse_extremal_construction hn v hv w μ hw hμ hperp hfirst hsecond

example {n : ℕ} (α τ : ℝ) (q x : SharpCut.V n) :
    2*α*τ*(α*τ-⟪q, x⟫) = ‖α • x-τ • q‖^2+
      α^2*(τ^2-‖x‖^2)+τ^2*(α^2-‖q‖^2) := SharpCut.Gap.cone_sum_of_squares α τ q x

/-- Proposition 9.1 expands the filtered weighted direction residual and both positive conjugates. -/
example {n N : ℕ} {g q : Fin N → SharpCut.V n} {β α : Fin N → ℝ} {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hp : SharpCut.Optimization.PrimalFeasible g β c A) (hd : SharpCut.Optimization.DualFeasible g β α q)
    (hg : ∀ r, g r ≠ 0) {ε : ℝ}
    (hgap : -Real.log (SharpCut.Optimization.aggregate g q).det-Real.log A.det ≤ ε) (hε : ε ≤ 1/4) :
    let M := SharpCut.Optimization.aggregate g q
    let τ : Fin N → ℝ := fun r => β r-⟪g r, c⟫
    SharpCut.frobeniusNorm (CFC.sqrt M*A*CFC.sqrt M-1) ≤ 2*Real.sqrt ε ∧
    (∑ r ∈ Finset.univ.filter (fun r => 0 < α r),
      α r*τ r*‖(τ r)⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)-(α r)⁻¹ • q r‖^2) ≤ 2*ε ∧
    SharpCut.frobeniusNorm (CFC.sqrt A*M*CFC.sqrt A-1) ≤ 2*Real.sqrt ε :=
  SharpCut.Gap.quantitative_complementarity hp hd hg hgap hε

run_cmd Lean.logInfo "SHARPCUT_GAP_MATCHING_EQUALITY_STATEMENTS_PASS"

/-- SUP-01: actual positive-dimensional existence/uniqueness and Lebesgue volume. -/
example {n : ℕ} [NeZero n] {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K) :
    ∃! p : SharpCut.V n × SharpCut.MatR n, SharpCut.IsMaxDet K p.1 p.2 := Khachiyan.existsUnique_isMaxDet hK

example {n : ℕ} [NeZero n] (a : SharpCut.V n) (A : SharpCut.MatR n) (hA : A.PosDef) :
    MeasureTheory.volume (SharpCut.ellipsoid a A) = ENNReal.ofReal A.det*MeasureTheory.volume (SharpCut.unitBall n) ∧
      0 < MeasureTheory.volume (SharpCut.ellipsoid a A) ∧ MeasureTheory.volume (SharpCut.ellipsoid a A) < ⊤ :=
  ⟨Khachiyan.volume_ellipsoid_eq_det hA a, Khachiyan.volume_ellipsoid_pos hA, Khachiyan.volume_ellipsoid_lt_top a A⟩

example {n : ℕ} (c a : SharpCut.V n) (S A : SharpCut.MatR n) :
    Khachiyan.normalizePoint c S '' SharpCut.ellipsoid a A =
      SharpCut.ellipsoid (Khachiyan.normalizePoint c S a) (Khachiyan.affineShape (S⁻¹*A)) :=
  Khachiyan.normalize_ellipsoid c a S A

example {n : ℕ} (S : SharpCut.MatR n) (hS : S.PosDef) (c : SharpCut.V n) (K L : Set (SharpCut.V n)) :
    SharpCut.maxEllipsoidVolume (Khachiyan.normalizedBody K c S)/
      SharpCut.maxEllipsoidVolume (Khachiyan.normalizedBody L c S) =
        SharpCut.maxEllipsoidVolume K/SharpCut.maxEllipsoidVolume L :=
  Khachiyan.maxEllipsoidVolume_normalize_ratio hS c K L

/-- SUP-06: actual left polar factors of a generally nonsymmetric matrix. -/
example {n : ℕ} (Q : SharpCut.MatR n) (hQ : 0 < Q.det) :
    (SharpCut.Certificate.polarMatrix Q).PosDef ∧
    (SharpCut.Certificate.polarRotation Q).transpose*SharpCut.Certificate.polarRotation Q = 1 ∧
    SharpCut.Certificate.polarRotation Q*(SharpCut.Certificate.polarRotation Q).transpose = 1 ∧
    SharpCut.Certificate.polarRotation Q*Q.transpose = SharpCut.Certificate.polarMatrix Q ∧
    (SharpCut.Certificate.polarMatrix Q).det = Q.det :=
  ⟨SharpCut.Certificate.polarMatrix_posDef hQ, SharpCut.Certificate.polarRotation_right_orthogonal hQ,
    SharpCut.Certificate.polarRotation_left_orthogonal hQ, SharpCut.Certificate.polarRotation_aggregate hQ,
    SharpCut.Certificate.polarMatrix_det hQ⟩

/-- SUP-07: the generic normalized gap, cone zero set and the exact matrix zero set. -/
example {n N : ℕ} {g q : Fin N → SharpCut.V n} {β α : Fin N → ℝ} {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hp : SharpCut.Optimization.PrimalFeasible g β c A) (hd : SharpCut.Optimization.DualFeasible g β α q) :
    SharpCut.Optimization.dualityGap A (SharpCut.Optimization.aggregate g q) =
      SharpCut.Optimization.coneGap g β α q c A+SharpCut.Optimization.pairDivergence A (SharpCut.Optimization.aggregate g q) ∧
    (SharpCut.Optimization.coneGap g β α q c A = 0 ↔ ∀ r, SharpCut.Optimization.conePairing g β α q c A r = 0) ∧
    (SharpCut.Optimization.pairDivergence A (SharpCut.Optimization.aggregate g q) = 0 ↔
      A = (SharpCut.Optimization.aggregate g q)⁻¹) :=
  ⟨SharpCut.Optimization.normalized_pair_gap hp hd, SharpCut.Optimization.coneGap_zero_iff hp hd,
    SharpCut.Gap.pairDivergence_zero_iff A _ hp.1 hd.positive⟩

example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    SharpCut.Gap.geometricGap F v = 0 ↔ ∀ i, ⟪F.contact i, v⟫ = -1 ∨ ⟪F.contact i, v⟫ = 1/(n : ℝ) :=
  SharpCut.Gap.geometricGap_contacts_iff F hn v hv

/-- SUP-13: ordered factorization, strict PD factors and exact normalization. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    SharpCut.Certificate.unrotatedQ F v = SharpCut.Certificate.certificateF F v*SharpCut.Certificate.certificateD v ∧
    (SharpCut.Certificate.certificateF F v).PosDef ∧ (SharpCut.Certificate.certificateD v).PosDef ∧
    (SharpCut.Certificate.modelF0 v).PosDef ∧ (SharpCut.Certificate.normalizedCertificate F v).PosDef ∧
    (SharpCut.Certificate.normalizedCertificate F v).det = SharpCut.sharpRatio n*(SharpCut.Certificate.unrotatedQ F v).det :=
  ⟨SharpCut.Certificate.ordered_factorization F hn v hv, SharpCut.Certificate.certificateF_posDef F hn v hv,
    SharpCut.Certificate.certificateD_posDef hn v hv, SharpCut.Certificate.modelF0_posDef hn v,
    SharpCut.Certificate.normalizedCertificate_posDef F hn v hv, SharpCut.Certificate.normalizedCertificate_det F hn v hv⟩

run_cmd Lean.logInfo "SHARPCUT_SUPPLEMENTARY_FOUNDATIONS_STATEMENTS_PASS"

/-- Independent Lemma 9.2 contract: exact coefficients and genuine Euclidean set distance. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    let b : ℝ := 1/(n : ℝ)
    let M₀ : SharpCut.MatR n := (2 : ℝ) • SharpCut.outer v+Real.sqrt (1-b) • (1-SharpCut.outer v)
    let Z : Set (SharpCut.V n) := {-v} ∪ {u | ‖u‖ = 1 ∧ ⟪u,v⟫ = b}
    (SharpCut.frobeniusNorm (SharpCut.Certificate.unrotatedQ F v-M₀))^2 ≤
      (1-b)/(2-b)*SharpCut.Certificate.frameDefect F v ∧
    (SharpCut.frobeniusNorm (SharpCut.Certificate.normalizedCertificate F v-1))^2 ≤
      SharpCut.Certificate.frameDefect F v/(2-b) ∧
    (∑ i, F.weight i*(Metric.infDist (F.contact i) Z)^2) ≤
      (32/3 : ℝ)*SharpCut.Certificate.frameDefect F v := by
  simpa only [SharpCut.Certificate.inverseModel, SharpCut.Certificate.projector,
    SharpCut.inverseDimension, SharpCut.Equality.modelContactSet] using
      SharpCut.Stability.geometric_residual F hn v hv

/-- The exact residual norm checks the root and denominator domains against the paper. -/
example {n : ℕ} (hn : 2 ≤ n) (v u : SharpCut.V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    let b : ℝ := 1/(n : ℝ)
    let s : ℝ := ⟪u,v⟫
    let ξ : SharpCut.V n := (-(s-b)/((2-b)*(1-b/(2-b)*s))) •
      (((1-b)*(s+1)) • v+Real.sqrt (1-b) • (u-s • v))
    ‖ξ‖^2 = (1-b)/(2-b)*((1+s)*(s-b)^2/(1-b/(2-b)*s)) := by
  simpa only [SharpCut.Stability.contactResidual, SharpCut.Certificate.transverse,
    SharpCut.inverseDimension, SharpCut.Certificate.boostParameter] using
      SharpCut.Stability.contactResidual_norm_sq hn v u hv hu

/-- SUP-28: every supporting frame and feasible ellipsoid, with no small-deficit assumption. -/
example {n N : ℕ} (hn : 2 ≤ n) {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K)
    (hJ : SharpCut.IsJohnNormalized K) (F : SharpCut.JohnFrame n N) (hs : F.Supports K)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hA : SharpCut.IsFeasible (K ∩ SharpCut.centralHalfspace 0 v) c A) :
    SharpCut.Certificate.frameDefect F v ≤ 1500*Real.log (SharpCut.sharpRatio n/A.det) ∧
    (∑ i, F.weight i*(Metric.infDist (F.contact i) ({-v} ∪ {u | ‖u‖ = 1 ∧ ⟪u,v⟫ = 1/(n : ℝ)}))^2) ≤
      16000*Real.log (SharpCut.sharpRatio n/A.det) ∧
    (1/1000 : ℝ)*(SharpCut.frobeniusNorm (SharpCut.Certificate.normalizedCertificate F v-1))^2 ≤
      Real.log (SharpCut.Certificate.normalizedCertificate F v).det := by
  simpa only [SharpCut.Gap.volumeDeficit, SharpCut.Equality.modelContactSet, SharpCut.inverseDimension] using
    SharpCut.Stability.global_geometric_stability hn hK hJ F hs v hv hA

example {n N : ℕ} (F : SharpCut.JohnFrame n N) (a : Fin N → ℝ) :
    ‖∑ i, (F.weight i*a i) • F.contact i‖^2 ≤ ∑ i, F.weight i*(a i)^2 := F.weighted_bessel a

example {n : ℕ} (A X : SharpCut.MatR n) :
    SharpCut.frobeniusNorm (A*X) ≤ SharpCut.operatorNorm A*SharpCut.frobeniusNorm X ∧
    SharpCut.frobeniusNorm (X*A) ≤ SharpCut.frobeniusNorm X*SharpCut.operatorNorm A :=
  ⟨SharpCut.frobeniusNorm_mul_operator_left A X, SharpCut.frobeniusNorm_mul_operator_right X A⟩

run_cmd Lean.logInfo "SHARPCUT_GEOMETRIC_RESIDUAL_STATEMENTS_PASS"

/-- Independent Lemma 9.3 contract: sigma is the original explicit defect, n >= 2 and zero included. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1)
    (hsmall : 2*SharpCut.Certificate.frameDefect F v/((2-1/(n : ℝ))*(2+1/(n : ℝ))) ≤ 1/1000) :
    (2*SharpCut.Certificate.frameDefect F v/((2-1/(n : ℝ))*(2+1/(n : ℝ))))/16 ≤
      Real.log (SharpCut.Certificate.normalizedCertificate F v).det ∧
    SharpCut.Certificate.frameDefect F v/32 ≤
      (2*SharpCut.Certificate.frameDefect F v/((2-1/(n : ℝ))*(2+1/(n : ℝ))))/16 := by
  simpa only [SharpCut.Certificate.transverseSigma, SharpCut.inverseDimension] using
    SharpCut.Stability.local_coercivity F hn v hv hsmall

/-- Lemma 6.1: the precise 3/2000 threshold and geometric gap are retained. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    let b : ℝ := 1/(n : ℝ)
    let M₀ : SharpCut.MatR n := (2 : ℝ) • SharpCut.outer v+Real.sqrt (1-b) • (1-SharpCut.outer v)
    (SharpCut.frobeniusNorm (SharpCut.Certificate.unrotatedQ F v-M₀))^2 ≤
      (1-b)/(2-b)*SharpCut.Certificate.frameDefect F v ∧
    (∑ i, F.weight i*(Metric.infDist (F.contact i) ({-v} ∪ {u | ‖u‖ = 1 ∧ ⟪u,v⟫ = b}))^2) ≤
      (32/3 : ℝ)*SharpCut.Certificate.frameDefect F v ∧
    (SharpCut.Certificate.frameDefect F v ≤ 3/2000 →
      SharpCut.Certificate.frameDefect F v/32 ≤ SharpCut.Gap.geometricGap F v) := by
  simpa only [SharpCut.Certificate.inverseModel, SharpCut.Certificate.projector,
    SharpCut.inverseDimension, SharpCut.Equality.modelContactSet] using
      SharpCut.Stability.geometric_control F hn v hv

/-- Supporting three Theorem 6.2 estimates; shape and center are not claimed here. -/
example {n N : ℕ} (hn : 2 ≤ n) {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K)
    (hJ : SharpCut.IsJohnNormalized K) (F : SharpCut.JohnFrame n N) (hs : F.Supports K)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hA : SharpCut.IsFeasible (K ∩ SharpCut.centralHalfspace 0 v) c A)
    (hε : 0 ≤ Real.log (SharpCut.sharpRatio n/A.det)) (hsmall : Real.log (SharpCut.sharpRatio n/A.det) ≤ 1/1000000) :
    SharpCut.Certificate.frameDefect F v ≤ 32*Real.log (SharpCut.sharpRatio n/A.det) ∧
    SharpCut.frobeniusNorm (SharpCut.Certificate.unrotatedQ F v-SharpCut.Certificate.inverseModel v) ≤
      4*Real.sqrt (Real.log (SharpCut.sharpRatio n/A.det)) ∧
    (∑ i, F.weight i*(Metric.infDist (F.contact i) ({-v} ∪ {u | ‖u‖ = 1 ∧ ⟪u,v⟫ = 1/(n : ℝ)}))^2) ≤
      (1024/3 : ℝ)*Real.log (SharpCut.sharpRatio n/A.det) := by
  simpa only [SharpCut.Gap.volumeDeficit, SharpCut.Equality.modelContactSet, SharpCut.inverseDimension] using
    SharpCut.Stability.near_extremal_contact_stability hn hK hJ F hs v hv hA hε hsmall

example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1)
    (hsmall : SharpCut.Certificate.transverseSigma F v ≤ 1/1000) :
    (SharpCut.frobeniusNorm (SharpCut.Certificate.transversePerturbation F v))^2+
      (20/21 : ℝ)*‖SharpCut.Certificate.transverseCoupling F v‖^2 ≤ (21/40 : ℝ)*SharpCut.Certificate.transverseSigma F v ∧
    (SharpCut.frobeniusNorm (SharpCut.Certificate.normalizedCertificate F v-1))^2 ≤ (5/6 : ℝ)*SharpCut.Certificate.transverseSigma F v ∧
    SharpCut.operatorNorm (SharpCut.Certificate.normalizedCertificate F v-1) < 1/30 :=
  ⟨SharpCut.Stability.local_metric_norm_bound F hn v hv hsmall, SharpCut.Stability.local_full_frobenius_bound F hn v hv hsmall,
    SharpCut.Stability.local_operator_bound F hn v hv hsmall⟩

example (z : ℝ) (hz : -(1/30 : ℝ) ≤ z) : z-(15/29 : ℝ)*z^2 ≤ Real.log (1+z) :=
  SharpCut.Stability.logarithm_quadratic_lower z hz

run_cmd Lean.logInfo "SHARPCUT_LOCAL_GEOMETRIC_COERCIVITY_STATEMENTS_PASS"

/-- SUP-21 supporting identities: exact isotropic action and the factor-eight model mismatch. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (A : SharpCut.MatR n) :
    (∑ i, F.weight i*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖^2) = (SharpCut.frobeniusNorm A)^2 :=
  SharpCut.Stability.frame_action_norm_sq F A

example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    (∑ i, F.weight i*(‖Matrix.toEuclideanCLM (𝕜 := ℝ) (SharpCut.Sharpness.modelShape v) (F.contact i)‖-1-⟪F.contact i,v⟫/2)^2) ≤
      8*SharpCut.Certificate.frameDefect F v := SharpCut.Stability.weighted_model_mismatch_bound F hn v hv

/-- The exact center transfer depends only on actual feasibility and derived multipliers. -/
example {n N : ℕ} {K : Set (SharpCut.V n)} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (hs : F.Supports K)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hA : SharpCut.IsFeasible (K ∩ SharpCut.centralHalfspace 0 v) c A) :
    (∑ i, F.weight i*(1-⟪F.contact i,c⟫-‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖)) ≤
      4*SharpCut.Gap.frameConeGap F v c A ∧
    ‖c-(-1/2 : ℝ) • v‖ ≤ 4*SharpCut.Gap.frameConeGap F v c A+
      Real.sqrt (8*SharpCut.Certificate.frameDefect F v)+SharpCut.frobeniusNorm (A-SharpCut.Sharpness.modelShape v) :=
  ⟨SharpCut.Stability.weighted_contact_slack_bound F hn hs v hv hA, SharpCut.Stability.center_recovery_bound F hn hs v hv hA⟩

run_cmd Lean.logInfo "SHARPCUT_CENTER_SUPPORT_TRANSFER_STATEMENTS_PASS"

open Matrix

/-- Complete Theorem 6.2 contract: all five estimates and every exact constant. -/
example {n N : ℕ} (hn : 2 ≤ n) {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K)
    (hJ : SharpCut.IsJohnNormalized K) (F : SharpCut.JohnFrame n N) (hs : F.Supports K)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hA : SharpCut.IsFeasible (K ∩ SharpCut.centralHalfspace 0 v) c A)
    (hε : 0 ≤ Real.log (SharpCut.sharpRatio n/A.det)) (hsmall : Real.log (SharpCut.sharpRatio n/A.det) ≤ 1/1000000) :
    let b : ℝ := 1/(n : ℝ)
    let d := 2-b
    let a := b/d
    let t := (1+b)/2
    let s := fun i => ⟪F.contact i,v⟫
    let p := fun i => (1-a*s i)⁻¹ • ((s i-a) • v+Real.sqrt (1-a^2) • (F.contact i-s i • v))
    let Q : SharpCut.MatR n := (∑ i, (F.weight i*(1-t*s i)) • SharpCut.Certificate.cross (F.contact i) (p i))+t • SharpCut.outer v
    let χ : ℝ := ∑ i, F.weight i*((1+s i)*(s i-b)^2)/(1-a*s i)
    let M₀ : SharpCut.MatR n := (2 : ℝ) • SharpCut.outer v+Real.sqrt (1-b) • (1-SharpCut.outer v)
    let Astar : SharpCut.MatR n := (1/2 : ℝ) • SharpCut.outer v+(Real.sqrt (1-b))⁻¹ • (1-SharpCut.outer v)
    let ε := Real.log (SharpCut.sharpRatio n/A.det)
    χ ≤ 32*ε ∧ SharpCut.frobeniusNorm (Q-M₀) ≤ 4*Real.sqrt ε ∧
    SharpCut.frobeniusNorm (A-Astar) ≤ 30*Real.sqrt ε ∧
    ‖c-(-1/2 : ℝ) • v‖ ≤ 50*Real.sqrt ε ∧
    (∑ i, F.weight i*(Metric.infDist (F.contact i) ({-v} ∪ {u | ‖u‖ = 1 ∧ ⟪u,v⟫ = b}))^2) ≤ (1024/3 : ℝ)*ε := by
  simpa only [SharpCut.Certificate.unrotatedQ, SharpCut.Certificate.originalWeight,
    SharpCut.Certificate.lorentzDirection, SharpCut.Certificate.cutWeight, SharpCut.Certificate.boostParameter,
    SharpCut.Certificate.transverse, SharpCut.Certificate.frameDefect, SharpCut.Certificate.defectTerm,
    SharpCut.Certificate.height, SharpCut.Certificate.inverseModel, SharpCut.Certificate.projector,
    SharpCut.Sharpness.modelShape, SharpCut.Sharpness.modelCenter, SharpCut.Equality.modelContactSet,
    SharpCut.Gap.volumeDeficit, SharpCut.inverseDimension] using
      SharpCut.Stability.dimension_independent_stability hn hK hJ F hs v hv hA hε hsmall

/-- SUP-21: positive polar spectra, exact ordered Sylvester trace and inverse identities. -/
example {n : ℕ} (Q : SharpCut.MatR n) (hQ : 0 < Q.det) (M₀ : SharpCut.MatR n) :
    let M : SharpCut.MatR n := SharpCut.Certificate.polarMatrix Q
    let X : SharpCut.MatR n := M-M₀
    M*X+X*M₀ = Q*Qᵀ-M₀*M₀ ∧
    (Xᵀ*M*X).trace+(Xᵀ*X*M₀).trace = SharpCut.Stability.frobeniusPair X (Q*Qᵀ-M₀*M₀) ∧
    SharpCut.Stability.frobeniusPair X (Q*Qᵀ-M₀*M₀) = (Xᵀ*(Q*Qᵀ-M₀*M₀)).trace :=
  ⟨SharpCut.Stability.polar_sylvester_identity Q hQ M₀, SharpCut.Stability.polar_sylvester_trace_identity Q hQ M₀,
    SharpCut.Stability.frobeniusPair_trace _ _⟩

example {n : ℕ} (A B : SharpCut.MatR n) (hA : A.PosDef) (hB : B.PosDef) :
    A⁻¹-B⁻¹ = A⁻¹*(B-A)*B⁻¹ ∧
    A-B⁻¹ = (CFC.sqrt B)⁻¹*(SharpCut.Optimization.matchingMatrix A B-1)*(CFC.sqrt B)⁻¹ :=
  ⟨SharpCut.Stability.inverse_difference_ordered A B hA hB, SharpCut.Stability.matching_error_reconstruction A B hB⟩

example {n : ℕ} (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) (Q : SharpCut.MatR n) (hQ : 0 < Q.det)
    (hsmall : SharpCut.operatorNorm (Q-SharpCut.Certificate.inverseModel v) ≤ 1/250) (i : Fin n) :
    7/10 < (SharpCut.Certificate.polarMatrix_posDef hQ).isHermitian.eigenvalues i ∧
    (SharpCut.Certificate.polarMatrix_posDef hQ).isHermitian.eigenvalues i < 201/100 ∧
    7/10 < (SharpCut.Sharpness.inverseModel_posDef hn v).isHermitian.eigenvalues i :=
  ⟨(SharpCut.Stability.polar_eigenvalue_bounds hn v hv Q hQ hsmall i).1,
    (SharpCut.Stability.polar_eigenvalue_bounds hn v hv Q hQ hsmall i).2, SharpCut.Stability.model_eigenvalue_lower hn v hv i⟩

example {n N : ℕ} (hn : 2 ≤ n) {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K)
    (hJ : SharpCut.IsJohnNormalized K) (F : SharpCut.JohnFrame n N) (hs : F.Supports K)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hA : SharpCut.IsFeasible (K ∩ SharpCut.centralHalfspace 0 v) c A)
    (hε : 0 ≤ SharpCut.Gap.volumeDeficit n A) (hsmall : SharpCut.Gap.volumeDeficit n A ≤ 1/1000000) :
    SharpCut.frobeniusNorm (SharpCut.Certificate.polarMatrix (SharpCut.Certificate.unrotatedQ F v)-SharpCut.Certificate.inverseModel v) ≤
      (401/35 : ℝ)*Real.sqrt (SharpCut.Gap.volumeDeficit n A) ∧
    SharpCut.frobeniusNorm (A-SharpCut.Sharpness.modelShape v) ≤ (20/7+1200/49 : ℝ)*Real.sqrt (SharpCut.Gap.volumeDeficit n A) :=
  ⟨SharpCut.Stability.near_extremal_polar_coefficient hn hK hJ F hs v hv hA hε hsmall,
    SharpCut.Stability.near_extremal_shape_coefficient hn hK hJ F hs v hv hA hε hsmall⟩

run_cmd Lean.logInfo "SHARPCUT_FULL_STABILITY_STATEMENTS_PASS"

/-- Proposition 2.3: actual attained maxima of both finite logdet problems, all positive dimensions. -/
example {n N : ℕ} (hn : 1 ≤ n) (g : Fin N → SharpCut.V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hK : SharpCut.IsConvexBody {x | ∀ r, ⟪g r,x⟫ ≤ β r}) :
    (∃ c : SharpCut.V n, ∃ A : SharpCut.MatR n, ∃ α : Fin N → ℝ, ∃ q : Fin N → SharpCut.V n,
      SharpCut.IsMaxDet {x | ∀ r, ⟪g r,x⟫ ≤ β r} c A ∧
      (SharpCut.Optimization.PrimalFeasible g β c A ∧ ∀ c' A', SharpCut.Optimization.PrimalFeasible g β c' A' → Real.log A'.det ≤ Real.log A.det) ∧
      (SharpCut.Optimization.DualFeasible g β α q ∧ ∀ α' q', SharpCut.Optimization.DualFeasible g β α' q' →
        Real.log (SharpCut.Optimization.aggregate g q').det ≤ Real.log (SharpCut.Optimization.aggregate g q).det) ∧
      SharpCut.Optimization.aggregate g q = A⁻¹ ∧
      (∀ r, α r*(β r-⟪g r,c⟫)-⟪q r,Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ = 0) ∧
      Real.log A.det+Real.log (SharpCut.Optimization.aggregate g q).det = 0) ∧
    (∀ c A, SharpCut.IsMaxDet {x | ∀ r, ⟪g r,x⟫ ≤ β r} c A →
      ∃ α : Fin N → ℝ, ∃ q : Fin N → SharpCut.V n,
      (SharpCut.Optimization.DualFeasible g β α q ∧ ∀ α' q', SharpCut.Optimization.DualFeasible g β α' q' →
        Real.log (SharpCut.Optimization.aggregate g q').det ≤ Real.log (SharpCut.Optimization.aggregate g q).det) ∧
      SharpCut.Optimization.aggregate g q = A⁻¹ ∧
      (∀ r, α r*(β r-⟪g r,c⟫)-⟪q r,Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ = 0) ∧
      Real.log A.det+Real.log (SharpCut.Optimization.aggregate g q).det = 0) := by
  simpa only [SharpCut.Optimization.constraintPolytope, SharpCut.Optimization.PrimalOptimal,
    SharpCut.Optimization.DualOptimal, SharpCut.Optimization.conePairing, SharpCut.Optimization.coneHeight] using
      SharpCut.Optimization.exact_duality hn g β hg hK

/-- Full Proposition 2.4: optimality iff KKT, plus active supports and every recovered John moment. -/
example {n N : ℕ} (hn : 1 ≤ n) (g : Fin N → SharpCut.V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hK : SharpCut.IsConvexBody {x | ∀ r, ⟪g r,x⟫ ≤ β r})
    {c : SharpCut.V n} {A : SharpCut.MatR n} {α : Fin N → ℝ} {q : Fin N → SharpCut.V n}
    (hp : SharpCut.Optimization.PrimalFeasible g β c A) (hd : SharpCut.Optimization.DualFeasible g β α q) :
    let ell := fun r => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖
    let p := fun r => (ell r)⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)
    let μ := fun r => α r*ell r
    let po := SharpCut.Optimization.PrimalFeasible g β c A ∧ ∀ c' A', SharpCut.Optimization.PrimalFeasible g β c' A' → Real.log A'.det ≤ Real.log A.det
    let do' := SharpCut.Optimization.DualFeasible g β α q ∧ ∀ α' q', SharpCut.Optimization.DualFeasible g β α' q' →
      Real.log (SharpCut.Optimization.aggregate g q').det ≤ Real.log (SharpCut.Optimization.aggregate g q).det
    ((po ∧ do') ↔ SharpCut.Optimization.aggregate g q = A⁻¹ ∧
      ∀ r, α r*(β r-⟪g r,c⟫)-⟪q r,Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ = 0) ∧
    ((po ∧ do') → (∀ r, ‖p r‖ = 1 ∧ 0 ≤ μ r) ∧
      (∀ r, 0 < α r → β r-⟪g r,c⟫ = ell r ∧ q r = α r • p r) ∧
      (∑ r, μ r • p r) = 0 ∧ (∑ r, μ r • SharpCut.outer (p r)) = 1 ∧
      (∑ r, μ r) = (n : ℝ) ∧ (∀ r, μ r*(β r-⟪g r,c⟫-ell r) = 0)) := by
  simpa only [SharpCut.Optimization.constraintPolytope, SharpCut.Optimization.PrimalOptimal,
    SharpCut.Optimization.DualOptimal, SharpCut.Optimization.conePairing, SharpCut.Optimization.coneHeight,
    SharpCut.Optimization.facetDirection, SharpCut.Optimization.facetLength,
    SharpCut.Optimization.normalizedNormals, SharpCut.Optimization.normalizedOffsets, SharpCut.Optimization.recoveredWeight] using
      SharpCut.Optimization.kkt_optimality_and_contacts hn g β hg hK hp hd

/-- Positive Sylvester injectivity is proved, including nonsymmetric H. -/
example {n : ℕ} (A H : SharpCut.MatR n) (hA : A.PosDef) (hzero : A*H+H*A = 0) : H = 0 :=
  SharpCut.Optimization.positive_sylvester_zero A H hA hzero

example {n : ℕ} (hn : 1 ≤ n) (A H : SharpCut.MatR n) (hA : A.PosDef) (hH : H.IsHermitian) :
    (H*(A*H+H*A)).trace = 2*(A*H^2).trace ∧
    2*SharpCut.Optimization.spectralMinimum A hA hn*(SharpCut.frobeniusNorm H)^2 ≤ (H*(A*H+H*A)).trace :=
  SharpCut.Optimization.sylvester_trace_coercivity hn A H hA hH

/-- Optimal facet-contact data produce the ordered UNSYMMETRIZED aggregate A inverse. -/
example {n N : ℕ} {g : Fin N → SharpCut.V n} {β : Fin N → ℝ} {c : SharpCut.V n} {A : SharpCut.MatR n}
    (D : SharpCut.Optimization.FacetJohnData g β c A) (hA : A.PosDef) (hg : ∀ r, g r ≠ 0) :
    (∑ r, Matrix.vecMulVec (D.vector r).ofLp (g r).ofLp) = A⁻¹ :=
  SharpCut.Optimization.FacetJohnData.raw_aggregate D hA hg

run_cmd Lean.logInfo "SHARPCUT_EXACT_DUALITY_KKT_STATEMENTS_PASS"

/-- Lemma 10.2 on every actual m-by-m transverse test, with the exact trace-range coefficient. -/
example {m N : ℕ} (hm : 1 ≤ m) (F : SharpCut.JohnFrame (m+1) N) (v : SharpCut.V (m+1)) (hv : ‖v‖ = 1)
    (B : OrthonormalBasis (Fin (m+1)) ℝ (SharpCut.V (m+1))) (hB : B 0 = v)
    (Z : SharpCut.MatR m) (hZ : Z.IsHermitian) (q : SharpCut.V m) :
    let b : ℝ := 1/(m+1 : ℕ)
    let d := 2-b
    let σ := 2*SharpCut.Certificate.frameDefect F v/(d*(2+b))
    let τ := 2*(1-b)/(d+b^2)-σ
    let E := SharpCut.Geometry.tailBlock B (SharpCut.Certificate.transversePerturbation F v)
    let j := SharpCut.Geometry.tailCoordinates B (SharpCut.Certificate.transverseCoupling F v)
    ((Z*E).trace+⟪q,j⟫)^2 ≤ σ*((Z^2*(E+(1/2 : ℝ) • (1 : SharpCut.MatR m))).trace+
      2*⟪q,Matrix.toEuclideanCLM (𝕜 := ℝ) Z j⟫+(d/4*τ)*‖q‖^2) := by
  simpa only [SharpCut.Coupled.traceRemainder, SharpCut.Coupled.sigmaStar,
    SharpCut.Certificate.transverseSigma, SharpCut.inverseDimension] using
      SharpCut.Coupled.general_cauchy_transverse F hm v hv B hB Z hZ q

/-- The full weighted contact identity underlying (10.11), with gamma's original single-root formula. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1)
    (Z : SharpCut.MatR n) (q : SharpCut.V n) :
    let b : ℝ := 1/(n : ℝ)
    let d := 2-b
    let a := b/d
    let γ := Real.sqrt (d*(1-b))/(d+b^2)
    let s := fun i => ⟪F.contact i,v⟫
    let y := fun i => F.contact i-s i • v
    (Z*SharpCut.Certificate.transversePerturbation F v).trace+⟪q,SharpCut.Certificate.transverseCoupling F v⟫ =
      -(1/d)*∑ i, F.weight i/(1-a*s i)*(s i-b)*⟪y i,Matrix.toEuclideanCLM (𝕜 := ℝ) Z (y i)+(γ*(s i+b)) • q⟫ := by
  have h := SharpCut.Coupled.general_linear_contact_identity F hn v hv Z q
  simp only [SharpCut.Certificate.couplingLinearSum, SharpCut.Certificate.couplingTestVector,
    SharpCut.Certificate.couplingGamma_explicit hn, SharpCut.Certificate.transverse,
    SharpCut.Certificate.height, SharpCut.Certificate.boostParameter, SharpCut.inverseDimension] at h
  exact h

example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1)
    (Z : SharpCut.MatR n) (hZ : Z.IsHermitian) (q : SharpCut.V n) :
    (∑ i, SharpCut.Certificate.minusContactWeight F v i*‖SharpCut.Certificate.couplingTestVector F v Z q i‖^2) =
      (2*(2-SharpCut.inverseDimension n)/(2+SharpCut.inverseDimension n))*SharpCut.Coupled.forwardQuadratic F v Z q :=
  SharpCut.Coupled.general_quadratic_contact_identity F hn v hv Z hZ q

run_cmd Lean.logInfo "SHARPCUT_GENERAL_CAUCHY_STATEMENTS_PASS"

/-- Full Lemma 10.3, on every symmetric transverse matrix and Euclidean transverse vector. -/
example {m N : ℕ} (hm : 1 ≤ m) (F : SharpCut.JohnFrame (m+1) N) (v : SharpCut.V (m+1)) (hv : ‖v‖ = 1)
    (B : OrthonormalBasis (Fin (m+1)) ℝ (SharpCut.V (m+1))) (hB : B 0 = v)
    (Z : SharpCut.MatR m) (hZ : Z.IsHermitian) (q : SharpCut.V m) :
    let b : ℝ := 1/(m+1 : ℕ)
    let d := 2-b
    let h := d+b^2
    let σ := 2*SharpCut.Certificate.frameDefect F v/(d*(2+b))
    let τ := 2*(1-b)/h-σ
    let estar := 2*b/h
    let t := (1+b)/2
    let E := SharpCut.Geometry.tailBlock B (SharpCut.Certificate.transversePerturbation F v)
    let j := SharpCut.Geometry.tailCoordinates B (SharpCut.Certificate.transverseCoupling F v)
    ((Z*(estar • (1 : SharpCut.MatR m)-E)).trace+⟪q,j⟫)^2 ≤
      τ*((Z^2*(t • (1 : SharpCut.MatR m)-E)).trace+
        2*⟪q,Matrix.toEuclideanCLM (𝕜 := ℝ) Z j⟫+(d/4*σ)*‖q‖^2) := by
  simpa only [SharpCut.Coupled.endpointShift, SharpCut.Coupled.traceRemainder, SharpCut.Coupled.sigmaStar,
    SharpCut.Certificate.transverseSigma, SharpCut.Certificate.cutWeight, SharpCut.inverseDimension] using
      SharpCut.Coupled.complementary_cauchy_transverse F hm v hv B hB Z hZ q

/-- SUP-24: exact opposite-endpoint contact representation with the paper's gamma and scale. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1)
    (Z : SharpCut.MatR n) (q : SharpCut.V n) :
    let b : ℝ := 1/(n : ℝ)
    let d := 2-b
    let a := b/d
    let h := d+b^2
    let e := 2*b/h
    let cminus := (1-a*b)/h
    let γminus := Real.sqrt d/(Real.sqrt (1-b)*(2+b))
    let s := fun i => ⟪F.contact i,v⟫
    let y := fun i => F.contact i-s i • v
    (Z*(e • SharpCut.Certificate.projector v-SharpCut.Certificate.transversePerturbation F v)).trace+
      ⟪q,SharpCut.Certificate.transverseCoupling F v⟫ =
      cminus*∑ i, F.weight i/(1-a*s i)*(s i+b)*
        ⟪y i,Matrix.toEuclideanCLM (𝕜 := ℝ) Z (y i)-(γminus*(s i-b)) • q⟫ := by
  simpa only [SharpCut.Coupled.endpointShift, SharpCut.Coupled.complementaryScale, SharpCut.Coupled.complementaryLinearSum,
    SharpCut.Coupled.complementaryTestVector, SharpCut.Coupled.complementaryGamma, SharpCut.Certificate.height,
    SharpCut.Certificate.transverse, SharpCut.Certificate.boostParameter, SharpCut.inverseDimension] using
      SharpCut.Coupled.complementary_linear_contact_identity F hn v hv Z q

example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1)
    (Z : SharpCut.MatR n) (hZ : Z.IsHermitian) (q : SharpCut.V n) :
    (∑ i, SharpCut.Coupled.plusContactWeight F v i*‖SharpCut.Coupled.complementaryTestVector F v Z q i‖^2) =
      SharpCut.Coupled.complementaryFactor n*SharpCut.Coupled.complementaryQuadratic F v Z q ∧
    (SharpCut.Coupled.complementaryScale n)^2*SharpCut.Certificate.reverseDefect F v =
      SharpCut.Coupled.traceRemainder F v/SharpCut.Coupled.complementaryFactor n :=
  ⟨SharpCut.Coupled.complementary_quadratic_contact_identity F hn v hv Z hZ q,
    SharpCut.Coupled.complementary_reverse_coefficient F hn v hv⟩

/-- Both trace endpoints and the dimension identity are retained exactly. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    ((n : ℝ)-1)*SharpCut.Coupled.endpointShift n = SharpCut.Coupled.sigmaStar n ∧
    0 ≤ SharpCut.Coupled.traceRemainder F v ∧
    ‖SharpCut.Certificate.transverseCoupling F v‖^2 ≤ ((2-SharpCut.inverseDimension n)/4)*
      SharpCut.Certificate.transverseSigma F v*SharpCut.Coupled.traceRemainder F v ∧
    (SharpCut.Certificate.transverseSigma F v = 0 ∨ SharpCut.Coupled.traceRemainder F v = 0 →
      SharpCut.Certificate.transverseCoupling F v = 0) :=
  ⟨SharpCut.Coupled.endpointShift_dimension hn, SharpCut.Coupled.traceRemainder_nonneg F hn v hv,
    SharpCut.Coupled.coupling_endpoint_norm F hn v hv, SharpCut.Coupled.coupling_zero_endpoints F hn v hv⟩

run_cmd Lean.logInfo "SHARPCUT_COMPLEMENTARY_CAUCHY_STATEMENTS_PASS"

/-- Complete Lemma 10.4: both all-test equivalences on the actual m-dimensional transverse blocks. -/
example {m N : ℕ} (hm : 1 ≤ m) (F : SharpCut.JohnFrame (m+1) N) (v : SharpCut.V (m+1)) (hv : ‖v‖ = 1)
    (B : OrthonormalBasis (Fin (m+1)) ℝ (SharpCut.V (m+1))) (hB : B 0 = v)
    (hσ : 0 < SharpCut.Certificate.transverseSigma F v)
    (hσstar : SharpCut.Certificate.transverseSigma F v < SharpCut.Coupled.sigmaStar (m+1)) :
    let b : ℝ := 1/(m+1 : ℕ)
    let d := 2-b
    let σ := SharpCut.Certificate.transverseSigma F v
    let τ := 2*(1-b)/(d+b^2)-σ
    let η := d/4*τ
    let x := d/4*σ
    let t := (1+b)/2
    let e := 2*b/(d+b^2)
    let E := SharpCut.Geometry.tailBlock B (SharpCut.Certificate.transversePerturbation F v)
    let j := SharpCut.Geometry.tailCoordinates B (SharpCut.Certificate.transverseCoupling F v)
    let Rplus := E+(1/2 : ℝ) • (1 : SharpCut.MatR m)-(1/η) • SharpCut.outer j
    let Rminus := t • (1 : SharpCut.MatR m)-E-(1/x) • SharpCut.outer j
    ((∀ Z : SharpCut.MatR m, Z.IsHermitian → ∀ q : SharpCut.V m,
      ((Z*E).trace+⟪q,j⟫)^2 ≤ σ*((Z^2*(E+(1/2 : ℝ) • (1 : SharpCut.MatR m))).trace+
        2*⟪q,Matrix.toEuclideanCLM (𝕜 := ℝ) Z j⟫+η*‖q‖^2)) ↔ Rplus.PosDef ∧ Rplus⁻¹.trace ≤ 2*(m : ℝ)) ∧
    ((∀ Z : SharpCut.MatR m, Z.IsHermitian → ∀ q : SharpCut.V m,
      ((Z*(e • (1 : SharpCut.MatR m)-E)).trace+⟪q,j⟫)^2 ≤ τ*((Z^2*(t • (1 : SharpCut.MatR m)-E)).trace+
        2*⟪q,Matrix.toEuclideanCLM (𝕜 := ℝ) Z j⟫+x*‖q‖^2)) ↔ Rminus.PosDef ∧ Rminus⁻¹.trace ≤ (m : ℝ)/(t-e)) := by
  have h := SharpCut.Coupled.InverseTrace.inverse_trace_interpretation F hm v hv B hB hσ hσstar
  rw [SharpCut.Certificate.axialDeficit_sigma F (show 2 ≤ m+1 by omega) v] at h
  simpa only [SharpCut.Coupled.InverseTrace.AllCoupledTests, SharpCut.Coupled.InverseTrace.originalLinear,
    SharpCut.Coupled.InverseTrace.originalQuadratic, SharpCut.Coupled.InverseTrace.effectiveMatrix,
    SharpCut.Coupled.InverseTrace.transverseE, SharpCut.Coupled.InverseTrace.transverseJ,
    SharpCut.Coupled.InverseTrace.forwardEta, SharpCut.Coupled.traceRemainder, SharpCut.Coupled.sigmaStar,
    SharpCut.Coupled.endpointShift, SharpCut.Coupled.oppositeBeta, SharpCut.Certificate.cutWeight, SharpCut.inverseDimension] using h

/-- Independent generic inverse-trace contract: no John frame or effective PD assumption. -/
example {m : ℕ} (E : SharpCut.MatR m) (hE : E.IsHermitian) (j : SharpCut.V m) (β η σ : ℝ)
    (hβ : 0 < β) (hη : 0 < η) (hσ : 0 < σ) (htrace : E.trace = σ) :
    (∀ Z : SharpCut.MatR m, Z.IsHermitian → ∀ q : SharpCut.V m,
      ((Z*E).trace+⟪q,j⟫)^2 ≤ σ*((Z^2*(E+β • (1 : SharpCut.MatR m))).trace+
        2*⟪q,Matrix.toEuclideanCLM (𝕜 := ℝ) Z j⟫+η*‖q‖^2)) ↔
      (E+β • (1 : SharpCut.MatR m)-(1/η) • SharpCut.outer j).PosDef ∧
      (E+β • (1 : SharpCut.MatR m)-(1/η) • SharpCut.outer j)⁻¹.trace ≤ (m : ℝ)/β :=
  SharpCut.Coupled.InverseTrace.all_tests_inverse_trace_iff E hE j β η σ hβ hη hσ htrace

/-- Exact completed square and optimal test, all multiplication orders and domains retained. -/
example {m : ℕ} (E : SharpCut.MatR m) (j : SharpCut.V m) (β η : ℝ) (hη : 0 < η)
    (Z : SharpCut.MatR m) (hZ : Z.IsHermitian) (q : SharpCut.V m) :
    let R := E+β • (1 : SharpCut.MatR m)-(1/η) • SharpCut.outer j
    ((Z*E).trace+⟪q-(1/η) • Matrix.toEuclideanCLM (𝕜 := ℝ) Z j,j⟫) = (Z*(R-β • (1 : SharpCut.MatR m))).trace+⟪q,j⟫ ∧
    (Z^2*(E+β • (1 : SharpCut.MatR m))).trace+2*⟪q-(1/η) • Matrix.toEuclideanCLM (𝕜 := ℝ) Z j,Matrix.toEuclideanCLM (𝕜 := ℝ) Z j⟫+
      η*‖q-(1/η) • Matrix.toEuclideanCLM (𝕜 := ℝ) Z j‖^2 = (Z^2*R).trace+η*‖q‖^2 :=
  ⟨SharpCut.Coupled.InverseTrace.linear_completion E j β η Z q,
    SharpCut.Coupled.InverseTrace.quadratic_completion E j β η hη.ne' Z hZ q⟩

example {m : ℕ} (R : SharpCut.MatR m) (hR : R.PosDef) (j : SharpCut.V m) (β η : ℝ) (hη : 0 < η) :
    let S := ((R-β • (1 : SharpCut.MatR m))^2*R⁻¹).trace+‖j‖^2/η
    (1-β • R⁻¹).IsHermitian ∧
    ((1-β • R⁻¹)*(R-β • (1 : SharpCut.MatR m))).trace+⟪(1/η) • j,j⟫ = S ∧
    ((1-β • R⁻¹)^2*R).trace+η*‖(1/η) • j‖^2 = S :=
  SharpCut.Coupled.InverseTrace.inverse_trace_optimal_tests R hR j β η hη

run_cmd Lean.logInfo "SHARPCUT_INVERSE_TRACE_STATEMENTS_PASS"

/-- Proposition 10.1, for every actual common Euclidean contraction and positive symmetric part. -/
example {n : ℕ} (Q R : SharpCut.MatR n) (hQ : 0 < Q.det) (hR : SharpCut.operatorNorm R ≤ 1)
    (hN : ((1/2 : ℝ) • (R*Qᵀ+(R*Qᵀ)ᵀ)).PosDef) :
    ((1/2 : ℝ) • (R*Qᵀ+(R*Qᵀ)ᵀ)).det ≤ Q.det :=
  SharpCut.Optimization.common_contraction_det Q R hQ hR hN

example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    let Q := SharpCut.Certificate.unrotatedQ F v
    let U := SharpCut.Certificate.polarRotation Q
    (∀ R : SharpCut.MatR n, SharpCut.operatorNorm R ≤ 1 → ((1/2 : ℝ) • (R*Qᵀ+(R*Qᵀ)ᵀ)).PosDef →
      ((1/2 : ℝ) • (R*Qᵀ+(R*Qᵀ)ᵀ)).det ≤ Q.det) ∧
    SharpCut.operatorNorm U ≤ 1 ∧ ((1/2 : ℝ) • (U*Qᵀ+(U*Qᵀ)ᵀ)).PosDef ∧
    ((1/2 : ℝ) • (U*Qᵀ+(U*Qᵀ)ᵀ)).det = Q.det :=
  SharpCut.Optimization.common_contraction_optimal F hn v hv

/-- The independently displayed skew Gram determinant identity (10.4). -/
example {n : ℕ} (T : SharpCut.MatR n) (hT : Tᵀ = -T) :
    (1+T)ᵀ*(1+T) = 1+Tᵀ*T ∧ 1 ≤ ((1+T).det)^2 :=
  SharpCut.Optimization.skew_gram_identity T hT

/-- The order in (10.5) is the actual Loewner order, with PSD and determinant signatures. -/
example {n : ℕ} (R : SharpCut.MatR n) (hR : SharpCut.operatorNorm R ≤ 1) :
    (Rᵀ*R).PosSemidef ∧ (1-Rᵀ*R).PosSemidef ∧ 0 ≤ Rᵀ*R ∧ Rᵀ*R ≤ 1 ∧
    (Rᵀ*R).det ≤ 1 ∧ |R.det| ≤ 1 :=
  SharpCut.Optimization.contraction_gram_bounds R hR

example {n : ℕ} (A K : SharpCut.MatR n) (hA : A.PosDef) (hK : Kᵀ = -K) : A.det ≤ |(A+K).det| :=
  SharpCut.Optimization.positive_plus_skew_det A K hA hK

run_cmd Lean.logInfo "SHARPCUT_COMMON_POLAR_STATEMENTS_PASS"

open scoped ENNReal

/-- Complete Corollary 7.1: actual bodies, canonical exact centers and all-positive-dimension sharp potential. -/
example {n : ℕ} [NeZero n] (hn : 1 ≤ n) {K : ℕ → Set (SharpCut.V n)} (hK0 : SharpCut.IsConvexBody (K 0))
    {p : ℕ → SharpCut.V n} (hp : ∀ k, p k ≠ 0)
    (hstep : ∀ k, K (k+1) = K k ∩ {x | ⟪p k,x-Khachiyan.johnCenter (K k)⟫ ≤ 0}) (N : ℕ) :
    SharpCut.IsConvexBody (K N) ∧ 0 < SharpCut.maxEllipsoidVolume (K N) ∧ SharpCut.maxEllipsoidVolume (K N) < ∞ ∧
    SharpCut.maxEllipsoidVolume (K N) ≤ ENNReal.ofReal ((SharpCut.sharpRatio n)^N)*SharpCut.maxEllipsoidVolume (K 0) ∧
    (∀ outerCenter targetCenter : SharpCut.V n, ∀ R r : ℝ, 0 < r → K 0 ⊆ Metric.closedBall outerCenter R →
      Metric.closedBall targetCenter r ⊆ K N → (N : ℝ) ≤ (n : ℝ)*Real.log (R/r)/(-Real.log (SharpCut.sharpRatio n))) :=
  SharpCut.Applications.successive_exact_central_cuts hn hK0 hp hstep N

/-- The actual target-ball and outer-ball volume comparisons are separate checked statements. -/
example {n : ℕ} [NeZero n] (hn : 1 ≤ n) {K : ℕ → Set (SharpCut.V n)} (hK0 : SharpCut.IsConvexBody (K 0))
    {p : ℕ → SharpCut.V n} (hp : ∀ k, p k ≠ 0)
    (hstep : ∀ k, K (k+1) = K k ∩ SharpCut.centralHalfspace (Khachiyan.johnCenter (K k)) (p k))
    (N : ℕ) (outerCenter targetCenter : SharpCut.V n) (R r : ℝ) (hr : 0 < r)
    (houter : K 0 ⊆ Metric.closedBall outerCenter R) (htarget : Metric.closedBall targetCenter r ⊆ K N) :
    ENNReal.ofReal (r^n)*MeasureTheory.volume (SharpCut.unitBall n) ≤ SharpCut.maxEllipsoidVolume (K N) ∧
    SharpCut.maxEllipsoidVolume (K N) ≤ ENNReal.ofReal ((SharpCut.sharpRatio n)^N)*SharpCut.maxEllipsoidVolume (K 0) ∧
    ENNReal.ofReal ((SharpCut.sharpRatio n)^N)*SharpCut.maxEllipsoidVolume (K 0) ≤
      ENNReal.ofReal ((SharpCut.sharpRatio n)^N)*(ENNReal.ofReal (R^n)*MeasureTheory.volume (SharpCut.unitBall n)) :=
  SharpCut.Applications.retained_ball_volume_chain hn hK0 hp hstep N outerCenter targetCenter R r hr houter htarget

example {n : ℕ} [NeZero n] (hn : 1 ≤ n) {K : ℕ → Set (SharpCut.V n)} (hK0 : SharpCut.IsConvexBody (K 0))
    {p : ℕ → SharpCut.V n} (hp : ∀ k, p k ≠ 0)
    (hstep : ∀ k, K (k+1) = K k ∩ SharpCut.centralHalfspace (Khachiyan.johnCenter (K k)) (p k))
    (N : ℕ) (outerCenter targetCenter : SharpCut.V n) (R r : ℝ) (hr : 0 < r)
    (houter : K 0 ⊆ Metric.closedBall outerCenter R) (htarget : Metric.closedBall targetCenter r ⊆ K N) :
    (n : ℝ)*Real.log r ≤ (N : ℝ)*Real.log (SharpCut.sharpRatio n)+(n : ℝ)*Real.log R ∧
    (N : ℝ)*(-Real.log (SharpCut.sharpRatio n)) ≤ (n : ℝ)*Real.log (R/r) :=
  SharpCut.Applications.retained_ball_log_chain hn hK0 hp hstep N outerCenter targetCenter R r hr houter htarget

example {n : ℕ} (hn : 1 ≤ n) : 0 < SharpCut.sharpRatio n ∧ SharpCut.sharpRatio n < 1 ∧ 0 < -Real.log (SharpCut.sharpRatio n) :=
  ⟨SharpCut.sharpRatio_pos hn, SharpCut.Applications.sharpRatio_lt_one hn, SharpCut.Applications.sharpRatio_log_decrease_pos hn⟩

example {n : ℕ} (c : SharpCut.V n) (r : ℝ) (hr : 0 < r) :
    Khachiyan.ellipsoid c (r • (1 : SharpCut.MatR n)) = Metric.closedBall c r ∧
    MeasureTheory.volume (Metric.closedBall c r) = ENNReal.ofReal (r^n)*MeasureTheory.volume (SharpCut.unitBall n) :=
  ⟨SharpCut.Applications.scalar_ball_ellipsoid c r hr, SharpCut.Applications.ball_volume_eq c r hr⟩

run_cmd Lean.logInfo "SHARPCUT_ITERATION_STATEMENTS_PASS"

/-- SUP-17: exact original-to-transformed scalar integral, without a substituted hypothesis. -/
example (b : ℝ) (hb : 0 < b) (hbq : b ≤ 1/4) :
    (4*(1-b)^2*(2+b)*(3+b)/(b^2+b+2)) *
      (∫ z in b/(2-b)..(1+b)/2, z^2/((1-z^2)*(1-b*z)^2)) =
    (4*(2+b)*(3+b)/(b^2+b+2)) *
      (∫ w in (0 : ℝ)..(2+b)/(4+b), ((2*w+b*(1-w))/(2+b*(1-w)))^2/(1-w^2)) := by
  simpa only [SharpCut.Scalar.lossRatio, SharpCut.Scalar.scalarA, SharpCut.Scalar.scalarT, SharpCut.Scalar.originalIntegrand,
    SharpCut.Scalar.transformedRatio, SharpCut.Scalar.ratioPrefactor, SharpCut.Scalar.ratioEndpoint,
    SharpCut.Scalar.ratioIntegrand, SharpCut.Scalar.ratioFactor] using SharpCut.Scalar.lossRatio_eq_transformedRatio hb hbq

example (b₁ b₂ w : ℝ) (hb₁ : 0 ≤ b₁) (hb₁₂ : b₁ ≤ b₂) (hb₂ : b₂ ≤ 1/4) (hw : 0 ≤ w) (hwh : w ≤ 9/17) :
    SharpCut.Scalar.ratioPrefactor b₁ ≤ SharpCut.Scalar.ratioPrefactor b₂ ∧
    SharpCut.Scalar.ratioFactor b₁ w ≤ SharpCut.Scalar.ratioFactor b₂ w ∧
    SharpCut.Scalar.ratioEndpoint b₁ ≤ SharpCut.Scalar.ratioEndpoint b₂ ∧
    SharpCut.Scalar.transformedRatio b₁ ≤ SharpCut.Scalar.transformedRatio b₂ :=
  ⟨SharpCut.Scalar.ratioPrefactor_mono hb₁ hb₁₂ hb₂, SharpCut.Scalar.ratioFactor_mono hb₁ hb₁₂ hwh,
    SharpCut.Scalar.ratioEndpoint_mono hb₁ hb₁₂, SharpCut.Scalar.transformedRatio_mono hb₁ hb₁₂ hb₂⟩

example :
    (∫ w in (0 : ℝ)..9/17, (1+7*w)^2/((1-w^2)*(9-w)^2)) = 9/50*Real.log 13-1/25*Real.log 2-16/45 :=
  SharpCut.Scalar.endpointIntegral_eq

example : SharpCut.Scalar.lossRatio (1/4) = (2106*Real.log 13-468*Real.log 2-4160)/925 ∧
    SharpCut.Scalar.lossRatio (1/4) ≤ (21144601309 : ℝ)/21319034625 ∧
    (21144601309 : ℝ)/21319034625 < 9919/10000 ∧ (9919 : ℝ)/10000 < 124/125 :=
  SharpCut.Scalar.endpoint_full_certificate

example : Real.log 2 ≤ 2*((1/3 : ℝ)+1/81+1/1215)+1/6804 ∧
    2*((3/29 : ℝ)+(3/29)^3/3) ≤ Real.log (16/13) ∧
    2*((1/3 : ℝ)+1/81+1/1215)+1/6804 = 23581/34020 ∧ 2*((3/29 : ℝ)+(3/29)^3/3) = 5064/24389 :=
  SharpCut.Scalar.endpoint_record_logarithms

example (u : ℝ) (hu : 0 ≤ u) (hu3 : u ≤ 1/3) :
    1/(1-u^2) = 1+u^2+u^4+u^6/(1-u^2) ∧ 1/(1-u^2) ≤ 9/8 :=
  SharpCut.Scalar.endpoint_finite_identity u hu hu3

run_cmd Lean.logInfo "SHARPCUT_ENDPOINT_SUPPLEMENTARY_STATEMENTS_PASS"

/-- SUP-05: the exact homogeneous Lorentz block matrix and its Euclidean action (10.27). -/
example {n : ℕ} (v u : SharpCut.V n) :
    let b : ℝ := 1/(n : ℝ)
    let a := b/(2-b)
    let k := Real.sqrt (1-a^2)
    let P : SharpCut.MatR n := 1-SharpCut.outer v
    let L : SharpCut.MatR (n+1) := Matrix.of (Fin.cases
      (Fin.cases 1 (fun j => -a*v j))
      (fun i => Fin.cases (-a*v i) (fun j => (SharpCut.outer v+k • P) i j)))
    let s := ⟪u,v⟫
    Matrix.toEuclideanCLM (𝕜 := ℝ) L (WithLp.toLp 2 (Fin.cases (1 : ℝ) u.ofLp)) =
      WithLp.toLp 2 (Fin.cases (1-a*s) (((s-a) • v+k • (u-s • v)).ofLp)) := by
  simpa only [SharpCut.Certificate.homogeneousLorentzBlock, SharpCut.Certificate.homogeneousPoint,
    SharpCut.Certificate.boostParameter, SharpCut.Certificate.boostScale, SharpCut.Certificate.projector,
    SharpCut.Certificate.transverse, SharpCut.inverseDimension] using SharpCut.Certificate.homogeneous_lorentz_action v u

/-- The contact weights, denominator, unit directions and full zero-defect quantifier (3.5)-(3.11). -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    (∀ i, F.weight i/4 ≤ SharpCut.Certificate.originalWeight F v i ∧ 0 < SharpCut.Certificate.originalWeight F v i) ∧
    (∑ i, SharpCut.Certificate.originalWeight F v i) = (n : ℝ) ∧
    (∑ i, SharpCut.Certificate.originalWeight F v i • F.contact i)+SharpCut.Certificate.cutWeight n • v = 0 ∧
    (∀ i, 2/3 ≤ 1-SharpCut.Certificate.boostParameter n*⟪F.contact i,v⟫ ∧ ‖SharpCut.Certificate.lorentzDirection v (F.contact i)‖ = 1) ∧
    0 ≤ SharpCut.Certificate.frameDefect F v ∧
    (SharpCut.Certificate.frameDefect F v = 0 ↔ ∀ i, ⟪F.contact i,v⟫ = -1 ∨ ⟪F.contact i,v⟫ = 1/(n : ℝ)) := by
  refine ⟨SharpCut.Certificate.originalWeight_lower F v hn hv, SharpCut.Certificate.originalWeight_sum F v,
    SharpCut.Certificate.balanced_normals F v, ?_, SharpCut.Certificate.frameDefect_nonneg F hn v hv,
    SharpCut.Certificate.frameDefect_zero_iff F hn v hv⟩
  intro i
  exact ⟨SharpCut.certificate_denominator_lower hn (F.heights_bounds v hv i).2,
    SharpCut.Certificate.lorentzDirection_unit hn v (F.contact i) hv (F.contact_unit i)⟩

/-- The independently displayed model support-direction matching (3.9), including the pole. -/
example {n : ℕ} (hn : 2 ≤ n) (v u : SharpCut.V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (hh : ⟪u,v⟫ = -1 ∨ ⟪u,v⟫ = 1/(n : ℝ)) :
    SharpCut.Certificate.lorentzDirection v u = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (SharpCut.Sharpness.modelShape v) u‖⁻¹ •
      Matrix.toEuclideanCLM (𝕜 := ℝ) (SharpCut.Sharpness.modelShape v) u :=
  SharpCut.Certificate.lorentz_model_direction hn v u hv hu hh

example (b a t : ℝ) (hb : 0 < b) (hb2 : b ≤ 1/2) (hden : 1-a*b ≠ 0)
    (ha : (b-a)/(1-a*b) = b/(2+b)) (ht : 1-t*b = (1-b)*(1+b/2)) :
    a = b/(2-b) ∧ t = (1+b)/2 := SharpCut.Certificate.model_matching_parameters b a t hb hb2 hden ha ht

run_cmd Lean.logInfo "SHARPCUT_LORENTZ_SUPPLEMENTARY_STATEMENTS_PASS"

/-- SUP-11: physical maximal-volume denominator and exact feasible primal-dual stopping guarantee. -/
example {n N : ℕ} [NeZero n] (hn : 1 ≤ n) {g q : Fin N → SharpCut.V n} {β α : Fin N → ℝ}
    {c : SharpCut.V n} {A : SharpCut.MatR n} (hP : SharpCut.IsConvexBody {x | ∀ r, ⟪g r,x⟫ ≤ β r})
    (hp : SharpCut.Optimization.PrimalFeasible g β c A) (hd : SharpCut.Optimization.DualFeasible g β α q) :
    let P : Set (SharpCut.V n) := {x | ∀ r, ⟪g r,x⟫ ≤ β r}
    let M := SharpCut.Optimization.aggregate g q
    let G := -Real.log M.det-Real.log A.det
    let pstar := Real.log ((SharpCut.maxEllipsoidVolume P).toReal/(MeasureTheory.volume (SharpCut.unitBall n)).toReal)
    0 < (SharpCut.maxEllipsoidVolume P).toReal ∧ pstar ≤ -Real.log M.det ∧
    -Real.log M.det = Real.log A.det+G ∧
    (MeasureTheory.volume (Khachiyan.ellipsoid c A)).toReal/(SharpCut.maxEllipsoidVolume P).toReal = Real.exp (Real.log A.det-pstar) ∧
    Real.exp (-G) ≤ (MeasureTheory.volume (Khachiyan.ellipsoid c A)).toReal/(SharpCut.maxEllipsoidVolume P).toReal ∧
    ENNReal.ofReal (Real.exp (-G))*SharpCut.maxEllipsoidVolume P ≤ MeasureTheory.volume (Khachiyan.ellipsoid c A) :=
  SharpCut.Applications.relative_volume_gap hn hP hp hd

example {n N : ℕ} [NeZero n] (hn : 1 ≤ n) {g q : Fin N → SharpCut.V n} {β α : Fin N → ℝ}
    {c : SharpCut.V n} {A : SharpCut.MatR n} (hP : SharpCut.IsConvexBody {x | ∀ r, ⟪g r,x⟫ ≤ β r})
    (hp : SharpCut.Optimization.PrimalFeasible g β c A) (hd : SharpCut.Optimization.DualFeasible g β α q)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hgap : -Real.log (SharpCut.Optimization.aggregate g q).det-Real.log A.det ≤ -Real.log (1-δ)) :
    ENNReal.ofReal (1-δ)*SharpCut.maxEllipsoidVolume {x | ∀ r, ⟪g r,x⟫ ≤ β r} ≤ MeasureTheory.volume (Khachiyan.ellipsoid c A) :=
  SharpCut.Applications.relative_accuracy_stop hn hP hp hd δ hδ hδ1 hgap

run_cmd Lean.logInfo "SHARPCUT_RELATIVE_VOLUME_STOPPING_STATEMENTS_PASS"

/-- SUP-10: the literal physical inner ball and the exact 8n+2 next-coordinate radius ratio. -/
example {n : ℕ} [NeZero n] (hn : 1 ≤ n) {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K)
    (hJ : SharpCut.IsJohnNormalized K) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    Metric.closedBall ((-1/4 : ℝ) • v) (1/8 : ℝ) ⊆ K ∩ {x | ⟪v,x⟫ ≤ 0} ∧
    SharpCut.unitBall n ⊆ (fun x => (8 : ℝ) • (x+(1/4 : ℝ) • v)) '' (K ∩ {x | ⟪v,x⟫ ≤ 0}) ∧
    (fun x => (8 : ℝ) • (x+(1/4 : ℝ) • v)) '' (K ∩ {x | ⟪v,x⟫ ≤ 0}) ⊆ Metric.closedBall 0 (8*(n : ℝ)+2) ∧
    SharpCut.Applications.initializationRatio n ≤ 10*(n : ℝ) ∧
    SharpCut.Applications.initializationRatio =O[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
  have h := SharpCut.Applications.central_cut_initialization hn hK hJ v hv
  have hmap : SharpCut.Applications.postCutCoordinates v = (fun x => (8 : ℝ) • (x+(1/4 : ℝ) • v)) := by
    funext x
    rfl
  rw [hmap] at h
  simpa only [SharpCut.centralHalfspace, sub_zero] using h

/-- SUP-03: actual affine John rounding, central symmetry about an arbitrary center and true ratio suprema. -/
example {n : ℕ} [NeZero n] (hn : 1 ≤ n) {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K) :
    (∀ c : SharpCut.V n, ∀ A : SharpCut.MatR n, SharpCut.IsMaxDet K c A →
      Khachiyan.ellipsoid c A ⊆ K ∧ K ⊆ Khachiyan.ellipsoid c ((n : ℝ) • A)) ∧
    ((∃ z : SharpCut.V n, ∀ x ∈ K, (2 : ℝ) • z-x ∈ K) →
      ∀ c : SharpCut.V n, ∀ A : SharpCut.MatR n, SharpCut.IsMaxDet K c A →
        Khachiyan.ellipsoid c A ⊆ K ∧ K ⊆ Khachiyan.ellipsoid c (Real.sqrt (n : ℝ) • A)) ∧
    SharpCut.Geometry.optimalConstant n = SharpCut.sharpRatio n ∧
    SharpCut.Geometry.contactOptimalConstant n = SharpCut.sharpRatio n :=
  SharpCut.Applications.john_rounding_and_contact_supremum hn hK

example {n : ℕ} [NeZero n] {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K) {c z : SharpCut.V n} {A : SharpCut.MatR n}
    (hsym : ∀ x ∈ K, (2 : ℝ) • z-x ∈ K) (hmax : SharpCut.IsMaxDet K c A) : c = z :=
  SharpCut.Applications.symmetry_center_eq hK hsym hmax

run_cmd Lean.logInfo "SHARPCUT_ROUNDING_INITIALIZATION_STATEMENTS_PASS"

/-- SUP-26: actual full-dimensional offset-cut polytope, exact optimal dual and changed normalization. -/
example {n N : ℕ} (hn : 1 ≤ n) (u : Fin N → SharpCut.V n) (v : SharpCut.V n) (η : ℝ)
    (hu : ∀ i, u i ≠ 0) (hv : v ≠ 0)
    (hP : SharpCut.IsConvexBody ({x | ∀ i, ⟪u i,x⟫ ≤ 1} ∩ {x | ⟪v,x⟫ ≤ η})) :
    let g := Fin.cases v u
    let β : Fin (N+1) → ℝ := Fin.cases η (fun _ => 1)
    ∃ c : SharpCut.V n, ∃ A : SharpCut.MatR n, ∃ α : Fin (N+1) → ℝ, ∃ q : Fin (N+1) → SharpCut.V n,
      SharpCut.IsMaxDet ({x | ∀ i, ⟪u i,x⟫ ≤ 1} ∩ {x | ⟪v,x⟫ ≤ η}) c A ∧
      SharpCut.Optimization.PrimalOptimal g β c A ∧ SharpCut.Optimization.DualOptimal g β α q ∧
      SharpCut.Optimization.aggregate g q = A⁻¹ ∧ (∀ r, α r*(β r-⟪g r,c⟫)-⟪q r,Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ = 0) ∧
      (∑ i : Fin N, α i.succ)+η*α 0 = (n : ℝ) ∧ (∑ i, α i.succ • u i)+α 0 • v = 0 ∧
      Real.log A.det+Real.log (SharpCut.Optimization.aggregate g q).det = 0 := by
  have h := SharpCut.Optimization.offset_cut_duality hn u v η hu hv hP
  have hg : SharpCut.Optimization.offsetNormals u v = Fin.cases v u := by funext r; rfl
  have hb : SharpCut.Optimization.offsetOffsets (N := N) η = Fin.cases η (fun _ => 1) := by funext r; rfl
  rw [hg, hb] at h
  simpa only [SharpCut.Optimization.offsetPolytope, SharpCut.Optimization.constraintPolytope,
    SharpCut.Optimization.conePairing, SharpCut.Optimization.coneHeight] using h

/-- Simultaneous constraints retain every cut normal and offset, and still attain both exact optima. -/
example {n N L : ℕ} (hn : 1 ≤ n) (u : Fin N → SharpCut.V n) (v : Fin L → SharpCut.V n) (η : Fin L → ℝ)
    (hu : ∀ i, u i ≠ 0) (hv : ∀ j, v j ≠ 0)
    (hP : SharpCut.IsConvexBody ({x | ∀ i, ⟪u i,x⟫ ≤ 1} ∩ {x | ∀ j, ⟪v j,x⟫ ≤ η j})) :
    let g : Fin (N+L) → SharpCut.V n := Fin.addCases u v
    let β : Fin (N+L) → ℝ := Fin.addCases (fun _ => 1) η
    ∃ c : SharpCut.V n, ∃ A : SharpCut.MatR n, ∃ α : Fin (N+L) → ℝ, ∃ q : Fin (N+L) → SharpCut.V n,
      SharpCut.IsMaxDet ({x | ∀ i, ⟪u i,x⟫ ≤ 1} ∩ {x | ∀ j, ⟪v j,x⟫ ≤ η j}) c A ∧
      SharpCut.Optimization.PrimalOptimal g β c A ∧ SharpCut.Optimization.DualOptimal g β α q ∧
      SharpCut.Optimization.aggregate g q = A⁻¹ ∧ (∀ r, α r*(β r-⟪g r,c⟫)-⟪q r,Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ = 0) ∧
      (∑ i, α (Fin.castAdd L i))+(∑ j, α (Fin.natAdd N j)*η j) = (n : ℝ) ∧
      (∑ i, α (Fin.castAdd L i) • u i)+(∑ j, α (Fin.natAdd N j) • v j) = 0 ∧
      Real.log A.det+Real.log (SharpCut.Optimization.aggregate g q).det = 0 := by
  have h := SharpCut.Optimization.multiple_cut_duality hn u v η hu hv hP
  have hg : SharpCut.Optimization.multipleNormals u v = Fin.addCases u v := by funext r; rfl
  have hb : SharpCut.Optimization.multipleOffsets (N := N) η = Fin.addCases (fun _ => 1) η := by funext r; rfl
  rw [hg, hb] at h
  simpa only [SharpCut.Optimization.multiplePolytope, SharpCut.Optimization.constraintPolytope,
    SharpCut.Optimization.conePairing, SharpCut.Optimization.coneHeight] using h

run_cmd Lean.logInfo "SHARPCUT_OFFSET_MULTIPLE_DUAL_STATEMENTS_PASS"

/-- SUP-02: genuine all-matrix positive logdet concavity and the convex SOC feasible set. -/
example {n : ℕ} : ConcaveOn ℝ {A : SharpCut.MatR n | A.PosDef} (fun A => Real.log A.det) :=
  SharpCut.Optimization.logdet_concaveOn

example {n N : ℕ} (g : Fin N → SharpCut.V n) (β : Fin N → ℝ) :
    Convex ℝ {p : SharpCut.V n × SharpCut.MatR n | SharpCut.Optimization.PrimalFeasible g β p.1 p.2} :=
  SharpCut.Optimization.primal_feasible_convex g β

/-- The support formula is actually attained in the ellipsoid, including zero normals. -/
example {n : ℕ} (c g : SharpCut.V n) (A : SharpCut.MatR n) (hA : A.PosDef) :
    (∀ x ∈ Khachiyan.ellipsoid c A, ⟪g,x⟫ ≤ ⟪g,c⟫+‖Matrix.toEuclideanCLM (𝕜 := ℝ) A g‖) ∧
    (∃ x ∈ Khachiyan.ellipsoid c A, ⟪g,x⟫ = ⟪g,c⟫+‖Matrix.toEuclideanCLM (𝕜 := ℝ) A g‖) :=
  ⟨fun x hx => Khachiyan.ellipsoid_support_le hA.isHermitian.isSymm hx, Khachiyan.ellipsoid_support_attained hA.isHermitian.isSymm g⟩

/-- Standard Euclidean Lorentz self-duality and the optimization's equivalent minus-sign convention. -/
example {n : ℕ} (α : ℝ) (q : SharpCut.V n) :
    ((∀ τ : ℝ, ∀ x : SharpCut.V n, ‖x‖ ≤ τ → 0 ≤ α*τ+⟪q,x⟫) ↔ ‖q‖ ≤ α) ∧
    ((∀ τ : ℝ, ∀ x : SharpCut.V n, ‖x‖ ≤ τ → 0 ≤ α*τ-⟪q,x⟫) ↔ ‖q‖ ≤ α) :=
  ⟨SharpCut.Optimization.lorentz_self_dual_plus α q, SharpCut.Optimization.lorentz_self_dual α q⟩

example {n : ℕ} (A B : SharpCut.MatR n) (hA : A.PosDef) (hB : B.PosDef) :
    Real.log B.det ≤ Real.log A.det+(A⁻¹*(B-A)).trace :=
  SharpCut.Optimization.logdet_supporting_hyperplane A B hA hB

run_cmd Lean.logInfo "SHARPCUT_CONVEX_LORENTZ_STATEMENTS_PASS"

/-- SUP-18: both reciprocal polynomial lower bounds on their exact positive domains. -/
example (z s : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) (hs : 0 ≤ s) (hs1 : s < 1) :
    1+z^2+z^4 ≤ 1/(1-z^2) ∧ 1+2*s+3*s^2 ≤ 1/(1-s)^2 :=
  SharpCut.Scalar.reciprocal_polynomial_lower z s hz hz1 hs hs1

/-- The claimed integral values are supported by a symbolic antiderivative, not an external computation. -/
example (b a t : ℝ) :
    (∫ z in a..t, z^2*(1+z^2+z^4)*(1+2*b*z+3*b^2*z^2)) =
    SharpCut.Scalar.polynomialLowerPrimitive b t-SharpCut.Scalar.polynomialLowerPrimitive b a :=
  SharpCut.Scalar.polynomial_lower_integral b a t

example (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 1/2) :
    (4*(1-b)^2*(2+b)*(3+b)/(b^2+b+2)) *
      (SharpCut.Scalar.polynomialLowerPrimitive b ((1+b)/2)-SharpCut.Scalar.polynomialLowerPrimitive b (b/(2-b))) ≤
    SharpCut.Scalar.lossRatio b :=
  SharpCut.Scalar.lossRatio_polynomial_lower b hb hb2

example : (16/15 : ℝ) < SharpCut.Scalar.lossRatio (1/3) ∧ (7/6 : ℝ) < SharpCut.Scalar.lossRatio (1/2) :=
  SharpCut.Scalar.low_dimension_scalar_remainder

run_cmd Lean.logInfo "SHARPCUT_LOW_DIMENSION_REMAINDER_STATEMENTS_PASS"

/-- SUP-27: rebuilt cone geometry and actual new fixed-dimensional attainment. -/
example {m : ℕ} (hm : 1 ≤ m) :
    SharpCut.IsConvexBody (Khachiyan.Cone.body m) ∧ SharpCut.IsJohnNormalized (Khachiyan.Cone.body m) ∧
    SharpCut.IsConvexBody (Khachiyan.Cone.cut m) ∧
    SharpCut.IsFeasible (Khachiyan.Cone.cut m) (Khachiyan.Cone.candidateCenter m) (Khachiyan.Cone.candidateShape m) ∧
    (Khachiyan.Cone.candidateShape m).det = SharpCut.sharpRatio (m+1) ∧
    (Khachiyan.maxEllipsoidVolume (Khachiyan.Cone.cut m)).toReal/(Khachiyan.maxEllipsoidVolume (Khachiyan.Cone.body m)).toReal = SharpCut.sharpRatio (m+1) :=
  SharpCut.Sharpness.legacy_cone_attainment hm

example {m : ℕ} (hm : 1 ≤ m) :
    SharpCut.IsMaxDet (Khachiyan.Cone.cut m) (Khachiyan.Cone.candidateCenter m) (Khachiyan.Cone.candidateShape m) :=
  SharpCut.Sharpness.legacy_cone_candidate_maximal hm

example {K : Set (SharpCut.V 1)} (hK : SharpCut.IsConvexBody K) {v : SharpCut.V 1} (hv : v ≠ 0) :
    SharpCut.maxEllipsoidVolume (K ∩ SharpCut.centralHalfspace (Khachiyan.johnCenter K) v) =
      ENNReal.ofReal (1/2 : ℝ)*SharpCut.maxEllipsoidVolume K ∧
    (SharpCut.maxEllipsoidVolume (K ∩ SharpCut.centralHalfspace (Khachiyan.johnCenter K) v)).toReal/(SharpCut.maxEllipsoidVolume K).toReal = 1/2 :=
  SharpCut.Sharpness.one_dimensional_reference hK hv

example : Filter.Tendsto (fun m : ℕ => SharpCut.sharpRatio (m+1)) Filter.atTop (nhds Khachiyan.rStar) :=
  SharpCut.Sharpness.sharpRatio_shifted_limit

run_cmd Lean.logInfo "SHARPCUT_LEGACY_CONE_STATEMENTS_PASS"

/-- SUP-12: the actual normalized-dual supremum equals the reciprocal physical optimal volume. -/
example {n N : ℕ} [NeZero n] (hn : 1 ≤ n) (g : Fin N → SharpCut.V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hP : SharpCut.IsConvexBody {x | ∀ r, ⟪g r,x⟫ ≤ β r}) :
    0 < sSup {d : ℝ | ∃ α q, SharpCut.Optimization.DualFeasible g β α q ∧
      d = (SharpCut.Optimization.aggregate g q).det} ∧
    (SharpCut.maxEllipsoidVolume {x | ∀ r, ⟪g r,x⟫ ≤ β r}).toReal / (MeasureTheory.volume (SharpCut.unitBall n)).toReal =
      (sSup {d : ℝ | ∃ α q, SharpCut.Optimization.DualFeasible g β α q ∧
        d = (SharpCut.Optimization.aggregate g q).det})⁻¹ := by
  simpa only [SharpCut.Optimization.constraintPolytope, SharpCut.Optimization.dualDeterminantMaximum,
    SharpCut.Optimization.dualDeterminants] using
      SharpCut.Optimization.dual_maximum_volume_identity hn g β hg hP

/-- Fixed alpha optimization actually attains a positive-definite maximum, including boundary cone data. -/
example {n N : ℕ} {g q₀ : Fin N → SharpCut.V n} {β α : Fin N → ℝ}
    (hseed : SharpCut.Optimization.DualFeasible g β α q₀) :
    ∃ q, SharpCut.Optimization.DualFeasible g β α q ∧
      IsGreatest {d : ℝ | ∃ q', SharpCut.Optimization.DualFeasible g β α q' ∧
        d = (SharpCut.Optimization.aggregate g q').det} (SharpCut.Optimization.aggregate g q).det ∧
      sSup {d : ℝ | ∃ q', SharpCut.Optimization.DualFeasible g β α q' ∧
        d = (SharpCut.Optimization.aggregate g q').det} = (SharpCut.Optimization.aggregate g q).det ∧
      (SharpCut.Optimization.aggregate g q₀).det ≤ (SharpCut.Optimization.aggregate g q).det := by
  simpa only [SharpCut.Optimization.fixedDualDeterminants, SharpCut.Optimization.fixedDualDeterminantMaximum] using
    SharpCut.Optimization.fixed_dual_determinant_attained hseed

/-- The explicit fixed balanced weights give an attained improvement and the full optimum bounds it. -/
example {n N : ℕ} [NeZero n] (hn : 2 ≤ n) (F : SharpCut.JohnFrame n N) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    ∃ q, SharpCut.Optimization.DualFeasible (SharpCut.Certificate.cutNormals F v)
      (SharpCut.Certificate.cutOffsets N) (SharpCut.Certificate.cutAlpha F v) q ∧
      IsGreatest (SharpCut.Optimization.fixedDualDeterminants (SharpCut.Certificate.cutNormals F v)
        (SharpCut.Certificate.cutOffsets N) (SharpCut.Certificate.cutAlpha F v))
        (SharpCut.Optimization.aggregate (SharpCut.Certificate.cutNormals F v) q).det ∧
      SharpCut.Optimization.fixedDualDeterminantMaximum (SharpCut.Certificate.cutNormals F v)
        (SharpCut.Certificate.cutOffsets N) (SharpCut.Certificate.cutAlpha F v) =
        (SharpCut.Optimization.aggregate (SharpCut.Certificate.cutNormals F v) q).det ∧
      (SharpCut.Certificate.unrotatedQ F v).det ≤ (SharpCut.Optimization.aggregate (SharpCut.Certificate.cutNormals F v) q).det ∧
      (SharpCut.Optimization.aggregate (SharpCut.Certificate.cutNormals F v) q).det ≤
        SharpCut.Applications.instanceDeterminant F v :=
  SharpCut.Applications.instance_fixed_weight_improvement hn F v hv

/-- All-positive-dimension (7.11), exact attained frame infimum, actual cut and Lebesgue volume. -/
example {n N : ℕ} [NeZero n] (hn : 1 ≤ n) (F : SharpCut.JohnFrame n N) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    0 < SharpCut.Applications.instanceDeterminant F v ∧
    (SharpCut.maxEllipsoidVolume (F.polytope ∩ {x | ⟪v,x⟫ ≤ 0})).toReal / (MeasureTheory.volume (SharpCut.unitBall n)).toReal =
      (SharpCut.Applications.instanceDeterminant F v)⁻¹ ∧
    SharpCut.Geometry.optimalConstant n =
      (sInf {d : ℝ | ∃ L : ℕ, ∃ T : SharpCut.JohnFrame n L, ∃ u : SharpCut.V n,
        ‖u‖ = 1 ∧ d = SharpCut.Applications.instanceDeterminant T u})⁻¹ ∧
    sInf {d : ℝ | ∃ L : ℕ, ∃ T : SharpCut.JohnFrame n L, ∃ u : SharpCut.V n,
      ‖u‖ = 1 ∧ d = SharpCut.Applications.instanceDeterminant T u} = (SharpCut.sharpRatio n)⁻¹ ∧
    IsLeast {d : ℝ | ∃ L : ℕ, ∃ T : SharpCut.JohnFrame n L, ∃ u : SharpCut.V n,
      ‖u‖ = 1 ∧ d = SharpCut.Applications.instanceDeterminant T u} (SharpCut.sharpRatio n)⁻¹ ∧
    (∃ α q, SharpCut.Optimization.DualFeasible (SharpCut.Certificate.cutNormals F v)
      (SharpCut.Certificate.cutOffsets N) α q ∧
      SharpCut.Applications.instanceDeterminant F v = (SharpCut.Optimization.aggregate (SharpCut.Certificate.cutNormals F v) q).det) := by
  simpa only [SharpCut.centralHalfspace, sub_zero, SharpCut.Applications.frameDualInfimum,
    SharpCut.Applications.frameDualMaxima] using
      SharpCut.Applications.exact_instance_dual_characterization hn F v hv

run_cmd Lean.logInfo "SHARPCUT_INSTANCE_DUAL_STATEMENTS_PASS"

attribute [local instance] Classical.propDecidable

/-- SUP-22: the original SOC Lagrangian, its finite conjugate and both genuine EReal infinite branches. -/
example {n N : ℕ} (hn : 1 ≤ n) (g q : Fin N → SharpCut.V n) (β α : Fin N → ℝ) :
    sSup {z : EReal | ∃ c : SharpCut.V n, ∃ A : SharpCut.MatR n, A.PosDef ∧
      z = ((Real.log A.det + ∑ r, (α r*(β r-⟪g r,c⟫)-⟪q r,Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫) : ℝ) : EReal)} =
      if (∑ r, α r • g r) = 0 ∧ (SharpCut.Optimization.aggregate g q).PosDef
      then (((∑ r, α r*β r)-(n : ℝ)-Real.log (SharpCut.Optimization.aggregate g q).det : ℝ) : EReal) else ⊤ := by
  have h := SharpCut.Optimization.original_lagrangian_supremum hn g q β α
  have hB : SharpCut.Optimization.balanceVector g α = ∑ r, α r • g r := rfl
  have hs : SharpCut.Optimization.dualMass β α = ∑ r, α r*β r := rfl
  have hL : SharpCut.Optimization.originalLagrangian g β α q =
      (fun c A => Real.log A.det + ∑ r, (α r*(β r-⟪g r,c⟫)-⟪q r,Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫)) := by
    funext c A
    rfl
  rw [hB, hs, hL] at h
  simpa only [EReal.coe_sub] using h

example {n : ℕ} (M A : SharpCut.MatR n) (hM : M.PosDef) (hA : A.PosDef) :
    Real.log A.det-(A*M).trace ≤ -(n : ℝ)-Real.log M.det ∧
    Real.log M⁻¹.det-(M⁻¹*M).trace = -(n : ℝ)-Real.log M.det :=
  ⟨SharpCut.Optimization.logdet_conjugate_bound M A hM hA, SharpCut.Optimization.logdet_conjugate_attained M hM⟩

/-- The multiplier mass is derived to be positive from actual primal feasibility, not assumed as a field. -/
example {n N : ℕ} (hn : 1 ≤ n) {g q : Fin N → SharpCut.V n} {β α : Fin N → ℝ}
    {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hp : SharpCut.Optimization.PrimalFeasible g β c A)
    (hd : SharpCut.Optimization.UnnormalizedDualFeasible g α q) :
    0 < (A*SharpCut.Optimization.aggregate g q).trace ∧
      (A*SharpCut.Optimization.aggregate g q).trace ≤ ∑ r, α r*β r ∧ 0 < ∑ r, α r*β r :=
  SharpCut.Optimization.unnormalized_mass_positive hn hp hd

/-- Exact (10.3) on all positive scales, including an attained minimum at n/s. -/
example {n : ℕ} (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s) (M : SharpCut.MatR n) (ρ : ℝ) (hρ : 0 < ρ) :
    (ρ*s-(n : ℝ)-(n : ℝ)*Real.log ρ-Real.log M.det) -
      (((n : ℝ)/s)*s-(n : ℝ)-(n : ℝ)*Real.log ((n : ℝ)/s)-Real.log M.det) =
        (n : ℝ)*(ρ*s/(n : ℝ)-1-Real.log (ρ*s/(n : ℝ))) ∧
    (((n : ℝ)/s)*s-(n : ℝ)-(n : ℝ)*Real.log ((n : ℝ)/s)-Real.log M.det) ≤
      ρ*s-(n : ℝ)-(n : ℝ)*Real.log ρ-Real.log M.det :=
  SharpCut.Optimization.optimal_scale hn s hs M ρ hρ

example {n N : ℕ} (hn : 1 ≤ n) {g q : Fin N → SharpCut.V n} {β α : Fin N → ℝ}
    {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hp : SharpCut.Optimization.PrimalFeasible g β c A)
    (hd : SharpCut.Optimization.UnnormalizedDualFeasible g α q) :
    SharpCut.Optimization.DualFeasible g β (fun r => ((n : ℝ)/(∑ j, α j*β j))*α r)
      (fun r => ((n : ℝ)/(∑ j, α j*β j)) • q r) :=
  SharpCut.Optimization.normalize_unnormalized hn hp hd

/-- Actual bounded full-dimensional polytope and nonzero facets give a strictly feasible spherical seed. -/
example {n N : ℕ} (hn : 1 ≤ n) (g : Fin N → SharpCut.V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hP : SharpCut.IsConvexBody {x | ∀ r, ⟪g r,x⟫ ≤ β r}) :
    ∃ c : SharpCut.V n, ∃ ε : ℝ, 0 < ε ∧ (ε • (1 : SharpCut.MatR n)).PosDef ∧
      (∀ r, ⟪g r,c⟫+‖Matrix.toEuclideanCLM (𝕜 := ℝ) (ε • (1 : SharpCut.MatR n)) (g r)‖ < β r) ∧
      Metric.closedBall c ε ⊆ {x | ∀ r, ⟪g r,x⟫ ≤ β r} :=
  SharpCut.Optimization.strictly_feasible_ball_seed hn g β hg hP

/-- The unnormalized objective attains its actual optimum, against every feasible competitor. -/
example {n N : ℕ} (hn : 1 ≤ n) (g : Fin N → SharpCut.V n) (β : Fin N → ℝ)
    (hg : ∀ r, g r ≠ 0) (hP : SharpCut.IsConvexBody {x | ∀ r, ⟪g r,x⟫ ≤ β r}) :
    ∃ c : SharpCut.V n, ∃ A : SharpCut.MatR n, ∃ α : Fin N → ℝ, ∃ q : Fin N → SharpCut.V n,
      SharpCut.IsMaxDet {x | ∀ r, ⟪g r,x⟫ ≤ β r} c A ∧
      SharpCut.Optimization.UnnormalizedDualFeasible g α q ∧ (∑ r, α r*β r) = (n : ℝ) ∧
      (∑ r, α r*β r)-(n : ℝ)-Real.log (SharpCut.Optimization.aggregate g q).det = Real.log A.det ∧
      (∀ α' q', SharpCut.Optimization.UnnormalizedDualFeasible g α' q' →
        (∑ r, α r*β r)-(n : ℝ)-Real.log (SharpCut.Optimization.aggregate g q).det ≤
          (∑ r, α' r*β r)-(n : ℝ)-Real.log (SharpCut.Optimization.aggregate g q').det) :=
  SharpCut.Optimization.unnormalized_dual_attainment hn g β hg hP

run_cmd Lean.logInfo "SHARPCUT_UNNORMALIZED_LAGRANGIAN_STATEMENTS_PASS"

/-- SUP-09: the full infinite series, with j=0 here representing paper index j=1. -/
example {n : ℕ} (hn : 2 ≤ n) :
    HasSum (fun j : ℕ => 1/(2*((j : ℝ)+1)*((j : ℝ)+2)*(n : ℝ)^(j+1)))
      (-Real.log (SharpCut.sharpRatio n)-Real.log 2+1/2) ∧
    Summable (fun j : ℕ => |1/(2*((j : ℝ)+1)*((j : ℝ)+2)*(n : ℝ)^(j+1))|) ∧
    -Real.log (SharpCut.sharpRatio n) = Real.log 2-1/2+
      ∑' j : ℕ, 1/(2*((j : ℝ)+1)*((j : ℝ)+2)*(n : ℝ)^(j+1)) ∧
    -Real.log (SharpCut.sharpRatio n) = Real.log 2-1/2+
      ∑' j : ℕ, (1/(2*((j : ℝ)+1))-1/(2*((j : ℝ)+2)))*(1/(n : ℝ))^(j+1) :=
  ⟨SharpCut.Applications.sharpRatio_hasSum hn, SharpCut.Applications.sharpRatio_series_absolute hn,
    SharpCut.Applications.sharpRatio_full_series hn, SharpCut.Applications.sharpRatio_alternative_series hn⟩

example {n : ℕ} (hn : 2 ≤ n) :
    -Real.log (SharpCut.sharpRatio n) = Real.log 2+((n : ℝ)-1)/2*Real.log (1-1/(n : ℝ)) :=
  SharpCut.Applications.negative_log_sharpRatio_formula hn

/-- Strict monotonicity covers every positive dimension, including the separately treated n=1 value. -/
example : StrictMonoOn SharpCut.sharpRatio {n : ℕ | 1 ≤ n} := SharpCut.Applications.sharpRatio_strictMonoOn

example {n : ℕ} (hn : 1 ≤ n) :
    (1/2 : ℝ) ≤ SharpCut.sharpRatio n ∧ SharpCut.sharpRatio n < Real.sqrt (Real.exp 1)/2 :=
  SharpCut.Applications.sharpRatio_all_dimension_bounds hn

example : Filter.Tendsto SharpCut.sharpRatio Filter.atTop (nhds (Real.sqrt (Real.exp 1)/2)) := by
  simpa only [Khachiyan.Scalar.rStar_eq_sqrt_exp_one] using SharpCut.Applications.sharpRatio_limit

/-- Every n>=2 has a literal explicit remainder bound; the three displayed coefficients are retained. -/
example {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ -Real.log (SharpCut.sharpRatio n)-
      (Real.log 2-1/2+1/(4*(n : ℝ))+1/(12*(n : ℝ)^2)+1/(24*(n : ℝ)^3)) ∧
    -Real.log (SharpCut.sharpRatio n)-
      (Real.log 2-1/2+1/(4*(n : ℝ))+1/(12*(n : ℝ)^2)+1/(24*(n : ℝ)^3)) ≤ 1/(20*(n : ℝ)^4) :=
  SharpCut.Applications.negativeLogRemainder_bounds hn

/-- Genuine eventual O(n^-4), with the original logarithmic remainder expanded in the expected type. -/
example :
    (fun n : ℕ => -Real.log (SharpCut.sharpRatio n)-
      (Real.log 2-1/2+1/(4*(n : ℝ))+1/(12*(n : ℝ)^2)+1/(24*(n : ℝ)^3))) =O[Filter.atTop]
      (fun n : ℕ => 1/(n : ℝ)^4) := by
  have h := SharpCut.Applications.negativeLogRemainder_isBigO
  have hf : SharpCut.Applications.negativeLogRemainder =
      (fun n : ℕ => -Real.log (SharpCut.sharpRatio n)-
        (Real.log 2-1/2+1/(4*(n : ℝ))+1/(12*(n : ℝ)^2)+1/(24*(n : ℝ)^3))) := by
    funext n
    rfl
  rw [hf] at h
  exact h

example (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    0 ≤ (1/2+(1-x)/(2*x)*Real.log (1-x))-(x/4+x^2/12+x^3/24) ∧
    (1/2+(1-x)/(2*x)*Real.log (1-x))-(x/4+x^2/12+x^3/24) ≤ x^4/(40*(1-x)) :=
  SharpCut.Scalar.constantSeries_fourth_tail x hx hx1

run_cmd Lean.logInfo "SHARPCUT_CONSTANT_SERIES_ASYMPTOTICS_STATEMENTS_PASS"

/-- SUP-23: actual trace-of-Gram-root nuclear triangle inequality on all real matrices, including singular matrices. -/
example {n : ℕ} (X Y : SharpCut.MatR n) :
    (CFC.sqrt ((X+Y)*(X+Y)ᵀ)).trace ≤ (CFC.sqrt (X*Xᵀ)).trace+(CFC.sqrt (Y*Yᵀ)).trace :=
  SharpCut.Nuclear.nuclearNorm_triangle X Y

example {n : ℕ} (u v : SharpCut.V n) :
    let X := Matrix.vecMulVec u.ofLp v.ofLp
    (CFC.sqrt (X*Xᵀ)).trace = ‖u‖*‖v‖ :=
  SharpCut.Nuclear.nuclearNorm_cross u v

example {n : ℕ} (X R : SharpCut.MatR n) :
    (X*Rᵀ).trace ≤ (CFC.sqrt (X*Xᵀ)).trace*‖Matrix.toEuclideanCLM (𝕜 := ℝ) R‖ :=
  SharpCut.Nuclear.trace_le_nuclear_operator X R

/-- The full contraction dual representation has a genuine attainer even when X is singular. -/
example {n : ℕ} (X : SharpCut.MatR n) :
    ∃ R : SharpCut.MatR n, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) R‖ ≤ 1 ∧
      (X*Rᵀ).trace = (CFC.sqrt (X*Xᵀ)).trace :=
  SharpCut.Nuclear.nuclear_dual_attainment X

example {n : ℕ} (X : SharpCut.MatR n) (hX : 0 < X.det) :
    (CFC.sqrt (X*Xᵀ)).trace-(n : ℝ)-Real.log X.det =
      ∑ i, (SharpCut.Nuclear.singularValue X i-1-Real.log (SharpCut.Nuclear.singularValue X i)) ∧
    0 ≤ (CFC.sqrt (X*Xᵀ)).trace-(n : ℝ)-Real.log X.det :=
  SharpCut.Nuclear.nuclear_logdet_spectral X hX

/-- Every named singular value is the eigenvalue of the actual positive Gram root. -/
example {n : ℕ} (X : SharpCut.MatR n) :
    (CFC.sqrt (X*Xᵀ)).trace = ∑ i, SharpCut.Nuclear.singularValue X i ∧
    (∀ i, 0 ≤ SharpCut.Nuclear.singularValue X i) :=
  ⟨SharpCut.Nuclear.nuclearNorm_eq_sum_singularValues X, SharpCut.Nuclear.singularValue_nonneg X⟩

example {n : ℕ} (Q A : SharpCut.MatR n) (hQ : 0 < Q.det) (hA : A.PosDef)
    (hcomm : Commute A (SharpCut.Certificate.polarMatrix Q)) :
    (CFC.sqrt ((A*Q)*(A*Q)ᵀ)).trace-(A*SharpCut.Certificate.polarMatrix Q).trace = 0 :=
  SharpCut.Nuclear.commuting_polar_correction Q A hQ hA hcomm

/-- Original (10.6)-(10.8), with all four nonnegative terms, both correction signs and logdet Fhat explicit. -/
example {n N : ℕ} (hn : 2 ≤ n) {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K)
    (hJ : SharpCut.IsJohnNormalized K) (F : SharpCut.JohnFrame n N) (hs : F.Supports K)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hA : SharpCut.IsFeasible (K ∩ {x | ⟪v,x⟫ ≤ 0}) c A) :
    let Q := SharpCut.Certificate.unrotatedQ F v
    let M := SharpCut.Certificate.polarMatrix Q
    let S := (∑ i, SharpCut.Certificate.originalWeight F v i*
      (1-⟪F.contact i,c⟫-‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖))+
      SharpCut.Certificate.cutWeight n*(-⟪v,c⟫-‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖)
    let T := (∑ i, SharpCut.Certificate.originalWeight F v i*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (F.contact i)‖)+
      SharpCut.Certificate.cutWeight n*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖-SharpCut.Nuclear.nuclearNorm (A*Q)
    let H := SharpCut.Nuclear.nuclearNorm (A*Q)-(n : ℝ)-Real.log (A*Q).det
    let Rpol := SharpCut.Nuclear.nuclearNorm (A*Q)-(A*M).trace
    0 ≤ S ∧ 0 ≤ T ∧ 0 ≤ H ∧ 0 ≤ Rpol ∧
    SharpCut.Gap.frameConeGap F v c A = S+T+Rpol ∧
    SharpCut.Optimization.pairDivergence A M = H-Rpol ∧
    Real.log (SharpCut.sharpRatio n/A.det) = Real.log (SharpCut.Certificate.normalizedCertificate F v).det+S+T+H ∧
    (Commute A M → Rpol = 0) := by
  have hcut : SharpCut.IsFeasible (K ∩ SharpCut.centralHalfspace 0 v) c A := by
    simpa only [SharpCut.centralHalfspace, sub_zero] using hA
  have h := SharpCut.Nuclear.nuclear_frame_deficit hn hK hJ F hs v hv hcut
  have hgeo : SharpCut.Gap.geometricGap F v = Real.log (SharpCut.Certificate.normalizedCertificate F v).det := by
    rw [SharpCut.Gap.geometricGap, SharpCut.Gap.frameMatrix,
      SharpCut.Certificate.polarMatrix_det (SharpCut.Certificate.unrotatedQ_det_pos F hn v hv),
      ← SharpCut.Certificate.normalizedCertificate_det F hn v hv]
  rw [hgeo] at h
  simpa only [SharpCut.Nuclear.frameSupportSlack, SharpCut.Nuclear.frameTriangleGap,
    SharpCut.Nuclear.frameNuclearTotal, SharpCut.Nuclear.frameLogGap, SharpCut.Nuclear.framePolarCorrection,
    SharpCut.Gap.frameMatrix, SharpCut.Gap.volumeDeficit] using h

run_cmd Lean.logInfo "SHARPCUT_NUCLEAR_DEFICIT_STATEMENTS_PASS"

/-- SUP-08: the signed transverse unit vectors and literal one-half weights obey all defining moments. -/
example (m : ℕ) :
    (∀ i : Fin m × Bool, ‖SharpCut.Sharpness.signedTransverse m i‖ = 1 ∧
      ⟪SharpCut.Sharpness.axis m,SharpCut.Sharpness.signedTransverse m i⟫ = 0) ∧
    (∑ i : Fin m × Bool, (1/2 : ℝ) • SharpCut.Sharpness.signedTransverse m i) = 0 ∧
    (∑ i : Fin m × Bool, (1/2 : ℝ) • SharpCut.outer (SharpCut.Sharpness.signedTransverse m i)) =
      SharpCut.Certificate.projector (SharpCut.Sharpness.axis m) :=
  ⟨fun i => ⟨SharpCut.Sharpness.signed_transverse_unit m i,SharpCut.Sharpness.signed_transverse_perp m i⟩,
    SharpCut.Sharpness.signed_transverse_balance m,SharpCut.Sharpness.signed_transverse_isotropy m⟩

example {m : ℕ} (hm : 1 ≤ m) :
    SharpCut.IsConvexBody (SharpCut.Sharpness.extremalBody m hm) ∧
    SharpCut.IsJohnNormalized (SharpCut.Sharpness.extremalBody m hm) ∧
    SharpCut.maxEllipsoidVolume (SharpCut.Sharpness.extremalBody m hm ∩ SharpCut.centralHalfspace 0 (SharpCut.Sharpness.axis m)) =
      ENNReal.ofReal (SharpCut.sharpRatio (m+1))*SharpCut.maxEllipsoidVolume (SharpCut.Sharpness.extremalBody m hm) ∧
    SharpCut.IsMaxDet (SharpCut.Sharpness.extremalBody m hm ∩ SharpCut.centralHalfspace 0 (SharpCut.Sharpness.axis m))
      ((-1/2 : ℝ) • SharpCut.Sharpness.axis m) (SharpCut.Sharpness.modelShape (SharpCut.Sharpness.axis m)) ∧
    Khachiyan.johnEllipsoid (SharpCut.Sharpness.extremalBody m hm ∩ SharpCut.centralHalfspace 0 (SharpCut.Sharpness.axis m)) =
      SharpCut.Equality.modelEllipsoid (SharpCut.Sharpness.axis m) :=
  SharpCut.Sharpness.signed_family_geometry hm

/-- Literal paper coordinates, original John ball and actual new John center/shape/volume. -/
example :
    let K : Set (SharpCut.V 3) := {p | -1 ≤ p 2 ∧ 2*Real.sqrt 2*|p 0|+p 2 ≤ 3 ∧ 2*Real.sqrt 2*|p 1|+p 2 ≤ 3}
    let L : Set (SharpCut.V 3) := K ∩ {p | p 2 ≤ 0}
    let c : SharpCut.V 3 := WithLp.toLp 2 ![0,0,(-1/2 : ℝ)]
    let A : SharpCut.MatR 3 := Matrix.diagonal ![Real.sqrt (3/2),Real.sqrt (3/2),(1/2 : ℝ)]
    SharpCut.IsConvexBody K ∧ SharpCut.IsJohnNormalized K ∧ Khachiyan.johnEllipsoid K = SharpCut.unitBall 3 ∧
    Khachiyan.johnCenter K = 0 ∧ SharpCut.IsConvexBody L ∧
    Khachiyan.johnCenter L = c ∧ Khachiyan.johnShape L = A ∧ Khachiyan.johnEllipsoid L = Khachiyan.ellipsoid c A ∧
    A.det = (3/4 : ℝ) ∧ SharpCut.maxEllipsoidVolume L = ENNReal.ofReal (3/4 : ℝ)*SharpCut.maxEllipsoidVolume K ∧
    (SharpCut.maxEllipsoidVolume L).toReal/(SharpCut.maxEllipsoidVolume K).toReal = (3/4 : ℝ) :=
  ⟨SharpCut.Examples.SquarePyramid.body_isConvexBody,SharpCut.Examples.SquarePyramid.body_isJohnNormalized,
    SharpCut.Examples.SquarePyramid.original_john_ball,
    Khachiyan.johnCenter_eq_of_isMaxDet SharpCut.Examples.SquarePyramid.body_isConvexBody SharpCut.Examples.SquarePyramid.body_isJohnNormalized,
    SharpCut.Examples.SquarePyramid.cut_isConvexBody,
    SharpCut.Examples.SquarePyramid.new_john_parameters.1,SharpCut.Examples.SquarePyramid.new_john_parameters.2.1,
    SharpCut.Examples.SquarePyramid.new_john_parameters.2.2,SharpCut.Examples.SquarePyramid.candidate_shape_det,
    SharpCut.Examples.SquarePyramid.volume_ratio.1,SharpCut.Examples.SquarePyramid.volume_ratio.2⟩

/-- Exact original contact coordinates, including the four latitude points at z=1/3 and the pole. -/
example : SharpCut.Examples.SquarePyramid.frame.contact =
    ![WithLp.toLp 2 ![0,0,(-1 : ℝ)],WithLp.toLp 2 ![2*Real.sqrt 2/3,0,(1/3 : ℝ)],
      WithLp.toLp 2 ![-2*Real.sqrt 2/3,0,(1/3 : ℝ)],WithLp.toLp 2 ![0,2*Real.sqrt 2/3,(1/3 : ℝ)],
      WithLp.toLp 2 ![0,-2*Real.sqrt 2/3,(1/3 : ℝ)]] :=
  SharpCut.Examples.SquarePyramid.contact_array

example : SharpCut.Examples.SquarePyramid.frame.weight 0 = (3/4 : ℝ) ∧
    (∀ i : Fin 4, SharpCut.Examples.SquarePyramid.frame.contact i.succ 2 = (1/3 : ℝ) ∧
      SharpCut.Examples.SquarePyramid.frame.weight i.succ = (9/16 : ℝ)) := by
  refine ⟨?_,SharpCut.Examples.SquarePyramid.latitude_contacts_and_weights⟩
  have h := congrFun SharpCut.Examples.SquarePyramid.weight_function (0 : Fin 5)
  simpa only [Fin.cases_zero] using h

example (i : Fin 5) :
    SharpCut.Examples.SquarePyramid.frame.contact i ∈ SharpCut.unitBall 3 ∧
    SharpCut.Examples.SquarePyramid.frame.contact i ∈ frontier SharpCut.Examples.SquarePyramid.body ∧
    ⟪SharpCut.Examples.SquarePyramid.frame.contact i,SharpCut.Examples.SquarePyramid.frame.contact i⟫ = 1 :=
  SharpCut.Examples.SquarePyramid.original_facet_contacts i

/-- Actual six supporting contacts of the newly maximal ellipse, including the added cut. -/
example :
    (∀ i : Fin 5, ∃ x ∈ Khachiyan.johnEllipsoid SharpCut.Examples.SquarePyramid.cutBody,
      x ∈ SharpCut.Examples.SquarePyramid.cutBody ∧ ⟪SharpCut.Examples.SquarePyramid.frame.contact i,x⟫ = 1) ∧
    (∃ x ∈ Khachiyan.johnEllipsoid SharpCut.Examples.SquarePyramid.cutBody,
      x ∈ SharpCut.Examples.SquarePyramid.cutBody ∧ x 2 = 0) :=
  SharpCut.Examples.SquarePyramid.new_facet_contacts

/-- The given vertex lists are exact hull generators AND exactly all extreme points. -/
example :
    SharpCut.Examples.SquarePyramid.body = convexHull ℝ SharpCut.Examples.SquarePyramid.pyramidVertices ∧
    (SharpCut.Examples.SquarePyramid.body).extremePoints ℝ = SharpCut.Examples.SquarePyramid.pyramidVertices ∧
    SharpCut.Examples.SquarePyramid.cutBody = convexHull ℝ SharpCut.Examples.SquarePyramid.frustumVertices ∧
    (SharpCut.Examples.SquarePyramid.cutBody).extremePoints ℝ = SharpCut.Examples.SquarePyramid.frustumVertices :=
  ⟨SharpCut.Examples.SquarePyramid.body_eq_vertex_hull,SharpCut.Examples.SquarePyramid.body_extremePoints,
    SharpCut.Examples.SquarePyramid.cut_eq_vertex_hull,SharpCut.Examples.SquarePyramid.cut_extremePoints⟩

example : SharpCut.Examples.SquarePyramid.pyramidVertices =
    {SharpCut.Examples.SquarePyramid.point 0 0 3} ∪ Set.range
      ![SharpCut.Examples.SquarePyramid.point (-Real.sqrt 2) (-Real.sqrt 2) (-1),
        SharpCut.Examples.SquarePyramid.point (Real.sqrt 2) (-Real.sqrt 2) (-1),
        SharpCut.Examples.SquarePyramid.point (-Real.sqrt 2) (Real.sqrt 2) (-1),
        SharpCut.Examples.SquarePyramid.point (Real.sqrt 2) (Real.sqrt 2) (-1)] := rfl

example (i : Fin 4) :
    (SharpCut.Examples.SquarePyramid.body ∩ {p | ⟪SharpCut.Examples.SquarePyramid.frame.contact i.succ,p⟫ = 1}) =
      convexHull ℝ (Set.range (SharpCut.Examples.SquarePyramid.sideTriangle i)) ∧
    AffineIndependent ℝ (SharpCut.Examples.SquarePyramid.sideTriangle i) :=
  SharpCut.Examples.SquarePyramid.four_triangular_facets i

example : (SharpCut.Examples.SquarePyramid.body ∩ {p | ⟪SharpCut.Examples.SquarePyramid.frame.contact 0,p⟫ = 1}) =
    convexHull ℝ (Set.range (SharpCut.Examples.SquarePyramid.squareVertices (Real.sqrt 2) (-1))) :=
  SharpCut.Examples.SquarePyramid.base_facet_hull

example (i : Fin 5) : ∃ x : SharpCut.V 3, 1 < ⟪SharpCut.Examples.SquarePyramid.frame.contact i,x⟫ ∧
    ∀ j : Fin 5, j ≠ i → ⟪SharpCut.Examples.SquarePyramid.frame.contact j,x⟫ ≤ 1 :=
  SharpCut.Examples.SquarePyramid.defining_facet_nonredundant i

example : (SharpCut.Examples.SquarePyramid.body.extremePoints ℝ).ncard = 5 :=
  SharpCut.Examples.SquarePyramid.five_extreme_points

run_cmd Lean.logInfo "SHARPCUT_SIGNED_PYRAMID_STATEMENTS_PASS"

/-- SUP-04: every positive dimension has an actual regular simplex, explicit facet normals, and actual sharp cut volume. -/
example (n : ℕ) (hn : 1 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    ∃ u : Fin (n+1) → SharpCut.V n, ∃ p : Fin (n+1) → SharpCut.V n, ∃ K : Set (SharpCut.V n),
      (∀ i, ‖u i‖ = 1) ∧ (∀ i j, i ≠ j → ⟪u i,u j⟫ = -1/(n : ℝ)) ∧
      (∑ i, u i) = 0 ∧ (∑ i, SharpCut.outer (u i)) = (((n : ℝ)+1)/(n : ℝ)) • (1 : SharpCut.MatR n) ∧
      (∀ i, p i = -(n : ℝ) • u i) ∧ AffineIndependent ℝ p ∧ K = convexHull ℝ (Set.range p) ∧
      K = {x | ∀ i, ⟪u i,x⟫ ≤ 1} ∧ SharpCut.IsConvexBody K ∧ SharpCut.IsJohnNormalized K ∧
      Khachiyan.johnEllipsoid K = SharpCut.unitBall n ∧ (∀ i, u i ∈ frontier K) ∧
      SharpCut.maxEllipsoidVolume (K ∩ SharpCut.centralHalfspace 0 (-u 0)) =
        ENNReal.ofReal (SharpCut.sharpRatio n)*SharpCut.maxEllipsoidVolume K :=
  SharpCut.Simplex.exists_regular_simplex n hn

/-- Regularity is certified by affine independence and the same edge length for every distinct vertex pair. -/
example (m : ℕ) :
    AffineIndependent ℝ (SharpCut.Simplex.vertex m) ∧
    SharpCut.Simplex.body m = convexHull ℝ (Set.range (SharpCut.Simplex.vertex m)) ∧
    SharpCut.IsConvexBody (SharpCut.Simplex.body m) ∧ SharpCut.IsJohnNormalized (SharpCut.Simplex.body m) ∧
    (∑ i, SharpCut.Simplex.vertex m i) = 0 ∧
    (∀ i j, i ≠ j → ‖SharpCut.Simplex.vertex m i-SharpCut.Simplex.vertex m j‖^2 =
      2*((m : ℝ)+1)*((m : ℝ)+2)) :=
  SharpCut.Simplex.regular_simplex_geometry m

example (m : ℕ) (i : Fin (m+2)) : (SharpCut.Simplex.regularFrame m).weight i = ((m : ℝ)+1)/((m : ℝ)+2) := by
  simpa only [SharpCut.Simplex.johnWeight,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
    SharpCut.Simplex.regular_weights m i

/-- The exact centered vertex covariance will also be used in the arbitrary affine-simplex transport. -/
example (m : ℕ) : (∑ i, SharpCut.outer (SharpCut.Simplex.vertex m i)) =
    (((m : ℝ)+1)*((m : ℝ)+2)) • (1 : SharpCut.MatR (m+1)) :=
  SharpCut.Simplex.vertex_outer_sum m

/-- The translated shape has the original determinant, axis support, pole support and latitude support values. -/
example {n : ℕ} (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    (SharpCut.Sharpness.modelShape v).PosDef ∧ (SharpCut.Sharpness.modelShape v).det = SharpCut.sharpRatio n ∧
    ⟪v,(-1/2 : ℝ) • v⟫ = -1/2 ∧ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (SharpCut.Sharpness.modelShape v) v‖ = 1/2 ∧
    ⟪-v,(-1/2 : ℝ) • v⟫ = 1/2 ∧ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (SharpCut.Sharpness.modelShape v) (-v)‖ = 1/2 :=
  ⟨SharpCut.Sharpness.modelShape_posDef hn v hv,SharpCut.Sharpness.modelShape_det hn v hv,
    SharpCut.Simplex.model_axis_support_values hn v hv⟩

example {n : ℕ} (hn : 2 ≤ n) (v u : SharpCut.V n) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (hs : ⟪u,v⟫ = 1/(n : ℝ)) :
    ⟪u,(-1/2 : ℝ) • v⟫ = -(1/(n : ℝ))/2 ∧
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (SharpCut.Sharpness.modelShape v) u‖ = 1+(1/(n : ℝ))/2 ∧
    Real.sqrt ((1/(n : ℝ))^2/4+(1-(1/(n : ℝ))^2)/(1-1/(n : ℝ))) = 1+(1/(n : ℝ))/2 :=
by
  have h := SharpCut.Simplex.model_latitude_support_values hn v u hv hu hs
  exact ⟨h.1,h.2,SharpCut.Simplex.model_latitude_square_root hn⟩

/-- Ordinary Lebesgue volume of the old ball is halved; this is an explicit actual-set measure assertion. -/
example {n : ℕ} (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    MeasureTheory.volume (SharpCut.unitBall n ∩ {x | ⟪v,x⟫ ≤ 0}) =
      ENNReal.ofReal (1/2 : ℝ)*MeasureTheory.volume (SharpCut.unitBall n) := by
  simpa only [SharpCut.centralHalfspace,sub_zero] using SharpCut.Geometry.unit_ball_half_volume v hv

/-- Full Figure 1: the actual old ball, actual new optimum with semiaxes 1/2 and sqrt2, exact area ratio and used space outside the old ball. -/
example :
    SharpCut.IsConvexBody (SharpCut.Simplex.body 1) ∧ AffineIndependent ℝ (SharpCut.Simplex.vertex 1) ∧
    Khachiyan.johnEllipsoid (SharpCut.Simplex.body 1) = SharpCut.unitBall 2 ∧
    SharpCut.IsMaxDet (SharpCut.Simplex.body 1 ∩ SharpCut.centralHalfspace 0 (SharpCut.Sharpness.axis 1))
      ((-1/2 : ℝ) • SharpCut.Sharpness.axis 1) (Matrix.diagonal ![(1/2 : ℝ),Real.sqrt 2]) ∧
    SharpCut.maxEllipsoidVolume (SharpCut.Simplex.body 1 ∩ SharpCut.centralHalfspace 0 (SharpCut.Sharpness.axis 1)) =
      ENNReal.ofReal (1/Real.sqrt 2)*SharpCut.maxEllipsoidVolume (SharpCut.Simplex.body 1) ∧
    (SharpCut.maxEllipsoidVolume (SharpCut.Simplex.body 1 ∩ SharpCut.centralHalfspace 0 (SharpCut.Sharpness.axis 1))).toReal /
      (SharpCut.maxEllipsoidVolume (SharpCut.Simplex.body 1)).toReal = 1/Real.sqrt 2 ∧
    MeasureTheory.volume (SharpCut.unitBall 2 ∩ SharpCut.centralHalfspace 0 (SharpCut.Sharpness.axis 1)) =
      ENNReal.ofReal (1/2 : ℝ)*MeasureTheory.volume (SharpCut.unitBall 2) ∧
    (∃ x ∈ Khachiyan.johnEllipsoid (SharpCut.Simplex.body 1 ∩ SharpCut.centralHalfspace 0 (SharpCut.Sharpness.axis 1)),
      x ∈ SharpCut.Simplex.body 1 ∩ SharpCut.centralHalfspace 0 (SharpCut.Sharpness.axis 1) ∧ x ∉ SharpCut.unitBall 2) :=
  SharpCut.Simplex.figure_one_geometry

run_cmd Lean.logInfo "SHARPCUT_REGULAR_SIMPLEX_MODEL_STATEMENTS_PASS"

/-- SUP-25: all positive dimensions, arbitrary affinely independent vertices and the actual canonical John shape. -/
example (n : ℕ) (hn : 1 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    ∀ p : Fin (n+1) → SharpCut.V n, AffineIndependent ℝ p →
      let K := convexHull ℝ (Set.range p)
      let c := (1/((n : ℝ)+1)) • (∑ i, p i)
      SharpCut.IsConvexBody K ∧ Khachiyan.johnCenter K = c ∧ (Khachiyan.johnShape K).PosDef ∧
      (Khachiyan.johnShape K)^2 = (1/((n : ℝ)*((n : ℝ)+1))) • (∑ i, SharpCut.outer (p i-c)) ∧
      SharpCut.IsMaxDet K c (Khachiyan.johnShape K) :=
  SharpCut.Simplex.affine_simplex_shape_formula n hn

/-- Every interpolation vertex is actually mapped, and invertibility is derived from affine independence. -/
example {m : ℕ} (p : Fin (m+2) → SharpCut.V (m+1)) (hp : AffineIndependent ℝ p) :
    (∀ i, Matrix.toEuclideanCLM (𝕜 := ℝ) (SharpCut.Simplex.interpolationMatrix p) (SharpCut.Simplex.vertex m i) =
      p i-SharpCut.Simplex.centroid p) ∧ IsUnit (SharpCut.Simplex.interpolationMatrix p).det ∧
    SharpCut.Simplex.interpolationAffine p '' SharpCut.Simplex.body m = convexHull ℝ (Set.range p) :=
  ⟨SharpCut.Simplex.interpolation_vertex p,SharpCut.Simplex.interpolation_det_isUnit p hp,
    SharpCut.Simplex.affine_image_body p⟩

/-- A general invertible C has both left-polar orthogonality identities; no positive determinant or symmetry is assumed. -/
example {m : ℕ} (C : SharpCut.MatR (m+1)) (hC : IsUnit C.det) :
    let S := CFC.sqrt (C*Cᵀ)
    S.PosDef ∧ S^2 = C*Cᵀ ∧ (S⁻¹*C)*(S⁻¹*C)ᵀ = 1 ∧ (S⁻¹*C)ᵀ*(S⁻¹*C) = 1 ∧ S*(S⁻¹*C) = C :=
  ⟨Khachiyan.affineShape_posDef hC,SharpCut.Simplex.affineShape_square C,
    (SharpCut.Simplex.shapeRotation_orthogonal C hC).1,(SharpCut.Simplex.shapeRotation_orthogonal C hC).2,
    SharpCut.Simplex.shapeRotation_factor C hC⟩

example {m : ℕ} (p : Fin (m+2) → SharpCut.V (m+1)) (hp : AffineIndependent ℝ p) :
    SharpCut.IsMaxDet (convexHull ℝ (Set.range p)) (SharpCut.Simplex.centroid p)
      (CFC.sqrt (SharpCut.Simplex.interpolationMatrix p*(SharpCut.Simplex.interpolationMatrix p)ᵀ)) :=
  SharpCut.Simplex.affine_simplex_isMaxDet p hp

/-- The formula describes actual maximal Lebesgue volume and the actual John ellipsoid, not only an algebraic covariance. -/
example {n : ℕ} [NeZero n] (hn : 1 ≤ n) (p : Fin (n+1) → SharpCut.V n) (hp : AffineIndependent ℝ p) :
    let K := convexHull ℝ (Set.range p)
    let c := (1/((n : ℝ)+1)) • (∑ i, p i)
    Khachiyan.johnEllipsoid K = Khachiyan.ellipsoid c (Khachiyan.johnShape K) ∧
    SharpCut.maxEllipsoidVolume K = ENNReal.ofReal (Khachiyan.johnShape K).det*MeasureTheory.volume (SharpCut.unitBall n) := by
  have h := SharpCut.Simplex.affine_simplex_shape_formula n hn p hp
  have hmax := Khachiyan.john_isMaxDet h.1
  refine ⟨?_,hmax.maxEllipsoidVolume_eq_det⟩
  rw [Khachiyan.johnEllipsoid,h.2.1]

run_cmd Lean.logInfo "SHARPCUT_AFFINE_SIMPLEX_STATEMENTS_PASS"

/-- Explicit (2.6)-(2.7) intermediate chains, including full trace-mean AM-GM for the positive conjugate. -/
example {n N : ℕ} (hn : 1 ≤ n) {g q : Fin N → SharpCut.V n} {β α : Fin N → ℝ}
    {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hp : SharpCut.Optimization.PrimalFeasible g β c A) (hd : SharpCut.Optimization.DualFeasible g β α q) :
    let M := SharpCut.Optimization.aggregate g q
    let Y := CFC.sqrt M*A*CFC.sqrt M
    A.det*M.det = Y.det ∧ Y.det = ∏ i, (SharpCut.Optimization.matchingMatrix_posDef A M hp.1 hd.positive).isHermitian.eigenvalues i ∧
    Y.det ≤ ((A*M).trace/(n : ℝ))^n ∧ ((A*M).trace/(n : ℝ))^n ≤ 1 :=
  SharpCut.Paper.normalized_determinant_chain hn hp hd

example {n N : ℕ} {g q : Fin N → SharpCut.V n} {β α : Fin N → ℝ}
    {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hp : SharpCut.Optimization.PrimalFeasible g β c A) (hd : SharpCut.Optimization.DualFeasible g β α q) :
    (A*SharpCut.Optimization.aggregate g q).trace = ∑ r, ⟪q r,Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫ ∧
    (∑ r, ⟪q r,Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)⟫) ≤ ∑ r, α r*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖ ∧
    (∑ r, α r*‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (g r)‖) ≤ ∑ r, α r*(β r-⟪g r,c⟫) ∧
    (∑ r, α r*(β r-⟪g r,c⟫)) = (n : ℝ) :=
  SharpCut.Paper.normalized_trace_chain hp hd

/-- Original (2.19), with r=the actual Euclidean norm and every finite moment retained. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) {x : SharpCut.V n} (hx : x ∈ F.polytope) :
    0 ≤ ∑ i, F.weight i*(1-⟪F.contact i,x⟫)*(‖x‖+⟪F.contact i,x⟫) ∧
    (∑ i, F.weight i*(1-⟪F.contact i,x⟫)*(‖x‖+⟪F.contact i,x⟫)) = (n : ℝ)*‖x‖-‖x‖^2 :=
  ⟨SharpCut.Paper.frame_radius_polynomial_nonneg F hx,SharpCut.Paper.frame_radius_polynomial F x⟩

example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) (i : Fin N) :
    F.weight i*(1-SharpCut.Certificate.cutWeight n) ≤ SharpCut.Certificate.originalWeight F v i ∧
    F.weight i/4 ≤ F.weight i*(1-SharpCut.Certificate.cutWeight n) :=
  SharpCut.Paper.frame_balanced_weight_chain F hn v hv i

run_cmd Lean.logInfo "SHARPCUT_INITIAL_EQUATION_CHAINS_PASS"


/-- Literal expanded cone trace identity in (4.2), before normalized feasibility. -/
example {n N : ℕ} {g q : Fin N → SharpCut.V n} {β α : Fin N → ℝ}
    {c : SharpCut.V n} {A : SharpCut.MatR n} (hA : A.IsHermitian) :
    SharpCut.Optimization.coneGap g β α q c A =
      (∑ r, α r*β r)-⟪c,∑ r, α r • g r⟫-(A*SharpCut.Optimization.aggregate g q).trace :=
  SharpCut.Paper.cone_gap_expanded hA

example {n : ℕ} (hn : 1 ≤ n) (A M : SharpCut.MatR n) (hA : A.PosDef) (hM : M.PosDef) :
    Real.log (SharpCut.sharpRatio n*M.det)-Real.log M.det-Real.log A.det =
      Real.log (SharpCut.sharpRatio n/A.det) :=
  SharpCut.Paper.deficit_cancellation hn A M hA hM

/-- The full zero-loss certificate in (5.3), rather than just the model shape. -/
example {n N : ℕ} (hn : 2 ≤ n) {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K)
    (hJ : SharpCut.IsJohnNormalized K) (F : SharpCut.JohnFrame n N) (hs : F.Supports K)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hA : SharpCut.IsFeasible (K ∩ SharpCut.centralHalfspace 0 v) c A)
    (hz : SharpCut.Gap.volumeDeficit n A = 0) :
    SharpCut.Gap.geometricGap F v = 0 ∧ SharpCut.Gap.frameConeGap F v c A = 0 ∧
    SharpCut.Optimization.pairDivergence A (SharpCut.Gap.frameMatrix F v) = 0 ∧
    SharpCut.Certificate.frameDefect F v = 0 ∧
    SharpCut.Certificate.unrotatedQ F v = SharpCut.Certificate.inverseModel v ∧
    SharpCut.Gap.frameMatrix F v = SharpCut.Certificate.inverseModel v ∧
    SharpCut.Certificate.polarRotation (SharpCut.Certificate.unrotatedQ F v) = 1 ∧
    A = SharpCut.Sharpness.modelShape v :=
  SharpCut.Paper.zero_deficit_certificate hn hK hJ F hs v hv hA hz

example {n N : ℕ} (hn : 2 ≤ n) {K : Set (SharpCut.V n)} (hK : SharpCut.IsConvexBody K)
    (hJ : SharpCut.IsJohnNormalized K) (F : SharpCut.JohnFrame n N) (hs : F.Supports K)
    (v : SharpCut.V n) (hv : ‖v‖ = 1) {c : SharpCut.V n} {A : SharpCut.MatR n}
    (hA : SharpCut.IsFeasible (K ∩ SharpCut.centralHalfspace 0 v) c A)
    (hz : SharpCut.Gap.volumeDeficit n A = 0) :
    (∀ i, SharpCut.Certificate.originalWeight F v i*
      (1-⟪F.contact i,c⟫-‖Matrix.toEuclideanCLM (𝕜 := ℝ)
        (SharpCut.Sharpness.modelShape v) (F.contact i)‖) = 0) ∧
    (∀ i, ⟪F.contact i,c-SharpCut.Sharpness.modelCenter v⟫ = 0) ∧
    ‖c-SharpCut.Sharpness.modelCenter v‖^2 =
      ∑ i, F.weight i*⟪F.contact i,c-SharpCut.Sharpness.modelCenter v⟫^2 ∧
    (∑ i, F.weight i*⟪F.contact i,c-SharpCut.Sharpness.modelCenter v⟫^2) = 0 :=
  SharpCut.Paper.zero_deficit_support_center hn hK hJ F hs v hv hA hz

example {n : ℕ} (v x : SharpCut.V n) (hv : ‖v‖ = 1)
    (hx : x ∈ Metric.closedBall ((-1/4 : ℝ) • v) (1/8 : ℝ)) :
    ‖x‖ ≤ 3/8 ∧ (3/8 : ℝ) < 1 ∧ ⟪v,x⟫ ≤ -1/8 ∧ (-1/8 : ℝ) < 0 :=
  SharpCut.Paper.initialization_strict_bounds v x hv hx

run_cmd Lean.logInfo "SHARPCUT_GAP_EQUATION_CHAINS_PASS"


/-- The complete literal theta chain in (8.21) on its actual scalar domain. -/
example (theta1 theta2 : ℝ) (h1 : 0 ≤ theta1) (h12 : theta1 ≤ theta2) (h2 : theta2 < 1) :
    1-(1-theta2)/(1-theta1) ≤ Real.log ((1-theta1)/(1-theta2)) ∧
    1-(1-theta2)/(1-theta1) = (theta2-theta1)/(1-theta1) ∧
    theta2-theta1 ≤ (theta2-theta1)/(1-theta1) :=
  SharpCut.Paper.theta_log_chain theta1 theta2 h1 h12 h2

example (H kappa tau z delta : ℝ) (hH : 0 < H) (hkappa : 0 ≤ kappa) (htau : 0 ≤ tau)
    (hz : 0 < z) (hdelta : 0 ≤ delta) (hd : 0 < H*z-tau) :
    0 ≤ delta/(z+delta+kappa) ∧ delta/(z+delta+kappa) ≤ H*delta/(H*(z+delta)-tau) ∧
    H*delta/(H*(z+delta)-tau) < 1 :=
  SharpCut.Paper.theta_parameter_bounds H kappa tau z delta hH hkappa htau hz hdelta hd

example (H kappa tau z delta : ℝ) (hz : z+kappa ≠ 0) (hd : H*z-tau ≠ 0)
    (hz0 : z+delta+kappa ≠ 0) (hd0 : H*(z+delta)-tau ≠ 0) :
    (1-delta/(z+delta+kappa))/(1-H*delta/(H*(z+delta)-tau)) =
      ((z+kappa)/(H*z-tau))/((z+delta+kappa)/(H*(z+delta)-tau)) ∧
    H*delta/(H*(z+delta)-tau)-delta/(z+delta+kappa) =
      delta*(H/(H*(z+delta)-tau)-1/(z+delta+kappa)) :=
  SharpCut.Paper.theta_drop_identities H kappa tau z delta hz hd hz0 hd0

example {n : ℕ} (hn : 2 ≤ n) (v : SharpCut.V n) (hv : ‖v‖ = 1) :
    (SharpCut.Certificate.modelF0 v).det =
      (2-SharpCut.inverseDimension n)^(n+1)/((2 : ℝ)^n*(1-SharpCut.inverseDimension n)) :=
  SharpCut.Paper.model_determinant_closed hn v hv

/-- The exact polynomial comparison in (8.62), before its final lower bound. -/
example (sigma z r omega value : ℝ) (hs : 0 ≤ sigma) (hz : 0 ≤ z)
    (hgram : (2/3-sigma)*r+omega ≤ 5*sigma/12*((2/3)^2-2/3*sigma+(z-sigma)/4))
    (hvar : ((1+sigma)*(1+4*sigma)-z)*r-4*(1+sigma)*omega ≤
      (5/8-5*sigma/6)/2*z*(1+sigma+z))
    (hvalue : value = (1-5*sigma/12)*(1+sigma+(z-sigma)/4)-((1+sigma)*r-omega)) :
    72*sigma*(1+sigma)+(171/4-53/4*sigma+75*sigma^2)*z+(-333/4+75*sigma)*z^2 ≤
      108*((11/3)*(1+sigma)-z)*(value-1) :=
  SharpCut.Paper.three_polynomial_elimination sigma z r omega value hs hz hgram hvar hvalue

example (sigma z r omega : ℝ) (hs : 0 ≤ sigma) (hz : 0 ≤ z)
    (hdelta : 0 < (11/3 : ℝ)*(1+sigma)-z)
    (hgram : (2/3-sigma)*r+omega ≤ 5*sigma/12*((2/3)^2-2/3*sigma+(z-sigma)/4))
    (hvar : ((1+sigma)*(1+4*sigma)-z)*r-4*(1+sigma)*omega ≤
      (5/8-5*sigma/6)/2*z*(1+sigma+z)) :
    (1+sigma)*r-omega ≤
      ((5*sigma/12*((2/3)^2-2/3*sigma+(z-sigma)/4))*(3*(1+sigma)+z)+
        (5/6)*(5/8-5*sigma/6)*z*(1+sigma+z))/((11/3)*(1+sigma)-z) :=
  SharpCut.Paper.three_adjugate_elimination sigma z r omega hs hz hdelta hgram hvar

run_cmd Lean.logInfo "SHARPCUT_DETERMINANT_EQUATION_CHAINS_PASS"


/-- The original selected value equality in (8.54) retains both variational terms. -/
example {n N : ℕ} (F : SharpCut.JohnFrame n N) (hn : 2 ≤ n) (v : SharpCut.V n)
    (hv : ‖v‖ = 1) (hL : 0 < SharpCut.Certificate.couplingL F v) :
    let w := Matrix.toEuclideanCLM (𝕜 := ℝ) (SharpCut.Certificate.couplingK F v)⁻¹
      (SharpCut.Certificate.transverseCoupling F v)
    let q := (1/SharpCut.Certificate.couplingL F v) • w
    2*SharpCut.Certificate.couplingLinearTest F v (SharpCut.Certificate.couplingZ F v) q-
      SharpCut.Certificate.couplingQuadraticTest F v (SharpCut.Certificate.couplingZ F v) q =
      SharpCut.Certificate.transverseDeformation F v+‖w‖^2/SharpCut.Certificate.couplingL F v ∧
    SharpCut.Certificate.transverseDeformation F v+‖w‖^2/SharpCut.Certificate.couplingL F v ≤
      SharpCut.Certificate.transverseSigma F v/2 :=
  SharpCut.Paper.selected_coupling_value F hn v hv hL

run_cmd Lean.logInfo "SHARPCUT_SELECTED_VARIATIONAL_EQUATION_PASS"


/-- EXT-04 uses the actual previously proved uniform bound and uniform optimality. -/
example {n : ℕ} [NeZero n] {K : Set (Khachiyan.V n)} (hK : Khachiyan.IsConvexBody K)
    {p : Khachiyan.V n} (hp : p ≠ 0) :
    Khachiyan.IsConvexBody (K ∩ Khachiyan.centralHalfspace (Khachiyan.johnCenter K) p) ∧
    Khachiyan.maxEllipsoidVolume (K ∩ Khachiyan.centralHalfspace (Khachiyan.johnCenter K) p) ≤
      ENNReal.ofReal Khachiyan.rStar*Khachiyan.maxEllipsoidVolume K :=
  Khachiyan.t01 hK hp

example {r : ℝ} (hr : r < Khachiyan.rStar) :
    ∃ (n : ℕ) (hn : 2 ≤ n),
      letI : NeZero n := ⟨by omega⟩
      ∃ (K : Set (Khachiyan.V n)) (p : Khachiyan.V n),
        Khachiyan.IsConvexBody K ∧ p ≠ 0 ∧
        r*(Khachiyan.maxEllipsoidVolume K).toReal <
          (Khachiyan.maxEllipsoidVolume (K ∩ Khachiyan.centralHalfspace (Khachiyan.johnCenter K) p)).toReal :=
  Khachiyan.sharp_constant hr

example : Khachiyan.rStar = Real.sqrt (Real.exp 1)/2 :=
  Khachiyan.Scalar.rStar_eq_sqrt_exp_one

run_cmd Lean.logInfo "SHARPCUT_REUSED_UNIFORM_EXTERNAL_PASS"
