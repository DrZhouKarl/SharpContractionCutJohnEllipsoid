import SharpCut.Certificate.GramCoupling

/-!
# Complete intrinsic form of Lemma 8.5

The transverse identity is the orthogonal projector on v-perp. Bilinear
identities describe every block of the actual normalized certificate; strict
Loewner inequalities on v-perp are expressed by all nonzero transverse tests.
This coordinate-free statement is transported by Geometry.inBasis, whose
orthonormal basis, determinant and Euclidean norm bridges are proved.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open Matrix
namespace SharpCut.Certificate
variable {n N : ℕ}

theorem transversePerturbation_explicit (F : JohnFrame n N) (v : V n) :
    transversePerturbation F v = (-(1/(2-inverseDimension n))) •
      (∑ i, (F.weight i/(1-boostParameter n*height F v i)*(height F v i-inverseDimension n)) •
        outer (transverse v (F.contact i))) := by
  unfold transversePerturbation transverseMatrixMoment
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, smul_smul, ← sub_smul,
    pow_one, pow_zero, mul_one]
  congr 1
  funext i
  congr 1
  ring

theorem transversePerturbation_isHermitian (F : JohnFrame n N) (v : V n) :
    (transversePerturbation F v).IsHermitian := by
  rw [transversePerturbation_explicit]
  let M : Fin N → MatR n := fun i =>
    (F.weight i/(1-boostParameter n*height F v i)*(height F v i-inverseDimension n)) •
      outer (transverse v (F.contact i))
  have hM (i : Fin N) : (M i).IsHermitian :=
    (Khachiyan.outer_posSemidef _).isHermitian.smul
      (show IsSelfAdjoint (F.weight i/(1-boostParameter n*height F v i)*
        (height F v i-inverseDimension n)) by rfl)
  have h : (∑ i, M i).IsHermitian :=
    (isSelfAdjoint_sum (R := MatR n) Finset.univ (fun i hi => (hM i).isSelfAdjoint)).isHermitian
  exact h.smul (show IsSelfAdjoint (-(1/(2-inverseDimension n))) by rfl)

theorem transverseCoupling_contact_sum (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    transverseCoupling F v =
      (-Real.sqrt (1-inverseDimension n)/(inverseDimension n*Real.sqrt (2-inverseDimension n))) •
        (∑ i, (F.weight i/(1-boostParameter n*height F v i)*(height F v i-inverseDimension n)) •
          transverse v (F.contact i)) := by
  rw [transverseCoupling_explicit F hn v hv]
  congr 1
  unfold transverseVectorMoment
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, smul_smul, ← sub_smul,
    pow_one, pow_zero, mul_one]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

/-- Lemma 8.5: exact blocks, explicit contact formulas, ranges and strict Gram constraints. -/
theorem block_identities_and_constraints (F : JohnFrame n N) (hn : 2 ≤ n)
    (v : V n) (hv : ‖v‖ = 1) :
    ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizedCertificate F v) v⟫ = 1-axialDeficit F v ∧
    (∀ x y : V n, ⟪x, v⟫ = 0 → ⟪y, v⟫ = 0 →
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizedCertificate F v) y⟫ =
        ⟪x, y⟫+⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v) y⟫) ∧
    (∀ x : V n, ⟪x, v⟫ = 0 →
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizedCertificate F v) v⟫ = ⟪x, transverseCoupling F v⟫) ∧
    (transversePerturbation F v).trace = transverseSigma F v ∧
    (transversePerturbation F v).IsHermitian ∧
    axialDeficit F v = (2-inverseDimension n)/4*transverseSigma F v ∧
    transversePerturbation F v = (-(1/(2-inverseDimension n))) •
      (∑ i, (F.weight i/(1-boostParameter n*height F v i)*(height F v i-inverseDimension n)) •
        outer (transverse v (F.contact i))) ∧
    transverseCoupling F v =
      (-Real.sqrt (1-inverseDimension n)/(inverseDimension n*Real.sqrt (2-inverseDimension n))) •
        (∑ i, (F.weight i/(1-boostParameter n*height F v i)*(height F v i-inverseDimension n)) •
          transverse v (F.contact i)) ∧
    (0 ≤ transverseSigma F v ∧ transverseSigma F v ≤
      2*(1-inverseDimension n)/(2-inverseDimension n+(inverseDimension n)^2)) ∧
    (0 ≤ frameDefect F v ∧ frameDefect F v ≤ 2) ∧
    (axialDeficit F v • outer v-cross v (transverseCoupling F v)-cross (transverseCoupling F v) v+
      (cutWeight n • projector v-transversePerturbation F v)).PosSemidef ∧
    (∀ u : V n, ⟪u, v⟫ = 0 → u ≠ 0 →
      -(1/2 : ℝ)*‖u‖^2 < ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v) u⟫ ∧
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (transversePerturbation F v) u⟫ < cutWeight n*‖u‖^2) := by
  refine ⟨normalized_axial_bilinear F hn v hv,
    (fun x y hx hy => normalized_transverse_bilinear F hn v x y hv hx hy),
    (fun x hx => normalized_mixed_bilinear F hn v x hv hx),
    transversePerturbation_trace F hn v hv, transversePerturbation_isHermitian F v,
    axialDeficit_sigma F hn v, transversePerturbation_explicit F v, transverseCoupling_contact_sum F hn v hv,
    transverseSigma_range F hn v hv, ?_, ?_,
    (fun u hu hu0 => transverse_strict_bounds F hn v u hv hu hu0)⟩
  · have h := frameDefect_range F hn v hv
    exact ⟨h.1, h.2.2⟩
  · rw [← contactGram_identity F hn v hv]
    exact contactGram_posSemidef F hn v hv

end SharpCut.Certificate
