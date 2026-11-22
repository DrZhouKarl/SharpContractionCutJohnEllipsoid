# Theorem map

All listed paper results are certified. Names below are actual Lean declarations.
The exact paper statements and all display assignments are in [paper_inventory.json](paper_inventory.json); [equation_map.json](equation_map.json) records every numbered-equation correspondence.

## Named results

| Paper | Stable ID | Lean declaration | Source |
| --- | --- | --- | --- |
| Lemma 2.1 | `lem-certificate` | `SharpCut.Optimization.volume_certificate` | [source](SharpCut/Optimization/Certificate.lean#L117) |
| Lemma 2.2 | `lem-john` | `SharpCut.Geometry.john_contact_iff` | [source](SharpCut/John/Necessity.lean#L100) |
| Proposition 2.3 | `prop-exact-duality` | `SharpCut.Optimization.exact_duality` | [source](SharpCut/Optimization/Exact/Theorem.lean#L69) |
| Proposition 2.4 | `prop-kkt` | `SharpCut.Optimization.kkt_optimality_and_contacts` | [source](SharpCut/Optimization/Exact/RecoveredMoments.lean#L78) |
| Lemma 2.5 | `lem-reduction` | `SharpCut.Geometry.contact_reduction` | [source](SharpCut/John/Reduction.lean#L29) |
| Theorem 3.1 | `thm-sharp` | `SharpCut.Geometry.sharp_central_cut_contraction` | [source](SharpCut/Geometry/SharpTheorem.lean#L82) |
| Theorem 3.2 | `thm-frame-bound` | `SharpCut.Certificate.john_frame_certificate_bound` | [source](SharpCut/Certificate/FrameBound.lean#L39) |
| Proposition 4.1 | `prop-gap` | `SharpCut.Gap.exact_volume_deficit`; `SharpCut.Gap.affine_optimal_volume_deficit` | [source](SharpCut/Gap/Exact.lean#L51) |
| Lemma 4.2 | `lem-matching` | `SharpCut.Gap.matrix_matching` | [source](SharpCut/Gap/Matching.lean#L46) |
| Theorem 5.1 | `thm-equality` | `SharpCut.Equality.equality_classification` | [source](SharpCut/Equality/Theorem.lean#L46) |
| Proposition 5.2 | `prop-extremizers` | `SharpCut.Equality.transverse_extremal_construction` | [source](SharpCut/Equality/TransverseFamily.lean#L146) |
| Lemma 6.1 | `lem-geometric-control` | `SharpCut.Stability.geometric_control` | [source](SharpCut/Stability/LocalCoercivity.lean#L112) |
| Theorem 6.2 | `thm-stability` | `SharpCut.Stability.dimension_independent_stability` | [source](SharpCut/Stability/Theorem.lean#L39) |
| Corollary 7.1 | `cor-iteration` | `SharpCut.Applications.successive_exact_central_cuts` | [source](SharpCut/Applications/Iteration.lean#L92) |
| Theorem 8.1 | `thm-determinant` | `SharpCut.Determinant.quantitative_frame_determinant` | [source](SharpCut/Determinant/Theorem.lean#L27) |
| Lemma 8.2 | `lem-lifted-bound` | `SharpCut.Determinant.lifted_determinant_bound` | [source](SharpCut/Determinant/LiftedBound.lean#L209) |
| Lemma 8.3 | `lem-hermite` | `SharpCut.Determinant.interpolation_loss` | [source](SharpCut/Determinant/InterpolationLoss.lean#L56) |
| Lemma 8.4 | `lem-rational` | `SharpCut.Scalar.uniform_certificate` | [source](SharpCut/Scalar/LossIntegral.lean#L135) |
| Lemma 8.5 | `lem-moments` | `SharpCut.Certificate.block_identities_and_constraints` | [source](SharpCut/Certificate/BlockConstraints.lean#L62) |
| Lemma 8.6 | `lem-variational` | `SharpCut.Certificate.direct_coupling_bound` | [source](SharpCut/Certificate/DirectCoupling.lean#L71) |
| Proposition 8.7 | `prop-dim3` | `SharpCut.Determinant.dimension_three_determinant` | [source](SharpCut/Determinant/DimensionThree.lean#L15) |
| Proposition 9.1 | `prop-gap-control` | `SharpCut.Gap.cone_sum_of_squares`; `SharpCut.Gap.quantitative_complementarity` | [source](SharpCut/Gap/Complementarity.lean#L13) |
| Lemma 9.2 | `lem-residual` | `SharpCut.Stability.geometric_residual` | [source](SharpCut/Stability/Residual.lean#L14) |
| Lemma 9.3 | `lem-local` | `SharpCut.Stability.local_coercivity` | [source](SharpCut/Stability/LocalCoercivity.lean#L90) |
| Proposition 10.1 | `prop-polar` | `SharpCut.Optimization.common_contraction_optimal` | [source](SharpCut/Optimization/PolarContraction.lean#L82) |
| Lemma 10.2 | `lem-cauchy` | `SharpCut.Coupled.general_cauchy_transverse` | [source](SharpCut/Coupled/Coordinates.lean#L101) |
| Lemma 10.3 | `lem-cauchy-minus` | `SharpCut.Coupled.complementary_cauchy_transverse` | [source](SharpCut/Coupled/Complementary.lean#L83) |
| Lemma 10.4 | `lem-inverse-trace` | `SharpCut.Coupled.InverseTrace.inverse_trace_interpretation` | [source](SharpCut/Coupled/InverseTrace/TransverseTheorem.lean#L82) |

## Supporting contracts

| ID | Mathematical content | Status |
| --- | --- | --- |
| SUP-01 | Geometry, support, affine transport, existence/uniqueness and actual volume | Verified |
| SUP-02 | Concavity of logdet, convex feasibility and Lorentz self-duality | Verified |
| SUP-03 | General and symmetric John rounding; contact-polytope sharp supremum | Verified |
| SUP-04 | Model determinant, regular-simplex existence, contacts and support values | Verified |
| SUP-05 | Balanced weights, Lorentz unit directions, domain inequalities and zero chi | Verified |
| SUP-06 | Left polar construction, aggregate identity and determinant preservation | Verified |
| SUP-07 | Generic gap identity and all zero sets | Verified |
| SUP-08 | Signed transverse examples and exact square pyramid | Verified |
| SUP-09 | Constants, strict monotonicity, uniform limit, full series and O(n^-4) | Verified |
| SUP-10 | Post-cut inner ball and radius-ratio initialization | Verified |
| SUP-11 | Relative-volume stopping criterion | Verified |
| SUP-12 | Instance-specific determinant optimization, exact supremum/infimum and attainment | Verified |
| SUP-13 | Q=FD, strict positivity, F0 model and normalized determinant identity | Verified |
| SUP-14 | Reweighted scalar moments and axial defect formula | Verified |
| SUP-15 | Finite-frame logdet inequality, squared-minor weights and marginal identities | Verified |
| SUP-16 | Exact pointwise Hermite remainder and rational interpolation | Verified |
| SUP-17 | Exact endpoint logarithms and rational certificates | Verified |
| SUP-18 | Scalar remainder exceeds one in dimensions two and three | Verified |
| SUP-19 | Two-dimensional determinant bound for arbitrary frame and unit axis | Verified |
| SUP-20 | Zero endpoints and selected-test variational identities | Verified |
| SUP-21 | Weighted Bessel, norm transfers, polar perturbation and support mismatch | Verified |
| SUP-22 | Unnormalized Lagrangian dual, infinite branch, scale and strict feasible seed | Verified |
| SUP-23 | Nuclear-norm gap, nonnegative terms and polar correction | Verified |
| SUP-24 | Complementary moments and coupling bound at endpoints | Verified |
| SUP-25 | Affine simplex shape formula | Verified |
| SUP-26 | Exact offset-cut and simultaneous-cut dual formulations | Verified |
| SUP-27 | Legacy cone witnesses and exact one-dimensional ratio | Verified |
| SUP-28 | Global weighted contact stability bound 16000 epsilon | Verified |
| EXT-01 | Centroid ordinary-volume fraction and comparison with 1-exp(-1) | Excluded background |
| EXT-02 | O(n^2) enclosing-ellipsoid arithmetic update | Excluded background |
| EXT-03 | O(N^(7/2) log(N Lambda / delta)) approximation algorithm | Excluded background |
| EXT-04 | Prior dimension-independent constant and uniform optimality | Verified |

SUP-01–SUP-28 are verified supporting contracts. EXT-04 is the inherited and audited prior uniform theorem. EXT-01–EXT-03 are cited introduction-only background, excluded by the author. Definitions and composed identities may account for a display; not every display is a separate named theorem. All 198 have explicit checked correspondences.
