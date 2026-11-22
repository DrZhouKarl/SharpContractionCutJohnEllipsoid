# Statement correspondence: reference-style V2

All mathematical statements are preserved; this table changes only their printed locations and numbers. The existing Lean project is read-only and retains its original mapping.

| Original paper | V2 | Stable label | Existing Lean declaration(s) |
| --- | --- | --- | --- |
| Theorem 3.1 | Theorem 1 | `thm-sharp` | `SharpCut.Geometry.sharp_central_cut_contraction` |
| Lemma 2.2 | Lemma 2 | `lem-john` | `SharpCut.Geometry.john_contact_iff` |
| Lemma 2.5 | Lemma 3 | `lem-reduction` | `SharpCut.Geometry.contact_reduction` |
| Lemma 2.1 | Lemma 4 | `lem-certificate` | `SharpCut.Optimization.volume_certificate` |
| Theorem 3.2 | Theorem 5 | `thm-frame-bound` | `SharpCut.Certificate.john_frame_certificate_bound` |
| Theorem 8.1 | Theorem 6 | `thm-determinant` | `SharpCut.Determinant.quantitative_frame_determinant` |
| Lemma 8.2 | Lemma 7 | `lem-lifted-bound` | `SharpCut.Determinant.lifted_determinant_bound` |
| Lemma 8.3 | Lemma 8 | `lem-hermite` | `SharpCut.Determinant.interpolation_loss` |
| Lemma 8.4 | Lemma 9 | `lem-rational` | `SharpCut.Scalar.uniform_certificate` |
| Lemma 8.5 | Lemma 10 | `lem-moments` | `SharpCut.Certificate.block_identities_and_constraints` |
| Lemma 8.6 | Lemma 11 | `lem-variational` | `SharpCut.Certificate.direct_coupling_bound` |
| Proposition 8.7 | Proposition 12 | `prop-dim3` | `SharpCut.Determinant.dimension_three_determinant` |
| Proposition 4.1 | Proposition 13 | `prop-gap` | `SharpCut.Gap.exact_volume_deficit`; `SharpCut.Gap.affine_optimal_volume_deficit` |
| Lemma 4.2 | Lemma 14 | `lem-matching` | `SharpCut.Gap.matrix_matching` |
| Theorem 5.1 | Theorem 15 | `thm-equality` | `SharpCut.Equality.equality_classification` |
| Proposition 5.2 | Proposition 16 | `prop-extremizers` | `SharpCut.Equality.transverse_extremal_construction` |
| Lemma 6.1 | Lemma 17 | `lem-geometric-control` | `SharpCut.Stability.geometric_control` |
| Theorem 6.2 | Theorem 18 | `thm-stability` | `SharpCut.Stability.dimension_independent_stability` |
| Proposition 9.1 | Proposition 19 | `prop-gap-control` | `SharpCut.Gap.cone_sum_of_squares`; `SharpCut.Gap.quantitative_complementarity` |
| Lemma 9.2 | Lemma 20 | `lem-residual` | `SharpCut.Stability.geometric_residual` |
| Lemma 9.3 | Lemma 21 | `lem-local` | `SharpCut.Stability.local_coercivity` |
| Proposition 2.3 | Proposition 22 | `prop-exact-duality` | `SharpCut.Optimization.exact_duality` |
| Proposition 2.4 | Proposition 23 | `prop-kkt` | `SharpCut.Optimization.kkt_optimality_and_contacts` |
| Corollary 7.1 | Corollary 24 | `cor-iteration` | `SharpCut.Applications.successive_exact_central_cuts` |
| Proposition 10.1 | Proposition 25 | `prop-polar` | `SharpCut.Optimization.common_contraction_optimal` |
| Lemma 10.2 | Lemma 26 | `lem-cauchy` | `SharpCut.Coupled.general_cauchy_transverse` |
| Lemma 10.3 | Lemma 27 | `lem-cauchy-minus` | `SharpCut.Coupled.complementary_cauchy_transverse` |
| Lemma 10.4 | Lemma 28 | `lem-inverse-trace` | `SharpCut.Coupled.InverseTrace.inverse_trace_interpretation` |

All 198 equation-number correspondences and section locations are in [numbering_map.json](numbering_map.json). The formalization remains based on the same stable theorem/equation identifiers. The abstract, introductory summaries and overview table restate existing verified results; their assumptions and correspondences are recorded in [front_summary_claims.json](front_summary_claims.json).
