# Formalization architecture

The implementation is complete for the author-agreed paper-results scope.
This document describes the dependency structure of the finished development;
[theorem_map.md](theorem_map.md) gives actual declaration names, and
[plan.json](plan.json) retains the 31 high-level architectural nodes.

| Layer | Implemented modules and role |
| --- | --- |
| Geometry and volume | `Geometry.lean`, `OneDimensional.lean`, `JohnFrame.lean`, `Geometry/`, and the attributed legacy library |
| John necessity | `John/`: compact contact-moment hull, separation, uniformly feasible perturbation and positive finite contact extraction |
| Optimization | `Optimization/`: complete SOC certificate, exact dual attainment, KKT/contact recovery, convexity, Lagrangian and scale |
| Explicit certificate | `Certificate/`: Lorentz geometry, finite moments, ordered factorization, polar rotation, normalized blocks and coupling |
| Determinant theorem | `Determinant/` and `Scalar/`: rectangular minor identities, lifted estimate, exact integrals, three dimension branches and equality |
| Sharp geometry | `Sharpness/`, `Geometry/SharpUpper.lean`, `Geometry/SharpTheorem.lean`: actual volume upper bound, fixed-dimensional witnesses and attained suprema |
| Gaps and equality | `Gap/`, `Equality/`: exact nonnegative losses, matrix matching, complete sandwich and every-frame classification |
| Stability | `Stability/`: weighted residuals, genuine set distance, local coercivity, polar and inverse perturbation, all shape/center constants |
| Applications and models | `Applications/`, `Simplex/`, `Examples/`: iteration, exact series, rounding, instance extrema and actual simplex/pyramid geometry |
| Further matrix results | `Coupled/` and `Matrix/`: universal tests, inverse-trace equivalences and nuclear-norm gap |
| Literal equation correspondences | `Paper/`, `equation_map.json`: explicit intermediate identities and compositions of certified results |
| Audit | `audit/Enumerate.lean`, `audit/Statements.lean`, `scripts/verify.py` |

The main chain is finite contact reduction, explicit balanced certificate,
all-dimensional determinant bound, and actual-volume transport. Constructive
exact duality is a separate result; the main sharp upper bound uses the weak
certificate and its explicitly proved feasibility.

The determinant proof retains separate branches for dimensions two, three,
and at least four. Dimension one is handled geometrically. The scalar
certificate holds on the full real interval in its statement, and the
low-dimensional proofs retain both zero endpoints.

The equality proof first recovers the shape from zero divergence, then the
center from the supporting contact moments. The sufficient general-body
condition includes the candidate ellipsoid; the necessary contact condition
quantifies over every supporting positive-weight frame.

Stability applies to any feasible near-extremal ellipsoid in John coordinates,
with all five numerical constants and the zero-deficit case. Contact estimates
are weighted. They do not assert proximity of the whole body to a unique simplex.

The three cited external background statements in the Introduction are
excluded by the author. They are neither unfinished requirements of this
release nor custom axioms. Open research directions and historical novelty
are also outside kernel certification.
