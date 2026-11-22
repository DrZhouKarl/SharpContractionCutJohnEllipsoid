# Mathematical rigor review — 9 November 2026

The English Markdown report and its LaTeX paper were reviewed together after
completion of the Lean development. **No mathematical correction to the
stated results or proofs was required.** The global positive-dimension
convention is now explicit. The abstract and conclusion accurately describe
the completed formalization, and the author excludes the three cited
introduction-only background assertions from its scope.

## Review scope and conclusions

| Argument | Points checked | Result |
| --- | --- | --- |
| Geometry and normalization | Actual maximum-volume inscribed ellipsoid; compact convex body with nonempty interior; positive finite Lebesgue volume; proper central cut; separate interval case | Consistent |
| Finite John reduction | Both contact directions; positive weights; bounded outer polytope; preservation of the old optimum; one-sided comparison of cut optima and both supremum directions | Closed |
| Logdet/SOC certificate | Complete feasibility conditions, cancellation of the center, symmetric positive conjugate, positive determinant before division | Closed |
| Exact duality and optimal contacts | Attainment, active-facet assignment, zero inactive weights, nonzero normals, positive lengths, Sylvester recovery without commutativity | Closed |
| Explicit certificate | Positive Lorentz denominators, unit directions, model calibration, ordered factorization and left polar rotation | Closed |
| Determinant theorem | All three dimension branches; exact interpolation remainder; compact integral domains; rational endpoint certification; low-dimensional zero endpoints | Closed |
| Equality | Shape and center recovery; existential model-containing sandwich; every supporting frame; arbitrary transverse families and nonsimplex examples | Consistent with the full stated class |
| Stability | Nonnegative exact losses, genuine Frobenius/Euclidean norms, global-to-local threshold, weighted distances, ordered inverse products and zero deficit | All stated constants retained |
| Applications | Retained target ball; positive logarithm denominators; convergent dimension series and genuine remainder; initialization and attained instance bounds | Scope stated correctly |
| Discussion | Full extended-real conjugate; common-contraction scope; nuclear polar correction; both inverse-trace implications; simplex affine independence; offset/multiple-cut feasibility | No unsupported extension found |

Particular attention was given to the elementary estimates omitted from the
main narrative for readability: the exact endpoint logarithm comparison,
the dimension-three polynomial margin, and the assembly of the local
stability constants. Their explicit identities and supporting inequalities
remain in the verification records and in the audited Lean dependency chain.
The earlier request to keep the detailed logarithm-bound derivation out of
the paper's main text is respected.

## Evidence

- A fresh run of the research report's `verify_report.py` with the installed Python/SymPy
  environment passed all **49 exact algebra checks**, the statement/formula
  correspondence checks, and the then-current document checks.
- The publication comparison confirms that all **198 displayed** and
  **865 inline** mathematical expressions are byte-identical across the
  verification-status revision. All 28 named statement bodies and every
  LaTeX proof environment are preserved.
- The independent Lean review on the same mathematical baseline completed
  a new full-cold build and 3,787 transitive axiom checks, plus explicit
  physical-volume contracts. Only `propext`, `Classical.choice` and
  `Quot.sound` were admitted. The public export is separately validated
  after its packaging changes.

These checks have different scopes. Exact finite algebra supports the
specified identities; the Lean proofs establish their all-dimensional
theorem chains. The present review checks the written reasoning and the
faithfulness of those chains to the paper. Neither compiler success nor
symbolic sampling is used as a substitute for mathematical scope review.

## Publication changes

The abstract explicitly states completion of Lean 4 verification. The
conclusion records the verified mathematical scope, toolchain, foundational
axioms and source distribution. The references for Lean and mathlib are
reused from the first paper's local bibliography. The date and factual
AI-assistance disclosure are updated. No future report title or citation
has been reintroduced.

The three external background statements about centroid volume and algorithmic
complexity remain cited in the Introduction. At the author's request they
are outside the required formalization, rather than outstanding tasks in
the released proof project. Historical attribution, novelty and publication
metadata are not Lean-certified mathematical claims.
