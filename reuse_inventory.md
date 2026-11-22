# Reused foundations and provenance

The new `SharpCut` namespace reuses the `Khachiyan` library from the first
paper, *A Spectral Proof of Khachiyan's Ellipsoid Conjecture*
(arXiv:2609.28447v1). The preserved source commit and all 34 Lean file hashes
are in [PROVENANCE.json](vendor/khachiyan/PROVENANCE.json).

The reusable foundations include actual Euclidean ellipsoids and Lebesgue
volume, existence and uniqueness of maximum-volume inscribed ellipsoids,
affine normalization, support functions, spectral/CFC tools, contact
sufficiency, the exact one-dimensional result and the cone witnesses.

John-contact necessity, the new finite-dimensional sharp bound, complete
equality classification, exact deficit and dimension-independent stability
are implemented in `SharpCut`; the old uniform constant is not substituted
for the new sharp constant.

The legacy Lean files are preserved byte for byte. The author confirmed
MIT licensing and copyright attribution to Zhou Longfei for the reused
library and the new project on 9 November 2026. Only the previously unfilled
license attribution was completed; no legacy proof source was edited.

The Lean/mathlib versions and all transitive revisions are fixed in
[baseline.json](environment/baseline.json). Dependencies are restored from
exact checked archives. Their own licenses remain in their downloaded sources;
they are not reassigned to this project's copyright holder.
