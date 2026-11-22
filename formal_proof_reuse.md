# Reusing the existing Lean formalization

The V2 manuscript preserves the mathematical statements certified by the
existing `formal_proof/` project. That directory, the preceding arXiv manuscript
and the existing public proof distribution remain unchanged.

## What changed

The main theorem moves to the Introduction. John frames and the weak
certificate form the preliminaries. The determinant proof now immediately
follows the certificate construction, before completion of the geometric bound.
Equality and stability are grouped together; exact duality and applications
follow as further consequences. Theorem numbers run continuously; equation numbers restart in each section. The abstract and linking prose are rewritten around this
reading order.

## Why the old proofs still apply

- Every one of the **28 named statement bodies** is identical to the old
  LaTeX statement and to the corresponding frozen formal inventory entry.
- Every one of the **198 numbered equation bodies** is identical to the old
  formula and has the same stable label, such as `eq:8.55`.
- All **24 proof environments** are identical. The original body has the same multiset
  of **858 inline mathematical expressions**. The new introductory summaries
  are checked separately against their recorded text and explicit correspondence
  to the existing equality, stability and gap results.
- The abstract's displayed bound is the already certified sharp theorem and
  its dimensional constant. The four new Introduction displays and Table 1 summarize existing sharpness,
  equality, stability and certificate/gap results. Their hypotheses and exact
  constants are mapped in `front_summary_claims.json`; no new theorem
  is introduced. The equality summary is equivalent to the original sandwich
  condition by convexity and the definition of a supporting frame.
- The declarations for all 28 supplementary contracts remain recorded in
  `math_baseline.json`. The new numbering map connects every
  numbered equation to its existing formal declarations and correspondence.

| Previous statement | V2 statement | Existing Lean declaration |
| --- | --- | --- |
| Theorem 3.1 | Theorem 1 | `SharpCut.Geometry.sharp_central_cut_contraction` |
| Theorem 5.1 | Theorem 15 | `SharpCut.Equality.equality_classification` |
| Theorem 6.2 | Theorem 18 | `SharpCut.Stability.dimension_independent_stability` |

The full correspondence is in [theorem_map.md](theorem_map.md) and
[numbering_map.json](numbering_map.json). The old IDs are not
renamed in the Lean source or in its original maps. Thus the preceding paper
and its existing proof records retain their own numbering and consistency.

## Checks and limits

`scripts/validate.py` compares the complete mathematical bodies, verifies
the new numbers against actual LaTeX labels, checks references and confirms
the hashes of 1,705 protected original source/document files when the old
workspace is present. The frozen comparison data are local to this directory;
the manuscript and arXiv source package do not depend on those original paths.

No new Lean proof, dependency update, kernel build or axiom audit is performed
for this organizational edition. Reuse is justified by the explicit content
identity and complete correspondence to the previously checked contracts.
The current work does not extend the original verification scope, certify
the excluded introduction-only background assertions, or claim that Lean
certifies presentation, historical attribution or novelty.
