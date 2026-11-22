# Proof maintenance instructions

- Preserve the mathematical contracts in `proof.md` and the stable paper IDs.
- Use the pinned Lean and dependency sources; do not silently update versions.
- Keep actual Euclidean norms, Loewner order, positive-definite shape matrices,
  actual Lebesgue volume and every dimensional/quantifier condition.
- No certified theorem may rely on `sorry`, project-specific axioms,
  `native_decide`, `Lean.ofReduceBool`, or an external numerical oracle.
- New completed results must be imported by `SharpCut.lean`, mapped to the
  inventory, built and audited. Keep exploratory files outside certified imports.
- Update statement/equation maps when changing a result. Synchronize mathematical
  corrections with the included paper and record their reasons.
- Preserve the original Khachiyan source hashes and MIT attribution. Record
  any deliberate adaptation separately and rerun the affected proof chain.
- Treat the three cited introduction-only background assertions as outside
  scope; do not assume them as axioms or report them as Lean-verified.
- Use one primary editor per file and do not start additional model sessions
  or subagents without the user's instruction.
- Use GitHub-compatible math syntax as described in `markdown_math.md`.

The reproducible acceptance command is documented in README.md. A successful
document check alone is not proof certification.
