# Release verification — 9 November 2026

The exported proof sources passed a new independent build starting with **zero
project and dependency Lean compilation artifacts**, followed by the complete
paper-profile verification. All nine dependencies were restored by the exported
installer from exact checked source archives; no compiled cache was copied.
The cold build completed 3,369 jobs in 541.002 seconds.

All 28 named results, 28 supplementary contracts and 198 equation correspondences
passed. The audit enumerated 3,058 project and 729 legacy entries and accepted
only `propext`, `Classical.choice` and `Quot.sound` in all 3,787 axiom reports.

After correcting only the verifier's module documentation to reflect the
agreed scope, the exact final source snapshot passed the audit again using
those freshly produced artifacts. Its executable Python AST is unchanged,
and all distributed Lean proof sources are byte-identical to the cold run.
The source hashes and both stages are explicit in [release.json](release.json).

- [Axiom output](axioms.log): every actual axiom entry in order; style warnings
  containing private execution paths are omitted from this public log.
- [Mathematical signature output](statements.log): unchanged compiler output.
- [Dependency archive/setup tests](dependency_setup_tests.json): all 10 passed.
- [Markdown transformation](markdown_conversion.json): all 198 paper displays preserved.
- [MathJax check](markdown_math.json): 1,234 expressions, including 220 displays,
  parsed without errors by local MathJax 2.7.9. The documents use common TeX/AMS
  syntax and GitHub math fences. Live GitHub rendering was not tested because
  the repository has not been uploaded; documentation/engine downloads were
  unavailable at DNS resolution, so the installed local engine was used.

The three introduction-only external background assertions are outside the
author-agreed scope. They are not pending required proofs or custom axioms.

Run your own checks with the root README commands. New runtime logs belong
in the ignored `.verification/` directory. These recorded results support
reproducibility; they do not replace executing the verifier on your machine.

## Author-confirmed disclosure update

The author subsequently clarified that large language models assisted result
discovery, mathematical proof development and formal verification. Only the
companion paper disclosure and its three document/inventory hashes changed.
All Lean/audit sources, theorem statements and numbered equations are unchanged.
The PDF was rebuilt and checked; no new kernel run is claimed for this prose
edit. The original audited hashes remain in `audited_source_sha256`, and current
deliverable hashes are in `source_sha256`. See
[the disclosure update](paper_disclosure_update.json).
