# Release status

The formalization is complete for the author-agreed paper-results scope:
28 named results, 28 supplementary mathematical contracts and 198 numbered
equation correspondences, together with the inherited prior uniform result.
The three introduction-only external background assertions are excluded.

The public source preserves every `SharpCut` and legacy Lean proof file from
the independently audited development. Packaging changes concern portable
dependency receipts, setup/verification tools, updated paper metadata,
documentation and confirmed MIT attribution.

The exact release validation and source hashes are recorded in
[verification/README.md](verification/README.md). The release is locally
prepared for independent checking and later public upload by the author;
no GitHub upload or repository URL is assumed here.

Known nonblocking compiler warnings concern deprecated interface names,
unused variables/simplification arguments and tactic style. No placeholder
proof or disallowed axiom is accepted. Future cleanup must retain the exact
mathematical contracts and rerun the audit.
