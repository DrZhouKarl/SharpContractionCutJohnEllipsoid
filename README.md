# Sharp Volume Contraction of a Centrally Cut John Ellipsoid

Lean 4 formalization of **Sharp Volume Contraction of a Centrally Cut John Ellipsoid**, by Zhou Longfei.

For every positive-dimensional convex body, a closed halfspace whose boundary passes through the center of its maximum-volume inscribed ellipsoid satisfies

```math
\frac{\operatorname{vol}J(K\cap H)}{\operatorname{vol}J(K)}\le R_n,
\qquad
R_n=\begin{cases}
\frac12,&n=1,\\[2pt]
\frac12\left(\frac n{n-1}\right)^{(n-1)/2},&n\ge2.
\end{cases}
```

**The bound is attained in every fixed dimension.** 

The formalization also proves the full equality classification, exact deficits, dimension-independent stability, primal–dual characterizations, examples and applications.

The statements use actual Euclidean convex bodies and Lebesgue ellipsoid volume, with existence, uniqueness and affine normalization included.

**Certified scope:** all 28 named results, 28 supporting mathematical contracts and explicit correspondences for all 198 numbered equations. The three introduction-only citations concerning centroid volume and external algorithmic complexity are outside the author-agreed scope.They are not assumptions or custom axioms in the certified proof chain.

## Paper and proof map

- [Paper PDF](paper/main.pdf) and [GitHub-readable Markdown](paper/report.md).
- [Mathematical specification](proof.md).
- [Theorem map](theorem_map.md), with actual Lean declaration names.
- [Proof architecture](formalization_plan.md).
- [Verification scope and audit contract](verification_plan.md).
- [Recorded release verification](verification/README.md).

The main geometric theorem is `SharpCut.Geometry.sharp_central_cut_contraction`; equality is `SharpCut.Equality.equality_classification`; stability is `SharpCut.Stability.dimension_independent_stability`.

## Reproduce

Use the fixed Lean toolchain and Python 3.10 or later. Dependency setup also uses `curl`; the proof itself needs no Python mathematical package or model API. Linux was used for the recorded reproduction. On Windows, WSL provides the same command environment.

If elan is not installed, follow the [Lean installation guide](https://lean-lang.org/install/) first. Then run these commands from the repository root:

```bash
elan toolchain install leanprover/lean4:v4.35.0-rc2
python3 scripts/fetch_dependencies.py
python3 scripts/check_plan.py
python3 scripts/verify.py --profile paper --output-dir .verification/paper-001
```

The setup script fetches nine exact revision archives and checks their checksums and every source file against committed receipts. It does not follow a floating branch or download compiled proof caches. Existing valid sources are reused. The verifier is offline and reruns the root build, declaration enumeration, transitive axiom audit and mathematical signature checks. A failed or incomplete check returns a nonzero exit code.

For an offline installation, supply a cache containing the nine archive filenames recorded in [the dependency baseline](environment/baseline.json):

```bash
python3 scripts/fetch_dependencies.py --offline --archive-dir /path/to/archive-cache
python3 scripts/verify.py --profile paper --output-dir .verification/offline-001
```

For an independent build without any preexisting project or dependency Lean compilation artifacts:

```bash
python3 scripts/reproduce.py --profile paper --mode full-cold \
  --destination /tmp/sharpcut-clean \
  --output-dir .verification/full-cold-001
```

Choose a new destination and output directory for every run. The installed pinned compiler is reused; all required project and dependency modules are built from source in `full-cold` mode. See [lean_guide.md](lean_guide.md) for details. Do not run a floating `lake update`.

## Pins and trust

- Lean: `v4.35.0-rc2`.
- mathlib: `0a6c8e0355da0405d616f80b9f8232c4fab2cc5b`.
- Every transitive dependency is fixed in the baseline and
  [source receipts](environment/source-receipts).
- Allowed foundational axioms: `propext`, `Classical.choice`, `Quot.sound`.
- The certified chain contains no proof placeholders, project axioms,
  native decision shortcut or external numerical oracle.

Source-only dependencies, local build products and runtime logs are kept in ignored directories. The repository itself contains the proof, immutable dependency receipts, paper and reproducible tools; no original research workspace path is required.

## License and citation

The project and the reused Khachiyan library are MIT licensed, copyright 2026 Zhou Longfei. See [LICENSE](LICENSE), [NOTICE](NOTICE) and [legacy provenance](vendor/khachiyan/PROVENANCE.json). Third-party dependencies retain their own licenses. Citation metadata is in [CITATION.cff](CITATION.cff).

Markdown uses standard inline math and fenced `math` blocks for GitHub's MathJax rendering. See [the notation/rendering guide](markdown_math.md).
