# Building and auditing the formalization

## Environment

The project pins Lean `v4.35.0-rc2` and all nine package revisions. Python 3.10+
is used for preparation and audit orchestration, and `curl` for explicit
HTTPS source acquisition. No SymPy, numerical solver or model API is needed.
The current release is verified on Linux; WSL is the recommended equivalent
environment on Windows.

Install the pinned toolchain with elan if it is not already available, then
run `python3 scripts/fetch_dependencies.py` from the repository root. This
restores `.lake/packages/` from exact archive checksums and validates every
file and symbolic link against `environment/source-receipts/`.
Those committed receipts are immutable inputs; setup never overwrites them
to accept changed source.

An existing source or archive mismatch is an error. Diagnose it instead of
updating the receipt or lockfile merely to make verification pass. The
`--offline --archive-dir PATH` option restores the same environment from a
user-supplied cache without network requests. The cache is read-only to the
installer. Source extraction rejects escaping or ambiguous archive paths.

## Routine verification

```bash
python3 scripts/check_plan.py
python3 scripts/verify.py --profile paper --output-dir .verification/run-001
```

The first command checks the frozen paper, mathematical inventory and document
links. The second executes Lean and requires complete paper-profile coverage,
actual imported declarations, exact signature gates and allowed transitive
axioms. Use a new output directory; old verification logs are never used as
the success test for a new run.

The verifier locates the pinned elan toolchain by default. Use its
`--toolchain-dir PATH` option if that installed toolchain has another location.
Its actual version and compiler commit are checked before the build. Ordinary
verification can reuse existing build artifacts; this fact is recorded.

## Independent source reproduction

```bash
python3 scripts/reproduce.py --profile paper --mode full-cold \
  --destination /tmp/sharpcut-clean \
  --output-dir .verification/full-cold-001
```

The destination must be new and outside this repository. The command copies
the certified project inputs and authenticated dependency sources, starts
without any project or dependency Lean compilation artifact, and invokes
the same strict verifier. It compares the resulting source snapshot with
the development snapshot. The installed compiler is the baseline.

`--mode project-cold` is a faster, separately recorded option: it omits project
artifacts but reuses pinned dependency build artifacts. It is not a full-cold
reproduction. Neither mode downloads dependencies; prepare them first.

## Development

Compile a small changed module before integrating it:

```bash
lake --no-cache env lean SharpCut/JohnFrame.lean
lake --no-cache build SharpCut.JohnFrame
```

Search the fixed mathlib source before guessing interfaces. Check actual
project types, positive domains and normalization factors. In particular,
the default norm on a plain function space is not the Euclidean norm, and
`0 < A` in a matrix order is not a substitute for `A.PosDef`.

After an intentional proof change, update the declaration inventory and the
paper correspondence, then run the full verifier. Do not weaken a theorem,
add the desired conclusion as a hypothesis or suppress an audit failure.
The main source module imports every certified project module.

## Verification outputs

Each run records commands, return codes, versions, source hashes, dependency
revisions, cache use, declarations, signature gates and complete axiom output.
Only `propext`, `Classical.choice` and `Quot.sound` are accepted. Missing
entries, forbidden axioms, changed source, incomplete coverage or failed
commands cause a nonzero return code.

The recorded release results in `verification/` are supporting evidence.
External users should execute the commands above to obtain their own fresh
records in the ignored `.verification/` directory.
