# Verification contract and scope

The `paper` profile certifies all 28 named results, SUP-01–SUP-28 and the
198 numbered-equation correspondences recorded in the inventories. The prior
uniform bound, EXT-04, is inherited from the fixed legacy source and audited.
The author excludes EXT-01–EXT-03, the three introduction-only centroid and
algorithmic complexity citations. They are not premises of the certified proofs.

## Required gates

1. Actual Lean/compiler revision and every dependency source receipt match
   the committed pins; all import paths remain inside the independent source
   project or the installed toolchain.
2. The root builds and imports every certified project module.
3. Actual loaded public declarations match `implementation_map.json`.
4. Every named and supplementary contract is present, and every numbered
   equation has an explicit, source-hash-matched correspondence.
5. `audit/Statements.lean` checks explicit mathematical signatures, including
   actual volume, all positive dimensions, exact constants, equality
   quantifiers, noncommutative matrix order and all stability estimates.
6. Fresh `#print axioms` output covers the enumerated project and loaded
   legacy declarations exactly. Only `propext`, `Classical.choice` and
   `Quot.sound` are accepted.
7. Sources and dependency identities remain unchanged during the run.

A source-token scan supplements the kernel dependency audit. It is not the
sole reason for accepting a proof. Empty roots, missing audit entries, old
logs and a conclusion stored as a structure field cannot satisfy these gates.
The existing negative coverage tests exercise rejection of incomplete maps.

## Reproduction levels

Routine runs can reuse existing compiled artifacts and record that use.
Project-cold reproduction rebuilds the project but reuses dependency artifacts.
Full-cold reproduction starts with no project or dependency Lean compilation
artifacts and rebuilds the required sources. The installed pinned compiler is
the explicit baseline in every case.

## Reporting

Kernel proof validity and mathematical statement fidelity are distinct checks.
The signature gates and human-readable specification make the intended
contracts inspectable. The 198 equation records include definitions and
equivalent formulations; they do not assert that every printed display is a
separate named Lean theorem.

Historical attribution, novelty, bibliographic metadata and rendering are not
Lean-certified claims. Verification outputs must identify the `paper` scope
and its explicitly excluded background material. See `verification/README.md`
for the actual release run and `lean_guide.md` for commands that rerun it.
