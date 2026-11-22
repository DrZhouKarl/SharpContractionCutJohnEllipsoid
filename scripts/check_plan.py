#!/usr/bin/env python3
"""Check planning coverage and documents offline; this never verifies Lean proofs."""

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
REQUIRED_DOCS = [
    "README.md", "AGENTS.md", "STATUS.md", "proof.md", "formalization_plan.md",
    "lean_guide.md", "theorem_map.md", "reuse_inventory.md",
    "verification_plan.md",
]
STATES = {
    "planned", "source_inspected", "reuse_pending", "implemented_pending_audit",
    "verified", "deferred_external", "excluded_background",
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper-root", type=Path,
                        help="Optional current manuscript directory for exact comparison")
    args = parser.parse_args()
    output = ROOT / ".verification/plan_validation.json"
    result = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "command": [sys.executable, *sys.argv],
        "scope": "Frozen-paper, coverage and documentation validation; mathematical certification is performed separately by scripts/verify.py.",
        "lean_build_run": False, "axiom_audit_run": False,
        "network_requests": 0, "success": False,
    }
    try:
        for name in REQUIRED_DOCS:
            require((ROOT / name).is_file(), f"Missing document: {name}")
        inventory = json.loads((ROOT / "paper_inventory.json").read_text())
        plan = json.loads((ROOT / "plan.json").read_text())
        baseline = json.loads((ROOT / "environment/baseline.json").read_text())
        legacy_manifest = json.loads((ROOT / "environment/legacy-lake-manifest.json").read_text())
        nodes = {node["id"]: node for node in plan["nodes"]}
        require(len(nodes) == len(plan["nodes"]) == 31, "Missing or duplicate planning node")
        active, visited, order = set(), set(), []

        def visit(key):
            require(key in nodes, f"Unknown dependency: {key}")
            require(key not in active, f"Dependency cycle at {key}")
            if key in visited:
                return
            active.add(key)
            for dependency in nodes[key]["dependencies"]:
                visit(dependency)
            active.remove(key)
            visited.add(key)
            order.append(key)

        for key in nodes:
            visit(key)
        statements = inventory["named_statements"]
        supplementary = inventory["supplementary_claims"]
        equations = inventory["equations"]
        ids = [item["id"] for item in statements + supplementary]
        require(len(statements) == 28, "Expected all 28 named paper results")
        require(len(supplementary) == 32, "Expected 28 supplementary and four external records")
        require(len(ids) == len(set(ids)), "Duplicate coverage ID")
        require({s["id"] for s in supplementary if s["id"].startswith("SUP-")} ==
                {f"SUP-{i:02}" for i in range(1, 29)}, "Supplementary coverage mismatch")
        require({s["id"] for s in supplementary if s["id"].startswith("EXT-")} ==
                {f"EXT-{i:02}" for i in range(1, 5)}, "External coverage mismatch")
        proposed = []
        for item in statements + supplementary:
            require(item["node"] in nodes, f"Unknown node for {item['id']}")
            require(item["status"] in STATES, f"Invalid status for {item['id']}")
            if item["status"] == "verified":
                require(item["lean_declarations"], f"No actual declarations for {item['id']}")
            if "statement_latex" in item:
                require(sha256(item["statement_latex"].encode()).hexdigest() ==
                        item["statement_sha256"], f"Corrupt statement snapshot: {item['id']}")
                require(f"\\label{{{item['id']}}}" in item["statement_latex"], item["id"])
                require(bool(item["ambient_contract"]), f"Missing contract for {item['id']}")
                proposed.extend(item["lean_declarations"])
        require(len(proposed) == len(set(proposed)), "Duplicate named declaration names")
        eq_ids = [item["id"] for item in equations]
        require(len(eq_ids) == len(set(eq_ids)) == 198, "Numbered equation coverage mismatch")
        for item in equations:
            require(item["coverage_owner"] in ids, f"Unowned display: {item['id']}")
            require(sha256(item["latex"].encode()).hexdigest() == item["sha256"],
                    f"Corrupt display snapshot: {item['id']}")
        require(baseline["lean_toolchain"] == "leanprover/lean4:v4.35.0-rc2", "Toolchain drift")
        require(baseline["mathlib_rev"] == "0a6c8e0355da0405d616f80b9f8232c4fab2cc5b",
                "mathlib pin drift")
        pins = {p["name"]: (p["url"], p["rev"]) for p in baseline["packages"]}
        reference_pins = {p["name"]: (p["url"], p["rev"]) for p in legacy_manifest["packages"]}
        require(len(pins) == 9 and pins == reference_pins, "Dependency reference mismatch")

        paper = args.paper_root or ROOT / "paper"
        paper_check = {"available": paper.is_dir(), "compared": False}
        if args.paper_root:
            require(paper.is_dir(), f"Requested paper root is unavailable: {paper}")
        if paper.is_dir():
            for name, expected in inventory["paper_source_sha256"].items():
                require((paper / name).is_file() and digest(paper / name) == expected,
                        f"Paper baseline changed: {name}")
            require(digest(paper / "main.pdf") == inventory["pdf_sha256"], "Paper PDF changed")
            actual_statements, actual_equations = {}, {}
            for file in sorted((paper / "sections").glob("*.tex")):
                text = file.read_text()
                for match in re.finditer(
                        r"\\begin\{(theorem|lemma|proposition|corollary)\}.*?\\end\{\1\}",
                        text, re.S):
                    label = re.search(r"\\label\{([^}]+)\}", match[0])[1]
                    require(label not in actual_statements, f"Duplicate paper label: {label}")
                    actual_statements[label] = match[0]
                for number, content in re.findall(
                        r"\\begin\{equation\}\\label\{eq:([^}]+)\}(.*?)\\end\{equation\}",
                        text, re.S):
                    require(number not in actual_equations, f"Duplicate equation: {number}")
                    actual_equations[number] = content
            require(actual_statements == {s["id"]: s["statement_latex"] for s in statements},
                    "Paper statement/inventory mismatch")
            require(actual_equations == {e["id"]: e["latex"] for e in equations},
                    "Paper equation/inventory mismatch")
            markdown = ROOT / "paper/report.md"
            if markdown.exists():
                require(digest(markdown) == inventory["markdown_sha256"], "Markdown baseline changed")
            paper_check.update(compared=True, source_files=len(inventory["paper_source_sha256"]))

        links, optional_unavailable = 0, []
        for name in REQUIRED_DOCS:
            path = ROOT / name
            text = path.read_text()
            require(text.count("$$") % 2 == 0, f"Unpaired display delimiters in {name}")
            require(not any(ord(c) < 32 and c not in "\n\t" for c in text),
                    f"Control character in {name}")
            for target in re.findall(r"\[[^\]]*\]\(([^)]+)\)", text):
                if "://" in target:
                    continue
                local, _, fragment = target.partition("#")
                resolved = (path.parent / local).resolve() if local else path
                if resolved == output.resolve():
                    # This run creates that record even if a check fails.
                    links += 1
                    continue
                if resolved.is_relative_to(ROOT):
                    require(resolved.exists(), f"Missing local link in {name}: {target}")
                elif not resolved.exists():
                    optional_unavailable.append({"document": name, "reference": target})
                links += 1
        covered_map = (ROOT / "theorem_map.md").read_text()
        for key in ids:
            require(key in covered_map, f"Missing human-readable map entry: {key}")
        json_files = sorted(ROOT.glob("*.json")) + sorted((ROOT / "environment").glob("*.json"))
        result.update(
            named_results=len(statements), supplementary_records=28, external_records=4,
            numbered_displays=len(equations), dependency_nodes=len(nodes),
            topological_order=order, actual_named_exports=len(proposed),
            current_verified_targets=sum(s["status"] == "verified" for s in statements + supplementary),
            paper_baseline=paper_check, checked_document_links=links,
            unavailable_optional_source_links=optional_unavailable,
            pinned_dependencies=len(pins),
            input_sha256={str(p.relative_to(ROOT)): digest(p) for p in
                          [*(ROOT / name for name in REQUIRED_DOCS), *json_files, Path(__file__)]},
            success=True,
        )
    except Exception as error:
        result["error"] = str(error)
        raise
    finally:
        result["finished_utc"] = datetime.now(timezone.utc).isoformat()
        output.parent.mkdir(exist_ok=True)
        output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "input_sha256"}, indent=2))


if __name__ == "__main__":
    main()
