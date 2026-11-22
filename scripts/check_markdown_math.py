#!/usr/bin/env python3
"""Check GitHub-style math fences/inline math; optionally parse with local MathJax."""

import argparse
from hashlib import sha256
from html import unescape
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def expressions(path):
    text = path.read_text()
    result, fence, body, start = [], None, [], 0
    for number, line in enumerate(text.splitlines(), 1):
        marker = re.match(r"^\s{0,3}(`{3,}|~{3,})(.*)$", line)
        if fence:
            if marker and marker[1][0] == fence[0] and len(marker[1]) >= fence[1]:
                if fence[2] == "math":
                    result.append({"line": start, "display": True, "tex": "\n".join(body).strip()})
                fence, body = None, []
            elif fence[2] == "math":
                body.append(line)
            continue
        if marker:
            fence = (marker[1][0], len(marker[1]), marker[2].strip())
            start = number
            continue
        plain = re.sub(r"(`+).*?\1", "", line)
        if "$$" in plain or re.search(r"\\[\[\]() ]", plain):
            # Raw TeX delimiters are not used; backslash-space is a valid TeX command.
            if "$$" in plain or r"\(" in plain or r"\[" in plain:
                raise RuntimeError(f"Nonstandard display/inline delimiter at {path}:{number}")
        for match in re.finditer(r"(?<!\\)\$([^$\n]+)(?<!\\)\$", plain):
            result.append({"line": number, "display": False, "tex": match[1]})
        rest = re.sub(r"(?<!\\)\$([^$\n]+)(?<!\\)\$", "", plain)
        if re.search(r"(?<!\\)\$", rest):
            raise RuntimeError(f"Unpaired dollar delimiter at {path}:{number}")
    if fence:
        raise RuntimeError(f"Unclosed code/math fence in {path}")
    for item in result:
        if re.search(r"\\(?:newcommand|renewcommand|def|input|include|usepackage|documentclass|label|eqref|ref)\b", item["tex"]):
            raise RuntimeError(f"Unsupported/custom TeX dependency at {path}:{item['line']}")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / ".verification/markdown-math.json")
    parser.add_argument("--mathjax-root", type=Path, help="Local MathJax 2 distribution; never downloaded by this script")
    parser.add_argument("--browser", default="google-chrome")
    parser.add_argument("--backend", choices=["jsdom", "chrome"], default="jsdom")
    args = parser.parse_args()
    files = sorted(ROOT.glob("*.md")) + sorted((ROOT / "paper").glob("*.md"))
    collected = []
    for path in files:
        for item in expressions(path):
            collected.append({"file": str(path.relative_to(ROOT)), **item})
    record = {"scope": "GitHub delimiter and common TeX checks; optional local MathJax parsing, not live GitHub rendering.",
              "files": len(files), "expressions": len(collected),
              "display_expressions": sum(item["display"] for item in collected),
              "source_sha256": {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest() for p in files},
              "network_requests": 0, "success": False}
    if args.mathjax_root:
        engine = args.mathjax_root.resolve() / "MathJax.js"
        if not engine.is_file():
            raise RuntimeError("Local MathJax distribution is missing")
        with tempfile.TemporaryDirectory(prefix="sharpcut-mathjax-") as tmp:
            work = Path(tmp)
            parts = ["<!doctype html><html><head><meta charset='utf-8'>",
                     "<script>window.mathErrors=[];</script>",
                     '<script type="text/x-mathjax-config">',
                     'MathJax.Hub.Config({messageStyle:"none",showMathMenu:false});',
                     'MathJax.Hub.Register.MessageHook("TeX Jax - parse error",function(m){window.mathErrors.push(String(m[1]));});',
                     'MathJax.Hub.Register.StartupHook("End",function(){var e=document.getElementById("math-check-result");e.textContent=JSON.stringify({version:MathJax.version,processed:MathJax.Hub.getAllJax().length,errors:window.mathErrors,errorNodes:document.querySelectorAll(".MathJax_Error").length});});',
                     '</script>', f'<script src="{engine.as_uri()}?config=TeX-AMS_SVG"></script>',
                     '</head><body><pre id="math-check-result">PENDING</pre>']
            for item in collected:
                mode = "; mode=display" if item["display"] else ""
                parts.append(f'<script type="math/tex{mode}">{item["tex"].replace("</script", "< /script")}</script>')
            parts.append('</body></html>')
            page = work / "check.html"
            page.write_text("\n".join(parts))
            command = [args.browser, "--headless", "--no-sandbox", "--disable-gpu",
                       "--disable-background-networking", "--disable-dev-shm-usage",
                       "--no-first-run", "--allow-file-access-from-files",
                       f"--user-data-dir={work / 'browser'}", "--virtual-time-budget=30000",
                       "--dump-dom", page.as_uri()]
            if args.backend == "jsdom":
                command = ["node", str(ROOT / "scripts/mathjax_dom.cjs"), str(page)]
                run = subprocess.run(command, capture_output=True, text=True, timeout=90)
                if run.returncode:
                    raise RuntimeError(f"Local MathJax did not finish: {run.stderr[-1500:]}")
                parsed = json.loads(run.stdout)
            else:
                run = subprocess.run(command, capture_output=True, text=True, timeout=90)
                match = re.search(r'<pre id="math-check-result">(.*?)</pre>', run.stdout, re.S)
                if run.returncode or not match or match[1] == "PENDING":
                    raise RuntimeError(f"Local MathJax did not finish: {run.stderr[-1500:]}")
                parsed = json.loads(unescape(match[1]))
            if parsed["processed"] != len(collected) or parsed["errors"] or parsed["errorNodes"]:
                raise RuntimeError(f"MathJax parse failure: {parsed}")
            record["local_mathjax"] = parsed
            record["engine_sha256"] = sha256(engine.read_bytes()).hexdigest()
    record["success"] = True
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: v for k, v in record.items() if k != "source_sha256"}, indent=2))


if __name__ == "__main__":
    main()
