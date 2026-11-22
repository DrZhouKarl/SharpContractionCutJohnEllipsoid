# Markdown mathematics and GitHub rendering

Use `$...$` for inline mathematics and fenced `math` blocks for displays.
The fenced form preserves matrix row separators and keeps Markdown list or
emphasis parsing from consuming TeX backslashes. The included paper and
specification use this convention without changing their mathematical content.

```math
\log\frac{R_n}{\det A}
=\Delta_{\mathrm{geom}}+\mathcal C+\mathcal D.
```

Keep mathematical subscripts, superscripts and commands inside math delimiters.
Use backticks for Lean declaration names, file paths and code. Avoid custom
LaTeX macros, preambles, packages, raw `\(...\)`/`\[...\]` delimiters,
cross-document `\label`/`\ref` dependencies, and raw pipe characters in
Markdown table cells. Prefer `\lVert ...\rVert` and `\lvert ...\rvert` in
table mathematics. Matrix displays use supported `aligned`, `cases`, `pmatrix`
or `bmatrix` environments; explicit paper equation tags are retained.

The local documentation check validates delimiters, links and conservative
TeX syntax, and runs the available local MathJax engine when supplied.
The recorded engine version and its scope are explicit in the release
verification record. A local parser check is not a claim that this repository
has already been uploaded or visually inspected on GitHub.

```bash
python3 scripts/check_markdown_math.py
python3 scripts/check_markdown_math.py --mathjax-root /path/to/mathjax \
  --output .verification/mathjax.json
```

The optional parser run requires Node.js, jsdom and a local MathJax 2
distribution. These tools are not needed for Lean proof verification.
The recorded local run uses MathJax 2.7.9 and the common TeX/AMS syntax
retained by the GitHub-facing documents.
