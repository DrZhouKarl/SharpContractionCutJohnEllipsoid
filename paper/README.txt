Sharp Volume Contraction of a Centrally Cut John Ellipsoid
Zhou Longfei

This source package is self-contained. The entry file is main.tex.
Compile with pdfLaTeX; shell escape and network access are not needed.
All figures are included as vector PDF files. main.bbl is included.

Build with the supplied bibliography:
  pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
  pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
  pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex

If the bibliography is edited, run bibtex main after the first pdfLaTeX pass,
then run pdfLaTeX twice more. Alternatively, use:
  latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

Dependencies are standard TeX Live packages: article, geometry, AMS packages,
mathtools, newtx, microtype, graphicx, enumitem, needspace, placeins, natbib,
xcolor, and hyperref. The bibliography style is abbrvnat.

This is a portable arXiv preprint layout, not a publisher-supplied journal class.
The paper does not claim completed Lean formalization of the new results.
