# Building the paper

The authoritative typeset source is `paper.tex`. No private research file or bibliography database is required. The two photographs in the Acknowledgments are read from `figures/`, so compile from the repository root.

With a current TeX installation, run:

```text
xelatex paper.tex
xelatex paper.tex
```

Alternatively:

```text
tectonic paper.tex
```

The supplied PDF was built with XeLaTeX (TeX Live). Required standard packages are amsart, geometry, amsmath, amssymb, mathtools, longtable, booktabs, array, hyperref, xurl, needspace, graphicx, and fontspec. The two Chinese characters in the Acknowledgments use the font Noto Serif CJK SC; if it is not installed, change the `\newfontfamily\cjkfont{...}` line in the preamble to any installed CJK font.

Equation tags intentionally retain stable numbering rather than being renumbered after every insertion. Page references to IUT papers refer to author preprints, not journal pagination. The Markdown companion is supplied for reading and editing; GitHub's rendering need not reproduce all typeset formulas or equation tags. Use the PDF when checking formula layout.
