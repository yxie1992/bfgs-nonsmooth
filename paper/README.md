# Main Research Article

Entry point: `master.tex` (*BFGS on Convex Nonsmooth Functions: Convergence and Failure*).

## Building the PDF

Requires TeX Live (`pdflatex` and `latexmk`):

```bash
cd paper
TEXINPUTS="$PWD/../editorial/vendor/svjour3//:" \
  SOURCE_DATE_EPOCH=1789199005 FORCE_SOURCE_DATE=1 \
  latexmk -g -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=build master.tex
```

The compiled manuscript is written to `paper/build/master.pdf` (git-ignored). To regenerate the TikZ figure PDFs from rational data before compiling, run `python3 figures/generate_figures.py`.

## Layout

- `master.tex`: Document preamble, title/author metadata, abstract, and section/appendix inputs (uses `editorial/vendor/svjour3/`).
- `sections/`: Main body (`introduction.tex`, `energy.tex`, `global.tex`, `local.tex`, `failure.tex`, `verification.tex`).
- `statements/`: Shared theorem statements (`positive_partition.tex`, `negative_upper.tex`, `negative_lower.tex`).
- `appendices/`: Complete self-contained proofs (`matrix_algebra.tex`, `planar_geometry.tex`, `seed_certificate.tex`, `lower_curvature.tex`, `hypothesis_examples.tex`).
- `figures/`: Reproducible Python/TikZ figure generators (`generate_figures.py`) and figure sources.
- `bibliography.tex` and `preprint_references.tex`: Published bibliography and inline preprint identifiers.

For the exact Lean 4 map of all core definitions and all 38 numbered statements in this article, see [`../ARTICLE_LEAN_MAP.md`](../ARTICLE_LEAN_MAP.md) and [`../editorial/lean_coverage/README.md`](../editorial/lean_coverage/README.md).
