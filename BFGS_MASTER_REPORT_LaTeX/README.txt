LaTeX source for BFGS_MASTER_REPORT.pdf
=======================================

The report/ directory contains the original LaTeX source files, unchanged,
extracted from BFGS_complete_research_record_20260910.zip.

Main file: report/master.tex
Included: all 14 chapter .tex files, bibliography.tex, and the original build.sh.
No external images or bibliography database are required by these sources.
The research statements and proofs have not been revised in this extraction.

Build the original multi-file source:
    cd report
    latexmk -pdf -interaction=nonstopmode -halt-on-error master.tex

This creates report/master.pdf. Alternatively, run report/build.sh to also
copy the output to BFGS_MASTER_REPORT.pdf in the parent directory.

For a single-file source, use BFGS_MASTER_REPORT.tex in the root of this archive.
It contains the same text with all LaTeX \input directives expanded inline.
Compile with:
    latexmk -pdf -interaction=nonstopmode -halt-on-error BFGS_MASTER_REPORT.tex

Use a TeX Live installation containing the standard packages named in the
preamble. The source uses pdfLaTeX; no custom font files are included.
