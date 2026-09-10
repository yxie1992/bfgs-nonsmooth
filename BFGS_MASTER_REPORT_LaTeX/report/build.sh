#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
latexmk -pdf -interaction=nonstopmode -halt-on-error master.tex
cp master.pdf ../BFGS_MASTER_REPORT.pdf
printf '%s\n' 'Built ../BFGS_MASTER_REPORT.pdf'
