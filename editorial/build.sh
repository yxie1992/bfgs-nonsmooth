#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"
mkdir -p editorial/logs paper/build companion/build
export SOURCE_DATE_EPOCH=1789199005
export FORCE_SOURCE_DATE=1
python3 paper/figures/generate_figures.py > editorial/logs/figure_build.log 2>&1
python3 editorial/generate_companion.py
python3 editorial/prepare_shared_appendix.py
python3 editorial/assemble_claim_ledger.py
export TEXINPUTS="$repo_root/editorial/vendor/svjour3//:${TEXINPUTS:-}"
(cd paper && latexmk -g -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=build master.tex) > editorial/logs/paper_build.log 2>&1
(cd companion && latexmk -g -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=build master.tex) > editorial/logs/companion_build.log 2>&1
python3 editorial/check_documents.py
