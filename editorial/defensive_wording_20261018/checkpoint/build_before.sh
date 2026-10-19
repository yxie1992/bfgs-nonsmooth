#!/bin/bash
# Build the article and companion PDFs of HEAD (before the M44 edits) for page comparison.
B=/tmp/opencode/m44
REPO=/home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth
rm -rf "$B/before_tree"
mkdir -p "$B/before_tree"
git -C "$REPO" archive HEAD paper companion editorial/vendor | tar -x -C "$B/before_tree"
export PATH="$HOME/.local/bin:$PATH"
export SOURCE_DATE_EPOCH=1789199005 FORCE_SOURCE_DATE=1
for doc in paper companion; do
  cd "$B/before_tree/$doc" || exit 1
  TEXINPUTS="$PWD/../editorial/vendor/svjour3//:" latexmk -g -pdf -interaction=nonstopmode \
    -halt-on-error -file-line-error -outdir=build master.tex > "$B/before_$doc.log" 2>&1
  echo "EXIT $?" >> "$B/before_$doc.log"
done
python3 -m venv "$B/venv" > "$B/venv.log" 2>&1
"$B/venv/bin/pip" install -q pymupdf >> "$B/venv.log" 2>&1
echo "EXIT $?" >> "$B/venv.log"
