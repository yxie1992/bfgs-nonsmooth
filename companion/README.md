# Companion Monograph

Entry point: `master.tex`. Compile directly with `latexmk`:

```bash
cd companion
SOURCE_DATE_EPOCH=1789199005 FORCE_SOURCE_DATE=1 \
  latexmk -g -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=build master.tex
```

The compiled monograph is written to `companion/build/master.pdf` (git-ignored).

`editorial/generate_companion.py` generates the fourteen thematic chapters in
`chapters/` from the frozen stage-1 sources in `bfgs_lean_stage1/master_report/`,
verifying source hashes first (`python3 editorial/generate_companion.py --check`
performs a read-only check without rewriting files). Do not hand-edit generated
files in `chapters/`; modify `editorial/generate_companion.py` and regenerate.
`editorial/prepare_shared_appendix.py` adapts the shared rational seed appendix
from `paper/appendices/seed_certificate.tex`.

All 172 source spans and 3,087 distinct formal exports from the core library are
mapped in `SOURCE_CORRESPONDENCE.json` and `editorial/CLAIM_LEDGER.json`, with
browsable exact Lean theorem signatures in `PROOF_CORRESPONDENCE.html` and
complete item-by-item Lean coverage registers in `editorial/lean_coverage/register/C_*.json`.
