# Complete companion

The entry point is `master.tex`. Build both documents from the repository root
with `bash editorial/build.sh`; the resulting PDF is `build/master.pdf`.

`editorial/generate_companion.py` regenerates the fourteen thematic chapters from
the frozen corrected edition, checking its source hashes first. Do not hand-edit
the generated `chapters/` files: make an explicit, reviewed transformation in the
generator. `--check` performs an in-memory comparison without rewriting files.
`editorial/prepare_shared_appendix.py` adapts the canonical article seed appendix
for inclusion here with local references. The report contains the finite
certificate proof itself, not only a pointer to the article.

All 172 corrected source spans and all 3,087 distinct full formal exports are
retained in `SOURCE_CORRESPONDENCE.json`. `PROOF_CORRESPONDENCE.html` provides
expandable exact theorem types; `editorial/CLAIM_LEDGER.json` and the supplemental
manual-statement register map named and unnamed results. The original source
index, corrections and immutable audit evidence remain under
`bfgs_lean_stage1/master_report/`.

This is a complete repository report, not journal-published supplementary
material. The article's main theorems have their own complete arguments. The
companion preserves additional noncompact, quantitative, geometric, lifting,
scalar and negative results without merging incomparable hypotheses.

The current build, formal audit, access-limited literature comparisons and
author-side review records are under `editorial/`. Human author approval,
metadata and submission/deposit decisions remain separate.

To replay the sealed original public gate without changing its historical
scope, run `python3 editorial/verify_historical_baseline.py` from the repository
root. In a ZIP extraction, first run `_archive/restore_git_history.py` to restore
the bundled history. The wrapper records the old gate's expected rejection of
new editorial Lean files at current HEAD, verifies the unchanged frozen inputs,
and runs every original check at the exact historical release commit. Current
authoring integrity is checked separately by `editorial/verify_release_inputs.py`.
