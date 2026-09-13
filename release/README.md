# BFGS article and complete companion — focused exposition revision

The author-review article has **49 pages**, including its essential proof appendices; the complete companion has **107 pages**. The seven-section article architecture and its positive and negative theorem selection are unchanged. The revision clarifies the historical increment, teaches the planar field construction, supplies familiar norm/composite examples, explains why the actual negatives evade the positive hypotheses, and improves the finite-trial and fixed-objective scale figures.

The PDFs are `BFGS_Journal_Article.pdf` and `BFGS_Complete_Companion.pdf`. LaTeX entry points are `paper/master.tex` and `companion/master.tex`. Exact page counts, hashes, source freeze and later extraction validation are recorded in `RELEASE.json` and `SOURCE_MANIFEST.json`. The preceding 12 September edition and receipts are preserved in `history/20260912_satisfaction/`.

## Reproduction and source identity

In an existing repository checkout:

```bash
bash editorial/build.sh
python3 editorial/scientific_exposition_20260913/refresh_correspondence.py --check
python3 editorial/verify_release_inputs.py
```

The source archive `BFGS_paper_companion_sources.zip` preserves the outer `BFGS-non-smooth/` directory and every committed relative path, including Lean sources, pinned dependencies, complete proof/source maps, actual audits and review records. It excludes dependency caches, compiled objects, untracked user files and temporary build debris. The Git history bundle supports immutable historical checks. After a fresh extraction, run `python3 _archive/restore_git_history.py` before any other command. `_archive/RELEASE_SNAPSHOT.json` identifies the immutable source commit; any older receipt inside that snapshot is explicitly historical. The archive's own hash and its later validation record are external, avoiding a circular hash or future-execution claim.

Python 3, TeX Live, latexmk/pdflatex and Poppler are required. The supplied journal class retains its original notices. Figure generation is reproducible standard-library Python/TikZ. `paper/figures/check_trial_display.py` independently checks the displayed rational current/trial intervals; it is diagnostic evidence, not a premise imported into Lean.

## Proof and review scope

The revision adds no Lean theorem, custom axiom or weakened guard. All 31 named article statements, 52 existing labeled displays, the deterministic bracket algorithm and the full seed/lower appendices agree with the baseline under explicit scoped notation aliases. New explanatory deductions are tied to exact existing contracts and identified as reviewed compositions, rather than newly compiled endpoints. All 172 companion source spans and 3,087 distinct original exports are preserved. Full mappings are in `editorial/CLAIM_LEDGER.json`, `companion/PROOF_CORRESPONDENCE.html` and `editorial/scientific_exposition_20260913/mapping_refresh.json`.

The three self-review passes and N1–N6 response are in `editorial/scientific_exposition_20260913/REVIEW_LOG.md` and `RESPONSE.md`. Page-level visual evidence is in `editorial/reviews/render_manifest.json`. The existing source/audit integrity gate authenticates the actual pinned main and four supplemental proof audits; it checks present sealed cache bytes when available. Reproduced compilation is reported only by actual dated run receipts. Counts overlap, and only `propext`, `Classical.choice` and `Quot.sound` are permitted. No empty-cache original-library or Mathlib rebuild, foundational consistency proof, publication-priority certification or floating-point robustness is asserted.

The source freeze is reviewed before packaging. `RELEASE.json` distinguishes awaiting extraction validation from a completed release; the final validation record will show the commands that actually ran and their outcomes. New builds/audits use fresh versioned output directories, preserving existing evidence. The historical citation-only checker remains unchanged and is replayed at its frozen baseline by `editorial/verify_historical_baseline.py`; current editorial checks are separate.

## Author decisions

Human mathematical/literature and novelty review, authorship metadata and consent, responsibility/declarations, target/length decisions, and any archival identifier or submission remain with the author; see `editorial/AI_AND_AUTHOR_ACTIONS.md`. The article retains an honest substantive AI-use disclosure. The 49-page length exceeds the earlier editorial aim to preserve the requested proof-complete positive/negative selection; `editorial/JOURNAL_FIT.md` explains this and dates the policy access. No DOI, deposit, submission, author approval or independent human peer review has been invented.
