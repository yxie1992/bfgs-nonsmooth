# Journal article

Entry point: `master.tex`. Build from the repository root:

```bash
bash editorial/build.sh
```

The build uses the unmodified official `svjour3` class under
`editorial/vendor/svjour3/`, with its normal one-column body typography.
The article explicitly uses normal-size appendix proofs. Only empty author/editor
placeholders are suppressed for this author-review edition. No author names,
affiliations, consent, funding declarations or submission status are invented.

The command generates the seed figure with standard-library Python and TikZ,
then compiles the article and companion with `latexmk`/`pdflatex`. It sets a
documented fixed source epoch for reproducible PDF metadata. A TeX Live installation
with the declared packages, `latexmk`, Python 3 and Poppler `pdfinfo` is sufficient
for document builds; Lean is needed only to repeat formal verification.

`sections/` and `appendices/` contain the complete article proof chain.
The three introductory theorem statements live in `statements/` and are included
once, with later proofs referring to their labels. `bibliography.tex` contains
only cited published works; unpublished works are identified in text through
`preprint_references.tex`. Exact root data and rendering code are in `figures/`.
The figure uses the rational center only for plotting and never as a proof of
the isolated algebraic root or stable-manifold membership.

The article's theorem/source/formal map is `editorial/CLAIM_LEDGER.json` and its
component contract reviews. Small additional geometric deductions are verified
in `editorial/article_formal/`, separately from the sealed source-project audit.
The final author-review PDF is copied into `release/` with a source manifest.

The further skeptical review is recorded in `editorial/satisfaction_review/`.
It preserves all31 theorem/definition blocks, clarifies the reciprocal-growth
summary hypotheses, and adds a literal formal endpoint for the actual lower
counterexample branches' failure of second differentiability. The active
supplemental audits and compiled-library provenance are registered in
`editorial/root_contract_review.json`; the original corrected sources remain
unchanged. Human author-review and submission decisions remain separate.
