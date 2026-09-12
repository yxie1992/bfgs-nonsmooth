# BFGS journal-paper authoring handoff

Prepared 12 September 2026 for continuation inside the author's existing Git repository.

## Use

Place this directory inside the repository (for example, under `editorial/handoff/`). Give Codex `CODEX_PROMPT.md`. It is an execution brief: create a finished journal-style article and an organized companion report, not merely an outline or recommendations.

The author requested a coherent, human-readable story joining positive and negative results, suitable in substance for Mathematical Programming or SIAM Journal on Optimization. The suggested story is **local convergence and failure of unmodified BFGS: regularity within branches versus compatibility of nonsmooth geometry with remaining descent**. This is an organizing interpretation, not a necessary-and-sufficient mathematical classification.

## What this package is—and is not

This package contains editorial specifications, result-placement recommendations, ledger templates, source-discovery metadata, and completion criteria. It contains **no new mathematical results, no Lean proofs, no replacement audit, and no finished manuscript**. The current repository's corrected mathematical statements and exact formal theorem contracts govern what may be claimed.

The supplied `latex.zip` was inspected programmatically. It contains the corrected LaTeX edition dated 11 September 2026, its bibliography, and chapter correspondence tables. It does not contain the Lean project, complete proof index, source map, or literature-audit directory referenced by the manuscript. Codex must discover and inspect those in the author's repository. Their existence or verification is not newly certified by this editorial package.

Do not restart from the old uncompiled `bfgs_lean_stage1` draft when the repository contains the later formalization. Do not restore claims, formulas, run counts, or unsupported historical assertions withdrawn in the corrected edition. Do not mix constants from different counterexample seeds.

## Read in this order

1. `CODEX_PROMPT.md`: the complete job, milestones, and required outputs.
2. `PAPER_BLUEPRINT.md`: narrative, article architecture, proof placement, and sample opening.
3. `RESULTS_SELECTION.md`: what must be retained and what is superseded or incomparable.
4. `COMPANION_AND_TRACEABILITY.md`: companion structure and statement-to-proof mapping.
5. `ATTRIBUTION_GUIDE.md` and `JOURNAL_POLICY.md`: literature and submission constraints.
6. `FIGURES_AND_TABLES.md` and `ACCEPTANCE_AND_GIT.md`: production and completion checks.

Templates are starting registers, **not completed audits**. Empty formal-declaration fields deliberately require inspection of the repository. The `source_review/` files record observations of the supplied archive; locations are archive-relative, not assumed repository paths.

## Important correction to the earlier publication outline

Do not plan to publish indispensable proofs as a journal supplement. The policy snapshot in `JOURNAL_POLICY.md` changes that part of the earlier advice. The **article must contain the complete argument for its main claims**, including article appendices when needed. The companion preserves broader results, expanded derivations, formal correspondence, and reproducibility as a separate archival document. Its presence is not permission to leave the article mathematically incomplete.

Default editorial target: one Mathematical Programming-style regular article, with a concise, proof-complete core. Record a separate SIOPT feasibility assessment rather than claiming that a lengthy article meets both journals' requirements. Target choice here is an editorial recommendation, not a submission decision or prediction of acceptance.

## Completion standard

The work ends with an author-review-ready article, companion report, reproducible source builds, a complete claim/proof and attribution ledger, an actual verification record, a resolved review checklist, and major milestones committed and pushed to the existing authorized remote. Journal acceptance, author consent, publication priority, and human independent review cannot be self-certified by Codex.

If genuinely external items remain, isolate them in an author-action list. Do not describe a blocked proof, a failed build, or a missing formal audit as completed.
