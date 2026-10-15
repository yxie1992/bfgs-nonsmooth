# October 2026 Lean-coverage and correction edition: release run

15 October 2026. Plan: `editorial/release_plan_20261015/PLAN.md`, with the run order and the release host of `README.md` in this directory. Baseline: the 13 September edition (source freeze `3e8b5c6`, release commits `fa54d6a` and `db4dc37`).

## Before the freeze

The commits since the release tooling, in order (each pushed to `origin/main`):

- `58270f5` Release tooling T1–T5 for the October release (independently reviewed and fixed)
- `6e06960` Article corrections M30–M41 from the line-by-line reading, their companion recurrences and W47 (independently reviewed)
- `3fa85bc` Claim/proof index: real provenance of 24 Lean signatures; October revision rows (tooling review SF6)
- `5b5c273` Release run steps 2–3: edition date 15 October 2026; register notes without counts
- `c481b03` Release run step 4: October correspondence revision (77 rows, independently reviewed)
- `2cfa27a` Release run step 5: printed Lean counts in the companion (5420 names, 783 modules)
- `8ca8bac` Release run step 6: Lean evidence (axiom audit 5420 names, kernel replay 783 modules)
- `e5e9816` Questions for the author: Q7, typesetting points from the release visual review

The Lean evidence (axiom audit, 5,420 names; kernel replay, 783 modules; of commit `2cfa27a`) is bound to the frozen sources by the release-input gate: from the audited commit on, no Lean file, Lake configuration, audit script, claim ledger or coverage register changed.

## Milestone A: reviewed source freeze

The release workspace is a fresh clone named `BFGS-non-smooth` (the archive root); its `bfgs_lean_stage1/.lake` and `.toolchain` link to an APFS copy-on-write clone of the sealed September host cache (`cache_binding_04`: PASS, 8853 objects, 32470 files), never to the September checkout, which was left unchanged. The 13 September edition was preserved in `release/history/20260913_exposition/` with `PRESERVATION.json` (its git-ignored archive copied there, hash `b76bd245…` verified) before its files were replaced. `build.sh` regenerated the figures, companion chapters, shared appendix and ledger byte-identically; only the build logs changed. The article has 49 pages and the companion 108, with no unresolved reference or overfull box; both PDFs were copied to `release/`. Every page was rendered and visually reviewed: Article: all 49 pages viewed on 13 contact sheets and 48 pages at full size (every page whose body changed since 13 September: 48); 15 cosmetic findings, none blocking. Companion: all 108 pages viewed on 27 contact sheets and 78 pages at full size (every page whose body changed since 13 September: 78); 13 cosmetic findings, none blocking. The visual review was made by three agents (V1 the article; V2 and V3 the companion, PDF pages 1–56 and 57–108) on PDFs built from `2cfa27a` in a scratch clone; the PDFs built here are byte- and text-identical to them, and all 157 page renders equal the reviewed ones. Their typesetting points, none blocking, are Q7 of `TODO_MANUSCRIPT_REVIEW.md`, left for a later edition. The release-input gate passed 23/23 with the cached bytes verified; the October correspondence check and the strict coverage check passed; the 13 September correspondence check (at `3e8b5c6`) and the historical gate passed in a scratch clone of the workspace.

Milestone A source commit: `992d477d98fd01911371a223c407d628ddd74381`. Push to `origin/main` succeeded and the remote branch hash was verified; see `source_push.json`.

## Milestone B: reproduced author-review release

Packaged the immutable source freeze with 4,979 archive members (4,974 committed files and five archive-only members), preserving the repository directory structure and excluding dependency caches and untracked files. The archive is 171,605,001 bytes, SHA-256 `175c1c60cc89a507549dc7cc570c1e425abaeeee5b6c239c3b759a3424cd7e15`; the package output is in `package.log`. Fresh extraction validation completed PASS in `release/validation/runs/coverage_20261015_01/SUMMARY.json` (2.4 minutes); its 41 recorded commands reproduce both PDFs byte for byte and all 157 reviewed page images, run the preservation, correspondence (13 September, at its release commit; October) and strict coverage checks, the four supplement compilations with full structural audits, and the historical and current integrity gates. Exact pinned host libraries were reused with before/after cache and ordered search-path checks. This is not an empty-cache original-library or Mathlib build. The unchanged source archive stays fixed; post-execution receipts are external. The release commit and its verified push are recorded in a subsequent receipt.

Milestone B release commit: `67a4c408920b8d1643b71244f0933e4b98507d7f`. Push to `origin/main` succeeded and the remote branch hash was verified; the exact output is in `final_push.json`. GitHub accepted the push with a nonblocking 56.72 MB file-size warning for the retained branch-regularity dependency graph, as on 13 September. The final status records no remaining execution; only the reserved human author actions and the questions for the author remain. This completion receipt is committed afterward without repackaging the frozen source.
