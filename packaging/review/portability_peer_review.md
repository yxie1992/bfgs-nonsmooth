# Portable manifest correction: independent review

Reviewed 2026-09-12 against committed baseline `70a60d4e627a7897e3f820397d57d71d0de785e1` and the working-tree correction. Scope: manifest/inventory portability, not a new mathematical or Lean proof review.

**PASS — no blocking finding.** The actual diff is confined to the documented macOS metadata exclusion, the two explanatory report documents, resealing, and the packager's matching forbidden-path component.

The first extracted-archive gate failed because the old release manifest required three ignored, untracked `.DS_Store` files that `git archive` correctly omitted. The revised gate permits exactly `excluded_basenames == ['.DS_Store']`, rejects any sealed entry with that basename, and removes only that basename from the computed inventory. It still hashes every included artifact and requires equality of the entire remaining inventory. The pre-existing Python-cache exclusion is unchanged. The packager now rejects `.DS_Store` as a path component, without weakening its tracked-tree, nonregular-file, cache/object, Git-bundle or ZIP checksum checks.

An independent JSON comparison of the old and new manifests confirmed:

- Exactly three entries removed: `master_report/.DS_Store`, `master_report/latex/.DS_Store`, `master_report/latex/output/.DS_Store`.
- No new sealed paths; 286 paths remain and every one is Git-tracked.
- Exactly three existing hashes changed: `master_report/README.md`, `master_report/FINAL_REVIEW.md`, and `scripts/verify_rigorous_master_report.py`.
- All other **283 sealed artifact hashes are unchanged**, including the report sources, mathematical correspondence, proof/compiler evidence and PDF.
- No working-tree diff to Lean sources, pinned toolchain/dependency records or either historical baseline JSON.

The original scientific release checks are still executed before the manifest check: exact report regeneration, compiler/axiom evidence, citation-preservation comparison, independent source/index checks, corruption-rejection cases, index navigation, and PDF/render/visual evidence. The metadata exception is a fixed literal, not a configurable list that could silently exempt a proof or evidence file. Historical Git fallback and its SHA-256 comparisons are unchanged.

The parent-run `local_release_gate_after_portability_fix.json` was inspected and records PASS, with all eight release checks and the same 98-page PDF hash:

`4229687ed71308031d557c91e41d9a9a021840cc93f571abdcf5b3b29ef3ca70`.

Final reviewed script SHA-256 values:

- Main verifier: `c4feaf7d8625996832999b71a1a3d48d0dc95e4ac926a0b59b2a040940e3f97c`.
- Packager: `3928e51802f15190df41ee6b69a1fdc3031106cfdd1fe6655b745a7821ec9ffb`.

This reviewer performed read-only inspection and the independent manifest/path comparisons. The fresh ZIP extraction and full gate replay are performed and recorded separately by the parent task; this note does not claim they have completed before their evidence is available. The correction neither changes a mathematical statement nor relaxes a scientific verification check.
