# Literature audit of the corrected BFGS report

Start with [REPORT.md](REPORT.md). It answers which results have published precedents and which proof techniques have an existing lineage. [CITATION_PLAN.md](CITATION_PLAN.md) gives concrete attribution changes for a future scholarly edition.

The comparison covers all 172 corrected report spans through 75 research groups and separately classified scope/execution records. This is a completed, bounded literature search as of 11 September 2026 in Los Angeles. “No exact match found” does not establish novelty. Two metric-selector priority questions remain unresolved; an explicit open conjecture is also recorded separately from proved claims.

The audited report edition is preserved in Git at the commit and hashes in [BASELINE.json](BASELINE.json). This supplement does not introduce proof axioms or claim to have rerun Lean compilation. Independent packet reviews, artifact checks, and the unchanged-edition verification log appear under [review](review).

## Detailed comparisons

- [Negative results, D/L](packets/negative_D_L.md): deterministic failures and construction techniques.
- [Geometry, C/Q/U/A](packets/geometry_C_Q_U_A.md): affine criticality, planar and fixed-normal results, geometry precedents.
- [Positive families, R/F/H and scalar G](packets/positive_R_F_H_G.md): known special cases, families, rates, fibers and certificate limitations.
- [Foundation, M/T and G](packets/foundation_M_T_G.md): actual matrix hierarchy, reciprocal growth, frames and PSD certificates.

Each packet has companion JSON with statement comparisons, primary URLs, version-specific theorem/proof locators, confidence and access limits.

## Registers and reproducibility

- [CLAIMS.json](CLAIMS.json): research comparisons and coverage of every corrected span.
- [SOURCES.json](SOURCES.json): source records, access levels and duplicate-DOI groups.
- [SEARCH_LOG.json](SEARCH_LOG.json): executed-query ledger; web rankings and access are not frozen.
- [references.bib](references.bib): bibliography keyed to the source register, with intentional version duplicates.
- [REGISTER_SUMMARY.json](REGISTER_SUMMARY.json): generated counts and classifications.
- [STATUS.json](STATUS.json): completion status and material limitations.
- [MANIFEST.json](MANIFEST.json): hashes of the delivered supplement.
- [PLAN.md](PLAN.md), [MILESTONE_1.md](MILESTONE_1.md): scope and first committed milestone, including a disclosed source-locator correction.

From the repository root:

```bash
python3 bfgs_lean_stage1/literature_audit/scripts/rebuild_register.py
python3 bfgs_lean_stage1/literature_audit/scripts/validate.py
```

The readers use the exact audited baseline, verifying its hashes in the current checkout or, after an authorized report revision, in the recorded Git commit. A clone must retain that commit; changing baseline hashes is not a substitute for restoring missing history. The current corrected report now incorporates these citations, with its revision record in `../master_report/authoring/citation_revision/`.

The first command deterministically rebuilds the combined JSON/BibTeX files from reviewed packets and explicit span routing. The second checks baseline integrity, register links, exact span coverage and the supplement manifest. These commands validate artifact structure and preservation; they do not automate mathematical priority judgment. After intentional edits, review them, rebuild the registers, then regenerate the manifest with `python3 bfgs_lean_stage1/literature_audit/scripts/validate.py --write-manifest` before rerunning validation.

No external paper full text is redistributed. The bibliography establishes mathematical antecedents, not the causal source history of AI-generated research text.
