# Geometry attribution review

Date: 11 September 2026. Scope: the 19 A/C/Q/U/G attribution notes, their application in the guarded edit ledger, the attribution/frontmatter statements, and the bibliography entries they cite. This is a semantic and source-correspondence review against the completed local literature packets; it is not a new search or an external-paper correctness audit.

## Outcome

The substantive attributions agree with the inspected evidence. Two small wording refinements were sent to the integrating agent before release:

1. **G scalar comparison:** qualify the first sentence by Lewis–Overton's specified bracketing/secant algorithm. The packet records that Section 5.1 analyzes that algorithm, initially with `c1 = 0`; the report's general scalar theorem permits every positive metric and fixed valid Armijo–weak-Wolfe constants. Suggested sentence: “Lewis--Overton analyzes convergence on the scalar absolute value for its specified bracketing/secant algorithm (Section~5.1)~\cite{LO}.” The accumulating-corner attribution in the following sentence is appropriate and does not claim that the same exact certificate obstruction appeared there.
2. **C tame application:** change “hypotheses below remain necessary for this application” to “hypotheses below are retained in this application.” The latter preserves the theorem's stated assumptions without suggesting that their mathematical necessity has been proved.

No mathematical theorem or proof needs to change for either refinement.

## Source and scope checks

- **A affine geometry:** Lewis and the partial-smoothness lineage substantiate the common projected subgradient and affine-hull decomposition. Liu–Sagastizábal–Solodov Section 3.1 substantiates the affine-hull discontinuity mechanism. The notes distinguish that existing mechanism from this report's concrete finite strongly convex example.
- **A multiplier stability:** the note uses the inspected Lewis–Wylie preprint Propositions 5.5–5.6 and the published Gebken Lemma 3.5. It does not transfer Gebken's old preprint theorem numbering to the journal article or turn geometric nondegeneracy into an unconditional algorithmic theorem.
- **A stratified critical values:** the note does not attribute the affine-critical assertion directly to BDLS's narrower printed Clarke-critical corollary. It explicitly supplies the linear-projection inference: coefficients summing to one preserve the common stratum gradient, and a zero affine combination therefore forces that gradient to vanish. The packet supports the subsequent finite-stratification/critical-value deduction. The report's actual lifted-graph proof remains the formally reviewed proof.
- **C algorithmic comparison:** Gebken's iterate-limit and matrix-behavior assumptions remain explicit; Lewis–Wylie's bundle method is identified as a different algorithm. No priority claim is made for the full-BFGS theorem. The angular formula is credited to classical geometry through Bogosel's inspected equation (4), while the report's glued function is not misidentified as a convex support function.
- **C and U smooth estimates:** Wachsmuth–Wachsmuth Theorem 2.5 supports the differentiable open-convex-domain cocoercivity ingredient. The local buffered hypotheses remain visible; no global normal-curvature bound is imported.
- **Q comparison:** Guo–Lewis Corollary 4.4 is correctly described as a subsequence approaching the nonsmooth axis for `u² + |v|`, not convergence of the entire sequence to the minimizer. The report's complete finite family and Gebken's behavior assumptions are distinguished.
- **U scope and examples:** VU, quantitative tangential projection, and proximal-gradient VU methods are credited without treating their algorithms as unmodified full BFGS. The note retains `c ≠ 0` for the nonsplitting exclusion and limits the example's separation to RS and the stated differentiable-plus-scalar representation.
- **G certificate geometry:** rescaling, PSD Cauchy–Schwarz, polar-set duality and the seminorm triangle inequality are identified as established tools. The text distinguishes pointwise feasibility from transport, certificate failure from BFGS failure, and line-search-accessible jumps from the span of all active-gradient differences.

## Editorial statements and Lean verification

The new frontmatter expressly labels the bibliographic notes as editorial scholarship rather than additional assertions certified by Lean. It retains the stronger verification statement for the report's operative mathematical claims, explains that the exact formal statement includes all hypotheses, and identifies the source-correspondence review as the bridge from prose to Lean.

This distinction is appropriate. In particular, the BDLS attribution describes an external mathematical antecedent and the projection inference used for that comparison; it does not substitute an external theorem or an assumed stratification fact for the report's existing formal proof. The frontmatter separately names the lifted-graph route actually used by that proof. Publication dates, historical priority and AI-source provenance are correctly excluded from Lean certification. A historical-priority disclaimer cannot prove novelty, and the text does not represent it as doing so.

## Reproducible checks performed

Using the current guarded edit ledger and `build_rigorous_master_report.edited_source`, reconstructed the five corrected chapters and checked:

- A: 4 attribution blocks; C: 6; Q: 1; U: 3; G: 5.
- Each complete block occurs exactly once and is outside every theorem, lemma, proposition, corollary and proof environment.
- Removing the blocks and reversing the five recorded wording edits recovers each prior chapter byte for byte at baseline commit `06ee12f7e7661437b8481fcab3b5bd26cff60130`.
- All 13 bibliography keys used by the geometry notes exist, with no duplicate bibliography keys: `BDLS`, `BG`, `FND_CV13`, `GL18`, `LL`, `LO`, `LW`, `WW`, `geom_Bogosel2023`, `geom_DDJ2026`, `geom_LSS2019`, `geom_LSS2025`, `geom_Lewis2002`.
- The bibliography correctly distinguishes the inspected Guo–Lewis journal manuscript's numbering from the older preprint, Gebken's published and preprint numbering, and the two-author Lewis–Liang preprint from the three-author Lewis–Liang–Tian successor.

The frontmatter SHA-256 at this check was `972f9c2b246e98d7ea4249ff115ddcc86192be50324f790414e9f52f4f3a3fc5`. The generated chapter files had not yet been regenerated when the first check ran, so the substantive review used the reconstructed ledger output. Final regeneration, rendered-PDF inspection and the full release gate remain the integrating agent's checks. This review did not edit any original research source, Lean proof, chapter, bibliography or shared ledger.

## Resolved closeout after regeneration

Both requested refinements are now **resolved** in the authoring JSON, guarded ledger and regenerated chapter output. `g.scalar` expressly names Lewis–Overton's specified bracketing/secant algorithm. `c.tame` says the planar hypotheses “are retained in this application.” No review issue remains open.

Repeated the baseline-recovery checks against the actual regenerated A/C/Q/U/G chapter files: all five passed. Each of the 19 geometry notes is present exactly once and has an identical entry in `BIBLIOGRAPHIC_NOTES.json`. Each maps to exactly one claim span through that span's separate `bibliographic_notes` array, with matching source IDs, kind `bibliographic_attribution`, and status `Editorial source comparison; not a Lean-certified assertion`. The top-level note register also states that its editorial scope is separate from Lean-verified mathematics. The proof index contains the editorial warning. All 172 claim export lists remain identical to the preceding edition.

Final files inspected, with SHA-256:

| File under `master_report/` | SHA-256 |
|---|---|
| `authoring/frontmatter.tex` | `972f9c2b246e98d7ea4249ff115ddcc86192be50324f790414e9f52f4f3a3fc5` |
| `authoring/citation_revision/geometry_notes.json` | `ed76f9185f0e6d59bcea499d34cf5a72ef9bef955d6e3fd090e59eb1410d203a` |
| `latex/chapters/affine_geometry.tex` | `8583d3f3c01beeefbadedda47a3325aee53608688bd5ef8ff2ed96856a6a5cf8` |
| `latex/chapters/C.tex` | `4f8a9022e996dad01fabb77b0e03ee7e57d8f570df8c3f713dbb710cff0596ae` |
| `latex/chapters/Q.tex` | `1ec21f2af94144dcd403f560a0d1ebb3dc0305782e1a4778fa249539ae735ecc` |
| `latex/chapters/U.tex` | `a889f6a8e0c67c8b3d118a19b782b06f84b3da2ac02eacc58969109f364a6456` |
| `latex/chapters/G.tex` | `a8510a51a319faeb3fcf2b2b037343b173dbfc53bfc19b976ffd1896c544b455` |
| `BIBLIOGRAPHIC_NOTES.json` | `a8019baf120f43cc54f0590a9c441acab2957d243bf5b8bf2b882f166347f123` |
| `CLAIMS.json` | `bebaf9786c0920386e8817e639f8edb485b665255db97d934e036cbe935b3308` |

Classification and source-correspondence review: **PASS**. The integrating agent retains responsibility for rendered-PDF and full release checks; those are not asserted by this review.
