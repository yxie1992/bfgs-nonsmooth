# Independent attribution and preservation review

Review performed: 2026-09-12T06:55:31.052503+00:00. Comparison baseline: `06ee12f7e7661437b8481fcab3b5bd26cff60130`. Reviewer: citation-positive subagent. The reviewer authored the 15 positive notes and independently reviewed the final collection, root integration script, other agents' notes, frontmatter and bibliography. This is a bibliographic/editorial review, not a new Lean proof audit or an independent correctness certification of external papers.

## Findings

**No blocking finding in the reviewed snapshot.** The 41 added notes and five specified wording substitutions preserve the operative mathematical text while distinguishing attribution from formal certification. The detailed findings below use the existing literature-audit packets and bibliography review; no new comprehensive external search was performed.

1. **M and T preserve the distinction between established tools and specific report results.** The determinant identity and classical matrix-potential analysis receive Nocedal/Byrd–Nocedal attribution. The complete adjacent-principal-minor hierarchy is not misidentified with that endpoint. The product/AM–GM notes point to Schöpfer's Theorem 3.7 proof and Jin–Jiang–Mokhtari's Appendices C–D without identifying their smooth quantities with `q = gᵀHg`. Combettes–Vũ's summable-error lemmas are described as technique precedents, not as proofs for singular/unbounded comparison fields or nonsummable additive residual budgets.
2. **R, F and H correctly distinguish known special cases and larger claims.** Guo–Lewis's arbitrary-dimensional Euclidean-norm result and Lewis–Overton's scalar absolute-value case are credited. Guo–Lewis's quadratic-plus-absolute-value statement remains subsequential in the comparison; the report does not claim that paper proves the broader centered theorem. The F smooth secant note retains the open convex neighborhood, compact buffer and possible constant enlargement. The nuclear example separately attributes its optimizer to singular-value thresholding while preserving the narrower radial-certificate obstruction.
3. **F rate and line-search comparisons retain algorithmic scope.** The smooth Armijo–Wolfe, exact-search and self-concordant references are separated. No rate transfer, uniform trial-complexity bound, or identification of scalar ray differentiability with full-gradient acceptance is asserted. The exact affine-fiber selector and its homogeneous specialization remain explicitly unresolved priority questions. Neither passage weakens a theorem by adding a literature assumption.
4. **H credits the stronger two-piece predecessor.** Xie–Wächter is identified as the inspected 2017 preprint and its Theorem IV.1 finite detection is described as stronger on that specialization than the report's many-piece infinite-run value conclusion. The discussion neither imports a modified algorithm nor promotes the more general value result to finite detection.
5. **D/L comparisons preserve the decisive distinctions.** The added text separates the earlier convex subgradient/null-step exact-search construction, globally nonconvex smooth constructions, Clarke-stationary limits with descent directions, and scaled memoryless BFGS failure. Diao's recent planar example is correctly described as smooth nonconvex with an escaping exact-search trajectory. The shared search-method citation is localized to Lewis–Overton Algorithm 4.6. L's fixed parameter pair and loss of second differentiability at the accumulation point are not merged with D's broader parameter family and upper branch regularity. The global quadratic-plus-maximum example is not promoted to arbitrarily local failure near its actual minimizer.
6. **Construction tools receive appropriately limited attribution.** Prescribed orbits plus objective extension, preconditioned root enclosures, stable manifolds/graph transforms and affine invariance are credited as established tools. The notes do not assert that external numerical output was imported into Lean, that the report used a particular external implementation, or that mathematical similarity reconstructs AI training provenance.
7. **Geometry notes and frontmatter correctly delimit the scholarship.** The affine-critical finiteness note includes the affine-combination projection step needed to pass beyond BDLS's printed Clarke-critical corollary. Gebken's behavior assumptions remain explicit. Accessible jumps are not replaced by all active differences, pointwise feasibility is not upgraded to transport, and RS failure is not called BFGS failure. The frontmatter explicitly excludes historical comparisons and priority judgments from the claims certified by Lean.
8. **The bibliography reconciles version and access status.** The existing keys are preserved, including the two-author 2018 Lewis–Liang version alongside the three-author 2022 successor. Gebken uses the May 2026 publication with the different preprint theorem number disclosed. Guo–Lewis journal-manuscript locators are separated from the earlier preprint. The NeurIPS Armijo–Wolfe article, exact-search publication and self-concordance preprint remain distinct. Access-limited original proofs are not described as fully inspected. Internal topic labels remain in their own category and are not presented as independently published sources.

## Independent preservation and structural checks

The integration script was read without rerunning its mutation. Independently, the review imported the current builder and reconstructed all 14 corrected chapters in memory from original report sources plus the entire edit ledger. It removed each exact note text and reversed each exact editorial substitution, then compared the result to `git show` at the baseline commit. Every comparison passed byte-for-byte.

Actual check output:

```text
PASS: exact restoration of all 14 prior corrected chapters, after removing 41 notes and undoing 5 wording replacements.
PASS: original chapter sources at baseline commit match working files: True
PASS: 53 unique bibliography keys; 34 citation keys in notes/frontmatter all resolve.
```

The five reviewed substitutions remove unqualified novelty wording in C/Q and do not change a mathematical formula, hypothesis or conclusion. The script validates exact anchors and note identity before writing ledgers, records applied note IDs and source IDs, and refuses immediate reapplication. Its final byte comparison also detects any incidental alteration not explained by the authorized insertion/replacement lists. The checked script is a one-use guarded migration; reproducible generation of the resulting edition is the report builder's separate responsibility.

No Lean source, external-paper proof, axiom dependency, rendered page or final release manifest was revalidated by this subtask. The parent task handles generated source maps, release checks and PDF rendering. The hash snapshot below fixes exactly what was reviewed; later changes require proportionate follow-up review.

## Snapshot

| SHA-256 | Repository path |
|---|---|
| `430760911422d46ac9c1e48556624894cfcdf5ddf156d9dc21051d5048d9db50` | `bfgs_lean_stage1/scripts/apply_report_attributions.py` |
| `35fd493950203ee8546da2a01235403b08a94a87a6e5a107f80108086b884ff8` | `bfgs_lean_stage1/master_report/authoring/bibliography.tex` |
| `972f9c2b246e98d7ea4249ff115ddcc86192be50324f790414e9f52f4f3a3fc5` | `bfgs_lean_stage1/master_report/authoring/frontmatter.tex` |
| `4078f4c3fe892457f89470b7aa8217d68ac583c599fd55fb48b5e687225c9fb9` | `bfgs_lean_stage1/master_report/authoring/citation_revision/geometry_notes.json` |
| `128b499ac43d0221e712fb587950d0705393427c2f6dcd30624f92c06ee6d4eb` | `bfgs_lean_stage1/master_report/authoring/citation_revision/negative_inventory_notes.json` |
| `d8a4ffbce107a07d218e821f669607741cae0e47e1ed89a6dfc0631610a01912` | `bfgs_lean_stage1/master_report/authoring/citation_revision/positive_notes.json` |
| `d6943d2ee60d1438543023c7224c1d1b6e87e29e60e30225e013118584691d00` | `bfgs_lean_stage1/master_report/authoring/citation_revision/editorial_replacements.json` |
| `f8ebbcee664ff41831cf8c10b360ea5f8de0c2876acb11f60a8484d9c3e96224` | `bfgs_lean_stage1/master_report/authoring/citation_revision/APPLIED.json` |
| `61cbb0700752b9cfea469abefc8c940bd53093d1f12618ddb7e3a05b6eca8e95` | `bfgs_lean_stage1/master_report/edits/60_attributions.json` |
| `1223854181012ff3452a1667fc47a4e34fc1b5898cf424e9aaf620c412aecb9e` | `bfgs_lean_stage1/master_report/edits/00_editorial.json` |
