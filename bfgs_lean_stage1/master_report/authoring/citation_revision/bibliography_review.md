# Bibliography revision review

Review date: 2026-09-11. Edited source: `master_report/authoring/bibliography.tex`.

The bibliography now contains 38 external works and the 15 original internal topic labels. All nine pre-existing external keys remain valid. No theorem or Lean source was changed by this subtask. The bibliography describes publication and inspection status; these descriptions do not turn references into formal proof dependencies or certify priority.

## Source-key reconciliation

| Report key | Literature audit record(s) | Version decision |
|---|---|---|
| XW | XW17, NEG_XW17 | Retain 2017 preprint; no journal publication inferred. |
| LO | LO13, NEG_LO13 | Merge as published 2013 article, online 16 February 2012; retain author PDF. |
| DY | NEG_DY18 | Retain 2018 preprint and Sections 3–4. |
| WW | WW22 | Retain inspected arXiv v1 of 1 April 2022, Theorem 2.5. |
| BG | BG26, geom_Gebken2026, NEG_BG26 | Update to JOTA 209 article 57, 8 May 2026; retain 2025 v1 and explicitly separate theorem numbering. |
| LW | geom_LewisWylie2019 | Retain 2019 preprint; no later publication established. |
| BDLS | geom_BDLS2007 | Add SJO 18(2), 556–572 (2007), retaining 14-page arXiv version for numbered locators. |
| LL | LL18, geom_LewisLiang2018 and its published_successor | Add three-author Lewis–Liang–Tian SJO 32(1), 276–291 (2022); retain inspected two-author 2018 v1 with explicit version caution. |
| BB | BB05 | Preserve journal reference; describe Definition 1 as established background. |
| GL18 | GL18, geom_GuoLewis2018 | Merge as 2018 published title, while retaining earlier 2017 title/version separately within the entry. Journal-manuscript Corollaries 4.2/4.4 are identified explicitly. |
| All remaining source-ID keys | Same-named SOURCES.json entries | Preserve individual article identities, dates, inspected versions and access limitations. |

The 29 added external keys are `GL18`, `S16`, `CCS10`, `GR91`, `FND_N92`, `FND_BN89`, `FND_P76`, `FND_Z05`, `FND_JJM24AW`, `FND_JJM26EX`, `FND_JM25`, `FND_CV13`, `geom_LSS2019`, `geom_Bogosel2023`, `geom_DDJ2026`, `geom_LSS2025`, `geom_Lewis2002`, `geom_BauschkeCombettes2010`, `NEG_LO08`, `NEG_LZ15`, `NEG_AO21`, `NEG_M04`, `NEG_M07`, `NEG_M14`, `NEG_DAI02`, `NEG_DAI13`, `NEG_DIAO26`, `NEG_RUMP10`, and `YVGS10`. Short printed labels avoid exposing source-register key lengths in the typeset report.

## Supplemental primary metadata checks

The existing audit was the main source. Additional direct checks during this revision resolved missing bibliographic fields:

- [Guo–Lewis publisher record](https://epubs.siam.org/doi/10.1137/17M1121883): SIAM Journal on Optimization 28(2), **1301–1311**, online 8 May 2018. These page numbers were absent from the merged source record.
- [Schöpfer publisher record](https://epubs.siam.org/doi/10.1137/140992990): SIAM Journal on Optimization 26(3), **1883–1911**, online 8 September 2016.
- [Cai–Candès–Shen publisher record](https://epubs.siam.org/doi/10.1137/080738970): SIAM Journal on Optimization 20(4), **1956–1982**, online 3 March 2010.
- [Liu–Sagastizábal–Solodov 2019 publisher chapter](https://link.springer.com/chapter/10.1007/978-3-030-11370-4_4): *Nonsmooth Optimization and Its Applications*, International Series of Numerical Mathematics 170, **55–87**, first online 30 March 2019.
- [Yu et al. primary JMLR page](https://www.jmlr.org/papers/v11/yu10a.html): 11(39), **1145–1200** (2010); its modified subBFGS/subLBFGS scope remains explicit.
- [Wachsmuth–Wachsmuth arXiv record](https://arxiv.org/abs/2204.00282): only v1 of 1 April 2022 and no journal-reference field. This supports retaining the inspected preprint; it is not a proof that no publication exists elsewhere.
- [Dai publisher record](https://epubs.siam.org/doi/10.1137/S1052623401383455): title is printed as *Convergence Properties of the BFGS Algoritm*, with that spelling, volume 13(3), 693–701 and year 2002. The record also displays a 2006 online date; the bibliography uses the publisher's volume year and retains the known 2002/2003 citation variation. The title was not silently corrected.
- [Zhang publisher book contents](https://link.springer.com/book/10.1007/b105056): 2005 hardcover; Horn–Zhang chapter *Basic Properties of the Schur Complement*, 17–46. No full chapter proof inspection is asserted.

No additional full-proof claims follow from these metadata checks. Search results and accessed pages were used only for the fields listed here.

## Caveats retained in the publication bibliography

Powell's original paper, Byrd–Nocedal's full text, Griewank's full proof and Dai's complete proofs were not obtained in the audit. These entries remain qualified background pointers. Lewis–Zhang was checked through publisher information and indexed manuscript excerpts, not a complete proof review. Zhang's book was checked at contents/metadata level. YVGS10 was an abstract-level algorithm screen. The bibliographic text does not upgrade any of these access statuses.

The NeurIPS 2024 Armijo–Wolfe paper, the exact-search article published online in 2025 and appearing in the 2026 volume, and the 2025 self-concordance preprint have separate keys. Diao remains a 9 September 2026 preprint, with no journal status or independent correctness certification asserted. The general Lewis partial-smoothness article retains its known 2002 electronic/2003 citation variation.

Internal labels remain a separate category with their original wording. They do not establish a historical archive or independent source provenance.

## Checks performed

A Python check on the edited file passed: 53 unique bibliography keys (38 external and 15 internal); every requested citation key present; the complete internal-label section byte-for-byte identical to `master_report/latex/bibliography.tex` before report regeneration. This is a structural check, not a LaTeX compilation. The parent task performs the report build, undefined-reference checks and PDF review.
