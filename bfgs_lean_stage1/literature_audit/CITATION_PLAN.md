# Concrete attribution supplement for a future report edition

This file supplies reviewable changes without modifying the frozen verified edition. It is an attribution supplement, not an assertion that every proposed reference is a formal proof dependency. The source IDs below resolve to [SOURCES.json](SOURCES.json); version-specific locators and access limits are retained there. The broader assessment is [REPORT.md](REPORT.md).

## Claim wording to use

For an exact known case: “This special case was established by [source]. We recover it as a consequence of the broader theorem below.”

For an established geometric deduction: “The following is a consequence of standard [specific machinery]. We include the argument to make the hypotheses and the connection to BFGS explicit.”

For a possible extension: “The closest results identified in our literature audit prove [precise narrower statement]. The theorem below adds [precise scope], using [specific derived condition]. We do not assert historical priority on the basis of that search.”

For a counterexample: state the dimension, global convexity, branch regularity, initialization, line-search implementation, differentiability of queries, locality and limit stationarity together. Avoid an unqualified “first BFGS counterexample.”

For a certificate obstruction: name the certificate and its quantifiers. Do not describe failure of that condition as failure of BFGS, or failure of a canonical field as impossibility of every field.

## Chapter-by-chapter insertions

| Corrected report location | Concrete addition or correction | Sources / exact comparison |
|---|---|---|
| Inventory, I.span.3 | Add classical algorithmic background before the new results, with accepted-gradient/full-update scope. | Nocedal1992 §5; Lewis–Overton2013 §2 and Algorithm4.6; Xie–Wächter2017 algorithm convention. |
| Inventory, I.span.5–7 and D/L opening | Add a related-counterexamples paragraph separating convex/differentiable-query/bracketing failures from prior nonconvex, null-step and memoryless constructions. | Negative packet: LO08, LZ15, AO21, M04/M07/M14, DAI02/DAI13, DIAO26. Do not imply all original proofs were available. |
| M.span.1–3 | Credit trace/determinant analysis; distinguish the standard determinant endpoint from the complete adjacent-principal-minor hierarchy. | FND_N92 §5, especially (5.7),(5.15),(5.21); FND_BN89 and FND_P76 with access qualifications; FND_JJM24AW Appendices C/D; S16 Theorem3.7 proof. |
| M.span.4–5 | Identify quadratic cancellation, congruence, Young inequalities and multiplicative-error estimates as existing tools; state what residual budget is derived. | FND_N92; FND_CV13 Lemmas2.2–2.3. No claim that a bounded/coercive-metric theorem directly covers singular comparison fields. |
| T.span.3–6, G.span.3 | Introduce the criterion as a specific sufficient condition and the exponential rescaling as an elementary normalization. | FND_CV13 as a technique precedent; the report's actual PSD-field proof supplies the additional quantifiers. |
| R.span.2 | Retain BB for the Bregman expression, explaining differentiability only at the supporting endpoint. | BB05 Definition1; ordinary convex supporting-plane calculus. No new-divergence claim. |
| R.span.10–12, F.span.1–2, H.span.12 | Add Guo–Lewis for Euclidean norm and explicitly compare `u²+|v|` with their weaker subsequential conclusion. | GL18 Corollaries4.2/4.4 and Theorem4.1. This is an essential missing reference. |
| R/F smooth secant estimates, C.span.15, U.span.7–9 | Credit cocoercivity; preserve open-neighborhood and compact-buffer qualifications. | WW22 Theorem2.5; geom_BauschkeCombettes2010. A global Lipschitz hypothesis must not replace the report's local one. |
| R.span.16 | Credit the known optimizer calculation separately from the rotated-pair radial obstruction. | CCS10 Theorem2.1 (singular-value thresholding). |
| F.span.4, H.span.16/20 | Add invertible affine invariance and smooth noncompact comparisons; mark exact rectangular metric-selector priority unresolved. | XW17 TheoremII.1; LO13 §2; S16 Assumption3.1 and Theorems3.4/3.7. The last is not a proof of the selector. |
| F.span.5 | Add current smooth-rate comparisons while preserving accepted-iteration units and nonsmooth assumptions. | FND_JJM24AW; FND_JJM26EX; FND_JM25; S16. Do not identify their gradient-normalization symbols with q=gᵀHg. |
| F.span.6 | Distinguish line-restriction differentiability from full-space differentiable acceptance. | LO13 Theorem4.5 and Proposition4.11. |
| H.span.13–14 | Retain explicit credit for the stronger finite-detection two-piece result. | XW17 TheoremIV.1; not merely a consequence of the report's infinite-run theorem. |
| G.span.4–7 | Identify polar-set/PSD arguments as elementary; credit the normal/tangent lineage and retain accessible-jump qualifications. | geom_Lewis2002, geom_LewisLiang2018 and its published successor; FND_POINTWISE is a standard deduction, not an exact publication match. |
| G.span.9–10 | Add scalar absolute-value convergence and accumulating-corner line-search precedents, without conflating them with the exact certificate obstruction. | LO13 §§4.2/5.1, as explained in the positive packet. |
| A.span.1–3, C.span.3/11 | Credit VU decomposition, partial smoothness and stable positive multipliers. | geom_Lewis2002; geom_LSS2019 §3.1; geom_LewisWylie2019 Propositions5.5–5.6; published Gebken Lemma3.5. |
| A.span.4, C.span.12 | Present affine-critical finiteness as a corollary/reproof of stratified projection and definable critical-value machinery. Include the affine-combination projection step. | geom_BDLS2007 Proposition4, Lemma8 and Corollary9 proof. The narrower printed Clarke-critical corollary alone does not justify the affine claim. |
| C.span.7–8 | Credit the classical angular formula and derivative cancellation; distinguish the glued comparison function from a convex support function. | geom_Bogosel2023 §2 equation(4). |
| C/Q/U main theorems | Add the nearest algorithmic comparisons with explicit conditional assumptions or algorithm changes. | Gebken2026 Theorem3.1 behavior(B1); Lewis–Wylie bundle Newton; DDJ active-manifold geometry and PGVU. Full comparisons in geometry packet. |
| U.span.12–14 | Limit novelty language to the exact spikes/coupling and stated certificate separation; retain c≠0 for the nonsplitting exclusion. | Established VU/partial-smoothness context; no exact example match located. |
| D.span.2, L.span.2 | Retain and localize Lewis–Overton algorithm credit; preserve the different parameter ranges of D and L. | NEG_LO13 Algorithm4.6 p.147. |
| D.span.3–9, L.span.3–7 | Add prescribed-orbit/objective-extension precedents, separating the general method from these specific convex constructions. | NEG_M04/NEG_M07/NEG_M14; Diao2026 as recent neighboring work. |
| D seed validation and L.span.5 | Credit established root-enclosure and hyperbolic-dynamics methods; distinguish Lean rational certificates from external software computations. | NEG_RUMP10 §13.2 Theorem13.3; NEG_DY18 §§3–4. |
| L.span.7 final coordinate change | Add a local affine-invariance citation. | NEG_LO13 §2 p.140 or XW17 TheoremII.1. |

Rows identify substantive span groups. Exact corrected file and line ranges are available in the 172-row `span_coverage` array of [CLAIMS.json](CLAIMS.json); original report hashes make the references reproducible.

## Ready-to-use related-work paragraph

Ordinary BFGS has an established convergence theory for smooth convex problems and several proved nonsmooth special cases. Guo–Lewis establishes Euclidean-norm convergence and a smooth-extension route, while Xie–Wächter proves finite detection of unbounded descent for a two-piece affine class. Classical trace/determinant analysis supplies important matrix tools. The results developed here concern additional nonsmooth families and specific deterministic failures under differentiable accepted iterates. Their comparisons must preserve the objective class, full update, line-search rule, initialization and convergence conclusion. The accompanying literature audit identifies known special cases and technique antecedents and records the remaining uncertainty about exact publication priority.

Use citations to GL18, XW17, Nocedal1992/Byrd–Nocedal1989 and the appropriate negative packet entries when inserting this paragraph. The detailed local comparisons should accompany each principal claim; this paragraph is not a substitute for them.

## Bibliography updates

1. Add Guo–Lewis2018, Schöpfer2016, Nocedal1992, Byrd–Nocedal1989, Combettes–Vũ2013, Cai–Candès–Shen2010 and the negative precedents appropriate to the cited text.
2. Update Gebken from preprint-only metadata to the May2026 journal article; retain the inspected preprint as a version locator where necessary.
3. Retain Lewis–Liang2018 when citing that version; add the published Lewis–Liang–Tian2022 record with three authors. Do not silently attach old theorem numbers to the new version.
4. Distinguish NeurIPS2024 Armijo–Wolfe rates, the exact-search article online2025/volume2026, and the 2025 self-concordance preprint.
5. Retain preprint status for Diao2026 and for any work whose later publication has not been established in this audit.
6. Keep internal report-topic labels in a separate category. They do not substantiate historical publication or independent source provenance.

[references.bib](references.bib) contains every source record under its packet ID. It intentionally retains version/access duplicates to support the audit; a publication bibliography should merge duplicates only after preserving the locators used by the text. Metadata-only entries are pointers for follow-up, not assertions that their full proofs were inspected.
