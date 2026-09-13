# Review of the revised BFGS article and companion

**Review date:** 12 September 2026  
**Source:** `BFGS_article_companion_LaTeX_sources.zip`  
**Source commit reported by the archive:** `91d30dadcfd0980472c3896be0c9fd83fc7d4db1`  
**Rebuilt documents:** article 46 pages; companion 107 pages.

## Overall assessment

**The narrative rebuild has largely succeeded. This version is recognizably a research paper, rather than a technical inventory. Keep its present theorem selection and overall architecture. The next step is a focused scientific-exposition revision, not another wholesale rewrite.**

The article now makes all three intended contributions visible: stronger deterministic failures, global/local positive theorems resolving concrete questions, and a reusable actual-BFGS analysis. The mixed benchmark appears in the abstract and is compared explicitly to the cited predecessor in the introduction. The homogeneous and centered global theorems now have complete in-article proofs. The former “beyond radial” catalogue has been replaced by the planar theorem, its nondegenerate smooth-max corollary, a genuinely nonradial quadratic example, and a proof appendix. The negative construction now has a design explanation and a shared scaling calculation.

These are substantial improvements. Do not undo them by narrowing the positive theory to a footnote of the counterexample, importing every companion theorem into the article, or reintroducing the old catalogue section.

The remaining scientific-exposition gaps are more specific:

1. The historical distinction of the negative results is still deferred until page 23, whereas the positive benchmark receives a compelling early comparison.
2. The article explains that the geometric assumptions help, but should more directly show **which positive hypotheses the actual counterexamples violate**.
3. The reader cannot see the main idea constructing the nonradial comparison field without entering Appendix B. This is the central geometric insight of the strongest selected positive extension, not merely routine appendix detail.
4. Some general family statements still need familiar worked specializations, especially for norms with nonisolated nonsmoothness and smooth loss plus polyhedral regularization.
5. The local-failure scale diagram is still missing; the existing cycle figure is byte-identical to the previous submission.
6. Repetition, notation collisions, and a small amount of audit-report language make a now 46-page article feel longer than its scientific story requires.

## Scope of this review

I read the article's seven sections and four proof appendices, inspected every article page as a rendered image, and inspected selected pages at full size. For the companion I inspected the new narrative, reading guide, inventory, relevant theorem/proof passages, and verification/correspondence descriptions. This is **not** an independent line-by-line audit of all 107 companion pages.

Both source builds succeeded. All 52 source hashes in the archive's manifest match. The final article log has no overfull boxes, undefined references, or LaTeX warnings; it has eight underfull box notices. The companion has the same absence of those substantive warnings and three underfull notices. The page counts agree with the source manifest. Reference PDFs were not included, so no claim is made that the locally rebuilt PDFs have identical text or bytes to another release.

This compact archive intentionally omits the Lean project and full audit database. No Lean build, transitive axiom review, fresh literature-priority search, or re-execution of the algebraic/hyperbolicity certificates was performed in this review. Claims about what prior authors proved below are evaluated as the manuscript's cited comparisons, not newly certified priority conclusions. `REVIEW_CHECKS.json` records the precise scope. `EVIDENCE.md` contains verbatim source excerpts with line numbers.

---

## What the revision now does well

### A. The introduction has a genuine research gap

`paper/sections/introduction.tex:28–52` (article pp. 2–3) gives a concrete comparison: the cited Guo–Lewis result reaches the line `v=0` along a subsequence, whereas the present centered-composite theorem yields whole-sequence convergence to the optimizer. The sentence “Approaching the nonsmooth line does not force the smooth coordinate u to vanish” is particularly effective. It explains the gap to a reader without requiring the reader to know the history already.

The introduction also places Xie–Wächter's finite-escape theorem and Gebken's conditional criticality analysis in that story, and describes the broader Lewis–Overton challenge without claiming that exceptional deterministic starts refute its almost-sure formulation. Keep those distinctions.

### B. The positive side is now a main contribution

Sections 4 and 5 prove the centered smooth–sublinear theorem, the explicit benchmark corollary, coercive homogeneous convergence, finite-partition local convergence, and the planar extension. The previous review's concern that the broad certificate had no in-paper nonradial payoff is resolved.

Using the planar theorem and its three-quadratic example, rather than the alternative many-parabola application suggested earlier, is a legitimate and strong editorial choice. Do not add another theorem merely to match an earlier suggested example. The separate flat-contour and fixed-normal results can remain in the companion.

### C. The framework is motivated by a proof problem

`paper/sections/energy.tex:74–111` (p. 7) shows the energy identity and explains why a positive limiting gap with bounded corrections would force only linear reciprocal growth. The hierarchy and reciprocal theorem then have a clear purpose. This is much better than introducing principal minors without explaining the problem they solve.

The three certificate clauses are motivated in `energy.tex:220–237`; the inward condition is explained in `global.tex:9–52`. The distinction between analytical comparison segments and executed BFGS steps is useful and correctly maintained.

### D. The failure construction now has a design

`failure.tex:13–19,66–80,225–268` (pp. 22,24,26–27) explains the shrinking cycle, actual trial selection, and the local embedding. The relation `H_F=(lambda^2/sigma) H_G` makes the identity-initialization claim understandable. Keep this explanation, the all-query containment, and the separation of the two regularity regimes.

### E. The companion's new entry route is helpful

`companion/research_story.tex` now supplies the same research question and three contributions before the inventory. `companion/master.tex:26–47` maps the distinct families and proof routes. This is the correct role for the companion: preserve the larger record without making the article carry every case.

---

## N1 — Finish the prior-work-to-contribution comparison

**Priority:** High.  
**Locations:** `paper/sections/introduction.tex:19–52,61–102`; `paper/sections/failure.tex:51–64`; `paper/sections/global.tex:250–260`; article pp. 2–3,15,23.  
**Evidence:** E1, E2, E3, E6.

### Issue

The mixed-benchmark comparison works exceptionally well. The negative and methodological contributions do not yet receive equally sharp early positioning. The discussion distinguishing the new counterexamples from smooth nonconvex, exact-search/subgradient, and limited-memory failures arrives only after the first negative theorem on page 23. A reader should not need to reach that page to know which negative result was missing.

Likewise, “every norm” is a strong understandable conclusion, but its significance beyond the attributed Euclidean case is not made concrete. An expert can infer the distinction; the article should explain it.

### Requested revision

Move a compact, sourced synthesis of `failure.tex:54–64` into the introduction. It should say what the cited failure constructions did and what they did not supply: the present conjunction of convexity, ordinary full BFGS, a specified Armijo–weak-Wolfe routine, and local failure at one objective's true minimizer. Keep detailed comparisons in Section 6 as needed, but remove duplication. Do not change the conclusion to an unsupported “first-ever BFGS counterexample.”

Add a short “what changes” synthesis, in prose or by revising the existing outcome table. It should distinguish four comparison units:

- smooth-extension/isolated-geometry results and the explicitly cited mixed-benchmark gap;
- conditional conclusions from iterate/matrix assumptions versus the stated objective-only sufficient families;
- earlier failures with different hypotheses versus the complete new deterministic convex local claim;
- classical trace/determinant potentials versus the adjacent-degree inequality and the consequence actually used here.

These are not set-inclusion claims about all results in the cited papers. Keep the scope of each comparison explicit and follow the primary-literature audit in the repository. In particular, convex restricted-class conclusions need not subsume a more general nonconvex but conditional theorem.

In the homogeneous application, name `l1` or `l_infinity` as an example where the nonsmooth locus is not isolated; no separate proof is needed beyond the norm corollary. Distinguish that elementary illustration from any claim that its complete convergence theorem had no antecedent, which must come from the literature audit.

### Acceptance test

By the end of the introduction a reader can state, for each contribution, a predecessor, its relevant limitation, and the precise advancement here. The negative distinction is no longer first explained on p. 23. No unsupported priority or universal superiority claim is introduced.

---

## N2 — Explain why the proved positive hypotheses and the actual negatives are compatible

**Priority:** High.  
**Locations:** `local.tex:245–318`, `failure.tex:355–382,464–490`, `verification.tex:3–32`; article pp. 19–21,28–31.  
**Evidence:** E10, E12, E13, E15.

### Issue

The current synthesis juxtaposes successful classes and failure regimes accurately, but it mainly lists them. The reader should be shown exactly why the counterexamples evade the strongest positive theorem. This is the missing final connection in the requested coherent story.

### Requested revision

Add one concise “what distinguishes the two outcomes” paragraph or small map after the negative proofs, using the actual constructed objectives, not generic rhetoric:

1. **Homogeneous global success versus the capped global counterexample.** The failing seed is unbounded below; its coercive cap has an affine intercept and is not the coercive homogeneous class. These distinctions are already proved in the manuscript. State them where the results are compared.
2. **Finite-partition local success versus the accumulating examples.** Bad vertices recur at arbitrarily small scales; a sufficiently small neighborhood cannot discard them. This is not the finite local polyhedral-cell geometry of Theorem 7.
3. **Planar nondegeneracy versus the local counterexamples.** At the optimizer of the first construction, all four branches are active and their gradients are `0,0,0,(0,1)`. The strong-convexity construction has the same pattern before the fixed invertible change of coordinates, and an equivalent pattern afterward. Therefore affine independence fails, and zero cannot be represented using strictly positive weights on all those branches. These are concrete failed hypotheses of Corollary 7, not simply an unspecified “geometric pathology.”

Also show, for the quadratic-plus-corner model, the exact secant decomposition `y = mu s + (g_j-g_i)`: the positive smooth-curvature term decreases with the step, while an active-branch jump need not. This explains why a lower Hessian bound does not remove the constructed mechanism; it does not claim that every such jump produces failure.

The last observation follows directly from the displayed branch formulas and the stated gradient calculation. Check the correspondence to the corrected formal construction if this becomes an explicit assertion in the article; do not silently alter a theorem.

Conclude at the right level: these examples show why regularity alone is insufficient and how the sufficient hypotheses distinguish the positive theorem's setting. **They do not prove that affine independence, positive multipliers, radial smoothness, or the certificate are necessary for BFGS convergence.** Nor is every accumulating kink pattern a failure mechanism.

### Acceptance test

A reader can answer “Why does the strongly convex counterexample not contradict the planar strongly convex positive corollary?” by pointing to explicit objective data, not a vague qualifier. The conclusion links the results rather than merely re-enumerating them.

---

## N3 — Bring the nonradial geometric insight into the main text

**Priority:** High.  
**Locations:** `local.tex:130–160,199–207`; `paper/appendices/planar_geometry.tex:40–123`; article pp. 18–19 versus pp. 34–35.  
**Evidence:** E8, E9.

### Issue

The main text correctly explains the roles of strict contours and regular switching, but the essential construction is still packaged as “Lemma B constructs a field with all required properties.” That is an acceptable proof citation, but not yet a satisfying explanation of the principal new geometric extension. The reader has to go to the appendix to see where the field comes from.

### Requested revision

Add a 200–350-word main-text proof overview before invoking the field lemma. Reuse the existing mathematics:

- A regular corner on the contour `F=t` follows a curve `p_j(t)` defined by `f_1(p_j(t))=f_2(p_j(t))=t`.
- Differentiating yields `grad f_1^T p_j' = grad f_2^T p_j' = 1`. Thus its velocity supplies a direction on which the active models agree; its negative is equal-rate descent.
- Strict contour convexity separates the normal arcs of distinct corners. This allows their prescribed directions to be joined consistently in normal-angle coordinates.
- The special joined field has the tangent-preserving derivative property. In the plane a level tangent is a line, so the relevant change is parallel to the tangent rather than an uncontrolled shear into another tangent direction.
- The resulting transport cost is controlled by actual objective decrease, which is summable. No finite-path-length assumption or nonlinear coordinate invariance is being used.

Do not bring the entire cutoff construction and one-sided comparison proof into the main text. Keep Appendix B complete. One core equation and an explanatory sketch should make the construction intelligible without duplicating its proof.

Consider adding a contour/ridge sketch or revising the existing geometric figure so it distinguishes the radial direction, switching tangent, and level-velocity direction. Different spaces and arrows must be labeled clearly; do not confuse primal directions with gradient-space vectors.

### Acceptance test

A reader who has not read Appendix B can explain (i) how the candidate direction is chosen, (ii) why multiple local choices can be joined, and (iii) why the proof is planar. The proof itself remains fully supplied in the article's appendix.

---

## N4 — Add two recognizable specializations, not more theorem families

**Priority:** Medium/high.  
**Locations:** Table 1 in `geometry.tex:62–86`; `global.tex:231–260`; `local.tex:78–128`; article pp. 5,15,17.  
**Evidence:** E6, E7.

### Issue

The benchmark is now concrete, but several further achievements remain presented mainly through abstract class names. The table repeats “centered smooth–sublinear,” “finite polyhedral smooth-piece partition,” and “nondegenerate planar smooth maximum” without giving the reader a quick familiar example for each.

### Requested revision

Keep the existing theorem selection. Revise Table 1 or the surrounding prose to include small examples tied to its rows. A compact explanatory pair would suffice:

- **A nonsmooth norm in arbitrary dimension.** State explicitly that the norm corollary applies to `||x||_1` (and, if useful, `||x||_infinity`), not only the already attributed Euclidean norm. Explain why the nonsmooth locus differs without adding a new theorem or unverified priority claim.
- **A smooth loss plus an absolute-value penalty at a nonzero optimizer.** For example, `F(x)=0.5||Ax-b||^2 + lambda||x||_1`, with `lambda>0` and a unique minimizer. Near that optimizer, nonzero coordinates have fixed signs and their penalty contribution is affine; zero coordinates contribute centered absolute values. This is a transparent specialization of the existing local theorem, not a claim that every instance has a unique minimizer or that global convergence is proved for all such sums.

Use the examples to explain why a condition is natural. Do not add several pages of duplicate corollary proofs. Keep the local/global, unique/nonunique, affine/homogeneous distinctions from the current text.

### Acceptance test

A reader recognizes why the theorem matters for a familiar nonsmooth model, and understands which assumption supplies locality or uniqueness, without being required to translate all class names unaided.

---

## N5 — Make the local-failure quantifier visible; finish the cycle figure/table

**Priority:** Medium/high.  
**Locations:** `failure.tex:110–181,253–268,372–423`; `paper/figures/`; article pp. 24–29.  
**Evidence:** E11, E12, E14; rendered article p. 25 in this package.

### Issue

The scaling explanation is now good, but the only negative figure remains the finite cycle. The file `paper/figures/cycle_trials.pdf` is byte-identical to the previous submission. It still crowds the points near the wrong vertex and distinguishes rejection lengths more clearly than accepted lengths. Table 2 presents `10^4 G` interval data without the current phase values that make rejection visually immediate.

The decisive local construction still has no diagram. It is not a minor decorative omission: the difference between shrinking one wrong-corner model and putting bad starts near one fixed objective's true minimizer is the strongest negative theorem's central quantifier.

### Requested revision

Add a labeled schematic near the embedding argument showing `x_*`, bad centers `p_j -> x_*`, an affine model neighborhood of width `O(a_j)`, and the complete copied query orbit of size `O(a_j^2)` inside it. Include a magnified inset. State that it is schematic, not an exact plot of the infinitely defined objective. Preserve the fixed-objective and all-query aspects.

For the cycle, improve the near-vertex labeling or add an inset; label the accepted lengths `1,1/4,1/16`, and differentiate phase-one and phase-two rays in grayscale. The existing explicit label about vertical rescaling is good and should stay.

For Table 2, add the phase's current value or a readable accepted-decrease ratio, or split “decision logic” from the detailed interval-certificate table. The exact enclosures can remain in Appendix C; do not substitute rounded values for certificate inputs.

A small scaling table is also useful if it replaces, rather than repeats, prose:

| Regime | spatial factor | objective factor | matrix factor |
|---|---:|---:|---:|
| smoother-branch embedding | `a_j^2` | `a_j^4` | `1` |
| lower-curvature embedding | `a_j` | `a_j^2` | `1` |

### Acceptance test

The figures explain both the finite deterministic mechanism and the fixed-objective local quantifier at normal print size. No forward floating-point plot is presented as evidence of stable-manifold membership.

---

## N6 — Tighten the article without cutting the scientific advance

**Priority:** Medium.  
**Locations:** Throughout, especially `energy.tex:113–129,265–271,319–326`, `verification.tex:36–58`, and notation in Sections 3, 5 and 6.

### Issue

The 46 pages are not automatically excessive, and the added positive proofs justify much of the growth from the preceding article. But the length now makes residual repetition and audit vocabulary expensive. Do not solve this by removing the mixed/global achievements, the in-paper nonradial payoff, or one of the incomparable counterexample regimes.

Specific examples of removable friction:

- “Actual principal minors” and “These are actual principal determinants” repeat what a precise definition already establishes.
- The paragraph about replacing an arbitrary real secant constant by its maximum with zero (`energy.tex:267–268`) belongs in formal correspondence, not the journal narrative.
- The exact benchmark inward-remainder calculation is displayed in both Section 2 and its corollary proof. Retain one display and cross-reference it.
- Repeated reminders about no spectral limits, accepted differentiability, and nonnecessity often recur within a few paragraphs. Keep each restriction where its omission would alter the claim; remove repeated reassurance rather than the restrictions themselves.
- The conclusion still says “Human authors must review ...” and lists Lean internals. This is appropriate editorial or companion information. Keep a truthful substantive AI-assistance disclosure and concise formal/reproducibility statement in the article; reserve future-author instructions and audit internals for author-review metadata or the companion.

Notation still collides: `M_k` is the positive-semidefinite Hessian-update remainder, while `M_0,M_1,M_2` are seed inverse matrices; `c=1-c_2` becomes an algebraic slope parameter; `d` is predicted decrease, a coordinate of a slope, and a scalar variable; `n` is the ambient dimension and an embedding index; `p` is a direction, point and affine offset. Most concretely, Lemma 4 must say that `z_2` means a coordinate just after using `z_2` as the third point in a cycle. Rename article aliases to eliminate those ambiguities. Lean names need not change; update the correspondence aliases.

If the detailed scalar interpolation interrupts the argument, retain its design and lemma in the main text and move the explicit ramp formulas/proof to an **article appendix**, not only the companion. That improves the main exposition without making the main theorem dependent on an external report. Overall length should be earned by proof and explanation, not hidden by tighter typography.

### Acceptance test

The main text reads as optimization mathematics, with one clear scope convention and honest disclosures, rather than as repeated responses to an audit checklist. No theorem has been weakened or a necessary proof omitted to shorten it.

---

## Companion-specific recommendation

Keep its improved opening and reading routes. This review does not request a second complete rewrite of all chapters. The companion should remain the exhaustive record of incomparable results and formal correspondence.

Perform a small navigation pass: eliminate remaining hard-coded chapter/section names when generated labels exist; separate inherited audit-process prose from operative theorem statements; verify the current “article proves / companion alone proves” map after any restructuring. The compact archive is explicitly typesetting-only, so absent full-repository audit files are **not** treated as missing deliverables in this review. In the full release, provide a stable article citation or versioned archival reference for the companion and code once the human author authorizes it; do not invent a DOI or submit/deposit anything automatically.

## Recommended order of work

1. Close N1 and N2: sharpen the comparative contribution and the explicit positive/negative connection.
2. Close N3 and N4: teach the nonradial construction and show the recognizable specializations.
3. Close N5 and N6: explanatory figures, readable table/notation, and selective compression.
4. Rebuild both documents, inspect the affected pages and full article, check references and source/formal correspondence for any newly explicit deductions, and update the review response.

Keep the current seven-section architecture unless a very small adjustment demonstrably improves it. Do not start another rounds-long expansion of verification infrastructure. Preserve the completed mathematical proof chain; revise the reader-facing explanation.

## Final recommendation

The manuscript now substantially satisfies the requested narrative goal. The remaining task is to turn a clear account of **what has been proved** into an equally clear account of **why these advances belong together and why their assumptions distinguish success from failure**. That is a targeted revision with a well-defined endpoint, not a request for more results or stronger claims.
