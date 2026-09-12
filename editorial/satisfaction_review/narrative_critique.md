# Skeptical editorial re-review of the 47-page article

Reviewed 2026-09-12. Candidate: `paper/build/master.pdf`, SHA-256 `cd1ddb3e1c733176ace2b689763385f2f07528e41ba94e24d5eb95293ba06a96`.

This is an AI agent's author-side re-review. I previously drafted portions of the introduction and synthesis; it is not independent human or blind peer review. I freshly read the text of all 47 pages and inspected the current rendered figures/tables on pages 4, 5, 26 and 31. Earlier PASS records were not treated as the answer. This is an editorial and scope review, not another kernel replay or full proof audit.

## Judgment

The article now reads as a substantial optimization paper. Its question is intelligible before the technical machinery, the mixed benchmark has a concrete before-and-after comparison with Guo–Lewis, and the global/local positive families and two different local failure regimes fit the same question. The explicit nonradial example gives the planar machinery a mathematical payoff. The paper is no longer led by declaration counts or validation inventory.

The first two pages do communicate the scientific plot: the abstract and early bridge state the three axes, then the introduction gives Lewis–Overton's challenge, the prior positive framework, the precise mixed benchmark, and the different Xie–Wächter and Gebken conclusions. The detailed contribution paragraphs finish on page 3; that is not a failure of the opening because the reader already has the plot. Another wholesale introduction rewrite or theorem-selection change would be counterproductive.

I recommend a focused revision before calling the exposition satisfactory. There is one summary-level hypothesis omission worth correcting, several repeated explanatory passages worth consolidating, and a few avoidable typesetting and citation interruptions. No new mathematical blocker emerged from this editorial reading.

## Concrete revisions, in order of value

### N01 — Qualify the reciprocal-growth contribution

**Location:** `paper/sections/introduction.tex:92–101`, page 3; compare the reciprocal-growth theorem at `paper/sections/energy.tex:169`.

“[The hierarchy] forces growth of the arithmetic mean” omits the bounded-gradient and vanishing-predicted-decrease conditions used by the theorem. Unlike the actual theorem, this sentence can be read as an unconditional consequence of full BFGS. Add a short qualifier, for example: “For bounded gradients and predicted decreases tending to zero, it forces the mean of these reciprocals to diverge.” This is a prose correction; it must not change any theorem assumptions.

### N02 — Remove repeated motivation and consolidate the exclusions

**Locations:** `paper/sections/global.tex:3–20,169–206` (pages 11, 13–14), `paper/sections/failure.tex:486–508` (page 31), and `paper/sections/verification.tex:3–45` (page 32).

The mixed model's surviving horizontal error is explained in the introduction, shown algebraically in Section 2, restated at the global opening, and discussed again after its corollary. Likewise, comparison directions versus actual steps, admissible-run scope, arbitrary SPD initialization, and lack of prescribed spectral limits recur often. These are valuable distinctions at their first explanatory occurrence and in precise theorem statements, but the later repetitions slow the narrative.

Replace the global opening by a short transition to inward accuracy. Keep the centered theorem and the named benchmark's complete short proof. Reduce the following paragraph to a precise one-sentence comparison with Guo–Lewis. Retain the centered-family observation that no positive lower Hessian bound is needed, but do not repeat its whole contract.

Section 6.7 largely anticipates the first half of Section 7. Put the deterministic exclusions and unresolved boundaries in one place, preferably the synthesis, and end the construction section with at most a brief transition. Preserve the implementation/strong-Wolfe limitation if removing its present only occurrence. Compress the synthesis's catalogue of positive results to the benchmark, its family extension and the nonradial advance. Keep the finite uniformly strongly convex C2 local question and probability/semialgebraic challenge boundary.

This offers roughly 500–800 words of pruning across the indicated passages, as an editorial estimate rather than a required quota or page-count promise. Cut repeated explanations, not essential assumptions or proof steps.

### N03 — Optional: keep the negative construction's main line uninterrupted

**Location:** `paper/sections/failure.tex:261–353`, pages 27–29.

The cycle, matched scaling and all-query induction form a strong sequence. The detailed scalar ramp definition and its regularity proof interrupt it for roughly two pages. A defensible alternative is to retain the named interpolation lemma and the scaling design in the main text, place every explicit defining formula and its full proof in an article appendix, and then proceed directly to the objective and query induction. The lower-curvature construction already uses this arrangement.

This is optional: the current proof is readable and complete. Such a move improves the main-text flow but does not shorten the article. It must not outsource the definition or any estimate to the companion or Lean, and it should not be done merely to chase a page target.

### N04 — Repair literal reference and proof-heading text

**Locations:** `paper/sections/introduction.tex:87–90`; proof headings at `paper/sections/local.tex:48`, `paper/sections/failure.tex:384`, `paper/appendices/seed_certificate.tex:96`, and `paper/appendices/lower_curvature.tex:151`.

The introduction prints “example 9”, but the target is Theorem 9. Say “the example in Theorem 9” through the existing reference. With the current class, the optional proof titles render as “Proof (Proof of Theorem 7)” and similarly on pages 29, 39 and 44. Use the class's convention without the repeated word, or a plain proof heading for an immediately preceding statement. These are small but visible repairs.

### N05 — Integrate unpublished citations grammatically; locate the stable-manifold theorem

**Locations:** `paper/sections/failure.tex:53–60`, `paper/appendices/planar_geometry.tex:119–124`, and `paper/appendices/lower_curvature.tex:151–158`.

Some full unpublished-work mentions are inserted where the prose expects an author or work name: “examples in (authors, full title, manuscript)” and “see … in (full bibliographic mention)” are awkward. Use the author in the sentence, and place the full required mention at a natural boundary. Preserve the existing journal-policy treatment of unpublished sources; moving them into the published bibliography is not the proposed remedy.

The stable-manifold use is load-bearing and deserves an exact locator. I freshly inspected [Dyatlov's 2018 v1 primary text](https://arxiv.org/html/1805.11660v1): Section 3.5, Theorem 3 is the local-coordinate formulation with invariant stable graphs and convergence. Its remark 4 invokes the rescaling argument of Section 3.1. This is the appropriate route after an adapted splitting and shrinking the neighborhood of the smooth hyperbolic return map. Section 4.1, Theorem 4 is formulated for a manifold diffeomorphism and compact invariant hyperbolic set, so do not give that as if it directly had only the local hypotheses. This is a citation-fit check, not a new proof of the classical theorem; no paper was downloaded into the repository.

### N06 — Keep verification supporting the paper, while shortening administration

**Location:** `paper/sections/verification.tex:47–71`, pages 32–33.

The present verification discussion is candid and appropriately secondary. Keep the standard axiom list, placeholder/custom-axiom exclusions, statement correspondence, kernel trust and reproducible proof availability. Keep the substantive AI assistance disclosure and pending human author review.

The extra source-tree inventory and list of absent affiliations, grants and archive identifiers can be removed from the paper and left in the existing author-actions record. They do not help assess the optimization result. Do not replace this with an assertion of author consent, completed human review or unconditional certainty about prose fidelity.

## What should remain

- Keep both figures. Figure 1 makes the common-rate/descent distinction concrete; Figure 2 shows the actual trial tree. Their rational-center and scale qualifications matter. No additional figure is needed.
- Keep all three tables. The first distinguishes starting scope and outcome, the second is part of the finite certificate, and the third prevents conflating the two different negative regularity regimes. Caption compression is possible, but removing a table would not clearly improve the paper.
- Keep the named mixed benchmark and explicit three-quadratic nonradial example, both central finite-branch negative theorems, matched scaling, and actual all-query induction.
- Keep the complete planar, rational-certificate and lower-curvature existence arguments in the article. No essential estimate or parameter/existence choice should be delegated to Lean or the companion.
- Keep the present large-scale sequence: scientific orientation, analytical mechanism, global/local consequences, implemented failures, synthesis. The advance summaries are now sufficient to support method-first proofs.

## Citations, novelty and scope

I found no newly unsupported historical or priority assertion. The current Guo–Lewis, Xie–Wächter, Gebken and Lewis–Overton distinctions are defensible against the exact-version primary-source records already assembled in `editorial/narrative_rebuild/literature_primary_review.json`. This review did not repeat the entire literature search and is not an exhaustive priority certification. Only the newly uncertain local stable-manifold locator was rechecked online.

The admissibility restriction, compact-sublevel qualifier, local/global distinction, two different curvature regimes, exceptional-start character and non-resolution of the almost-sure challenge are all present. The editorial problem is repeated explanation of these restrictions, not their absence. Apart from N01's summary wording, no stronger unstated theorem contract was identified here.

## Next candidate

Apply N01 and the restrained consolidation/presentation repairs, then rebuild and inspect the changed pages and cross-references. N03 is optional and should be selected only if the main-text construction flow clearly improves. A satisfactory author-review manuscript does not require forcing 47 pages into the original informal 30–35-page target by dropping proofs. Human author review and submission decisions remain pending.

## Authorized response to the review

After this critique was completed, the parent explicitly authorized targeted edits to `paper/sections/introduction.tex` and `paper/sections/verification.tex` and confirmed completion of the PDF-operation marker. I made those two edits only:

- N01: qualified reciprocal-mean divergence by bounded gradients and predicted decreases tending to zero.
- N04 in the introduction: changed the bare example number to “the example in Theorem” with the existing reference.
- N02/N06 in the synthesis: reduced 587 to 449 whitespace-separated source words, preserving the two distinct local regimes, exact theorem references for search parameters, the finite strongly convex C2 and probabilistic/semialgebraic boundaries, standard axioms and audit limitations, and substantive AI assistance/pending human review. The specific-implementation/strong-Wolfe limitation is now included here so the preceding duplicated discussion can safely be consolidated.

`git diff --check` passed for both edited sources. The integrated rebuild and changed-page inspection are the parent's next step. The original 47-page PDF hash above remains the reviewed candidate; it is not relabeled as a build of these edits. The JSON records both prior and current hashes for the edited files. N02's global/failure cuts and the remaining N04/N05 repairs belong to the parent; N03 remains optional.

No Lean, original scientific source, package or Git changes were made by this agent.
