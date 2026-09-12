# Author-side review record

These are AI-assisted self-reviews and cross-checks within the authoring team,
not independent human peer review.

## Pass 1 — mathematical scope and proof completeness

Reviewed the assembled main statements and the full energy/minor/reciprocal/
certificate/radial/finite-cell chain, plus separate D and L arguments. Independent
checks are in positive_completeness_review.md and negative_completeness_review.md.
The latter includes exact Fraction checks of the root, every strict trial margin,
and the shape derivative/eigenvalue intervals. The article now states the
classical twice-differentiability convention explicitly. The mixed-ridge identity
was corrected to 0 <= tau <= 1; article-only Lean wrappers were requested for new
geometric deductions rather than inferred from a similar old theorem.

## Pass 2 — narrative, novelty and readability

The title, abstract and three introductory theorem statements consistently give
local finite-cell convergence versus two incomparable local failures. Planar,
fixed-normal and parabolic results are identified as companion results; they are
not advertised as independently established article headlines. The text distinguishes
all admissible infinite runs from one deterministic implementation, all-query
containment from a failure basin, and positive lower curvature from C2 branch
regularity. No necessary-and-sufficient dynamical classification is claimed.

Point-of-use source review refined the Lewis–Overton scalar absolute-value
comparison: its inspected special analysis has c1=0, so the sentence no longer
identifies all line-search assumptions. Both fresh publication corrections and
the Rump theorem locator are in the new literature ledger. Unpublished works
are identified in text under the preferred journal policy. Uncited bibliography
entries were removed from the article while the companion retains its full record.

The direction toward a fixed minimizer is described accurately as a varying
vector. The wrong corner's positive gap is attributed to its coercive realization,
not to the unbounded cone alone. A second narrative review is in
narrative_pass2_review.md.

## Pass 3 — initial build and visual integrity

The first normal-appendix build was 33 article pages and 104 companion pages.
Root visually inspected all 33 article pages through nine four-page sheets.
Overfull displays were split rather than reduced in font size. The class's
editor manuscript-number and missing-affiliation placeholders were removed for
the author-review edition; no author information was invented. Its reserved
empty author block was removed without changing the body font or page geometry.
The article appendix body was explicitly restored to normal size. Figures were
read for grayscale distinction, exact-data/schematic status and label placement.
A fresh full-page render of the final revision will be matched to PDF hashes.

### Final article visual reconciliation

The final 32-page article was rendered completely at 100 dpi. All pages were
visually inspected in the prior complete review. Pages 1–7 and 32 changed after
the final metadata/DOI edits and were visually reinspected; every other final
page has the identical pixel SHA256 to its reviewed predecessor. No clipping,
overlap, broken glyph, unresolved reference or overfull display remains.
The final page hashes and PDF hash are in paper_visual_review.json.
