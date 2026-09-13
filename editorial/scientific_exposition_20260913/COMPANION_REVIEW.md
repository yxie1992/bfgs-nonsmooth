# Companion consistency review, 13 September 2026

The bounded source review passed. The opening, reading routes, and scientific selection remain intact. This review did not rebuild the companion, rerun Lean, inspect new cited primary sources, or claim independent peer review.

## Findings and targeted corrections

Six inherited module references escaped the original generator's singular-name substitutions: “Modules R and F” in the inventory, “Modules C and U” twice in affine geometry, “Modules A and H” in the evidence boundary, and two `Module~\ref{M:chapter}` references in the planar proof. The generator now converts these exact forms to clickable companion chapter references, with each change logged in `SOURCE_CORRESPONDENCE.json`. The Dyatlov bibliography note likewise refers to Chapter 13 instead of “Module L.” No bibliographic hypothesis or theorem locator changed.

The opening sentence of `current_verification.tex` now says “The recorded 12 September replay used Lean 4.19.0” rather than “The current revision run used Lean 4.19.0.” Its generated chapter introduction calls the audit “dated” rather than “current.” This prevents a 13 September prose revision from implying a new mathematical execution. The counts remain attached to the actual dated receipts, not to this review. The inherited earlier record is still explicitly introduced as historical material; old unsupported job counts have not been restored.

The remaining numeric locators checked are correct: Section 7.7 is the effective-dimension-at-most-two argument; Section 11.6 is the tangential strong-convexity extension; Section 11.1.1 supplies its weaker-curvature hypotheses. These were left unchanged. Every chapter/appendix reference in the handwritten master/correspondence reading routes resolves in the last compiled `.aux` to its intended location.

## Scope, notation and evidence

The companion's stated article selection agrees with the current article: centered and homogeneous global convergence, finite-partition and planar local results, the actual matrix/reciprocal framework, and both distinct local failure constructions. The noncompact homogeneous alternatives, fixed-normal geometry, flat contours, lifting, rates, scalar baseline and infinite constant-Hessian family remain separate companion material. The opening correctly separates covariance from orbit existence, sufficient conditions from necessity, and the two local negative regularity regimes.

The companion deliberately retains seed coordinates `c,d` from its frozen construction. The article's disambiguated `c_\circ,d_\circ` aliases are converted by `prepare_shared_appendix.py` before its shared seed proof is included. A difference in notation between these documents is therefore intentional, not a theorem-contract mismatch.

Read-only inspection of the recorded summaries confirmed the printed 9,672/9,781 safe declaration totals and 7,954 combined theorem count; the four supplements retain their respective 3/31,960, 11/10,697, 14/26,496 and 3/37,525 module-owned/transitive counts. Their standard axiom policy and the overlap warning remain explicit. The main run is dated 12 September, used the existing pinned environment and changed no audited inputs. No empty-cache build or new execution is claimed here.

The actual generator and its read-only `--check` both passed. All 172 corrected source spans, their source hashes/classifications, their complete formal-export lists, their chapter assignments and dispositions match Git HEAD; there are still 3,087 distinct original exports. The machine record gives the exact six transformations, receipt paths, checked `.aux` targets and file hashes. Root still needs to rebuild and visually inspect pages affected by these small reference and wording changes.
