# N5: finite trial mechanism and the fixed-objective local quantifier

The focused figure/table revision is complete. This is a component review; the root agent still needs to build and visually review the integrated article and companion.

## Changes and mathematical scope

The cycle figure now separates (a) the accepted cycle, (b) all nine actual queries, and (c) an enlargement of the three accepted points near the nonstationary origin. Solid, dashed, and dash--dot phase rays remain distinguishable in grayscale. Accepted lengths 1, 1/4, and 1/16 are explicit. The vertical enlargement in panel (a) and the different panel scales remain disclosed. A separate leader disambiguates the rejected 1/8 query near the axes.

The new shrinking-scale figure is deliberately restricted to the first, globally C2,1 branch construction. It shows one fixed objective, bad centers approaching its true minimizer, affine model neighborhoods of width O(a_ell), and complete copied query orbits of size O(a_ell^2) inside those neighborhoods. Its enlarged inset uses the finite canonical seed and two contraction copies. The location, neighborhood shape and scale layout are schematic. The figure does not depict an exact graph of the objective and supplies no stable-manifold or floating-point evidence. The caption expressly distinguishes the lower-curvature construction's spatial factor a_ell. The new figure uses the root-coordinated bad-center notation bar x_ell; the remaining source notation is for the root agent to synchronize.

Table 2 now places each phase's current value next to its trial values. The three current intervals for 10^4 G are (8884,8885), (1218,1219), and (723,724). The latter two are the preceding accepted intervals already displayed in the original table. For phase zero, G(z0) is the first coordinate, and the existing query box gives the exact enclosure

    [27831410117/31327000000, 5218474963/5873687500].

Multiplying its endpoints by 10^4 puts them strictly between 8884 and 8885. This follows either directly from the displayed formula for z0 or by adding one to the first coordinate of the first accepted query. The new read-only `paper/figures/check_trial_display.py` repeats the article's rational interval rules with Fraction arithmetic, checks these three outer bounds, preserves every old trial interval, and verifies that every rejected trial's lower bound exceeds its current phase's upper bound. It also checks the stored strict acceptance margins. The script is diagnostic arithmetic, never an imported proof premise. Appendix C, the canonical seed JSON, all existing certificate enclosures, and all theorem statements remain unchanged by this task.

A second scaling table was not added: the existing covariance equations and the separate construction paragraphs already explain both scale pairs. The new schematic supplies the missing fixed-objective/all-query information without another repetitive table.

## Actual validation

`generate_figures.py` compiled both vector PDFs using the fixed source epoch. `check_trial_display.py` passed. Both use only Python's standard library and ordinary TikZ/pdflatex. A separate three-page svjour3 proof rendered the two figures at the article's actual 12.2 cm text width and the table at normal text size. All three pages were inspected as images. A near-corner leader, smaller contraction arrowheads, and repositioned schematic labels resolved crowding. A 0.292 pt table overrun was removed with a local 5.8 pt column separation; the final proof log has no overfull, underfull, or LaTeX warnings.

The generated PDFs are vector artifacts; no raster illustration, arbitrary forward trajectory, or external copyrighted figure was used. The exact canonical seed file is unchanged from Git HEAD. SHA-256 hashes, the full exact display-check output, commands, and review-page hashes are in `N5_review.json`. Development renders and logs remain under the ignored `paper/figures/build/` directory. The full-document build, float placement, cross-reference review, and final visual gate remain the root agent's responsibility.
