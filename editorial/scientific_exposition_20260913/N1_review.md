# N1: historical framing of the three contributions

13 September 2026. The introduction is revised against baseline
`91d30dadcfd0980472c3896be0c9fd83fc7d4db1`. This is a bounded author-side
self-review of exposition and existing source evidence, not a new literature
search, mathematical peer review or priority certification. The source edit
is complete; final pagination and visual acceptance belong to the root's
integrated build. No build, Lean compilation, commit or push was performed
for this subtask.

## What changed

Only `paper/sections/introduction.tex` was edited. The seven-section structure,
three contribution headings, theorem references and theorem selection remain.
The introduction grows from 826 to 938 whitespace-delimited words; moving the
old failure-section comparison removes its duplication in the integrated text.

| Comparison | Earlier result and relevant limitation | Additional conclusion made explicit |
|---|---|---|
| Smooth extensions and the benchmark | Guo–Lewis's general replacement theorems and Euclidean-norm result remain credited. Its specific mixed-model corollary supplies a subsequence approaching `v=0`, and the next paragraph leaves whole convergence to zero open. | The existing centered theorem settles whole-sequence convergence for `u²+|v|`. The homogeneous family includes every norm; `l1` illustrates nonisolated nonsmoothness along coordinate hyperplanes when the dimension is at least two. No novelty claim is made for each individual norm. |
| Conditional criticality | Gebken's published theorem assumes an iterate limit, repeated activity and the stated matrix/gradient-jump behavior. | The article derives convergence from objective conditions within its stated convex families. A new explicit sentence prevents reading this as subsuming Gebken's potentially nonconvex selection setting. |
| Deterministic failures | Prescribed-orbit smooth nonconvex examples, other nonconvex failures, exact-search/subgradient examples and scaled memoryless failures are now distinguished at the start of the negative contribution paragraph. | The following sentences retain the full conjunction: convex objective, ordinary full BFGS, the specified Armijo–weak-Wolfe routine, one fixed objective's unique minimizer, arbitrarily close failing starts with identity initialization, and all accepted/rejected queries close across the family. Both branch-regularity regimes remain explicit. |
| Matrix analysis | Nocedal's exposition supplies the classical trace/determinant potential ancestry and its uniform smooth secant bound. That bound need not survive gradient jumps. | The introduction identifies adjacent-degree principal-minor control for the full update, its reciprocal arithmetic-mean consequence under bounded gradients and vanishing predicted decreases, and the comparison-energy route to the stated convergence results. |

The Guo–Lewis comparison is not reduced to isolated singularities: the general
smooth-replacement theorems are still described before the concrete norm and
benchmark cases. The Xie–Wächter finite-exposure conclusion is unchanged and is
expressly not replaced by a broader infinite-run value theorem. Exceptional
deterministic starts are still distinguished from the probability-one
Lewis–Overton challenge. No first-ever, universal-superiority, positive-measure
failure or necessary-condition assertion was introduced.

## Existing primary-source evidence used

The local records reread are `editorial/LITERATURE_LEDGER.json`,
`editorial/narrative_rebuild/literature_primary_review.json`,
`editorial/narrative_rebuild/literature_comparison.md` and the preserved
`bfgs_lean_stage1/literature_audit/SOURCES.json`. Their hashes and individual
access records are reproduced or referenced in `N1_review.json`. No external
paper was downloaded and no new online access occurred on 13 September.

- **LO:** author-hosted published 2013 article, Challenge 7.1 on printed page
  160 and Algorithm 4.6. The 12 September primary text-layer inspection covers
  the probability-one assumptions and all four challenge items; screenshot
  access had failed. The introduction retains its different successful
  termination/infinite-run convention.
- **GL18:** inspected 11-page author manuscript with the published title,
  Theorems 3.2, 4.1 and 4.3, Corollaries 4.2 and 4.4 and the following open
  question. This is the numbering in the 12 September record, not the earlier
  2017 preprint's numbering.
- **XW:** arXiv:1712.08571v1, Theorem IV.1 under differentiable iterates,
  inspected as primary HTML on 12 September. Finite exposure of an unbounded
  descent direction is preserved; no bound on the subsequent unbounded search
  evaluations is asserted.
- **BG:** published Springer HTML, 8 May 2026, Theorem 3.1 with A2 and all B1
  clauses. The 12 September inspection covers the relevant proof and the
  introduction's mixed benchmark. The published number is not replaced by the
  preprint's Theorem 3.10.
- **NEG_M04 / NEG_M07:** Mascarenhas's published author copy, Theorems 1–4 and
  the relevant interpolation/orbit proof sections; the published 2007 primary
  HTML and earlier author manuscript have different numbering. The earlier
  literature audit inspected the seed/extension/BFGS construction; the later
  12 September M07 read supports technique lineage rather than a new complete
  audit. Only the supported smooth nonconvex and prescribed-orbit comparison
  is used.
- **NEG_LZ15:** Lewis–Zhang's published abstract and metadata, with previously
  indexed manuscript excerpts. Full-proof access was limited. The prose uses
  only the supported nonconvex distinction, not an uninspected theorem claim.
- **NEG_DIAO26:** arXiv:2609.09686v1, Theorem 1 and Section 2; the setup and main
  theorem were read on 12 September. It remains a preprint and is used only as
  another nonconvex comparison; no independent correctness or priority audit
  is asserted.
- **NEG_LO08:** 2008 author manuscript, Sections 2–3, Example 3.1 and
  Proposition 3.2. The recorded setup uses exact search and subgradient
  extensions, including zero steps. Publication status is not invented.
- **NEG_AO21:** final author manuscript, Assumption 3.2, Theorem 3.11 and
  Corollary 3.12; relevant hypotheses and proof excerpts were read. The failure
  comparison is restricted to the scaled memoryless update.
- **FND_N92:** author exposition, Section 5, especially the trace, smooth
  secant-quotient, determinant and potential identities. Earlier inspection
  supplies precise equation locators; the later extraction had corrupted
  numeral glyphs. The technical contrast relies on this accessible exposition.
  The already present Powell and Byrd–Nocedal citations retain their recorded
  limits: original Powell full text was not obtained, and original
  Byrd–Nocedal full-proof access was limited. No new full reading is claimed.

## Integration instruction and bounded checks

Root can remove the old text in `paper/sections/failure.tex` beginning
“Earlier prescribed-orbit” and ending “to the true minimizer.” In the baseline
this starts partway through line 54 and ends at line 64. Keep the preceding
sentences about objective/start versus parameter quantification, the sequence
of starts rather than a positive-measure basin, and the absence of a uniform
positive lower curvature requirement. This agent did not edit `failure.tex`.

All prior introduction citation keys are retained; the six added negative
keys already existed in the article bibliography or preprint references.
The source diff adds no theorem or algorithm environment and preserves the
arbitrary-SPD positive-run convention, accepted differentiability, both
negative regimes and the reciprocal theorem's hypotheses. The simple `l1`
observation explains an existing norm corollary; it is not a new theorem
family or a claim of unestablished publication priority.
