# Scientific-significance and publication-integrity review

Date: 12 September 2026. This is an author-side AI-agent review against the
five narrative handoff files and the current recursive article source graph.
The reviewer is separate from the integrating editor and positive/negative
proof authors, but contributed the introduction, synthesis and citation work.
It is therefore not a blind independent assessment or human peer review.
The JSON companion records exact source hashes and gate status.

**Source-level judgment: the revision now tells a research story with three
coequal contributions.** The opening establishes ordinary nonsmooth BFGS as
the problem, explains what earlier theory achieved, identifies a concrete
remaining benchmark, and gives complementary convergence and failure answers.
The matrix and comparison-energy work explains how the positive answers are
proved. Formal verification supports those answers at the end of the paper;
declaration counts and audit history do not organize its scientific narrative.

## What a reader can now say after the introduction

- **Problem:** Can ordinary full BFGS find minimizers of convex nonsmooth
  objectives, and how can this be proved when gradient jumps cause the
  matrices to degenerate, without assuming the iterate or spectral limit?
- **Precise prior limitation:** Guo–Lewis's smooth-replacement extension of
  Powell gives the norm result and only a subsequence reaching some point of
  the nonsmooth line for u squared plus absolute v. Their explicitly stated
  whole-sequence question leaves the smooth coordinate unresolved. Gebken's
  published 2026 result studies criticality with specified iterate and matrix
  behavior assumed. These are distinct prior contributions, not a blanket
  claim that all earlier theory was conditional.
- **Positive answer:** The named mixed-benchmark corollary follows from an
  arbitrary-dimensional centered-family theorem. The paper also proves
  compact/coercive homogeneous, localized polyhedral and nonradial planar
  results with the actual objective hypotheses and outcomes distinguished.
- **Negative answer:** One fixed objective per local construction has failing
  identity-initialized starts arbitrarily near its own unique minimizer under
  the specified unit-first search. The upper-regularity and positive-lower-
  curvature regimes are separate. The construction follows all queries; it
  does not establish positive-probability failure or disprove the full
  semialgebraic challenge.
- **Technical idea:** Adjacent degrees of actual principal minors constrain
  reciprocal metric-gradient growth. A comparison geometry converts that
  restriction into convergence when it sees the objective gap and controls
  secant and transport costs. A complete eigenvalue description is unnecessary.

## Handoff requirements and observed implementation

| Required repair | Current implementation and judgment |
|---|---|
| Establish the problem before an inventory of new theorems | The introduction starts with smooth BFGS, gradient jumps, nonsmooth effectiveness and the convergence question. No theorem-statement file is input there. |
| Put purposeful lineage before detailed results | Lewis–Overton, the general Guo–Lewis replacement framework, its exact mixed-benchmark gap, Xie–Wächter finite escape and Gebken's published behavioral hypotheses precede the detailed contribution paragraphs. |
| Promote the unresolved benchmark | The model is displayed in the introduction, explained geometrically in Section 2, and proved as the named corollary in Section 4. Its whole-sequence conclusion follows from the centered family, not an isolated planar recurrence. |
| Keep three explicit coequal contribution paragraphs | Deterministic limits, global/local convergence, and analysis with degenerating matrices remain distinct. A short early bridge now names all three before the longer lineage. |
| Give positive breadth a proved payoff | Section 4 proves the centered and coercive homogeneous families. Section 5 proves localization, finite partitions, planar cluster/convergence and a nondegenerate smooth-max corollary. The explicit three-quadratic example converges on the stated basin despite a radial obstruction. |
| Avoid a beyond-radial catalogue | The former catalogue is absent from the article graph. The planar application has its field construction and every essential endpoint estimate in the article appendix. Fixed-normal, flat-contour and noncompact alternatives remain explicit companion scope. |
| Explain sufficient conditions and their proof roles | Inward accuracy is a function-value modeling condition on positive bands; cells preserve inward segments after localization; moving fields retain a common pairing and control their motion. Each has examples, a place in the proof and a stated sufficient-only boundary. BFGS is never assumed to follow comparison directions. |
| Distinguish affine from ordinary criticality | Section 2 gives the common-rate versus strict-descent distinction. Section 5 uses affine criticality for the actual planar result. Neither presents affine balance as a universal classification of failure. |
| Explain the counterexample mechanism and actual implementation | Section 6 introduces the tempting global/local assertions, constructs a contracting cycle, proves the full trial decisions, explains matched scaling, and only then gives scalar interpolation and all-query induction. |
| Retain exact negative quantifiers and regularity | The fixed objective, fixed initialization and shrinking all-query neighborhoods remain explicit. Separate statements and the regularity table distinguish convex C2,1 from uniformly strongly convex C1,1. The global quadratic example is distinguished from an unresolved local finite-C2 question. |
| Explain identity initialization across shrinking copies | The matched-scaling calculation displays the spatial and objective factors, verifies update and line-search covariance, and isolates all-query containment as a separate requirement. The parameter choice leaves the common metric fixed. |
| Keep exact versus illustrative figures distinct | Captions identify the seed's rational center and show gradients or all queries. They disclaim exact-root equality and rounded stable-manifold membership. Final figure legibility still requires the scheduled visual pass. |
| Credit established tools affirmatively | The matrix section names the trace/determinant tradition and then the adjacent-degree extension. Geometry cites the normal-angle formula and local cocoercivity at the point of use, with explicit inspected-version locators. Negative antecedents occur near the construction. |
| Finish by answering the original question | The synthesis returns to the benchmark, family conclusions, deterministic exclusions and remaining boundary before a brief formal-verification paragraph and substantive AI disclosure. |
| Preserve complete principal proofs without artificial shortening | Matrix algebra, the planar field, root/trial certificate and lower-curvature perturbation remain article appendices. Peripheral noncompact, converse and further-family results are not promoted as independently proved article headlines. |
| Align the companion's story | The new companion research-story source uses the same benchmark comparison, positive breadth, distinct negative regimes and actual-matrix mechanism; wider independent results remain identified as such. Final correspondence-ledger reconciliation is an integrated release gate. |

## First-two-page gate

The initial 48-page build's first three pages were examined through the PDF
text layer. Page 2 contains the mixed benchmark, exact Guo–Lewis limitation,
Gebken assumption distinction and admissibility. The three detailed
contribution paragraphs continue onto page 3. The abstract already states all
three axes, but the introduction now also has a concise bridge immediately
after its opening question. A repeated later transition was removed. This is
a source correction aimed at making the first-two-page map explicit while
retaining the lineage; it is not a claim that source placement proves final
pagination. Both actual rendered first two pages of the 47-page final candidate were then
inspected with `view_image`: **PASS**. Page 2 contains the early three-axis
bridge, complete primary lineage, displayed benchmark with the prior/current
comparison, and the conditional-versus-objective distinction. The corresponding
PDF and page hashes are recorded in the JSON. This pass covers the opening;
the separate assigned all-page reviews retain their own scope.

## Citation and mathematical-exposition checks

The fresh primary-source record fixes the inspected versions and theorem
locators for Lewis–Overton, Guo–Lewis, Xie–Wächter, Gebken, Bogosel,
Lewis–Wylie and Wachsmuth–Wachsmuth. Classical original-source access limits
remain explicit in that record. Xie–Wächter's finite escape is not weakened
to or subsumed by an infinite-run value statement. Gebken's published theorem
number is used rather than transferring its preprint number. The challenge's
probability-one, semialgebraic, all-trial-value and spectral scope remains
distinct from deterministic exceptional starts. There is no blanket firstness
or priority certification.

At this review, the recursive article graph has 17 cited published entries,
all and only those in the bibliography, plus five unpublished works and two
explicit version pointers in the text. No source-level citation or reference
target is missing. The article abstract has 212 whitespace-delimited words,
five keywords and three MSC codes. These source checks do not establish final
PDF reference rendering or full journal readiness.

The separate `narrative_positive_review.md` records direct review of the
positive argument and exact rational checks of the displayed nonradial
example. It found no blocking mathematical gap. In particular, it verifies
that the length-local planar field is applied only after the proof shows
accepted step lengths vanish. The negative proof owner's reviewed contracts
and the integrating editor's formal audit remain distinct evidence; this
scientific-significance review does not silently promote their reported
results to a new independent Lean run.

## Length and publication integrity

The initial rebuild is 48 article pages, above the project's 30–35-page
budget. The broader complete positive theory and its planar field proof
account for a substantive scope change. Preserving both finite-branch
negative regimes also carries a real proof cost. A provisional project-budget
exception is justified while repetition and peripheral alternatives are
removed; compressing typography or delegating an essential proof would not
solve the editorial problem. The integrated final candidate measures 47 article pages and 107 companion pages; final rendered review is underway.

The official [Mathematical Programming instructions](https://link.springer.com/journal/10107/submission-guidelines)
were reopened on 12 September 2026. The updated `editorial/JOURNAL_FIT.md`
separates the journal's contribution/concision policy from the project's page
budget and retains the independent-report companion strategy. No numeric
general MP cap, editor-approved exception or SIOPT compliance is asserted.
Human author details, consent, final responsibility, interests/funding and
submission disclosures remain author decisions. The manuscript truthfully
states substantive AI assistance and is an author-review edition.

**Pending integrated release gates:** final PDF builds; remaining all-page visual inspection; rendered figures and citations; final
article/companion/formal-ledger reconciliation; final render hashes and length reconciliation;
and recorded Git milestone/push outcomes. The favorable source-level review
does not mark these gates complete.
