# Companion report and proof traceability

## Purpose

The article explains a focused set of results. The companion is the complete, organized research record. It must preserve all strongest incomparable conclusions without inheriting a chronological chat/report structure.

The companion is an archival document; it is not automatically a journal-published supplement. Essential new arguments for the article's own main results remain in the article and its in-document appendices. Formal code and detailed correspondence enhance reproducibility rather than replacing a readable mathematical proof.

## Suggested companion organization

1. **Scope and theorem map.** Exact algorithm, real-arithmetic model, positive versus negative quantifiers, notion of convergence, and article-to-companion map.
2. **Shared BFGS foundation.** Actual matrix definitions, preservation facts, principal-minor proof, normalized bridge, reciprocal growth, finite-horizon and ordered-tail arguments, fixed and moving energies.
3. **Certificate geometry.** General sufficient theorem, exact normalization, RS/inward equivalent, supporting-plane interpretation, pointwise feasibility, accessible-jump obstruction, and nonnecessity.
4. **Concrete positive families.** Centered/sublinear/powered/transformed cases, finite partitions, residual penalties, explicit basins, homogeneous dichotomy, low-rank and affine-fiber refinements, scalar results and rates.
5. **Affine criticality and curved geometry.** Exact geometric facts and attribution; planar joining and theorem; its scalar-ridge corollary; distinct flat-contour parabolic theorem.
6. **Arbitrary dimension with fixed normals.** Residual budget, exceptional hyperplane and parallel-interface results, weaker tangential curvature, full infinite-series example and limitations.
7. **Deterministic failures.** One canonical seed, actual line-search decision tree, global cap, C^{2,1} local embedding, positive-quadratic persistence, lower-curvature embeddings, and strict separation of regularity claims.
8. **Formal correspondence and reproducibility.** Exact contracts, allowed axioms, project/environment pinning, release hashes, actual build logs, archive layout, mathematical versus historical claims.
9. **Attribution and unresolved boundaries.** Scholarly comparison, access limits, supersession ledger, open questions, and preserved correction history/provenance.

Within sections, write conventional mathematics. Do not paste giant JSON dumps into the PDF. Provide a compact human-readable correspondence table and link it to a searchable machine index in the release.

## Stable mapping across documents

Assign a stable editorial claim ID independent of theorem numbering, such as `core.minorHierarchy`, `positive.localFinitePartition`, or `negative.localUpperRegularity`. These IDs are editorial identifiers, not asserted Lean declaration names.

For every claim, map:

    article statement/proof location
      -> companion statement/proof location
      -> corrected source file/span/version
      -> exact Lean declaration(s) and types
      -> correspondence argument / specialization
      -> transitive proof/audit evidence and commit
      -> relevant attribution entry

Different claims within one source span may need different formal declarations. A sample declaration in `coverage/*.tex` is not sufficient evidence of all statements in that span. Inspect the full index and dependencies. Preserve original versus corrected line locations as separate fields.

Include unnamed deductions that are mathematically load-bearing, especially positivity, finite-dimensional hypotheses, uniformity of constants, all-segment estimates, proper order of limits, and all-trial containment. Definitions and theorem hypotheses are not proved consequences merely because Lean accepts them.

## Source of truth and change discipline

Keep original source snapshots, original Git history and historical logs unchanged. New documents should derive from the current corrected edition, not replace it destructively. Record deliberate proof simplifications or alternate derivations in an editorial ledger. Do not claim a literal translation when the formal proof takes a different route.

Do not edit Lean definitions or weaken hypotheses to make prose claims compile. Resolve discrepancies explicitly. A newly strengthened theorem is a research task: either prove and map it, state it as a question, or leave it out of the theorem set. Editorial reorganization is not permission to add unproved deductions.

Shared notation, bibliography and stable statement data may be centralized. Avoid two divergent handwritten definitions of the algorithm or two inconsistent versions of the negative seed. The narrative structures of the article and companion may differ even when they share those data.

## Reproducible release

Use a documented build command for each PDF and a documented pinned formal audit. Record the commit actually audited. For builds that modify generated indexes, document how to reproduce the same file set without requiring a self-referential hash of a file that contains its own commit.

Provide:

- Sources and rebuild commands for both documents.
- Reproducible figure sources and exact/schematic data classifications.
- Updated claim/source/formal and attribution ledgers.
- Actual Lean/toolchain/mathlib revisions and complete audit scope.
- Permitted axioms and any conditional/export-boundary qualifications.
- Executed commands and outcomes, separate from inherited historical records.
- SHA-256 file manifest excluding its own recursive entry.
- A concise author-action list for metadata, consent, target journal and archive/DOI decisions.

Do not fabricate a DOI or make a public deposit without authorization. Existing remote pushes are separately authorized by the user; that does not authorize journal submission or new public dissemination channels.

## Unknown or blocked evidence

The inspected ZIP reports comprehensive formal correspondence but does not include its Lean project or full audit files. The user's repository is expected to contain more. If some referenced material cannot be found there, do not reconstruct fictitious audit evidence. State the missing artifact, trace what the available sources actually establish, and retain truthful verification wording.

Avoid downgrading genuinely checked results merely because the editorial handoff lacked their code. Conversely, do not repeat declaration counts or “fully verified” language based solely on the manuscript's front matter when the repository audit shows narrower coverage.
